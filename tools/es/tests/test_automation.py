import json
import sys
from concurrent.futures import ThreadPoolExecutor

import pytest

from es import operations, delivery, usage
from es.artifacts import compact, read
from es.errors import UsageError
from es.jobs import run_job, reserve_job, request_cancel
from es.store import Store


def spec(*commands):
    return {'schema_version': 1, 'stages': [{'name': f'step-{i}', 'action': 'command', 'argv': [sys.executable, '-c', cmd], 'memory': '1G', 'minutes': 1} for i, cmd in enumerate(commands)]}


def test_operation_restart_idempotence_and_delivery(cfg):
    request = spec('print(1)', 'print(2)')
    op = operations.submit(cfg, 'tester', request)
    assert operations.submit(cfg, 'tester', request)['id'] == op['id']
    for _ in range(2):
        current = operations.show(cfg, op['id'])
        stage = next(s for s in current['stages'] if s['status'] != 'succeeded')
        run_job(cfg, stage['job_id'])
    final = operations.show(cfg, op['id'])
    assert final['status'] == 'succeeded'
    assert final['result']['proof_accepted'] is False
    operations.advance(cfg)
    assert len(delivery.pending(cfg, 'tester')) == 1
    delivery.pause(cfg, 'tester')
    assert delivery.claim(cfg, 'tester', 'client') is None
    delivery.pause(cfg, 'tester', False)
    event = delivery.claim(cfg, 'tester', 'client')
    assert delivery.claim(cfg, 'tester', 'second') is None
    delivery.ack(cfg, 'tester', event['event_id'], 'client')
    delivery.ack(cfg, 'tester', event['event_id'], 'client')
    assert delivery.pending(cfg, 'tester') == []


def test_atomic_admission(cfg):
    op = operations.submit(cfg, 'tester', spec('pass'))
    job = op['stages'][0]['job_id']
    with ThreadPoolExecutor(max_workers=2) as pool:
        results = list(pool.map(lambda _: reserve_job(cfg, job, launching=True), range(2)))
    assert sorted(results) == [False, True]


def test_cancel_queued_does_not_execute(cfg):
    op = operations.submit(cfg, 'tester', spec('raise AssertionError()'))
    result = operations.control(cfg, op['id'], 'cancel')
    assert result['status'] == 'cancelled'
    assert run_job(cfg, op['stages'][0]['job_id'])['status'] == 'killed'


def test_failed_stage_retains_prior_receipt(cfg):
    op = operations.submit(cfg, 'tester', spec('pass', 'raise SystemExit(3)'))
    run_job(cfg, op['stages'][0]['job_id'])
    next_job = operations.show(cfg, op['id'])['stages'][1]['job_id']
    run_job(cfg, next_job)
    failed = operations.show(cfg, op['id'])
    assert failed['status'] == 'failed'
    after_cancel = operations.control(cfg, op['id'], 'cancel')
    assert after_cancel['status'] == 'failed'
    assert after_cancel['result'] == failed['result']
    with pytest.raises(UsageError):
        operations.control(cfg, op['id'], 'resume')
    retry = operations.control(cfg, op['id'], 'retry')
    assert retry['stages'][0]['attempt'] == 1
    assert retry['stages'][0]['status'] == 'succeeded'
    assert retry['stages'][1]['attempt'] == 2


def test_resource_block_is_visible(cfg):
    request = spec('pass')
    request['stages'][0]['memory'] = '999G'
    op = operations.submit(cfg, 'tester', request)
    assert op['status'] == 'blocked_resource'
    assert op['stages'][0]['job_id'] is None


def test_artifact_integrity_and_compact_output(cfg):
    payload = {'status': 'failed', 'diagnostic': 'x' * 10000}
    brief = compact(cfg, payload)
    assert len(json.dumps(brief)) < 4096
    assert json.loads(read(cfg, brief['detail']['id'])) == payload


def test_transaction_rollback(cfg):
    with pytest.raises(RuntimeError):
        with Store(cfg) as st:
            st.conn.execute("INSERT INTO automation_meta VALUES ('rollback','bad')")
            raise RuntimeError('crash')
    with Store(cfg) as st:
        assert not st.conn.execute("SELECT * FROM automation_meta WHERE key='rollback'").fetchall()


def write_usage(path, amount=100):
    u = dict(input_tokens=1000, cached_input_tokens=900, output_tokens=amount, reasoning_output_tokens=amount//2)
    events = [{'type': 'session_meta', 'payload': {'id': str(path)}},
              {'type': 'token_usage_record', 'timestamp': usage.now(), 'payload': {'thread_id': str(path), 'response_id': 'r1', 'usage': u, 'thread_token_usage': u}}]
    path.write_text('\n'.join(json.dumps(e) for e in events)+'\n')


def test_usage_exact_dedup_and_matched_estimate(cfg, tmp_path):
    ids = []
    for label, tokens in [('baseline',100), ('treatment',40), ('setup',120)]:
        ident = usage.begin(cfg, 'tester', label, 'replay', label, pair_key='source-hash')
        path = tmp_path / (label+'.jsonl')
        write_usage(path, tokens)
        usage.transition(cfg, ident, 'complete', 1)
        first = usage.ingest(cfg, path, ident)
        assert first['coverage'] == 'reconciled_snapshot'
        assert usage.ingest(cfg, path, ident)['inserted'] == 0
        ids.append(ident)
    estimate = usage.compare(cfg, [ids[0]], [ids[1]], 10, [ids[2]])
    assert estimate['mean_saved_per_window']['output_tokens'] == 60
    assert estimate['output_break_even_windows'] == 2
    assert estimate['estimated_net_saved']['output_tokens'] == 480
    assert usage.report(cfg, ids[0])['usage']['uncached_input_tokens'] == 100
    with pytest.raises(UsageError):
        usage.compare(cfg, [ids[0]], [ids[0]])
