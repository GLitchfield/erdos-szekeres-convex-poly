import json
from pathlib import Path
import time

import pytest

from es import agent_run, jobs, run_monitor
from es.errors import UsageError
from es.store import Store


def make_run(cfg, *, host_status='running', state_status='running'):
    out = cfg.root / 'runs/native'
    out.mkdir(parents=True, exist_ok=True)
    host = jobs.submit_run(cfg, command=['true'], why='test native host', outputs=['runs/native'],
                           agent='tester', memory_max='256M', queue=True)
    with Store(cfg) as st:
        st.job_update(host['id'], status=host_status)
    state = {'schema_version': 1, 'root': str(cfg.root), 'out': str(out),
             'coordinator_agent': 'tester', 'researcher_agent': 'sol-test',
             'current_host_job_id': host['id'], 'status': state_status, 'phase': 'test',
             'timing': {'deadline_at': agent_run._utc(time.time() + 120)},
             'goal': {'status': 'active'}, 'progress': {}}
    agent_run._atomic_json(out / agent_run.STATE_NAME, state)
    run_monitor.register(cfg, out, 'tester')
    return out, state, host


def policy(cfg, **values):
    # Workers reload the recorded checkout's config, not this process's overrides.
    with (cfg.root/'harness/config.toml').open('a') as handle:
        handle.write('\n[automation.monitor]\n')
        for name, value in values.items():
            handle.write(f'{name} = {value}\n')


@pytest.fixture
def transport(monkeypatch):
    from es import run_delivery
    events, calls = {}, []
    def emit(cfg, agent, ident, payload):
        events.setdefault(ident, payload)
    def dispatch(cfg, agent):
        calls.append(agent)
        return {'status': 'no_delivery', 'model_requests': 0}
    monkeypatch.setattr(run_delivery, 'emit', emit)
    monkeypatch.setattr(run_delivery, 'dispatch', dispatch)
    return events, calls


def test_idle_and_routine_compile_failures_never_emit(cfg, transport):
    out, state, _ = make_run(cfg)
    child = jobs.submit_run(cfg, command=['false'], why='ordinary Lean attempt', outputs=['runs/native'],
                            agent='sol-test', memory_max='256M', queue=True)
    with Store(cfg) as st:
        st.job_update(child['id'], status='failed')
    for _ in range(12):
        assert run_monitor.tick(cfg)['model_requests'] == 0
    assert transport[0] == {}
    snapshot = run_monitor.progress(cfg, out)
    assert snapshot['jobs'] == {'failed': 1}
    assert snapshot['host_terminal'] is False


def test_terminal_signal_once_across_observer_restart(cfg, transport, monkeypatch):
    from es import run_review
    calls = []
    monkeypatch.setattr(run_review, 'build_review', lambda *a: calls.append(a) or {'artifact': {'id': 'receipt'}})
    _, state, _ = make_run(cfg, host_status='done', state_status='complete')
    for _ in range(4):
        run_monitor.tick(cfg)
    assert len(transport[0]) == len(calls) == 1
    event = next(iter(transport[0].values()))
    assert event['type'] == 'run_terminal'
    assert event['theorem_credit'] == 'not_inferred'
    assert event['review']['artifact']['id'] == 'receipt'


def test_stale_stopped_host_is_reconciled_then_signalled_once(cfg, transport, monkeypatch):
    from es import resources, run_review

    monkeypatch.setattr(run_review, 'build_review', lambda *a: {'artifact': {'id': 'receipt'}})
    out, _, host = make_run(cfg, state_status='complete')
    with Store(cfg) as st:
        st.job_update(host['id'], pid=1234, process_start='gone',
                      heartbeat_at=time.time()-300, scope_unit='stopped.scope')
    monkeypatch.setattr(jobs, 'process_identity', lambda pid: None)
    monkeypatch.setattr(resources, 'scope_stopped', lambda unit: unit == 'stopped.scope')

    for _ in range(4):
        run_monitor.tick(cfg)

    with Store(cfg) as st:
        reconciled = st.job(host['id'])
    assert reconciled['status'] == 'failed'
    assert json.loads(reconciled['result_json'])['runner_reconciled_from'] == 'running'
    assert run_monitor.progress(cfg, out)['host_terminal'] is True
    assert len(transport[0]) == 1
    assert next(iter(transport[0].values()))['type'] == 'run_terminal'


def test_crash_after_outbox_insert_reuses_frozen_review(cfg, monkeypatch):
    from es import run_delivery, run_review
    make_run(cfg, host_status='done', state_status='complete')
    reviews = []
    monkeypatch.setattr(run_review, 'build_review', lambda *a: reviews.append(a) or {'generation': len(reviews)})
    original_emit = run_delivery.emit
    inserted = []

    class ProcessCrash(BaseException):
        pass

    def crash_after_insert(*args):
        result = original_emit(*args)
        inserted.append(result)
        if len(inserted) == 1:
            raise ProcessCrash()
        return result

    monkeypatch.setattr(run_delivery, 'emit', crash_after_insert)
    with pytest.raises(ProcessCrash):
        run_monitor.tick(cfg)
    run_monitor.tick(cfg)
    assert len(reviews) == 1
    assert [r['created'] for r in inserted] == [True, False]
    assert run_delivery.status(cfg, 'tester')['events'] == {'pending': 1}


def test_observer_error_counts_actual_callback_submission(cfg, monkeypatch):
    from es import run_delivery
    make_run(cfg)
    monkeypatch.setattr(run_monitor, 'progress', lambda *a: (_ for _ in ()).throw(ValueError()))
    monkeypatch.setattr(run_delivery, 'dispatch', lambda *a: {'model_requests': 1})
    result = run_monitor.tick(cfg)
    assert result['runs'][0]['status'] == 'observer_error'
    assert result['model_requests'] == 1


def test_no_final_result_while_child_job_is_still_running(cfg, transport, monkeypatch):
    from es import run_review
    monkeypatch.setattr(run_review, 'build_review', lambda *a: {'artifact': {'id': 'done'}})
    make_run(cfg, host_status='done', state_status='complete')
    child = jobs.submit_run(cfg, command=['true'], why='pending check', outputs=['runs/native'],
                            agent='sol-test', memory_max='256M', queue=True)
    run_monitor.tick(cfg)
    assert next(iter(transport[0].values()))['reason'] == 'host_stopped_with_pending_jobs'
    with Store(cfg) as st:
        st.job_update(child['id'], status='done')
    run_monitor.tick(cfg)
    assert len(transport[0]) == 2
    assert list(transport[0].values())[-1]['type'] == 'run_terminal'


def test_unknown_scope_beyond_compact_list_is_escalated_once(cfg, transport, monkeypatch):
    from es import resources
    policy(cfg, unknown_execution_grace_seconds=0)
    make_run(cfg)
    unknown = None
    for n in range(10):
        job = jobs.submit_run(cfg, command=['true'], why=f'job {n}', outputs=['runs/native'],
                              agent='sol-test', memory_max='256M', queue=True)
        if n == 9:
            unknown = job['id']
            with Store(cfg) as st:
                st.job_update(unknown, status='unknown_execution')
    monkeypatch.setattr(resources, 'reconcile', lambda cfg: {'unknown_execution': [unknown]})
    run_monitor.tick(cfg)
    run_monitor.tick(cfg)
    assert len(transport[0]) == 1
    assert next(iter(transport[0].values()))['unresolved_job_ids'] == [unknown]


@pytest.mark.parametrize('code,status,expired,cancelled', [
    ('usageLimitExceeded', 'blocked', False, False),
    ('serverOverloaded', 'paused', False, False),
    ('serverOverloaded', 'blocked', True, False),
    ('serverOverloaded', 'blocked', False, True),
])
def test_recovery_never_resets_limits_pause_deadline_or_cancel(cfg, transport, monkeypatch, code, status, expired, cancelled):
    from es import run_review
    monkeypatch.setattr(run_review, 'build_review', lambda *a: {})
    policy(cfg, provider_capacity_retries=1)
    out, state, host = make_run(cfg, host_status='failed', state_status='goal_blocked')
    state.update(goal={'status': status, 'updatedAt': 100}, progress={
        'last_turn_status': 'failed', 'last_turn_error_code': code, 'last_turn_completed_at': 101})
    if expired:
        state['timing']['deadline_at'] = agent_run._utc(time.time() - 1)
    if cancelled:
        with Store(cfg) as st:
            st.job_update(host['id'], cancel_requested=1)
    agent_run._atomic_json(out / agent_run.STATE_NAME, state)
    monkeypatch.setattr(agent_run, 'submit_agent_run', lambda *a, **k: pytest.fail('must not retry'))
    run_monitor.tick(cfg)
    assert len(transport[0]) == 1


def test_capacity_retry_once_and_uncertain_submission_is_not_replayed(cfg, transport, monkeypatch):
    from es import run_review
    monkeypatch.setattr(run_review, 'build_review', lambda *a: {})
    policy(cfg, provider_capacity_retries=1)
    out, state, host = make_run(cfg, host_status='failed', state_status='goal_blocked')
    state.update(goal={'status': 'blocked', 'updatedAt': 100}, progress={
        'last_turn_status': 'failed', 'last_turn_error_code': 'serverOverloaded', 'last_turn_completed_at': 101})
    agent_run._atomic_json(out / agent_run.STATE_NAME, state)
    attempts = []
    def lost(*a, **k):
        attempts.append(k)
        raise OSError('lost response')
    monkeypatch.setattr(agent_run, 'submit_agent_run', lost)
    run_monitor.tick(cfg)
    run_monitor.tick(cfg)
    assert len(attempts) == 1
    assert attempts[0]['resume'] is True
    assert len(transport[0]) == 1


def test_successful_retry_preserves_thread_and_deadline(cfg, transport, monkeypatch):
    policy(cfg, provider_capacity_retries=1)
    out, state, _ = make_run(cfg, host_status='failed', state_status='goal_blocked')
    state.update(thread_id='same-thread', goal={'status': 'blocked', 'updatedAt': 100}, progress={
        'last_turn_status': 'failed', 'last_turn_error_code': 'serverOverloaded', 'last_turn_completed_at': 101})
    agent_run._atomic_json(out / agent_run.STATE_NAME, state)
    calls = []
    def resumed(*a, **k):
        calls.append(k)
        return {'job': {'id': 'replacement-host'}}
    monkeypatch.setattr(agent_run, 'submit_agent_run', resumed)
    assert run_monitor.tick(cfg)['runs'][0]['status'] == 'capacity_retry_submitted'
    assert run_monitor.tick(cfg)['runs'][0]['status'] == 'capacity_retry_submitted'
    assert len(calls) == 1 and transport[0] == {}
    current = agent_run._read_state(out)
    assert current['thread_id'] == 'same-thread' and current['timing'] == state['timing']


def test_wrong_root_or_owner_cannot_register(cfg):
    out, state, _ = make_run(cfg)
    with pytest.raises(UsageError, match='coordinator'):
        run_monitor.register(cfg, out, 'other')
    state['root'] = '/tmp/another-checkout'
    agent_run._atomic_json(out / agent_run.STATE_NAME, state)
    with pytest.raises(UsageError, match='root'):
        run_monitor.progress(cfg, out)


def test_pause_stops_observer_without_cancelling_jobs(cfg, transport):
    out, _, host = make_run(cfg)
    run_monitor.pause(cfg, out, 'tester')
    assert run_monitor.tick(cfg)['runs'] == []
    with Store(cfg) as st:
        assert st.job(host['id'])['status'] == 'running'
