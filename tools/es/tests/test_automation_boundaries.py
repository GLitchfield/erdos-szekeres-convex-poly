import ast
from concurrent.futures import ThreadPoolExecutor
import json
from pathlib import Path
import random
import shutil
import sys
import time

import pytest

from es import delivery, operations, proofs, resources, usage
from es.artifacts import put_json, read
from es.build import run_guarded
from es.client_delivery import dispatch_one
from es.errors import UsageError
from es.jobs import reserve_job
from es.store import Store

ROOT=Path(__file__).resolve().parents[3]


def test_command_stage_overrides_worker_root_and_inherits_guard(cfg, monkeypatch):
    from types import SimpleNamespace
    monkeypatch.delenv('ES_WINDOW_ID', raising=False)
    monkeypatch.setenv('ES_PROJECT_ROOT', '/wrong-worker-checkout')
    op = operations.submit(cfg, 'tester', {'schema_version': 1, 'stages': [
        {'name': 'register', 'action': 'command', 'argv': ['es', 'node', 'add'],
         'memory': '1G'}]})
    job_id = op['stages'][0]['job_id']
    assert reserve_job(cfg, job_id)
    with Store(cfg) as st:
        job = st.job(job_id)
    monkeypatch.setattr(operations, 'load_config', lambda root: cfg)
    observed = {}
    def guarded(config, argv, **kwargs):
        observed.update(kwargs)
        return SimpleNamespace(rc=0, budget_exceeded=False, refused=None,
                               seconds=0, peak_mib=1, termination_acknowledged=True)
    monkeypatch.setattr(operations, 'run_guarded', guarded)
    operations.execute_stage(cfg, job)
    assert observed['cwd'] == cfg.root
    assert observed['env_extra']['ES_PROJECT_ROOT'] == str(cfg.root)
    assert observed['env_extra']['ES_IN_GUARDED_STAGE'] == '1'
    assert observed['env_extra']['ES_STAGE_MEMORY'] == '1G'
    assert operations.show(cfg, op['id'])['status'] == 'succeeded'


def test_proof_span_unicode_comments_and_nested_defaults():
    source='namespace T\n/- theorem foo : False := by sorry /- nested -/ -/\ntheorem foo (n : Nat := 0) : n = n := by\n  have h : n = n := by rfl\n  exact h\nend T\n'
    a,b=proofs.whole_span(source,'foo')
    assert source.encode()[a:b].decode()=='by\n  have h : n = n := by rfl\n  exact h'
    with pytest.raises(UsageError):
        proofs.whole_span(source+source,'foo')
    source='theorem foo : True := by trivial\n/-- Preserve the following declaration metadata. -/\ntheorem bar : True := by trivial\n'
    a,b=proofs.whole_span(source,'foo')
    assert source.encode()[a:b]==b'by trivial'
    assert b'Preserve' in source.encode()[b:]


def test_proof_span_preserves_let_bindings_in_result_type():
    source = ('namespace T\ntheorem foo (n : Nat := 0) :\n'
              '  let A := n + 1\n  let B := (let k := 2; k + A)\n'
              '  A ≤ B := by\n  dsimp\n  omega\nend T\n')
    a, b = proofs.whole_span(source, 'foo')
    assert source.encode()[a:b].decode() == 'by\n  dsimp\n  omega'
    replaced = source.encode()[:a] + b'by exact Nat.le_add_left _ _' + source.encode()[b:]
    assert b'let A := n + 1\n  let B := (let k := 2; k + A)' in replaced


def test_compact_operation_keeps_current_job_without_old_retry_outcome(cfg):
    from es.artifacts import compact
    payload = {'id': 'op-example', 'status': 'running', 'spec': {'body': 'x' * 10000},
               'result': {'proof_accepted': False, 'outcome': 'previous_attempt_failed',
                          'diagnostic_summary': {'errors': ['old error']},
                          'candidate_file': '/old/Candidate.lean'},
               'stages': [{'name': 'candidate', 'status': 'succeeded', 'job_id': 'job-1'},
                          {'name': 'original-source', 'status': 'running', 'job_id': 'job-2',
                           'attempt': 2}, {'name': 'full-extract', 'status': 'pending'}]}
    brief = compact(cfg, payload)
    assert brief['stage'] == {'name': 'original-source', 'status': 'running',
                              'job_id': 'job-2', 'attempt': 2}
    assert (brief['stages_done'], brief['stages_total']) == (1, 3)
    assert 'outcome' not in brief and 'proof_accepted' not in brief
    assert 'diagnostic_summary' not in brief and 'candidate_file' not in brief
    assert json.loads(read(cfg, brief['detail']['id'])) == payload


def test_small_operation_replies_keep_the_same_summary_fields(cfg):
    from es.artifacts import compact

    payload = {'id': 'op-small', 'status': 'running', 'stages': [
        {'name': 'candidate', 'status': 'succeeded', 'job_id': 'first'},
        {'name': 'review', 'status': 'running', 'job_id': 'second', 'attempt': 2}],
        'result': {'outcome': 'old_failure', 'proof_accepted': False}}
    small = compact(cfg, payload)
    large = compact(cfg, {**payload, 'spec': {'padding': 'x' * 8000}})
    for key in ('id', 'status', 'stage', 'stages_done', 'stages_total'):
        assert small[key] == large[key]
    assert small['stage']['job_id'] == 'second'
    assert 'outcome' not in small and 'proof_accepted' not in small
    assert 'detail' not in small and 'detail' in large
    assert small['stages'] == payload['stages']
    finished = compact(cfg, {**payload, 'status': 'succeeded',
                            'result': {'proof_accepted': True, 'published': False}})
    assert finished['proof_accepted'] and not finished['published']


def test_compiler_headers_are_bounded_and_point_into_utf8_diagnostics(cfg):
    from es.artifacts import canonical, compact, put

    raw = ('α context\nCandidate.lean:12:3: error: unsolved goals\n'
           + 'Candidate.lean:13:7: error(lean.unknownIdentifier): Unknown constant `Nat.min_le_min_right`\n'
           + 'huge context\n' * 1000
           + ''.join(f'Candidate.lean:{20+i}:4: error: '+ 'λ' * 1000 + '\n' for i in range(10))).encode()
    summary = proofs.diagnostic_summary(raw)
    assert summary['error_count'] == 12 and summary['truncated']
    assert len(canonical(summary)) < 2048
    first = summary['errors'][0]
    assert (first['line'], first['column'], first['message']) == (12, 3, 'unsolved goals')
    assert raw[first['log_byte_offset']:].startswith(b'Candidate.lean:12:3: error:')
    tagged = summary['errors'][1]
    assert (tagged['line'], tagged['column']) == (13, 7)
    assert tagged['message'] == 'Unknown constant `Nat.min_le_min_right`'
    assert raw[tagged['log_byte_offset']:].startswith(b'Candidate.lean:13:7: error(lean.unknownIdentifier):')
    diagnostic = put(cfg, raw, 'text/plain')
    payload = {'id': 'op-failed', 'status': 'failed', 'spec': {'large': 'x' * 10000},
               'result': {'proof_accepted': False, 'outcome': 'compile_failed',
                          'diagnostic_summary': summary, 'diagnostic': diagnostic,
                          'candidate_file': '/owned/Candidate.lean'}}
    brief = compact(cfg, payload)
    assert brief['diagnostic_summary'] == summary
    assert read(cfg, brief['diagnostic']['id']) == raw
    assert brief['candidate_file'] == '/owned/Candidate.lean'
    assert len(canonical(brief)) < 4096


def test_source_and_dependency_changes_refused(cfg):
    source=cfg.root/'TBlueprint/A/Foo.lean'
    f={'file':'TBlueprint/A/Foo.lean','source_hash':proofs.digest(source),'dependencies':{'TCore/Basic.lean':proofs.digest(cfg.root/'TCore/Basic.lean')},'standard_axioms':cfg.standard_axioms}
    proofs.validate(cfg,f)
    (cfg.root/'TCore/Basic.lean').write_text('theorem different : True := trivial')
    with pytest.raises(UsageError,match='dependency changed'): proofs.validate(cfg,f)


def test_dead_runner_never_replayed_and_keeps_reservation(cfg):
    request={'schema_version':1,'stages':[{'name':'work','action':'command','argv':['true'],'memory':'25G'}]}
    op=operations.submit(cfg,'tester',request)
    job=op['stages'][0]['job_id']
    with Store(cfg) as st:
        st.job_update(job,status='running',pid=99999999,process_start='gone',heartbeat_at=time.time()-300)
    assert operations.reconcile(cfg)['unknown_execution']==[job]
    unknown=operations.show(cfg,op['id'])
    assert unknown['status']=='unknown_execution'
    assert unknown['result']['termination_acknowledged'] is False
    cancel=operations.control(cfg,op['id'],'cancel')
    assert cancel['status']=='unknown_execution'
    assert cancel['result']==unknown['result']
    with Store(cfg) as st:
        assert st.job(job)['status']=='unknown_execution'
        assert st.job(job)['cancel_requested']==1
    with pytest.raises(UsageError): operations.control(cfg,op['id'],'retry')
    other=operations.submit(cfg,'tester',{'schema_version':1,'stages':[{'name':'other','action':'command','argv':['true'],'memory':'10G','lock':'other'}]})
    assert not reserve_job(cfg,other['stages'][0]['job_id'],launching=True)


def test_cancel_running_requires_owner_ack(cfg):
    op=operations.submit(cfg,'tester',{'schema_version':1,'stages':[{'name':'work','action':'command','argv':['true'],'memory':'1G'}]})
    job=op['stages'][0]['job_id']
    assert reserve_job(cfg,job)
    cancel=operations.control(cfg,op['id'],'cancel')
    assert cancel['status']=='cancel_requested'
    assert cancel['result'].get('termination_acknowledged') is not True
    with Store(cfg) as st: requested=st.job(job)
    assert requested['status']=='running'
    assert requested['cancel_requested']==1
    result=run_guarded(cfg,[sys.executable,'-c','import time; time.sleep(20)'],log_path=cfg.root/'cancel.log',budget_min=1,memory_max='1G',force=True,count_built=False,job_id=job)
    assert result.seconds < 5
    assert not result.budget_exceeded


def test_scope_stopped_requires_definite_systemd_state(monkeypatch):
    from types import SimpleNamespace

    def result(stdout, returncode=0):
        return SimpleNamespace(stdout=stdout, returncode=returncode)

    monkeypatch.setattr(resources.subprocess, 'run', lambda *args, **kwargs: result('ActiveState=failed\nLoadState=loaded\n'))
    assert resources.scope_stopped('failed.scope') is True
    monkeypatch.setattr(resources.subprocess, 'run', lambda *args, **kwargs: result('ActiveState=active\nLoadState=loaded\n'))
    assert resources.scope_stopped('live.scope') is False
    monkeypatch.setattr(resources.subprocess, 'run', lambda *args, **kwargs: result('ActiveState=inactive\nLoadState=not-found\n', returncode=4))
    assert resources.scope_stopped('collected.scope') is True
    monkeypatch.setattr(resources.subprocess, 'run', lambda *args, **kwargs: result('', returncode=1))
    assert resources.scope_stopped('hidden-bus.scope') is None


def test_wait_scope_stopped_acknowledges_delayed_teardown(monkeypatch):
    states = iter([False, False, True])
    monkeypatch.setattr(resources, 'scope_stopped', lambda unit: next(states))
    monkeypatch.setattr(resources.time, 'sleep', lambda seconds: None)
    assert resources.wait_scope_stopped('finishing.scope') is True


def test_wait_scope_stopped_preserves_bus_uncertainty(monkeypatch):
    calls = []
    monkeypatch.setattr(resources, 'scope_stopped', lambda unit: calls.append(unit))
    monkeypatch.setattr(resources.time, 'sleep', lambda seconds: pytest.fail('an unavailable bus must not be polled'))
    assert resources.wait_scope_stopped('hidden-bus.scope') is None
    assert calls == ['hidden-bus.scope']


def test_wait_scope_stopped_does_not_acknowledge_live_scope(monkeypatch):
    monkeypatch.setattr(resources, 'scope_stopped', lambda unit: False)
    monkeypatch.setattr(resources.time, 'sleep', lambda seconds: pytest.fail('a zero deadline must not sleep'))
    assert resources.wait_scope_stopped('live.scope', timeout_s=0) is False


def test_guarded_success_waits_for_scope_teardown(cfg, monkeypatch):
    from es import build

    class FinishedProcess:
        pid = 12345
        returncode = 0

        def wait(self, timeout=None):
            return self.returncode

    cfg.raw.setdefault('build', {})['guard'] = True
    monkeypatch.setattr(build.shutil, 'which', lambda name: '/usr/bin/systemd-run')
    monkeypatch.setattr(build.subprocess, 'Popen', lambda *args, **kwargs: FinishedProcess())
    states = iter([False, True])
    monkeypatch.setattr(resources, 'scope_stopped', lambda unit: next(states))
    monkeypatch.setattr(resources.time, 'sleep', lambda seconds: None)

    result = run_guarded(cfg, ['true'], log_path=cfg.root/'guarded-success.log',
                         budget_min=1, memory_max='1G', force=True, count_built=False)

    assert result.ok
    assert result.termination_acknowledged is True
    with Store(cfg) as st:
        assert st.conn.execute('SELECT COUNT(*) FROM resource_leases').fetchone()[0] == 0


def test_unknown_execution_reconcile_preserves_receipt(cfg, monkeypatch):
    op=operations.submit(cfg,'tester',{'schema_version':1,'stages':[{'name':'work','action':'command','argv':['true'],'memory':'1G'}]})
    job=op['stages'][0]['job_id']
    receipt={'error':'runner disappeared','artifact':{'id':'receipt-1'},'termination_acknowledged':False}
    with Store(cfg) as st:
        st.job_update(job,status='unknown_execution',pid=None,scope_unit='stopped.scope',result_json=json.dumps(receipt))
        st.conn.execute("UPDATE operation_stages SET status='unknown_execution',result_json=? WHERE operation_id=? AND ordinal=0",
                        (json.dumps(receipt),op['id']))
        st.conn.execute("UPDATE operations SET status='unknown_execution',result_json=? WHERE id=?",
                        (json.dumps({'stage':'work','job_id':job,'proof_accepted':False,'termination_acknowledged':False}),op['id']))
    monkeypatch.setattr(resources, 'scope_stopped', lambda unit: True)
    result=resources.reconcile(cfg)
    assert result['released_reservations']==[job]
    with Store(cfg) as st: reconciled=st.job(job)
    assert reconciled['status']=='failed'
    evidence=json.loads(reconciled['result_json'])
    assert evidence['error']=='runner disappeared'
    assert evidence['artifact']=={'id':'receipt-1'}
    assert evidence['execution_reconciled']=='scope_stopped'
    assert evidence['effects']=='require_review'
    assert evidence['termination_acknowledged'] is True
    cancelled=operations.control(cfg,op['id'],'cancel')
    assert cancelled['status']=='cancelled'
    assert cancelled['result']['status']=='cancelled'
    assert cancelled['result']['termination_acknowledged'] is True
    assert cancelled['result']['execution_reconciled']=='scope_stopped'
    assert cancelled['result']['effects']=='require_review'


def test_unknown_execution_reconcile_fails_closed_for_live_runner(cfg, monkeypatch):
    from es import jobs

    op=operations.submit(cfg,'tester',{'schema_version':1,'stages':[{'name':'work','action':'command','argv':['true'],'memory':'1G'}]})
    job=op['stages'][0]['job_id']
    with Store(cfg) as st:
        st.job_update(job,status='unknown_execution',pid=1234,process_start='same',scope_unit='live.scope')
    monkeypatch.setattr(jobs, 'process_identity', lambda pid: 'same')
    monkeypatch.setattr(resources, 'scope_stopped', lambda unit: pytest.fail('live runner must not be released from scope state alone'))
    result=resources.reconcile(cfg)
    assert result['released_reservations']==[]
    assert result['unknown_execution']==[job]
    with Store(cfg) as st: assert st.job(job)['status']=='unknown_execution'


def test_stale_running_job_reconciles_only_after_runner_and_scope_stop(cfg, monkeypatch):
    from es import jobs

    job = jobs.submit_run(cfg, command=['true'], why='test stale guarded runner',
                          outputs=['runs/result'], agent='tester', memory_max='1G', queue=True)['id']
    receipt = {'error': 'runner disappeared', 'artifact': {'id': 'receipt-1'}}
    with Store(cfg) as st:
        st.job_update(job, status='running', pid=1234, process_start='old',
                      heartbeat_at=time.time()-300, scope_unit='stopped.scope',
                      result_json=json.dumps(receipt))
    monkeypatch.setattr(jobs, 'process_identity', lambda pid: 'old')
    monkeypatch.setattr(resources, 'scope_stopped',
                        lambda unit: pytest.fail('a live runner must not be reconciled'))
    assert resources.reconcile(cfg)['released_reservations'] == []
    with Store(cfg) as st:
        assert st.job(job)['status'] == 'running'

    monkeypatch.setattr(jobs, 'process_identity', lambda pid: None)
    monkeypatch.setattr(resources, 'scope_stopped', lambda unit: False)
    assert resources.reconcile(cfg)['unknown_execution'] == [job]
    with Store(cfg) as st:
        assert st.job(job)['status'] == 'running'

    monkeypatch.setattr(resources, 'scope_stopped', lambda unit: unit == 'stopped.scope')

    result = resources.reconcile(cfg)

    assert result['released_reservations'] == [job]
    with Store(cfg) as st:
        reconciled = st.job(job)
    assert reconciled['status'] == 'failed'
    assert reconciled['exit_code'] == 1
    assert reconciled['finished_at'] is not None
    evidence = json.loads(reconciled['result_json'])
    assert evidence == {
        'artifact': {'id': 'receipt-1'},
        'effects': 'require_review',
        'error': 'runner disappeared',
        'execution_reconciled': 'scope_stopped',
        'runner_reconciled_from': 'running',
        'termination_acknowledged': True,
    }


def test_stale_running_reconcile_preserves_restarted_runner(cfg, monkeypatch):
    from es import jobs

    job = jobs.submit_run(cfg, command=['true'], why='test runner restart race',
                          outputs=['runs/result'], agent='tester', memory_max='1G', queue=True)['id']
    with Store(cfg) as st:
        st.job_update(job, status='running', pid=1234, process_start='old',
                      heartbeat_at=time.time()-300, scope_unit='old.scope')
    monkeypatch.setattr(jobs, 'process_identity', lambda pid: None)

    def restart_during_scope_probe(unit):
        with Store(cfg) as st:
            st.job_update(job, pid=5678, process_start='new', heartbeat_at=time.time(),
                          scope_unit='new.scope')
        return True

    monkeypatch.setattr(resources, 'scope_stopped', restart_during_scope_probe)
    result = resources.reconcile_stale_jobs(cfg)

    assert result['released_reservations'] == []
    assert result['unknown_execution'] == [job]
    with Store(cfg) as st:
        preserved = st.job(job)
    assert preserved['status'] == 'running'
    assert preserved['pid'] == 5678
    assert preserved['process_start'] == 'new'
    assert preserved['scope_unit'] == 'new.scope'


def test_cancel_accepts_legacy_stopped_scope_receipt(cfg):
    op=operations.submit(cfg,'tester',{'schema_version':1,'stages':[{'name':'work','action':'command','argv':['true'],'memory':'1G'}]})
    job=op['stages'][0]['job_id']
    legacy={'execution_reconciled':'scope_stopped','effects':'require_review'}
    with Store(cfg) as st:
        st.job_update(job,status='failed',result_json=json.dumps(legacy))
        st.conn.execute("UPDATE operation_stages SET status='unknown_execution' WHERE operation_id=? AND ordinal=0",(op['id'],))
        st.conn.execute("UPDATE operations SET status='unknown_execution',result_json=? WHERE id=?",
                        (json.dumps({'termination_acknowledged':False}),op['id']))
    cancelled=operations.control(cfg,op['id'],'cancel')
    assert cancelled['status']=='cancelled'
    assert cancelled['result']['status']=='cancelled'
    assert cancelled['result']['termination_acknowledged'] is True
    assert cancelled['result']['execution_reconciled']=='scope_stopped'
    assert cancelled['result']['effects']=='require_review'


def test_nested_cap_cannot_escape_reservation(cfg,monkeypatch):
    monkeypatch.setenv('ES_IN_GUARDED_STAGE','1')
    monkeypatch.setenv('ES_STAGE_MEMORY','1G')
    result=run_guarded(cfg,['must-not-run'],log_path=cfg.root/'log',budget_min=1,memory_max='2G')
    assert 'above enclosing cap' in result.refused


def test_at_least_once_delivery_disconnect_and_pause(cfg):
    op=operations.submit(cfg,'tester',{'schema_version':1,'stages':[{'name':'work','action':'command','argv':['true'],'memory':'999G'}]})
    event=delivery.claim(cfg,'tester','lost-client')
    with Store(cfg) as st: st.conn.execute('UPDATE deliveries SET lease_until=0')
    recovered=delivery.claim(cfg,'tester','new-client')
    assert recovered['event_id']==event['event_id']
    assert recovered['attempt']==2
    with pytest.raises(UsageError): delivery.ack(cfg,'tester',event['event_id'],'lost-client')
    delivery.ack(cfg,'tester',event['event_id'],'new-client')


class FakeClient:
    def __init__(self,busy=False,lose_reply=False): self.busy=busy; self.lose_reply=lose_reply; self.turns=[]; self.calls=[]
    def request(self,method,params):
        self.calls.append(method)
        if method=='thread/read': return {'thread':{'status':{'type':'active' if self.busy else 'idle'},'turns':self.turns if params.get('includeTurns') else []}}
        if method=='turn/start':
            self.turns.append(params)
            if self.lose_reply: raise UsageError('lost acknowledgement')
            return {'turn':{'id':'turn-1'}}
        raise AssertionError(method)


def test_client_loss_after_submission_reconciles_without_second_turn(cfg):
    cfg.raw.setdefault('automation',{})['delivery']={'enabled':True,'bindings':{'tester':{'thread':'thread-1','enabled':True}}}
    operations.submit(cfg,'tester',{'schema_version':1,'stages':[{'name':'work','action':'command','argv':['true'],'memory':'999G'}]})
    client=FakeClient(busy=True)
    assert dispatch_one(cfg,'tester','thread-1',client,'client')['model_requests']==0
    client.busy=False;client.lose_reply=True
    with pytest.raises(UsageError): dispatch_one(cfg,'tester','thread-1',client,'client')
    with Store(cfg) as st: st.conn.execute('UPDATE deliveries SET lease_until=0')
    assert dispatch_one(cfg,'tester','thread-1',client,'client')['status']=='reconciled'
    assert client.calls.count('turn/start')==1
    assert delivery.pending(cfg,'tester')==[]


def test_large_terminal_delivery_preserves_evidence_without_large_model_input(cfg):
    cfg.raw.setdefault('automation', {})['delivery'] = {
        'enabled': True, 'bindings': {'tester': {'thread': 'thread-1', 'enabled': True}}}
    op = operations.submit(cfg, 'tester', {'schema_version': 1, 'stages': [
        {'name': 'work', 'action': 'command', 'argv': ['true'], 'memory': '999G'}]})
    payload = {'operation_id': op['id'], 'status': 'failed',
               'result': {'proof_accepted': False, 'outcome': 'compile_failed',
                          'diagnostic': 'large diagnostic λ' * 100000}}
    with Store(cfg) as st:
        st.conn.execute('UPDATE deliveries SET payload_json=? WHERE operation_id=?',
                        (json.dumps(payload), op['id']))
    client = FakeClient()
    result = dispatch_one(cfg, 'tester', 'thread-1', client, 'client')
    text = client.turns[0]['input'][0]['text']
    assert len(text.encode()) < 1024
    packet = json.loads(text.split('\n', 1)[1])
    assert packet['proof_accepted'] is False
    assert json.loads(read(cfg, packet['detail']['id'])) == payload
    assert dispatch_one(cfg, 'tester', 'thread-1', client, 'client')['status'] == 'no_delivery'
    assert result['model_requests'] == client.calls.count('turn/start') == 1


def test_delivery_storage_failure_does_not_record_submission_intent(cfg, monkeypatch):
    import es.client_delivery as adapter
    cfg.raw.setdefault('automation', {})['delivery'] = {
        'enabled': True, 'bindings': {'tester': {'thread': 'thread-1', 'enabled': True}}}
    operations.submit(cfg, 'tester', {'schema_version': 1, 'stages': [
        {'name': 'work', 'action': 'command', 'argv': ['true'], 'memory': '999G'}]})
    def refused(*args):
        raise OSError('disk full')
    monkeypatch.setattr(adapter, 'put_json', refused)
    client = FakeClient()
    with pytest.raises(OSError, match='disk full'):
        dispatch_one(cfg, 'tester', 'thread-1', client, 'client')
    assert 'turn/start' not in client.calls
    with Store(cfg) as st:
        assert st.conn.execute("SELECT count(*) FROM automation_meta WHERE key LIKE 'delivery-intent:%'").fetchone()[0] == 0


def old_function(path,names):
    tree=ast.parse(path.read_text())
    code=ast.Module(body=[n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name in names],type_ignores=[])
    namespace={'math':__import__('math')}
    exec(compile(code,str(path),'exec'),namespace)
    return namespace


def test_retained_search_primitives_match_originals():
    sys.path.insert(0,str(ROOT))
    from harness.research import primitives as new
    base=ROOT/'runs/2026-09-10-active-lean-research'
    if not base.exists(): pytest.skip('historical parity artifacts not present in this checkout')
    old=old_function(base/'abstract_rank_strip_probe.py',{'P','clip'})
    ext=old_function(base/'rank_saturation_diagnostic_common.py',{'extension'})['extension']
    covers=old_function(base/'maximum_thin_clear_history_transfer_probe.py',{'sideat','actual','maximum_bounds','ordered_cover','sole_opposite_normalize'})
    rng=random.Random(20260912)
    for _ in range(100):
        rows=[[1,2,1,rng.randrange(2,10)] for i in range(rng.randrange(2,10))]
        keep=set(range(0,len(rows),2))
        assert new.P(rows)==old['P'](rows)
        for axis in (0,1): assert new.clip(rows,keep,axis)==old['clip'](rows,keep,axis)
        word=['S',(1,'lower'),'S',(2,'upper'),'S']
        for side in ('lower','upper'):
            for left in (False,True): assert new.extension(word,2,side,2,left)==ext(word,2,side,2,left)
        row={'word':word,'maxima':[1,2],'chosen':'upper','a':5,'u':5,'k':5}
        assert new.maximum_bounds(row)==covers['maximum_bounds'](row)
        rec={'rectangles':[[i,*r] for i,r in enumerate(rows)]}
        assert new.ordered_cover(rec)==covers['ordered_cover'](rec)
        assert new.sole_opposite_normalize(row)==covers['sole_opposite_normalize'](row)


def test_probe_known_witness_replay_and_bounded_negative():
    sys.path.insert(0,str(ROOT))
    from harness.research.context_rank import evaluate,replay
    spec={'semantics':'abstract-rank-strip-v1','domain':'abstract_interval_family',
          'generator':{'name':'sorted_intervals','seed':202609101509},'candidate':{'name':'clipped_potential'},'budget':{'cases':10000,'seconds':5}}
    value=evaluate(spec)
    assert value['outcome']=='witness_found'
    assert replay(value['witness'])['replayed']
    assert not value['lean_refutation']
    spec['budget']['cases']=1
    assert evaluate(spec)['coverage']['exhaustive'] is False
    spec['semantics']='implicit'
    with pytest.raises(ValueError): evaluate(spec)


def test_cli_global_json_is_not_lost_after_subcommand():
    from es.cli import build_parser
    assert build_parser().parse_args(['--json','job','list']).json


def test_runner_uses_submitted_worktree_for_nested_es(cfg, monkeypatch, tmp_path):
    from es.config import load_config
    from es.jobs import submit_run,run_job

    worker_root=tmp_path/'other-worktree'
    shutil.copytree(cfg.root,worker_root,ignore=shutil.ignore_patterns('.git'))
    worker_cfg=load_config(worker_root)
    monkeypatch.setenv('ES_PROJECT_ROOT',str(worker_root))
    monkeypatch.setenv('ES_EXTRACT_MEMORY_MAX','512M')
    output='runs/nested-env.json'
    script=(
        "import json,os,subprocess,sys;from pathlib import Path;"
        "p=subprocess.run([sys.executable,'-m','es','--json','doctor'],capture_output=True,text=True);"
        "Path('runs/nested-env.json').write_text(json.dumps({"
        "'returncode':p.returncode,'stdout':p.stdout,'stderr':p.stderr,"
        "'env':{k:os.environ.get(k) for k in "
        "('ES_AGENT','ES_JOB_ID','ES_PROJECT_ROOT','ES_STAGE_MEMORY','ES_IN_GUARDED_STAGE','ES_EXTRACT_MEMORY_MAX')}}))"
    )
    job=submit_run(cfg,command=[sys.executable,'-c',script],why='nested es root regression',outputs=[output],agent='submitted-agent',memory_max='1G',queue=True)
    finished=run_job(worker_cfg,job['id'])
    result=json.loads(finished['result_json'])
    assert result['outputs_missing']==[]
    assert result['outputs_present']==[output]
    record=json.loads((cfg.root/output).read_text())
    nested=json.loads(record['stdout'])
    config=next(check for check in nested['checks'] if check['name']=='config')
    assert config['detail']==str(cfg.root/'harness/config.toml')
    assert record['env']=={
        'ES_AGENT':'submitted-agent',
        'ES_JOB_ID':job['id'],
        'ES_PROJECT_ROOT':str(cfg.root),
        'ES_STAGE_MEMORY':'1G',
        'ES_IN_GUARDED_STAGE':'1',
        'ES_EXTRACT_MEMORY_MAX':'36G',
    }


def test_missing_usage_is_unknown_and_conflicting_duplicate_rolls_back(cfg,tmp_path):
    ident=usage.begin(cfg,'tester','no recorded requests')
    assert usage.report(cfg,ident)['usage']['output_tokens'] is None
    from test_automation import write_usage
    path=tmp_path/'conflict.jsonl';write_usage(path,10)
    lines=path.read_text().splitlines();other=json.loads(lines[-1]);other['payload']['usage']['output_tokens']=20
    path.write_text('\n'.join(lines+[json.dumps(other)])+'\n')
    with pytest.raises(UsageError,match='conflicting duplicate'): usage.ingest(cfg,path,ident)
    assert usage.report(cfg,ident)['responses']==0


def test_compact_read_preserved_when_artifact_store_unavailable(cfg,monkeypatch):
    from es import artifacts
    def refused(*args,**kwargs): raise PermissionError('read-only mount')
    monkeypatch.setattr(artifacts,'put_json',refused)
    payload={'nodes':['large record'*1000]}
    result=artifacts.compact(cfg,payload)
    assert result['nodes']==payload['nodes']
    assert result['compact_unavailable']


def test_compact_frontier_keeps_freshness_and_ready_choices(cfg):
    from es.artifacts import compact
    payload = {'counts': {'closed': 208, 'open': 12, 'refuted': 1},
               'stale': ['source changed'], 'problems': [],
               'nodes': [{'type_pp': 'large Lean type ' * 10000}]}
    brief = compact(cfg, payload)
    assert brief['counts'] == payload['counts']
    assert brief['stale_count'] == 1 and brief['stale'] == ['source changed']
    assert brief['problems_count'] == 0 and brief['problems'] == []
    assert json.loads(read(cfg, brief['detail']['id'])) == payload
    ready = {'ready': [{'name': f'project.node_{i}', 'description': 'useful goal',
                        'type_pp': 'large Lean type ' * 1000} for i in range(11)]}
    brief = compact(cfg, ready)
    assert brief['ready_count'] == 11
    assert [n['name'] for n in brief['ready_nodes']] == [f'project.node_{i}' for i in range(4)]
    assert len(json.dumps(brief).encode()) < 4096
    assert json.loads(read(cfg, brief['detail']['id'])) == ready


def test_full_output_and_utf8_pagination(cfg):
    from es.context import Ctx
    from es.commands.automation import result,artifact
    from es.artifacts import put
    ctx=Ctx(cfg);ctx.full_output=True
    payload={'diagnostic':'x'*10000}
    assert result(ctx,payload).payload==payload
    ident=put(cfg,'aβc'.encode(),'text/plain')['id']
    page=artifact(ctx,ident,limit=2).payload
    assert page['text']=='a' and page['next_offset']==1
    assert artifact(ctx,ident,offset=1,limit=2).payload['text']=='β'
