"""Reconcile reservations only after evidence that their process tree stopped."""
import json
import subprocess
import time

from es.artifacts import canonical
from es.store import Store


def scope_stopped(unit):
    if not unit: return None
    try:
        result = subprocess.run(['systemctl','--user','show',unit,'--property=ActiveState','--property=LoadState'],capture_output=True,text=True,timeout=5)
    except (OSError,subprocess.TimeoutExpired): return None
    fields = dict(line.split('=',1) for line in result.stdout.splitlines() if '=' in line)
    # A transient unit that systemd has already collected can be reported as
    # not-found with a nonzero exit status.  The missing unit is still definite
    # evidence that its cgroup is gone; other command failures remain unknown.
    if fields.get('LoadState') == 'not-found':
        return True
    if result.returncode or 'ActiveState' not in fields:
        return None
    return fields['ActiveState'] in ('inactive','failed')


def wait_scope_stopped(unit, timeout_s=5.0, poll_s=0.05):
    """Wait briefly for systemd's asynchronous active-to-stopped transition.

    An unavailable bus is not evidence about the cgroup, so return uncertainty
    immediately.  A scope that stays active through the deadline is likewise
    left for explicit reconciliation rather than releasing its reservation.
    """
    deadline = time.monotonic() + timeout_s
    while True:
        stopped = scope_stopped(unit)
        if stopped is not False:
            return stopped
        remaining = deadline - time.monotonic()
        if remaining <= 0:
            return False
        time.sleep(min(poll_s, remaining))


def reconcile(cfg):
    from es.jobs import process_identity
    with Store(cfg) as st:
        leases = [dict(r) for r in st.conn.execute('SELECT * FROM resource_leases')]
        jobs = [dict(r) for r in st.conn.execute("SELECT * FROM jobs WHERE status='unknown_execution'")]
    released=[]; uncertain=[]
    for row in leases+jobs:
        if row.get('pid') and process_identity(row['pid']) == row.get('process_start'):
            uncertain.append(row['id']); continue
        if scope_stopped(row.get('scope_unit')) is not True:
            uncertain.append(row['id']); continue
        with Store(cfg) as st:
            if 'memory_gib' in row:
                st.conn.execute('DELETE FROM resource_leases WHERE id=?',(row['id'],))
            else:
                try:
                    result = json.loads(row.get('result_json') or '{}')
                except (TypeError, json.JSONDecodeError):
                    result = {'prior_result_json': row.get('result_json')}
                if not isinstance(result, dict):
                    result = {'prior_result': result}
                result.update(execution_reconciled='scope_stopped', effects='require_review', termination_acknowledged=True)
                st.conn.execute("UPDATE jobs SET status='failed',result_json=? WHERE id=? AND status='unknown_execution'",
                                (canonical(result).decode(),row['id']))
        released.append(row['id'])
    return {'released_reservations':released,'unknown_execution':uncertain,'external_effects_retried':False}
