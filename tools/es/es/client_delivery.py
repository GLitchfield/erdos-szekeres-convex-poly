"""Opt-in Codex app-server adapter; requires an explicit thread/agent binding.

The default probe starts no model turn. Lost submission acknowledgements remain
uncertain until thread history contains the stable event marker. Never blindly retry.
"""
from __future__ import annotations

import json
import selectors
import subprocess
import time

from es import delivery
from es.artifacts import put_json
from es.errors import UsageError
from es.store import Store


class CodexProxy:
    def __init__(self, socket=None):
        command = ['codex', 'app-server', 'proxy'] + (['--sock', socket] if socket else [])
        self.proc = subprocess.Popen(command, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, bufsize=0)
        self.selector = selectors.DefaultSelector()
        self.selector.register(self.proc.stdout, selectors.EVENT_READ)
        self.buffer = b''
        self.sequence = 0

    def close(self):
        self.selector.close()
        self.proc.terminate()
        try: self.proc.wait(timeout=2)
        except subprocess.TimeoutExpired:
            self.proc.kill(); self.proc.wait()

    def request(self, method, params, timeout=10):
        self.sequence += 1
        ident = self.sequence
        self.proc.stdin.write((json.dumps({'id':ident,'method':method,'params':params})+'\n').encode())
        deadline = time.monotonic()+timeout
        while time.monotonic() < deadline:
            if b'\n' not in self.buffer:
                if not self.selector.select(max(0,deadline-time.monotonic())):
                    break
                chunk = self.proc.stdout.read(65536)
                if not chunk: raise UsageError('app-server proxy disconnected; no model turn requested by probe')
                self.buffer += chunk
            while b'\n' in self.buffer:
                line, self.buffer = self.buffer.split(b'\n',1)
                message = json.loads(line)
                if message.get('id') == ident:
                    if 'error' in message: raise UsageError(f"app-server {method} failed: {message['error'].get('code')}")
                    return message.get('result',{})
                if 'id' in message and 'method' in message:
                    # No permission delegation: this adapter cannot approve a tool.
                    self.proc.stdin.write((json.dumps({'id':message['id'],'error':{'code':-32601,'message':'approval requires the owning interactive client'}})+'\n').encode())
        raise UsageError(f'app-server {method} timed out')

    def initialize(self):
        response = self.request('initialize', {'clientInfo':{'name':'es-completion','version':'1'},'capabilities':{'experimentalApi':True}})
        self.proc.stdin.write(b'{"method":"initialized"}\n')
        return response


def probe(socket=None, thread=None):
    client = None
    try:
        client = CodexProxy(socket)
        client.initialize()
        state = client.request('thread/read', {'threadId':thread,'includeTurns':False}) if thread else None
        return {'transport_available':True, 'thread_available':bool(state), 'resume_verified':False,
                'model_requests':0, 'next_gate':'explicit binding plus a real result-triggered continuation'}
    except (OSError, UsageError) as exc:
        return {'transport_available':False,'resume_verified':False,'model_requests':0,'reason':str(exc)}
    finally:
        if client: client.close()


def terminal_packet(cfg, event):
    """Bound model context independently of receipt size; preserve full evidence."""
    payload = event['payload']
    packet = {'event_id': event['event_id'], 'operation_id': payload['operation_id'],
              'status': payload['status'], 'detail': put_json(cfg, payload)}
    result = payload.get('result', payload)
    if isinstance(result, dict):
        for key in ('proof_accepted', 'frontier_fresh', 'published'):
            if isinstance(result.get(key), bool):
                packet[key] = result[key]
        if isinstance(result.get('outcome'), str):
            packet['outcome'] = result['outcome'][:120]
    return packet


def dispatch_one(cfg, agent, thread, client, consumer):
    if not cfg.get('automation','delivery','enabled',default=False):
        raise UsageError('client delivery is disabled in project configuration')
    binding = cfg.get('automation','delivery','bindings',agent)
    if not binding or binding.get('thread') != thread or not binding.get('enabled',False):
        raise UsageError('delivery requires an enabled, explicit agent/thread binding in project config')
    state = client.request('thread/read', {'threadId':thread,'includeTurns':False})
    if state.get('thread',{}).get('status',{}).get('type') != 'idle':
        return {'status':'client_busy_or_unloaded','model_requests':0}
    event = delivery.claim(cfg, agent, consumer, 60)
    if event is None: return {'status':'no_delivery','model_requests':0}
    marker = '[es-event:'+event['event_id']+']'
    intent_key = 'delivery-intent:'+event['event_id']
    with Store(cfg) as st:
        prior = st.conn.execute('SELECT value FROM automation_meta WHERE key=?',(intent_key,)).fetchone()
    if prior:
        history = client.request('thread/read',{'threadId':thread,'includeTurns':True})
        if marker in json.dumps(history):
            delivery.ack(cfg,agent,event['event_id'],consumer)
            return {'status':'reconciled','model_requests':0,'event_id':event['event_id']}
        return {'status':'needs_reconciliation','model_requests':0,'event_id':event['event_id']}
    # Persist the full result before recording submission intent. Storage failure
    # must not strand an event as an uncertain model submission.
    packet = terminal_packet(cfg, event)
    with Store(cfg) as st:
        st.conn.execute('BEGIN IMMEDIATE')
        paused = st.conn.execute('SELECT value FROM automation_meta WHERE key=?',('delivery-paused:'+agent,)).fetchone()
        if paused and paused[0]=='1': return {'status':'paused','model_requests':0}
        st.conn.execute('INSERT INTO automation_meta VALUES (?,?)',(intent_key,json.dumps({'thread':thread,'at':time.time()})))
    # Do not override the user's model/effort/permissions or create another thread.
    text = marker+'\n'+json.dumps(packet,separators=(',',':'))
    reply = client.request('turn/start',{'threadId':thread,'input':[{'type':'text','text':text,'text_elements':[]}]})
    if not reply.get('turn',{}).get('id'):
        return {'status':'needs_reconciliation','model_requests':1,'event_id':event['event_id']}
    delivery.ack(cfg,agent,event['event_id'],consumer)
    return {'status':'delivered','model_requests':1,'event_id':event['event_id'],'turn_id':reply['turn']['id']}
