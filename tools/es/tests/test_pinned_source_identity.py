"""Source provenance checks; synthetic acceptance fields grant no theorem credit."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path

import pytest

from es import proofs
from es.artifacts import put, put_json
from es.context import Ctx
from es.errors import UsageError
from es.gitutil import git


DATA = json.loads((Path(__file__).parent / 'fixtures/pinned-proof-source-v1.json').read_text())


def commit_file(cfg, rel, content):
    path = cfg.root / rel
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(content)
    # Preserve the raw-byte fixture even on a host with autocrlf enabled.
    git(cfg, '-c', 'core.autocrlf=false', 'add', '--', rel)
    git(cfg, '-c', 'user.email=t@t', '-c', 'user.name=t', 'commit', '-q', '-m', 'source')
    return git(cfg, 'rev-parse', 'HEAD').strip()


@pytest.fixture
def candidate(cfg):
    baseline = git(cfg, 'rev-parse', 'HEAD').strip()
    source = DATA['source'].encode()
    start, end = proofs.whole_span(source.decode(), 'foo_node')
    f = {'schema_version': 1, 'root': str(cfg.root.resolve()), 'file': DATA['file'],
         'parent': DATA['parent'], 'type_hash': DATA['type_hash'],
         'source': put(cfg, source, 'text/x-lean'), 'span': [start, end],
         'compiled_dependencies': {}, 'scope': 'whole_declaration'}
    body = DATA['body'].encode()
    assembled = proofs.assembled(cfg, f, body)
    r = {'ok': True, 'proof_accepted': True, 'outcome': 'proof_accepted',
         'fixture': put_json(cfg, f, 'proof-fixture-v1')['id'],
         'body': put(cfg, body, 'text/x-lean')['id'],
         'candidate_source_hash': hashlib.sha256(assembled).hexdigest(),
         'audit': {'parent': DATA['parent'], 'type_hash': DATA['type_hash']}}
    receipt = put_json(cfg, r, 'stage-receipt-v1')['id']
    commit = commit_file(cfg, DATA['file'], assembled)
    return {'fixture': f, 'record': r, 'receipt': receipt, 'source': assembled,
            'commit': commit, 'baseline': baseline}


def test_exact_commit_identity_does_not_compile_or_close_frontier(cfg, candidate, monkeypatch):
    # The checkout is allowed to differ; the requested commit is the boundary.
    (cfg.root / DATA['file']).write_text('-- a later edit\n')
    monkeypatch.setattr(proofs, 'run_guarded', lambda *a, **k: pytest.fail('must not compile'))
    result = proofs.pinned_source_identity(cfg, candidate['receipt'], candidate['commit'])
    assert result['source_matches']
    assert result['source_sha256'] == candidate['record']['candidate_source_hash']
    assert result['compiler_rechecked'] is False
    assert result['theorem_credit'] == 'not_inferred'
    assert 'proof_accepted' not in result and 'frontier_fresh' not in result
    assert (cfg.root / DATA['file']).read_text() == '-- a later edit\n'


def test_baseline_cannot_be_reported_as_the_proof_commit(cfg, candidate):
    with pytest.raises(UsageError, match='cannot read'):
        proofs.pinned_source_identity(cfg, candidate['receipt'], candidate['baseline'])


def test_same_length_changed_source_is_rejected(cfg, candidate):
    changed = candidate['source'].replace(b'True.intro', b'False.elim')
    assert len(changed) == len(candidate['source'])
    commit = commit_file(cfg, DATA['file'], changed)
    with pytest.raises(UsageError, match='committed source differs'):
        proofs.pinned_source_identity(cfg, candidate['receipt'], commit)


@pytest.mark.parametrize('field,value', [('proof_accepted', False), ('ok', False),
                                        ('outcome', 'compile_failed')])
def test_unaccepted_receipts_are_rejected(cfg, candidate, field, value):
    r = dict(candidate['record'], **{field: value})
    receipt = put_json(cfg, r)['id']
    with pytest.raises(UsageError, match='accepted proof candidate'):
        proofs.pinned_source_identity(cfg, receipt, candidate['commit'])


@pytest.mark.parametrize('field', ['parent', 'type_hash'])
def test_receipt_must_match_captured_parent_and_type(cfg, candidate, field):
    r = dict(candidate['record'], audit=dict(candidate['record']['audit'], **{field: 'wrong'}))
    receipt = put_json(cfg, r)['id']
    with pytest.raises(UsageError, match='parent/type'):
        proofs.pinned_source_identity(cfg, receipt, candidate['commit'])


def test_reported_candidate_hash_must_match_immutable_assembly(cfg, candidate):
    r = dict(candidate['record'], candidate_source_hash='0' * 64)
    receipt = put_json(cfg, r)['id']
    with pytest.raises(UsageError, match='fixture/body artifacts'):
        proofs.pinned_source_identity(cfg, receipt, candidate['commit'])


@pytest.mark.parametrize('commit', ['HEAD', '--all', 'a' * 39, 'z' * 40])
def test_explicit_full_commit_required(cfg, candidate, commit):
    with pytest.raises(UsageError, match='full 40-character'):
        proofs.pinned_source_identity(cfg, candidate['receipt'], commit)


@pytest.mark.parametrize('rel', ['/tmp/Pinned.lean', '../escape.lean', 'notes.txt'])
def test_fixture_path_must_be_relative_lean_source(cfg, candidate, rel):
    f = dict(candidate['fixture'], file=rel)
    r = dict(candidate['record'], fixture=put_json(cfg, f)['id'])
    receipt = put_json(cfg, r)['id']
    with pytest.raises(UsageError, match='relative Lean source'):
        proofs.pinned_source_identity(cfg, receipt, candidate['commit'])


def test_raw_utf8_crlf_bytes_are_preserved(cfg):
    source = DATA['source'].replace('\n', '\r\n').encode()
    body = DATA['body'].replace('\n', '\r\n').encode()
    start, end = proofs.whole_span(source.decode(), 'foo_node')
    f = {'schema_version': 1, 'root': str(cfg.root.resolve()), 'file': DATA['file'],
         'parent': DATA['parent'], 'type_hash': DATA['type_hash'],
         'source': put(cfg, source), 'span': [start, end], 'compiled_dependencies': {}}
    assembled = proofs.assembled(cfg, f, body)
    r = {'ok': True, 'proof_accepted': True, 'outcome': 'proof_accepted',
         'fixture': put_json(cfg, f)['id'], 'body': put(cfg, body)['id'],
         'candidate_source_hash': hashlib.sha256(assembled).hexdigest(),
         'audit': {'parent': DATA['parent'], 'type_hash': DATA['type_hash']}}
    receipt = put_json(cfg, r)['id']
    commit = commit_file(cfg, DATA['file'], assembled)
    result = proofs.pinned_source_identity(cfg, receipt, commit)
    assert result['source_sha256'] == hashlib.sha256(assembled).hexdigest()


def test_cli_handler_preserves_noncredit_contract(cfg, candidate):
    from es.commands.proof import identity
    result = identity(Ctx(cfg), candidate['receipt'], candidate['commit'])
    assert result.exit_code == 0
    assert result.payload['compiler_rechecked'] is False
    assert result.payload['theorem_credit'] == 'not_inferred'
