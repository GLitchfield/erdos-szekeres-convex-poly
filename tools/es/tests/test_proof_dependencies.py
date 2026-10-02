from __future__ import annotations

import hashlib
import json
from pathlib import Path

import pytest

from es.errors import UsageError
from es.proof_dependencies import classify_trace, receipt


FIXTURE = Path(__file__).parent / "fixtures" / "proof-dependencies-v1.json"


def raw_trace():
    return json.loads(FIXTURE.read_text())["owner_differs_from_import"]


def test_owner_identity_and_imported_certificate_are_distinct(cfg, tmp_path):
    trace = raw_trace()
    path = tmp_path / "trace.json"
    path.write_text(json.dumps(trace))
    olean = cfg.root / ".lake/build/lib/lean/TCore/Basic.olean"
    olean.parent.mkdir(parents=True)
    olean.write_bytes(b"fixture-owner-olean")
    result = receipt(cfg, path)
    # TCore.Consumer imports a certificate, but this root only refers to Basic.
    assert result["import_module"] == "TCore.Consumer"
    assert result["root_module"] == "TCore.Basic"
    assert result["source_path"] == "TCore/Basic.lean"
    assert result["source_sha256"] == hashlib.sha256((cfg.root / "TCore/Basic.lean").read_bytes()).hexdigest()
    assert result["olean_sha256"] == hashlib.sha256(b"fixture-owner-olean").hexdigest()
    assert result["certificate_modules"] == []
    assert "proof_accepted" not in result and "frontier_fresh" not in result


def test_referenced_certificates_unknown_names_and_axioms_are_retained(cfg):
    trace = json.loads(FIXTURE.read_text())["referenced_obstructions"]
    result = classify_trace(cfg, trace)
    assert result["generated_modules"] == ["TCore.Chunk000"]
    assert result["certificate_modules"] == ["TCore.Chunk000"]
    assert result["unknown_project_modules"] == ["TBlueprint.Unknown", "TCore.Unknown"]
    assert result["nonstandard_axioms"] == ["sorryAx"]
    assert result["unsafe_constants"] == ["TCore.runtime"]


@pytest.mark.parametrize("field,value", [
    ("schema_version", True),
    ("schema_version", 0),
    ("semantics", "imports only"),
    ("root_module", "TCore.NotReachable"),
    ("modules", ["TCore.Basic", 7]),
    ("reachable_constants", True),
    ("imported_constant_upper_bound", 0),
])
def test_malformed_trace_cannot_make_identity_receipt(cfg, field, value):
    trace = raw_trace()
    trace[field] = value
    with pytest.raises(UsageError):
        classify_trace(cfg, trace)


def test_legacy_ownerless_trace_is_explicitly_refused(cfg):
    trace = raw_trace()
    del trace["root_module"]
    with pytest.raises(UsageError, match="predates declaration-owner"):
        classify_trace(cfg, trace)


def test_missing_compiled_owner_does_not_grant_identity(cfg, tmp_path):
    path = tmp_path / "trace.json"
    path.write_text(json.dumps(raw_trace()))
    with pytest.raises(UsageError, match="identity file is missing"):
        receipt(cfg, path)
