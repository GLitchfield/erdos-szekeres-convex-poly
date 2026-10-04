from __future__ import annotations

import json
from pathlib import Path

import pytest

from es import library
from es.errors import UsageError


ROOT = Path(__file__).resolve().parents[3]


def entry(
    ident: str,
    *,
    title: str,
    summary: str,
    keywords: list[str],
    symbol: str,
    kind: str = "primitive",
) -> dict:
    api = f"{symbol}(value) -> value"
    example = f"{symbol}(1)"
    if kind == "workflow":
        api = f"es {symbol.replace('_', ' ')} VALUE"
        example = api
    return {
        "id": ident,
        "kind": kind,
        "title": title,
        "summary": summary,
        "keywords": keywords,
        "api": api,
        "example": example,
        "semantics": "Deterministic fixture semantics.",
        "source": {"path": "research_helpers.py", "symbols": [symbol]},
    }


def install_catalog(cfg, entries: list[dict]) -> None:
    directory = cfg.root / "harness" / "research"
    directory.mkdir(parents=True, exist_ok=True)
    (directory / "catalog.json").write_text(
        json.dumps({"schema_version": 1, "entries": entries}) + "\n"
    )


@pytest.fixture
def catalog(cfg):
    # Loading this file would fail. Catalog validation must only parse it.
    (cfg.root / "research_helpers.py").write_text(
        "raise RuntimeError('catalog imported source')\n\n"
        "def recursive_bound(value):\n    return value\n\n"
        "def generic_search(value):\n    return value\n\n"
        "def proof_workflow(value):\n    return value\n"
    )
    entries = [
        entry(
            "math.recursive-bound",
            title="Recursive bounds",
            summary="Memoized evaluator for recursive context bounds.",
            keywords=["recursive bounds", "recurrence", "dynamic programming"],
            symbol="recursive_bound",
        ),
        entry(
            "math.generic-search",
            title="Generic finite search",
            summary="Enumerates finite candidates and reports bounded results.",
            keywords=["search", "enumeration", "bounds"],
            symbol="generic_search",
        ),
        entry(
            "workflow.proof",
            title="Proof workflow",
            summary="Captures and checks a proof candidate.",
            keywords=["proof", "Lean", "check"],
            symbol="proof_workflow",
            kind="workflow",
        ),
    ]
    install_catalog(cfg, entries)
    return entries


def test_search_is_usefully_ranked_and_compact(cfg, catalog):
    hits = library.search(cfg.root, "recursive bounds")
    assert [hit["id"] for hit in hits[:2]] == [
        "math.recursive-bound",
        "math.generic-search",
    ]
    assert hits[0]["score"] > hits[1]["score"]
    assert set(hits[0]) == {"id", "kind", "title", "summary", "score"}
    assert library.listing(cfg.root, kind="workflow") == [
        {
            "id": "workflow.proof",
            "kind": "workflow",
            "title": "Proof workflow",
            "summary": "Captures and checks a proof candidate.",
        }
    ]


def test_search_no_hit(cfg, catalog):
    assert library.search(cfg.root, "quaternion kaleidoscope") == []


def test_show_has_api_semantics_example_and_source(cfg, catalog):
    found = library.show(cfg.root, "math.recursive-bound")
    assert found["api"] == "recursive_bound(value) -> value"
    assert found["example"] == "recursive_bound(1)"
    assert found["semantics"] == "Deterministic fixture semantics."
    assert found["source"] == {
        "path": "research_helpers.py",
        "symbols": ["recursive_bound"],
    }
    with pytest.raises(UsageError, match="run `es lib list`"):
        library.show(cfg.root, "missing")


def test_stale_source_symbol_fails_usefully(cfg, catalog):
    broken = dict(catalog[0])
    broken["source"] = {
        "path": "research_helpers.py",
        "symbols": ["renamed_bound"],
    }
    install_catalog(cfg, [broken])
    with pytest.raises(
        UsageError,
        match=r"math\.recursive-bound: stale source research_helpers\.py; missing symbol\(s\): renamed_bound",
    ):
        library.listing(cfg.root)


def test_cli_and_mcp_share_registered_commands(cfg, catalog, capsys):
    from es.cli import main
    from es.mcp_server import _make_tool
    from es.spec import REGISTRY
    import es.commands  # noqa: F401

    specs = {spec.name: spec for spec in REGISTRY}
    assert {"lib_list", "lib_search", "lib_show"} <= specs.keys()

    rc = main(["lib", "search", "recursive bounds", "--json"])
    payload = json.loads(capsys.readouterr().out)
    assert rc == 0
    assert payload["entries"][0]["id"] == "math.recursive-bound"
    assert "api" not in payload["entries"][0]

    tool = _make_tool(specs["lib_show"])
    detail = tool(id="math.recursive-bound")
    assert detail["ok"] is True
    assert detail["entry"]["source"]["symbols"] == ["recursive_bound"]


def test_project_catalog_exposes_promoted_research_boundary():
    expected = {
        "research.recursive-bounds",
        "research.compiled-context-bound",
        "research.context-extension",
        "research.rank-clip-potential",
        "research.context-part",
        "research.singleton-cuts",
        "research.ordered-cover",
        "research.maximum-bounds",
        "research.sole-opposite-normalize",
        "research.cup-cap-chains",
        "research.lazy-strong-gons",
        "decomposable.label-sets",
        "decomposable.band-partitions",
        "workflow.proof",
        "workflow.node-finish",
        "workflow.probe",
        "workflow.recursive-cut-probe",
        "workflow.context",
        "workflow.usage",
        "workflow.setup-metadata-cleanup",
        "workflow.immutable-artifact-sharing",
    }
    entries = library.load(ROOT)
    assert expected <= {item["id"] for item in entries}

    hits = library.search(ROOT, "recursive bounds")
    assert hits[0]["id"] == "research.recursive-bounds"
    recursive = library.show(ROOT, hits[0]["id"])
    assert recursive["source"] == {
        "path": "harness/research/recursive.py",
        "symbols": ["evaluator"],
    }
    assert "semantics" in recursive["api"] and "cache_size" in recursive["api"]
    assert "not a certificate of equivalence to Lean" in recursive["semantics"]

    by_id = {item["id"]: item for item in entries}
    assert by_id["research.compiled-context-bound"]["source"] == {
        "path": "harness/research/context_bound.py", "symbols": ["compiled_evaluator"]}
    assert by_id["workflow.recursive-cut-probe"]["source"]["symbols"] == [
        "evaluate",
        "replay",
    ]
    assert by_id["workflow.node-finish"]["api"].startswith("es node finish ")
    assert all(
        item["api"].startswith("es ")
        for item in entries
        if item["kind"] == "workflow"
    )
