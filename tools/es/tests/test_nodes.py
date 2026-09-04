import json

from es.allowlist import uncovered
from es.lock import check_lock
from es.nodes import Destination, Node, camel, compute, duplicates, node_module_name, nodes_from_extract, render_status_md


def mk(name, ws="A", kind="formalization", sorry=True, deps=(), nonstd=(), falsifier=None, module=None):
    tags = {"ws": ws, "kind": kind, "depends": list(deps), "consumer": "TCore.c"}
    if falsifier:
        tags["falsifier"] = falsifier
    return Node(name=name, module=module or f"TBlueprint.{ws}.{camel(name.split('.')[-1])}", type_pp="True", type_hash="h" + name,
                sorry=sorry, axioms=["propext"] + list(nonstd), nonstandard_axioms=list(nonstd), deps_actual=[], tags=tags)


def test_naming(cfg):
    assert camel("fin15_endpoint") == "Fin15Endpoint"
    assert node_module_name(cfg, "TCore.fin15_endpoint", "A") == "TBlueprint.A.Fin15Endpoint"


def test_ready_computation(cfg):
    a = mk("TCore.a")
    b = mk("TCore.b", deps=["TCore.a"])
    c = mk("TCore.c_closed", sorry=False)
    d = mk("TCore.d", deps=["TCore.c_closed", "TCore.core_thm"])
    e = mk("TCore.e", deps=["TCore.unknown_name"])
    lock = {n.name: {"type_hash": n.type_hash} for n in (a, b, c, d, e)}
    compute(cfg, [a, b, c, d, e], [], core_names={"TCore.core_thm"}, claims={}, falsify={}, lock=lock, allow=[])
    assert a.status == "open" and a.ready
    assert b.status == "open" and not b.ready and b.blocked_by == ["TCore.a"]
    assert c.status == "closed"
    assert d.ready
    assert not e.ready and e.blocked_by == ["TCore.unknown_name (unknown)"]


def test_conjecture_needs_falsifier_pass_and_claims_block(cfg):
    conj = mk("TCore.conj", kind="conjecture", falsifier="f.py")
    lock = {conj.name: {"type_hash": conj.type_hash}}
    compute(cfg, [conj], [], set(), claims={}, falsify={}, lock=lock, allow=[])
    assert conj.status == "proposed" and not conj.ready
    compute(cfg, [conj], [], set(), claims={}, falsify={conj.name: {"result": "pass"}}, lock=lock, allow=[])
    assert conj.status == "open" and conj.ready
    compute(cfg, [conj], [], set(), claims={conj.name: {"agent": "x"}}, falsify={conj.name: {"result": "pass"}}, lock=lock, allow=[])
    assert conj.status == "claimed" and not conj.ready
    compute(cfg, [conj], [], set(), claims={}, falsify={conj.name: {"result": "counterexample"}}, lock=lock, allow=[])
    assert conj.status == "refuted"


def test_unlocked_node_is_proposed(cfg):
    a = mk("TCore.a")
    compute(cfg, [a], [], set(), claims={}, falsify={}, lock={}, allow=[])
    assert a.status == "proposed"


def test_allowlist_and_unallowlisted_status(cfg):
    n = mk("TCore.n", sorry=False, nonstd=["Lean.ofReduceBool"])
    lock = {n.name: {"type_hash": n.type_hash}}
    compute(cfg, [n], [], set(), claims={}, falsify={}, lock=lock, allow=[])
    assert n.status == "unallowlisted" and n.uncovered_axioms == ["Lean.ofReduceBool"]
    allow = [{"axiom": "Lean.ofReduceBool", "reaches": ["TCore.n"]}]
    compute(cfg, [n], [], set(), claims={}, falsify={}, lock=lock, allow=allow)
    assert n.status == "closed"
    assert uncovered([{"axiom": "x", "reaches": ["*"]}], "anything", ["x", "propext"], ["propext"]) == []
    assert uncovered([], "a", ["x"], []) == ["x"]


def test_duplicates_and_lock():
    a = mk("TCore.a"); b = mk("TCore.b"); b.type_hash = a.type_hash
    idx = [{"name": "TCore.core", "kind": "theorem", "type_hash": "hTCore.a"}]
    probs = duplicates([a, b], idx)
    assert any("TCore.b duplicates TCore.a" in p for p in probs)
    assert any("duplicates core theorem TCore.core" in p for p in probs)
    lock = {"TCore.a": {"type_hash": "other"}}
    lp = check_lock(lock, [a, b])
    assert any("changed by hand" in p for p in lp) and any("not in statements.lock" in p for p in lp)


def test_nodes_from_extract_and_render(cfg):
    raw = {
        "declarations": [
            {"name": "TCore.x", "module": "TBlueprint.A.X", "doc": "desc\n@node\n@ws A\n@kind formalization\n@consumer TCore.c", "type_pp": "True", "type_hash": "1", "sorry": True, "axioms": ["sorryAx"], "nonstandard_axioms": ["sorryAx"], "deps": [], "internal": False, "kind": "theorem"},
            {"name": "TCore.x.aux", "module": "TBlueprint.A.X", "doc": None, "type_pp": "True", "type_hash": "2", "sorry": False, "axioms": [], "nonstandard_axioms": [], "deps": [], "internal": False, "kind": "theorem"},
            {"name": "TCore.y", "module": "TBlueprint.A.Y", "doc": "no tags", "type_pp": "True", "type_hash": "3", "sorry": True, "axioms": [], "nonstandard_axioms": [], "deps": [], "internal": False, "kind": "theorem"},
        ],
        "destinations": [{"name": "TCore.dest", "module": "TCore.Basic", "doc": "d", "type_pp": "True", "type_hash": "9", "sorry": False, "axioms": ["propext"], "nonstandard_axioms": [], "deps": [], "internal": False, "kind": "theorem"}],
        "missing_destinations": ["TCore.gone"],
    }
    nodes, dests, problems = nodes_from_extract(cfg, raw)
    assert [n.name for n in nodes] == ["TCore.x"] and nodes[0].helpers == ["TCore.x.aux"]
    assert any("TBlueprint.A.Y: no declaration carries @node" in p for p in problems)
    assert any("TCore.gone" in p for p in problems)
    compute(cfg, nodes, dests, set(), claims={}, falsify={}, lock={"TCore.x": {"type_hash": "1"}}, allow=[])
    md = render_status_md(cfg, nodes, dests, problems, {"toolchain": "t", "modules": 3})
    assert "## Workstream A" in md and "`TCore.x`" in md and "## Destinations" in md and "## Problems" in md


def test_allowlist_glob_matches_native_decide_axioms():
    entries = [{"axiom": "*._native.native_decide.*", "reaches": ["TCore.n"]}]
    assert uncovered(entries, "TCore.n", ["TCore.n._native.native_decide.ax_1_1"], []) == []
    assert uncovered(entries, "TCore.other", ["TCore.other._native.native_decide.ax_1_1"], []) == ["TCore.other._native.native_decide.ax_1_1"]
