from types import SimpleNamespace

from es.context import Ctx


def test_targeted_check_never_requests_full_extraction(cfg, monkeypatch):
    from es.commands import check, extract, node

    declaration = SimpleNamespace(name="TCore.foo_node", module="TBlueprint.A.Foo", short="foo_node")
    checked = {"name": declaration.name, "sorry": False, "status": "closed", "axioms": [],
               "uncovered_axioms": [], "deps_declared": [], "deps_actual": []}
    monkeypatch.setattr(check, "find_node", lambda *_: declaration)
    monkeypatch.setattr(check, "run_guarded", lambda *_args, **_kwargs:
                        SimpleNamespace(ok=True, seconds=0, peak_mib=0, summary=lambda: "ok"))
    seen = []

    def targeted(ctx, module):
        seen.append(module)
        return {"nodes": [checked]}, [], []

    def forbidden(*_args, **_kwargs):
        raise AssertionError("a targeted check must not prebuild or extract the full blueprint")

    monkeypatch.setattr(node, "targeted_extract", targeted)
    monkeypatch.setattr(extract, "run_extract", forbidden)
    result = check.run(Ctx(cfg), declaration.name, targeted=True)
    assert result.exit_code == 0
    assert result.payload["targeted"]
    assert seen == [declaration.module]
    assert not cfg.nodes_json.exists()


def test_targeted_add_never_requests_full_extraction(cfg, monkeypatch):
    from es.commands import node

    seen = []
    monkeypatch.setattr(node, "elaborate_module", lambda *_args, **_kwargs: None)

    def targeted(ctx, module):
        seen.append(module)
        return {"nodes": [{"name": "TCore.regression", "type_hash": "hash", "type_pp": "True",
                           "status": "proposed"}]}, [], []

    def forbidden(*_args, **_kwargs):
        raise AssertionError("a targeted add must not prebuild or extract the full blueprint")

    monkeypatch.setattr(node, "targeted_extract", targeted)
    monkeypatch.setattr(node, "re_extract", forbidden)
    result = node.run_add(Ctx(cfg), "regression", "A", "formalization", ": True",
                          "Targeted registration regression.", dangling_ok="test", targeted=True)
    assert result.exit_code == 0
    assert seen == ["TBlueprint.A.Regression"]
    assert not cfg.nodes_json.exists()


def test_targeted_check_is_preserved_when_queued(cfg, monkeypatch):
    from es.commands import check
    from es import jobs

    monkeypatch.setattr(check, "find_node", lambda *_:
                        SimpleNamespace(name="TCore.foo_node", module="TBlueprint.A.Foo"))
    submitted = []

    def submit(_cfg, **kwargs):
        submitted.append(kwargs)
        return {"id": "test-job"}

    monkeypatch.setattr(jobs, "submit", submit)
    check.run(Ctx(cfg), "foo_node", async_=True, targeted=True)
    assert "--targeted" in submitted[0]["argv"]
