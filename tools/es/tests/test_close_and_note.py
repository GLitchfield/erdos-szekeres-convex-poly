import time

from es.commands.close import rewrite_imports
from es.commands.note import run as note_run
from es.context import Ctx
from es.store import Store


def test_rewrite_imports(cfg):
    (cfg.root / "TCore" / "User.lean").write_text("module\npublic import TBlueprint.A.Foo\nimport TCore.Basic\n")
    (cfg.root / "TCore" / "Other.lean").write_text("import TBlueprint.A.FooBar\n")
    touched = rewrite_imports(cfg, "TBlueprint.A.Foo", "TCore.Closed.A.Foo", ["TCore", "TBlueprint.lean"])
    assert "TCore/User.lean" in touched and "TCore/Other.lean" not in touched
    assert "public import TCore.Closed.A.Foo" in (cfg.root / "TCore" / "User.lean").read_text()
    assert "import TBlueprint.A.FooBar" in (cfg.root / "TCore" / "Other.lean").read_text()
    assert "import TCore.Closed.A.Foo" in (cfg.root / "TBlueprint.lean").read_text()


def test_note_from_fixture_tables(cfg):
    with Store(cfg) as st:
        st.event("node-added", "TCore.a", "t")
        st.event("closed", "TCore.b", "t")
        st.claim("TCore.c", "t", ttl_hours=1)
        st.release("TCore.c", "t", outcome="abandoned")
    ctx = Ctx(cfg=cfg, json_mode=False, agent="t")
    res = note_run(ctx, since=time.strftime("%Y-%m-%d", time.localtime(time.time() - 86400)), write=True)
    text = "\n".join(res.human)
    assert "opened: 1" in text and "closed: 1" in text and "attempts started this week: 1" in text and "## Judgment" in text
    assert (cfg.root / res.payload["path"]).exists()
