import json
import subprocess
import sys

from es.cli import main


def run(args, capsys):
    rc = main(args)
    out = capsys.readouterr().out
    return rc, out


def test_layers_cli_json(cfg, capsys):
    rc, out = run(["layers", "--json"], capsys)
    assert rc == 0
    data = json.loads(out)
    assert data["ok"] and data["violations"] == []


def test_doctor_runs(cfg, capsys):
    rc, out = run(["doctor"], capsys)
    assert "config" in out


def test_status_needs_extract(cfg, capsys):
    rc, out = run(["status"], capsys)
    assert rc == 2


def test_mcp_tool_signatures():
    from es.mcp_server import _make_tool
    from es.spec import REGISTRY
    import es.commands  # noqa: F401
    import inspect

    spec = next(s for s in REGISTRY if s.name == "node_add")
    tool = _make_tool(spec)
    params = inspect.signature(tool).parameters
    assert "name" in params and params["name"].default is inspect.Parameter.empty
    assert "force" in params and params["force"].default is False


def test_flag_names_strip_trailing_underscore():
    from es.cli import build_parser

    parser = build_parser()
    text = parser.format_help()
    sub = None
    for action in parser._subparsers._group_actions:
        sub = action
    checks = sub.choices["check"]
    assert "--async" in checks.format_help() and "--async-" not in checks.format_help()
    node = sub.choices["node"]
    add = [a for a in node._subparsers._group_actions][0].choices["add"]
    assert "--import IMPORT" in add.format_help()


def test_dispatch_drops_unset_optional_args(cfg):
    from es.cli import build_parser, dispatch
    from es.spec import CommandSpec, Arg
    from es.output import Result

    seen = {}

    def handler(ctx, name, generators="default,globs"):
        seen.update(name=name, generators=generators)
        return Result()

    spec = CommandSpec(name="t", cli=["t"], help="t", run=handler, args=[Arg("name", "n", positional=True, required=True), Arg("generators", "g")])
    parser = build_parser()
    ns = parser.parse_args(["layers"])
    ns.name = "x"; ns.generators = None
    dispatch(spec, ns)
    assert seen == {"name": "x", "generators": "default,globs"}
