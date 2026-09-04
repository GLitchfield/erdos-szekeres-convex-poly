"""``es`` command-line entry point: argparse built from the shared command specs."""

from __future__ import annotations

import argparse
import sys
import traceback
from pathlib import Path

from es import EXIT_USAGE, __version__
from es.errors import EsError
from es.output import Result, emit
from es.spec import REGISTRY, Arg, CommandSpec


def _add_arg(parser: argparse.ArgumentParser, a: Arg) -> None:
    kwargs: dict = {"help": a.help}
    if a.choices:
        kwargs["choices"] = a.choices
    if a.type == "int":
        kwargs["type"] = int
    elif a.type == "float":
        kwargs["type"] = float
    if a.positional:
        if not a.required:
            kwargs["nargs"] = "?"
            kwargs["default"] = a.default
        if a.type == "list":
            kwargs["nargs"] = "+" if a.required else "*"
        parser.add_argument(a.name, **kwargs)
        return
    flag = "--" + a.name.rstrip("_").replace("_", "-")
    if a.type == "bool":
        parser.add_argument(flag, dest=a.name, action="store_true", default=bool(a.default), help=a.help)
        return
    if a.type == "list":
        kwargs["action"] = "append"
        kwargs["default"] = None
    else:
        kwargs["default"] = a.default
    kwargs["required"] = a.required
    kwargs["dest"] = a.name
    parser.add_argument(flag, **kwargs)


def build_parser() -> argparse.ArgumentParser:
    import es.commands  # noqa: F401  (registers commands)

    common = argparse.ArgumentParser(add_help=False)
    common.add_argument("--json", action="store_true", help="emit JSON instead of tables")
    common.add_argument("--root", help="project root (default: discover harness/config.toml upwards)")
    parser = argparse.ArgumentParser(prog="es", description="Blueprint harness: state derived from Lean.", parents=[common])
    parser.add_argument("--version", action="version", version=f"es {__version__}")
    sub = parser.add_subparsers(dest="cmd")
    groups: dict[str, argparse._SubParsersAction] = {}
    for spec in REGISTRY:
        if len(spec.cli) == 1:
            p = sub.add_parser(spec.cli[0], help=spec.help, description=spec.help, parents=[common])
        else:
            head = spec.cli[0]
            if head not in groups:
                gp = sub.add_parser(head, help=f"{head} commands")
                groups[head] = gp.add_subparsers(dest=f"{head}_cmd")
            p = groups[head].add_parser(spec.cli[1], help=spec.help, description=spec.help, parents=[common])
        p.set_defaults(_spec=spec)
        for a in spec.args:
            _add_arg(p, a)
    return parser


def dispatch(spec: CommandSpec, ns: argparse.Namespace) -> Result:
    from es.context import Ctx

    root = Path(ns.root).resolve() if ns.root else None
    ctx = Ctx.load(root, json_mode=ns.json)
    kwargs = {}
    for a in spec.args:
        val = getattr(ns, a.name, a.default)
        if a.type == "list" and val is not None and not a.positional:
            # allow both repeated flags and comma-separated values
            flat: list[str] = []
            for v in val:
                flat.extend(x.strip() for x in str(v).split(",") if x.strip())
            val = flat
        if val is None and a.default is None and not a.positional:
            continue  # let the handler's own default apply
        kwargs[a.name] = val
    return spec.run(ctx, **kwargs)


def main(argv: list[str] | None = None) -> int:
    parser = build_parser()
    ns = parser.parse_args(argv)
    spec = getattr(ns, "_spec", None)
    if spec is None:
        parser.print_help()
        return EXIT_USAGE
    try:
        result = dispatch(spec, ns)
    except EsError as exc:
        res = Result(exit_code=exc.exit_code, payload={"error": str(exc)}, human=[f"error: {exc}"])
        emit(res, ns.json, sys.stderr if not ns.json else sys.stdout)
        return exc.exit_code
    except KeyboardInterrupt:
        return 130
    except Exception as exc:  # pragma: no cover - last resort
        traceback.print_exc()
        res = Result(exit_code=EXIT_USAGE, payload={"error": f"{type(exc).__name__}: {exc}"}, human=[f"error: {exc}"])
        emit(res, ns.json, sys.stderr if not ns.json else sys.stdout)
        return EXIT_USAGE
    emit(result, ns.json)
    return result.exit_code


if __name__ == "__main__":
    raise SystemExit(main())
