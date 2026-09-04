"""`es certs relocate`: move generated certificate modules under a sub-namespace (dry-run by default).

Renaming a module changes every import line that names it, so all certificate
oleans are rebuilt afterwards (for this project: days of guarded builds).  The
command therefore only plans by default and applies with --apply.
"""

from __future__ import annotations

import re
from pathlib import Path

from es import EXIT_OK
from es.context import Ctx
from es.errors import UsageError
from es.gitutil import git_mv
from es.modules import module_to_path, scan_modules
from es.output import Result
from es.spec import Arg, CommandSpec, command


def run(ctx: Ctx, target: str | None = None, apply: bool = False, generators: str = "scripts/generate_*.py,scripts/split_*.py") -> Result:
    cfg = ctx.cfg
    cert_layer = cfg.certificates_layer
    if not cert_layer:
        raise UsageError("no certificates layer configured")
    target = target or f"{cfg.core_namespace}.Certificates"
    mods = scan_modules(cfg)
    certs = sorted((m for m in mods.values() if m.layer == cert_layer), key=lambda m: m.name)
    rename: dict[str, str] = {}
    for m in certs:
        if m.name.startswith(target + "."):
            continue
        rename[m.name] = target + "." + m.name[len(cfg.core_namespace) + 1 :]
    if not rename:
        return Result(EXIT_OK, {"moves": 0}, ["nothing to relocate"])
    pat = re.compile(r"^(\s*(?:public\s+)?(?:private\s+)?import\s+(?:all\s+)?)([\w.]+)(\s*$)", re.M)
    rewrites: dict[str, int] = {}
    for m in mods.values():
        text = (cfg.root / m.path).read_text(errors="replace")
        n = sum(1 for im in pat.finditer(text) if im.group(2) in rename)
        if n:
            rewrites[str(m.path)] = n
    gen_hits: dict[str, int] = {}
    for glob in generators.split(","):
        for p in sorted(cfg.root.glob(glob.strip())):
            text = p.read_text(errors="replace")
            n = sum(text.count(old) for old in rename) + text.count(f"{cfg.core_namespace}.{{") + text.count(f"{cfg.core_namespace}/")
            if n:
                gen_hits[str(p.relative_to(cfg.root))] = n
    res = Result()
    res.line(f"{len(rename)} module(s) would move to {target}.*; {len(rewrites)} file(s) have import lines to rewrite; {len(gen_hits)} generator script(s) reference the old names")
    res.line("every moved module and every module importing one is rebuilt afterwards (all certificate oleans)")
    if not apply:
        res.line("dry run; pass --apply to perform the move (then run `es layers --write-allowlists`, update the generators, and rebuild under `es build`)")
        res.payload = {"moves": len(rename), "sample": list(rename.items())[:10], "rewrites": rewrites, "generators": gen_hits, "applied": False}
        res.exit_code = EXIT_OK
        return res
    for old, new in rename.items():
        git_mv(cfg, cfg.root / module_to_path(old), cfg.root / module_to_path(new))
    for m in mods.values():
        new_path = cfg.root / module_to_path(rename.get(m.name, m.name))
        text = new_path.read_text(errors="replace")
        new_text = pat.sub(lambda im: im.group(1) + rename.get(im.group(2), im.group(2)) + im.group(3), text)
        if new_text != text:
            new_path.write_text(new_text)
    for rel in gen_hits:
        p = cfg.root / rel
        text = p.read_text()
        for old, new in rename.items():
            text = text.replace(f'"{old}"', f'"{new}"').replace(f"{old}\n", f"{new}\n")
        text = text.replace(f"{cfg.core_namespace}.{{", f"{target}.{{").replace(f"{cfg.core_namespace}/", f"{target.replace('.', '/')}/")
        p.write_text(text)
    res.line("applied; review the generator edits by hand, then `es layers --write-allowlists` and `es build certs`")
    res.payload = {"moves": len(rename), "rewrites": rewrites, "generators": gen_hits, "applied": True}
    res.exit_code = EXIT_OK
    return res


command(CommandSpec(name="certs_relocate", cli=["certs", "relocate"], mcp=False,
                    help="Plan (or --apply) moving every generated certificate module under <core>.Certificates.", run=run,
                    args=[Arg("target", "target module prefix (default <core>.Certificates)"), Arg("apply", "perform the move", "bool"),
                          Arg("generators", "comma-separated globs of generator scripts to patch")]))
