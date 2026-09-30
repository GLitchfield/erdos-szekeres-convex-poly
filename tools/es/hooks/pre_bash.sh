#!/usr/bin/env bash
# Claude Code PreToolUse hook for Bash: block `git commit` / `git push` when the
# layering, the statement lock, or the axiom audit would fail.
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
es="$here/../bin/es"
input="$(cat)"
cmd="$(printf '%s' "$input" | python3 -c 'import json,sys
try:
    d=json.load(sys.stdin); print(d.get("tool_input",{}).get("command",""))
except Exception:
    print("")' 2>/dev/null)"
# Compute launched outside the harness is invisible to other agents and to the memory
# budget (two WSL crashes): `systemd-run` and `nohup` are only allowed through `es`
# itself (`es job run --why ... --out ... -- <command>` records purpose, cap, outputs, peak).
printf '%s' "$cmd" | python3 -c 'import re,sys
c=sys.stdin.read()
bare = re.search(r"(?:^|[;&|(]\s*)(?:systemd-run|nohup)\b", c)
via_es = re.search(r"(?:bin/es|\bes)\s+(?:job\s+run|extract|build|check|falsify|worker)\b", c)
sys.exit(2 if bare and not via_es else 0)'
if [ $? -eq 2 ]; then
  echo "blocked: launch compute through the harness so other agents can see it and the memory budget holds:" >&2
  echo "  es job run --why \"<purpose>\" --out <runs/... or data/...> [--node <node>] [--mem 2G] -- <command>" >&2
  exit 2
fi
# A research computation is reviewed at progress checkpoints, never killed at a self-chosen
# time (CLAUDE.md / AGENTS.md): a `timeout N` wrapper at the start of a command segment is
# refused.  Options named --timeout (e.g. `es job wait --timeout 55`) are not wrappers.
printf '%s' "$cmd" | python3 -c 'import re,sys
c=sys.stdin.read()
sys.exit(2 if re.search(r"(?:^|[;&|(]\s*|\bthen\s+|\bdo\s+|--\s+)timeout\s+(?:(?:-\S+|[A-Z]+)\s+)*[\d.]+[smhd]?\s", c) else 0)'
if [ $? -eq 2 ]; then
  echo "blocked: do not kill a computation at a time limit you chose. If it is not measured to finish within a" >&2
  echo "minute, run it as a job and review its progress at checkpoints:" >&2
  echo "  es job run --why \"<purpose>\" --out <runs/...> [--review MIN] -- <command>; es job wait <id>; es job review <id> --note ..." >&2
  echo "(a deadline the user set: es job run --budget MIN)" >&2
  exit 2
fi
# Only a real invocation counts: `git [global options] commit|push` at the start of a
# command segment (not the words inside a heredoc, a message, or a file being written).
printf '%s' "$cmd" | python3 -c 'import re,sys
c=sys.stdin.read()
sys.exit(0 if re.search(r"(?:^|[;&|(]\s*)git(?:\s+-[-\w=./]+)*\s+(commit|push)\b", c) else 1)' || exit 0
cd "$here/../../.." || exit 0
fail=0
# A commit whose message carries [certificate-rebuild] may touch frozen encoding modules;
# while the certificates rebuild the compiled state is in flux, so the extract check is
# skipped for that commit (the nightly run and the next ordinary commit re-check it).
rebuild=0
case "$cmd" in *"[certificate-rebuild]"*) rebuild=1 ;; esac
if [ "$rebuild" = 1 ]; then
  "$es" layers --allow-rebuild --base HEAD >/tmp/es-pre-bash.$$ 2>&1 || { echo "es layers failed:"; tail -20 /tmp/es-pre-bash.$$; fail=1; }
  echo "es: [certificate-rebuild] commit; extract consistency check skipped until the certificates are rebuilt" >&2
else
  "$es" layers --base HEAD >/tmp/es-pre-bash.$$ 2>&1 || { echo "es layers failed:"; tail -20 /tmp/es-pre-bash.$$; fail=1; }
  # --changed: a commit that touches no index input and no index file passes at once; otherwise
  # the check verifies by fingerprints without Lean, and only core changes need a full extraction.
  "$es" extract --check --changed >>/tmp/es-pre-bash.$$ 2>&1 || { echo "es extract --check failed:"; tail -20 /tmp/es-pre-bash.$$; fail=1; }
fi
"$es" audit --changed >>/tmp/es-pre-bash.$$ 2>&1 || { echo "es audit --changed failed:"; tail -20 /tmp/es-pre-bash.$$; fail=1; }
rm -f /tmp/es-pre-bash.$$
if [ "$fail" -ne 0 ]; then
  echo "blocked: fix the problems above (or run \`es extract\` to refresh generated files) before committing." >&2
  exit 2
fi
exit 0
