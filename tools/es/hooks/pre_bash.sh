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
  "$es" layers --allow-rebuild >/tmp/es-pre-bash.$$ 2>&1 || { echo "es layers failed:"; tail -20 /tmp/es-pre-bash.$$; fail=1; }
  echo "es: [certificate-rebuild] commit; extract consistency check skipped until the certificates are rebuilt" >&2
else
  "$es" layers >/tmp/es-pre-bash.$$ 2>&1 || { echo "es layers failed:"; tail -20 /tmp/es-pre-bash.$$; fail=1; }
  "$es" extract --check >>/tmp/es-pre-bash.$$ 2>&1 || { echo "es extract --check failed:"; tail -20 /tmp/es-pre-bash.$$; fail=1; }
fi
"$es" audit --changed >>/tmp/es-pre-bash.$$ 2>&1 || { echo "es audit --changed failed:"; tail -20 /tmp/es-pre-bash.$$; fail=1; }
rm -f /tmp/es-pre-bash.$$
if [ "$fail" -ne 0 ]; then
  echo "blocked: fix the problems above (or run \`es extract\` to refresh generated files) before committing." >&2
  exit 2
fi
exit 0
