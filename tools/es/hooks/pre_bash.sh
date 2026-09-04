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
case "$cmd" in
  *"git commit"*|*"git push"*|*"git-data commit"*|*"git-data push"*) ;;
  *) exit 0 ;;
esac
cd "$here/../../.." || exit 0
fail=0
"$es" layers >/tmp/es-pre-bash.$$ 2>&1 || { echo "es layers failed:"; tail -20 /tmp/es-pre-bash.$$; fail=1; }
"$es" extract --check >>/tmp/es-pre-bash.$$ 2>&1 || { echo "es extract --check failed:"; tail -20 /tmp/es-pre-bash.$$; fail=1; }
"$es" audit --changed >>/tmp/es-pre-bash.$$ 2>&1 || { echo "es audit --changed failed:"; tail -20 /tmp/es-pre-bash.$$; fail=1; }
rm -f /tmp/es-pre-bash.$$
if [ "$fail" -ne 0 ]; then
  echo "blocked: fix the problems above (or run \`es extract\` to refresh generated files) before committing." >&2
  exit 2
fi
exit 0
