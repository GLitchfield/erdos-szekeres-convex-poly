#!/usr/bin/env bash
# Claude Code SessionStart hook: give every session a stable agent id and the frontier.
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
es="$here/../bin/es"
# Claude Code passes hook input as JSON on stdin (session_id, cwd, ...); fall back to the parent pid.
sid="$(python3 -c 'import json,sys
try:
    print(json.load(sys.stdin).get("session_id") or "")
except Exception:
    print("")' 2>/dev/null)"
sid="${sid:-${CLAUDE_SESSION_ID:-$PPID}}"
export ES_AGENT="claude-code:${sid}"
cd "$here/../../.." || exit 0
echo "es harness: agent id ES_AGENT=$ES_AGENT (export it in Bash calls; \`es claim\` records it)."
echo "Project state comes from \`es status\`; pick work with \`es ready\`; never read docs/wayfinder to learn what is open."
echo
"$es" status --brief 2>&1 | head -40 || echo "es status failed (run \`es doctor\`)"
exit 0
