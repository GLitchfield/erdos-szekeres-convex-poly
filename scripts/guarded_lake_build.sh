#!/usr/bin/env bash
# Run `lake build` for the given targets inside a transient user cgroup with a
# hard memory ceiling, no swap, and a CPU quota.  If the ceiling is exceeded the
# kernel kills a compiler inside the cgroup; the WSL VM and every other process
# survive.  Records elapsed time, peak cgroup memory and OOM-kill count.
#
#   scripts/guarded_lake_build.sh [-m 20G] [-c 4] [-t 2] [-l LOG] Target [Target...]
#
# -m  MemoryMax for the whole build (default 20G).  ES6 checkpoint segments peak
#     near 14 GiB at 192-segment granularity; Fin13 clause chunks need about 15 GiB
#     each (run them one per invocation at 20G); ES6 clause chunks stay under 1 GiB.
# -c  CPU cores (CPUQuota = 100% * cores; default 4)
# -t  LEAN_NUM_THREADS per compiler (default 2).  This does NOT bound how many
#     compilers Lake starts (one per unbuilt module, up to the core count):
#     bound parallelism by passing few unbuilt targets per invocation.
# -l  append the one-line record to LOG
#
# Exit status is lake's (125 = guard refused to start).  A record with
# oom_kills>0 means the cap was hit and the build output is incomplete.
set -u
MEM=20G; CPUS=4; THREADS=2; LOG=""
while getopts "m:c:t:l:" opt; do
  case "$opt" in
    m) MEM=$OPTARG ;; c) CPUS=$OPTARG ;; t) THREADS=$OPTARG ;; l) LOG=$OPTARG ;;
    *) echo "usage: $0 [-m MEM] [-c CPUS] [-t THREADS] [-l LOG] Target..." >&2; exit 2 ;;
  esac
done
shift $((OPTIND - 1))
[ $# -ge 1 ] || { echo "no build targets given" >&2; exit 2; }
cd "$(dirname "$0")/.." || exit 2
avail_gb=$(awk '/MemAvailable/ {printf "%d", $2/1048576}' /proc/meminfo)
mem_gb=${MEM%G}
if [ "$avail_gb" -lt $((mem_gb + 6)) ]; then
  echo "guard: only ${avail_gb} GiB available; refusing to start a ${MEM} build" >&2
  exit 125
fi
# Language-server processes (lean --server / --worker) are not compilers.
compilers=$(pgrep -x lean | while read -r pid; do
  tr '\0' ' ' < "/proc/$pid/cmdline" 2>/dev/null | /usr/bin/grep -qE -- '--server|--worker' || echo "$pid"; done | wc -l)
if [ "$compilers" -gt 0 ] && [ "${GUARD_ALLOW_CONCURRENT:-0}" != 1 ]; then
  echo "guard: $compilers lean compiler(s) already running; refusing (GUARD_ALLOW_CONCURRENT=1 overrides)" >&2
  exit 125
fi
stats=$(mktemp)
start=$(date +%s)
systemd-run --user --scope -q \
  -p MemoryMax="$MEM" -p MemorySwapMax=0 -p CPUQuota="$((CPUS * 100))%" \
  -- env LEAN_NUM_THREADS="$THREADS" STATS="$stats" bash -c '
    lake build "$@"; rc=$?
    cg=/sys/fs/cgroup$(cut -d: -f3 /proc/self/cgroup)
    { cat "$cg/memory.peak" 2>/dev/null || echo 0
      awk "/^oom_kill /{print \$2}" "$cg/memory.events" 2>/dev/null || echo 0; } > "$STATS"
    exit $rc' _ "$@"
rc=$?
end=$(date +%s)
peak=$(sed -n 1p "$stats" 2>/dev/null); ooms=$(sed -n 2p "$stats" 2>/dev/null); rm -f "$stats"
line="$(date '+%F %T') rc=$rc elapsed=$((end - start))s peak=$(( ${peak:-0} / 1048576 ))MiB oom_kills=${ooms:-?} mem=$MEM cpus=$CPUS threads=$THREADS targets=$*"
echo "guard: $line" >&2
[ -n "$LOG" ] && echo "$line" >> "$LOG"
exit $rc
