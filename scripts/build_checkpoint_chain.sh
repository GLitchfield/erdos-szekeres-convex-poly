#!/usr/bin/env bash
# Build a checkpoint chain PREFIX{FIRST..LAST} sequentially through the guard.
#   scripts/build_checkpoint_chain.sh PREFIX FIRST LAST [MEM] [LOG]
# Writes "chain done PREFIX LAST" (or "chain FAILED at N") to LOG.
set -u
# A chain is meant to run beside a batch stream; every job is memory-capped.
export GUARD_ALLOW_CONCURRENT=1
PREFIX=$1; FIRST=$2; LAST=$3; MEM=${4:-20G}; LOG=${5:-runs/experiments/20260903-week1/build/guard.log}
cd "$(dirname "$0")/.." || exit 2
for ((s = FIRST; s <= LAST; s++)); do
  seg=$(printf '%03d' "$s")
  out=$(scripts/guarded_lake_build.sh -m "$MEM" -c 4 -l "$LOG" "ErdosSzekeres.${PREFIX}${seg}" 2>&1)
  rc=$?
  waited=0
  while [ $rc -eq 125 ] && [ $waited -lt 240 ]; do
    sleep 60; waited=$((waited + 1))
    out=$(scripts/guarded_lake_build.sh -m "$MEM" -c 4 -l "$LOG" "ErdosSzekeres.${PREFIX}${seg}" 2>&1)
    rc=$?
  done
  if [ $rc -ne 0 ]; then
    echo "$out" | tail -15
    echo "chain FAILED at $s rc=$rc $(date '+%F %T')" | tee -a "$LOG"
    exit $rc
  fi
done
echo "chain done $PREFIX $LAST $(date '+%F %T')" | tee -a "$LOG"
