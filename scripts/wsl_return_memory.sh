#!/usr/bin/env bash
# Return stale page cache from the WSL VM to Windows without root.
#
# WSL only hands memory back to the host through free-page reporting, which
# reports free blocks of 2 MB or more.  Dropping caches needs root and leaves
# fragmented free pages that are never reported.  Instead this allocates N GB
# of transparent-huge-page memory in a capped cgroup (the kernel evicts the
# least-recently-used cache to make room and compacts it into 2 MB blocks) and
# releases it; the freed 2 MB blocks are reported to Windows within a minute.
#
#   scripts/wsl_return_memory.sh [GB]      (default 8; keep below free+cache)
set -u
GB=${1:-8}
avail=$(awk '/MemAvailable/ {printf "%d", $2/1048576}' /proc/meminfo)
if [ "$GB" -ge "$avail" ]; then echo "only ${avail} GiB available; refusing" >&2; exit 1; fi
systemd-run --user --scope -q -p MemoryMax=$((GB + 1))G -p MemorySwapMax=0 -- python3 - "$GB" <<'PY'
import mmap, sys
size = int(sys.argv[1]) * 1024**3
m = mmap.mmap(-1, size, flags=mmap.MAP_PRIVATE | mmap.MAP_ANONYMOUS)
m.madvise(mmap.MADV_HUGEPAGE)
for off in range(0, size, 2 * 1024 * 1024):
    m[off] = 1
m.close()
PY
echo "released ${GB} GiB in 2 MB blocks; Windows should reclaim it within a minute"
