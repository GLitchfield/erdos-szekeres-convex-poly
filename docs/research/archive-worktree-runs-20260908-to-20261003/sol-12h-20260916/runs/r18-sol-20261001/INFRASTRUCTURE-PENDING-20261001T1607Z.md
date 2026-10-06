At approximately16:07Z both `es --json --full job status20261001-115504-d79ec9`
and `es status` failed with sqlite3.OperationalError: database is locked at
Store's PRAGMA user_version after the busy wait. A following `es log` attempt
failed similarly at PRAGMA user_version assignment. No database or worker
mutation was attempted. This record must be entered with es log when available.

The check's immutable output was readable directly and was copied to
check-root-nf.DONE.RECEIPT.json. It confirms targeted=true, lock_ok=true,
type e0cedb9ee88cc591, sorry=true, standard axioms plus expected sorryAx.
Terminal job wait previously reported DONE rc0. The all-end deletion grid
20261001-115602-22d1a0 has no log/output yet; its result remains uncertain.

At16:16Z the lock persists. Repeated status/log/job-wait calls failed and no
new research probe was launched. Primary logs/worker-20260930.log independently
contains repeated `worker: database is locked`, confirming worker observations
are also affected. Existing other-agent computations continue emitting progress;
their jobs were not changed. Routine `job list --active` was rejected as an
unsupported flag; the correct list command is plain `job list`.
