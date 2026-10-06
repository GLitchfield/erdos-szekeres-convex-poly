# R17 shared database lock checkpoint

Observed2026-10-01 16:07:40 UTC. es search (two independent queries),
es job status and es job wait failedrc2 in Store.__init__ at PRAGMA
user_version with sqlite3.OperationalError: database is locked. This is
not a job result and does not justify resubmission or cancellation.
No database, worker, resource ledger, config, or other agent's job repaired.

Preserve these admitted own jobs and inspect them first when reads recover:

- 20261001-115632-75eac4: chosen-axis-two actual-domain falsifier; last queued.
- 20261001-115641-e36234: whole-declaration chosen-axis-two candidate;
  operationop-92b54f84aec4439a, fixture
  b6f2aff058979497d42abc171c52f766443b8802b2d27cf4226f73a09a502d7e;
  last queued. Module retains its original sorry while the candidate is tested.
- 20261001-120051-be1a93: retained rescue geometry analysis; last queued,
  declared outputrescue-geometry-analysis.json absent at checkpoint.
- 20261001-120253-d8afde: longest chosen-global-three candidate timing;
  last queued, declared outputtiming-chosen-three-k7.json absent at checkpoint.

Current branchnode/CtxOneLevelRootSingletonBaseExchangeChosenAxisTwo,
approved5847base, registered/claimed node. Source and candidate scripts
remain stable for admitted jobs. Four previously closed commits and receipts
are listed in ACCEPTED-INVENTORY.md and require no rerun because of this lock.

The two new lemma-search queries have no valid result: "num runs remove
singleton adjacent child pair" and "child outside adjacent pair two runs".
Do not write a new lemma based on those failed searches; retry after recovery.
Journal this failure and checkpoint once es log can write again.
