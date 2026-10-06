# Finite endpoint constraint iff — accepted general theorem

2026-10-03 20:41UTC. ErdosSzekeres.deepSplit_finite_endpoint_constraints_iff,
locked typec615cb8eb6de0c0e, CLOSED/no sorry/standard axioms. Module
ESBlueprint/B/DeepSplitFiniteEndpointConstraintsIff.lean, branch
node/DeepSplitFiniteEndpointConstraintsIff, based0e89ed2609544e39ce448340d6dbb92228a4c09.
Commit9dcbe93678f188c63a127fd37d2cacf741315e23, guarded job
20261003-164200-9b5b5a, exact five node files and no tracked remainder.
Immutable final search receiptfa2d7d7d8c413508e224aed17b05e24198b04a26451872b618009b65daf15a38.

For any deep split and arbitrary cup/cap predicates, all parent constraints
are equivalent to pure child chains and one/two exterior opposite-child
insertions. One point is a sweep endpoint of the growing chain; two points
strictly bracket it. Empty chains/children and nonmonotone predicates remain.
No OneChange, realization or positive-parameter premise is added. Partition
the chain into child intersections, classify the opposite intersection into
0/1/2 points, and use existing insertion converses; caps follow by duality.
This certifies finite gain cases. Matrix/Ctx equivalence, joint placement,
maxima and a closed N/loss formula remain separate obligations.

Search finite-endpoint-constraints-search.json found no exact predicate iff;
the proof reuses deepSplit_two_endpoint_extensions and core DS endpoint APIs.
Registration20261003-161308-b699e5/capture20261003-161540-ce46df succeeded.
Fixturea4df07d57f1ad2d6b926393308e915fca2c83e5b2d2240c540c793d09ad6e1c7.
First isolated op4c4cdb927e7a44cd/job20261003-161617-b041e0 passed
8.491s/2106MiB, receipt
fa471f5d70b01262aab407a544124b5cf34edb8210328304cf27779e4d4483bd.
Body493de697080cf7c0d9cff3ec8af65f9d9fded43057b9617095f26acaa9b77ca0;
source9cddc5ad3f33c6885aca9de5fe630d4d2bbdbb52f902ac107733d8dff1e42f45.

Final op-b9cdc49377b44cd3 succeeded; finite-endpoint-final-operation.json
contains the complete immutable stage inventory. Candidate161657-a7e37c;
source20261003-161710-3f6ed2,50.880s/2354MiB, receipt
398cdefeff8721546c360a8e8a578a5f9422359142f0d4a79d858a7ed6dab9e9;
full20261003-161804-da37f2,1346.483s/5600MiB, receipt
45eb4c0f43f6b2e341512d37b0fe01fd6bc8f129e2b6c3da93ce840c440c6555,
fresh/problems[], tree2adba9ba96ef8c36.4560d6f33c43b8ee;
audits20261003-164033-8ff8d9, receipt
3cec82ce3e95797a36884d5b7ad227592a08b4523c6e0223317bee5475d2da5d;
review20261003-164052-a728bf, receipt
f799c78fce8e48e65d06937d1461a1fa7dfed8f5be1515898995c4bf303bc8eb.
Only propext, Quot.sound, Classical.choice; audit violations[].

No failed proof body. Branch job5e4d60 failed129 on an incorrectly placed
--json before any source change; corrected/logged, successful2b4db9.
Full extraction took longer than prior16..19.5min checks; at21.6min its
heartbeat was fresh but incremental progress unavailable. A review scheduled
the next checkpoint without stopping or changing its exact question/cap.
Terminal receipt resolved the uncertainty. Documentation patch failures
were atomic, logged and corrected; no statement was hand-edited.
