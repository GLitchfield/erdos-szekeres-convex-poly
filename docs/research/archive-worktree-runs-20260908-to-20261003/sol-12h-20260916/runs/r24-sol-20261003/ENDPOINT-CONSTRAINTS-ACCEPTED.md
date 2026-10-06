# Accepted exact endpoint constraints

2026-10-03 19:44 UTC. General theorem
`ErdosSzekeres.deepSplit_endpoint_constraints_iff`, module
ESBlueprint/B/DeepSplitEndpointConstraintsIff.lean, unchanged type
`1cf6dd851989965c`. CLOSED, no sorry, standard axioms only
(propext, Classical.choice, Quot.sound). Full finalization accepted.
One-node commit `469c5d2f64db029ed7301d6831f9d99334a45542` is on
node/DeepSplitEndpointConstraintsIff, base1a83a001. Guarded commit
20261003-154410-f1d8f1 changed exactly the module, root import, lock, index
and status; no tracked files remain uncommitted. No merge/push.

At an arbitrary deep-below split, arbitrary predicates on cup/cap finite sets
hold for every parent chain iff they hold for pure upper cups, pure lower
caps, and lower cups/upper caps augmented by opposite-child sweep endpoints
of the entire union. Empty children and chains are included. No one-change,
realizability, positivity or separated-root assumption is used.

Sufficiency: an opposite endpoint cannot be the middle vertex of a triple;
the middle lies in the growing chain, so each crossing triple has its cup/cap
color. Necessity: mixed chain intersections inherit their chain color and
existing DS endpoint geometry forces all opposite points to be endpoints.
Pure chains cover the case missing the growing child. This certifies the
chain-constraint component of exact profile gluing, alongside accepted strong
coupling. Joint placement, occupancy, formal maxima and closed loss remain open.

Receipts:

* Registration20261003-151925-c3b1be,101.4s/2304MiB; fixture
  7ff2b06c57ad0359311c989264cf85cf9ea63131aecc7c38245e1bcd42265dc5.
* First isolated body20261003-152330-84ec23,6.083s/2101MiB,
  receiptb8925e8865a3e9c11b8b1257b3c01bce20750b3a89bccaf28c124b3e9c17224d.
* Final operationop-04d29d5693eb4132 succeeded; candidate
  20261003-152409-d86a66, original-source20261003-152415-279b17,
  44.941s/2357MiB, receipt1829b401906940378878809411876e89f94a86fbfa1ef8fe925c1d623ba1c830.
* Full20261003-152506-455222,1082.401s/5667MiB, fresh/problems[],
  tree5df559e0699b1169.4560d6f33c43b8ee,
  receipt7cb54f097d27c5cb8e1e22ad0ababf856cf34e8542b49185fc33772286b7441e.
* Audits20261003-154310-d94c96,
  receipt8d1c76321ac8e3c3e6ccd9dc89551ea4b644e2fbdb6c5d03b3665ba8b564e0ad.
* Review20261003-154323-1509dd,
  receipt2cb14d7b5d5b5bbad9e54a1dd013e16ac79d02a342351c3ad9d7ae90d0226a6d.

Source4335799e0c3612fec028554c5d6b8c4cc244f074c2520e8b0121e56599cbd521;
body2c6663853f5054cb4f15589ae40a41736b9ad6bd9200eee30f8096be24eba67e.
Search426418254a3759ba2228dcc7fad7dfac647a5c1a8aaa7ee153a2b02d7fa9c319.
Exact operation files endpoint-constraints-final-operation.json and
endpoint-constraints-isolated-operation.json preserve all details.
Next: PROFILE-GLUING-EXISTS-PROOF-PLAN.md's independent-color constructor.
The native fixed deadline remains active.
