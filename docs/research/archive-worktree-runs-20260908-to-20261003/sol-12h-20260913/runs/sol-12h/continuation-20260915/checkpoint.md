# Sol/xhigh continuation checkpoint

- Window: `window-c8d65fe03ead46dd`; research deadline
  `2026-09-16T02:41:07.111516Z`; consolidation begins
  `2026-09-16T02:11:07.111516Z`.
- Agent: `codex:agent-run-0ce68047e38845f0`; native thread
  `01a0a676-12ca-7482-8951-4ddf01a9e12c`.
- Baseline commit: `8ae570bb` on `harness/sol-12h-post-review`; tracked tree was clean on
  admission. Previous segment contributed ten accepted theorems; continuation result count starts
  at zero.
- The required `AGENTS.md`, Lean skill, continuation plan, reconstructed report, and prior
  `runs/sol-12h/research-checkpoint.md` were read before proof work.
- Initial authoritative check reported 227 closed, 12 open, one refuted, but the compiled frontier
  was stale at `88950c5a`. Guarded job `20260915-150649-9a2aa1` refreshed the full index at current
  HEAD with the documented 28 G reservation and exited successfully. Its receipt is
  `initial-extract.json`: 240 nodes, 17 destinations, 12,910 declarations, no problems, and tree
  hash `7ec690dd0cbb848d`.
- Fresh `es status --brief` still reports 227 closed, 12 open, one refuted at `8ae570bb`; full parent
  context now reports matching current/indexed hash `7ec690dd0cbb848d` and
  `frontier_fresh=true`. The parent is ready, its previous claim expired, and there is no live
  mathematical claim. No theorem credit is attached to this operational refresh.
- Transition: retain the approved parent as the single research objective, claim it under this
  continuation identity, then select one exact compiling helper that removes the residual mixed
  small-maximum/capacity obstruction rather than accumulating an unrelated easy lemma.
- Claimed the parent through `2026-09-16T03:18Z`. Exact `es search` for a coupled six-point
  older-exterior cut returned no hits. Guarded branch job `20260915-152123-12c07b` renamed the
  branch to `node/CtxOlderExteriorInternalComplementCutSixBound`; targeted 20 G registration job
  `20260915-152157-312033` elaborated the new statement.
- New continuation theorem candidate:
  `ctx_older_exterior_internal_complement_cut_six_bound`. It sharpens the exact internal cut in
  the residual two-marker companion from 13 to 12 under `k=6` and the legal positive coupling.
  The proof retains the checked boundary-pair charge of at most three, uses a sibling-maximum-one
  bound at coupling endpoints, and the arbitrary-opposite-history saturated nonmonotone bound of
  nine for the two middle maxima.
- Compiler transition: targeted checks `20260915-152621-adf4df`,
  `20260915-152705-128f0e`, `20260915-152745-6e9b46`, `20260915-152824-5dd47a`,
  `20260915-152919-5dad2c`, `20260915-152951-560664`, `20260915-153051-91f78f`,
  `20260915-153144-4c5af6`, `20260915-153217-8a266c`, `20260915-153400-dba0b0`,
  `20260915-153448-c9cfde`, and `20260915-153518-0d03d8` exposed only local elaboration issues
  around dependent side matches. Reordering the side-independent saturated estimate before the
  boundary construction and making the `t` cases local resolved them. Targeted check
  `20260915-153609-a4c4a2` then passed in 97.24 s; its extracted declaration has no axioms and
  `git diff --check` is clean.
- Full extraction job `20260915-154050-ca7ee0` passed with 241 nodes, 17 destinations, 12,910
  declarations, no problems, and fresh tree hash `d744aef67fcb857e`. The authoritative frontier
  moved to 228 closed, 11 open, one refuted. The new theorem is sorry-free and uses only
  `propext`, `Classical.choice`, and `Quot.sound`; `es audit --changed` and `es layers --base HEAD`
  both passed. Local reviewed commit `29f32cfc` (`Sharpen the six-point older-exterior cut`) records
  the first mathematical continuation result. The tracked worktree is clean; nothing was pushed.
- The durable outer host is job `20260915-150549-609c48` (2 G). No delegation, alternate model,
  Astra mathematical hint, cloud proof, model download, purchase, push, or publication has occurred.
- Endpoint transition: exact search found no existing theorem that combines a sibling maximum at
  least `k-3` with upper normalization and the exact width-three potential. Guarded registration
  job `20260915-155124-f11902` added
  `ctx_bound_le_opposite_width_of_sibling_maximum_ge_k_minus_three` on its own node branch.
  Two fast checks (`20260915-155512-4c87d6`, `20260915-155542-13047a`) exposed only dependent-match
  elaboration and match/subtraction normalization issues. After explicit side splits, guarded check
  `20260915-155615-d27b96` passed: the theorem is sorry-free, has only `propext`,
  `Classical.choice`, and `Quot.sound`, and its 2.83 s module build peaked at 585 MiB. Changed-file
  audit, layer audit, and `git diff --check` are clean. A full frontier extraction is next before
  this second continuation result is committed and consumed by the coupled endpoint proof.
- Full extraction job `20260915-155902-37e35f` passed with 242 nodes, 17 destinations, 12,910
  declarations, no problems, and tree hash `c0d79dcf6a627eba`. The authoritative frontier is now
  229 closed, 11 open, one refuted at `29f32cfc`; the normalization theorem is fully indexed as
  sorry-free with only the standard three axioms. Exact search for the intended coupled
  older-exterior endpoint theorem returned no duplicate. The clear-opposite-history case actually
  needed by the two-marker reduction admits charges `10+1`, `9+3`, `4+8`, and `1+11` for new
  chosen maxima one through four; this is the next substantive node.
- One-hour milestone (recorded just after the wall-clock boundary): two compiling, fully extracted
  continuation results are locally committed (`29f32cfc`, `89d40558`), moving the authoritative
  frontier from 227/12/1 to 229/11/1. The third substantive result is underway. Guarded branch job
  `20260915-160735-b61b5f`, registration job `20260915-160800-18cb92`, and statement-restatement
  job `20260915-161105-37e7fe` created the exact `k=6` older-exterior endpoint node with the width
  lower bound actually required by its linear charge. Proof fixture
  `b9f481113eedecea80d1fb9d28283e3d85857f531090a05a7a675c5ce2077df4` was captured before
  checking. First targeted check `20260915-161525-d2a3a8` found only source/part field
  normalization failures; the four-case mathematical decomposition remains intact.
- Endpoint result: a second normalization-only check `20260915-161727-41260d` failed, then explicit
  source/part axis equalities made targeted check `20260915-161836-2f41e7` pass in 144.68 s. Full
  extraction job `20260915-162111-0da266` passed in 476.3 s at 5,415 MiB, producing 243 nodes,
  17 destinations, 12,910 declarations, tree hash `13dcf93b4a77c3ab`, and the authoritative
  frontier 230 closed, 11 open, one refuted. Its requested output path was not created because
  `es extract` emits JSON only to stdout; the complete result remains in the guarded job log and
  harness index rather than a fabricated receipt file. The first 20 G restatement job had in fact
  been refused by the nested 28 G extractor and its shell pipeline masked that status. Corrective
  guarded restatement job `20260915-163012-c386d8` succeeded at 28 G; the node and lock now share
  type hash `f034d2b8abb7e6d3`. The theorem is sorry-free with only `propext`,
  `Classical.choice`, and `Quot.sound`; changed audit, layer audit, and whitespace check all pass.
  Local reviewed commit `10118339` (`Sharpen the six-point older-exterior endpoint`) records this
  third continuation result; the tracked worktree is clean and nothing was pushed.
- Younger-endpoint transition: exact search found no duplicate. The rank analysis replaces the
  coarse `10+3` small-maximum charge by `10+2`: the new boundary marker is terminal on its clear
  axis and the ordered old markers contribute two full-history ranks on the other axis. For
  `m=3,4`, the already checked `4+8` and `1+11` branches apply. Guarded registration job
  `20260915-163647-0529ba` created
  `ctx_two_marker_younger_exterior_endpoint_cut_six_bound`; proof fixture
  `493a40c6778d0432100065bc42ff5a9f3d867a1179b47e28df328e8c972166e1` records the draft.
  Initial targeted check `20260915-164159-7f332a` exposed four local rewriting/list-pattern
  issues. After those repairs, targeted check `20260915-164243-726529` passed; its module build
  took 4.3 s. Full extraction is next.
- Full extraction job `20260915-164550-60d033` passed in 484.7 s at 5,395 MiB with tree hash
  `3c6b848146be2621`. The authoritative frontier is 231 closed, 11 open, one refuted; the new node
  and statement lock agree at type hash `1de2f0bef8088095`. It is sorry-free with only the standard
  three axioms. Changed audit (219 declarations), layer audit, and whitespace check all pass. Local
  reviewed commit `0bcc5b13` (`Sharpen the six-point younger-exterior endpoint`) records the fourth
  continuation result; the tracked worktree is clean and nothing was pushed.
- Endpoint-classification transition: exact search found no theorem closing the coupled `k=6`
  endpoint cut or isolating its remaining order obstruction. Guarded branch job
  `20260915-165516-3f1b71` and registration job `20260915-165537-4228b5` created
  `ctx_two_marker_endpoint_cut_six_obstruction_classification`. The proof first returns either
  literal kept-point witnesses straddling `x` or `y`; when neither marker is surrounded, the four
  relative-order cases are discharged by the two exact exterior theorems and the already sharper
  inward/between bounds. Targeted check `20260915-165939-9b39ee` passed on the first attempt, and
  proof fixture `27d9ab2d436bcd44a678d6461c83f00b1d5ea6961845f09808141a072a0f53f3`
  captures the compiling draft. Full extraction job `20260915-170227-c835eb` was refused before
  compilation because the nested extractor's default 28 G request exceeded its enclosing 20 G
  guard. The retry `20260915-170324-503a6b` explicitly caps the nested extractor at 18 G; prior
  measured full-extraction peaks are about 5.4 GiB. The retry passed in 475.4 s at 5,391 MiB,
  producing tree hash `51215f3852f771f6` and moving the authoritative frontier to 232 closed,
  11 open, one refuted. The node and statement lock agree at type hash `22c4a81450dbc64d`; the
  theorem is sorry-free with only `propext`, `Classical.choice`, and `Quot.sound`. Changed audit
  (220 declarations), layer audit, and whitespace check all pass. This is the fifth mathematical
  continuation result. Local reviewed commit `94a2d319` (`Classify the six-point endpoint
  obstruction`) records it; the tracked worktree was clean afterward and nothing was pushed.
- Surrounding-marker transition: the old-surround branch needs a width bound on the chosen
  complement before the legal `m+n=5` coupling can save the final unit. Exact searches for the
  nested-boundary normalization/rank statement returned no registered theorem, although the same
  local argument occurs throughout the existing two-marker cut developments. Guarded branch job
  `20260915-171221-bfb865` and registration job `20260915-171241-a0bd5f` created
  `ctx_nested_boundary_markers_rank_budget` as a standalone result. The first targeted check
  `20260915-171432-1722e7` exposed one omitted positivity fact from the source local proof; after
  restoring it, check `20260915-171456-e60bf0` passed. Proof fixture
  `4fdaf91ba593f2e75018b0c2a3dff978d86daf5b80b5b1202deb372a441b98b7`
  captures the repaired theorem. Full extraction job `20260915-171543-5bb886` passed in 477.0 s
  at 5,391 MiB, producing tree hash `a214a4409ee7f37c` and frontier 233 closed, 11 open, one
  refuted. The theorem and statement lock agree at `dc1db0d8f73feb5c`; it is sorry-free with only
  the standard three axioms. Changed audit (221 declarations), layer audit, and whitespace check
  pass. Local reviewed commit `8b238564` (`Extract nested boundary marker rank budget`) records
  this sixth continuation result; the tracked worktree was clean afterward and nothing was pushed.
- Older-surrounded complement transition: guarded branch job `20260915-172434-7a6853` renamed
  the branch (the journal marks its zero-exit execution `unknown_execution` only because the short
  worker process lacked a termination acknowledgement), and registration job
  `20260915-172546-8e6f7f` added
  `ctx_surrounded_older_marker_endpoint_complement_width_bound`. It splits source child runs at the
  older marker, prunes the new boundary level to a single occurrence, and applies the newly
  standalone nested-boundary budget on the surviving side. Proof fixture
  `2164c9181c901c8309b762599d5523768d876e9e86210f122e5521b969eebaa4` was captured;
  targeted check `20260915-172825-79a004` passed on the first attempt. Full extraction job
  `20260915-172952-4378ca` passed in 480.7 s at 5,394 MiB, producing tree hash
  `8667f090d955718f` and frontier 234 closed, 11 open, one refuted. The node and lock agree at
  `5e9b86d76152fd4d`; it is sorry-free with only the standard three axioms. Changed audit (222
  declarations), layer audit, and whitespace check pass. Local reviewed commit `50e2da14` (`Bound
  an older-surrounded endpoint complement`) records this seventh continuation result; the tracked
  worktree was clean afterward and nothing was pushed.
- Exact older-surround transition: search found no existing coupled `k=6` theorem. Guarded branch
  job `20260915-173841-131968` and registration job `20260915-173903-1c5a5f` created
  `ctx_two_marker_older_surrounding_endpoint_cut_six_bound`. It combines the new complement-width
  theorem with the legal maxima cases `4+1`, `4+4`, `4+8`, and `1+9`. Targeted checks
  `20260915-174254-1bd993` and `20260915-174339-60b68c` exposed only dependent-side-match
  normalization; after explicit side cases and simplifying the chosen-global hypothesis, check
  `20260915-174419-727eec` passed. Proof fixture
  `83e307ec9353b27f078f4d3dc87e078a5a758bcc74c14569aa4f752849a0b61d`
  captures the compiling theorem. Full extraction job `20260915-174701-e6692e` passed in 479.0 s
  at 5,403 MiB, producing tree hash `710f28dfdee33a27` and frontier 235 closed, 11 open, one
  refuted. The node and lock agree at `4103ab3975e7d81a`; it is sorry-free with only the standard
  three axioms. Changed audit (223 declarations), layer audit, and whitespace check pass. Local
  reviewed commit `8fea7aa5` (`Sharpen the older-surrounding endpoint at six`) records this eighth
  continuation result; the tracked worktree was clean afterward and nothing was pushed.
- Younger-only surround transition: exact searches found no standalone retained-boundary doubled
  rank theorem or younger-surrounded complement-width-plus-one theorem. Guarded branch job
  `20260915-175547-750ec5` renamed the branch (again with a harmless zero-exit
  `unknown_execution` journal status), and registration job `20260915-175703-98bada` created
  `ctx_boundary_retained_doubled_rank_budget`. The promoted proof normalizes at the retained outer
  marker and applies the one-level refined potential to the residual rank union. Proof fixture
  `4fd44af9120c11647798edf6fc63214cd358e24356329b80dec493f1a8f38c87` was captured;
  targeted check `20260915-175917-7c086f` passed on the first attempt. Full extraction job
  `20260915-180016-d36bf1` passed in 601.2 s at 5,397 MiB, producing tree hash
  `4f77904b7de79e9c` and frontier 236 closed, 11 open, one refuted. The node and lock agree at
  `4ca433989fed9ad8`; it is sorry-free with only the standard three axioms. Changed audit (224
  declarations), layer audit, and whitespace check pass. Local reviewed commit `90d64159`
  (`Extract retained-boundary doubled rank budget`) records this ninth continuation result; the
  tracked worktree was clean afterward and nothing was pushed.
- Three-hour milestone (`2026-09-15T22:05Z`): eight fully extracted, locally committed
  continuation theorems have moved the authoritative frontier from 227 to 235 closed nodes while
  leaving the 11 pre-existing open goals and one refuted node unchanged. The ninth theorem already
  passes its targeted check and is undergoing full extraction. The work has closed both exterior
  endpoint orientations, isolated the exact surrounding-marker obstruction, exported two hidden
  reusable boundary estimates, and closed the older-surrounding case at twelve. The remaining
  endpoint task is the younger-only surround branch, whose existing local estimates total at most
  ten. No delegation, alternate model, Astra mathematical hint, cloud proof, model download,
  purchase, push, or publication has occurred.
- Three-marker exterior transition: exact search found no registered theorem for the local
  three-ordered-marker singleton-rank argument. Guarded branch job `20260915-181122-86257d` and
  registration job `20260915-181136-fa535b` created
  `ctx_three_ordered_markers_exterior_unit_bound`. The proof derives a three-step pure-chain rank
  on the side opposite every exterior child and invokes the common-singleton-rank theorem. Proof
  fixture `3912b75699fb3b8838d5772438fb81cf39bfc14fa89bffe5bc648741ca298e31`
  was captured; targeted check `20260915-181353-74a72a` passed on the first attempt. Full
  extraction job `20260915-181440-a5dc71` passed in 564.6 s at 5,414 MiB, producing tree hash
  `510891917db35d2f` and frontier 237 closed, 11 open, one refuted. The theorem and lock agree at
  `56e89398d7f95b25`; it is sorry-free with only `propext`, `Classical.choice`, and `Quot.sound`.
  Changed audit (225 declarations), layer audit, and whitespace check pass. Local reviewed commit
  `a4aeddab` (`Extract three-marker exterior unit bound`) records this tenth mathematical
  continuation result; the tracked worktree was clean afterward and nothing was pushed. The first
  separately queued commit attempt `20260915-182447-dc635a` overlapped its separately queued index
  add and failed harmlessly on the transient git index lock; retry `20260915-182509-0dddbd` passed.
- Younger-surrounded complement transition: exact search found no standalone width-plus-one
  theorem. Guarded branch job `20260915-182529-a31bce` and registration job
  `20260915-182547-7527f8` created
  `ctx_surrounded_younger_marker_complement_width_plus_one_bound`. It splits child runs at the
  younger marker, bounds the exterior group by the new three-marker theorem, bounds the other
  group by a single-occurrence-pruned nested-boundary budget, and recombines them with the
  capacity-three run decomposition. Proof fixture
  `d63c2b1783af5e0c36ecee043f98d28a3d6265858483e29d59cc1831bff03be9` was captured; guarded
  targeted check `20260915-182718-924453` passed on the first attempt. The direct preflight check
  at `20260915-182713` made no build attempt because the sandbox could not reach the systemd user
  bus; the guarded worker check is authoritative. Full extraction job
  `20260915-182908-e1a05d` passed in 538.8 s at 5,391 MiB, producing tree hash
  `6c22a5d095678d04` and frontier 238 closed, 11 open, one refuted. The theorem and lock agree at
  `bee7b432732c042c`; it is sorry-free with only the standard three axioms. Changed audit (226
  declarations), layer audit, and whitespace check pass. Local reviewed commit `245d1155` (`Bound
  a younger-surrounded endpoint complement`) records this eleventh mathematical continuation
  result; the tracked worktree was clean afterward and nothing was pushed.
- Younger-only endpoint transition: exact search for a younger-only surrounding endpoint bound-ten
  theorem returned no hits. Guarded branch job `20260915-183859-4e3106` and registration job
  `20260915-183920-59fe48` created
  `ctx_two_marker_younger_only_surrounding_endpoint_cut_ten_bound`. The theorem intentionally
  omits `k=6` and the maxima coupling: the chosen complement costs at most `w+1`, the retained
  companion costs at most `2*(w-1)-1`, and the opposite global hypothesis gives `w≤4`, hence a
  uniform sum at most ten. Proof fixture
  `d5061369f8ef00bafd57473025b645bb94c5db8a8f05f2446195ab70ead26dc8` was captured; guarded
  targeted check `20260915-184149-cbd8e1` passed on the first attempt. Full extraction job
  `20260915-184344-5bc7c9` passed in 597.0 s at 5,404 MiB, producing tree hash
  `bdd01a73ab3bc490` and frontier 239 closed, 11 open, one refuted. The theorem and lock agree at
  `cb20cd98973ad3cc`; it is sorry-free with only the standard three axioms. Changed audit (227
  declarations), layer audit, and whitespace check pass. Local reviewed commit `ef6ebc81` (`Close
  the younger-only endpoint cut at ten`) records this twelfth mathematical continuation result;
  the tracked worktree was clean afterward and nothing was pushed.
- Exact endpoint transition: exact search found no theorem closing every two-marker endpoint case
  at twelve. Guarded branch job `20260915-185434-b44cb8` and registration job
  `20260915-185450-234113` created `ctx_two_marker_endpoint_cut_six_bound`. Its short proof applies
  the obstruction classifier, dispatches older-marker surrounds to the exact coupled theorem, and
  dispatches the younger-only surround to the stronger bound-ten theorem before lifting to twelve.
  Proof fixture `f3730adb62c6ca758717f4ba8cd99b7bceaae0ce41263dd38fac54ff3011a528`
  was captured; guarded targeted check `20260915-185842-01a0b2` passed on the first attempt. Full
  extraction job `20260915-190201-9fef26` passed in 588.3 s at 5,395 MiB, producing tree hash
  `cdc45eda5d71fb17` and frontier 240 closed, 11 open, one refuted. The theorem and lock agree at
  `28d6699a9fb55107`; it is sorry-free with only the standard three axioms. Changed audit (228
  declarations), layer audit, and whitespace check pass. Local reviewed commit `b1fde93c` (`Close
  every two-marker endpoint cut at six`) records this thirteenth mathematical continuation result;
  the tracked worktree was clean afterward and nothing was pushed.
- Internal-complement saturation transition: exact search found no `k=6` theorem below opposite
  global five. A plan-change log records that the obstruction classifier potential is at most
  eight when the opposite global is at most four, while its older-exterior alternative is already
  exact at twelve; hence only saturated opposite global five remains. Guarded branch job
  `20260915-191304-9f00d8` and registration job `20260915-191324-11737c` created
  `ctx_two_marker_internal_complement_cut_six_bound_of_opposite_global_le_four`. The first targeted
  check `20260915-191611-3f5200` exposed only an omitted positivity fact needed to rule out level
  zero while deriving empty history below the younger marker. After restoring it, proof fixture
  `91061837787fbdb54bd4216d1c793350e86d8ee863b2fc86d9045a4043263bf9` was captured and guarded
  check `20260915-191701-7cfb1c` passed. Full extraction job `20260915-191937-5baa27` passed in
  523.4 s at 5,410 MiB, producing tree hash `1820dde899d7b46b` and frontier 241 closed, 11 open,
  one refuted. Changed audit (229 declarations), layer audit, and whitespace check pass; the
  extraction reported no problems and retained the standard trusted environment. Local reviewed
  commit `0edb4ffd` (`Close low-width internal cuts at six`) records this fourteenth mathematical
  continuation result; the node was released closed and nothing was pushed.
- Saturated younger-surrounding internal transition: exact search found no registered bound-ten
  theorem. Guarded branch job `20260915-192922-700bb6` renamed the branch (with the familiar
  harmless zero-exit `unknown_execution` journal status). Initial registration job
  `20260915-193036-8e231f` preserved the generated statement but refused because its 4 GiB outer
  cap was below the nested extraction request; exact retry `20260915-193100-8e5a64` under 20 GiB
  registered `ctx_two_marker_younger_surrounding_internal_complement_cut_ten_bound`. The proof
  combines the exported complement bound `w+1` with the triangular retained-part budget after two
  unit boundary losses; opposite global at most five gives `w≤4`, so the total is at most ten.
  First targeted check `20260915-193402-20679d` exposed only an under-specified symbolic binomial
  comparison. After making its upper endpoint explicit, proof fixture
  `9e576658bcf788a26b33cadfc2eb00dd739cc2a3486773ec9c42e0d9cb4201be` was captured and guarded
  targeted check `20260915-193447-4348d8` passed, with no sorry and only the standard three axioms.
  Full extraction job `20260915-193625-9169f0` passed in 486.0 s at 5,396 MiB, producing tree hash
  `39e58053b38cb352` and frontier 242 closed, 11 open, one refuted. Changed audit (230
  declarations), layer audit, and whitespace check pass. Local reviewed commit `3a2ad60d`
  (`Sharpen younger-surrounding internal cuts`) records this fifteenth mathematical continuation
  result; the node was released closed and nothing was pushed.
- Between-case helper transition: exact search found no registered youngest-middle-marker
  doubled-width theorem. Guarded branch job `20260915-194526-7fb5ab` renamed the branch (again
  recorded as harmless zero-exit `unknown_execution`), and registration job
  `20260915-194639-cff13b` created `ctx_youngest_middle_marker_doubled_width_bound`. The promoted
  proof splits child runs at the oldest marker, bounds both pruned groups by one opposite width
  through the nested-boundary theorem, and recombines them with the capacity-three decomposition.
  Proof fixture `3c93f4667e7bcc1bde89347de09898fb51300253223e76dd879c6738135eb65e`
  was captured; guarded targeted check `20260915-194820-dc2afa` passed on the first attempt. Full
  extraction job `20260915-194944-29eded` passed in 481.2 s at 5,391 MiB, producing tree hash
  `f9fb63be8d383f20` and frontier 243 closed, 11 open, one refuted. Changed audit (231
  declarations), layer audit, and whitespace check pass. Local reviewed commit `c7bfd4e3`
  (`Extract middle-marker doubled-width bound`) records this sixteenth mathematical continuation
  result; the node was released closed and nothing was pushed.
- Exact between-markers transition: exact search found no bound-ten theorem. Guarded branch job
  `20260915-195835-e623e1` and registration job `20260915-195849-1b83ea` created
  `ctx_two_marker_between_internal_complement_cut_ten_bound`. It applies the newly exported
  doubled-width complement bound and the nested-boundary budget with two unit losses to the kept
  part; `w≤4` makes `2w+(w-2)≤10`. Proof fixture
  `61ce5a815931e74fb327648876555309fe7d176709bff6e4ef8ee28faa0f28bf` was captured; guarded
  targeted check `20260915-200129-93287a` passed on the first attempt. Full extraction job
  `20260915-200252-cf21d5` passed in 497.6 s at 5,397 MiB, producing tree hash
  `9cc1a80b944402b2` and frontier 244 closed, 11 open, one refuted. Changed audit (232
  declarations), layer audit, and whitespace check pass. Local reviewed commit `72e7ee72`
  (`Sharpen between-marker internal cuts`) records this seventeenth mathematical continuation
  result; the node was released closed and nothing was pushed.
- Exact internal residual-classifier transition: exact search found no classifier isolating only
  the older-surround and younger-exterior configurations. Guarded branch job
  `20260915-201224-15216d` and registration job `20260915-201244-d322b8` created
  `ctx_two_marker_internal_complement_cut_six_residual_classification`. It dispatches younger
  surrounds and between-marker intervals to the two bound-ten theorems, derives empty younger
  history from the exact two-marker hypothesis, and dispatches older-exterior intervals to the
  coupled bound-twelve theorem. First targeted check `20260915-201506-e7bedb` exposed only the
  omitted positivity fact needed when deriving empty history below the younger level. After
  restoring it, proof fixture
  `1551be1c69c058906eef94e9179d61d93765f24ad61196f5f3f06c0c1b672100` was captured and guarded
  targeted check `20260915-201541-8d9fbc` passed. Full extraction job
  `20260915-201739-8b718e` passed in 489.0 s at 5,399 MiB, producing tree hash
  `1f19aab28a9fe5e1` and frontier 245 closed, 11 open, one refuted. Changed audit (233
  declarations), layer audit, and whitespace check pass. Local reviewed commit `3d74615c`
  (`Isolate two saturated internal cut residuals`) records this eighteenth mathematical
  continuation result; the node was released closed and nothing was pushed.
- Older-surround helper transition: exact search found no standalone doubled-width complement
  theorem. Guarded branch job `20260915-202651-793bc2` and registration job
  `20260915-202707-f91cfa` created
  `ctx_surrounded_older_marker_complement_doubled_width_bound`. The promoted proof splits runs at
  the older marker, prunes the base-level occurrence separately on both arms, applies nested
  boundary budgets, and recombines the arms at cost `2w`. Proof fixture
  `49864d3a4788309b2cfe0e249512e18bdbc28fa36a855b31a60bf58cfdfae35d` was captured; guarded
  targeted check `20260915-202951-15d96b` passed on the first attempt. Full extraction job
  `20260915-203122-c7f6dd` passed in 489.1 s at 5,394 MiB, producing tree hash
  `2bfa45cf19cb57b0` and frontier 246 closed, 11 open, one refuted. Changed audit (234
  declarations), layer audit, and whitespace check pass. Local reviewed commit `b454c8b4`
  (`Extract older-surround complement bound`) records this nineteenth mathematical continuation
  result; the node was released closed and nothing was pushed.
- Older-surround extreme-maximum transition: exact search found no theorem closing the `m=1` or
  `m=4` coupled cases. Guarded branch job `20260915-204040-08b456` and registration job
  `20260915-204059-ed9a4d` created
  `ctx_two_marker_older_surrounding_internal_complement_cut_six_bound_of_extreme_maximum`. The
  proof combines the new `2w` complement theorem with the two-loss triangular retained-part
  theorem. At `m=1`, coupling forces retained maximum four and retained bound one; at `m=4`, the
  complement itself has bound one. Proof fixture
  `1f0e549362e712fdb443f9fcafce951ad3efaced7c8301b21391b60c5cc3a119` was captured; guarded
  targeted check `20260915-204348-1ff349` passed on the first attempt. Full extraction job
  `20260915-204524-a072a5` passed in 491.0 s at 5,393 MiB, producing tree hash
  `1feebfc0dbbfd9d8` and frontier 247 closed, 11 open, one refuted. Changed audit (235
  declarations), layer audit, and whitespace check pass. Local reviewed commit `67d0847c`
  (`Close extreme older-surround maxima`) records this twentieth mathematical continuation
  result; the node was released closed and nothing was pushed.
- Middle-residual classifier transition: exact search found no classifier carrying the narrowed
  maximum range. Guarded branch job `20260915-205433-beb879` renamed the branch (with a harmless
  zero-exit `unknown_execution` journal status), and registration job `20260915-205549-117c11`
  created `ctx_two_marker_internal_complement_cut_six_middle_residual_classification`. Its short
  proof applies the prior residual classifier, closes older-surround `m=1` or `m=4` with the new
  exact theorem, and uses positivity plus coupling to label every remaining older-surround branch
  by `m=2 ∨ m=3`. Proof fixture
  `77f1beaa371edfc859efe8605e4192cf5115d8b1452aaee6d20774a3ed8b4003` was captured; guarded
  targeted check `20260915-205818-3cc627` passed on the first attempt. Full extraction job
  `20260915-210014-c409a3` passed in 487.8 s at 5,389 MiB, producing tree hash
  `2f9e3e650cdcf64a` and frontier 248 closed, 11 open, one refuted. Changed audit (236
  declarations), layer audit, and whitespace check pass. Local reviewed commit `337e20db`
  (`Narrow internal cuts to middle residuals`) records this twenty-first mathematical continuation
  result; the node was released closed and nothing was pushed.
- Six-hour milestone (`2026-09-16T01:05Z`): 21 compiling, fully extracted continuation results
  were locally committed, moving the frontier from 227/12/1 to 248/11/1. Every two-marker endpoint
  cut at `k=6` was closed. Internal complement cuts were reduced to an older-surround branch with
  `m=2 ∨ m=3` and a younger-exterior branch; the next work was to expose the latter branch's hidden
  component estimates. The parent remained honestly claimed and open.
- Three-marker triangular-potential transition: exact search found no standalone theorem exposing
  the three ordered marker argument hidden inside the younger-exterior proof. Guarded branch job
  `20260915-210924-10f212` and registration job `20260915-210942-c2e096` created
  `ctx_three_ordered_markers_triangular_plus_one_bound`. The promoted proof partitions child runs
  at the oldest marker, charges one arm by the complete opposite-rank-pair triangle, forces a
  common singleton rank on the exterior arm from the three-marker chain, and recombines at
  triangular potential plus one. Proof fixture
  `76faaae97b812d8df466974d806df7fee970016d24c7ca58b4dead2571cc67ef` was captured; guarded
  targeted check `20260915-211338-255168` passed on the first attempt in 72.3 s at 2,340 MiB.
  Full extraction job `20260915-211510-a97141` passed in 486.1 s at 5,398 MiB, producing tree
  hash `8a1fab8ec8e34a08` and frontier 249 closed, 11 open, one refuted. Changed audit (237
  declarations), layer audit, and whitespace check pass. Local reviewed commit `8bda993d`
  (`Extract three-marker triangular-plus-one bound`) records this twenty-second mathematical
  continuation result; the node was released closed and nothing was pushed.
- Active separating-marker pruning transition: exact search found the stricter all-active
  separating-marker rank-union theorem but no standalone wrapper that tolerates inactive source
  children. Guarded branch job `20260915-212418-b1f729` and registration job
  `20260915-212436-6ae22c` created
  `ctx_active_separating_marker_retained_boundary_rank_union_bound`. The promoted proof derives
  the capacity-three condition from the separator, prunes inactive children while transporting all
  marker and rank data, applies the all-active theorem, and pulls the unchanged exact rank set back
  to the source context. Proof fixture
  `3239e424f61a39c47ba32218ce0e06a4263698dbca23d10d4bca9d5c6f3ed349` was captured; guarded
  targeted check `20260915-212705-b2b1b0` passed on the first attempt in 78.7 s at 2,335 MiB.
  Full extraction job `20260915-212841-b55c44` passed in 492.8 s at 5,394 MiB, producing tree
  hash `739aed599c31241a` and frontier 250 closed, 11 open, one refuted. Changed audit (238
  declarations), layer audit, and whitespace check pass. Local reviewed commit `f71a4cd3`
  (`Extract active separating-marker rank wrapper`) records this twenty-third mathematical
  continuation result; the node was released closed and nothing was pushed.
- Saturated top-width residual transition: exact search found no classifier combining the
  lower-width closure with the middle-maximum positional residuals. Guarded branch job
  `20260915-213756-110887` renamed the branch (with the already observed harmless zero-exit
  `unknown_execution` journal status), and registration job `20260915-213847-b25eb9` created
  `ctx_two_marker_internal_complement_cut_six_top_width_middle_residual_classification`. Its
  composition proof applies the exact opposite-global-at-most-four theorem below saturation and
  otherwise uses arithmetic plus the middle-residual classifier to attach opposite global exactly
  five to every remaining case. Proof fixture
  `ca4ed1e965b0adc1aa5dc9edbc2a533ce3f4d338c7ba7f3550fb654d6fad6496` was captured; guarded
  targeted check `20260915-214314-70520b` passed on the first attempt in 116.5 s at 2,376 MiB.
  Full extraction job `20260915-214530-3c3b53` passed in 484.8 s at 5,393 MiB, producing tree
  hash `46400e9f4f7a0708` and frontier 251 closed, 11 open, one refuted. Changed audit (239
  declarations), layer audit, and whitespace check pass. Local reviewed commit `031229ca`
  (`Isolate saturated internal cut residuals`) records this twenty-fourth mathematical continuation
  result; the node was released closed and nothing was pushed.
- Committed-frontier finalization: guarded full extraction job `20260915-215942-c30717` reran at
  reviewed theorem HEAD `031229ca`, passed in 496.1 s at 10,770 MiB, and produced tree hash
  `ea7bef4ca32b0635`. It changed only generated provenance metadata, replacing the last node's
  provisional `uncommitted` opening with `2026-09-15` and anchoring the authoritative 251/11/1
  frontier to `031229ca`. Metadata-only commit `bec4c12d` (`Refresh final compiled frontier`)
  records that refresh and is not counted as a mathematical result. Parent context now reports
  identical current/indexed tree hashes and `frontier_fresh=true`; the tracked worktree is clean.
- Consolidation milestone (`2026-09-16T02:11Z`): no further nodes were opened after the required
  cutoff. Final changed audit (239 declarations), layer audit, whitespace check, and tracked-tree
  check all pass. The parent claim was released `partial` with the exact saturated residual and
  next componentwise/extreme-maximum route recorded. Final status is 251 closed, 12 open, one
  refuted, no claims, and a fresh frontier at tree `ea7bef4ca32b0635`. The durable report is
  `runs/sol-12h/continuation-20260915/REPORT.md`; usage synchronization and window closure remain
  scheduled for the frozen `2026-09-16T02:41:07Z` deadline.
- Host-finalization anomaly: durable outer host job `20260915-150549-609c48` terminated with rc 1
  at `2026-09-16T02:23:44Z`, 1,042 seconds before the frozen deadline, because the native-goal
  monitor classified the intentional verified deadline hold as `goal_blocked`. The job was neither
  OOM-killed nor over budget (`budget_exceeded=false`, 520 MiB peak), and emitted handoff artifact
  `21fa6ac58f8fe1ade0cbc37b6f6bae7407c5fc7f290db8171918cd4eb89ecbb6`. No Lean or repository
  work was active or lost. The goal/window resumed at `02:30:05Z` for the permitted finalization
  path; the host was not restarted and no deadline was extended.
- End milestone (`2026-09-16T02:41:31Z`): final usage synchronization imported 1,861 records
  through `02:41:26Z` with zero reconciliation delta. Window `window-c8d65fe03ead46dd` was closed
  `complete` with 24 accepted results. Recorded usage is 269,471,305 input tokens, 266,068,608
  cached input tokens, 516,572 output tokens, 134,835 reasoning-output tokens, and 3,402,697
  uncached input tokens. The parent remains released partial; final status, audits, fresh frontier,
  commits, report, next action, and host pause are all recorded above. No work was pushed or
  published.

- Astra final review correction: provider serverOverloaded caused the 02:23:44Z stop; resumed host job 20260915-223000-612416 continued the same thread with unchanged deadlines and completed at 02:44:45Z. The earlier intentional-hold/no-host-restart explanation was incorrect. The native session totals include 14 finalization responses outside the closed research window. See corrected REPORT.md and coordinator accounting.
