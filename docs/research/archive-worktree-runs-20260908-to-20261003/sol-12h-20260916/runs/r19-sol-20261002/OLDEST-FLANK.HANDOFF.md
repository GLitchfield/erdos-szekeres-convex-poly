# Exact oldest singleton-flank normalization

2026-10-02, agent codex:01a0fc94-0467-7b90-823c-bce1e6fe6128.
Node `ctx_oldest_singleton_flank_normalize`, independent branch
node/CtxOldestSingletonFlankNormalize, basee3c87197b66a65092e1ffe5e9d0d8c7aa1981cf8,
unchanged type3936fca1bce6bdbd. Exact signature OLDEST-FLANK.signature.lean.txt.
Pinned commite51c80334b2da5be84b6630d5f1491129462b742, commit job
20261002-112944-616d1b. Claim released CLOSED.

The last indexed level N has exactly one external position x and maximum m>=1.
All children and all younger markers on its axis lie strictly on one side of x;
either direction and axis are allowed. Actual external labels are positive.
Other-axis markers and unindexed older positive letters are unrestricted.
No WellFormed, global-parameter lower bound or k-coupling premise is used.

Truncate maxima before N and replace its axis parameter G by min(G-1,k-m),
keeping the word. The accepted theorem proves equality of every child-endpoint
cup/cap limit, every recursive fuel bound and the full bound. Its normalization
can be iterated when a removed indexed marker remains as an unindexed letter.
It certifies the effective-parameter mechanism behind the oldest unit-flank
lift in the raw PEEL counterexample; it does not prove any singleton-selection
rule or a geometric realization.

The existing boundary-normalization theorem gives full<=normalized limits.
For the reverse, the full selected level list is the younger list followed by N.
Every sublist walk either omits N or appends it. A left walk moves only left and
a right walk only right, so the singleton is inactive in one direction and adds
at most one in the other. Hence fullChain<=oldPure+1. Younger strong-join terms
are identical because N is last; its new contribution is oldPure+m. Since m>=1,
fullJoin<=max(oldJoin,oldPure+m). Natural arithmetic, including all saturation
at zero, identifies the selected limit with the one at min(G-1,k-m), giving the
reverse inequality. The other axis is unchanged. Antisymmetry gives equality.

The word, children, runs, blocks and k agree. Normalization commutes with every
part as N shifts to N+1; its singleton, last-level identity and maximum persist.
New same-axis markers come from former children and satisfy the boundary
condition. Positive labels exclude old level0 markers from the new level1.
The boundary invariant persists, so base equality and fuel induction apply.

Original-source check20261002-112036-dd5454 CLOSED,6.431865s/909MiB,
no sorry, only propext/Classical.choice/Quot.sound, matching unchanged type/lock,
no blocked/uncovered dependencies. Full immutable receipt
62f7fe5143ebd50e933b2099cff7d0dc537303c5fdb6a214da89449c0a43ab06 is parsed in
OLDEST-FLANK.original-check.json. Changed-node audit and layers pass; all378
inherited locks unchanged, with only this one new entry. Registration
20261002-111121-506a75, frozen fixture
193d0eee92e8cf5f961ade6e494cb459fe3ae31578140ce20f5fa05791216910.

Search `boundary marker exact equality normalization oldest singleton` found no
duplicate; named search found ctx_boundary_marker_upper_normalize, reused as the
declared dependency. Library context-extension/proof APIs were inspected. The
proof reuses its compiled geometry and part transport locally. First full check
20261002-111903-8b133d failed5.629406s/808MiB only at rewriting limits inside an
unreduced base match/let. `simp only` with the proved equalities reduced it;
the target, hypotheses and guard stayed unchanged. All findings are journaled.

The singleton/last-level conditions matter: a marker level on both sides can
add two extensions, and a later indexed level changes the join history. This
theorem is not an arbitrary boundary-level equality claim. Its positive maximum
avoids a separate pure-chain saturation case; no weakening is claimed.

No new mathematical Python algorithm or tracked workflow helper. Inline text
assembly reuses frozen es proof spans and copies existing local transport at
explicit markers; durable chunks, full body and fixture are retained. Separate
code/library review is due before the next trial. Independent coordinator review
remains pending under the fixed Sol-only/no-delegation contract. Preserve the
ignored artifact root with the pinned branch; no merge or push.
