# Remove exterior unindexed padding without a WellFormed premise

R19's exact oldest-flank normalization retains the removed level's marker.
After truncating both old unit flanks of3U4LSS1L2USS, its prefix3U4L is
unindexed and the actual two-level core is SS1L2USS. Proving that exterior
unindexed padding can be erased makes the effective-parameter explanation
literal, instead of feeding a non-WellFormed raw state to a WellFormed-only
induction. This does not rescue full raw PEEL or characterize actual histories.

For a raw context sigma and exterior lists left/right whose labels exceed
sigma.maxima.length, let tau.word=left++sigma.word++right with identical globals
and maxima. The constant order embedding f(i)=left.length+i sends all children
and every indexed level's positions to their tau counterparts. Padding has
neither children nor indexed markers, so it changes neither run count nor
sideAt/maximumAt of a level used by an extension fold. Strict order comparisons,
getLast?/head? of filtered external positions and the fold count commute with f.
Thus all transported endpoint limits agree, including virtual endpoints.

After any part, every padding label increases by1 and maxima.length increases
by1; the strict unindexed inequality survives. Kept child positions map by f,
and the shifted prefix has the same length. Parts therefore commute with
padding, contiguous blocks/rest filters correspond, and fuel induction proves
boundFuel equality. Child-position lengths agree, yielding full bound equality.

The target handles both exterior sides simultaneously, arbitrary raw inner
words, labels and maxima, no global legality or positivity hypothesis. It does
not erase an unindexed marker strictly between children, where removing a
separator changes the run recursion. No sufficient feasibility or general
singleton-selection assertion is made.

Searches unindexed external erase, unindexed padding bound found no duplicate.
Existing ctx_bound_external_letter_contraction already handles adjacent
identical letters through position geometry; it is not changed. Reuse ordered
fold and part APIs, with scalar position translation rather than a duplicate
letter expansion. All proof/compiler work remains guarded es work.
