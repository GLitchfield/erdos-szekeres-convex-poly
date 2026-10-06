# R16 neither-marked opposite-three selector implementation plan

Current time12:11Z, same active native trial. No proof written yet.
Node ctx_one_level_root_first_singleton_cut_attains_of_neither_marked_opposite_global_three.
Branch node/CtxOneLevelRootFirstSingletonCutAttainsOfNeitherMarkedOppositeGlobalThree
from approved5847. Branchjob080918-146c21 done; targeted registration081048-12920c
queued20G/review5. Wait terminal, inspect locked type, claim before proof edit.
Do not edit registered statement.

Prospective next selector class (not registered/proved yet): opposite global exactly3,
legalG>=3,k>=3,m1..k-2,uniformheadchild/lastchild,actualoldmarker,2runs.
LetH=min(G,k-m), choosefirstp0 leaf on oppside withc=k-2, complement oldside maximum1.
Original upper<=H-1 follows absorbed-marker small-opposite upper (accepted sixteenth helper).
First leaf has T(2,V,k)=1 forV=min(G-1,k-m)>=2.
Complement prefix merge RETAINS G, mergedmaximum=max(1,m+1)=m+1,
wordheadmarker/lastchild. EffectiveW=min(G-1,k-m-1)=H-1.
H2 needs only nonnegativecomplement; H>=3 makesm+1<=k-2, so mirroredunrestricted
exposed-endlower applies under legalWFroot reflection and gives T(3,W,k)=H-2.
Thus leaf1+comp>=H-1 and original<=H-1 =>first cut attains.
No runcontraction/singletonexchange assumption. This is only oppositeA3, notA>=3.
Implementationreuse: exposedLowerPrefix172077chars; genericize exposedLowerTail
G,m to H,M with explicitlegalityparams; localrootWF from neitherRootWFOriginal1913chars
genericize M/hM/hMk; reflectiononlyonlegalroots, no raw-inert reflection.
Need hAnyExposedPoint/hLeafAnyExposed by replacing last-marker witness with
actualmarker witness (headchild makesalloldmarkers>0); hComplementNeither modifies
hComplementPrefix last-marker to last-child, keeps first-prefixmerge same, proves
lastpositioninps and maps child unchanged. Sourceupper localcopy accepted16v2 ifpasses.
es semanticsearch on opposite-three neither-first selectorreturnednohits.
All larger oppositeglobals/dynamiccoupling anddegenerateA2/G3 remainopen.


Proof construction:
1. Reuse frozen Exposed-first-lower.closed.lean/accepted14 and its 172077-character
   exposedLowerPrefix. Set local A:=3, hA:3<=A, hAk:A<=k from hk before prefix.
   Import its five modules plus CtxSmallGlobalAxisRankRegionPotential and
   CtxBoundReverse. Keep maxHeartbeats30M/maxRecDepth20000, all compiler guarded.
2. Genericize accepted14 exposedLowerTail's hExposedLower over H,M with explicit
   hH:3<=H,hHk:H<=k,hM:1<=M,hMk:M<=k-2. Replace its G/m/hG/hGk/hm/hmk references;
   truncate its final outer cases side. All geometric/both-marked lower helpers
   already generic and fixed only in outer A/k. New local lower must support M=m+1.
3. Copy checked rootWF helper from accepted13, stored neitherRootWFOriginal
   (1913chars), genericize M/hM/hMk instead of outer m/hm/hmk. RootWF takes actual
   a/u>=2<=k and uniformword. Define local marked-first/exposed-last lower by
   applying generic exposed lower to reversedword; head?_reverse/getLast?_reverse
   and mem_reverse as accepted13. Original legal root WF gives ctx_bound_reverse.
   Only full root-bound reflection needed; no part/run/head-index transport.
4. Add actual old marker position witness from List.mem_iff_getElem? and extPositions.
   hAnyExposedPoint is accepted hExposedPoint with last-marker condition replaced
   by actualmarker. Obtain y in extPositions1, use hOldAfterZero for0<y; own chain1,
   joinM and emptyotheraxis are unchanged. No last-marker bracket needed.
5. hLeafAnyExposed is accepted hLeafExposed with actualmarker replacing hl;
   old-side witness comes from marker, hRP uses hAnyExposedPoint. Keeps same first
   child p=0, ps nonempty, opposite singleton maximum K-B+1, and exact threshold.
6. hComplementNeither is accepted hComplementPrefix with lastletter CHILD and
   actualmarker. Normalize prefix exactly as before; older markers allafterp0,
   so G stays unchanged, maxima[max(B-2,M+1)]. Output firstmarker/LASTCHILD.
   At lastpositionL=wordlength-1, use hlast to show original letterAtL=child.
   psnonempty gives q>p=0 and q<wordlength, hence length>=2/L!=p; cp=p::ps
   impliesL inps. part_letterAt_of_child+if_pos keeps lastchild, mergeLetter
   keeps it. Rest of prefixmerge/uniformword/firstmarker/child witness proof unchanged.
7. Nest exact accepted16 upper proof as local hUpper(A,G,k,m,hsmallA<=3,side,word,
   uniform,actualmarker), reusing Absorbed-small-opposite-upper.closed.lean body.
   It is fully generic/raw and requires no new proof route. Outer Alet3 supplies <=3.
8. Main generic v/w: numRuns>=2 => cp=p::ps/hne. H=min(G,k-m)>=2, V=min(G-1,k-m)>=2.
   Source upper H-1. Opposite firstleaf maximum k-2 has T(2,V,k)=1 by classical
   threshold choose0 (V<=k). Complement selected1 exact prefixmerge gives M=m+1.
   IfH>=3, Mlegal<=k-2, reflected lower gives T(3,W,k)=W-1=H-2,
   W=min(G-1,k-m-1)=H-1. IfH=2 use nonnegativecomp only.
   Thus H-1<=leafbound+compbound. Compose source upper; restore raw leaf threshold
   with ctx_singleton_part_bound_eq_threshold, filter!=p=ps and coupledmax=1.
   Final cases side discharge canonical-record matcher differences.

This plan has no theorem credit until complete targeted check. No C1, X, N_ends
constant or other sorry is used. If fails, freeze and log exact compiler failure
before repair. Accepted16 receipt213b5c72... and all exact helpers in their handoffs.

Parallel reporting duty: full k6 diagnostic20261001-074826-da70dd remains active,
2944roots/100-root checkpoints,1G, no time deadline; lastreview1200/999.8s,0FIRST/LAST,
next12:15:35Z. Observe/review/inspect terminal automatically while proof work proceeds.
k5 complete1242/32076/0FIRST/LAST,46fixedcouplingfailures; no targetcounterexample.
Keep reporting turn open. No verifiedcallback/delegation.

Consolidation16:34:46.416915Z/research17:04:46.416915Z/final17:34:46.416915Z unchanged.
Nativegoal forbids earlycompletion. Renew N_root claim at consolidation if needed
to coverfinalization (TTLdoesnotextenddeadline). Do not merge/push/full extract.
