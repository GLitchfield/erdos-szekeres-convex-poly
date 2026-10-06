# Continuation at 2026-09-09 22:55 UTC

The explicitly authorized12-hour goal is ACTIVE, no token budget. Fixed start2026-09-09T19:32:21Z; deadline2026-09-10T07:32:21Z (3:32a.m.EDT). Do not reset timer or complete beforedeadline+checked handoff. User's quiet foreground worker works; do not ask to restart. Autonomous selection/registration/proofs/checks/commits/immediate pushes authorized. No parallel proof agents. Previous turn made progress: published12 fully, compiled13, prepared counting/reduction drafts and focused finite evidence.

ROOT=/home/gavin/git/erdos-szekeres-convex-poly
WT=ROOT/runs/worktrees/codex-01a07c5a
OUT=ROOT/runs/2026-09-09-lemma-continuation
ES_AGENT=codex:01a087a7-d0cf-7e23-8514-e295400a06ee. Use OUT/es wrapper. ES_PROJECT_ROOT=WT,ES_HOME=ROOT/.es. Git in WT uses git --git-dir=.git-data --work-tree=.; preserve inherited modified harness/config.toml and sharedrootmain/otheragentfiles. RootAGENTS/restart/Lean skill read earlier. No need reread.

All>1mincommands through es job run, normally OUT/submit.py. Proof/build/targetedchecks3G; fullrefresh28G serialized with Lean;publication2G;shared30G. Small256Mdiagnostics may overlapfullrefresh. Everycheck MUST use `check NODE --targeted --budget 10`, no extra positionalnode; run_es.py guards this after the earlier dispatch incident. Fullrefreshhelper restores3Gconfig. No bare large lake builds, no axioms/native_decide/sorry outsideblueprint. Newstatements onlynodeadd/restate; keepregisteredheader byteidentical. Searchbeforedraft;status/extract/ready/claimbeforeformalwork;one node/branch;accuraterelease;logplan changes. Commentary at least every60sec—break up long theory reasoning with updates.

## Twelve fully published results; thirteenth audit LIVE

All first12 theorem proof commits AND full-index commits are checked and pushed. run.json contains exact hashes/results. Baseline114closed; last verifiedfullstate126closed,11open,1parentclaim,1refuted,stale=[],problems=[]. The new13is nowpending, so expectonlyitsmodule/Blueprintstaleness.

Latest12:ctx_chain_one_straddling_unique_axis_level,stemchain-one-straddling.
-18lines,firstbuild3.2826sec,561MiB; standardaxioms only; no sorry;lockedstatementhash3d07f1b5bade1583.
-Registration20260909-183734-3a87eb;build20260909-183945-b1cc83;targetedaudit20260909-184006-ce651b;allpassed.
-Proofpublish20260909-184234-055457 passed,pushed b96cb9fb512a78b862a4247da01cb23eca1003a5.
-Fullrefresh20260909-184259-46b8ee passed,treehash7a0c46d5009faf49,139nodes.
-Indexpublish20260909-184939-a9bb2e passedallchecks,pushed287a6f5aa550f9d89149431724a9c9981e3cce17.
-Node12claimreleasedclosed.

CURRENT13:ctx_two_boundary_marker_upper_normalize,stemtwo-boundary-upper.
-Branch node/ctx_two_boundary_marker_upper_normalize.
-Registration20260909-185225-a1959b passedin103.9sec;claimeduntil06:54Z.
-Typehash11770e0686ca19a6.
-397linebodyAPPLIED with unchanged registeredheader.
-FIRSTBUILD20260909-185436-5f9be6 PASSED4.6258sec,754MiB. Outputtwo-boundary-upper-build-1.json. One harmless unused-simp linter warning.
-**LIVE TARGETED AUDIT20260909-185459-65acba**,cap3G,outputtwo-boundary-upper-check.json. Queued/started22:54:59Z. **POLL THIS NEXT**.
-Ifauditpassesok/locktrue/nosorry/standardaxioms,IMMEDIATELY publishproofviaOUT/publish_node.py two-boundary-upper under2G; then28Grefresh_after_node.py; then2Gpublish_node_refresh.py. Do not repeatregistration/build.
-Afterfull-indexpush,settwo-boundary-erase-spec.json expected_headfromACTUALindexcommit;freshstatus/readythenregister14.

Commands (expandOUT):
```
python3 OUT/submit.py NODE 3G STEM-check.json 'purpose' python3 OUT/run_es.py STEM-check.json check NODE --targeted --budget 10
python3 OUT/submit.py NODE 2G STEM-published.json 'purpose' python3 OUT/publish_node.py STEM
python3 OUT/submit.py NODE 28G STEM-full-refresh.json 'purpose' python3 OUT/refresh_after_node.py NODE STEM
python3 OUT/submit.py NODE 2G STEM-refresh-published.json 'purpose' python3 OUT/publish_node_refresh.py NODE STEM
```
Wait and inspecteachdependentresult. UseactualreturnedjobIDs;neverguessanID. One brieflymistypedmanifestIDfor13buildwasimmediatelycorrectedtoreturned5f9be6; allcurrentrecordsuseactualID.

## Prepared searched drafts after13, unregistered/uncompiled

Eachstemhas-signature.txt,-body.txt,-description.txt,-pr-body.md,-spec.json. Expectedbranchesarechained;expected_headsetonlyafteractualprecedingindexpush. No22draftwascreated.

14.two-boundary-erase:ctx_two_boundary_marker_erase_normalize,455lines. DoubleboundaryG-2/k-M normalization,eraseonlyoldestchosenlevel,keepolderoppositehistory. Generatorprepare_two_boundary_erase.py.
15.chain-one-two-level:ctx_chain_one_children_exterior_of_two_levels,35lines. Purechain≤1forceschildrenintocommonexterioroftwoactualchosenlevels,withoutglobal/k/activityassumptions.
16.active-two-boundary-rank:ctx_active_two_boundary_marker_rank_union_bound,604lines. Activechildren/youngerchosenpositionsbracketedatindexedlevel,min(G-2,k-M)≤3;exactopposite rankunion,inactivechildrenarbitrary.
17.separating-marker-normalize:ctx_separating_marker_erase_normalize,814linesLATEST. Selectedmarker separatesallchildren/youngerchosenpositions fromolderchosenpositions. Eraseonlyit,chosenG-1,samek. Exportschildpositions,depth-1,survivingindexedext/side/max,oppositepuretraceequality,POSITIVELABELS,endpoint/fuel/fullmonotonicity. **NO k-M cap**:strongervariantfalse. Generatorprepare_separating_normalize.py andseparator-greedy-fragment.txtmustbeupdatedconsistentlywhenfuturedebugging. PositivityusesexistinghErasePositivehelper.
18.separating-retained-rank:ctx_separating_marker_retained_boundary_rank_union_bound,125lines. Allsourcechildrenactive,G≤5,separatorconditions,explicitolderboundaryandsurvivingyoungerboundarycondition;normalize17thenoldlinearboundarytheorem;exactsourceopposite-rankunion. Generatorprepare_separating_retained_rank.py.
19.triple-face-interval:rank_triple_face_interval_union_card_sq,76lines. Exactunionoforderedtriplefacesanchoredatintervalendpoints=w²,includingemptyinterval. Finitecountonly. Generatorprepare_triple_face_interval.py.
20.NEW triple-face-group:rank_triple_face_union_card_eq_group_charges,246lines. Grouptriplefacesbylowerleft/upperrightendpointsaroundpivot,mergeonlyifintersect. Ordinarygroupsorderedpairrankcount;mergedgroup rankunioncard². Finitecountonly. Adaptscheckedrow/columnproof,uses19. Generatorprepare_triple_face_group.py. Searchproofs/triple-face-group-search.json.
21.NEW triple-face-reduction:ctx_youngest_marker_triple_face_bound_of_anchored_square,371lines. **CONDITIONAL** fulltriple-faceboundatG≤5 fromexplicit universallyquantifiedanchored-squarehypothesis. Thehypothesisallowsmixedcapacities,nestedindividualrankintervals,inactivechildren;leftactivechildrenpinlowerrankendpointtomarker,rightactivechildrenpinupperendpoint. Conclusionofhypothesisisfullbound≤active-rankunioncard². Reductionuses13'spredecessor11boundarypairs,capacity-threegroupdecomposition9,andfinitegroupcount20. hsquareisatheoremARGUMENT,notanaxiom;itisUNPROVED. DoNOTreport21asunconditionalcontextsquareorfacebound. Generatorprepare_triple_face_reduction.py. Searchproofs/triple-face-reduction-search.json.

No newerproofwasinsertedintoworktreeexceptregistered13. PreparedscriptgenerationonlywritesOUTdrafts. FuturepotentialLeanissuesin17–21mustbefixedinbody/generatorwithoutchangingregisteredheaders.

## Mathematical corrections and evidence

Readhigher-capacity-square-route.md for currentunprovedresearch; earlierpartscontainhistoricaldraftstatus, latestcorrectionsbelowtakeprecedence.

Importantcorrection: mergedpivotgroup doesNOTnecessarilyhaveidenticalindividualoppositerankintervals. Leftmemberssharelo(x)butmayhavesmallerhi;rightmemberssharehi(x)butmayhavelargerlo. Merge witnessesmaketheUNION Icc(lo(x),hi(x)). Thusanall-source-uniform-traces/all-chosen-capacity-three squaretheoremdoesnotautomaticallyimplyfullfacecontrol. MixedcapacitiesANDnestedintervalsneedhandling. Draft21statespreciseremaininganchoredhypothesisratherthanhidingthisgap.

Inductioncaution: run-groupdecomposition usesFULLgroupbounds,notsamefuels. Asame-fuelmutualinductionbetweenuniformsquareandfullfacepotentialwouldbecircularwithoutanadditionalargument. Child-countinductionmightwork;groupsretainingallchildrenneedadirectcase. ExistingboundFuel_mono+boundFuel_eq_boundgiveeachfuel≤fullbound.

Newfocuseddiagnostic:anchored-nonuniform-square-probe.json,job20260909-184642-ec68a8,done0,58.57sec.12000rawcontexts,6822anchored,490completedUNEQUALintervalcases,78timeouts;nosquare/facefailure. All490positive;233withsomechosenC3,107allactivechosenC3,214mixedcapacities,24tightsquareexamples. Of490,81haveoverlappingfaces/fullpivotintervalwitnessesonbothsides;49ofthesearemixedcapacity. Classificationanchored-nonuniform-merge-analysis.json. **Finiteevidenceonly**.

Earlierdiagnosticsandcounterexamplespreserved:
-own-zone-path-probe:445contexts,328low/55highcompleted,62timeouts,nofailureforrefinedz*w-minus-occupied-adjacencyedgeschargeandhightriangle+far-exterior*(w-1). Nooppositehistoryinthatsample.
-FALSE oldlowchargez*(w-1)+1:SS E1.lower E2.lower E1.lower S,max[3,0],a7,u5,k9,width6,zones02,allchosenC2,ownbound12>11. Wholecuttotalsbelow36;directsourceFtimedout5sec. Recordsown-zone-charge-probe.json/own-zone-counterexample-cut.json.
-FALSE strongerseparatorcap:SE1.lowerE2.lower,max[4,0],a6,u5,k6,origbound1;erase1/Gminus1bound5;addk-Mcapbound0. Recordseparating-marker-stronger-rejection.json.17mustnotassertthatcap.
-chosen-five-small-face-probe:922complete,78timeouts,185nonuniformintervals,nofailure. Earlierlargerprobe83complete88timeouts. Notexhaustive.

UsefulALREADYPROVEDlemmasfound/reviewedthisturn—donotduplicate:
-ctx_bound_le_one_of_common_singleton_rank:arbitraryglobals,inactivechildren,commonavailablesingletonrank⇒allfuel/full≤1;removinganactivewitnessonasame-axispartannihilatesit. Searchproofs/existing-common-singleton-rank-search.json.
-ctx_bound_mono_of_marker_inclusion:withsamechildpattern,length,depth,k,preservedindexedsideAt,subsetmarkerpositions/lowermaxima/largerglobal⇒endpoint/fuel/fullboundscanonlyincrease. Searchproofs/existing-marker-inclusion-search.json. Italreadytransportsgreedywitnessesbyskippingnewlyunneededlevels;naivesame-subsequencegreedycomparisonisfalse.
-Promisinglow-zoneuse:clipfaroccurrencesoftheNEWuniform-sidechosenleveltounindexedmarkers,retaininganactualnearwitness. Thenallretainedyoungerpositionsmaybeononesideofolderchosenboundary;oldboundarynormalizationreducesG5→4whilekeepingyoungeractualmarker,sooldG4doubledrankboundgives2w−1foradjacentzones. Generalgeometrycasesnotyetproved. Forrawmixed-sidelevels,mustproveindexedsideAtunchanged;deletingfirst/alloccurrencesisnotautomaticallyvalid.

## Timer/worker/checkpoints

Awakejob20260909-153542-ad824c remainslive;WindowsSetThreadExecutionStateconfirmed;heartbeatlastread22:56:07Zinthisturn,workercontinuousjobsprovequeuealive. Refreshactualscopeearlier~5.2GiB,noOOM. Readjobs/keep-awake-state.jsonperiodically. Linuxlogindinhibitordeniedearlier,recorded. Bootidca967a75-a19a-45df-bbd0-58a14b1e2600. Awakefallbackuntil08:32:21Z. OnlycreateOUT/stop-awakeafterfinalcheckedhandoff;leaveuserworker.

02hcheckpointcompleted21:32:29Z,job20260909-173224-5006eb. **NEXTCHECKPOINT23:32:21Z,label04h**,then01:32,03:32,05:32,07:32. Usecheckpoint.py04hthroughsubmit.py256Moutputcheckpoints/04h.json. Avoidmanifestpublicationmutationoverlap. DoNOTrepeat02horresettimer.

At07:32:21Zstopnewresearch,releaseparentctx_bound_additive_sandwich_one_singleton_endBEFORElongaudit(TTLshortlyafterdeadline),finish/safelycheckpointwork,verifyproofs/standardaxioms/pushes/fullindex,releaseclaims,writecheckedfinalreport,nextsteps/resources,stopawakeprocess,thenmarkgoalcomplete. Fullconjecture/parentremainOPEN. Automaticgoalcontinuationsareworking;keepgoalactiveacrossturns.
