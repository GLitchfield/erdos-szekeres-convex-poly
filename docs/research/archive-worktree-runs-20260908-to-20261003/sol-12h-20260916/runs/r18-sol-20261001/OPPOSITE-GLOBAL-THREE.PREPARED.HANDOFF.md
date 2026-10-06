# R18 opposite-global-three normal-form preparation

At 2026-10-02 00:00Z: artifact-only preparation, UNREGISTERED and UNCHECKED.
Current priority is finishing the counterexample audit/commit, publishing the
active-boundary and chosen-three NF nodes, and compiling the actual full-IH
induction update. This optional route is within the same R18/C1r trial.

Proposed local class: legal uniform one-level root with opposite global3,
chosen G>=4, k>=3, 1<=m<=k-2, actual old marker/child, >=2runs, arbitrary
physical multiplicities. Its proposed full bound is
  both actual ends marked: min(G-2,k-m)-1;
  exactly one end marked:  min(G-1,k-m)-1;
  neither end marked:     min(G,k-m)-1.
ChosenG3 is separately covered by accepted local marked/unmarked classifiers;
chosen<=2, unit/empty/single/saturated edges remain in the prepared NF driver.

Reused accepted R16 source Neither-opposite-three.closed.lean:
commit b8d7aa1ca13f1ca22ab5a5697f343bbab8553b16,
type3b3e5de88d9d3684, originalcheck082439-9c20aa,
receipt a6e6966856ae4c4a800935d860ad849bffeffc3953b0d207f8e617cb81c63514.
Its4276-line prelude supplies private both-marked/exposed/reflected lower
bounds and whole-prefix complementary merge. New neither equality tail
retains the accepted first leaf1 and complement>=H-2 (H=min(G,k-m)), and adds
the actual legal full-cut lower edge to get source>=H-1; raw opposite<=3
absorbed-marker upper gives source<=H-1.

Copied72-line small-global threshold upper plus46/43-line both/exposed
normalization uppers from R16 Both-marked-small-attainment.closed.lean
(commit10301b1910f55bbc159cbf069865a9da9d29e1d2/typec380b1b17be83d25)
and Exposed-first-small-attainment.closed.lean
(commit19f3afb270ae9117fc03b0437fdb968eeb09fb57/typec8e0da0d4fb01920).
Opposite3 ensures the small-global premise. Reflected upper reconstructs WF;
the endpoint classifier and raw-context field adapter are new untested glue.

Files:
ROOT-NF-OPPOSITE-THREE.all-endpoint-signature-v1.txt
ROOT-NF-OPPOSITE-THREE.all-endpoint-body-v2.txt (4587lines/noholes)
ROOT-NF-OPPOSITE-THREE.raw-adapter-v1.txt
ROOT-NF-OPPOSITE-GLOBAL-THREE.signature-v1.txt/body-v1.txt (10874lines/noholes)
ROOT-NF-CHOSEN-GLOBAL-THREE.with-opposite3-class-carrier-v1.txt (10973lines).
The carrier keeps the chosen-three NF registered target unchanged and adds
the private opposite-three class and adapter for a possible guarded8G check.
No such job has been submitted; source remains fixed for current CEX audit.

Static assembly failure: v1 substring norm renaming accidentally renamed
hnorm declaration but not uses. Logged before repair; v1 preserved, v2 uses
token-boundary renaming and asserts no hnormBoth/hnormExposed artifacts.
This was source-review evidence, not a compiler or mathematical result.
No R16/R17 source, claim, job or tracked primary file was changed.

If this compiles and the public Opp3 NF is separately registered/audited,
the actual full-IH induction could exclude both global axes<=3. Larger
unsaturated roots with both axes>=4 still require BOTH paired-cut upper
orientations and NF lower; no assertion of general ROOT-NF/C1r closure.
