module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 193. -/

theorem fin15Anchored_clause24704 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3919 chi ∧
      ¬Fin15AnchoredAtom1708 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1708 Fin15AnchoredAtom3919 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09412
  ] at hbad
  tauto

theorem fin15Anchored_clause24705 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3919 chi ∧
      Fin15AnchoredAtom1244 chi ∧
      Fin15AnchoredAtom1247 chi ∧
      Fin15AnchoredAtom1262 chi ∧
      Fin15AnchoredAtom1283 chi ∧
      Fin15AnchoredAtom1708 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1244 Fin15AnchoredAtom1247 Fin15AnchoredAtom1262
    Fin15AnchoredAtom1283 Fin15AnchoredAtom1708 Fin15AnchoredAtom3919 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09412
  ] at hbad
  tauto

theorem fin15Anchored_clause24706 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3920 chi ∧
      ¬Fin15AnchoredAtom1244 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1244 Fin15AnchoredAtom3920 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17604
  ] at hbad
  tauto

theorem fin15Anchored_clause24707 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3920 chi ∧
      ¬Fin15AnchoredAtom1248 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1248 Fin15AnchoredAtom3920 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17604
  ] at hbad
  tauto

theorem fin15Anchored_clause24708 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3920 chi ∧
      ¬Fin15AnchoredAtom1263 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1263 Fin15AnchoredAtom3920 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17604
  ] at hbad
  tauto

theorem fin15Anchored_clause24709 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3920 chi ∧
      ¬Fin15AnchoredAtom1284 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1284 Fin15AnchoredAtom3920 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17604
  ] at hbad
  tauto

theorem fin15Anchored_clause24710 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3920 chi ∧
      ¬Fin15AnchoredAtom1709 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1709 Fin15AnchoredAtom3920 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17604
  ] at hbad
  tauto

theorem fin15Anchored_clause24711 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3920 chi ∧
      Fin15AnchoredAtom1244 chi ∧
      Fin15AnchoredAtom1248 chi ∧
      Fin15AnchoredAtom1263 chi ∧
      Fin15AnchoredAtom1284 chi ∧
      Fin15AnchoredAtom1709 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1244 Fin15AnchoredAtom1248 Fin15AnchoredAtom1263
    Fin15AnchoredAtom1284 Fin15AnchoredAtom1709 Fin15AnchoredAtom3920 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17604
  ] at hbad
  tauto

theorem fin15Anchored_clause24712 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3921 chi ∧
      ¬Fin15AnchoredAtom1246 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1246 Fin15AnchoredAtom3921 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06340
  ] at hbad
  tauto

theorem fin15Anchored_clause24713 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3921 chi ∧
      ¬Fin15AnchoredAtom1264 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1264 Fin15AnchoredAtom3921 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06340
  ] at hbad
  tauto

theorem fin15Anchored_clause24714 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3921 chi ∧
      ¬Fin15AnchoredAtom1285 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1285 Fin15AnchoredAtom3921 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06340
  ] at hbad
  tauto

theorem fin15Anchored_clause24715 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3921 chi ∧
      ¬Fin15AnchoredAtom1710 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1710 Fin15AnchoredAtom3921 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06340
  ] at hbad
  tauto

theorem fin15Anchored_clause24716 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3922 chi ∧
      ¬Fin15AnchoredAtom1247 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1247 Fin15AnchoredAtom3922 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10436
  ] at hbad
  tauto

theorem fin15Anchored_clause24717 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3922 chi ∧
      ¬Fin15AnchoredAtom1286 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1286 Fin15AnchoredAtom3922 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10436
  ] at hbad
  tauto

theorem fin15Anchored_clause24718 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3922 chi ∧
      Fin15AnchoredAtom1245 chi ∧
      Fin15AnchoredAtom1247 chi ∧
      Fin15AnchoredAtom1265 chi ∧
      Fin15AnchoredAtom1286 chi ∧
      Fin15AnchoredAtom1711 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1245 Fin15AnchoredAtom1247 Fin15AnchoredAtom1265
    Fin15AnchoredAtom1286 Fin15AnchoredAtom1711 Fin15AnchoredAtom3922 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10436
  ] at hbad
  tauto

theorem fin15Anchored_clause24719 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3923 chi ∧
      ¬Fin15AnchoredAtom1248 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1248 Fin15AnchoredAtom3923 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18628
  ] at hbad
  tauto

theorem fin15Anchored_clause24720 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3924 chi ∧
      ¬Fin15AnchoredAtom1246 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1246 Fin15AnchoredAtom3924 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12484
  ] at hbad
  tauto

theorem fin15Anchored_clause24721 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3924 chi ∧
      ¬Fin15AnchoredAtom1247 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1247 Fin15AnchoredAtom3924 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12484
  ] at hbad
  tauto

theorem fin15Anchored_clause24722 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3924 chi ∧
      ¬Fin15AnchoredAtom1267 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1267 Fin15AnchoredAtom3924 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12484
  ] at hbad
  tauto

theorem fin15Anchored_clause24723 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3924 chi ∧
      ¬Fin15AnchoredAtom1288 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1288 Fin15AnchoredAtom3924 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12484
  ] at hbad
  tauto

theorem fin15Anchored_clause24724 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3924 chi ∧
      ¬Fin15AnchoredAtom1713 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1713 Fin15AnchoredAtom3924 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12484
  ] at hbad
  tauto

theorem fin15Anchored_clause24725 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3924 chi ∧
      Fin15AnchoredAtom1246 chi ∧
      Fin15AnchoredAtom1247 chi ∧
      Fin15AnchoredAtom1267 chi ∧
      Fin15AnchoredAtom1288 chi ∧
      Fin15AnchoredAtom1713 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1246 Fin15AnchoredAtom1247 Fin15AnchoredAtom1267
    Fin15AnchoredAtom1288 Fin15AnchoredAtom1713 Fin15AnchoredAtom3924 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12484
  ] at hbad
  tauto

theorem fin15Anchored_clause24726 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3925 chi ∧
      ¬Fin15AnchoredAtom1246 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1246 Fin15AnchoredAtom3925 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20676
  ] at hbad
  tauto

theorem fin15Anchored_clause24727 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3925 chi ∧
      ¬Fin15AnchoredAtom1248 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1248 Fin15AnchoredAtom3925 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20676
  ] at hbad
  tauto

theorem fin15Anchored_clause24728 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3925 chi ∧
      ¬Fin15AnchoredAtom1268 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1268 Fin15AnchoredAtom3925 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20676
  ] at hbad
  tauto

theorem fin15Anchored_clause24729 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3925 chi ∧
      ¬Fin15AnchoredAtom1289 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1289 Fin15AnchoredAtom3925 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20676
  ] at hbad
  tauto

theorem fin15Anchored_clause24730 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3925 chi ∧
      ¬Fin15AnchoredAtom1714 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1714 Fin15AnchoredAtom3925 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20676
  ] at hbad
  tauto

theorem fin15Anchored_clause24731 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3925 chi ∧
      Fin15AnchoredAtom1246 chi ∧
      Fin15AnchoredAtom1248 chi ∧
      Fin15AnchoredAtom1268 chi ∧
      Fin15AnchoredAtom1289 chi ∧
      Fin15AnchoredAtom1714 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1246 Fin15AnchoredAtom1248 Fin15AnchoredAtom1268
    Fin15AnchoredAtom1289 Fin15AnchoredAtom1714 Fin15AnchoredAtom3925 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20676
  ] at hbad
  tauto

theorem fin15Anchored_clause24732 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3926 chi ∧
      ¬Fin15AnchoredAtom1247 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1247 Fin15AnchoredAtom3926 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24772
  ] at hbad
  tauto

theorem fin15Anchored_clause24733 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3926 chi ∧
      ¬Fin15AnchoredAtom1248 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1248 Fin15AnchoredAtom3926 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24772
  ] at hbad
  tauto

theorem fin15Anchored_clause24734 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3926 chi ∧
      ¬Fin15AnchoredAtom1269 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1269 Fin15AnchoredAtom3926 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24772
  ] at hbad
  tauto

theorem fin15Anchored_clause24735 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3926 chi ∧
      ¬Fin15AnchoredAtom1290 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1290 Fin15AnchoredAtom3926 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24772
  ] at hbad
  tauto

theorem fin15Anchored_clause24736 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3926 chi ∧
      ¬Fin15AnchoredAtom1715 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1715 Fin15AnchoredAtom3926 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24772
  ] at hbad
  tauto

theorem fin15Anchored_clause24737 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3926 chi ∧
      Fin15AnchoredAtom1247 chi ∧
      Fin15AnchoredAtom1248 chi ∧
      Fin15AnchoredAtom1269 chi ∧
      Fin15AnchoredAtom1290 chi ∧
      Fin15AnchoredAtom1715 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1247 Fin15AnchoredAtom1248 Fin15AnchoredAtom1269
    Fin15AnchoredAtom1290 Fin15AnchoredAtom1715 Fin15AnchoredAtom3926 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24772
  ] at hbad
  tauto

theorem fin15Anchored_clause24738 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3927 chi ∧
      ¬Fin15AnchoredAtom1255 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1255 Fin15AnchoredAtom3927 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01860
  ] at hbad
  tauto

theorem fin15Anchored_clause24739 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3933 chi ∧
      ¬Fin15AnchoredAtom1297 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1297 Fin15AnchoredAtom3933 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05444
  ] at hbad
  tauto

theorem fin15Anchored_clause24740 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3934 chi ∧
      ¬Fin15AnchoredAtom1298 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1298 Fin15AnchoredAtom3934 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09540
  ] at hbad
  tauto

theorem fin15Anchored_clause24741 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3935 chi ∧
      ¬Fin15AnchoredAtom1263 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1263 Fin15AnchoredAtom3935 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17732
  ] at hbad
  tauto

theorem fin15Anchored_clause24742 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3939 chi ∧
      ¬Fin15AnchoredAtom1267 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1267 Fin15AnchoredAtom3939 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12612
  ] at hbad
  tauto

theorem fin15Anchored_clause24743 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3940 chi ∧
      ¬Fin15AnchoredAtom1268 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1268 Fin15AnchoredAtom3940 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20804
  ] at hbad
  tauto

theorem fin15Anchored_clause24744 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3941 chi ∧
      ¬Fin15AnchoredAtom1269 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1269 Fin15AnchoredAtom3941 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24900
  ] at hbad
  tauto

theorem fin15Anchored_clause24745 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3942 chi ∧
      ¬Fin15AnchoredAtom1255 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1255 Fin15AnchoredAtom3942 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03652
  ] at hbad
  tauto

theorem fin15Anchored_clause24746 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3942 chi ∧
      ¬Fin15AnchoredAtom1256 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1256 Fin15AnchoredAtom3942 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03652
  ] at hbad
  tauto

theorem fin15Anchored_clause24747 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3942 chi ∧
      ¬Fin15AnchoredAtom1260 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1260 Fin15AnchoredAtom3942 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03652
  ] at hbad
  tauto

theorem fin15Anchored_clause24748 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3942 chi ∧
      ¬Fin15AnchoredAtom1306 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1306 Fin15AnchoredAtom3942 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03652
  ] at hbad
  tauto

theorem fin15Anchored_clause24749 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3942 chi ∧
      ¬Fin15AnchoredAtom1731 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1731 Fin15AnchoredAtom3942 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03652
  ] at hbad
  tauto

theorem fin15Anchored_clause24750 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3942 chi ∧
      Fin15AnchoredAtom1255 chi ∧
      Fin15AnchoredAtom1256 chi ∧
      Fin15AnchoredAtom1260 chi ∧
      Fin15AnchoredAtom1306 chi ∧
      Fin15AnchoredAtom1731 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1255 Fin15AnchoredAtom1256 Fin15AnchoredAtom1260
    Fin15AnchoredAtom1306 Fin15AnchoredAtom1731 Fin15AnchoredAtom3942 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03652
  ] at hbad
  tauto

theorem fin15Anchored_clause24751 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3943 chi ∧
      ¬Fin15AnchoredAtom1255 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1255 Fin15AnchoredAtom3943 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05700
  ] at hbad
  tauto

theorem fin15Anchored_clause24752 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3943 chi ∧
      ¬Fin15AnchoredAtom1257 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1257 Fin15AnchoredAtom3943 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05700
  ] at hbad
  tauto

theorem fin15Anchored_clause24753 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3943 chi ∧
      ¬Fin15AnchoredAtom1261 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1261 Fin15AnchoredAtom3943 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05700
  ] at hbad
  tauto

theorem fin15Anchored_clause24754 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3943 chi ∧
      ¬Fin15AnchoredAtom1307 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1307 Fin15AnchoredAtom3943 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05700
  ] at hbad
  tauto

theorem fin15Anchored_clause24755 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3943 chi ∧
      ¬Fin15AnchoredAtom1732 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1732 Fin15AnchoredAtom3943 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05700
  ] at hbad
  tauto

theorem fin15Anchored_clause24756 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3943 chi ∧
      Fin15AnchoredAtom1255 chi ∧
      Fin15AnchoredAtom1257 chi ∧
      Fin15AnchoredAtom1261 chi ∧
      Fin15AnchoredAtom1307 chi ∧
      Fin15AnchoredAtom1732 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1255 Fin15AnchoredAtom1257 Fin15AnchoredAtom1261
    Fin15AnchoredAtom1307 Fin15AnchoredAtom1732 Fin15AnchoredAtom3943 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05700
  ] at hbad
  tauto

theorem fin15Anchored_clause24757 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3944 chi ∧
      ¬Fin15AnchoredAtom1255 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1255 Fin15AnchoredAtom3944 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09796
  ] at hbad
  tauto

theorem fin15Anchored_clause24758 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3944 chi ∧
      ¬Fin15AnchoredAtom1258 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1258 Fin15AnchoredAtom3944 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09796
  ] at hbad
  tauto

theorem fin15Anchored_clause24759 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3944 chi ∧
      ¬Fin15AnchoredAtom1262 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1262 Fin15AnchoredAtom3944 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09796
  ] at hbad
  tauto

theorem fin15Anchored_clause24760 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3944 chi ∧
      ¬Fin15AnchoredAtom1308 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1308 Fin15AnchoredAtom3944 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09796
  ] at hbad
  tauto

theorem fin15Anchored_clause24761 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3944 chi ∧
      ¬Fin15AnchoredAtom1733 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1733 Fin15AnchoredAtom3944 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09796
  ] at hbad
  tauto

theorem fin15Anchored_clause24762 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3944 chi ∧
      Fin15AnchoredAtom1255 chi ∧
      Fin15AnchoredAtom1258 chi ∧
      Fin15AnchoredAtom1262 chi ∧
      Fin15AnchoredAtom1308 chi ∧
      Fin15AnchoredAtom1733 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1255 Fin15AnchoredAtom1258 Fin15AnchoredAtom1262
    Fin15AnchoredAtom1308 Fin15AnchoredAtom1733 Fin15AnchoredAtom3944 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09796
  ] at hbad
  tauto

theorem fin15Anchored_clause24763 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3945 chi ∧
      ¬Fin15AnchoredAtom1255 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1255 Fin15AnchoredAtom3945 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17988
  ] at hbad
  tauto

theorem fin15Anchored_clause24764 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3945 chi ∧
      ¬Fin15AnchoredAtom1259 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1259 Fin15AnchoredAtom3945 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17988
  ] at hbad
  tauto

theorem fin15Anchored_clause24765 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3945 chi ∧
      ¬Fin15AnchoredAtom1263 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1263 Fin15AnchoredAtom3945 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17988
  ] at hbad
  tauto

theorem fin15Anchored_clause24766 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3945 chi ∧
      ¬Fin15AnchoredAtom1309 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1309 Fin15AnchoredAtom3945 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17988
  ] at hbad
  tauto

theorem fin15Anchored_clause24767 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3945 chi ∧
      ¬Fin15AnchoredAtom1734 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1734 Fin15AnchoredAtom3945 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17988
  ] at hbad
  tauto

theorem fin15Anchored_clause24768 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3945 chi ∧
      Fin15AnchoredAtom1255 chi ∧
      Fin15AnchoredAtom1259 chi ∧
      Fin15AnchoredAtom1263 chi ∧
      Fin15AnchoredAtom1309 chi ∧
      Fin15AnchoredAtom1734 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1255 Fin15AnchoredAtom1259 Fin15AnchoredAtom1263
    Fin15AnchoredAtom1309 Fin15AnchoredAtom1734 Fin15AnchoredAtom3945 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17988
  ] at hbad
  tauto

theorem fin15Anchored_clause24769 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3946 chi ∧
      ¬Fin15AnchoredAtom1256 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1256 Fin15AnchoredAtom3946 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06724
  ] at hbad
  tauto

theorem fin15Anchored_clause24770 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3946 chi ∧
      ¬Fin15AnchoredAtom1257 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1257 Fin15AnchoredAtom3946 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06724
  ] at hbad
  tauto

theorem fin15Anchored_clause24771 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3946 chi ∧
      ¬Fin15AnchoredAtom1735 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1735 Fin15AnchoredAtom3946 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06724
  ] at hbad
  tauto

theorem fin15Anchored_clause24772 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3946 chi ∧
      Fin15AnchoredAtom1256 chi ∧
      Fin15AnchoredAtom1257 chi ∧
      Fin15AnchoredAtom1264 chi ∧
      Fin15AnchoredAtom1310 chi ∧
      Fin15AnchoredAtom1735 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1256 Fin15AnchoredAtom1257 Fin15AnchoredAtom1264
    Fin15AnchoredAtom1310 Fin15AnchoredAtom1735 Fin15AnchoredAtom3946 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06724
  ] at hbad
  tauto

theorem fin15Anchored_clause24773 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3947 chi ∧
      ¬Fin15AnchoredAtom1256 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1256 Fin15AnchoredAtom3947 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10820
  ] at hbad
  tauto

theorem fin15Anchored_clause24774 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3947 chi ∧
      ¬Fin15AnchoredAtom1258 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1258 Fin15AnchoredAtom3947 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10820
  ] at hbad
  tauto

theorem fin15Anchored_clause24775 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3947 chi ∧
      ¬Fin15AnchoredAtom1311 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1311 Fin15AnchoredAtom3947 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10820
  ] at hbad
  tauto

theorem fin15Anchored_clause24776 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3947 chi ∧
      ¬Fin15AnchoredAtom1736 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1736 Fin15AnchoredAtom3947 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10820
  ] at hbad
  tauto

theorem fin15Anchored_clause24777 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3947 chi ∧
      Fin15AnchoredAtom1256 chi ∧
      Fin15AnchoredAtom1258 chi ∧
      Fin15AnchoredAtom1265 chi ∧
      Fin15AnchoredAtom1311 chi ∧
      Fin15AnchoredAtom1736 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1256 Fin15AnchoredAtom1258 Fin15AnchoredAtom1265
    Fin15AnchoredAtom1311 Fin15AnchoredAtom1736 Fin15AnchoredAtom3947 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10820
  ] at hbad
  tauto

theorem fin15Anchored_clause24778 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3948 chi ∧
      ¬Fin15AnchoredAtom1256 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1256 Fin15AnchoredAtom3948 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask19012
  ] at hbad
  tauto

theorem fin15Anchored_clause24779 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3948 chi ∧
      ¬Fin15AnchoredAtom1266 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1266 Fin15AnchoredAtom3948 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask19012
  ] at hbad
  tauto

theorem fin15Anchored_clause24780 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3948 chi ∧
      ¬Fin15AnchoredAtom1312 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1312 Fin15AnchoredAtom3948 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask19012
  ] at hbad
  tauto

theorem fin15Anchored_clause24781 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3948 chi ∧
      ¬Fin15AnchoredAtom1737 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1737 Fin15AnchoredAtom3948 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask19012
  ] at hbad
  tauto

theorem fin15Anchored_clause24782 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3948 chi ∧
      Fin15AnchoredAtom1256 chi ∧
      Fin15AnchoredAtom1259 chi ∧
      Fin15AnchoredAtom1266 chi ∧
      Fin15AnchoredAtom1312 chi ∧
      Fin15AnchoredAtom1737 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1256 Fin15AnchoredAtom1259 Fin15AnchoredAtom1266
    Fin15AnchoredAtom1312 Fin15AnchoredAtom1737 Fin15AnchoredAtom3948 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask19012
  ] at hbad
  tauto

theorem fin15Anchored_clause24783 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3949 chi ∧
      ¬Fin15AnchoredAtom1257 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1257 Fin15AnchoredAtom3949 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12868
  ] at hbad
  tauto

theorem fin15Anchored_clause24784 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3949 chi ∧
      ¬Fin15AnchoredAtom1258 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1258 Fin15AnchoredAtom3949 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12868
  ] at hbad
  tauto

theorem fin15Anchored_clause24785 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3949 chi ∧
      ¬Fin15AnchoredAtom1267 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1267 Fin15AnchoredAtom3949 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12868
  ] at hbad
  tauto

theorem fin15Anchored_clause24786 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3949 chi ∧
      ¬Fin15AnchoredAtom1313 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1313 Fin15AnchoredAtom3949 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12868
  ] at hbad
  tauto

theorem fin15Anchored_clause24787 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3949 chi ∧
      ¬Fin15AnchoredAtom1738 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1738 Fin15AnchoredAtom3949 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12868
  ] at hbad
  tauto

theorem fin15Anchored_clause24788 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3949 chi ∧
      Fin15AnchoredAtom1257 chi ∧
      Fin15AnchoredAtom1258 chi ∧
      Fin15AnchoredAtom1267 chi ∧
      Fin15AnchoredAtom1313 chi ∧
      Fin15AnchoredAtom1738 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1257 Fin15AnchoredAtom1258 Fin15AnchoredAtom1267
    Fin15AnchoredAtom1313 Fin15AnchoredAtom1738 Fin15AnchoredAtom3949 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12868
  ] at hbad
  tauto

theorem fin15Anchored_clause24789 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3950 chi ∧
      ¬Fin15AnchoredAtom1257 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1257 Fin15AnchoredAtom3950 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21060
  ] at hbad
  tauto

theorem fin15Anchored_clause24790 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3950 chi ∧
      ¬Fin15AnchoredAtom1259 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1259 Fin15AnchoredAtom3950 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21060
  ] at hbad
  tauto

theorem fin15Anchored_clause24791 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3950 chi ∧
      ¬Fin15AnchoredAtom1268 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1268 Fin15AnchoredAtom3950 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21060
  ] at hbad
  tauto

theorem fin15Anchored_clause24792 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3950 chi ∧
      ¬Fin15AnchoredAtom1314 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1314 Fin15AnchoredAtom3950 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21060
  ] at hbad
  tauto

theorem fin15Anchored_clause24793 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3950 chi ∧
      ¬Fin15AnchoredAtom1739 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1739 Fin15AnchoredAtom3950 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21060
  ] at hbad
  tauto

theorem fin15Anchored_clause24794 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3950 chi ∧
      Fin15AnchoredAtom1257 chi ∧
      Fin15AnchoredAtom1259 chi ∧
      Fin15AnchoredAtom1268 chi ∧
      Fin15AnchoredAtom1314 chi ∧
      Fin15AnchoredAtom1739 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1257 Fin15AnchoredAtom1259 Fin15AnchoredAtom1268
    Fin15AnchoredAtom1314 Fin15AnchoredAtom1739 Fin15AnchoredAtom3950 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21060
  ] at hbad
  tauto

theorem fin15Anchored_clause24795 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3951 chi ∧
      ¬Fin15AnchoredAtom1258 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1258 Fin15AnchoredAtom3951 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25156
  ] at hbad
  tauto

theorem fin15Anchored_clause24796 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3951 chi ∧
      ¬Fin15AnchoredAtom1259 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1259 Fin15AnchoredAtom3951 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25156
  ] at hbad
  tauto

theorem fin15Anchored_clause24797 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3951 chi ∧
      ¬Fin15AnchoredAtom1269 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1269 Fin15AnchoredAtom3951 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25156
  ] at hbad
  tauto

theorem fin15Anchored_clause24798 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3951 chi ∧
      ¬Fin15AnchoredAtom1315 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1315 Fin15AnchoredAtom3951 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25156
  ] at hbad
  tauto

theorem fin15Anchored_clause24799 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3951 chi ∧
      ¬Fin15AnchoredAtom1740 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1740 Fin15AnchoredAtom3951 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25156
  ] at hbad
  tauto

theorem fin15Anchored_clause24800 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3951 chi ∧
      Fin15AnchoredAtom1258 chi ∧
      Fin15AnchoredAtom1259 chi ∧
      Fin15AnchoredAtom1269 chi ∧
      Fin15AnchoredAtom1315 chi ∧
      Fin15AnchoredAtom1740 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1258 Fin15AnchoredAtom1259 Fin15AnchoredAtom1269
    Fin15AnchoredAtom1315 Fin15AnchoredAtom1740 Fin15AnchoredAtom3951 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25156
  ] at hbad
  tauto

theorem fin15Anchored_clause24801 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3952 chi ∧
      ¬Fin15AnchoredAtom1260 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1260 Fin15AnchoredAtom3952 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07236
  ] at hbad
  tauto

theorem fin15Anchored_clause24802 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3952 chi ∧
      ¬Fin15AnchoredAtom1261 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1261 Fin15AnchoredAtom3952 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07236
  ] at hbad
  tauto

theorem fin15Anchored_clause24803 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3952 chi ∧
      ¬Fin15AnchoredAtom1264 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1264 Fin15AnchoredAtom3952 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07236
  ] at hbad
  tauto

theorem fin15Anchored_clause24804 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3952 chi ∧
      ¬Fin15AnchoredAtom1316 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1316 Fin15AnchoredAtom3952 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07236
  ] at hbad
  tauto

theorem fin15Anchored_clause24805 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3952 chi ∧
      ¬Fin15AnchoredAtom1741 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1741 Fin15AnchoredAtom3952 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07236
  ] at hbad
  tauto

theorem fin15Anchored_clause24806 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3952 chi ∧
      Fin15AnchoredAtom1260 chi ∧
      Fin15AnchoredAtom1261 chi ∧
      Fin15AnchoredAtom1264 chi ∧
      Fin15AnchoredAtom1316 chi ∧
      Fin15AnchoredAtom1741 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1260 Fin15AnchoredAtom1261 Fin15AnchoredAtom1264
    Fin15AnchoredAtom1316 Fin15AnchoredAtom1741 Fin15AnchoredAtom3952 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07236
  ] at hbad
  tauto

theorem fin15Anchored_clause24807 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3953 chi ∧
      ¬Fin15AnchoredAtom1262 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1262 Fin15AnchoredAtom3953 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11332
  ] at hbad
  tauto

theorem fin15Anchored_clause24808 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3953 chi ∧
      ¬Fin15AnchoredAtom1265 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1265 Fin15AnchoredAtom3953 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11332
  ] at hbad
  tauto

theorem fin15Anchored_clause24809 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3953 chi ∧
      ¬Fin15AnchoredAtom1317 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1317 Fin15AnchoredAtom3953 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11332
  ] at hbad
  tauto

theorem fin15Anchored_clause24810 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3953 chi ∧
      Fin15AnchoredAtom1260 chi ∧
      Fin15AnchoredAtom1262 chi ∧
      Fin15AnchoredAtom1265 chi ∧
      Fin15AnchoredAtom1317 chi ∧
      Fin15AnchoredAtom1742 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1260 Fin15AnchoredAtom1262 Fin15AnchoredAtom1265
    Fin15AnchoredAtom1317 Fin15AnchoredAtom1742 Fin15AnchoredAtom3953 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11332
  ] at hbad
  tauto

theorem fin15Anchored_clause24811 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3954 chi ∧
      ¬Fin15AnchoredAtom1263 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1263 Fin15AnchoredAtom3954 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask19524
  ] at hbad
  tauto

theorem fin15Anchored_clause24812 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3955 chi ∧
      ¬Fin15AnchoredAtom1261 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1261 Fin15AnchoredAtom3955 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13380
  ] at hbad
  tauto

theorem fin15Anchored_clause24813 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3955 chi ∧
      ¬Fin15AnchoredAtom1262 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1262 Fin15AnchoredAtom3955 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13380
  ] at hbad
  tauto

theorem fin15Anchored_clause24814 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3955 chi ∧
      ¬Fin15AnchoredAtom1267 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1267 Fin15AnchoredAtom3955 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13380
  ] at hbad
  tauto

theorem fin15Anchored_clause24815 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3955 chi ∧
      ¬Fin15AnchoredAtom1319 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1319 Fin15AnchoredAtom3955 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13380
  ] at hbad
  tauto

theorem fin15Anchored_clause24816 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3955 chi ∧
      ¬Fin15AnchoredAtom1744 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1744 Fin15AnchoredAtom3955 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13380
  ] at hbad
  tauto

theorem fin15Anchored_clause24817 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3955 chi ∧
      Fin15AnchoredAtom1261 chi ∧
      Fin15AnchoredAtom1262 chi ∧
      Fin15AnchoredAtom1267 chi ∧
      Fin15AnchoredAtom1319 chi ∧
      Fin15AnchoredAtom1744 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1261 Fin15AnchoredAtom1262 Fin15AnchoredAtom1267
    Fin15AnchoredAtom1319 Fin15AnchoredAtom1744 Fin15AnchoredAtom3955 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13380
  ] at hbad
  tauto

theorem fin15Anchored_clause24818 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3956 chi ∧
      ¬Fin15AnchoredAtom1261 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1261 Fin15AnchoredAtom3956 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21572
  ] at hbad
  tauto

theorem fin15Anchored_clause24819 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3956 chi ∧
      ¬Fin15AnchoredAtom1263 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1263 Fin15AnchoredAtom3956 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21572
  ] at hbad
  tauto

theorem fin15Anchored_clause24820 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3956 chi ∧
      ¬Fin15AnchoredAtom1268 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1268 Fin15AnchoredAtom3956 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21572
  ] at hbad
  tauto

theorem fin15Anchored_clause24821 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3956 chi ∧
      ¬Fin15AnchoredAtom1320 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1320 Fin15AnchoredAtom3956 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21572
  ] at hbad
  tauto

theorem fin15Anchored_clause24822 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3956 chi ∧
      ¬Fin15AnchoredAtom1745 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1745 Fin15AnchoredAtom3956 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21572
  ] at hbad
  tauto

theorem fin15Anchored_clause24823 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3956 chi ∧
      Fin15AnchoredAtom1261 chi ∧
      Fin15AnchoredAtom1263 chi ∧
      Fin15AnchoredAtom1268 chi ∧
      Fin15AnchoredAtom1320 chi ∧
      Fin15AnchoredAtom1745 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1261 Fin15AnchoredAtom1263 Fin15AnchoredAtom1268
    Fin15AnchoredAtom1320 Fin15AnchoredAtom1745 Fin15AnchoredAtom3956 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21572
  ] at hbad
  tauto

theorem fin15Anchored_clause24824 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3957 chi ∧
      ¬Fin15AnchoredAtom1262 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1262 Fin15AnchoredAtom3957 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25668
  ] at hbad
  tauto

theorem fin15Anchored_clause24825 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3957 chi ∧
      ¬Fin15AnchoredAtom1263 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1263 Fin15AnchoredAtom3957 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25668
  ] at hbad
  tauto

theorem fin15Anchored_clause24826 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3957 chi ∧
      ¬Fin15AnchoredAtom1269 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1269 Fin15AnchoredAtom3957 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25668
  ] at hbad
  tauto

theorem fin15Anchored_clause24827 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3957 chi ∧
      ¬Fin15AnchoredAtom1321 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1321 Fin15AnchoredAtom3957 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25668
  ] at hbad
  tauto

theorem fin15Anchored_clause24828 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3957 chi ∧
      ¬Fin15AnchoredAtom1746 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1746 Fin15AnchoredAtom3957 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25668
  ] at hbad
  tauto

theorem fin15Anchored_clause24829 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3957 chi ∧
      Fin15AnchoredAtom1262 chi ∧
      Fin15AnchoredAtom1263 chi ∧
      Fin15AnchoredAtom1269 chi ∧
      Fin15AnchoredAtom1321 chi ∧
      Fin15AnchoredAtom1746 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1262 Fin15AnchoredAtom1263 Fin15AnchoredAtom1269
    Fin15AnchoredAtom1321 Fin15AnchoredAtom1746 Fin15AnchoredAtom3957 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25668
  ] at hbad
  tauto

theorem fin15Anchored_clause24830 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3958 chi ∧
      ¬Fin15AnchoredAtom1267 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1267 Fin15AnchoredAtom3958 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14404
  ] at hbad
  tauto

theorem fin15Anchored_clause24831 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3958 chi ∧
      ¬Fin15AnchoredAtom1322 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1322 Fin15AnchoredAtom3958 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14404
  ] at hbad
  tauto

end ErdosSzekeres

end
