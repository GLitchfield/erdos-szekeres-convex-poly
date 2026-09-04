module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 189. -/

theorem fin15Anchored_clause24192 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3765 chi ∧
      ¬Fin15AnchoredAtom1176 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1176 Fin15AnchoredAtom3765 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24660
  ] at hbad
  tauto

theorem fin15Anchored_clause24193 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3765 chi ∧
      ¬Fin15AnchoredAtom1177 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1177 Fin15AnchoredAtom3765 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24660
  ] at hbad
  tauto

theorem fin15Anchored_clause24194 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3765 chi ∧
      ¬Fin15AnchoredAtom1205 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1205 Fin15AnchoredAtom3765 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24660
  ] at hbad
  tauto

theorem fin15Anchored_clause24195 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3765 chi ∧
      ¬Fin15AnchoredAtom1269 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1269 Fin15AnchoredAtom3765 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24660
  ] at hbad
  tauto

theorem fin15Anchored_clause24196 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3765 chi ∧
      ¬Fin15AnchoredAtom1554 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1554 Fin15AnchoredAtom3765 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24660
  ] at hbad
  tauto

theorem fin15Anchored_clause24197 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3765 chi ∧
      Fin15AnchoredAtom1176 chi ∧
      Fin15AnchoredAtom1177 chi ∧
      Fin15AnchoredAtom1205 chi ∧
      Fin15AnchoredAtom1269 chi ∧
      Fin15AnchoredAtom1554 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1176 Fin15AnchoredAtom1177 Fin15AnchoredAtom1205
    Fin15AnchoredAtom1269 Fin15AnchoredAtom1554 Fin15AnchoredAtom3765 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24660
  ] at hbad
  tauto

theorem fin15Anchored_clause24198 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3766 chi ∧
      ¬Fin15AnchoredAtom1178 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1178 Fin15AnchoredAtom3766 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00916
  ] at hbad
  tauto

theorem fin15Anchored_clause24199 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3766 chi ∧
      ¬Fin15AnchoredAtom1179 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1179 Fin15AnchoredAtom3766 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00916
  ] at hbad
  tauto

theorem fin15Anchored_clause24200 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3766 chi ∧
      ¬Fin15AnchoredAtom1270 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1270 Fin15AnchoredAtom3766 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00916
  ] at hbad
  tauto

theorem fin15Anchored_clause24201 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3766 chi ∧
      ¬Fin15AnchoredAtom1555 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1555 Fin15AnchoredAtom3766 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00916
  ] at hbad
  tauto

theorem fin15Anchored_clause24202 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3766 chi ∧
      Fin15AnchoredAtom1178 chi ∧
      Fin15AnchoredAtom1179 chi ∧
      Fin15AnchoredAtom1185 chi ∧
      Fin15AnchoredAtom1270 chi ∧
      Fin15AnchoredAtom1555 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1178 Fin15AnchoredAtom1179 Fin15AnchoredAtom1185
    Fin15AnchoredAtom1270 Fin15AnchoredAtom1555 Fin15AnchoredAtom3766 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00916
  ] at hbad
  tauto

theorem fin15Anchored_clause24203 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3767 chi ∧
      ¬Fin15AnchoredAtom1180 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1180 Fin15AnchoredAtom3767 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01428
  ] at hbad
  tauto

theorem fin15Anchored_clause24204 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3767 chi ∧
      Fin15AnchoredAtom1178 chi ∧
      Fin15AnchoredAtom1180 chi ∧
      Fin15AnchoredAtom1186 chi ∧
      Fin15AnchoredAtom1271 chi ∧
      Fin15AnchoredAtom1556 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1178 Fin15AnchoredAtom1180 Fin15AnchoredAtom1186
    Fin15AnchoredAtom1271 Fin15AnchoredAtom1556 Fin15AnchoredAtom3767 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01428
  ] at hbad
  tauto

theorem fin15Anchored_clause24205 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3769 chi ∧
      ¬Fin15AnchoredAtom1182 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1182 Fin15AnchoredAtom3769 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04500
  ] at hbad
  tauto

theorem fin15Anchored_clause24206 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3771 chi ∧
      ¬Fin15AnchoredAtom1184 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1184 Fin15AnchoredAtom3771 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16788
  ] at hbad
  tauto

theorem fin15Anchored_clause24207 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3771 chi ∧
      ¬Fin15AnchoredAtom1190 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1190 Fin15AnchoredAtom3771 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16788
  ] at hbad
  tauto

theorem fin15Anchored_clause24208 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3771 chi ∧
      ¬Fin15AnchoredAtom1560 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1560 Fin15AnchoredAtom3771 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16788
  ] at hbad
  tauto

theorem fin15Anchored_clause24209 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3772 chi ∧
      ¬Fin15AnchoredAtom1179 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1179 Fin15AnchoredAtom3772 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01684
  ] at hbad
  tauto

theorem fin15Anchored_clause24210 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3772 chi ∧
      ¬Fin15AnchoredAtom1180 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1180 Fin15AnchoredAtom3772 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01684
  ] at hbad
  tauto

theorem fin15Anchored_clause24211 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3772 chi ∧
      ¬Fin15AnchoredAtom1191 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1191 Fin15AnchoredAtom3772 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01684
  ] at hbad
  tauto

theorem fin15Anchored_clause24212 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3772 chi ∧
      ¬Fin15AnchoredAtom1276 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1276 Fin15AnchoredAtom3772 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01684
  ] at hbad
  tauto

theorem fin15Anchored_clause24213 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3772 chi ∧
      ¬Fin15AnchoredAtom1561 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1561 Fin15AnchoredAtom3772 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01684
  ] at hbad
  tauto

theorem fin15Anchored_clause24214 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3772 chi ∧
      Fin15AnchoredAtom1179 chi ∧
      Fin15AnchoredAtom1180 chi ∧
      Fin15AnchoredAtom1191 chi ∧
      Fin15AnchoredAtom1276 chi ∧
      Fin15AnchoredAtom1561 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1179 Fin15AnchoredAtom1180 Fin15AnchoredAtom1191
    Fin15AnchoredAtom1276 Fin15AnchoredAtom1561 Fin15AnchoredAtom3772 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01684
  ] at hbad
  tauto

theorem fin15Anchored_clause24215 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3773 chi ∧
      ¬Fin15AnchoredAtom1179 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1179 Fin15AnchoredAtom3773 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02708
  ] at hbad
  tauto

theorem fin15Anchored_clause24216 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3773 chi ∧
      ¬Fin15AnchoredAtom1562 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1562 Fin15AnchoredAtom3773 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02708
  ] at hbad
  tauto

theorem fin15Anchored_clause24217 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3773 chi ∧
      Fin15AnchoredAtom1179 chi ∧
      Fin15AnchoredAtom1181 chi ∧
      Fin15AnchoredAtom1192 chi ∧
      Fin15AnchoredAtom1277 chi ∧
      Fin15AnchoredAtom1562 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1179 Fin15AnchoredAtom1181 Fin15AnchoredAtom1192
    Fin15AnchoredAtom1277 Fin15AnchoredAtom1562 Fin15AnchoredAtom3773 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02708
  ] at hbad
  tauto

theorem fin15Anchored_clause24218 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3774 chi ∧
      ¬Fin15AnchoredAtom1179 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1179 Fin15AnchoredAtom3774 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04756
  ] at hbad
  tauto

theorem fin15Anchored_clause24219 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3774 chi ∧
      ¬Fin15AnchoredAtom1182 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1182 Fin15AnchoredAtom3774 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04756
  ] at hbad
  tauto

theorem fin15Anchored_clause24220 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3774 chi ∧
      ¬Fin15AnchoredAtom1193 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1193 Fin15AnchoredAtom3774 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04756
  ] at hbad
  tauto

theorem fin15Anchored_clause24221 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3774 chi ∧
      ¬Fin15AnchoredAtom1278 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1278 Fin15AnchoredAtom3774 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04756
  ] at hbad
  tauto

theorem fin15Anchored_clause24222 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3774 chi ∧
      ¬Fin15AnchoredAtom1563 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1563 Fin15AnchoredAtom3774 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04756
  ] at hbad
  tauto

theorem fin15Anchored_clause24223 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3774 chi ∧
      Fin15AnchoredAtom1179 chi ∧
      Fin15AnchoredAtom1182 chi ∧
      Fin15AnchoredAtom1193 chi ∧
      Fin15AnchoredAtom1278 chi ∧
      Fin15AnchoredAtom1563 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1179 Fin15AnchoredAtom1182 Fin15AnchoredAtom1193
    Fin15AnchoredAtom1278 Fin15AnchoredAtom1563 Fin15AnchoredAtom3774 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04756
  ] at hbad
  tauto

theorem fin15Anchored_clause24224 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3775 chi ∧
      ¬Fin15AnchoredAtom1179 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1179 Fin15AnchoredAtom3775 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08852
  ] at hbad
  tauto

theorem fin15Anchored_clause24225 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3775 chi ∧
      ¬Fin15AnchoredAtom1183 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1183 Fin15AnchoredAtom3775 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08852
  ] at hbad
  tauto

theorem fin15Anchored_clause24226 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3775 chi ∧
      ¬Fin15AnchoredAtom1194 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1194 Fin15AnchoredAtom3775 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08852
  ] at hbad
  tauto

theorem fin15Anchored_clause24227 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3775 chi ∧
      ¬Fin15AnchoredAtom1279 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1279 Fin15AnchoredAtom3775 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08852
  ] at hbad
  tauto

theorem fin15Anchored_clause24228 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3775 chi ∧
      ¬Fin15AnchoredAtom1564 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1564 Fin15AnchoredAtom3775 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08852
  ] at hbad
  tauto

theorem fin15Anchored_clause24229 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3775 chi ∧
      Fin15AnchoredAtom1179 chi ∧
      Fin15AnchoredAtom1183 chi ∧
      Fin15AnchoredAtom1194 chi ∧
      Fin15AnchoredAtom1279 chi ∧
      Fin15AnchoredAtom1564 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1179 Fin15AnchoredAtom1183 Fin15AnchoredAtom1194
    Fin15AnchoredAtom1279 Fin15AnchoredAtom1564 Fin15AnchoredAtom3775 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08852
  ] at hbad
  tauto

theorem fin15Anchored_clause24230 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3776 chi ∧
      ¬Fin15AnchoredAtom1179 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1179 Fin15AnchoredAtom3776 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17044
  ] at hbad
  tauto

theorem fin15Anchored_clause24231 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3776 chi ∧
      ¬Fin15AnchoredAtom1184 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1184 Fin15AnchoredAtom3776 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17044
  ] at hbad
  tauto

theorem fin15Anchored_clause24232 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3776 chi ∧
      ¬Fin15AnchoredAtom1195 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1195 Fin15AnchoredAtom3776 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17044
  ] at hbad
  tauto

theorem fin15Anchored_clause24233 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3776 chi ∧
      ¬Fin15AnchoredAtom1280 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1280 Fin15AnchoredAtom3776 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17044
  ] at hbad
  tauto

theorem fin15Anchored_clause24234 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3776 chi ∧
      ¬Fin15AnchoredAtom1565 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1565 Fin15AnchoredAtom3776 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17044
  ] at hbad
  tauto

theorem fin15Anchored_clause24235 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3776 chi ∧
      Fin15AnchoredAtom1179 chi ∧
      Fin15AnchoredAtom1184 chi ∧
      Fin15AnchoredAtom1195 chi ∧
      Fin15AnchoredAtom1280 chi ∧
      Fin15AnchoredAtom1565 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1179 Fin15AnchoredAtom1184 Fin15AnchoredAtom1195
    Fin15AnchoredAtom1280 Fin15AnchoredAtom1565 Fin15AnchoredAtom3776 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17044
  ] at hbad
  tauto

theorem fin15Anchored_clause24236 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3777 chi ∧
      ¬Fin15AnchoredAtom1180 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1180 Fin15AnchoredAtom3777 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03220
  ] at hbad
  tauto

theorem fin15Anchored_clause24237 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3777 chi ∧
      ¬Fin15AnchoredAtom1181 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1181 Fin15AnchoredAtom3777 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03220
  ] at hbad
  tauto

theorem fin15Anchored_clause24238 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3777 chi ∧
      ¬Fin15AnchoredAtom1281 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1281 Fin15AnchoredAtom3777 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03220
  ] at hbad
  tauto

theorem fin15Anchored_clause24239 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3777 chi ∧
      ¬Fin15AnchoredAtom1566 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1566 Fin15AnchoredAtom3777 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03220
  ] at hbad
  tauto

theorem fin15Anchored_clause24240 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3778 chi ∧
      ¬Fin15AnchoredAtom1180 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1180 Fin15AnchoredAtom3778 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05268
  ] at hbad
  tauto

theorem fin15Anchored_clause24241 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3778 chi ∧
      ¬Fin15AnchoredAtom1182 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1182 Fin15AnchoredAtom3778 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05268
  ] at hbad
  tauto

theorem fin15Anchored_clause24242 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3778 chi ∧
      ¬Fin15AnchoredAtom1197 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1197 Fin15AnchoredAtom3778 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05268
  ] at hbad
  tauto

theorem fin15Anchored_clause24243 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3778 chi ∧
      ¬Fin15AnchoredAtom1282 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1282 Fin15AnchoredAtom3778 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05268
  ] at hbad
  tauto

theorem fin15Anchored_clause24244 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3778 chi ∧
      ¬Fin15AnchoredAtom1567 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1567 Fin15AnchoredAtom3778 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05268
  ] at hbad
  tauto

theorem fin15Anchored_clause24245 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3778 chi ∧
      Fin15AnchoredAtom1180 chi ∧
      Fin15AnchoredAtom1182 chi ∧
      Fin15AnchoredAtom1197 chi ∧
      Fin15AnchoredAtom1282 chi ∧
      Fin15AnchoredAtom1567 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1180 Fin15AnchoredAtom1182 Fin15AnchoredAtom1197
    Fin15AnchoredAtom1282 Fin15AnchoredAtom1567 Fin15AnchoredAtom3778 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05268
  ] at hbad
  tauto

theorem fin15Anchored_clause24246 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3779 chi ∧
      ¬Fin15AnchoredAtom1180 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1180 Fin15AnchoredAtom3779 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09364
  ] at hbad
  tauto

theorem fin15Anchored_clause24247 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3779 chi ∧
      ¬Fin15AnchoredAtom1183 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1183 Fin15AnchoredAtom3779 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09364
  ] at hbad
  tauto

theorem fin15Anchored_clause24248 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3779 chi ∧
      ¬Fin15AnchoredAtom1198 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1198 Fin15AnchoredAtom3779 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09364
  ] at hbad
  tauto

theorem fin15Anchored_clause24249 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3779 chi ∧
      ¬Fin15AnchoredAtom1283 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1283 Fin15AnchoredAtom3779 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09364
  ] at hbad
  tauto

theorem fin15Anchored_clause24250 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3779 chi ∧
      ¬Fin15AnchoredAtom1568 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1568 Fin15AnchoredAtom3779 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09364
  ] at hbad
  tauto

theorem fin15Anchored_clause24251 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3779 chi ∧
      Fin15AnchoredAtom1180 chi ∧
      Fin15AnchoredAtom1183 chi ∧
      Fin15AnchoredAtom1198 chi ∧
      Fin15AnchoredAtom1283 chi ∧
      Fin15AnchoredAtom1568 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1180 Fin15AnchoredAtom1183 Fin15AnchoredAtom1198
    Fin15AnchoredAtom1283 Fin15AnchoredAtom1568 Fin15AnchoredAtom3779 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09364
  ] at hbad
  tauto

theorem fin15Anchored_clause24252 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3780 chi ∧
      ¬Fin15AnchoredAtom1180 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1180 Fin15AnchoredAtom3780 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17556
  ] at hbad
  tauto

theorem fin15Anchored_clause24253 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3780 chi ∧
      ¬Fin15AnchoredAtom1184 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1184 Fin15AnchoredAtom3780 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17556
  ] at hbad
  tauto

theorem fin15Anchored_clause24254 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3780 chi ∧
      ¬Fin15AnchoredAtom1199 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1199 Fin15AnchoredAtom3780 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17556
  ] at hbad
  tauto

theorem fin15Anchored_clause24255 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3780 chi ∧
      ¬Fin15AnchoredAtom1284 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1284 Fin15AnchoredAtom3780 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17556
  ] at hbad
  tauto

theorem fin15Anchored_clause24256 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3780 chi ∧
      ¬Fin15AnchoredAtom1569 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1569 Fin15AnchoredAtom3780 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17556
  ] at hbad
  tauto

theorem fin15Anchored_clause24257 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3780 chi ∧
      Fin15AnchoredAtom1180 chi ∧
      Fin15AnchoredAtom1184 chi ∧
      Fin15AnchoredAtom1199 chi ∧
      Fin15AnchoredAtom1284 chi ∧
      Fin15AnchoredAtom1569 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1180 Fin15AnchoredAtom1184 Fin15AnchoredAtom1199
    Fin15AnchoredAtom1284 Fin15AnchoredAtom1569 Fin15AnchoredAtom3780 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17556
  ] at hbad
  tauto

theorem fin15Anchored_clause24258 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3781 chi ∧
      ¬Fin15AnchoredAtom1182 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1182 Fin15AnchoredAtom3781 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06292
  ] at hbad
  tauto

theorem fin15Anchored_clause24259 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3781 chi ∧
      ¬Fin15AnchoredAtom1200 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1200 Fin15AnchoredAtom3781 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06292
  ] at hbad
  tauto

theorem fin15Anchored_clause24260 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3781 chi ∧
      ¬Fin15AnchoredAtom1570 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1570 Fin15AnchoredAtom3781 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06292
  ] at hbad
  tauto

theorem fin15Anchored_clause24261 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3781 chi ∧
      Fin15AnchoredAtom1181 chi ∧
      Fin15AnchoredAtom1182 chi ∧
      Fin15AnchoredAtom1200 chi ∧
      Fin15AnchoredAtom1285 chi ∧
      Fin15AnchoredAtom1570 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1181 Fin15AnchoredAtom1182 Fin15AnchoredAtom1200
    Fin15AnchoredAtom1285 Fin15AnchoredAtom1570 Fin15AnchoredAtom3781 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06292
  ] at hbad
  tauto

theorem fin15Anchored_clause24262 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3782 chi ∧
      ¬Fin15AnchoredAtom1183 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1183 Fin15AnchoredAtom3782 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10388
  ] at hbad
  tauto

theorem fin15Anchored_clause24263 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3783 chi ∧
      ¬Fin15AnchoredAtom1184 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1184 Fin15AnchoredAtom3783 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18580
  ] at hbad
  tauto

theorem fin15Anchored_clause24264 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3784 chi ∧
      ¬Fin15AnchoredAtom1182 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1182 Fin15AnchoredAtom3784 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12436
  ] at hbad
  tauto

theorem fin15Anchored_clause24265 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3784 chi ∧
      ¬Fin15AnchoredAtom1183 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1183 Fin15AnchoredAtom3784 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12436
  ] at hbad
  tauto

theorem fin15Anchored_clause24266 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3784 chi ∧
      ¬Fin15AnchoredAtom1203 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1203 Fin15AnchoredAtom3784 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12436
  ] at hbad
  tauto

theorem fin15Anchored_clause24267 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3784 chi ∧
      ¬Fin15AnchoredAtom1288 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1288 Fin15AnchoredAtom3784 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12436
  ] at hbad
  tauto

theorem fin15Anchored_clause24268 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3784 chi ∧
      ¬Fin15AnchoredAtom1573 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1573 Fin15AnchoredAtom3784 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12436
  ] at hbad
  tauto

theorem fin15Anchored_clause24269 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3784 chi ∧
      Fin15AnchoredAtom1182 chi ∧
      Fin15AnchoredAtom1183 chi ∧
      Fin15AnchoredAtom1203 chi ∧
      Fin15AnchoredAtom1288 chi ∧
      Fin15AnchoredAtom1573 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1182 Fin15AnchoredAtom1183 Fin15AnchoredAtom1203
    Fin15AnchoredAtom1288 Fin15AnchoredAtom1573 Fin15AnchoredAtom3784 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12436
  ] at hbad
  tauto

theorem fin15Anchored_clause24270 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3785 chi ∧
      ¬Fin15AnchoredAtom1182 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1182 Fin15AnchoredAtom3785 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20628
  ] at hbad
  tauto

theorem fin15Anchored_clause24271 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3785 chi ∧
      ¬Fin15AnchoredAtom1184 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1184 Fin15AnchoredAtom3785 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20628
  ] at hbad
  tauto

theorem fin15Anchored_clause24272 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3785 chi ∧
      ¬Fin15AnchoredAtom1204 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1204 Fin15AnchoredAtom3785 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20628
  ] at hbad
  tauto

theorem fin15Anchored_clause24273 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3785 chi ∧
      ¬Fin15AnchoredAtom1289 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1289 Fin15AnchoredAtom3785 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20628
  ] at hbad
  tauto

theorem fin15Anchored_clause24274 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3785 chi ∧
      ¬Fin15AnchoredAtom1574 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1574 Fin15AnchoredAtom3785 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20628
  ] at hbad
  tauto

theorem fin15Anchored_clause24275 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3785 chi ∧
      Fin15AnchoredAtom1182 chi ∧
      Fin15AnchoredAtom1184 chi ∧
      Fin15AnchoredAtom1204 chi ∧
      Fin15AnchoredAtom1289 chi ∧
      Fin15AnchoredAtom1574 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1182 Fin15AnchoredAtom1184 Fin15AnchoredAtom1204
    Fin15AnchoredAtom1289 Fin15AnchoredAtom1574 Fin15AnchoredAtom3785 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20628
  ] at hbad
  tauto

theorem fin15Anchored_clause24276 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3786 chi ∧
      ¬Fin15AnchoredAtom1183 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1183 Fin15AnchoredAtom3786 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24724
  ] at hbad
  tauto

theorem fin15Anchored_clause24277 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3786 chi ∧
      ¬Fin15AnchoredAtom1184 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1184 Fin15AnchoredAtom3786 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24724
  ] at hbad
  tauto

theorem fin15Anchored_clause24278 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3786 chi ∧
      ¬Fin15AnchoredAtom1205 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1205 Fin15AnchoredAtom3786 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24724
  ] at hbad
  tauto

theorem fin15Anchored_clause24279 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3786 chi ∧
      ¬Fin15AnchoredAtom1290 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1290 Fin15AnchoredAtom3786 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24724
  ] at hbad
  tauto

theorem fin15Anchored_clause24280 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3786 chi ∧
      ¬Fin15AnchoredAtom1575 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1575 Fin15AnchoredAtom3786 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24724
  ] at hbad
  tauto

theorem fin15Anchored_clause24281 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3786 chi ∧
      Fin15AnchoredAtom1183 chi ∧
      Fin15AnchoredAtom1184 chi ∧
      Fin15AnchoredAtom1205 chi ∧
      Fin15AnchoredAtom1290 chi ∧
      Fin15AnchoredAtom1575 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1183 Fin15AnchoredAtom1184 Fin15AnchoredAtom1205
    Fin15AnchoredAtom1290 Fin15AnchoredAtom1575 Fin15AnchoredAtom3786 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24724
  ] at hbad
  tauto

theorem fin15Anchored_clause24282 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3787 chi ∧
      ¬Fin15AnchoredAtom1576 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1576 Fin15AnchoredAtom3787 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01812
  ] at hbad
  tauto

theorem fin15Anchored_clause24283 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3787 chi ∧
      Fin15AnchoredAtom1185 chi ∧
      Fin15AnchoredAtom1186 chi ∧
      Fin15AnchoredAtom1191 chi ∧
      Fin15AnchoredAtom1291 chi ∧
      Fin15AnchoredAtom1576 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1185 Fin15AnchoredAtom1186 Fin15AnchoredAtom1191
    Fin15AnchoredAtom1291 Fin15AnchoredAtom1576 Fin15AnchoredAtom3787 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01812
  ] at hbad
  tauto

theorem fin15Anchored_clause24284 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3789 chi ∧
      ¬Fin15AnchoredAtom1188 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1188 Fin15AnchoredAtom3789 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04884
  ] at hbad
  tauto

theorem fin15Anchored_clause24285 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3789 chi ∧
      ¬Fin15AnchoredAtom1578 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1578 Fin15AnchoredAtom3789 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04884
  ] at hbad
  tauto

theorem fin15Anchored_clause24286 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3789 chi ∧
      Fin15AnchoredAtom1185 chi ∧
      Fin15AnchoredAtom1188 chi ∧
      Fin15AnchoredAtom1193 chi ∧
      Fin15AnchoredAtom1293 chi ∧
      Fin15AnchoredAtom1578 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1185 Fin15AnchoredAtom1188 Fin15AnchoredAtom1193
    Fin15AnchoredAtom1293 Fin15AnchoredAtom1578 Fin15AnchoredAtom3789 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04884
  ] at hbad
  tauto

theorem fin15Anchored_clause24287 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3791 chi ∧
      ¬Fin15AnchoredAtom1195 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1195 Fin15AnchoredAtom3791 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17172
  ] at hbad
  tauto

theorem fin15Anchored_clause24288 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3793 chi ∧
      ¬Fin15AnchoredAtom1197 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1197 Fin15AnchoredAtom3793 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05396
  ] at hbad
  tauto

theorem fin15Anchored_clause24289 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3793 chi ∧
      ¬Fin15AnchoredAtom1582 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1582 Fin15AnchoredAtom3793 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05396
  ] at hbad
  tauto

theorem fin15Anchored_clause24290 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3793 chi ∧
      Fin15AnchoredAtom1186 chi ∧
      Fin15AnchoredAtom1188 chi ∧
      Fin15AnchoredAtom1197 chi ∧
      Fin15AnchoredAtom1297 chi ∧
      Fin15AnchoredAtom1582 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1186 Fin15AnchoredAtom1188 Fin15AnchoredAtom1197
    Fin15AnchoredAtom1297 Fin15AnchoredAtom1582 Fin15AnchoredAtom3793 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05396
  ] at hbad
  tauto

theorem fin15Anchored_clause24291 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3794 chi ∧
      ¬Fin15AnchoredAtom1198 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1198 Fin15AnchoredAtom3794 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09492
  ] at hbad
  tauto

theorem fin15Anchored_clause24292 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3794 chi ∧
      Fin15AnchoredAtom1186 chi ∧
      Fin15AnchoredAtom1189 chi ∧
      Fin15AnchoredAtom1198 chi ∧
      Fin15AnchoredAtom1298 chi ∧
      Fin15AnchoredAtom1583 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1186 Fin15AnchoredAtom1189 Fin15AnchoredAtom1198
    Fin15AnchoredAtom1298 Fin15AnchoredAtom1583 Fin15AnchoredAtom3794 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09492
  ] at hbad
  tauto

theorem fin15Anchored_clause24293 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3795 chi ∧
      ¬Fin15AnchoredAtom1199 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1199 Fin15AnchoredAtom3795 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17684
  ] at hbad
  tauto

theorem fin15Anchored_clause24294 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3799 chi ∧
      ¬Fin15AnchoredAtom1188 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1188 Fin15AnchoredAtom3799 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12564
  ] at hbad
  tauto

theorem fin15Anchored_clause24295 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3799 chi ∧
      Fin15AnchoredAtom1188 chi ∧
      Fin15AnchoredAtom1189 chi ∧
      Fin15AnchoredAtom1203 chi ∧
      Fin15AnchoredAtom1303 chi ∧
      Fin15AnchoredAtom1588 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1188 Fin15AnchoredAtom1189 Fin15AnchoredAtom1203
    Fin15AnchoredAtom1303 Fin15AnchoredAtom1588 Fin15AnchoredAtom3799 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12564
  ] at hbad
  tauto

theorem fin15Anchored_clause24296 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3800 chi ∧
      ¬Fin15AnchoredAtom1190 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1190 Fin15AnchoredAtom3800 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20756
  ] at hbad
  tauto

theorem fin15Anchored_clause24297 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3800 chi ∧
      ¬Fin15AnchoredAtom1204 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1204 Fin15AnchoredAtom3800 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20756
  ] at hbad
  tauto

theorem fin15Anchored_clause24298 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3800 chi ∧
      ¬Fin15AnchoredAtom1304 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1304 Fin15AnchoredAtom3800 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20756
  ] at hbad
  tauto

theorem fin15Anchored_clause24299 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3801 chi ∧
      ¬Fin15AnchoredAtom1590 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1590 Fin15AnchoredAtom3801 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24852
  ] at hbad
  tauto

theorem fin15Anchored_clause24300 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3802 chi ∧
      ¬Fin15AnchoredAtom1191 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1191 Fin15AnchoredAtom3802 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03604
  ] at hbad
  tauto

theorem fin15Anchored_clause24301 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3802 chi ∧
      ¬Fin15AnchoredAtom1306 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1306 Fin15AnchoredAtom3802 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03604
  ] at hbad
  tauto

theorem fin15Anchored_clause24302 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3802 chi ∧
      ¬Fin15AnchoredAtom1591 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1591 Fin15AnchoredAtom3802 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03604
  ] at hbad
  tauto

theorem fin15Anchored_clause24303 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3803 chi ∧
      ¬Fin15AnchoredAtom1191 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1191 Fin15AnchoredAtom3803 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05652
  ] at hbad
  tauto

theorem fin15Anchored_clause24304 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3803 chi ∧
      ¬Fin15AnchoredAtom1193 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1193 Fin15AnchoredAtom3803 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05652
  ] at hbad
  tauto

theorem fin15Anchored_clause24305 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3803 chi ∧
      ¬Fin15AnchoredAtom1197 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1197 Fin15AnchoredAtom3803 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05652
  ] at hbad
  tauto

theorem fin15Anchored_clause24306 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3803 chi ∧
      ¬Fin15AnchoredAtom1307 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1307 Fin15AnchoredAtom3803 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05652
  ] at hbad
  tauto

theorem fin15Anchored_clause24307 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3803 chi ∧
      ¬Fin15AnchoredAtom1592 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1592 Fin15AnchoredAtom3803 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05652
  ] at hbad
  tauto

theorem fin15Anchored_clause24308 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3803 chi ∧
      Fin15AnchoredAtom1191 chi ∧
      Fin15AnchoredAtom1193 chi ∧
      Fin15AnchoredAtom1197 chi ∧
      Fin15AnchoredAtom1307 chi ∧
      Fin15AnchoredAtom1592 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1191 Fin15AnchoredAtom1193 Fin15AnchoredAtom1197
    Fin15AnchoredAtom1307 Fin15AnchoredAtom1592 Fin15AnchoredAtom3803 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05652
  ] at hbad
  tauto

theorem fin15Anchored_clause24309 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3804 chi ∧
      ¬Fin15AnchoredAtom1191 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1191 Fin15AnchoredAtom3804 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09748
  ] at hbad
  tauto

theorem fin15Anchored_clause24310 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3804 chi ∧
      ¬Fin15AnchoredAtom1194 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1194 Fin15AnchoredAtom3804 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09748
  ] at hbad
  tauto

theorem fin15Anchored_clause24311 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3804 chi ∧
      ¬Fin15AnchoredAtom1198 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1198 Fin15AnchoredAtom3804 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09748
  ] at hbad
  tauto

theorem fin15Anchored_clause24312 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3804 chi ∧
      ¬Fin15AnchoredAtom1308 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1308 Fin15AnchoredAtom3804 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09748
  ] at hbad
  tauto

theorem fin15Anchored_clause24313 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3804 chi ∧
      ¬Fin15AnchoredAtom1593 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1593 Fin15AnchoredAtom3804 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09748
  ] at hbad
  tauto

theorem fin15Anchored_clause24314 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3804 chi ∧
      Fin15AnchoredAtom1191 chi ∧
      Fin15AnchoredAtom1194 chi ∧
      Fin15AnchoredAtom1198 chi ∧
      Fin15AnchoredAtom1308 chi ∧
      Fin15AnchoredAtom1593 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1191 Fin15AnchoredAtom1194 Fin15AnchoredAtom1198
    Fin15AnchoredAtom1308 Fin15AnchoredAtom1593 Fin15AnchoredAtom3804 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09748
  ] at hbad
  tauto

theorem fin15Anchored_clause24315 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3805 chi ∧
      ¬Fin15AnchoredAtom1191 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1191 Fin15AnchoredAtom3805 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17940
  ] at hbad
  tauto

theorem fin15Anchored_clause24316 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3805 chi ∧
      ¬Fin15AnchoredAtom1195 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1195 Fin15AnchoredAtom3805 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17940
  ] at hbad
  tauto

theorem fin15Anchored_clause24317 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3805 chi ∧
      ¬Fin15AnchoredAtom1199 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1199 Fin15AnchoredAtom3805 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17940
  ] at hbad
  tauto

theorem fin15Anchored_clause24318 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3805 chi ∧
      ¬Fin15AnchoredAtom1309 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1309 Fin15AnchoredAtom3805 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17940
  ] at hbad
  tauto

theorem fin15Anchored_clause24319 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3805 chi ∧
      ¬Fin15AnchoredAtom1594 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1594 Fin15AnchoredAtom3805 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17940
  ] at hbad
  tauto

end ErdosSzekeres

end
