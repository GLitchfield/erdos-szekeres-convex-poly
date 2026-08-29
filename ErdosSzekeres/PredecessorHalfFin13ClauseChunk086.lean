module

public import ErdosSzekeres.PredecessorHalfFin13Support

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Retained Fin13 semantic clauses in bounded group 086. -/

theorem predecessorHalfFin13_clause24258 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2184 chi ∧
      PredecessorHalfFin13Atom0883 chi ∧
      PredecessorHalfFin13Atom0886 chi ∧
      PredecessorHalfFin13Atom0893 chi ∧
      PredecessorHalfFin13Atom0918 chi ∧
      PredecessorHalfFin13Atom0953 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0883 PredecessorHalfFin13Atom0886 PredecessorHalfFin13Atom0893
    PredecessorHalfFin13Atom0918 PredecessorHalfFin13Atom0953 PredecessorHalfFin13Atom2184 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4784
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24259 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2185 chi ∧
      ¬PredecessorHalfFin13Atom0884 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0884 PredecessorHalfFin13Atom2185 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3248
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24260 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2185 chi ∧
      ¬PredecessorHalfFin13Atom0885 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0885 PredecessorHalfFin13Atom2185 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3248
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24261 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2185 chi ∧
      ¬PredecessorHalfFin13Atom0894 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0894 PredecessorHalfFin13Atom2185 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3248
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24262 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2185 chi ∧
      ¬PredecessorHalfFin13Atom0919 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0919 PredecessorHalfFin13Atom2185 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3248
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24263 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2185 chi ∧
      ¬PredecessorHalfFin13Atom0954 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0954 PredecessorHalfFin13Atom2185 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3248
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24265 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2186 chi ∧
      ¬PredecessorHalfFin13Atom0884 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0884 PredecessorHalfFin13Atom2186 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5296
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24266 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2186 chi ∧
      ¬PredecessorHalfFin13Atom0886 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0886 PredecessorHalfFin13Atom2186 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5296
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24267 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2186 chi ∧
      ¬PredecessorHalfFin13Atom0895 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0895 PredecessorHalfFin13Atom2186 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5296
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24268 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2186 chi ∧
      ¬PredecessorHalfFin13Atom0920 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0920 PredecessorHalfFin13Atom2186 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5296
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24269 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2186 chi ∧
      ¬PredecessorHalfFin13Atom0955 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0955 PredecessorHalfFin13Atom2186 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5296
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24270 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2186 chi ∧
      PredecessorHalfFin13Atom0884 chi ∧
      PredecessorHalfFin13Atom0886 chi ∧
      PredecessorHalfFin13Atom0895 chi ∧
      PredecessorHalfFin13Atom0920 chi ∧
      PredecessorHalfFin13Atom0955 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0884 PredecessorHalfFin13Atom0886 PredecessorHalfFin13Atom0895
    PredecessorHalfFin13Atom0920 PredecessorHalfFin13Atom0955 PredecessorHalfFin13Atom2186 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5296
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24272 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2187 chi ∧
      ¬PredecessorHalfFin13Atom0886 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0886 PredecessorHalfFin13Atom2187 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6320
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24274 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2187 chi ∧
      ¬PredecessorHalfFin13Atom0921 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0921 PredecessorHalfFin13Atom2187 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6320
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24275 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2187 chi ∧
      ¬PredecessorHalfFin13Atom0956 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0956 PredecessorHalfFin13Atom2187 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6320
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24277 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2188 chi ∧
      ¬PredecessorHalfFin13Atom0887 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0887 PredecessorHalfFin13Atom2188 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1840
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24278 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2188 chi ∧
      ¬PredecessorHalfFin13Atom0888 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0888 PredecessorHalfFin13Atom2188 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1840
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24279 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2188 chi ∧
      ¬PredecessorHalfFin13Atom0891 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0891 PredecessorHalfFin13Atom2188 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1840
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24280 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2188 chi ∧
      ¬PredecessorHalfFin13Atom0922 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0922 PredecessorHalfFin13Atom2188 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1840
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24281 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2188 chi ∧
      ¬PredecessorHalfFin13Atom0957 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0957 PredecessorHalfFin13Atom2188 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1840
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24282 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2188 chi ∧
      PredecessorHalfFin13Atom0887 chi ∧
      PredecessorHalfFin13Atom0888 chi ∧
      PredecessorHalfFin13Atom0891 chi ∧
      PredecessorHalfFin13Atom0922 chi ∧
      PredecessorHalfFin13Atom0957 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0887 PredecessorHalfFin13Atom0888 PredecessorHalfFin13Atom0891
    PredecessorHalfFin13Atom0922 PredecessorHalfFin13Atom0957 PredecessorHalfFin13Atom2188 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1840
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24283 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2189 chi ∧
      ¬PredecessorHalfFin13Atom0887 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0887 PredecessorHalfFin13Atom2189 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2864
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24284 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2189 chi ∧
      ¬PredecessorHalfFin13Atom0889 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0889 PredecessorHalfFin13Atom2189 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2864
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24285 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2189 chi ∧
      ¬PredecessorHalfFin13Atom0892 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0892 PredecessorHalfFin13Atom2189 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2864
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24286 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2189 chi ∧
      ¬PredecessorHalfFin13Atom0923 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0923 PredecessorHalfFin13Atom2189 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2864
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24287 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2189 chi ∧
      ¬PredecessorHalfFin13Atom0958 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0958 PredecessorHalfFin13Atom2189 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2864
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24288 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2189 chi ∧
      PredecessorHalfFin13Atom0887 chi ∧
      PredecessorHalfFin13Atom0889 chi ∧
      PredecessorHalfFin13Atom0892 chi ∧
      PredecessorHalfFin13Atom0923 chi ∧
      PredecessorHalfFin13Atom0958 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0887 PredecessorHalfFin13Atom0889 PredecessorHalfFin13Atom0892
    PredecessorHalfFin13Atom0923 PredecessorHalfFin13Atom0958 PredecessorHalfFin13Atom2189 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2864
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24289 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2190 chi ∧
      ¬PredecessorHalfFin13Atom0887 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0887 PredecessorHalfFin13Atom2190 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4912
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24290 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2190 chi ∧
      ¬PredecessorHalfFin13Atom0890 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0890 PredecessorHalfFin13Atom2190 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4912
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24291 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2190 chi ∧
      ¬PredecessorHalfFin13Atom0893 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0893 PredecessorHalfFin13Atom2190 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4912
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24292 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2190 chi ∧
      ¬PredecessorHalfFin13Atom0924 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0924 PredecessorHalfFin13Atom2190 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4912
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24293 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2190 chi ∧
      ¬PredecessorHalfFin13Atom0959 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0959 PredecessorHalfFin13Atom2190 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4912
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24294 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2190 chi ∧
      PredecessorHalfFin13Atom0887 chi ∧
      PredecessorHalfFin13Atom0890 chi ∧
      PredecessorHalfFin13Atom0893 chi ∧
      PredecessorHalfFin13Atom0924 chi ∧
      PredecessorHalfFin13Atom0959 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0887 PredecessorHalfFin13Atom0890 PredecessorHalfFin13Atom0893
    PredecessorHalfFin13Atom0924 PredecessorHalfFin13Atom0959 PredecessorHalfFin13Atom2190 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4912
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24295 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2191 chi ∧
      ¬PredecessorHalfFin13Atom0888 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0888 PredecessorHalfFin13Atom2191 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3376
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24296 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2191 chi ∧
      ¬PredecessorHalfFin13Atom0889 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0889 PredecessorHalfFin13Atom2191 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3376
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24297 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2191 chi ∧
      ¬PredecessorHalfFin13Atom0894 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0894 PredecessorHalfFin13Atom2191 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3376
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24298 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2191 chi ∧
      ¬PredecessorHalfFin13Atom0925 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0925 PredecessorHalfFin13Atom2191 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3376
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24299 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2191 chi ∧
      ¬PredecessorHalfFin13Atom0960 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0960 PredecessorHalfFin13Atom2191 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3376
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24300 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2191 chi ∧
      PredecessorHalfFin13Atom0888 chi ∧
      PredecessorHalfFin13Atom0889 chi ∧
      PredecessorHalfFin13Atom0894 chi ∧
      PredecessorHalfFin13Atom0925 chi ∧
      PredecessorHalfFin13Atom0960 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0888 PredecessorHalfFin13Atom0889 PredecessorHalfFin13Atom0894
    PredecessorHalfFin13Atom0925 PredecessorHalfFin13Atom0960 PredecessorHalfFin13Atom2191 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3376
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24301 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2192 chi ∧
      ¬PredecessorHalfFin13Atom0888 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0888 PredecessorHalfFin13Atom2192 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5424
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24302 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2192 chi ∧
      ¬PredecessorHalfFin13Atom0890 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0890 PredecessorHalfFin13Atom2192 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5424
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24303 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2192 chi ∧
      ¬PredecessorHalfFin13Atom0895 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0895 PredecessorHalfFin13Atom2192 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5424
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24304 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2192 chi ∧
      ¬PredecessorHalfFin13Atom0926 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0926 PredecessorHalfFin13Atom2192 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5424
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24305 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2192 chi ∧
      ¬PredecessorHalfFin13Atom0961 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0961 PredecessorHalfFin13Atom2192 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5424
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24306 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2192 chi ∧
      PredecessorHalfFin13Atom0888 chi ∧
      PredecessorHalfFin13Atom0890 chi ∧
      PredecessorHalfFin13Atom0895 chi ∧
      PredecessorHalfFin13Atom0926 chi ∧
      PredecessorHalfFin13Atom0961 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0888 PredecessorHalfFin13Atom0890 PredecessorHalfFin13Atom0895
    PredecessorHalfFin13Atom0926 PredecessorHalfFin13Atom0961 PredecessorHalfFin13Atom2192 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5424
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24308 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2193 chi ∧
      ¬PredecessorHalfFin13Atom0890 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0890 PredecessorHalfFin13Atom2193 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6448
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24310 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2193 chi ∧
      ¬PredecessorHalfFin13Atom0927 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0927 PredecessorHalfFin13Atom2193 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6448
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24311 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2193 chi ∧
      ¬PredecessorHalfFin13Atom0962 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0962 PredecessorHalfFin13Atom2193 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6448
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24313 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2194 chi ∧
      ¬PredecessorHalfFin13Atom0891 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0891 PredecessorHalfFin13Atom2194 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3632
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24314 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2194 chi ∧
      ¬PredecessorHalfFin13Atom0892 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0892 PredecessorHalfFin13Atom2194 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3632
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24315 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2194 chi ∧
      ¬PredecessorHalfFin13Atom0894 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0894 PredecessorHalfFin13Atom2194 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3632
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24316 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2194 chi ∧
      ¬PredecessorHalfFin13Atom0928 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0928 PredecessorHalfFin13Atom2194 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3632
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24317 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2194 chi ∧
      ¬PredecessorHalfFin13Atom0963 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0963 PredecessorHalfFin13Atom2194 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3632
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24319 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2195 chi ∧
      ¬PredecessorHalfFin13Atom0891 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0891 PredecessorHalfFin13Atom2195 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5680
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24320 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2195 chi ∧
      ¬PredecessorHalfFin13Atom0893 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0893 PredecessorHalfFin13Atom2195 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5680
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24321 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2195 chi ∧
      ¬PredecessorHalfFin13Atom0895 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0895 PredecessorHalfFin13Atom2195 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5680
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24322 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2195 chi ∧
      ¬PredecessorHalfFin13Atom0929 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0929 PredecessorHalfFin13Atom2195 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5680
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24323 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2195 chi ∧
      ¬PredecessorHalfFin13Atom0964 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0964 PredecessorHalfFin13Atom2195 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5680
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24324 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2195 chi ∧
      PredecessorHalfFin13Atom0891 chi ∧
      PredecessorHalfFin13Atom0893 chi ∧
      PredecessorHalfFin13Atom0895 chi ∧
      PredecessorHalfFin13Atom0929 chi ∧
      PredecessorHalfFin13Atom0964 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0891 PredecessorHalfFin13Atom0893 PredecessorHalfFin13Atom0895
    PredecessorHalfFin13Atom0929 PredecessorHalfFin13Atom0964 PredecessorHalfFin13Atom2195 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5680
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24325 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2196 chi ∧
      ¬PredecessorHalfFin13Atom0892 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0892 PredecessorHalfFin13Atom2196 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6704
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24326 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2196 chi ∧
      ¬PredecessorHalfFin13Atom0893 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0893 PredecessorHalfFin13Atom2196 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6704
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24328 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2196 chi ∧
      ¬PredecessorHalfFin13Atom0930 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0930 PredecessorHalfFin13Atom2196 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6704
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24329 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2196 chi ∧
      ¬PredecessorHalfFin13Atom0965 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0965 PredecessorHalfFin13Atom2196 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6704
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24330 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2196 chi ∧
      PredecessorHalfFin13Atom0892 chi ∧
      PredecessorHalfFin13Atom0893 chi ∧
      PredecessorHalfFin13Atom0896 chi ∧
      PredecessorHalfFin13Atom0930 chi ∧
      PredecessorHalfFin13Atom0965 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0892 PredecessorHalfFin13Atom0893 PredecessorHalfFin13Atom0896
    PredecessorHalfFin13Atom0930 PredecessorHalfFin13Atom0965 PredecessorHalfFin13Atom2196 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6704
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24331 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2197 chi ∧
      ¬PredecessorHalfFin13Atom0894 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0894 PredecessorHalfFin13Atom2197 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7216
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24332 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2197 chi ∧
      ¬PredecessorHalfFin13Atom0895 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0895 PredecessorHalfFin13Atom2197 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7216
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24334 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2197 chi ∧
      ¬PredecessorHalfFin13Atom0931 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0931 PredecessorHalfFin13Atom2197 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7216
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24335 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2197 chi ∧
      ¬PredecessorHalfFin13Atom0966 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0966 PredecessorHalfFin13Atom2197 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask7216
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24337 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2198 chi ∧
      ¬PredecessorHalfFin13Atom0897 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0897 PredecessorHalfFin13Atom2198 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0976
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24338 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2198 chi ∧
      ¬PredecessorHalfFin13Atom0898 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0898 PredecessorHalfFin13Atom2198 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0976
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24339 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2198 chi ∧
      ¬PredecessorHalfFin13Atom0902 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0902 PredecessorHalfFin13Atom2198 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0976
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24340 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2198 chi ∧
      ¬PredecessorHalfFin13Atom0912 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0912 PredecessorHalfFin13Atom2198 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0976
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24341 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2198 chi ∧
      ¬PredecessorHalfFin13Atom0967 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0967 PredecessorHalfFin13Atom2198 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0976
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24342 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2198 chi ∧
      PredecessorHalfFin13Atom0897 chi ∧
      PredecessorHalfFin13Atom0898 chi ∧
      PredecessorHalfFin13Atom0902 chi ∧
      PredecessorHalfFin13Atom0912 chi ∧
      PredecessorHalfFin13Atom0967 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0897 PredecessorHalfFin13Atom0898 PredecessorHalfFin13Atom0902
    PredecessorHalfFin13Atom0912 PredecessorHalfFin13Atom0967 PredecessorHalfFin13Atom2198 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0976
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24343 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2199 chi ∧
      ¬PredecessorHalfFin13Atom0897 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0897 PredecessorHalfFin13Atom2199 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1488
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24344 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2199 chi ∧
      ¬PredecessorHalfFin13Atom0899 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0899 PredecessorHalfFin13Atom2199 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1488
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24345 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2199 chi ∧
      ¬PredecessorHalfFin13Atom0903 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0903 PredecessorHalfFin13Atom2199 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1488
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24346 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2199 chi ∧
      ¬PredecessorHalfFin13Atom0913 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0913 PredecessorHalfFin13Atom2199 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1488
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24347 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2199 chi ∧
      ¬PredecessorHalfFin13Atom0968 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0968 PredecessorHalfFin13Atom2199 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1488
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24348 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2199 chi ∧
      PredecessorHalfFin13Atom0897 chi ∧
      PredecessorHalfFin13Atom0899 chi ∧
      PredecessorHalfFin13Atom0903 chi ∧
      PredecessorHalfFin13Atom0913 chi ∧
      PredecessorHalfFin13Atom0968 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0897 PredecessorHalfFin13Atom0899 PredecessorHalfFin13Atom0903
    PredecessorHalfFin13Atom0913 PredecessorHalfFin13Atom0968 PredecessorHalfFin13Atom2199 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1488
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24349 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2200 chi ∧
      ¬PredecessorHalfFin13Atom0897 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0897 PredecessorHalfFin13Atom2200 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2512
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24350 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2200 chi ∧
      ¬PredecessorHalfFin13Atom0900 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0900 PredecessorHalfFin13Atom2200 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2512
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24351 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2200 chi ∧
      ¬PredecessorHalfFin13Atom0904 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0904 PredecessorHalfFin13Atom2200 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2512
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24352 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2200 chi ∧
      ¬PredecessorHalfFin13Atom0914 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0914 PredecessorHalfFin13Atom2200 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2512
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24353 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2200 chi ∧
      ¬PredecessorHalfFin13Atom0969 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0969 PredecessorHalfFin13Atom2200 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2512
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24354 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2200 chi ∧
      PredecessorHalfFin13Atom0897 chi ∧
      PredecessorHalfFin13Atom0900 chi ∧
      PredecessorHalfFin13Atom0904 chi ∧
      PredecessorHalfFin13Atom0914 chi ∧
      PredecessorHalfFin13Atom0969 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0897 PredecessorHalfFin13Atom0900 PredecessorHalfFin13Atom0904
    PredecessorHalfFin13Atom0914 PredecessorHalfFin13Atom0969 PredecessorHalfFin13Atom2200 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2512
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24355 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2201 chi ∧
      ¬PredecessorHalfFin13Atom0897 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0897 PredecessorHalfFin13Atom2201 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4560
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24356 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2201 chi ∧
      ¬PredecessorHalfFin13Atom0901 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0901 PredecessorHalfFin13Atom2201 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4560
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24357 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2201 chi ∧
      ¬PredecessorHalfFin13Atom0905 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0905 PredecessorHalfFin13Atom2201 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4560
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24358 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2201 chi ∧
      ¬PredecessorHalfFin13Atom0915 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0915 PredecessorHalfFin13Atom2201 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4560
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24359 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2201 chi ∧
      ¬PredecessorHalfFin13Atom0970 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0970 PredecessorHalfFin13Atom2201 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4560
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24360 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2201 chi ∧
      PredecessorHalfFin13Atom0897 chi ∧
      PredecessorHalfFin13Atom0901 chi ∧
      PredecessorHalfFin13Atom0905 chi ∧
      PredecessorHalfFin13Atom0915 chi ∧
      PredecessorHalfFin13Atom0970 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0897 PredecessorHalfFin13Atom0901 PredecessorHalfFin13Atom0905
    PredecessorHalfFin13Atom0915 PredecessorHalfFin13Atom0970 PredecessorHalfFin13Atom2201 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4560
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24361 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2202 chi ∧
      ¬PredecessorHalfFin13Atom0898 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0898 PredecessorHalfFin13Atom2202 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1744
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24362 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2202 chi ∧
      ¬PredecessorHalfFin13Atom0899 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0899 PredecessorHalfFin13Atom2202 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1744
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24363 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2202 chi ∧
      ¬PredecessorHalfFin13Atom0906 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0906 PredecessorHalfFin13Atom2202 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1744
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24364 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2202 chi ∧
      ¬PredecessorHalfFin13Atom0916 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0916 PredecessorHalfFin13Atom2202 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1744
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24365 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2202 chi ∧
      ¬PredecessorHalfFin13Atom0971 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0971 PredecessorHalfFin13Atom2202 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1744
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24366 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2202 chi ∧
      PredecessorHalfFin13Atom0898 chi ∧
      PredecessorHalfFin13Atom0899 chi ∧
      PredecessorHalfFin13Atom0906 chi ∧
      PredecessorHalfFin13Atom0916 chi ∧
      PredecessorHalfFin13Atom0971 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0898 PredecessorHalfFin13Atom0899 PredecessorHalfFin13Atom0906
    PredecessorHalfFin13Atom0916 PredecessorHalfFin13Atom0971 PredecessorHalfFin13Atom2202 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1744
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24367 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2203 chi ∧
      ¬PredecessorHalfFin13Atom0898 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0898 PredecessorHalfFin13Atom2203 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2768
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24368 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2203 chi ∧
      ¬PredecessorHalfFin13Atom0900 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0900 PredecessorHalfFin13Atom2203 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2768
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24369 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2203 chi ∧
      ¬PredecessorHalfFin13Atom0907 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0907 PredecessorHalfFin13Atom2203 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2768
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24370 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2203 chi ∧
      ¬PredecessorHalfFin13Atom0917 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0917 PredecessorHalfFin13Atom2203 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2768
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24371 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2203 chi ∧
      ¬PredecessorHalfFin13Atom0972 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0972 PredecessorHalfFin13Atom2203 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2768
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24372 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2203 chi ∧
      PredecessorHalfFin13Atom0898 chi ∧
      PredecessorHalfFin13Atom0900 chi ∧
      PredecessorHalfFin13Atom0907 chi ∧
      PredecessorHalfFin13Atom0917 chi ∧
      PredecessorHalfFin13Atom0972 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0898 PredecessorHalfFin13Atom0900 PredecessorHalfFin13Atom0907
    PredecessorHalfFin13Atom0917 PredecessorHalfFin13Atom0972 PredecessorHalfFin13Atom2203 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2768
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24373 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2204 chi ∧
      ¬PredecessorHalfFin13Atom0898 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0898 PredecessorHalfFin13Atom2204 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4816
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24374 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2204 chi ∧
      ¬PredecessorHalfFin13Atom0901 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0901 PredecessorHalfFin13Atom2204 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4816
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24375 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2204 chi ∧
      ¬PredecessorHalfFin13Atom0908 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0908 PredecessorHalfFin13Atom2204 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4816
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24376 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2204 chi ∧
      ¬PredecessorHalfFin13Atom0918 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0918 PredecessorHalfFin13Atom2204 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4816
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24377 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2204 chi ∧
      ¬PredecessorHalfFin13Atom0973 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0973 PredecessorHalfFin13Atom2204 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4816
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24378 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2204 chi ∧
      PredecessorHalfFin13Atom0898 chi ∧
      PredecessorHalfFin13Atom0901 chi ∧
      PredecessorHalfFin13Atom0908 chi ∧
      PredecessorHalfFin13Atom0918 chi ∧
      PredecessorHalfFin13Atom0973 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0898 PredecessorHalfFin13Atom0901 PredecessorHalfFin13Atom0908
    PredecessorHalfFin13Atom0918 PredecessorHalfFin13Atom0973 PredecessorHalfFin13Atom2204 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4816
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24379 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2205 chi ∧
      ¬PredecessorHalfFin13Atom0899 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0899 PredecessorHalfFin13Atom2205 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3280
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24380 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2205 chi ∧
      ¬PredecessorHalfFin13Atom0900 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0900 PredecessorHalfFin13Atom2205 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3280
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24381 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2205 chi ∧
      ¬PredecessorHalfFin13Atom0909 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0909 PredecessorHalfFin13Atom2205 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3280
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24382 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2205 chi ∧
      ¬PredecessorHalfFin13Atom0919 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0919 PredecessorHalfFin13Atom2205 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3280
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24383 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2205 chi ∧
      ¬PredecessorHalfFin13Atom0974 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0974 PredecessorHalfFin13Atom2205 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3280
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24384 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2205 chi ∧
      PredecessorHalfFin13Atom0899 chi ∧
      PredecessorHalfFin13Atom0900 chi ∧
      PredecessorHalfFin13Atom0909 chi ∧
      PredecessorHalfFin13Atom0919 chi ∧
      PredecessorHalfFin13Atom0974 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0899 PredecessorHalfFin13Atom0900 PredecessorHalfFin13Atom0909
    PredecessorHalfFin13Atom0919 PredecessorHalfFin13Atom0974 PredecessorHalfFin13Atom2205 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3280
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24385 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2206 chi ∧
      ¬PredecessorHalfFin13Atom0899 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0899 PredecessorHalfFin13Atom2206 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5328
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24386 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2206 chi ∧
      ¬PredecessorHalfFin13Atom0901 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0901 PredecessorHalfFin13Atom2206 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5328
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24387 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2206 chi ∧
      ¬PredecessorHalfFin13Atom0910 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0910 PredecessorHalfFin13Atom2206 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5328
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24388 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2206 chi ∧
      ¬PredecessorHalfFin13Atom0920 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0920 PredecessorHalfFin13Atom2206 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5328
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24389 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2206 chi ∧
      ¬PredecessorHalfFin13Atom0975 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0975 PredecessorHalfFin13Atom2206 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5328
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24390 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2206 chi ∧
      PredecessorHalfFin13Atom0899 chi ∧
      PredecessorHalfFin13Atom0901 chi ∧
      PredecessorHalfFin13Atom0910 chi ∧
      PredecessorHalfFin13Atom0920 chi ∧
      PredecessorHalfFin13Atom0975 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0899 PredecessorHalfFin13Atom0901 PredecessorHalfFin13Atom0910
    PredecessorHalfFin13Atom0920 PredecessorHalfFin13Atom0975 PredecessorHalfFin13Atom2206 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5328
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24391 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2207 chi ∧
      ¬PredecessorHalfFin13Atom0900 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0900 PredecessorHalfFin13Atom2207 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6352
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24392 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2207 chi ∧
      ¬PredecessorHalfFin13Atom0901 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0901 PredecessorHalfFin13Atom2207 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6352
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24394 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2207 chi ∧
      ¬PredecessorHalfFin13Atom0921 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0921 PredecessorHalfFin13Atom2207 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6352
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24396 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom2207 chi ∧
      PredecessorHalfFin13Atom0900 chi ∧
      PredecessorHalfFin13Atom0901 chi ∧
      PredecessorHalfFin13Atom0911 chi ∧
      PredecessorHalfFin13Atom0921 chi ∧
      PredecessorHalfFin13Atom0976 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0900 PredecessorHalfFin13Atom0901 PredecessorHalfFin13Atom0911
    PredecessorHalfFin13Atom0921 PredecessorHalfFin13Atom0976 PredecessorHalfFin13Atom2207 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6352
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24397 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2208 chi ∧
      ¬PredecessorHalfFin13Atom0902 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0902 PredecessorHalfFin13Atom2208 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1872
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause24398 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom2208 chi ∧
      ¬PredecessorHalfFin13Atom0903 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0903 PredecessorHalfFin13Atom2208 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1872
  ] at hbad
  tauto

end ErdosSzekeres

end
