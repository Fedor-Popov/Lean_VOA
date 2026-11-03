/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.GNLink0Closure
import VOA.Modularity.GNSwap

/-!
# A grade-bounded induction invariant for Gaberdiel--Neitzke Proposition 8

The unbounded `gnSpan W gen wt N` is the right final target, but it forgets the GN grade of its
spanning words.  GN's outer induction must retain that bound: every commutator and `C₂` replacement
is absorbed at a strictly smaller word grade.  This file records the strengthened invariant and
the forgetful map back to the already-banked `GNReach` API.
-/

namespace VOA

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- The GN target span with the outer-induction grade bound retained in every generator. -/
noncomputable def gnSpanBounded (W : VertexOperatorAlgebra 𝒱) {g : ℕ}
    (gen : Fin g → 𝒱) (wt : Fin g → ℕ) (gr N : ℕ) : Submodule ℂ 𝒱 :=
  Submodule.span ℂ {x | ∃ l : List (GNLetter 𝒱),
    GNWordOK W l ∧ gnWordGrade l ≤ gr ∧ GNWeakDec l ∧ GNNoRepeatLE N l ∧
      OverGens gen wt l ∧ x = gnWord W l W.vacuum}

/-- The grade-bounded form of the GN induction statement. -/
def GNReachBounded (W : VertexOperatorAlgebra 𝒱) {g : ℕ}
    (gen : Fin g → 𝒱) (wt : Fin g → ℕ) (gr N : ℕ) : Prop :=
  gnGradeFil W gr ≤ gnSpanBounded W gen wt gr N

/-- Forgetting the grade bound gives the original GN span. -/
theorem gnSpanBounded_le_gnSpan (W : VertexOperatorAlgebra 𝒱) {g : ℕ}
    (gen : Fin g → 𝒱) (wt : Fin g → ℕ) (gr N : ℕ) :
    gnSpanBounded W gen wt gr N ≤ gnSpan W gen wt N := by
  rw [gnSpanBounded, gnSpan, Submodule.span_le]
  rintro x ⟨l, hOK, _, hweak, hrepeat, hover, rfl⟩
  exact Submodule.subset_span ⟨l, hOK, hweak, hrepeat, hover, rfl⟩

/-- The strengthened invariant implies the original `GNReach`. -/
theorem GNReachBounded.toGNReach {W : VertexOperatorAlgebra 𝒱} {g : ℕ}
    {gen : Fin g → 𝒱} {wt : Fin g → ℕ} {gr N : ℕ}
    (h : GNReachBounded W gen wt gr N) : GNReach W gen wt gr N :=
  le_trans h (gnSpanBounded_le_gnSpan W gen wt gr N)

/-- The bounded target is monotone in the retained grade. -/
theorem gnSpanBounded_mono_grade (W : VertexOperatorAlgebra 𝒱) {g : ℕ}
    (gen : Fin g → 𝒱) (wt : Fin g → ℕ) {gr gr' N : ℕ} (hgr : gr ≤ gr') :
    gnSpanBounded W gen wt gr N ≤ gnSpanBounded W gen wt gr' N := by
  rw [gnSpanBounded, gnSpanBounded, Submodule.span_le]
  rintro x ⟨l, hOK, hgrade, hweak, hrepeat, hover, rfl⟩
  exact Submodule.subset_span ⟨l, hOK, le_trans hgrade hgr, hweak, hrepeat, hover, rfl⟩

/-- A stronger no-repeat bound gives a smaller bounded target span. -/
theorem gnSpanBounded_antitone_index (W : VertexOperatorAlgebra 𝒱) {g : ℕ}
    (gen : Fin g → 𝒱) (wt : Fin g → ℕ) {gr N N' : ℕ} (hN : N ≤ N') :
    gnSpanBounded W gen wt gr N' ≤ gnSpanBounded W gen wt gr N := by
  rw [gnSpanBounded, gnSpanBounded, Submodule.span_le]
  rintro x ⟨l, hOK, hgrade, hweak, hrepeat, hover, rfl⟩
  exact Submodule.subset_span
    ⟨l, hOK, hgrade, hweak, gnNoRepeatLE_of_le hN hrepeat, hover, rfl⟩

/-- A word-level normalisation theorem is exactly what is needed to establish bounded reach. -/
theorem GNReachBounded.of_words {W : VertexOperatorAlgebra 𝒱} {g : ℕ}
    {gen : Fin g → 𝒱} {wt : Fin g → ℕ} {gr N : ℕ}
    (hwords : ∀ l : List (GNLetter 𝒱), GNWordOK W l → gnWordGrade l ≤ gr →
      gnWord W l W.vacuum ∈ gnSpanBounded W gen wt gr N) :
    GNReachBounded W gen wt gr N := by
  rw [GNReachBounded, gnGradeFil, Submodule.span_le]
  rintro x ⟨l, hOK, hgrade, rfl⟩
  exact hwords l hOK hgrade

/-- Conversely, bounded reach normalises every admissible word within the retained grade. -/
theorem GNReachBounded.word_mem {W : VertexOperatorAlgebra 𝒱} {g : ℕ}
    {gen : Fin g → 𝒱} {wt : Fin g → ℕ} {gr N : ℕ}
    (h : GNReachBounded W gen wt gr N) {l : List (GNLetter 𝒱)}
    (hOK : GNWordOK W l) (hgrade : gnWordGrade l ≤ gr) :
    gnWord W l W.vacuum ∈ gnSpanBounded W gen wt gr N :=
  h (word_mem_gnGradeFil W hOK hgrade)

/-- Grade-bounded reach at all parameters is sufficient for the existing Link-0 closure. -/
noncomputable def strictSpanning_of_GNReachBounded (W : VertexOperatorAlgebra 𝒱) {g : ℕ}
    (gen : Fin g → 𝒱) (wt : Fin g → ℕ)
    (hgen : ∀ i, gen i ∈ W.grading (wt i : ℤ))
    (hwt : ∀ i, 1 ≤ wt i)
    (hReach : ∀ gr N, GNReachBounded W gen wt gr N) : StrictSpanning W :=
  strictSpanning_of_GNReach W gen wt hgen hwt
    (fun gr N => (hReach gr N).toGNReach)

end VOA
