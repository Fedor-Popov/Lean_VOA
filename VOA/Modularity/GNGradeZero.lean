/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.GNLink2Representatives

/-!
# The grade-zero case of bounded Gaberdiel--Neitzke reach

Positive generator weights force every generator word of GN grade zero to be the empty word.
Consequently the grade-zero bounded span is independent of the no-repeat cutoff.  Combining this
observation with the `N = 0` representative-normalisation theorem removes the truncated-subtraction
circularity in the successor step at outer grade zero.
-/

namespace VOA

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- At GN grade zero, increasing the no-repeat cutoff does not remove any generator word: positivity
forces every witness in the source span to be the empty word. -/
theorem gnSpanBounded_zero_le (W : VertexOperatorAlgebra 𝒱) {g : ℕ}
    (gen : Fin g → 𝒱) (wt : Fin g → ℕ) (hwt : ∀ i, 1 ≤ wt i) (N : ℕ) :
    gnSpanBounded W gen wt 0 0 ≤ gnSpanBounded W gen wt 0 N := by
  rw [gnSpanBounded, gnSpanBounded, Submodule.span_le]
  rintro x ⟨l, hOK, hgrade, hwd, hnr, hover, rfl⟩
  have hl : l = [] := by
    cases l with
    | nil => rfl
    | cons p l =>
        obtain ⟨i, _, hiwt⟩ := hover p (List.mem_cons_self ..)
        have hpwt : 1 ≤ p.2.1 := by
          rw [hiwt]
          exact hwt i
        simp only [gnWordGrade_cons] at hgrade
        omega
  subst l
  exact Submodule.subset_span
    ⟨[], GNWordOK.nil W, by simp [gnWordGrade], by simp [GNWeakDec],
      by simp [GNNoRepeatLE], by simp [OverGens], rfl⟩

/-- Bounded reach at outer grade zero holds for every no-repeat cutoff. -/
theorem gnReachBounded_grade_zero (W : VertexOperatorAlgebra 𝒱) {g : ℕ}
    (gen : Fin g → 𝒱) (wt : Fin g → ℕ)
    (hgen : ∀ i, gen i ∈ W.grading (wt i : ℤ)) (hwt : ∀ i, 1 ≤ wt i)
    (hdec : (⊤ : Submodule ℂ 𝒱) =
      Submodule.span ℂ (Set.range gen ∪ {W.vacuum}) ⊔ O₂ W)
    (N : ℕ) : GNReachBounded W gen wt 0 N :=
  le_trans
    (gnLink2_GNReachBounded_zero W gen wt hgen hwt hdec 0 (by
      intro G hG
      omega))
    (gnSpanBounded_zero_le W gen wt hwt N)

end VOA
