import VOA.DeligneAudit.D4CharMixedFiveCoeff

/-!
Coefficientwise uniqueness for the stable mixed shift. Symmetry in x_1,x_2 means
the negative-only C(2,5) base suffices for both positive-variable induction steps.
The actual GT shift remains an explicit hypothesis in the final reduction.
-/

namespace VOA.DeligneAudit.D4Char

open scoped BigOperators

noncomputable section

variable {R : Type*} [CommRing R]

/-- Uniqueness in x_2 with a fixed x_1 degree and arbitrary y degrees. -/
theorem gtMixedFiveRecurrence_unique_row (q : R) (h : PochhammerUnits q)
    (u : ℕ → Rˣ) (F G : ℕ → ℕ → ℕ → ℕ → R)
    (hF : GTMixedFiveRecurrence q u F) (hG : GTMixedFiveRecurrence q u G)
    (r : ℕ) (hzero : ∀ t v, F r 0 t v = G r 0 t v) :
    ∀ s t v, F r s t v = G r s t v := by
  intro s
  induction s using Nat.strong_induction_on with
  | h s ih =>
      intro t v
      by_cases hs : s = 0
      · subst s
        exact hzero t v
      have h₁ : (if 0 < s ∧ 0 < t then
          q ^ (s - 1) * F r (s - 1) (t - 1) v else 0) =
          (if 0 < s ∧ 0 < t then
            q ^ (s - 1) * G r (s - 1) (t - 1) v else 0) := by
        split_ifs <;> simp only [ih (s - 1) (by omega)]
      have h₂ : (if 0 < s ∧ 0 < v then
          q ^ (s - 1) * F r (s - 1) t (v - 1) else 0) =
          (if 0 < s ∧ 0 < v then
            q ^ (s - 1) * G r (s - 1) t (v - 1) else 0) := by
        split_ifs <;> simp only [ih (s - 1) (by omega)]
      have h₃ : (if 1 < s ∧ 0 < t ∧ 0 < v then
          q ^ (s - 2) * F r (s - 2) (t - 1) (v - 1) else 0) =
          (if 1 < s ∧ 0 < t ∧ 0 < v then
            q ^ (s - 2) * G r (s - 2) (t - 1) (v - 1) else 0) := by
        split_ifs <;> simp only [ih (s - 2) (by omega)]
      have htail : (∑ j ∈ Finset.range s,
          (-1 : R) ^ (j + 1) * pieriElementary u 5 (j + 1) *
            F r (s - (j + 1)) t v) =
          ∑ j ∈ Finset.range s,
            (-1 : R) ^ (j + 1) * pieriElementary u 5 (j + 1) *
              G r (s - (j + 1)) t v := by
        apply Finset.sum_congr rfl
        intro j _
        rw [ih (s - (j + 1)) (by omega)]
      have hf := hF r s t v
      have hg := hG r s t v
      rw [Finset.sum_range_succ'] at hf hg
      have he : pieriElementary u 5 0 = 1 := by simp [pieriElementary]
      simp only [pow_zero, he, one_mul, Nat.sub_zero] at hf hg
      rw [h₁, h₂, h₃, htail] at hf
      apply (pochhammerUnits_qDifferenceUnits q h s (by omega)).mul_left_cancel
      linear_combination hg - hf

/-- The negative-only base and x symmetry determine all four-degree coefficients. -/
theorem gtMixedFiveRecurrence_unique (q : R) (h : PochhammerUnits q)
    (u : ℕ → Rˣ) (F G : ℕ → ℕ → ℕ → ℕ → R)
    (hF : GTMixedFiveRecurrence q u F) (hG : GTMixedFiveRecurrence q u G)
    (hsF : ∀ r s t v, F r s t v = F s r t v)
    (hsG : ∀ r s t v, G r s t v = G s r t v)
    (hzero : ∀ t v, F 0 0 t v = G 0 0 t v) : F = G := by
  have hrow := gtMixedFiveRecurrence_unique_row q h u F G hF hG 0 hzero
  funext r s t v
  apply gtMixedFiveRecurrence_unique_row q h u F G hF hG r ?_ s t v
  intro t' v'
  rw [hsF r 0, hsG r 0]
  exact hrow r t' v'

/-- Precise reduction of the stable GT sum to its remaining homogeneous shift. -/
theorem gtMixedFiveCoeff_eq_of_shift (q : R) (h : PochhammerUnits q) (u : ℕ → Rˣ)
    (hshift : GTMixedFiveShift q h u) (G : ℕ → ℕ → ℕ → ℕ → R)
    (hG : GTMixedFiveRecurrence q u G)
    (hsG : ∀ r s t v, G r s t v = G s r t v)
    (hzero : ∀ t v, G 0 0 t v =
      gtOneRowCoeff q h (fun i => (u i)⁻¹) 5 t *
        gtOneRowCoeff q h (fun i => (u i)⁻¹) 5 v) :
    gtMixedFiveCoeff q h u = G := by
  apply gtMixedFiveRecurrence_unique q h u _ G hshift hG
    (gtMixedFiveCoeff_swap_x q h u) hsG
  intro t v
  rw [gtMixedFiveCoeff_zero_x, hzero]

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.gtMixedFiveRecurrence_unique_row
#print axioms VOA.DeligneAudit.D4Char.gtMixedFiveRecurrence_unique
#print axioms VOA.DeligneAudit.D4Char.gtMixedFiveCoeff_eq_of_shift
