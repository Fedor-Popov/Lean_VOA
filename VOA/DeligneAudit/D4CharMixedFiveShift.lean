import VOA.DeligneAudit.D4CharMixedSliceShift

/-! The stable mixed-Cauchy shift, in every four-tuple of formal-variable degrees. -/

namespace VOA.DeligneAudit.D4Char

open scoped BigOperators

noncomputable section

variable {R : Type*} [CommRing R]

theorem gtMixedSlice_eval_sub (q : R) (h : PochhammerUnits q) (u : ℕ → Rˣ)
    (r s t v i j k : ℕ) :
    Finsupp.linearCombination R (gtEval q u 5)
      (gtMixedSlice q h r ((s : ℤ) - i) ((t : ℤ) - j) ((v : ℤ) - k)) =
      if i ≤ s ∧ j ≤ t ∧ k ≤ v then gtMixedFiveCoeff q h u r (s - i) (t - j) (v - k)
        else 0 := by
  rw [gtMixedSlice_nat_sub]
  split_ifs <;> simp only [gtMixedSlice_eval, map_zero]

/-- The mixed five-variable shift, discharged using X, B, Y and e-Pieri. -/
theorem gtMixedFive_shift (q : R) (h : PochhammerUnits q) (u : ℕ → Rˣ) :
    GTMixedFiveShift q h u := by
  intro r s t v
  have hh := congrArg (Finsupp.linearCombination R (gtEval q u 5))
    (gtMixedSlice_shift_card q h r s (t : ℤ) (v : ℤ))
  simp only [map_add, map_sub, map_smul, map_sum, smul_eq_mul, gtMixedSlice_eval] at hh
  have he (j : ℕ) :
      Finsupp.linearCombination R (gtEval q u 5)
        (∑ S ∈ (Finset.univ : Finset (Fin 5)).powersetCard j,
          gtPieriUp q S (gtMixedSlice q h r (s - j : ℕ) t v)) =
        pieriElementary u 5 j * gtMixedFiveCoeff q h u r (s - j) t v := by
    rw [gtPieriUp_eval_card q u j _ (gtMixedSlice_dominant q h r _ _ _), gtMixedSlice_eval]
  have h₁ := gtMixedSlice_eval_sub q h u r s t v 1 1 0
  have h₂ := gtMixedSlice_eval_sub q h u r s t v 1 0 1
  have h₃ := gtMixedSlice_eval_sub q h u r s t v 2 1 1
  simp only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, sub_zero, Nat.sub_zero, Nat.zero_le,
    and_true, true_and, Nat.one_le_iff_ne_zero] at h₁ h₂ h₃
  have hp₁ : ((s : ℤ) - 1).toNat = s - 1 := by omega
  have hp₂ : ((s : ℤ) - 2).toNat = s - 2 := by omega
  have ht₁ : (s ≠ 0 ∧ t ≠ 0) ↔ 0 < s ∧ 0 < t := by omega
  have ht₂ : (s ≠ 0 ∧ v ≠ 0) ↔ 0 < s ∧ 0 < v := by omega
  have ht₃ : (2 ≤ s ∧ t ≠ 0 ∧ v ≠ 0) ↔ 1 < s ∧ 0 < t ∧ 0 < v := by omega
  rw [h₁, h₂, h₃, hp₁, hp₂] at hh
  simp only [ht₁, ht₂, ht₃, mul_ite, mul_zero] at hh
  rw [hh]
  apply Finset.sum_congr rfl
  intro j _
  have hj := he j
  rw [map_sum] at hj
  rw [hj]
  ring

/-- Uniqueness applies without any hypothesis on the GT shift. -/
theorem gtMixedFiveCoeff_eq (q : R) (h : PochhammerUnits q) (u : ℕ → Rˣ)
    (G : ℕ → ℕ → ℕ → ℕ → R) (hG : GTMixedFiveRecurrence q u G)
    (hsG : ∀ r s t v, G r s t v = G s r t v)
    (hzero : ∀ t v, G 0 0 t v =
      gtOneRowCoeff q h (fun i => (u i)⁻¹) 5 t *
        gtOneRowCoeff q h (fun i => (u i)⁻¹) 5 v) :
    gtMixedFiveCoeff q h u = G :=
  gtMixedFiveCoeff_eq_of_shift q h u (gtMixedFive_shift q h u) G hG hsG hzero

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.gtMixedSlice_eval_sub
#print axioms VOA.DeligneAudit.D4Char.gtMixedFive_shift
#print axioms VOA.DeligneAudit.D4Char.gtMixedFiveCoeff_eq
