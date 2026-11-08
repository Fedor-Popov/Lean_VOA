import VOA.Moonshine.MoonshineCNHyperbolicNegativeModes

/-! # Positive Sugawara commutators with creation operators -/

noncomputable section

namespace VOA.Moonshine.ConwayNorton

open MvPolynomial
open scoped BigOperators

theorem hypSecondDerivative_creation (u w v : ℕ × Fin 2) (p : hypFock) :
    pderiv u (pderiv w (X v * p)) = X v * pderiv u (pderiv w p) +
      (if v = w then pderiv u p else 0) + (if v = u then pderiv w p else 0) := by
  classical
  simp only [pderiv_mul, pderiv_X, Pi.single_apply]
  split_ifs <;> simp_all [pderiv_X] <;> ring

theorem hypPositiveSecondOrder_creation_sum (j : ℕ) (v : ℕ × Fin 2) (p : hypFock) :
    hypPositiveSecondOrder j (X v * p) - X v * hypPositiveSecondOrder j p =
      (∑ k ∈ Finset.range j, ((k + 1 : ℂ) * (j - k : ℂ)) •
        (if v = (j - 1 - k, 1) then pderiv (k, 0) p else 0)) +
      (∑ k ∈ Finset.range j, ((k + 1 : ℂ) * (j - k : ℂ)) •
        (if v = (k, 0) then pderiv (j - 1 - k, 1) p else 0)) := by
  simp only [hypPositiveSecondOrder, LinearMap.sum_apply, LinearMap.smul_apply,
    Module.End.mul_apply, Derivation.coeFn_coe, Derivation.map_smul,
    hypSecondDerivative_creation, smul_add, Finset.sum_add_distrib,
    ← mul_smul_comm, ← Finset.mul_sum]
  abel

theorem hypPositiveSecondOrder_creation_a (j t : ℕ) (p : hypFock) :
    hypPositiveSecondOrder j (X (t, 0) * p) - X (t, 0) * hypPositiveSecondOrder j p =
      if t < j then ((t + 1 : ℂ) * (j - t : ℂ)) • pderiv (j - 1 - t, 1) p else 0 := by
  rw [hypPositiveSecondOrder_creation_sum]
  simp only [Prod.mk.injEq, show (0 : Fin 2) ≠ 1 by decide, and_false, if_false,
    smul_zero, Finset.sum_const_zero, zero_add, and_true]
  simp [smul_ite, Finset.mem_range]

theorem hypPositiveSecondOrder_creation_b (j t : ℕ) (p : hypFock) :
    hypPositiveSecondOrder j (X (t, 1) * p) - X (t, 1) * hypPositiveSecondOrder j p =
      if t < j then ((t + 1 : ℂ) * (j - t : ℂ)) • pderiv (j - 1 - t, 0) p else 0 := by
  rw [hypPositiveSecondOrder_creation_sum]
  simp only [Prod.mk.injEq, show (1 : Fin 2) ≠ 0 by decide, and_false, if_false,
    smul_zero, Finset.sum_const_zero, add_zero, and_true]
  by_cases ht : t < j
  · rw [if_pos ht, Finset.sum_eq_single (j - 1 - t)]
    · have he : j - 1 - (j - 1 - t) = t := by omega
      rw [he, if_pos rfl]
      have ha : ((j - 1 - t : ℕ) + 1 : ℂ) = (j : ℂ) - t := by
        have hn : j - 1 - t + 1 + t = j := by omega
        have hc := congrArg (fun n : ℕ => (n : ℂ)) hn
        push_cast at hc
        linear_combination hc
      have hb : (j : ℂ) - (j - 1 - t : ℕ) = t + 1 := by
        have hn : j - 1 - t + (t + 1) = j := by omega
        have hc := congrArg (fun n : ℕ => (n : ℂ)) hn
        push_cast at hc
        linear_combination -hc
      rw [ha, hb, mul_comm]
    · intro k hk hkt
      have hk' := Finset.mem_range.mp hk
      have he : t ≠ j - 1 - k := by omega
      simp [he]
    · intro h
      exact (h (Finset.mem_range.mpr (by omega))).elim
  · rw [if_neg ht]
    apply Finset.sum_eq_zero
    intro k hk
    have hk' := Finset.mem_range.mp hk
    have he : t ≠ j - 1 - k := by omega
    simp [he]

theorem hypPositiveSecondOrder_creation (j t : ℕ) (a : Fin 2) (p : hypFock) :
    hypPositiveSecondOrder j (X (t, a) * p) - X (t, a) * hypPositiveSecondOrder j p =
      if t < j then ((t + 1 : ℂ) * (j - t : ℂ)) • pderiv (j - 1 - t, a.rev) p else 0 := by
  fin_cases a
  · exact hypPositiveSecondOrder_creation_a j t p
  · exact hypPositiveSecondOrder_creation_b j t p

/-- The exact positive-mode creation commutator, including the momentum term. -/
theorem hypSugawara_positive_creation (κ ell : ℂ) (j t : ℕ) (a : Fin 2) (p : hypFock) :
    hypSugawara κ ell (j + 1 : ℤ) (X (t, a) * p) -
      X (t, a) * hypSugawara κ ell (j + 1 : ℤ) p =
      (t + 1 : ℂ) • hypOscillator a (if a = 0 then κ else ell) ((j : ℤ) - t) p := by
  rw [hypSugawara_positive, hypSugawara_positive, Derivation.leibniz,
    hypLoweringDerivation_X]
  have h := hypPositiveSecondOrder_creation j t a p
  simp only [smul_eq_mul] at *
  rw [mul_add]
  have he : ∀ A B C E : hypFock, B + A + C - (B + E) = A + (C - E) := by
    intros; ring
  rw [he, h]
  rcases lt_trichotomy t j with ht | rfl | ht
  · rw [if_neg (by omega : ¬t + 1 = j + 1), if_neg (by omega : ¬j + 1 < t + 1),
      if_pos ht]
    rw [show (j : ℤ) - t = ((j - 1 - t : ℕ) + 1 : ℤ) by omega,
      hypOscillator_positive_apply]
    simp only [mul_zero, zero_add, smul_smul]
    congr 1
    have hc : ((j - 1 - t : ℕ) + 1 : ℂ) = (j : ℂ) - t := by
      have hn : j - 1 - t + 1 + t = j := by omega
      have hc := congrArg (fun n : ℕ => (n : ℂ)) hn
      push_cast at hc
      linear_combination hc
    rw [hc]
  · simp only [if_true, lt_self_iff_false, if_false, sub_self, add_zero,
      hypOscillator_zero, LinearMap.smul_apply, LinearMap.id_apply]
    simp only [smul_eq_C_mul]
    ring
  · rw [if_neg (by omega : ¬t + 1 = j + 1), if_pos (by omega : j + 1 < t + 1),
      if_neg (by omega : ¬t < j)]
    rw [show (j : ℤ) - t = -((t - (j + 1) : ℕ) + 1 : ℤ) by omega,
      hypOscillator_negative_apply]
    simp only [add_zero, smul_eq_C_mul]
    ring

end VOA.Moonshine.ConwayNorton
