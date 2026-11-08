import VOA.Moonshine.MoonshineCNHyperbolicSugawara
import Mathlib.RingTheory.Derivation.Lie

/-! # Differential identities for the negative hyperbolic modes

These identities concern the actual polynomial operators, at arbitrary
momentum. They require no Virasoro representation or splitting hypothesis.
-/

noncomputable section

namespace VOA.Moonshine.ConwayNorton

open MvPolynomial
open scoped BigOperators

theorem hypNegativePotential_pderiv_b (κ ell : ℂ) (j t : ℕ) :
    pderiv (t, 1) (hypNegativePotential κ ell j) =
      (if t = j then MvPolynomial.C κ else 0) +
        (if t < j then X (j - 1 - t, 0) else 0) := by
  classical
  have hs : (∑ k ∈ Finset.range j,
      pderiv (t, 1) (X (j - 1 - k, 0) * X (k, 1) : hypFock)) =
      if t < j then X (j - 1 - t, 0) else 0 := by
    simp only [pderiv_mul, pderiv_X, Pi.single_apply, Prod.mk.injEq,
      show (0 : Fin 2) ≠ 1 by decide, and_false, if_false, zero_mul, zero_add,
      and_true]
    simp [Finset.sum_ite_eq', Finset.mem_range, mul_ite]
  rw [hypNegativePotential, map_add, map_add, Derivation.map_smul, Derivation.map_smul,
    map_sum, hs]
  simp [pderiv_X, Pi.single_apply, smul_eq_C_mul, eq_comm]

theorem hypNegativePotential_pderiv_a (κ ell : ℂ) (j t : ℕ) :
    pderiv (t, 0) (hypNegativePotential κ ell j) =
      (if t = j then MvPolynomial.C ell else 0) +
        (if t < j then X (j - 1 - t, 1) else 0) := by
  classical
  have hs : (∑ k ∈ Finset.range j,
      pderiv (t, 0) (X (j - 1 - k, 0) * X (k, 1) : hypFock)) =
      if t < j then X (j - 1 - t, 1) else 0 := by
    simp only [pderiv_mul, pderiv_X, Pi.single_apply, Prod.mk.injEq,
      show (1 : Fin 2) ≠ 0 by decide, and_false, if_false, mul_zero, add_zero,
      and_true]
    by_cases ht : t < j
    · rw [if_pos ht]
      rw [Finset.sum_eq_single (j - 1 - t)]
      · have he : j - 1 - (j - 1 - t) = t := by omega
        simp [he]
      · intro k hk hkt
        have hk' : k < j := Finset.mem_range.mp hk
        have he : j - 1 - k ≠ t := by omega
        simp [he]
      · intro h
        exact (h (Finset.mem_range.mpr (by omega))).elim
    · rw [if_neg ht]
      apply Finset.sum_eq_zero
      intro k hk
      have hk' : k < j := Finset.mem_range.mp hk
      have he : j - 1 - k ≠ t := by omega
      simp [he]
  rw [hypNegativePotential, map_add, map_add, Derivation.map_smul, Derivation.map_smul,
    map_sum, hs]
  simp [pderiv_X, Pi.single_apply, smul_eq_C_mul, eq_comm]

theorem hypNegativePotential_pderiv (κ ell : ℂ) (j t : ℕ) (a : Fin 2) :
    pderiv (t, a.rev) (hypNegativePotential κ ell j) =
      (if t = j then MvPolynomial.C (if a = 0 then κ else ell) else 0) +
        (if t < j then X (j - 1 - t, a) else 0) := by
  fin_cases a
  · simpa using hypNegativePotential_pderiv_b κ ell j t
  · simpa using hypNegativePotential_pderiv_a κ ell j t

theorem hypRaisingDerivation_pderiv_comm (n t : ℕ) (a : Fin 2) :
    ⁅hypRaisingDerivation n, (pderiv (t, a) : Derivation ℂ hypFock hypFock)⁆ =
      if n ≤ t then -(((t - n : ℕ) + 1 : ℂ)) • pderiv (t - n, a) else 0 := by
  classical
  apply derivation_ext
  rintro ⟨s, b⟩
  rw [Derivation.commutator_apply, hypRaisingDerivation_X, Derivation.map_smul]
  simp only [pderiv_X, Pi.single_apply, Prod.mk.injEq]
  have hz : hypRaisingDerivation n (if (s = t ∧ b = a) then 1 else 0) = 0 := by
    split <;> simp
  rw [hz]
  by_cases ht : n ≤ t
  · rw [if_pos ht]
    simp only [Derivation.smul_apply, pderiv_X, Pi.single_apply, Prod.mk.injEq]
    by_cases h : s + n = t ∧ b = a
    · have hs : s = t - n := by omega
      simp [h, hs, Nat.sub_add_cancel ht, smul_eq_C_mul, map_neg, map_add]
    · have h' : ¬(s = t - n ∧ b = a) := by omega
      simp [h, h']
  · rw [if_neg ht]
    have h : ¬(s + n = t ∧ b = a) := by omega
    simp [h]

theorem hypSugawara_negative_pderiv (κ ell : ℂ) (j t : ℕ)
    (a : Fin 2) (p : hypFock) :
    hypSugawara κ ell (-(j + 1 : ℤ)) (pderiv (t, a.rev) p) -
      pderiv (t, a.rev) (hypSugawara κ ell (-(j + 1 : ℤ)) p) =
      -(pderiv (t, a.rev) (hypNegativePotential κ ell j) * p) +
        (if j + 1 ≤ t then -(((t - (j + 1) : ℕ) + 1 : ℂ)) •
          pderiv (t - (j + 1), a.rev) p else 0) := by
  have hd := congrArg (fun D : Derivation ℂ hypFock hypFock => D p)
    (hypRaisingDerivation_pderiv_comm (j + 1) t a.rev)
  simp only [Derivation.commutator_apply] at hd
  rw [hypSugawara_negative, hypSugawara_negative, map_add, pderiv_mul]
  have hd' : hypRaisingDerivation (j + 1) (pderiv (t, a.rev) p) -
      pderiv (t, a.rev) (hypRaisingDerivation (j + 1) p) =
      if j + 1 ≤ t then -(((t - (j + 1) : ℕ) + 1 : ℂ)) •
        pderiv (t - (j + 1), a.rev) p else 0 := by
    by_cases h : j + 1 ≤ t <;> simpa [h] using hd
  rw [← hd']
  ring

/-- Every negative Sugawara mode has the required commutator with every
signed oscillator, including its scalar zero mode. -/
theorem hypSugawara_negative_oscillator_comm (κ ell : ℂ) (j : ℕ)
    (a : Fin 2) (n : ℤ) :
    ⁅hypSugawara κ ell (-(j + 1 : ℤ)),
      hypOscillator a (if a = 0 then κ else ell) n⁆ =
      -(n : ℂ) • hypOscillator a (if a = 0 then κ else ell) (n - (j + 1)) := by
  apply LinearMap.ext
  intro p
  simp only [Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply,
    LinearMap.smul_apply]
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · obtain ⟨t, rfl⟩ : ∃ t : ℕ, n = -(t + 1 : ℤ) := ⟨(-n - 1).toNat, by omega⟩
    rw [hypOscillator_negative_apply, hypOscillator_negative_apply,
      hypSugawara_negative_mul_variable]
    rw [show -(t + 1 : ℤ) - (j + 1) = -((t + (j + 1) : ℕ) + 1 : ℤ) by omega,
      hypOscillator_negative_apply]
    simp
  · simp only [hypOscillator_zero, LinearMap.smul_apply, LinearMap.id_apply,
      map_smul, sub_self, Int.cast_zero, neg_zero, zero_smul]
  · obtain ⟨t, rfl⟩ : ∃ t : ℕ, n = (t + 1 : ℤ) := ⟨(n - 1).toNat, by omega⟩
    rw [hypOscillator_positive_apply, hypOscillator_positive_apply, map_smul,
      ← smul_sub, hypSugawara_negative_pderiv, hypNegativePotential_pderiv]
    rcases lt_trichotomy t j with ht | rfl | ht
    · rw [if_neg (by omega : t ≠ j), if_pos ht, if_neg (by omega : ¬j + 1 ≤ t)]
      rw [show (t + 1 : ℤ) - (j + 1) = -((j - 1 - t : ℕ) + 1 : ℤ) by omega,
        hypOscillator_negative_apply]
      simp only [zero_add, add_zero, smul_neg, Int.cast_add, Int.cast_natCast,
        Int.cast_one, neg_smul]
    · simp only [lt_self_iff_false, if_true, if_false, Nat.not_succ_le_self,
        add_zero, sub_self, hypOscillator_zero, LinearMap.smul_apply,
        LinearMap.id_apply, smul_neg, Int.cast_add, Int.cast_natCast, Int.cast_one]
      simp [smul_eq_C_mul, map_neg, map_add]
      split_ifs <;> ring
    · rw [if_neg (by omega : t ≠ j), if_neg (by omega : ¬t < j),
        if_pos (by omega : j + 1 ≤ t)]
      rw [show (t + 1 : ℤ) - (j + 1) = ((t - (j + 1) : ℕ) + 1 : ℤ) by omega,
        hypOscillator_positive_apply]
      simp only [zero_add, zero_mul, neg_zero, smul_smul, Int.cast_add,
        Int.cast_natCast, Int.cast_one]
      congr 1
      ring

end VOA.Moonshine.ConwayNorton
