/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroFockPositiveOperators

/-!
# A finite sum for the actual energy-shift derivation

Every polynomial involves finitely many oscillator variables. Below any
bound containing those variables, the shift derivation is exactly the
finite sum of a derivative followed by multiplication by the lower-energy
oscillator. This permits coefficient extraction without an infinite sum.
-/
namespace VOA.VirasoroScreening
open HeisenbergN MvPolynomial
open scoped BigOperators

/-- On a polynomial whose variables lie below K, the energy-shift
operator is a finite sum of oscillator migrations. The index i refers to
the output oscillator, so the differentiated input has index i+n. -/
theorem fockShiftDerivation_eq_sum (n K : ℕ) (P : FockN 1)
    (hK : ∀ v ∈ P.vars, v.1 < K) :
    fockShiftDerivation n P =
      ∑ i ∈ Finset.range K, ((i+n+1:ℕ):ℂ) •
        (X (i,0) * pderiv (i+n,0) P) := by
  classical
  let D : Derivation ℂ (FockN 1) (FockN 1) :=
    ∑ i ∈ Finset.range K, (((i+n+1:ℕ):ℂ) • (X (i,0) : FockN 1)) •
      (pderiv (i+n,0) : Derivation ℂ (FockN 1) (FockN 1))
  have hD (Q : FockN 1) : D Q = ∑ i ∈ Finset.range K,
      (((i+n+1:ℕ):ℂ) • X (i,0)) * pderiv (i+n,0) Q := by
    change (Derivation.coeFnAddMonoidHom D) Q = _
    dsimp only [D]
    rw [map_sum]
    simp only [Finset.sum_apply, Derivation.coeFnAddMonoidHom_apply,
      Derivation.smul_apply, smul_eq_mul]
  have he : fockShiftDerivation n P = D P := by
    apply derivation_eq_of_forall_mem_vars
    rintro ⟨j,a⟩ hj
    have ha : a=0 := Subsingleton.elim _ _
    subst a
    rw [fockShiftDerivation_X]
    rw [hD]
    by_cases hn : n ≤ j
    · rw [if_pos hn]
      symm
      rw [Finset.sum_eq_single (j-n)]
      · have hjn : j-n+n=j := Nat.sub_add_cancel hn
        simp [hjn]
      · intro i hi hne
        have hij : i+n ≠ j := by omega
        simp [MvPolynomial.pderiv_X, hij, Ne.symm hij]
      · intro hnot
        exact False.elim (hnot (Finset.mem_range.mpr (by have := hK (j,0) hj; omega)))
    · rw [if_neg hn]
      symm
      apply Finset.sum_eq_zero
      intro i hi
      have hij : i+n ≠ j := by omega
      simp [MvPolynomial.pderiv_X, hij, Ne.symm hij]
  rw [he]
  rw [hD]
  apply Finset.sum_congr rfl
  intro i hi
  exact smul_mul_assoc _ _ _

end VOA.VirasoroScreening
