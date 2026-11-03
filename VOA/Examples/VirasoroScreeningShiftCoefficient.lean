/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroFockShiftSum
import VOA.Examples.VirasoroScreeningMigration

/-!
# Actual screening coefficients under the shift derivation

Homogeneity bounds all oscillator indices. The actual shift derivation
therefore has a finite sum, and each term is evaluated by the proved
factorial cancellation. The resulting scalar is the finite power-sum
chain-rule expression needed for the auxiliary residue Ward identities.
-/
namespace VOA.VirasoroScreening
open HeisenbergN MvPolynomial
open scoped BigOperators

/-- Every variable occurring in the actual screening polynomial has index
strictly below its total energy. This also handles the zero-energy case. -/
theorem screeningFockState_vars_lt (r s t : ℕ) (β : ℚ)
    (v : ℕ × Fin 1) (hv : v ∈ (screeningFockState r s t β).vars) : v.1 < r*s := by
  obtain ⟨d,hd,hvd⟩ := (MvPolynomial.mem_vars_iff_mem_support _).mp hv
  have hw := (screeningFockState_mem_grade r s t β)
    (MvPolynomial.mem_support_iff.mp hd)
  exact weightDegSetN_support_lt hw (Finsupp.mem_support_iff.mp hvd)

/-- The exact coefficient of the actual shift part of a positive Virasoro
mode. Every sum is finite, and the total output energy is explicitly fixed. -/
theorem screeningFockState_shift_coeff (r s t n : ℕ) (β : ℚ) (d : ℕ →₀ ℕ)
    (hd : Finsupp.weight (fun k => k+1) d + n = r*s) :
    coeff (fockOccupation d) (fockShiftDerivation n (screeningFockState r s t β)) =
      ((screeningPrefactor β d * ∑ i ∈ Finset.range (r*s),
        ((i+1:ℕ):ℚ) * (d i:ℚ) * screeningMoment r s t
          (powerSumSubstitution (Fin r) (monomial
            (d - Finsupp.single i 1 + Finsupp.single (i+n) 1) 1))) : ℂ) := by
  classical
  rw [fockShiftDerivation_eq_sum n (r*s) _ (screeningFockState_vars_lt r s t β)]
  simp only [coeff_sum, coeff_smul, smul_eq_mul, Rat.cast_mul, Rat.cast_sum,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hdi : d i=0
  · rw [screeningFockState_migration_coeff_zero r s t β d i (i+n) hdi]
    simp [hdi]
  · have hpos : 0<d i := Nat.pos_of_ne_zero hdi
    have hw : Finsupp.weight (fun k => k+1) (d - Finsupp.single i 1) + (i+n+1) = r*s := by
      have he := Finsupp.weight_sub_single_add (w := fun k : ℕ => k+1) hdi
      dsimp only at he
      omega
    rw [screeningFockState_migration_coeff r s t β d i (i+n) hpos hw]
    push_cast
    ring

end VOA.VirasoroScreening
