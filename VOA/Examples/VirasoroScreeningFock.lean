/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroScreeningCoefficient
import VOA.Examples.HeisenbergNVertex

/-!
# The finite, nonzero screening state in the actual rank-one Fock space

The coefficient of an oscillator monomial is its finite power-sum residue,
multiplied by the exponential's beta powers, mode denominators and factorials.
Only occupations of weight rs are used, so the definition is a finite sum in
the existing Fock carrier. The nonzero rational residue proved earlier survives
these nonzero prefactors and passage to complex coefficients. This module does
not assert the positive-mode Ward equations.
-/
namespace VOA.VirasoroScreening
open scoped BigOperators
open HeisenbergN

/-- Put an ordinary oscillator occupation into the single Fock colour. -/
noncomputable def fockOccupation (d : ℕ →₀ ℕ) : (ℕ × Fin 1) →₀ ℕ :=
  d.mapDomain (fun i => (i, 0))

/-- Forget the unique colour of a rank-one oscillator occupation. -/
noncomputable def plainOccupation (d : (ℕ × Fin 1) →₀ ℕ) : ℕ →₀ ℕ :=
  d.mapDomain Prod.fst

/-- Forgetting the colour recovers the original occupation exactly. -/
theorem plain_fockOccupation (d : ℕ →₀ ℕ) :
    plainOccupation (fockOccupation d) = d := by
  simp only [plainOccupation, fockOccupation, ← Finsupp.mapDomain_comp]
  exact Finsupp.mapDomain_id

/-- Adding the unique colour preserves the oscillator energy. -/
theorem fockOccupation_weight (d : ℕ →₀ ℕ) :
    Finsupp.weight weightFnN (fockOccupation d) = Finsupp.weight (fun i => i+1) d := by
  induction d using Finsupp.induction_linear with
  | zero => simp [fockOccupation]
  | add d e hd he => simpa [fockOccupation, Finsupp.mapDomain_add] using congrArg₂ (· + ·) hd he
  | single i n => simp [fockOccupation, Finsupp.weight_single, weightFnN]

/-- The exact rational exponential prefactor. Each occurrence of mode i+1
contributes beta/(i+1), and repeated occurrences contribute an inverse factorial. -/
noncomputable def screeningPrefactor (β : ℚ) (d : ℕ →₀ ℕ) : ℚ :=
  β ^ (d.sum fun _ n => n) /
    ∏ i ∈ d.support, ((i+1 : ℕ) : ℚ) ^ d i * (Nat.factorial (d i) : ℚ)

/-- All exponential prefactors are nonzero whenever beta is nonzero. -/
theorem screeningPrefactor_ne_zero {β : ℚ} (hβ : β ≠ 0) (d : ℕ →₀ ℕ) :
    screeningPrefactor β d ≠ 0 := by
  classical
  apply div_ne_zero (pow_ne_zero _ hβ)
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  exact mul_ne_zero (pow_ne_zero _ (by positivity)) (by positivity)

/-- The coefficient assigned to one oscillator occupation, before complexification. -/
noncomputable def screeningFockCoefficient (r s t : ℕ) (β : ℚ) (d : ℕ →₀ ℕ) : ℚ :=
  screeningPrefactor β d * screeningMoment r s t
    (powerSumSubstitution (Fin r) (MvPolynomial.monomial d 1))

/-- The actual finite screening polynomial in the existing complex rank-one
Fock space. Finiteness follows from the already established energy grading. -/
noncomputable def screeningFockState (r s t : ℕ) (β : ℚ) : FockN 1 :=
  ∑ d ∈ (weightDegSetN_finite 1 (r * s)).toFinset,
    MvPolynomial.monomial d (screeningFockCoefficient r s t β (plainOccupation d) : ℂ)

/-- At an occupation of the prescribed weight, the actual Fock coefficient
is exactly the proposed finite residue with its exponential prefactor. -/
theorem screeningFockState_coeff (r s t : ℕ) (β : ℚ)
    (d : (ℕ × Fin 1) →₀ ℕ) (hd : Finsupp.weight weightFnN d = r * s) :
    MvPolynomial.coeff d (screeningFockState r s t β) =
      (screeningFockCoefficient r s t β (plainOccupation d) : ℂ) := by
  classical
  simp only [screeningFockState, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  rw [Finset.sum_eq_single d]
  · simp
  · intro b hb hbd
    simp [hbd]
  · intro h
    exact False.elim (h ((weightDegSetN_finite 1 (r * s)).mem_toFinset.mpr hd))

/-- The actual screening polynomial is homogeneous of energy rs. -/
theorem screeningFockState_mem_grade (r s t : ℕ) (β : ℚ) :
    screeningFockState r s t β ∈ gradingWN 1 (r * s) := by
  classical
  apply Submodule.sum_mem
  intro d hd
  rw [mem_gradingWN]
  apply MvPolynomial.isWeightedHomogeneous_monomial
  exact (weightDegSetN_finite 1 (r * s)).mem_toFinset.mp hd

/-- The finite screening polynomial is genuinely nonzero for every rank,
label and natural screening power, provided beta is nonzero. This is a state
nonvanishing theorem, not yet a singular-vector theorem. -/
theorem screeningFockState_ne_zero (r s t : ℕ) {β : ℚ} (hβ : β ≠ 0) :
    screeningFockState r s t β ≠ 0 := by
  obtain ⟨d, hd, hn⟩ := screening_nonzero_monomial r s t
  have hc := screeningFockState_coeff r s t β (fockOccupation d)
    ((fockOccupation_weight d).trans hd)
  rw [plain_fockOccupation] at hc
  intro hz
  rw [hz, MvPolynomial.coeff_zero] at hc
  have hq : screeningFockCoefficient r s t β d ≠ 0 :=
    mul_ne_zero (screeningPrefactor_ne_zero hβ d) hn
  exact hq (by exact_mod_cast hc.symm)

end VOA.VirasoroScreening
