import VOA.Huang.NSCongruenceCyclotomic
import VOA.Huang.NgSchauenburgRotationOrder
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra

/-! # Field operations in the specified cyclotomic subalgebra

The positive-order subalgebra `cycloField N` is the underlying subalgebra of
an intermediate field. This justifies inverse closure without changing the
meaning of cyclotomic membership in the congruence contracts.
-/
noncomputable section
set_option maxSynthPendingDepth 3
namespace VOA.Huang.NSCongruence
open VOA.Huang.NgSchauenburg

theorem cycloField_eq_intermediateField (N : ℕ) (hN : 0 < N) :
    cycloField N = (IntermediateField.adjoin ℚ
      ({Complex.exp (2 * Real.pi * Complex.I / N)} : Set ℂ)).toSubalgebra := by
  symm
  apply IntermediateField.adjoin_toSubalgebra_of_isAlgebraic
  rintro x (rfl : x = _)
  apply IsIntegral.isAlgebraic
  apply IsIntegral.of_pow (n := N) hN
  rw [(Complex.isPrimitiveRoot_exp N hN.ne').pow_eq_one]
  exact isIntegral_one

theorem cycloField_inv_mem {N : ℕ} (hN : 0 < N) {x : ℂ}
    (hx : x ∈ cycloField N) : x⁻¹ ∈ cycloField N := by
  rw [cycloField_eq_intermediateField N hN] at hx ⊢
  exact IntermediateField.inv_mem _ hx

theorem cycloField_div_mem {N : ℕ} (hN : 0 < N) {x y : ℂ}
    (hx : x ∈ cycloField N) (hy : y ∈ cycloField N) : x / y ∈ cycloField N := by
  rw [div_eq_mul_inv]
  exact (cycloField N).mul_mem hx (cycloField_inv_mem hN hy)

set_option maxHeartbeats 800000 in
-- Restriction of scalars through the integer/rational algebra tower needs extra elaboration fuel.
theorem cyclotomicIntegers_le_cycloField (N : ℕ) :
    Algebra.adjoin ℤ ({Complex.exp (2 * Real.pi * Complex.I / N)} : Set ℂ) ≤
      (cycloField N).restrictScalars ℤ := by
  apply Algebra.adjoin_le
  intro x hx
  exact Algebra.subset_adjoin hx

theorem trace_mem_cycloField {W : Type*} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (E : Module.End ℂ W) {N : ℕ} (hN : 0 < N)
    (hE : E ^ N = 1) : LinearMap.trace ℂ W E ∈ cycloField N :=
  cyclotomicIntegers_le_cycloField N (trace_mem_standardCyclotomicIntegers E hN hE)

end VOA.Huang.NSCongruence
