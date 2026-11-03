import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Cyclotomic integrality of traces of finite-order operators

This is the linear-algebra part of cyclotomicity of Frobenius–Schur indicators.
It does not assume diagonalizability, and proves membership in the cyclotomic
integer ring, rather than merely in the cyclotomic field.
-/

noncomputable section

namespace VOA.Huang.NgSchauenburg

variable {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]

omit [FiniteDimensional ℂ W] in
/-- An eigenvalue of an operator annihilated by `X^n - 1` is an `n`-th root of unity. -/
theorem eigenvalue_pow_eq_one (E : Module.End ℂ W) {n : ℕ} (hE : E ^ n = 1)
    {z : ℂ} (hz : E.HasEigenvalue z) : z ^ n = 1 := by
  obtain ⟨w, hw⟩ := hz.exists_hasEigenvector
  have h := hw.pow_apply n
  rw [hE, Module.End.one_apply] at h
  exact (smul_left_injective ℂ hw.2) (h.symm.trans (one_smul ℂ w).symm)

/-- Trace of a finite-order complex operator lies in `ℤ[ζ]` for any primitive
`n`-th root `ζ`. The hypothesis `E^n = 1` is explicit. -/
theorem trace_mem_cyclotomicIntegers (E : Module.End ℂ W) {n : ℕ} (hn : 0 < n)
    (hE : E ^ n = 1) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ n) :
    LinearMap.trace ℂ W E ∈ Algebra.adjoin ℤ ({ζ} : Set ℂ) := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  rw [Module.End.trace_eq_sum_roots_charpoly_of_splits (IsAlgClosed.splits E.charpoly)]
  apply Subalgebra.multiset_sum_mem
  intro z hz
  have he : E.HasEigenvalue z :=
    (Module.End.hasEigenvalue_iff_isRoot_charpoly E z).mpr
      ((Polynomial.mem_roots E.charpoly_monic.ne_zero).mp hz)
  obtain ⟨k, _, hk⟩ := hζ.eq_pow_of_pow_eq_one (eigenvalue_pow_eq_one E hE he)
  rw [← hk]
  exact Subalgebra.pow_mem _ (Algebra.self_mem_adjoin_singleton ℤ ζ) k

/-- The standard root `exp(2πi/n)` version. -/
theorem trace_mem_standardCyclotomicIntegers (E : Module.End ℂ W) {n : ℕ}
    (hn : 0 < n) (hE : E ^ n = 1) :
    LinearMap.trace ℂ W E ∈
      Algebra.adjoin ℤ ({Complex.exp (2 * Real.pi * Complex.I / n)} : Set ℂ) :=
  trace_mem_cyclotomicIntegers E hn hE
    (Complex.isPrimitiveRoot_exp n (Nat.ne_of_gt hn))

end VOA.Huang.NgSchauenburg
