import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

/-! # Euler dimensions of a finite exact resolution

The alternating formula is derived from actual kernels and ranges. No character
formula is assumed here. The terminal differential must vanish in the degree in
which this theorem is used.
-/

namespace VOA.FiniteResolution
open scoped BigOperators

theorem alternating_telescope (r : ℕ → ℚ) (n : ℕ) :
    (∑ i ∈ Finset.range n, (-1 : ℚ)^i * (r i + r (i+1))) =
      r 0 - (-1 : ℚ)^n * r n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    ring

variable {K : Type*} [Field K]
variable {E : ℕ → Type*} [∀ i, AddCommGroup (E i)] [∀ i, Module K (E i)]
variable [∀ i, FiniteDimensional K (E i)]
variable {B : Type*} [AddCommGroup B] [Module K B] [FiniteDimensional K B]

/-- The alternating dimension of a genuinely exact finite resolution is the
dimension of its augmentation target. -/
theorem finrank_eq_alternating_sum
    (d : ∀ i, E (i+1) →ₗ[K] E i) (ε : E 0 →ₗ[K] B)
    (hε : Function.Surjective ε)
    (hfirst : LinearMap.range (d 0) = LinearMap.ker ε)
    (hexact : ∀ i, LinearMap.range (d (i+1)) = LinearMap.ker (d i))
    (N : ℕ) (hlast : d N = 0) :
    (Module.finrank K B : ℚ) =
      ∑ i ∈ Finset.range (N+1), (-1 : ℚ)^i * (Module.finrank K (E i) : ℚ) := by
  let r : ℕ → ℚ := fun i => match i with
    | 0 => (Module.finrank K B : ℚ)
    | j+1 => (Module.finrank K (LinearMap.range (d j)) : ℚ)
  have hr : ∀ i, (Module.finrank K (E i) : ℚ) = r i + r (i+1) := by
    intro i
    cases i with
    | zero =>
      have h := ε.finrank_range_add_finrank_ker
      rw [LinearMap.range_eq_top.mpr hε, finrank_top, ← hfirst] at h
      dsimp only [r]
      exact_mod_cast h.symm
    | succ i =>
      have h := (d i).finrank_range_add_finrank_ker
      rw [← hexact i] at h
      dsimp only [r]
      exact_mod_cast h.symm
  have hzero : r (N+1) = 0 := by simp [r, hlast]
  symm
  simp_rw [hr]
  rw [alternating_telescope, hzero, mul_zero, sub_zero]

end VOA.FiniteResolution
