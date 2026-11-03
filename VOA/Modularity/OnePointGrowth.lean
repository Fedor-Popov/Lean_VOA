/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modularity.AnalyticBlock

/-!
# The general-`v` growth datum is a statement about a spanning set

`Modularity.AnalyticBlock` consumes `OnePointSubexp N h` — subexponential growth of the
coefficients of `𝒵_M(v; q)` for **every** `v`.  When this file was written the repo's growth theorem
(`Modularity.BuhlSpanningC2.subexponentialCoeffs_adjoint_of_C2Cofinite`) covered only `v = 𝟙`; the
every-`v` statement is `onePointSubexp_of_c2` (`Modularity/BlockGrowth.lean`).

The gap is smaller than it looks: `v ↦ 𝒵_M(v; q)` is **linear**, `Subexponential` is closed under
sums and scalar multiples, and every `v` is a *finite* combination of elements of any spanning set.
So:

  `onePointSubexp_of_spanning` — the growth datum on any spanning set (for instance Buhl's
  ordered monomials, or the homogeneous vectors) already gives it for all `v`.

## Status
Proved, axiom-clean, `pbw`-free, no `sorry`.
-/

namespace VOA

open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## `Subexponential` is a linear condition -/

/-- Sums of subexponential sequences are subexponential. -/
theorem Subexponential.add {a b : ℕ → ℝ} (ha : Subexponential a) (hb : Subexponential b) :
    Subexponential (fun n => a n + b n) := fun r hr => by
  obtain ⟨C₁, hC₁⟩ := ha r hr
  obtain ⟨C₂, hC₂⟩ := hb r hr
  refine ⟨C₁ + C₂, fun n => ?_⟩
  calc a n + b n ≤ C₁ * r ^ n + C₂ * r ^ n := add_le_add (hC₁ n) (hC₂ n)
    _ = (C₁ + C₂) * r ^ n := by ring

/-- The zero sequence is subexponential. -/
theorem subexponential_zero : Subexponential (fun _ : ℕ => (0 : ℝ)) := subexponential_const 0

section

variable {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- **The growth datum only has to be checked on a spanning set.**  `𝒵_M(·; q)` is linear and
`Subexponential` is closed under sums and scalar multiples, so subexponential growth on a set
spanning `𝒱` propagates to all of `𝒱`. -/
theorem onePointSubexp_of_spanning (N : OrdVModule W M) (h : ℂ) (S : Set 𝒱)
    (hspan : Submodule.span ℂ S = ⊤)
    (hS : ∀ s ∈ S, Subexponential (fun n : ℕ => ‖torusOnePoint N s (h + (n : ℂ))‖)) :
    OnePointSubexp N h := by
  intro v
  have hv : v ∈ Submodule.span ℂ S := by rw [hspan]; trivial
  induction hv using Submodule.span_induction with
  | mem s hs => exact hS s hs
  | zero =>
      refine Subexponential.of_le (fun n => ?_) subexponential_zero
      rw [torusOnePoint_zero]
      simp
  | add x y _ _ ihx ihy =>
      refine Subexponential.of_le (fun n => ?_) (ihx.add ihy)
      rw [torusOnePoint_add]
      exact norm_add_le _ _
  | smul c x _ ihx =>
      refine Subexponential.of_le (fun n => ?_) (ihx.const_mul (norm_nonneg c))
      rw [torusOnePoint_smul]
      simp only [Pi.smul_apply, smul_eq_mul, norm_mul]
      exact le_refl _

/-- The homogeneous vectors are a spanning set, so the growth datum may be checked on them. -/
theorem onePointSubexp_of_homog (N : OrdVModule W M) (h : ℂ)
    (hS : ∀ s : 𝒱, IsHomog W s → Subexponential (fun n : ℕ => ‖torusOnePoint N s (h + (n : ℂ))‖)) :
    OnePointSubexp N h :=
  onePointSubexp_of_spanning N h {y : 𝒱 | IsHomog W y} (span_homog_eq_top W) (fun s hs => hS s hs)

end

end VOA
