/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Foundations.LatticeCocycle
import Mathlib.Tactic.LinearCombination

/-!
# The cocycle-twisted group algebra `ℂ_ε{L}`  (FLM Ch. 8; Gannon §5.2.2)

The charge lattice of the general lattice VOA `V_L` is the **twisted group algebra** `ℂ_ε{L}`:
the ℂ-vector space `ℂ{L}` (`= L.carrier →₀ ℂ`) with the cocycle-deformed product
`eᵅ ⋆ eᵝ = ε(α,β) e^{α+β}`, where `ε = latticeCocycle L` is the FLM 2-cocycle
(`Foundations.LatticeCocycle`).  This file builds that product `twMul` and proves its structural
laws directly from the cocycle:

* **`twMul_e`** — the defining law `eᵅ ⋆ eᵝ = ε(α,β) • e^{α+β}` (`eᵅ = latticeAlgebra.e α`).
* **bi-`ℂ`-linearity** (`twMul_add_left`/`_right`, `twMul_smul_left`/`_right`,
  `twMul_zero_left`/`_right`) — immediate: `twMul` is packaged as the `ℂ`-bilinear `twMulL`.
* **`twMul_assoc`** — **associativity** `(f ⋆ g) ⋆ h = f ⋆ (g ⋆ h)`, from the 2-cocycle law
  `latticeCocycle_cocycleLaw` (via triple `Finsupp.induction_linear`; the single-single-single
  case is exactly the cocycle identity).
* **`one_twMul`/`twMul_one`** — `e⁰` is a two-sided unit (from `ε(0,·) = ε(·,0) = 1`).

We keep the twisted product as an explicit operation on `L.carrier →₀ ℂ` (rather than a competing
`Ring` instance, which would clash with the untwisted `AddMonoidAlgebra` ring on the same carrier);
the lattice VOA consumes `ε` as operator scalars and this product as the charge-fusion law.

## References
* Frenkel–Lepowsky–Meurman, *Vertex Operator Algebras and the Monster*, Ch. 8; Gannon §5.2.2.
-/

namespace VOA.IntegralLattice

open scoped BigOperators

variable (L : IntegralLattice)

/-- `eᵅ` as a raw `Finsupp` (defeq to `latticeAlgebra.e α`). -/
theorem e_eq_single (α : L.carrier) :
    (latticeAlgebra.e α : L.carrier →₀ ℂ) = Finsupp.single α (1 : ℂ) := rfl

/-- For a fixed `α`, the `ℂ`-linear "left-multiply by `eᵅ`" operator
`g ↦ ∑_β g(β) ε(α,β) e^{α+β}`. -/
noncomputable def twMulInner (α : L.carrier) : (L.carrier →₀ ℂ) →ₗ[ℂ] (L.carrier →₀ ℂ) :=
  Finsupp.lsum ℂ fun β => LinearMap.toSpanSingleton ℂ (L.carrier →₀ ℂ)
    (latticeCocycle L α β • Finsupp.single (α + β) (1 : ℂ))

/-- The **cocycle-twisted product** on `ℂ{L}`, as a `ℂ`-bilinear map. -/
noncomputable def twMulL : (L.carrier →₀ ℂ) →ₗ[ℂ] (L.carrier →₀ ℂ) →ₗ[ℂ] (L.carrier →₀ ℂ) :=
  Finsupp.lsum ℂ fun α => LinearMap.toSpanSingleton ℂ ((L.carrier →₀ ℂ) →ₗ[ℂ] (L.carrier →₀ ℂ))
    (twMulInner L α)

/-- The twisted product `f ⋆ g = ∑_{α,β} f(α) g(β) ε(α,β) e^{α+β}`. -/
noncomputable def twMul (f g : L.carrier →₀ ℂ) : L.carrier →₀ ℂ := twMulL L f g

theorem twMulInner_single (α β : L.carrier) (b : ℂ) :
    twMulInner L α (Finsupp.single β b)
      = b • (latticeCocycle L α β • Finsupp.single (α + β) (1 : ℂ)) := by
  rw [twMulInner, Finsupp.lsum_single, LinearMap.toSpanSingleton_apply]

theorem twMulL_single (α : L.carrier) (a : ℂ) :
    twMulL L (Finsupp.single α a) = a • twMulInner L α := by
  rw [twMulL, Finsupp.lsum_single, LinearMap.toSpanSingleton_apply]

/-- The single-single product `single α a ⋆ single β b = single (α+β) (a b ε(α,β))`. -/
theorem twMul_single_single (α β : L.carrier) (a b : ℂ) :
    twMul L (Finsupp.single α a) (Finsupp.single β b)
      = Finsupp.single (α + β) (a * b * latticeCocycle L α β) := by
  rw [twMul, twMulL_single, LinearMap.smul_apply, twMulInner_single, smul_smul, smul_smul,
    Finsupp.smul_single, smul_eq_mul]
  congr 1
  ring

/-- The generator law in `e`-form: `eᵅ ⋆ eᵝ = e^{α+β}` scaled by `ε(α,β)` — i.e. the twisted
product `single α 1 ⋆ single β 1 = single (α+β) ε(α,β)` (the `a = b = 1` case of
`twMul_single_single`; `latticeAlgebra.e γ = single γ 1`). -/
theorem twMul_e (α β : L.carrier) :
    twMul L (latticeAlgebra.e α) (latticeAlgebra.e β)
      = Finsupp.single (α + β) (latticeCocycle L α β) := by
  have h := twMul_single_single L α β 1 1
  rw [one_mul, one_mul] at h
  rw [e_eq_single, e_eq_single, h]

/-! ## Bi-`ℂ`-linearity (free, from `twMulL` being a bilinear map) -/

@[simp] theorem twMul_zero_left (g : L.carrier →₀ ℂ) : twMul L 0 g = 0 := by
  simp only [twMul, map_zero, LinearMap.zero_apply]

@[simp] theorem twMul_zero_right (f : L.carrier →₀ ℂ) : twMul L f 0 = 0 := by
  simp only [twMul, map_zero]

theorem twMul_add_left (f₁ f₂ g : L.carrier →₀ ℂ) :
    twMul L (f₁ + f₂) g = twMul L f₁ g + twMul L f₂ g := by
  simp only [twMul, map_add, LinearMap.add_apply]

theorem twMul_add_right (f g₁ g₂ : L.carrier →₀ ℂ) :
    twMul L f (g₁ + g₂) = twMul L f g₁ + twMul L f g₂ := by
  simp only [twMul, map_add]

theorem twMul_smul_left (c : ℂ) (f g : L.carrier →₀ ℂ) :
    twMul L (c • f) g = c • twMul L f g := by
  simp only [twMul, map_smul, LinearMap.smul_apply]

theorem twMul_smul_right (c : ℂ) (f g : L.carrier →₀ ℂ) :
    twMul L f (c • g) = c • twMul L f g := by
  simp only [twMul, map_smul]

/-! ## Associativity, from the 2-cocycle law -/

/-- **Associativity of the twisted product** `(f ⋆ g) ⋆ h = f ⋆ (g ⋆ h)`.  Both sides are
`ℂ`-trilinear, so it reduces (triple `Finsupp.induction_linear`) to the single-single-single case,
which is EXACTLY the 2-cocycle law `latticeCocycle_cocycleLaw`. -/
theorem twMul_assoc (f g h : L.carrier →₀ ℂ) :
    twMul L (twMul L f g) h = twMul L f (twMul L g h) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f₁ f₂ hf₁ hf₂ => rw [twMul_add_left, twMul_add_left, twMul_add_left, hf₁, hf₂]
  | single α a =>
      induction g using Finsupp.induction_linear with
      | zero => simp
      | add g₁ g₂ hg₁ hg₂ =>
          rw [twMul_add_right, twMul_add_left, twMul_add_left, twMul_add_right, hg₁, hg₂]
      | single β b =>
          induction h using Finsupp.induction_linear with
          | zero => simp
          | add h₁ h₂ hh₁ hh₂ =>
              rw [twMul_add_right, twMul_add_right, twMul_add_right, hh₁, hh₂]
          | single γ c =>
              rw [twMul_single_single, twMul_single_single, twMul_single_single,
                twMul_single_single, show α + β + γ = α + (β + γ) from add_assoc α β γ]
              congr 1
              have hcoc := latticeCocycle_cocycleLaw L α β γ
              linear_combination (a * b * c) * hcoc

/-! ## The unit `e⁰` -/

/-- `e⁰ ⋆ g = g` (using `ε(0,·) = 1`). -/
theorem one_twMul (g : L.carrier →₀ ℂ) : twMul L (latticeAlgebra.e 0) g = g := by
  induction g using Finsupp.induction_linear with
  | zero => simp
  | add g₁ g₂ hg₁ hg₂ => rw [twMul_add_right, hg₁, hg₂]
  | single β b =>
      rw [e_eq_single, twMul_single_single, zero_add, latticeCocycle_zero_left, one_mul, mul_one]

/-- `f ⋆ e⁰ = f` (using `ε(·,0) = 1`). -/
theorem twMul_one (f : L.carrier →₀ ℂ) : twMul L f (latticeAlgebra.e 0) = f := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f₁ f₂ hf₁ hf₂ => rw [twMul_add_left, hf₁, hf₂]
  | single α a =>
      rw [e_eq_single, twMul_single_single, add_zero, latticeCocycle_zero_right, mul_one, mul_one]

end VOA.IntegralLattice
