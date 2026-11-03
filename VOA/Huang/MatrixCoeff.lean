/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.FusionTop

/-!
# Matrix coefficients of products and iterates of intertwining operators

For FHL intertwining operators (`Huang/Intertwining.lean`, mode data `Y n w w' = w₍ₙ₎w'`, `n ∈ ℂ`)

* `𝒴₁` of type `(M₄ / M₁ M₅)` and `𝒴₂` of type `(M₅ / M₂ M₃)` (a **product**), and
* `𝒴₃` of type `(M₄ / M₅ M₃)` and `𝒴₄` of type `(M₅ / M₁ M₂)` (an **iterate**),

and a linear functional `f : M₄ → ℂ`, the formal correlation functions are

  `⟨f, 𝒴₁(w₁, z₁) 𝒴₂(w₂, z₂) w₃⟩ = Σ_{n₁, n₂ ∈ ℂ} prodCoeff(n₁, n₂) z₁^{−n₁−1} z₂^{−n₂−1}`,
  `⟨f, 𝒴₃(𝒴₄(w₁, z₀) w₂, z₂) w₃⟩ = Σ_{n₀, n₂ ∈ ℂ} iterCoeff(n₀, n₂) z₀^{−n₀−1} z₂^{−n₂−1}`,

with `prodCoeff(n₁, n₂) = f(𝒴₁(w₁)₍ₙ₁₎ 𝒴₂(w₂)₍ₙ₂₎ w₃)` and
`iterCoeff(n₀, n₂) = f(𝒴₃(𝒴₄(w₁)₍ₙ₀₎ w₂)₍ₙ₂₎ w₃)` — each a *single* vector pairing, no sums.

## The right truncation (and why the two-variable series is a one-variable one)

Let `w₁, w₂, w₃` be homogeneous of weights `α₁, α₂, α₃` and let `f` be **supported at `h₄`**
(`SupportedAt`: it kills every other weight space; equivalently `f` is a vector of weight `h₄` of
the contragredient `M₄'`).  Then (`L₀`-conjugation, `FusionTop.mem_weight`):

* `prodCoeff_eq_zero_of_ne`: `prodCoeff(n₁, n₂) = 0` unless `n₁ + n₂ = σ := α₁+α₂+α₃−h₄−2`;
* upper truncation in `n₂` along each coset `ν + ℤ` (FHL truncation of `𝒴₂` at `(w₂, w₃)`),
  packaged as a **base** `ν₀` (`IsProdBase`): `𝒴₂(w₂)₍ν₀+j₎w₃ = 0` for all `j ≥ 1`
  (`exists_prodBase` — every coset has one).

So on one coset the product is `z₁^{−σ+ν₀−1} z₂^{−ν₀−1} · G(z₂/z₁)` with
`G = prodSeries … σ ν₀ := Σ_k prodCoeff(σ−ν₀+k, ν₀−k) x^k ∈ ℂ⟦x⟧` (`prodCoeff_eq_coeff`: every
coefficient of the coset is a coefficient of `G` or zero).  Likewise the iterate on one coset of
`n₀` is `z₀^{−ν₀−1} z₂^{−σ+ν₀−1} · G'(z₀/z₂)` with `G' = iterSeries … σ ν₀`.  These one-variable
series are what Huang's equations (after his degree-0 reduction) constrain;
see `Huang/Convergence.lean`.

## Algebra
`prodCoeff` is additive and homogeneous in each of `𝒴₁`, `𝒴₂`, `f`, `w₁`, `w₂`, `w₃`
(`prodCoeff_add_left`, …), and so is `prodSeries`; likewise for iterates.

## Status
No `sorry`, no new axioms.
-/

namespace VOA.Huang.MatrixCoeff

open VOA VOA.Huang.FusionTop PowerSeries
open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
variable {M₁ M₂ M₃ M₄ M₅ : Type u}
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] [AddCommGroup M₄] [Module ℂ M₄]
  [AddCommGroup M₅] [Module ℂ M₅]

/-! ## Definitions -/

/-- The coefficient of `z₁^{−n₁−1} z₂^{−n₂−1}` in `⟨f, 𝒴₁(w₁, z₁) 𝒴₂(w₂, z₂) w₃⟩`. -/
noncomputable def prodCoeff (Y₁ : IntertwiningModes M₁ M₅ M₄) (Y₂ : IntertwiningModes M₂ M₃ M₅)
    (f : M₄ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) (n₁ n₂ : ℂ) : ℂ :=
  f (Y₁ n₁ w₁ (Y₂ n₂ w₂ w₃))

/-- The coefficient of `z₀^{−n₀−1} z₂^{−n₂−1}` in `⟨f, 𝒴₃(𝒴₄(w₁, z₀) w₂, z₂) w₃⟩`. -/
noncomputable def iterCoeff (Y₃ : IntertwiningModes M₅ M₃ M₄) (Y₄ : IntertwiningModes M₁ M₂ M₅)
    (f : M₄ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) (n₀ n₂ : ℂ) : ℂ :=
  f (Y₃ n₂ (Y₄ n₀ w₁ w₂) w₃)

/-- `f` is **supported at weight `h`**: it vanishes on every other weight space. -/
def SupportedAt (A : OrdVModule W M₄) (f : M₄ →ₗ[ℂ] ℂ) (h : ℂ) : Prop :=
  ∀ α : ℂ, α ≠ h → ∀ x ∈ A.weight α, f x = 0

/-- On one coset, the product as a power series in `x = z₂/z₁`:
`Σ_k prodCoeff(σ − ν₀ + k, ν₀ − k) x^k`. -/
noncomputable def prodSeries (Y₁ : IntertwiningModes M₁ M₅ M₄) (Y₂ : IntertwiningModes M₂ M₃ M₅)
    (f : M₄ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) (σ ν₀ : ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun k => prodCoeff Y₁ Y₂ f w₁ w₂ w₃ (σ - ν₀ + k) (ν₀ - k)

/-- On one coset, the iterate as a power series in `x = z₀/z₂`:
`Σ_k iterCoeff(ν₀ − k, σ − ν₀ + k) x^k`. -/
noncomputable def iterSeries (Y₃ : IntertwiningModes M₅ M₃ M₄) (Y₄ : IntertwiningModes M₁ M₂ M₅)
    (f : M₄ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) (σ ν₀ : ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun k => iterCoeff Y₃ Y₄ f w₁ w₂ w₃ (ν₀ - k) (σ - ν₀ + k)

/-- `ν₀` is a **base** for the inner operator at `(w, w')`: its modes `ν₀ + j`, `j ≥ 1`, vanish. -/
def IsBase {N₁ N₂ N₃ : Type u} [AddCommGroup N₁] [Module ℂ N₁] [AddCommGroup N₂] [Module ℂ N₂]
    [AddCommGroup N₃] [Module ℂ N₃] (Y : IntertwiningModes N₁ N₂ N₃) (w : N₁) (w' : N₂)
    (ν₀ : ℂ) : Prop :=
  ∀ j : ℕ, Y (ν₀ + ((j : ℂ) + 1)) w w' = 0

theorem coeff_prodSeries (Y₁ : IntertwiningModes M₁ M₅ M₄) (Y₂ : IntertwiningModes M₂ M₃ M₅)
    (f : M₄ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) (σ ν₀ : ℂ) (k : ℕ) :
    coeff k (prodSeries Y₁ Y₂ f w₁ w₂ w₃ σ ν₀) = prodCoeff Y₁ Y₂ f w₁ w₂ w₃ (σ - ν₀ + k) (ν₀ - k) :=
  coeff_mk _ _

theorem coeff_iterSeries (Y₃ : IntertwiningModes M₅ M₃ M₄) (Y₄ : IntertwiningModes M₁ M₂ M₅)
    (f : M₄ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) (σ ν₀ : ℂ) (k : ℕ) :
    coeff k (iterSeries Y₃ Y₄ f w₁ w₂ w₃ σ ν₀) = iterCoeff Y₃ Y₄ f w₁ w₂ w₃ (ν₀ - k) (σ - ν₀ + k) :=
  coeff_mk _ _

/-! ## Algebra: multilinearity -/

section Algebra

variable (Y₁ Y₁' : IntertwiningModes M₁ M₅ M₄) (Y₂ Y₂' : IntertwiningModes M₂ M₃ M₅)
  (f f' : M₄ →ₗ[ℂ] ℂ) (w₁ w₁' : M₁) (w₂ w₂' : M₂) (w₃ w₃' : M₃) (n₁ n₂ c : ℂ)

theorem prodCoeff_add_left :
    prodCoeff (Y₁ + Y₁') Y₂ f w₁ w₂ w₃ n₁ n₂
      = prodCoeff Y₁ Y₂ f w₁ w₂ w₃ n₁ n₂ + prodCoeff Y₁' Y₂ f w₁ w₂ w₃ n₁ n₂ := by
  simp [prodCoeff]

theorem prodCoeff_smul_left :
    prodCoeff (c • Y₁) Y₂ f w₁ w₂ w₃ n₁ n₂ = c * prodCoeff Y₁ Y₂ f w₁ w₂ w₃ n₁ n₂ := by
  simp [prodCoeff]

theorem prodCoeff_add_right :
    prodCoeff Y₁ (Y₂ + Y₂') f w₁ w₂ w₃ n₁ n₂
      = prodCoeff Y₁ Y₂ f w₁ w₂ w₃ n₁ n₂ + prodCoeff Y₁ Y₂' f w₁ w₂ w₃ n₁ n₂ := by
  simp [prodCoeff]

theorem prodCoeff_smul_right :
    prodCoeff Y₁ (c • Y₂) f w₁ w₂ w₃ n₁ n₂ = c * prodCoeff Y₁ Y₂ f w₁ w₂ w₃ n₁ n₂ := by
  simp [prodCoeff]

theorem prodCoeff_add_functional :
    prodCoeff Y₁ Y₂ (f + f') w₁ w₂ w₃ n₁ n₂
      = prodCoeff Y₁ Y₂ f w₁ w₂ w₃ n₁ n₂ + prodCoeff Y₁ Y₂ f' w₁ w₂ w₃ n₁ n₂ := by
  simp [prodCoeff]

theorem prodCoeff_add_w₁ :
    prodCoeff Y₁ Y₂ f (w₁ + w₁') w₂ w₃ n₁ n₂
      = prodCoeff Y₁ Y₂ f w₁ w₂ w₃ n₁ n₂ + prodCoeff Y₁ Y₂ f w₁' w₂ w₃ n₁ n₂ := by
  simp [prodCoeff]

theorem prodCoeff_add_w₂ :
    prodCoeff Y₁ Y₂ f w₁ (w₂ + w₂') w₃ n₁ n₂
      = prodCoeff Y₁ Y₂ f w₁ w₂ w₃ n₁ n₂ + prodCoeff Y₁ Y₂ f w₁ w₂' w₃ n₁ n₂ := by
  simp [prodCoeff]

theorem prodCoeff_add_w₃ :
    prodCoeff Y₁ Y₂ f w₁ w₂ (w₃ + w₃') n₁ n₂
      = prodCoeff Y₁ Y₂ f w₁ w₂ w₃ n₁ n₂ + prodCoeff Y₁ Y₂ f w₁ w₂ w₃' n₁ n₂ := by
  simp [prodCoeff]

theorem prodCoeff_smul_w₃ :
    prodCoeff Y₁ Y₂ f w₁ w₂ (c • w₃) n₁ n₂ = c * prodCoeff Y₁ Y₂ f w₁ w₂ w₃ n₁ n₂ := by
  simp [prodCoeff]

/-- The product series is linear in the outer operator. -/
theorem prodSeries_add_left (σ ν₀ : ℂ) :
    prodSeries (Y₁ + Y₁') Y₂ f w₁ w₂ w₃ σ ν₀
      = prodSeries Y₁ Y₂ f w₁ w₂ w₃ σ ν₀ + prodSeries Y₁' Y₂ f w₁ w₂ w₃ σ ν₀ := by
  ext k; simp [coeff_prodSeries, prodCoeff_add_left]

theorem prodSeries_smul_left (σ ν₀ : ℂ) :
    prodSeries (c • Y₁) Y₂ f w₁ w₂ w₃ σ ν₀ = c • prodSeries Y₁ Y₂ f w₁ w₂ w₃ σ ν₀ := by
  ext k; simp [coeff_prodSeries, prodCoeff_smul_left]

/-- The product series is linear in the inner operator. -/
theorem prodSeries_add_right (σ ν₀ : ℂ) :
    prodSeries Y₁ (Y₂ + Y₂') f w₁ w₂ w₃ σ ν₀
      = prodSeries Y₁ Y₂ f w₁ w₂ w₃ σ ν₀ + prodSeries Y₁ Y₂' f w₁ w₂ w₃ σ ν₀ := by
  ext k; simp [coeff_prodSeries, prodCoeff_add_right]

theorem prodSeries_smul_right (σ ν₀ : ℂ) :
    prodSeries Y₁ (c • Y₂) f w₁ w₂ w₃ σ ν₀ = c • prodSeries Y₁ Y₂ f w₁ w₂ w₃ σ ν₀ := by
  ext k; simp [coeff_prodSeries, prodCoeff_smul_right]

end Algebra

section IterAlgebra

variable (Y₃ Y₃' : IntertwiningModes M₅ M₃ M₄) (Y₄ Y₄' : IntertwiningModes M₁ M₂ M₅)
  (f : M₄ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) (n₀ n₂ c : ℂ)

theorem iterCoeff_add_left :
    iterCoeff (Y₃ + Y₃') Y₄ f w₁ w₂ w₃ n₀ n₂
      = iterCoeff Y₃ Y₄ f w₁ w₂ w₃ n₀ n₂ + iterCoeff Y₃' Y₄ f w₁ w₂ w₃ n₀ n₂ := by
  simp [iterCoeff]

theorem iterCoeff_smul_left :
    iterCoeff (c • Y₃) Y₄ f w₁ w₂ w₃ n₀ n₂ = c * iterCoeff Y₃ Y₄ f w₁ w₂ w₃ n₀ n₂ := by
  simp [iterCoeff]

theorem iterCoeff_add_right :
    iterCoeff Y₃ (Y₄ + Y₄') f w₁ w₂ w₃ n₀ n₂
      = iterCoeff Y₃ Y₄ f w₁ w₂ w₃ n₀ n₂ + iterCoeff Y₃ Y₄' f w₁ w₂ w₃ n₀ n₂ := by
  simp [iterCoeff]

theorem iterCoeff_smul_right :
    iterCoeff Y₃ (c • Y₄) f w₁ w₂ w₃ n₀ n₂ = c * iterCoeff Y₃ Y₄ f w₁ w₂ w₃ n₀ n₂ := by
  simp [iterCoeff]

end IterAlgebra

/-! ## Truncation: the weight line and the upper bound -/

section Weights

variable {A₁ : OrdVModule W M₁} {A₂ : OrdVModule W M₂} {A₃ : OrdVModule W M₃}
  {A₄ : OrdVModule W M₄} {A₅ : OrdVModule W M₅}

/-- **The weight line of a product.**  For homogeneous `w₁, w₂, w₃` and `f` supported at `h₄`,
`prodCoeff(n₁, n₂) = 0` unless `n₁ + n₂ = α₁ + α₂ + α₃ − h₄ − 2`. -/
theorem prodCoeff_eq_zero_of_ne {Y₁ : IntertwiningModes M₁ M₅ M₄}
    {Y₂ : IntertwiningModes M₂ M₃ M₅} (hY₁ : IsIntertwiningOperator A₁ A₅ A₄ Y₁)
    (hY₂ : IsIntertwiningOperator A₂ A₃ A₅ Y₂) {α₁ α₂ α₃ h₄ : ℂ} {w₁ : M₁} {w₂ : M₂} {w₃ : M₃}
    (h₁ : w₁ ∈ A₁.weight α₁) (h₂ : w₂ ∈ A₂.weight α₂) (h₃ : w₃ ∈ A₃.weight α₃)
    {f : M₄ →ₗ[ℂ] ℂ} (hf : SupportedAt A₄ f h₄) {n₁ n₂ : ℂ}
    (hn : n₁ + n₂ ≠ α₁ + α₂ + α₃ - h₄ - 2) :
    prodCoeff Y₁ Y₂ f w₁ w₂ w₃ n₁ n₂ = 0 := by
  have hin := mem_weight hY₂ h₂ h₃ n₂
  have hout := mem_weight hY₁ h₁ hin n₁
  refine hf _ ?_ _ hout
  intro h
  apply hn
  linear_combination -h

/-- **The weight line of an iterate.**  `iterCoeff(n₀, n₂) = 0` unless
`n₀ + n₂ = α₁ + α₂ + α₃ − h₄ − 2`. -/
theorem iterCoeff_eq_zero_of_ne {Y₃ : IntertwiningModes M₅ M₃ M₄}
    {Y₄ : IntertwiningModes M₁ M₂ M₅} (hY₃ : IsIntertwiningOperator A₅ A₃ A₄ Y₃)
    (hY₄ : IsIntertwiningOperator A₁ A₂ A₅ Y₄) {α₁ α₂ α₃ h₄ : ℂ} {w₁ : M₁} {w₂ : M₂} {w₃ : M₃}
    (h₁ : w₁ ∈ A₁.weight α₁) (h₂ : w₂ ∈ A₂.weight α₂) (h₃ : w₃ ∈ A₃.weight α₃)
    {f : M₄ →ₗ[ℂ] ℂ} (hf : SupportedAt A₄ f h₄) {n₀ n₂ : ℂ}
    (hn : n₀ + n₂ ≠ α₁ + α₂ + α₃ - h₄ - 2) :
    iterCoeff Y₃ Y₄ f w₁ w₂ w₃ n₀ n₂ = 0 := by
  have hin := mem_weight hY₄ h₁ h₂ n₀
  have hout := mem_weight hY₃ hin h₃ n₂
  refine hf _ ?_ _ hout
  intro h
  apply hn
  linear_combination -h

/-- **Every coset has a base** (FHL truncation): for any `ν`, some `ν₀ ∈ ν + ℤ` has
`Y(ν₀ + j) w w' = 0` for all `j ≥ 1`. -/
theorem exists_isBase {N₁ N₂ N₃ : Type u} [AddCommGroup N₁] [Module ℂ N₁] [AddCommGroup N₂]
    [Module ℂ N₂] [AddCommGroup N₃] [Module ℂ N₃] {B₁ : OrdVModule W N₁} {B₂ : OrdVModule W N₂}
    {B₃ : OrdVModule W N₃} {Y : IntertwiningModes N₁ N₂ N₃}
    (hY : IsIntertwiningOperator B₁ B₂ B₃ Y) (w : N₁) (w' : N₂) (ν : ℂ) :
    ∃ m : ℤ, IsBase Y w w' (ν + m) := by
  obtain ⟨N, hN⟩ := hY.truncation w w' ν
  refine ⟨N - 1, fun j => ?_⟩
  have e : ν + ((N - 1 : ℤ) : ℂ) + ((j : ℂ) + 1) = ν + ((N + j : ℤ) : ℂ) := by push_cast; ring
  rw [e]
  exact hN (N + j) (by omega)

/-- A base stays a base when moved up. -/
theorem IsBase.add_nat {N₁ N₂ N₃ : Type u} [AddCommGroup N₁] [Module ℂ N₁] [AddCommGroup N₂]
    [Module ℂ N₂] [AddCommGroup N₃] [Module ℂ N₃] {Y : IntertwiningModes N₁ N₂ N₃} {w : N₁}
    {w' : N₂} {ν₀ : ℂ} (h : IsBase Y w w' ν₀) (d : ℕ) : IsBase Y w w' (ν₀ + d) := by
  intro j
  have e : ν₀ + (d : ℂ) + ((j : ℂ) + 1) = ν₀ + (((j + d : ℕ) : ℂ) + 1) := by push_cast; ring
  rw [e]
  exact h (j + d)

/-- **The product on one coset is the power series `prodSeries`.**  For `n₂ = ν₀ − j`
(`j ∈ ℤ`) with `ν₀` a base: the coefficient vanishes for `j < 0` and off the weight line, and
otherwise equals the `j`-th coefficient of `prodSeries … σ ν₀`. -/
theorem prodCoeff_eq_coeff {Y₁ : IntertwiningModes M₁ M₅ M₄}
    {Y₂ : IntertwiningModes M₂ M₃ M₅} (hY₁ : IsIntertwiningOperator A₁ A₅ A₄ Y₁)
    (hY₂ : IsIntertwiningOperator A₂ A₃ A₅ Y₂) {α₁ α₂ α₃ h₄ : ℂ} {w₁ : M₁} {w₂ : M₂} {w₃ : M₃}
    (h₁ : w₁ ∈ A₁.weight α₁) (h₂ : w₂ ∈ A₂.weight α₂) (h₃ : w₃ ∈ A₃.weight α₃)
    {f : M₄ →ₗ[ℂ] ℂ} (hf : SupportedAt A₄ f h₄) {ν₀ : ℂ} (hb : IsBase Y₂ w₂ w₃ ν₀)
    (n₁ : ℂ) (j : ℤ) :
    prodCoeff Y₁ Y₂ f w₁ w₂ w₃ n₁ (ν₀ - j)
      = if n₁ + (ν₀ - j) = α₁ + α₂ + α₃ - h₄ - 2 ∧ 0 ≤ j then
          coeff j.toNat (prodSeries Y₁ Y₂ f w₁ w₂ w₃ (α₁ + α₂ + α₃ - h₄ - 2) ν₀)
        else 0 := by
  split_ifs with h
  · obtain ⟨hl, hj⟩ := h
    rw [coeff_prodSeries]
    have hjc : ((j.toNat : ℕ) : ℂ) = (j : ℂ) := by exact_mod_cast Int.toNat_of_nonneg hj
    rw [hjc]
    congr 1
    linear_combination hl
  · by_cases hl : n₁ + (ν₀ - j) = α₁ + α₂ + α₃ - h₄ - 2
    · have hj : j < 0 := by
        by_contra hj; exact h ⟨hl, by omega⟩
      have hz : Y₂ (ν₀ - j) w₂ w₃ = 0 := by
        have hc : (((-j - 1).toNat : ℕ) : ℂ) = ((-j - 1 : ℤ) : ℂ) := by
          exact_mod_cast Int.toNat_of_nonneg (by omega)
        have e : ν₀ - (j : ℂ) = ν₀ + ((((-j - 1).toNat : ℕ) : ℂ) + 1) := by
          rw [hc]; push_cast; ring
        rw [e]
        exact hb _
      simp [prodCoeff, hz]
    · exact prodCoeff_eq_zero_of_ne hY₁ hY₂ h₁ h₂ h₃ hf hl

/-- **The iterate on one coset is the power series `iterSeries`.** -/
theorem iterCoeff_eq_coeff {Y₃ : IntertwiningModes M₅ M₃ M₄}
    {Y₄ : IntertwiningModes M₁ M₂ M₅} (hY₃ : IsIntertwiningOperator A₅ A₃ A₄ Y₃)
    (hY₄ : IsIntertwiningOperator A₁ A₂ A₅ Y₄) {α₁ α₂ α₃ h₄ : ℂ} {w₁ : M₁} {w₂ : M₂} {w₃ : M₃}
    (h₁ : w₁ ∈ A₁.weight α₁) (h₂ : w₂ ∈ A₂.weight α₂) (h₃ : w₃ ∈ A₃.weight α₃)
    {f : M₄ →ₗ[ℂ] ℂ} (hf : SupportedAt A₄ f h₄) {ν₀ : ℂ} (hb : IsBase Y₄ w₁ w₂ ν₀)
    (j : ℤ) (n₂ : ℂ) :
    iterCoeff Y₃ Y₄ f w₁ w₂ w₃ (ν₀ - j) n₂
      = if (ν₀ - j) + n₂ = α₁ + α₂ + α₃ - h₄ - 2 ∧ 0 ≤ j then
          coeff j.toNat (iterSeries Y₃ Y₄ f w₁ w₂ w₃ (α₁ + α₂ + α₃ - h₄ - 2) ν₀)
        else 0 := by
  split_ifs with h
  · obtain ⟨hl, hj⟩ := h
    rw [coeff_iterSeries]
    have hjc : ((j.toNat : ℕ) : ℂ) = (j : ℂ) := by exact_mod_cast Int.toNat_of_nonneg hj
    rw [hjc]
    congr 1
    linear_combination hl
  · by_cases hl : (ν₀ - j) + n₂ = α₁ + α₂ + α₃ - h₄ - 2
    · have hj : j < 0 := by
        by_contra hj; exact h ⟨hl, by omega⟩
      have hz : Y₄ (ν₀ - j) w₁ w₂ = 0 := by
        have hc : (((-j - 1).toNat : ℕ) : ℂ) = ((-j - 1 : ℤ) : ℂ) := by
          exact_mod_cast Int.toNat_of_nonneg (by omega)
        have e : ν₀ - (j : ℂ) = ν₀ + ((((-j - 1).toNat : ℕ) : ℂ) + 1) := by
          rw [hc]; push_cast; ring
        rw [e]
        exact hb _
      simp [iterCoeff, hz]
    · exact iterCoeff_eq_zero_of_ne hY₃ hY₄ h₁ h₂ h₃ hf hl

end Weights

end VOA.Huang.MatrixCoeff
