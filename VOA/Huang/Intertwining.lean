/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.Translation
import VOA.Foundations.IotaZExpansion

/-!
# Intertwining operators (Frenkel–Huang–Lepowsky, Def. 5.4.1)

For `𝒱`-modules `M₁, M₂, M₃` (`OrdVModule`), an **intertwining operator of type `(M₃ / M₁ M₂)`**
is a linear map `𝒴 : M₁ ⊗ M₂ → M₃{z}`,

  `𝒴(w₁, z) w₂ = ∑_{n ∈ ℂ} (w₁)₍ₙ₎ w₂ z^{-n-1}`,

such that
1. **truncation**: for all `w₁, w₂` and `n ∈ ℂ`, `(w₁)₍ₙ₊ₖ₎ w₂ = 0` for `k ∈ ℤ` large;
2. **`L₋₁`-derivative**: `𝒴(L₋₁ w₁, z) = d/dz 𝒴(w₁, z)`;
3. **the Jacobi identity**
   `z₀⁻¹δ((z₁-z₂)/z₀) Y₃(u,z₁)𝒴(w₁,z₂) − z₀⁻¹δ((z₂-z₁)/(-z₀)) 𝒴(w₁,z₂)Y₂(u,z₁)`
   `= z₂⁻¹δ((z₁-z₀)/z₂) 𝒴(Y₁(u,z₀)w₁, z₂)`.

This is a separate notion: the bundled `VOA.Intertwiner` of `Modules/Fusion.lean` imposes only
truncation and the commutator formula, and its `fusionCoeff` is identically `0`
(so it carries no fusion information).  That file is kept as is (the Moonshine chain uses it).

## Encoding (and why it is faithful)

* **Modes.** `IntertwiningModes M₁ M₂ M₃ := ℂ → (M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] M₃)`, with
  `Y n w₁ w₂ = (w₁)₍ₙ₎ w₂`, the coefficient of `z^{-n-1}`.  This is *literally* FHL's
  `Hom(M₂, M₃){z}` (arbitrary complex exponents, no support restriction); bilinearity in
  `(w₁, w₂)` is FHL's linearity of `𝒴`.  We do **not** fix a coset `h + ℤ` of exponents: for
  irreducible modules the support of a nonzero intertwiner lies in the single coset
  `h₁ + h₂ − h₃ + ℤ`, but that is a *consequence* (of the `L₀`-conjugation formula), not part of
  FHL's definition, and imposing it would make the space depend on a choice.  Everything below
  respects cosets: each axiom relates modes in one class `n + ℤ` only.
* **Truncation** is FHL's per-coset form: `∀ w₁ w₂ n, ∃ N : ℤ, ∀ k ≥ N, (w₁)₍ₙ₊ₖ₎w₂ = 0`.
  (It is weaker than "zero for `Re n ≫ 0`" uniformly, exactly as in FHL.)
* **`L₋₁`-derivative** in modes: `d/dz ∑ (w₁)₍ₙ₎ z^{-n-1} = ∑ (-n) (w₁)₍ₙ₋₁₎ z^{-n-1}`, so
  `(L₋₁ w₁)₍ₙ₎ = −n (w₁)₍ₙ₋₁₎`, with `L₋₁ = ω₍₀₎` acting on `M₁` (`Lₖ = ω₍ₖ₊₁₎`).
* **Jacobi identity** in mode form: the coefficient of `z₀^{-ℓ-1} z₁^{-m-1} z₂^{-n-1}`
  (`ℓ, m ∈ ℤ`, `n ∈ ℂ` — the `z₀, z₁` exponents are integral, only `z₂` carries complex
  exponents) of the generating identity above is

  `∑ᵢ (-1)ⁱ C(ℓ,i) (u₍ℓ₊ₘ₋ᵢ₎ (w₁)₍ₙ₊ᵢ₎ w₂ − (-1)^ℓ (w₁)₍ℓ₊ₙ₋ᵢ₎ u₍ₘ₊ᵢ₎ w₂)`
  `= ∑ᵢ C(m,i) (u₍ℓ₊ᵢ₎ w₁)₍ₘ₊ₙ₋ᵢ₎ w₂`,

  the same shape and conventions (`cbz`, `negOnePow`, `∑ᶠ i : ℤ`) as the module Jacobi identity
  `WeakModule.jacobi`, with the `v`-modes replaced by the complex-indexed intertwiner modes.
  The family over all `(ℓ, m, n)` is equivalent to the generating identity.  All sums have
  finite support by truncation (proved below), so the `∑ᶠ` are genuine finite sums.

## Main declarations
* `IsIntertwiningOperator` — the three FHL axioms on mode data.
* `intertwiningSpace A₁ A₂ A₃ : Submodule ℂ (IntertwiningModes M₁ M₂ M₃)` — **(a)** a `ℂ`-vector
  space; `IntertwiningOperator A₁ A₂ A₃` its carrier type.
* `IsIntertwiningOperator.commutator` — the commutator formula (`ℓ = 0`).
* `moduleIntertwiner A : IntertwiningOperator (adjointModule W) A A` — **(b)** `Y_M` is an
  intertwiner of type `(M / W M)`; `moduleIntertwiner_ne_zero` (non-vacuity).
* `fusionRule A₁ A₂ A₃ := finrank ℂ (intertwiningSpace A₁ A₂ A₃)` — **(c)**; and
  `one_le_fusionRule_adjoint` : `1 ≤ N^M_{W M}` *given* finite-dimensionality.

## Not done here
* Finite-dimensionality of `intertwiningSpace` (needs the `L₀`-conjugation formula, grading and
  e.g. Frenkel–Zhu / `C₂`-cofiniteness: stages H2/H3).  Without it `fusionRule` is the `finrank`
  convention value `0` on infinite-dimensional spaces — so positivity statements here are stated
  under an explicit `FiniteDimensional` hypothesis.
* **(d) Lattice intertwiners** among `latticeModule m hm j`: not attempted.  The modules are built
  inside *different* gluing lattices `glueLat m j` (one per `j`), and the intertwiner
  `𝒴(e^{λ_j}, z)` on `V_{L+λ_k}` carries the fractional power `z^{jk/(2m)}`, which no integral
  lattice VOA's vertex operator produces; it needs either a common gluing lattice together with a
  tensor factorisation `V_N ≅ V_L ⊗ V_{L^⊥}`, or a direct construction of the `ℂ`-graded
  vertex operators `E^±(λ,z) z^{λ(0)}` on `Fock ⊗ ℂ{L+ℤλ}`.

## Status
No `sorry`, no new axioms.
-/

namespace VOA

open Module (End)
open scoped BigOperators

universe u v₁ v₂ v₃

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
variable {M₁ : Type v₁} {M₂ : Type v₂} {M₃ : Type v₃}
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃]

/-- The **mode data** of a would-be intertwining operator `𝒴(·,z) : M₁ → Hom(M₂,M₃){z}`:
`Y n w₁ w₂ = (w₁)₍ₙ₎ w₂`, the coefficient of `z^{-n-1}`, `n ∈ ℂ` (FHL §5.4). -/
abbrev IntertwiningModes (M₁ : Type v₁) (M₂ : Type v₂) (M₃ : Type v₃)
    [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
    [AddCommGroup M₃] [Module ℂ M₃] :=
  ℂ → (M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] M₃)

/-- The `L₋₁` operator `ω₍₀₎` of a module (`Lₖ = ω₍ₖ₊₁₎`). -/
abbrev OrdVModule.Lm1 (A : OrdVModule W M₁) : End ℂ M₁ := mode (A.YM W.conformalVector) 0

/-- **Intertwining operator of type `(M₃ / M₁ M₂)`** (Frenkel–Huang–Lepowsky Def. 5.4.1), on mode
data `Y n w₁ w₂ = (w₁)₍ₙ₎ w₂`: truncation, the `L₋₁`-derivative property and the full Jacobi
identity (mode form; see the module docstring for the coefficient extraction). -/
structure IsIntertwiningOperator (A₁ : OrdVModule W M₁) (A₂ : OrdVModule W M₂)
    (A₃ : OrdVModule W M₃) (Y : IntertwiningModes M₁ M₂ M₃) : Prop where
  /-- **Truncation** (FHL): `(w₁)₍ₙ₊ₖ₎ w₂ = 0` for `k ∈ ℤ` sufficiently large. -/
  truncation : ∀ (w₁ : M₁) (w₂ : M₂) (n : ℂ), ∃ N : ℤ, ∀ k : ℤ, N ≤ k → Y (n + k) w₁ w₂ = 0
  /-- **`L₋₁`-derivative**: `𝒴(L₋₁ w₁, z) = d/dz 𝒴(w₁, z)`, i.e. `(L₋₁w₁)₍ₙ₎ = −n (w₁)₍ₙ₋₁₎`. -/
  L_neg_one : ∀ (w₁ : M₁) (n : ℂ), Y n (A₁.Lm1 w₁) = (-n) • Y (n - 1) w₁
  /-- **Jacobi identity**, coefficient of `z₀^{-ℓ-1} z₁^{-m-1} z₂^{-n-1}`. -/
  jacobi : ∀ (u : 𝒱) (w₁ : M₁) (w₂ : M₂) (ℓ m : ℤ) (n : ℂ),
    (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
        (mode (A₃.YM u) (ℓ + m - i) (Y (n + i) w₁ w₂)
          - negOnePow ℓ • Y (ℓ + n - i) w₁ (mode (A₂.YM u) (m + i) w₂)))
      = ∑ᶠ i : ℤ, cbz m i • Y (m + n - i) (mode (A₁.YM u) (ℓ + i) w₁) w₂

namespace IsIntertwiningOperator

variable {A₁ : OrdVModule W M₁} {A₂ : OrdVModule W M₂} {A₃ : OrdVModule W M₃}

/-- The left summand of the Jacobi identity. -/
noncomputable def jacL (A₂ : OrdVModule W M₂) (A₃ : OrdVModule W M₃)
    (Y : IntertwiningModes M₁ M₂ M₃) (u : 𝒱) (w₁ : M₁) (w₂ : M₂) (ℓ m : ℤ) (n : ℂ) (i : ℤ) :
    M₃ :=
  (negOnePow i * cbz ℓ i) •
    (mode (A₃.YM u) (ℓ + m - i) (Y (n + i) w₁ w₂)
      - negOnePow ℓ • Y (ℓ + n - i) w₁ (mode (A₂.YM u) (m + i) w₂))

/-- The right summand of the Jacobi identity. -/
noncomputable def jacR (A₁ : OrdVModule W M₁) (Y : IntertwiningModes M₁ M₂ M₃) (u : 𝒱)
    (w₁ : M₁) (w₂ : M₂) (ℓ m : ℤ) (n : ℂ) (i : ℤ) : M₃ :=
  cbz m i • Y (m + n - i) (mode (A₁.YM u) (ℓ + i) w₁) w₂

theorem jacL_add (Y₁ Y₂ : IntertwiningModes M₁ M₂ M₃) (u : 𝒱) (w₁ : M₁) (w₂ : M₂)
    (ℓ m : ℤ) (n : ℂ) (i : ℤ) :
    jacL A₂ A₃ (Y₁ + Y₂) u w₁ w₂ ℓ m n i
      = jacL A₂ A₃ Y₁ u w₁ w₂ ℓ m n i + jacL A₂ A₃ Y₂ u w₁ w₂ ℓ m n i := by
  simp only [jacL, Pi.add_apply, LinearMap.add_apply, map_add]
  module

theorem jacR_add (Y₁ Y₂ : IntertwiningModes M₁ M₂ M₃) (u : 𝒱) (w₁ : M₁) (w₂ : M₂)
    (ℓ m : ℤ) (n : ℂ) (i : ℤ) :
    jacR A₁ (Y₁ + Y₂) u w₁ w₂ ℓ m n i
      = jacR A₁ Y₁ u w₁ w₂ ℓ m n i + jacR A₁ Y₂ u w₁ w₂ ℓ m n i := by
  simp only [jacR, Pi.add_apply, LinearMap.add_apply, smul_add]

theorem jacL_smul (c : ℂ) (Y : IntertwiningModes M₁ M₂ M₃) (u : 𝒱) (w₁ : M₁) (w₂ : M₂)
    (ℓ m : ℤ) (n : ℂ) (i : ℤ) :
    jacL A₂ A₃ (c • Y) u w₁ w₂ ℓ m n i = c • jacL A₂ A₃ Y u w₁ w₂ ℓ m n i := by
  simp only [jacL, Pi.smul_apply, LinearMap.smul_apply, map_smul]
  module

theorem jacR_smul (c : ℂ) (Y : IntertwiningModes M₁ M₂ M₃) (u : 𝒱) (w₁ : M₁) (w₂ : M₂)
    (ℓ m : ℤ) (n : ℂ) (i : ℤ) :
    jacR A₁ (c • Y) u w₁ w₂ ℓ m n i = c • jacR A₁ Y u w₁ w₂ ℓ m n i := by
  simp only [jacR, Pi.smul_apply, LinearMap.smul_apply]
  rw [smul_comm]

/-- Finite support of the left Jacobi summand, from the truncation of `Y` and of `M₂`. -/
theorem jacL_support_finite {Y : IntertwiningModes M₁ M₂ M₃}
    (htr : ∀ (w₁ : M₁) (w₂ : M₂) (n : ℂ), ∃ N : ℤ, ∀ k : ℤ, N ≤ k → Y (n + k) w₁ w₂ = 0)
    (u : 𝒱) (w₁ : M₁) (w₂ : M₂) (ℓ m : ℤ) (n : ℂ) :
    (Function.support (jacL A₂ A₃ Y u w₁ w₂ ℓ m n)).Finite := by
  obtain ⟨N₁, hN₁⟩ := htr w₁ w₂ n
  obtain ⟨N₂, hN₂⟩ := A₂.truncation u w₂
  refine (Set.finite_Ico (0 : ℤ) (max N₁ (N₂ - m))).subset (fun i hi => ?_)
  simp only [Function.mem_support] at hi
  simp only [Set.mem_Ico]
  by_contra hcon
  apply hi
  rcases lt_or_ge i 0 with hneg | hnn
  · simp [jacL, cbz_apply_neg ℓ hneg]
  · have hge : max N₁ (N₂ - m) ≤ i := by
      by_contra h; exact hcon ⟨hnn, not_le.mp h⟩
    have h1 : Y (n + i) w₁ w₂ = 0 := hN₁ i (le_trans (le_max_left _ _) hge)
    have h2 : mode (A₂.YM u) (m + i) w₂ = 0 :=
      hN₂ (m + i) (by have := le_trans (le_max_right _ _) hge; omega)
    simp only [jacL, h1, h2, map_zero, smul_zero, sub_zero]

/-- Finite support of the right Jacobi summand, from the truncation of `M₁`. -/
theorem jacR_support_finite (Y : IntertwiningModes M₁ M₂ M₃) (u : 𝒱) (w₁ : M₁) (w₂ : M₂)
    (ℓ m : ℤ) (n : ℂ) :
    (Function.support (jacR A₁ Y u w₁ w₂ ℓ m n)).Finite := by
  obtain ⟨N, hN⟩ := A₁.truncation u w₁
  refine (Set.finite_Ico (0 : ℤ) (N - ℓ)).subset (fun i hi => ?_)
  simp only [Function.mem_support] at hi
  simp only [Set.mem_Ico]
  by_contra hcon
  apply hi
  rcases lt_or_ge i 0 with hneg | hnn
  · simp [jacR, cbz_apply_neg m hneg]
  · have h : mode (A₁.YM u) (ℓ + i) w₁ = 0 := hN (ℓ + i) (by
      by_contra h; exact hcon ⟨hnn, by omega⟩)
    simp only [jacR, h, map_zero, LinearMap.zero_apply, smul_zero]

/-- The **commutator formula** (Jacobi at `ℓ = 0`):
`u₍ₘ₎ (w₁)₍ₙ₎ w₂ − (w₁)₍ₙ₎ u₍ₘ₎ w₂ = ∑ᵢ C(m,i) (u₍ᵢ₎ w₁)₍ₘ₊ₙ₋ᵢ₎ w₂`. -/
theorem commutator {Y : IntertwiningModes M₁ M₂ M₃} (hY : IsIntertwiningOperator A₁ A₂ A₃ Y)
    (u : 𝒱) (w₁ : M₁) (w₂ : M₂) (m : ℤ) (n : ℂ) :
    mode (A₃.YM u) m (Y n w₁ w₂) - Y n w₁ (mode (A₂.YM u) m w₂)
      = ∑ᶠ i : ℤ, cbz m i • Y (m + n - i) (mode (A₁.YM u) i w₁) w₂ := by
  have h := hY.jacobi u w₁ w₂ 0 m n
  rw [finsum_eq_single _ (0 : ℤ)] at h
  · simpa [cbz_zero_left, negOnePow] using h
  · intro i hi
    simp [cbz_zero_left, hi]

end IsIntertwiningOperator

/-! ## (a) The space of intertwining operators -/

/-- **(a)** The `ℂ`-vector space of intertwining operators of type `(M₃ / M₁ M₂)`. -/
noncomputable def intertwiningSpace (A₁ : OrdVModule W M₁) (A₂ : OrdVModule W M₂)
    (A₃ : OrdVModule W M₃) : Submodule ℂ (IntertwiningModes M₁ M₂ M₃) where
  carrier := {Y | IsIntertwiningOperator A₁ A₂ A₃ Y}
  zero_mem' := by
    refine ⟨fun _ _ _ => ⟨0, fun _ _ => rfl⟩, fun _ _ => by simp, ?_⟩
    intro u w₁ w₂ ℓ m n
    simp
  add_mem' := by
    intro Y₁ Y₂ (h₁ : IsIntertwiningOperator A₁ A₂ A₃ Y₁) (h₂ : IsIntertwiningOperator A₁ A₂ A₃ Y₂)
    refine ⟨?_, ?_, ?_⟩
    · intro w₁ w₂ n
      obtain ⟨N₁, hN₁⟩ := h₁.truncation w₁ w₂ n
      obtain ⟨N₂, hN₂⟩ := h₂.truncation w₁ w₂ n
      refine ⟨max N₁ N₂, fun k hk => ?_⟩
      simp [hN₁ k (le_trans (le_max_left _ _) hk), hN₂ k (le_trans (le_max_right _ _) hk)]
    · intro w₁ n
      simp only [Pi.add_apply, LinearMap.add_apply, h₁.L_neg_one, h₂.L_neg_one, smul_add]
    · intro u w₁ w₂ ℓ m n
      have e1 := h₁.jacobi u w₁ w₂ ℓ m n
      have e2 := h₂.jacobi u w₁ w₂ ℓ m n
      change ∑ᶠ i, IsIntertwiningOperator.jacL A₂ A₃ (Y₁ + Y₂) u w₁ w₂ ℓ m n i
        = ∑ᶠ i, IsIntertwiningOperator.jacR A₁ (Y₁ + Y₂) u w₁ w₂ ℓ m n i
      simp only [IsIntertwiningOperator.jacL_add, IsIntertwiningOperator.jacR_add]
      rw [finsum_add_distrib (IsIntertwiningOperator.jacL_support_finite h₁.truncation ..)
          (IsIntertwiningOperator.jacL_support_finite h₂.truncation ..),
        finsum_add_distrib (IsIntertwiningOperator.jacR_support_finite (A₁ := A₁) Y₁ u w₁ w₂ ℓ m n)
          (IsIntertwiningOperator.jacR_support_finite (A₁ := A₁) Y₂ u w₁ w₂ ℓ m n)]
      exact congrArg₂ (· + ·) e1 e2
  smul_mem' := by
    intro c Y (h : IsIntertwiningOperator A₁ A₂ A₃ Y)
    refine ⟨?_, ?_, ?_⟩
    · intro w₁ w₂ n
      obtain ⟨N, hN⟩ := h.truncation w₁ w₂ n
      exact ⟨N, fun k hk => by simp [hN k hk]⟩
    · intro w₁ n
      simp only [Pi.smul_apply, LinearMap.smul_apply, h.L_neg_one, smul_comm c (-n)]
    · intro u w₁ w₂ ℓ m n
      have e := h.jacobi u w₁ w₂ ℓ m n
      change ∑ᶠ i, IsIntertwiningOperator.jacL A₂ A₃ (c • Y) u w₁ w₂ ℓ m n i
        = ∑ᶠ i, IsIntertwiningOperator.jacR A₁ (c • Y) u w₁ w₂ ℓ m n i
      simp only [IsIntertwiningOperator.jacL_smul, IsIntertwiningOperator.jacR_smul]
      rw [← smul_finsum' c (IsIntertwiningOperator.jacL_support_finite h.truncation ..),
        ← smul_finsum' c (IsIntertwiningOperator.jacR_support_finite (A₁ := A₁) Y u w₁ w₂ ℓ m n)]
      exact congrArg (c • ·) e

theorem mem_intertwiningSpace {A₁ : OrdVModule W M₁} {A₂ : OrdVModule W M₂}
    {A₃ : OrdVModule W M₃} {Y : IntertwiningModes M₁ M₂ M₃} :
    Y ∈ intertwiningSpace A₁ A₂ A₃ ↔ IsIntertwiningOperator A₁ A₂ A₃ Y := Iff.rfl

/-- The type of intertwining operators of type `(M₃ / M₁ M₂)`, a `ℂ`-vector space. -/
abbrev IntertwiningOperator (A₁ : OrdVModule W M₁) (A₂ : OrdVModule W M₂)
    (A₃ : OrdVModule W M₃) :=
  ↥(intertwiningSpace A₁ A₂ A₃)

/-! ## (c) Fusion rules -/

/-- **(c)** The **fusion rule** `N^{M₃}_{M₁ M₂} := dim_ℂ` of the space of intertwining operators
of type `(M₃ / M₁ M₂)`.  ⚠ `Module.finrank` is `0` on an infinite-dimensional space; finiteness of
this space is later work (H2/H3), so read `fusionRule` together with a `FiniteDimensional`
hypothesis. -/
noncomputable def fusionRule (A₁ : OrdVModule W M₁) (A₂ : OrdVModule W M₂)
    (A₃ : OrdVModule W M₃) : ℕ :=
  Module.finrank ℂ (intertwiningSpace A₁ A₂ A₃)

/-! ## (b) The module vertex operator is an intertwiner of type `(M / W M)` -/

section ModuleY

variable {M : Type v₁} [AddCommGroup M] [Module ℂ M]

/-- The bilinear map `(u, x) ↦ u₍ₖ₎ x` of a module, `k ∈ ℤ`. -/
noncomputable def OrdVModule.intMode (A : OrdVModule W M) (k : ℤ) : 𝒱 →ₗ[ℂ] M →ₗ[ℂ] M where
  toFun u := mode (A.YM u) k
  map_add' u₁ u₂ := by simp only [map_add, mode_add]
  map_smul' c u := by simp only [map_smul, mode_smul, RingHom.id_apply]

/-- The module vertex operator `Y_M` as complex-indexed mode data: `u₍ₙ₎x` for `n ∈ ℤ`, and `0`
at non-integral `n` (`Y_M(u,z)` has integral exponents only). -/
noncomputable def moduleModes (A : OrdVModule W M) : IntertwiningModes 𝒱 M M := fun n =>
  haveI := Classical.propDecidable (∃ k : ℤ, (k : ℂ) = n)
  if h : ∃ k : ℤ, (k : ℂ) = n then A.intMode h.choose else 0

theorem moduleModes_intCast (A : OrdVModule W M) (k : ℤ) :
    moduleModes A (k : ℂ) = A.intMode k := by
  have h : ∃ k' : ℤ, (k' : ℂ) = (k : ℂ) := ⟨k, rfl⟩
  rw [moduleModes, dif_pos h]
  have : h.choose = k := Int.cast_injective h.choose_spec
  rw [this]

theorem moduleModes_apply_intCast (A : OrdVModule W M) (k : ℤ) (u : 𝒱) (x : M) :
    moduleModes A (k : ℂ) u x = mode (A.YM u) k x := by
  rw [moduleModes_intCast]; rfl

theorem moduleModes_of_not_int (A : OrdVModule W M) {n : ℂ} (hn : ∀ k : ℤ, (k : ℂ) ≠ n) :
    moduleModes A n = 0 := by
  rw [moduleModes, dif_neg (not_exists.mpr hn)]

/-- **(b)** The module vertex operator `Y_M` satisfies the FHL intertwining axioms for the type
`(M / W M)`: truncation is the module field property, `L₋₁`-derivative is module translation
covariance (`act_T_covariance`), and the Jacobi identity is `WeakModule.jacobi` (the adjoint
module's action being the `𝒱`-product). -/
theorem isIntertwiningOperator_moduleModes (A : OrdVModule W M) :
    IsIntertwiningOperator (adjointModule W) A A (moduleModes A) := by
  refine ⟨?_, ?_, ?_⟩
  · intro u x n
    by_cases hn : ∃ k : ℤ, (k : ℂ) = n
    · obtain ⟨k, rfl⟩ := hn
      obtain ⟨N, hN⟩ := A.truncation u x
      refine ⟨N - k, fun j hj => ?_⟩
      rw [show ((k : ℂ) + (j : ℂ)) = ((k + j : ℤ) : ℂ) by push_cast; ring,
        moduleModes_apply_intCast]
      exact hN _ (by omega)
    · refine ⟨0, fun j _ => ?_⟩
      rw [moduleModes_of_not_int A (n := n + j)
        (fun k hk => hn ⟨k - j, by push_cast; rw [hk]; ring⟩)]
      rfl
  · intro u n
    have hL : (adjointModule W).Lm1 u = W.L (-1) u := by
      simp only [OrdVModule.Lm1, VertexOperatorAlgebra.L_def]; rfl
    rw [hL]
    by_cases hn : ∃ k : ℤ, (k : ℂ) = n
    · obtain ⟨k, rfl⟩ := hn
      rw [moduleModes_intCast, show ((k : ℂ) - 1) = ((k - 1 : ℤ) : ℂ) by push_cast; ring,
        moduleModes_intCast]
      ext x
      have h := act_T_covariance A.toWeakModule u k x
      simp only [WeakModule.act_def] at h
      simpa [OrdVModule.intMode] using h
    · rw [moduleModes_of_not_int A (fun k hk => hn ⟨k, hk⟩),
        moduleModes_of_not_int A (n := n - 1) (fun k hk => hn ⟨k + 1, by push_cast; rw [hk]; ring⟩)]
      simp
  · intro u v x ℓ m n
    by_cases hn : ∃ k : ℤ, (k : ℂ) = n
    · obtain ⟨k, rfl⟩ := hn
      have h := A.jacobi u v x ℓ m k
      convert h using 2
      · funext i
        rw [show ((k : ℂ) + (i : ℂ)) = ((k + i : ℤ) : ℂ) by push_cast; ring,
          show ((ℓ : ℂ) + (k : ℂ) - (i : ℂ)) = ((ℓ + k - i : ℤ) : ℂ) by push_cast; ring,
          moduleModes_apply_intCast, moduleModes_apply_intCast]
      · funext i
        rw [show ((m : ℂ) + (k : ℂ) - (i : ℂ)) = ((m + k - i : ℤ) : ℂ) by push_cast; ring,
          moduleModes_apply_intCast]
        rfl
    · have hz : ∀ j : ℤ, moduleModes A (n + j) = 0 := fun j =>
        moduleModes_of_not_int A (fun k hk => hn ⟨k - j, by push_cast; rw [hk]; ring⟩)
      have h1 : ∀ i : ℤ, moduleModes A (n + i) = 0 := hz
      have h2 : ∀ i : ℤ, moduleModes A (ℓ + n - i) = 0 := fun i => by
        rw [show (ℓ : ℂ) + n - i = n + ((ℓ - i : ℤ) : ℂ) by push_cast; ring]; exact hz _
      have h3 : ∀ i : ℤ, moduleModes A (m + n - i) = 0 := fun i => by
        rw [show (m : ℂ) + n - i = n + ((m - i : ℤ) : ℂ) by push_cast; ring]; exact hz _
      simp [h1, h2, h3]

/-- **(b)** `Y_M` as an element of the space of intertwining operators of type `(M / W M)`. -/
noncomputable def moduleIntertwiner (A : OrdVModule W M) :
    IntertwiningOperator (adjointModule W) A A :=
  ⟨moduleModes A, isIntertwiningOperator_moduleModes A⟩

/-- Non-vacuity: on a nonzero module, `Y_M ≠ 0` (its `(-1)`-mode on the vacuum is the identity). -/
theorem moduleIntertwiner_ne_zero (A : OrdVModule W M) [Nontrivial M] :
    moduleIntertwiner A ≠ 0 := by
  intro h
  obtain ⟨x, hx⟩ := exists_ne (0 : M)
  have h1 : (moduleIntertwiner A : IntertwiningModes 𝒱 M M) ((-1 : ℤ) : ℂ) W.vacuum x = x := by
    change moduleModes A ((-1 : ℤ) : ℂ) W.vacuum x = x
    rw [moduleModes_apply_intCast, ← WeakModule.act_def, WeakModule.act_vacuum, if_pos rfl]
  rw [h] at h1
  exact hx (by simpa using h1.symm)

instance (A : OrdVModule W M) [Nontrivial M] :
    Nontrivial (IntertwiningOperator (adjointModule W) A A) :=
  ⟨⟨moduleIntertwiner A, 0, moduleIntertwiner_ne_zero A⟩⟩

/-- `N^M_{W M} ≥ 1` for a nonzero module `M`, **given** that the intertwiner space is
finite-dimensional (not yet proved; see the module docstring). -/
theorem one_le_fusionRule_adjoint (A : OrdVModule W M) [Nontrivial M]
    [FiniteDimensional ℂ (IntertwiningOperator (adjointModule W) A A)] :
    1 ≤ fusionRule (adjointModule W) A A :=
  (_root_.Module.finrank_pos_iff_of_free ℂ _).mpr inferInstance

end ModuleY

end VOA
