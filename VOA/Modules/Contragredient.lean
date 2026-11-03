/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.Character
import VOA.Core.BilinearForm
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Contragredient and unitary modules  (Gannon §5.3.1, p. 332)

The module-level analogue of the invariant bilinear form (`Core.BilinearForm`); in RCFT the
contragredient is the charge-conjugate / anti-particle.

* **Restricted dual** (eq. 5.3.4a): for a graded module `M = ⊕_α M_α`, the *graded* dual
  `M* := ⊕_α (M_α)*` (smaller than the full dual in infinite dimensions). Built here as
  `RestrictedDual` (a genuine `⨁`-type).
* **Graded dimension** (eq. 5.3.4b): `χ_{M*}(τ) = χ_M(τ)` — proved here
  (`contragredient_gradedDim`) since `dim (M_α)* = dim M_α`. (So graded dimensions do *not*
  always distinguish modules — `M* ≇ M` in general, yet `χ_{M*} = χ_M`.)
* **Unitary / self-contragredient** predicates (eq. 5.3.5b): an invariant Hermitian form;
  `SelfContragredient` records `M ≅ M*`.

## Status

Full module structure **unconditional** (module FHL → CanPStep; Li 1994 / FHL, Mem. AMS 104
(1993) no. 494): the fully-discharged contragredient is `ContragredientClose.contragredientModule N
: OrdVModule W (RestrictedDual N)`, axiom-clean, built from the proved `dualAdjResidualMvec_holds`.

Axiom-clean for the **restricted dual and the character equality**: `RestrictedDual`, its
graded dimension `contragredientGradedDim`, **`contragredient_gradedDim`** (5.3.4b), and the
`Unitary` / `SelfContragredient` predicates.

The **full contragredient module action** `contragredient N hJac : OrdVModule W (RestrictedDual N)`
is **assembled** (in `Modules.ContragredientJacobi`, off the `dualModeEndo` engine of
`Modules.ContragredientAction`): the transpose action twisted by `e^{zL₁}(-z⁻²)^{L₀}` (eq. 5.1.11a),
a genuine graded `OrdVModule`, parametric in the hypothesis `ContragredientJacobi N` (the
module Jacobi 5.3.1b ⟸ the module-level FHL/`ι_z` full-invariance). Its engine (`L₁` local
nilpotence and the exponential `e^{zL₁}`) is the proved `Core.BilinearForm.L_one_pow_eq_zero` /
`Core.Automorphism.expEquiv`. **`ContragredientJacobi N` itself is proved** unconditionally,
axiom-clean (`Modules.ContragredientClose`, `contragredientJacobi_holds`), so `contragredient N
(contragredientJacobi_holds N)` is unconditional. The one-point refinement `χ_{M*}(τ,v) = (-1)ⁿ χ_M(τ,v)` is **proved**
(in `Modules.ContragredientCharacter`, `onePoint_contragredient`) *exactly* for **quasi-primary**
`v ∈ 𝒱ₙ` (`L₁v = 0`), riding on `contragredient N hJac`; it carries explicit `L₁`-correction terms
for general `v` (that general form is not proved here).

## Dependencies
* `VOA.Modules.Character`, `Core.BilinearForm`; `Mathlib.LinearAlgebra.Dual.Lemmas`.

## References
* Gannon §5.3.1, eqs. (5.3.4)–(5.3.5); Frenkel–Huang–Lepowsky [199]; Li [380].
-/

namespace VOA

open Module (End Dual)
open scoped BigOperators
open Classical

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
variable {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M]

/-! ## The restricted dual `M* = ⊕_α (M_α)*` (5.3.4a) -/

/-- The **restricted dual** `M* := ⊕_α (M_α)*` of a graded module (Gannon 5.3.4a): the
*graded* dual, `⨁` of the duals of the (finite-dimensional) weight spaces. -/
def RestrictedDual (N : OrdVModule W M) : Type u := DirectSum ℂ (fun α => Module.Dual ℂ (N.weight α))

noncomputable instance (N : OrdVModule W M) : AddCommGroup (RestrictedDual N) :=
  inferInstanceAs (AddCommGroup (DirectSum ℂ (fun α => Module.Dual ℂ (N.weight α))))

noncomputable instance (N : OrdVModule W M) : Module ℂ (RestrictedDual N) :=
  inferInstanceAs (Module ℂ (DirectSum ℂ (fun α => Module.Dual ℂ (N.weight α))))

/-- The `α`-weight space of the contragredient: `(M*)_α = (M_α)*`, sitting inside `M*` via
`DirectSum.lof`. -/
noncomputable def RestrictedDual.weight (N : OrdVModule W M) (α : ℂ) :
    Submodule ℂ (RestrictedDual N) :=
  LinearMap.range (DirectSum.lof ℂ ℂ (fun β => Module.Dual ℂ (N.weight β)) α)

/-! ## Graded dimension: `χ_{M*} = χ_M` (5.3.4b) -/

/-- The graded dimension of the contragredient `M*`: the coefficient of `q^e` is
`dim (M_{e+c/24})*` (Gannon 5.3.4b). -/
noncomputable def contragredientGradedDim (N : OrdVModule W M) : FormalQSeries :=
  fun e => (Module.finrank ℂ (Module.Dual ℂ (N.weight (e + W.centralCharge / 24))) : ℂ)

/-- **`χ_{M*}(τ) = χ_M(τ)`** (Gannon 5.3.4b): the contragredient has the *same* graded
dimension as `M`, because each weight space and its dual have equal dimension. (Hence
graded dimensions need not distinguish `M` from `M*`.) -/
theorem contragredient_gradedDim (N : OrdVModule W M) :
    contragredientGradedDim N = gradedDim N := by
  funext e
  simp only [contragredientGradedDim, gradedDim]
  haveI := N.finrank (e + W.centralCharge / 24)
  rw [Subspace.dual_finrank_eq]

/-! ## Unitary and self-contragredient modules (5.3.5b) -/

/-- A **unitary module** (Gannon 5.3.5b): a positive-definite invariant Hermitian form
`(u x | y)_M = (x | u* y)_M`. (`star` is the VOA's anti-linear involution.) -/
structure Unitary [StarRing ℂ] (N : OrdVModule W M) where
  /-- The Hermitian form. -/
  form : M →ₗ[ℂ] M →ₗ[ℂ] ℂ
  /-- Invariance under the action twisted by the star involution `u ↦ u*`. -/
  invariant : ∀ (u : 𝒱) (n : ℤ) (x y : M),
    form (N.toWeakModule.act u n x) y = form x (N.toWeakModule.act u n y)
  /-- Positive-definiteness on the real diagonal. -/
  posDef : ∀ x : M, x ≠ 0 → form x x ≠ 0

/-- `M` is **self-contragredient** if it is isomorphic to its restricted dual `M*` (as a
graded space; the full module iso rides on the contragredient action — see status). -/
def SelfContragredient (N : OrdVModule W M) : Prop :=
  Nonempty (M ≃ₗ[ℂ] RestrictedDual N)

/-!
### `contragredient` (the module action) and `χ_{M*}(τ,v) = (-1)ⁿχ_M(τ,v)` — done downstream

The `𝒱`-module structure on `M*` is the transpose action twisted by `e^{zL₁}(-z⁻²)^{L₀}`
(Gannon 5.1.11a, the module analogue of the invariant form): for `f ∈ M*`,
`⟨Y_{M*}(u,z) f, x⟩ = ⟨f, Y_M(e^{zL₁}(-z⁻²)^{L₀} u, z⁻¹) x⟩`.  It is constructed, with the module
Jacobi identity, in `Modules/ContragredientClose.lean` (`contragredientModule`,
`contragredientJacobi_holds`), and the one-point refinement `χ_{M*}(τ,v) = (-1)ⁿ χ_M(τ,v)` is
`onePoint_contragredient_holds` (`Modules/ContragredientCharacterClose.lean`).
-/

end VOA
