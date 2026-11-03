/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchDLM3Induced
import VOA.Modules.ZhuVermaAnArchIterateNonneg

/-!
# DLM3 Theorem 4.1, part II — the module identity and the universal property of `M̄_n(U)`

Dong–Li–Mason, *Vertex operator algebras and associative algebras*, J. Algebra **206** (1998)
67–96 (arXiv `q-alg/9612010v2`), Theorem 4.1 asserts three things about the induced/defect quotient
`M̄_n(U) = M_n(U)/U(V̂)W`:

> "The space `M̄_n(U)` is an admissible `V`-module … with `M̄_n(U)(0) ≠ 0`, `M̄_n(U)(n) = U` and
> with the following universal property: for any weak `V`-module `M` and any `A_n(V)`-morphism
> `φ : U → Ω_n(M)`, there is a unique morphism `φ̄ : M̄_n(U) → M` of weak `V`-modules which extends
> `φ`."

`ZhuVermaAnArchDLM3Induced` built the carrier `M_n(U) = U(V̂) ⊗_{U(P_n)} U` (DLM3 (4.1)), its
`V̂`-representation `indRho` (DLM3 (4.2)), and the two module-field properties
(`ind_actModeTruncated`, `ind_vacuumCreation`).  **This file supplies the module identity and the
universal property.**

## What is proved here

* **The iterate identity.**  `ind_moduleIterate_nonneg` records that the *whole* `ℓ ≥ 0` half of
  `ModuleIterate` already holds on `M_n(U)` itself, before any quotient — it is
  `moduleIterate_nonneg` specialized to `indRho P`, whose only input is truncation.  The genuine
  content sits at `ℓ < 0` and is exactly what DLM3 (4.3)–(4.4) quotient in; on the defect quotient
  it is `indBar_moduleIterate` (unconditional), hence `indBar_isModuleJacobi`, hence
  `indBarWeakModule` (already assembled in `ZhuVermaAnArchDLM3Induced`).
* **The bottom map.**  `indBottom P : U →ₗ[ℂ] M_n(U)`, `u ↦ [1 ⊗ u]`, and its quotient
  `indBarBottom P : U →ₗ[ℂ] M̄_n(U)`.  Two theorems about it:
  - `indBottom_equivariant` / `indBarBottom_equivariant`: it **intertwines** the `P_n`-action on
    `U` with the `V̂`-action.  On degree-`0` generators `a(wt a − 1)` — DLM3's `o(a)` — this reads
    `o(a)·[1 ⊗ u] = [1 ⊗ a·u]`, i.e. `A_n(𝒱)`-equivariance *modulo* DLM3 Proposition 3.1
    (`V̂(0) ↠ A_n(𝒱)`, which is **not** built in this repo — see the module docstring caveat).
  - `indBarBottom_mem_omegaN`: its image lies in `Ω_n(M̄_n(U))` (DLM3 (3.3)), the space of `n`-th
    lowest-weight vectors.
* **The universal property** (`indLift`, `indLift_bottom`, `indLift_intertwine`,
  `indLift_unique`; and after descent `indBarLift`, `indBarLift_bottom`, `indBarLift_intertwine`,
  `indBarLift_unique`).  The descent through the defect submodule is
  `defectSubmodule_le_ker_indLift`, whose engine is the new general transport lemma
  `VHatRep.defectVec_map` (a `V̂`-map carries iterate defects to iterate defects — the
  common generalization of the proved `defectVec_quotientRep_mk`).
* **The exact obstruction to `M̄_n(U)(n) = U`.**  `indBarBottom_injective_iff`: the bottom map is
  injective **iff** `U` admits a *separating realization* — a `V̂`-representation satisfying
  `ModuleIterate` (equivalently: a weak `𝒱`-module) together with an injective `P_n`-equivariant
  map from `U`.  This is DLM3's "enough modules" statement isolated as a clean equivalence: the
  `⇐` direction is the universal property, the `⇒` direction is `M̄_n(U)` itself.

## What is **not** proved

DLM3 obtain `J ∩ U = 0` (hence injectivity of the bottom map, hence `M̄_n(U)(n) = U`) from the
explicit `U*`/length-filtration pairing (4.5) together with Propositions 4.3, 4.6, 4.7 — of which
Proposition 4.6 has **no printed proof anywhere** (DLM3 defer it wholesale to [DLM] Prop 6.1).
Nothing of that package is formalized; `indBarBottom_injective_iff` names the exact missing input
and is *not* discharged.  Likewise `M̄_n(U)(0) ≠ 0` is untouched (it is the only use DLM3 make of
their standing hypothesis "`U` cannot factor through `A_{n-1}(V)`", which Dong–Jiang explicitly
drop).

Everything here is `sorry`-free, `pbw`-free and `#print axioms`-clean
(`[propext, Classical.choice, Quot.sound]`).

## References
DLM3 (`q-alg/9612010v2`) §3 (3.3), §4 (4.1)–(4.5), Thm 4.1, Props 4.3/4.6/4.7;
`ZhuVermaAnArchDLM3Induced` (`IndMod`, `indRho`, `ind_generation`, `IndBar`, `indBarWeakModule`),
`ZhuVermaAnArchDLM3Deg` (`Pn`, `deepPart`), `ZhuVermaAnArchMUjacobi` (`ModuleIterate`),
`ZhuVermaAnArchIterateNonneg` (`moduleIterate_nonneg`),
`ZhuVermaAnArchMUjacobiClose` (`defectVec`, `defectSubmodule`, `moduleIterate_quotientRep`).
-/

namespace VOA

open VertexOperatorAlgebra
open Module (End)
open scoped BigOperators TensorProduct

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace VHat
namespace VHatRep

variable {W : VertexOperatorAlgebra 𝒱}
variable {M : Type u} [AddCommGroup M] [Module ℂ M]
variable {N : Type u} [AddCommGroup N] [Module ℂ N]

/-! ## Transport of iterate defects along a `V̂`-map

The one general fact needed to descend the universal property through the defect quotient: a linear
map intertwining two `V̂`-representations sends the iterate defect of the source to the iterate
defect of the target.  This is the common generalization of the proved `defectVec_quotientRep_mk`
(which is the case `f = mkQ`). -/

/-- **A `V̂`-map transports iterate defects.**  If `f` intertwines `ρ` and `ρ'` then
`f (δ_ρ(u,v,z,ℓ,K)) = δ_{ρ'}(u,v,f z,ℓ,K)`.  (Truncation of `ρ` supplies the finiteness needed to
push `f` through the defect `finsum`.) -/
theorem defectVec_map (ρ : VHatRep W M) (ρ' : VHatRep W N) (f : M →ₗ[ℂ] N)
    (hf : ∀ (x : VHatCarrier W) (z : M), f (ρ x z) = ρ' x (f z))
    (htr : ActModeTruncated ρ) (u v : 𝒱) (z : M) (ℓ K : ℤ) :
    f (defectVec ρ u v z ℓ K) = defectVec ρ' u v (f z) ℓ K := by
  have hmode : ∀ (a : 𝒱) (m : ℤ) (y : M), f (ρ.actMode a m y) = ρ'.actMode a m (f y) :=
    fun a m y => hf (gen W a m) y
  obtain ⟨Nv, hNv⟩ := htr v z
  obtain ⟨Nu, hNu⟩ := htr u z
  -- finite support of the source summand family
  have hfinM : (Function.support fun i : ℤ =>
      (negOnePow i * cbz ℓ i) •
        (ρ.actMode u (ℓ - i) (ρ.actMode v (K + i) z)
          - negOnePow ℓ • ρ.actMode v (ℓ + K - i) (ρ.actMode u i z))).Finite := by
    apply Set.Finite.subset (Set.finite_Icc 0 (max (Nv - K) Nu))
    intro i hi
    rw [Function.mem_support] at hi; rw [Set.mem_Icc]
    refine ⟨not_lt.mp fun h => hi ?_, not_lt.mp fun h => hi ?_⟩
    · rw [cbz_apply_neg ℓ h, mul_zero, zero_smul]
    · rw [hNv (K + i) (by omega), map_zero, hNu i (by omega), map_zero]
      simp
  rw [defectVec, defectVec, map_sub, hmode, map_finsum f hfinM]
  congr 1
  exact finsum_congr fun i => by simp only [map_smul, map_sub, hmode]

end VHatRep

namespace DLM3

variable {W : VertexOperatorAlgebra 𝒱} {n : ℕ} {U : Type u} [AddCommGroup U] [Module ℂ U]
variable {M : Type u} [AddCommGroup M] [Module ℂ M]

/-! ## (a) The iterate identity for the DLM3 representation -/

/-- **The `ℓ ≥ 0` half of `ModuleIterate` holds on `M_n(U)` itself** — before *any* quotient.  Its
only input is the module-field property `ind_actModeTruncated`: the `ℓ = 0` slice is locality
(`actMode_bracket`, free for a `V̂`-representation) and the inverted Pascal recursion propagates it
upward in `ℓ` (`moduleIterate_nonneg`).  Consequently the entire genuine content of the DLM3
associativity defect (4.3) sits at `ℓ < 0`. -/
theorem ind_moduleIterate_nonneg (P : ParabolicRep W n U) (u v : 𝒱) (z : IndMod P) (j : ℕ)
    (K : ℤ) :
    (indRho P).actMode (W.smul u (j : ℤ) v) K z
      = ∑ᶠ i : ℤ, (negOnePow i * cbz (j : ℤ) i) •
          ((indRho P).actMode u ((j : ℤ) - i) ((indRho P).actMode v (K + i) z)
            - negOnePow (j : ℤ) •
                (indRho P).actMode v ((j : ℤ) + K - i) ((indRho P).actMode u i z)) :=
  moduleIterate_nonneg (indRho P) (ind_actModeTruncated P) u v z j K

/-- **`ModuleIterate` for the DLM3 representation** — i.e. on the defect quotient `M̄_n(U)`, for
*every* `ℓ ∈ ℤ`.  This is DLM3 (4.3)–(4.4) discharged: the `ℓ < 0` content, which is false on
`M_n(U)`, is exactly what the defect submodule divides out. -/
theorem indBar_moduleIterate (P : ParabolicRep W n U) :
    VHatRep.ModuleIterate (indBarRho P) :=
  VHatRep.moduleIterate_quotientRep (indRho P) (ind_actModeTruncated P)

/-- **The module Borcherds identity 5.3.1b for `M̄_n(U)`.**  `ind_moduleIterate_nonneg` supplies the
`ℓ ≥ 0` half free, `indBar_moduleIterate` the rest; `isModuleJacobi_of_iterate` assembles. -/
theorem indBar_isModuleJacobi (P : ParabolicRep W n U) :
    (indBarRho P).IsModuleJacobi :=
  VHatRep.isModuleJacobi_quotientRep (indRho P) (ind_actModeTruncated P)

/-! ## `Ω_n` — the `n`-th lowest weight vectors (DLM3 (3.3)) -/

/-- **DLM3 (3.3)**: `Ω_n(M) = {x ∈ M | V̂(−p)·x = 0 for p > n}`, the space of "`n`-th lowest weight
vectors" of a `V̂`-representation.  (DLM3 print `k ≥ m`; the intended — and here formalized —
condition is on the *deep part* `⨁_{p>n} V̂(−p)`, i.e. degrees `≤ −n−1`.) -/
def omegaN (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (ρ : VHatRep W M) : Submodule ℂ M where
  carrier := {x | ∀ g ∈ deepPart W n, ρ g x = 0}
  add_mem' := by
    intro x y hx hy g hg
    rw [map_add, hx g hg, hy g hg, add_zero]
  zero_mem' := fun g _ => map_zero _
  smul_mem' := by
    intro c x hx g hg
    rw [map_smul, hx g hg, smul_zero]

@[simp] theorem mem_omegaN {ρ : VHatRep W M} {x : M} :
    x ∈ omegaN W n ρ ↔ ∀ g ∈ deepPart W n, ρ g x = 0 := Iff.rfl

/-! ## The bottom map `U → M_n(U)` and its equivariance -/

/-- **The bottom map** `u ↦ [1 ⊗ u]`, `U →ₗ[ℂ] M_n(U)`.  DLM3 write `U ⊆ M_n(U)(n)`; the inclusion
is only *claimed* at the end of their §4, so here it is honestly a linear map whose injectivity is
the open point (`indBarBottom_injective_iff`). -/
noncomputable def indBottom (P : ParabolicRep W n U) : U →ₗ[ℂ] IndMod P :=
  (indMk P).comp (TensorProduct.mk ℂ (UEnv W) U 1)

@[simp] theorem indBottom_apply (P : ParabolicRep W n U) (u : U) :
    indBottom P u = indMk P ((1 : UEnv W) ⊗ₜ[ℂ] u) := rfl

/-- **`P_n`-equivariance of the bottom map** (the defining relation of the induced module).  On a
degree-`0` generator `g = a(wt a − 1)` this is DLM3's `o(a)·[1 ⊗ u] = [1 ⊗ a·u]`, i.e. the
`A_n(𝒱)`-linearity of `u ↦ [1 ⊗ u]` *modulo* DLM3 Proposition 3.1. -/
theorem indBottom_equivariant (P : ParabolicRep W n U) (g : Pn W n) (u : U) :
    indBottom P (P.act g u) = indRho P (g : VHatCarrier W) (indBottom P u) := by
  have hbal := indMk_balance P 1 g u
  rw [one_mul] at hbal
  rw [indBottom_apply, indBottom_apply, indRho_apply, indActEnd_mk, mul_one, ← hbal]

/-- The deep part `⨁_{p>n} V̂(−p)` annihilates the bottom of `M_n(U)`: `[1 ⊗ u] ∈ Ω_n(M_n(U))`. -/
theorem indBottom_mem_omegaN (P : ParabolicRep W n U) (u : U) :
    indBottom P u ∈ omegaN W n (indRho P) := by
  intro g hg
  have hgp : g ∈ parabolic W n := deepPart_le_parabolic W n hg
  have h := indBottom_equivariant P (⟨g, hgp⟩ : Pn W n) u
  rw [P.deep_zero (⟨g, hgp⟩ : Pn W n) hg] at h
  simpa using h.symm

/-- **The bottom map of `M̄_n(U)`**, `u ↦ [1 ⊗ u]` composed with the defect quotient.  DLM3's
Theorem 4.1 asserts this map is an isomorphism onto `M̄_n(U)(n)`. -/
noncomputable def indBarBottom (P : ParabolicRep W n U) : U →ₗ[ℂ] IndBar P :=
  (VHatRep.defectSubmodule (indRho P)).mkQ.comp (indBottom P)

@[simp] theorem indBarBottom_apply (P : ParabolicRep W n U) (u : U) :
    indBarBottom P u = Submodule.Quotient.mk (indBottom P u) := rfl

/-- `P_n`-equivariance of the bottom map of `M̄_n(U)`. -/
theorem indBarBottom_equivariant (P : ParabolicRep W n U) (g : Pn W n) (u : U) :
    indBarBottom P (P.act g u) = indBarRho P (g : VHatCarrier W) (indBarBottom P u) := by
  rw [indBarBottom_apply, indBarBottom_apply, indBottom_equivariant P g u, indBarRho,
    VHatRep.quotientRep_mk]

/-- `[1 ⊗ u] ∈ Ω_n(M̄_n(U))` — the bottom of the defect quotient consists of `n`-th lowest weight
vectors (DLM3 (3.3)). -/
theorem indBarBottom_mem_omegaN (P : ParabolicRep W n U) (u : U) :
    indBarBottom P u ∈ omegaN W n (indBarRho P) := by
  intro g hg
  rw [indBarBottom_apply, indBarRho, VHatRep.quotientRep_mk,
    indBottom_mem_omegaN P u g hg, Submodule.Quotient.mk_zero]

/-! ## The universal property of `M_n(U)` (Lie induction) -/

variable {ρ' : VHatRep W M}

/-- The bilinear datum `(y, u) ↦ ρ'(y)·φ(u)` underlying the induced-module lift. -/
noncomputable def indLiftBil (ρ' : VHatRep W M) (φ : U →ₗ[ℂ] M) : UEnv W →ₗ[ℂ] (U →ₗ[ℂ] M) where
  toFun y := (ρ'.toAlgHom y).comp φ
  map_add' y z := by
    refine LinearMap.ext fun u => ?_
    rw [map_add]
    rfl
  map_smul' c y := by
    refine LinearMap.ext fun u => ?_
    rw [map_smul]
    rfl

@[simp] theorem indLiftBil_apply (ρ' : VHatRep W M) (φ : U →ₗ[ℂ] M) (y : UEnv W) (u : U) :
    indLiftBil ρ' φ y u = ρ'.toAlgHom y (φ u) := rfl

/-- The lift on the `ℂ`-linear cover `U(V̂) ⊗_ℂ U`. -/
noncomputable def indLiftCover (ρ' : VHatRep W M) (φ : U →ₗ[ℂ] M) : IndCover W U →ₗ[ℂ] M :=
  TensorProduct.lift (indLiftBil ρ' φ)

@[simp] theorem indLiftCover_tmul (ρ' : VHatRep W M) (φ : U →ₗ[ℂ] M) (y : UEnv W) (u : U) :
    indLiftCover ρ' φ (y ⊗ₜ[ℂ] u) = ρ'.toAlgHom y (φ u) :=
  TensorProduct.lift.tmul _ _

/-- The `U(P_n)`-balancing relations are killed by the lift, exactly because `φ` is
`P_n`-equivariant. -/
theorem balancing_le_ker_indLiftCover (P : ParabolicRep W n U) (ρ' : VHatRep W M) (φ : U →ₗ[ℂ] M)
    (hφ : ∀ (g : Pn W n) (u : U), φ (P.act g u) = ρ' (g : VHatCarrier W) (φ u)) :
    balancing P ≤ LinearMap.ker (indLiftCover ρ' φ) := by
  refine Submodule.span_le.mpr ?_
  rintro t ⟨y, g, u, rfl⟩
  rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub, indLiftCover_tmul, indLiftCover_tmul,
    map_mul, hφ g u, VHatRep.toAlgHom_uι]
  rw [Module.End.mul_apply, sub_self]

/-- **The universal property of the induced module `M_n(U)` (Lie induction).**  Given a
`V̂`-representation `ρ'` on `M` and a `P_n`-equivariant `φ : U → M`, there is a `ℂ`-linear
`M_n(U) → M` sending `[y ⊗ u]` to `ρ'(y)·φ(u)`.  It intertwines the `V̂`-actions
(`indLift_intertwine`), extends `φ` (`indLift_bottom`), and is the *unique* such map
(`indLift_unique`). -/
noncomputable def indLift (P : ParabolicRep W n U) (ρ' : VHatRep W M) (φ : U →ₗ[ℂ] M)
    (hφ : ∀ (g : Pn W n) (u : U), φ (P.act g u) = ρ' (g : VHatCarrier W) (φ u)) :
    IndMod P →ₗ[ℂ] M :=
  Submodule.liftQ (balancing P) (indLiftCover ρ' φ) (balancing_le_ker_indLiftCover P ρ' φ hφ)

@[simp] theorem indLift_mk (P : ParabolicRep W n U) (ρ' : VHatRep W M) (φ : U →ₗ[ℂ] M)
    (hφ : ∀ (g : Pn W n) (u : U), φ (P.act g u) = ρ' (g : VHatCarrier W) (φ u))
    (y : UEnv W) (u : U) :
    indLift P ρ' φ hφ (indMk P (y ⊗ₜ[ℂ] u)) = ρ'.toAlgHom y (φ u) :=
  indLiftCover_tmul ρ' φ y u

/-- The lift **extends `φ`**: it sends `[1 ⊗ u]` to `φ u`. -/
@[simp] theorem indLift_bottom (P : ParabolicRep W n U) (ρ' : VHatRep W M) (φ : U →ₗ[ℂ] M)
    (hφ : ∀ (g : Pn W n) (u : U), φ (P.act g u) = ρ' (g : VHatCarrier W) (φ u)) (u : U) :
    indLift P ρ' φ hφ (indBottom P u) = φ u := by
  rw [indBottom_apply, indLift_mk, map_one]
  rfl

/-- The lift **intertwines the `V̂`-actions**. -/
theorem indLift_intertwine (P : ParabolicRep W n U) (ρ' : VHatRep W M) (φ : U →ₗ[ℂ] M)
    (hφ : ∀ (g : Pn W n) (u : U), φ (P.act g u) = ρ' (g : VHatCarrier W) (φ u))
    (x : VHatCarrier W) (z : IndMod P) :
    indLift P ρ' φ hφ (indRho P x z) = ρ' x (indLift P ρ' φ hφ z) := by
  have hcomp : (indLift P ρ' φ hφ).comp (indActEnd P x)
      = (ρ' x).comp (indLift P ρ' φ hφ) := by
    refine indMod_ext fun y u => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, indActEnd_mk, indLift_mk, indLift_mk,
      map_mul, VHatRep.toAlgHom_uι, Module.End.mul_apply]
  exact LinearMap.congr_fun hcomp z

/-- **Uniqueness** in the universal property of `M_n(U)`: a `V̂`-equivariant map out of `M_n(U)`
is determined by its restriction to the bottom `1 ⊗ U` (`ind_generation`). -/
theorem indLift_unique (P : ParabolicRep W n U) (ρ' : VHatRep W M) (φ : U →ₗ[ℂ] M)
    (hφ : ∀ (g : Pn W n) (u : U), φ (P.act g u) = ρ' (g : VHatCarrier W) (φ u))
    (f : IndMod P →ₗ[ℂ] M) (hbot : ∀ u : U, f (indBottom P u) = φ u)
    (hint : ∀ (x : VHatCarrier W) (z : IndMod P), f (indRho P x z) = ρ' x (f z)) :
    f = indLift P ρ' φ hφ := by
  have hker : LinearMap.ker (f - indLift P ρ' φ hφ) = ⊤ := by
    refine ind_generation P _ (fun u => ?_) (fun x z hz => ?_)
    · rw [LinearMap.mem_ker, LinearMap.sub_apply]
      have h1 : f (indBottom P u) = φ u := hbot u
      have h2 : indLift P ρ' φ hφ (indBottom P u) = φ u := indLift_bottom P ρ' φ hφ u
      rw [indBottom_apply] at h1 h2
      rw [h1, h2, sub_self]
    · rw [LinearMap.mem_ker, LinearMap.sub_apply] at hz ⊢
      rw [hint x z, indLift_intertwine P ρ' φ hφ x z, ← map_sub, hz, map_zero]
  refine LinearMap.ext fun z => ?_
  have hz : z ∈ LinearMap.ker (f - indLift P ρ' φ hφ) := by rw [hker]; trivial
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at hz
  exact hz

/-! ## Descent to `M̄_n(U)` — the universal property of DLM3 Theorem 4.1 -/

/-- If the target satisfies the iterate identity (equivalently, is a genuine weak `𝒱`-module), the
lift kills the defect submodule: `ker` is a `V̂`-invariant submodule containing every defect vector
(`defectVec_map`), hence contains the smallest one. -/
theorem defectSubmodule_le_ker_indLift (P : ParabolicRep W n U) (ρ' : VHatRep W M)
    (hit : VHatRep.ModuleIterate ρ') (φ : U →ₗ[ℂ] M)
    (hφ : ∀ (g : Pn W n) (u : U), φ (P.act g u) = ρ' (g : VHatCarrier W) (φ u)) :
    VHatRep.defectSubmodule (indRho P) ≤ LinearMap.ker (indLift P ρ' φ hφ) := by
  refine sInf_le ⟨?_, ?_⟩
  · rintro t ⟨a, b, z, ℓ, K, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker,
      VHatRep.defectVec_map (indRho P) ρ' (indLift P ρ' φ hφ)
        (indLift_intertwine P ρ' φ hφ) (ind_actModeTruncated P) a b z ℓ K,
      (VHatRep.moduleIterate_iff_defectVec_zero ρ').mp hit]
  · intro x d hd
    rw [LinearMap.mem_ker] at hd ⊢
    rw [indLift_intertwine P ρ' φ hφ x d, hd, map_zero]

/-- **The universal property of `M̄_n(U)` — DLM3 Theorem 4.1, third clause.**  For any
`V̂`-representation `ρ'` satisfying the iterate identity (i.e. any weak `𝒱`-module) and any
`P_n`-equivariant `φ : U → M`, there is a unique `V̂`-map `M̄_n(U) → M` extending `φ`. -/
noncomputable def indBarLift (P : ParabolicRep W n U) (ρ' : VHatRep W M)
    (hit : VHatRep.ModuleIterate ρ') (φ : U →ₗ[ℂ] M)
    (hφ : ∀ (g : Pn W n) (u : U), φ (P.act g u) = ρ' (g : VHatCarrier W) (φ u)) :
    IndBar P →ₗ[ℂ] M :=
  Submodule.liftQ (VHatRep.defectSubmodule (indRho P)) (indLift P ρ' φ hφ)
    (defectSubmodule_le_ker_indLift P ρ' hit φ hφ)

@[simp] theorem indBarLift_mk (P : ParabolicRep W n U) (ρ' : VHatRep W M)
    (hit : VHatRep.ModuleIterate ρ') (φ : U →ₗ[ℂ] M)
    (hφ : ∀ (g : Pn W n) (u : U), φ (P.act g u) = ρ' (g : VHatCarrier W) (φ u))
    (z : IndMod P) :
    indBarLift P ρ' hit φ hφ (Submodule.Quotient.mk z) = indLift P ρ' φ hφ z := rfl

/-- The descended lift extends `φ`. -/
@[simp] theorem indBarLift_bottom (P : ParabolicRep W n U) (ρ' : VHatRep W M)
    (hit : VHatRep.ModuleIterate ρ') (φ : U →ₗ[ℂ] M)
    (hφ : ∀ (g : Pn W n) (u : U), φ (P.act g u) = ρ' (g : VHatCarrier W) (φ u)) (u : U) :
    indBarLift P ρ' hit φ hφ (indBarBottom P u) = φ u := by
  rw [indBarBottom_apply, indBarLift_mk, indLift_bottom]

/-- The descended lift intertwines the `V̂`-actions. -/
theorem indBarLift_intertwine (P : ParabolicRep W n U) (ρ' : VHatRep W M)
    (hit : VHatRep.ModuleIterate ρ') (φ : U →ₗ[ℂ] M)
    (hφ : ∀ (g : Pn W n) (u : U), φ (P.act g u) = ρ' (g : VHatCarrier W) (φ u))
    (x : VHatCarrier W) (z : IndBar P) :
    indBarLift P ρ' hit φ hφ (indBarRho P x z) = ρ' x (indBarLift P ρ' hit φ hφ z) := by
  refine Submodule.Quotient.induction_on _ z (fun y => ?_)
  rw [indBarRho, VHatRep.quotientRep_mk, indBarLift_mk, indBarLift_mk, indRho_apply,
    ← indRho_apply, indLift_intertwine]

/-- **Uniqueness** in the universal property of `M̄_n(U)`. -/
theorem indBarLift_unique (P : ParabolicRep W n U) (ρ' : VHatRep W M)
    (hit : VHatRep.ModuleIterate ρ') (φ : U →ₗ[ℂ] M)
    (hφ : ∀ (g : Pn W n) (u : U), φ (P.act g u) = ρ' (g : VHatCarrier W) (φ u))
    (f : IndBar P →ₗ[ℂ] M) (hbot : ∀ u : U, f (indBarBottom P u) = φ u)
    (hint : ∀ (x : VHatCarrier W) (z : IndBar P), f (indBarRho P x z) = ρ' x (f z)) :
    f = indBarLift P ρ' hit φ hφ := by
  have hcomp : f.comp (VHatRep.defectSubmodule (indRho P)).mkQ = indLift P ρ' φ hφ := by
    refine indLift_unique P ρ' φ hφ _ (fun u => ?_) (fun x z => ?_)
    · rw [LinearMap.comp_apply]
      exact hbot u
    · rw [LinearMap.comp_apply, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.mkQ_apply,
        show (Submodule.Quotient.mk (indRho P x z) : IndBar P)
            = indBarRho P x (Submodule.Quotient.mk z) from
          (VHatRep.quotientRep_mk (indRho P) _ _ x z).symm]
      exact hint x _
  refine LinearMap.ext fun z => ?_
  refine Submodule.Quotient.induction_on _ z (fun y => ?_)
  have := LinearMap.congr_fun hcomp y
  rw [LinearMap.comp_apply, Submodule.mkQ_apply] at this
  rw [this, indBarLift_mk]

/-! ## The exact obstruction to `M̄_n(U)(n) = U` -/

/-- **A separating realization of `U` at level `n`**: a `V̂`-representation which is a genuine weak
`𝒱`-module (truncated + iterate identity) together with an *injective* `P_n`-equivariant map from
`U`.  This is DLM3's "there are enough modules" input, isolated. -/
structure Realization (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (U : Type u) [AddCommGroup U]
    [Module ℂ U] (P : ParabolicRep W n U) : Type (u + 1) where
  /-- The underlying space of the realizing module. -/
  carrier : Type u
  /-- Its additive structure. -/
  [carrierAddCommGroup : AddCommGroup carrier]
  /-- Its `ℂ`-module structure. -/
  [carrierModule : Module ℂ carrier]
  /-- The `V̂`-representation. -/
  rho : VHatRep W carrier
  /-- The module-field (lower truncation) property. -/
  truncated : VHatRep.ActModeTruncated rho
  /-- The iterate identity — equivalently, `rho` is a genuine weak `𝒱`-module. -/
  iterate : VHatRep.ModuleIterate rho
  /-- The realizing map. -/
  emb : U →ₗ[ℂ] carrier
  /-- `P_n`-equivariance of the realizing map. -/
  equivariant : ∀ (g : Pn W n) (u : U), emb (P.act g u) = rho (g : VHatCarrier W) (emb u)

attribute [instance] Realization.carrierAddCommGroup Realization.carrierModule

/-- A realization **separates** `U` when its realizing map is injective. -/
def Realization.Separates {P : ParabolicRep W n U} (R : Realization W n U P) : Prop :=
  Function.Injective R.emb

/-- `M̄_n(U)` is itself a realization of `U` (the tautological one). -/
noncomputable def indBarRealization (P : ParabolicRep W n U) : Realization W n U P where
  carrier := IndBar P
  rho := indBarRho P
  truncated := indBar_actModeTruncated P
  iterate := indBar_moduleIterate P
  emb := indBarBottom P
  equivariant := indBarBottom_equivariant P

/-- **The exact obstruction to DLM3's `M̄_n(U)(n) = U`.**  The bottom map `U → M̄_n(U)` is injective
**iff** `U` admits a separating realization.

`⇐` is the universal property (`indBarLift_bottom`: the lift retracts the bottom map onto the
realizing map); `⇒` is the tautological realization `M̄_n(U)` itself.

DLM3 discharge the right-hand side by their `U*`/length-filtration pairing (4.5) and the radical
`J`, whose key step (Proposition 4.6) they defer wholesale to [DLM] Proposition 6.1; **none of that
is formalized here**, so this equivalence is a faithful statement of what remains, not a proof of
it. -/
theorem indBarBottom_injective_iff (P : ParabolicRep W n U) :
    Function.Injective (indBarBottom P) ↔ ∃ R : Realization W n U P, R.Separates := by
  constructor
  · intro h
    exact ⟨indBarRealization P, h⟩
  · rintro ⟨R, hR⟩
    have hretract : ∀ u : U,
        indBarLift P R.rho R.iterate R.emb R.equivariant (indBarBottom P u) = R.emb u :=
      indBarLift_bottom P R.rho R.iterate R.emb R.equivariant
    intro u₁ u₂ h12
    refine hR ?_
    rw [← hretract u₁, ← hretract u₂, h12]

end DLM3

end VHat

end VOA

-- Axiom check (axiom-clean: [propext, Classical.choice, Quot.sound]).
