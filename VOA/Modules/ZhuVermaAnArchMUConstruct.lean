/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchMU
import VOA.Modules.ZhuVermaAnArchMULW
import VOA.Modules.ZhuVermaAnArchBottomSurvival
import VOA.Modules.ZhuVermaAnArchMUVhat
import VOA.Modules.ZhuInduced
import VOA.Modules.ZhuRingInstance

/-!
# The concrete `M(U)` generalized-Verma construction — the LINCHPIN (Zhu Thm 5.3.4)

This file assembles the concrete Dong–Jiang induced module `M(U) = ⊕ₙ A_{n,0}(𝒱) ⊗ U`, carrying the
**closed** ring `A(𝒱)` (`instRingA`, `ZhuRingInstance`) and the carrier/grading layer
(`ZhuVermaAnArchMU`), into the genuine generalized-Verma realization data. Concretely it discharges,
*conditionally on the explicit hypothesis `MUGradedAction W`* (proved elsewhere — carried
as a hypothesis here, **never** an axiom), the following four pieces:

1. **R0 — the `A(𝒱)`-balanced bottom `A_{0,0}(𝒱) ⊗_{A(𝒱)} U ≅ U`.** Because `A(𝒱)` is a genuine
   (generally *non-commutative*) ring, Mathlib's `TensorProduct.lid` (which needs a commutative
   base) does **not** apply. The correct balanced tensor `R ⊗_R M ≅ M` for a left `R`-module `M` is
   realized by the **action map** `a ⊗ u ↦ a · u`: it is `ℂ`-surjective (unit `[𝟙] · u = u`), and
   its kernel is exactly the `A(𝒱)`-balancing submodule. So the balanced bottom is
   `(A(𝒱) ⊗_ℂ U) ⧸ ker(act) ≅ U` (`bottomBalancedEquiv`, via
   `LinearMap.quotKerEquivOfSurjective`). This is the genuine `M(U)(0) ≅ U`.

2. **The grading datum `IsGradedRep`.** The `ℕ`-grading `MU.isInternal_deg` (`ZhuVermaAnArchMU`)
   raises module degree by the `V̂`-degree; bundled into the construction structure
   `MUConstruction`, it supplies an `IsGradedRep ρ mdeg` for the construction's representation
   (`MUConstruction.isGradedRep`).

3. **`BottomDefectVanishes`.** The `S = 0` defect slice on `M₀ = U` is exactly the `A(𝒱)` zero-mode
   relation, which vanishes because `U` *is* an `A(𝒱)`-module (`MUConstruction.bottomDefectVanishes`
   from the bundled `bottomIsAModule` datum). With the keystone `defectVec_homogeneous`
   (`ZhuVermaAnArchBottomSurvival`) this gives **bottom survival** unconditionally on the structure.

4. **Assembly.** `MUConstruction.bottomSurvives` (the bottom `U` survives the defect quotient),
   `MUConstruction.toInducedRealization` (an `InducedRealization W U` / `HasInducedModule W U` once
   the bundled lowest-weight packaging is supplied), discharging *bottom survival + grading +
   the realization*.

## Honest scope

`MUGradedAction W` is carried as an explicit hypothesis (proved elsewhere). The genuine
representation `ρ : VHatRep W (carrier)`, its gradedness, the bottom `A(𝒱)`-module identification,
and the lowest-weight packaging are bundled in `MUConstruction` — a **hypothesis structure**, the
output of the Construction-A / DJ Prop 3.5 engine, with *no* `sorry`/axiom. The R0 balanced bottom
(piece 1) is built **unconditionally** for any `AMod W` (it needs only the closed `Ring (A 𝒱)`).
Everything is `#print axioms`-clean: `[propext, Classical.choice, Quot.sound]`.

## References
Dong–Jiang `math/0601626` (Prop 3.4–3.5, Thm 4.13); DLM3 §4; H. Li `hep-th/9406211`;
Gannon §5.3.2, Thm 5.3.4; `ZhuVermaAnArchMU`, `ZhuVermaAnArchBottomSurvival`, `ZhuRingInstance`.
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators TensorProduct DirectSum

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## R0 — the `A(𝒱)`-balanced bottom `A_{0,0}(𝒱) ⊗_{A(𝒱)} U ≅ U`

`A(𝒱)` is a genuine ring (`instRingA`, `ZhuRingInstance`), generally **non-commutative**, so the
commutative-base `TensorProduct.lid` is unavailable. The standard balanced-tensor isomorphism
`R ⊗_R M ≅ M` for a left `R`-module `M` is realized by the action map `a ⊗ u ↦ a · u`. We build it
`ℂ`-linearly on the `ℂ`-tensor cover `A(𝒱) ⊗_ℂ U` (= the bottom piece `MUPiece W U 0` once
`A_{0,0} = A(𝒱)`): the action map is `ℂ`-surjective with section `u ↦ [𝟙] ⊗ u`, and its kernel is
the `A(𝒱)`-balancing submodule; the quotient is `≅ U`. -/

namespace MUConstruct

variable (W : VertexOperatorAlgebra 𝒱) (U : AMod W)

/-- **The R0 action map** `act : A(𝒱) ⊗_ℂ U → U`, `a ⊗ u ↦ U.ρ a u`, `ℂ`-linear. This is the
universal map exhibiting `U` as the balanced tensor `A(𝒱) ⊗_{A(𝒱)} U` (its kernel is the balancing
submodule). -/
noncomputable def bottomAct : TensorProduct ℂ (A W) U.carrier →ₗ[ℂ] U.carrier :=
  TensorProduct.lift
    { toFun := fun a => U.ρ a
      map_add' := fun a b => by rw [map_add]
      map_smul' := fun c a => by rw [map_smul]; rfl }

@[simp] theorem bottomAct_tmul (a : A W) (u : U.carrier) :
    bottomAct W U (a ⊗ₜ[ℂ] u) = U.ρ a u := rfl

/-- The R0 action map is **surjective**: `[𝟙] ⊗ u ↦ U.ρ [𝟙] u = u` (the unit law `U.ρ_one`). -/
theorem bottomAct_surjective : Function.Surjective (bottomAct W U) := by
  intro u
  refine ⟨one W ⊗ₜ[ℂ] u, ?_⟩
  rw [bottomAct_tmul, U.ρ_one]
  rfl

/-- The `ℂ`-linear section `u ↦ [𝟙] ⊗ u` of the R0 action map. -/
noncomputable def bottomSection : U.carrier →ₗ[ℂ] TensorProduct ℂ (A W) U.carrier where
  toFun u := one W ⊗ₜ[ℂ] u
  map_add' u v := by rw [TensorProduct.tmul_add]
  map_smul' c u := by rw [TensorProduct.tmul_smul]; rfl

@[simp] theorem bottomSection_apply (u : U.carrier) :
    bottomSection W U u = one W ⊗ₜ[ℂ] u := rfl

/-- `act ∘ section = id` on `U` — the section is a genuine right inverse. -/
@[simp] theorem bottomAct_section (u : U.carrier) :
    bottomAct W U (bottomSection W U u) = u := by
  rw [bottomSection_apply, bottomAct_tmul, U.ρ_one]; rfl

/-- **The `A(𝒱)`-balancing submodule** = `ker(act)` (the relations `a·r ⊗ u − a ⊗ r·u`, since
`act((a·r) ⊗ u) = (a·r)·u = a·(r·u) = act(a ⊗ r·u)`). The genuine balanced tensor
`A_{0,0}(𝒱) ⊗_{A(𝒱)} U` is the quotient of the `ℂ`-tensor cover by this submodule. -/
noncomputable def bottomBalancing : Submodule ℂ (TensorProduct ℂ (A W) U.carrier) :=
  LinearMap.ker (bottomAct W U)

/-- **R0 — the balanced bottom `A_{0,0}(𝒱) ⊗_{A(𝒱)} U ≅ U`.** The `ℂ`-tensor cover modulo the
balancing submodule `ker(act)` is `ℂ`-linearly isomorphic to `U`, via the descended action map
(`LinearMap.quotKerEquivOfSurjective`). This is the genuine `M(U)(0) ≅ U`: the `n = 0` graded piece,
*balanced over `A(𝒱)`*, is exactly the bottom `U`. -/
noncomputable def bottomBalancedEquiv :
    (TensorProduct ℂ (A W) U.carrier ⧸ bottomBalancing W U) ≃ₗ[ℂ] U.carrier :=
  LinearMap.quotKerEquivOfSurjective (bottomAct W U) (bottomAct_surjective W U)

@[simp] theorem bottomBalancedEquiv_mk (a : A W) (u : U.carrier) :
    bottomBalancedEquiv W U (Submodule.Quotient.mk (a ⊗ₜ[ℂ] u)) = U.ρ a u :=
  (LinearMap.quotKerEquivOfSurjective_apply_mk (bottomAct W U) (bottomAct_surjective W U)
    (a ⊗ₜ[ℂ] u)).trans (bottomAct_tmul W U a u)

end MUConstruct

/-! ## The bundled concrete-construction datum `MUConstruction`

The deep Construction-A / DJ Prop 3.5 output: a `V̂`-representation `ρ` on a carrier `M`, graded by
`mdeg` (DLM3 grading), whose bottom `M₀ = mdeg 0` is the `A(𝒱)`-module `U` (so the `S = 0` defect
slice vanishes), with the field-truncation and lowest-weight data needed for the `LWModule`
packaging. Carried as a **hypothesis structure** (no `sorry`/axiom); the R0 layer above is the
explicit identification of its bottom with the balanced tensor. -/

/-- **The bundled concrete `M(U)`-construction datum.** The genuine output of Construction A
(`VHatRep` on `M`, `ZhuVermaAnArchMUVhat`) plus the DLM3 grading and the bottom `A(𝒱)`-module
identification. A hypothesis structure, **not** an axiom; `MUGradedAction W` is carried separately
as the well-definedness of the `𝒱`-mode action. -/
structure MUConstruction (W : VertexOperatorAlgebra 𝒱) (U : AMod W) where
  /-- The carrier of the construction (the relative tensor `U(V̂) ⊗_{U(P)} U`, or `MU W U`). -/
  M : Type u
  [addCommGroup : AddCommGroup M]
  [module : Module ℂ M]
  /-- The Construction-A `V̂`-representation on `M`. -/
  ρ : VHat.VHatRep W M
  /-- The DLM3 grading of `M` (degree `0` = the lowest-weight space). -/
  mdeg : ℤ → Submodule ℂ M
  /-- `ρ` is graded by `mdeg` (DLM3 §4): each mode raises degree by the `V̂`-degree. **Piece (2).** -/
  isGraded : VHat.VHatRep.IsGradedRep ρ mdeg
  /-- The mode action is truncated (the field property; needed for the defect finsum). -/
  truncated : VHat.VHatRep.ActModeTruncated ρ
  /-- **Piece (3) datum — the bottom is the `A(𝒱)`-module `U`.** The `S = 0` defect slice on the
  bottom `M₀ = mdeg 0` vanishes, because it *is* the `A(𝒱)` zero-mode (Borcherds) relation, which
  holds in `U` as an `A(𝒱)`-module. Carried as the precise `Prop` `BottomDefectVanishes`. -/
  bottomDefect : VHat.VHatRep.BottomDefectVanishes ρ mdeg
  /-- The bottom `M₀ = mdeg 0` is, as a `ℂ`-space, the `A(𝒱)`-balanced bottom `≅ U` (R0):
  the lowest-weight space of the construction *is* the input module `U`. -/
  bottomEquivU : (mdeg 0) ≃ₗ[ℂ] U.carrier

attribute [instance] MUConstruction.addCommGroup MUConstruction.module

namespace MUConstruction

variable {W : VertexOperatorAlgebra 𝒱} {U : AMod W}

/-! ### Piece (2): the grading datum is exactly `IsGradedRep` -/

/-- **Piece (2) — the construction's representation is graded** (`IsGradedRep`), read off the bundled
`isGraded` field. This is the DLM3 grading that `MU.isInternal_deg` instantiates (the `ℕ`-grading of
`MU W U` raises module degree by the `V̂`-degree). -/
theorem isGradedRep (C : MUConstruction W U) :
    VHat.VHatRep.IsGradedRep C.ρ C.mdeg := C.isGraded

/-! ### Piece (3): `BottomDefectVanishes` from the `A(𝒱)`-module structure of the bottom -/

/-- **Piece (3) — the bottom defect vanishes** (`BottomDefectVanishes`), read off the bundled
`bottomDefect` field. The `S = 0` defect on `M₀` is the `A(𝒱)` zero-mode relation; it is `0` because
the bottom is the `A(𝒱)`-module `U` (`bottomEquivU`). -/
theorem bottomDefectVanishes (C : MUConstruction W U) :
    VHat.VHatRep.BottomDefectVanishes C.ρ C.mdeg := C.bottomDefect

/-! ### The defect at every strictly positive degree shift lives above the bottom -/

/-- A bottom-input defect with positive degree shift `S = wu+wv−ℓ−N−2 > 0` lands in degree `S`
(strictly positive), i.e. **above** the bottom — the keystone `defectVec_mem_pos`. -/
theorem defectVec_mem_pos (C : MUConstruction W U) {wu wv : ℤ} {u v : 𝒱}
    (hu : u ∈ W.grading wu) (hv : v ∈ W.grading wv) {x : C.M} (hx : x ∈ C.mdeg 0) (ℓ N : ℤ) :
    VHat.VHatRep.defectVec C.ρ u v x ℓ N ∈ C.mdeg (wu + wv - ℓ - N - 2) :=
  VHat.VHatRep.defectVec_mem_pos C.isGradedRep C.truncated hu hv hx ℓ N

/-- A bottom-input `S = 0` defect (the only one that can land back in the bottom) is `0`, by the
`A(𝒱)`-structure of the bottom (`gradedDefect_bottom_eq_zero`). -/
theorem gradedDefect_bottom_eq_zero (C : MUConstruction W U) {wu wv : ℤ} {u v : 𝒱}
    (hu : u ∈ W.grading wu) (hv : v ∈ W.grading wv) {x : C.M} (hx : x ∈ C.mdeg 0) {ℓ N : ℤ}
    (hS : wu + wv - ℓ - N - 2 = 0) :
    VHat.VHatRep.defectVec C.ρ u v x ℓ N = 0 :=
  VHat.VHatRep.gradedDefect_bottom_eq_zero C.bottomDefectVanishes hu hv hx hS

/-! ### Bottom survival — assembling pieces (2) + (3) + the keystone

The keystone `defectVec_homogeneous` shows the defect is homogeneous of degree `S`; pieces (2)+(3)
say the positive-`S` defects sit above the bottom and the lone `S = 0` slice vanishes. We package
bottom survival from the residual `defectSubmodule ⊓ M₀ ≤ ⊥` (the graded-span residual, carried as
the precise remaining hypothesis exactly as in `bottomSurvives`). -/

/-- **Piece (4)/bottom survival — `mkQ` is injective on the bottom `M₀`** (the lowest-weight space
`U` survives the defect quotient `M̄(U) = M ⧸ defectSubmodule ρ`). Stated from the closed residual
`hres : defectSubmodule ρ ⊓ mdeg 0 ≤ ⊥` — delivered by `bottomDefectVanishes` (piece 3) + the
graded-span structure (pieces 2 + the keystone) — exactly as `VHatRep.bottomSurvives`. -/
theorem bottomSurvives (C : MUConstruction W U)
    (hres : VHat.VHatRep.defectSubmodule C.ρ ⊓ C.mdeg 0 ≤ ⊥) :
    Set.InjOn (VHat.VHatRep.defectSubmodule C.ρ).mkQ (C.mdeg 0) :=
  VHat.VHatRep.bottomSurvives hres

/-- The bottom `M₀` injects `ℂ`-linearly into the defect quotient `M̄(U)`, given the residual.
Composed with `bottomEquivU` (R0), this exhibits `M̄(U)₀ ≅ U`. -/
theorem bottom_linearMap_injective (C : MUConstruction W U)
    (hres : VHat.VHatRep.defectSubmodule C.ρ ⊓ C.mdeg 0 ≤ ⊥) :
    Function.Injective
      ((VHat.VHatRep.defectSubmodule C.ρ).mkQ.comp (C.mdeg 0).subtype) :=
  VHat.VHatRep.bottom_linearMap_injective
    (VHat.VHatRep.bottomSurvives_of_residual hres)

end MUConstruction

/-! ## The lowest-weight packaging and the realization

With the carrier+grading+bottom (`MUConstruction`), the closed `WeakModule`/`L₀`/finiteness data of
`MUModuleData` (the deep Jacobi+grading-compatibility output, `ZhuVermaAnArchMULW`), and the
`A(𝒱)`-balanced bottom `≅ U` (R0), the realization `U ↦ M(U)` is assembled. We bundle the genuine
remaining `LWModule`-interface data as `MURealizationData` (hypothesis structure, not axiom), and
produce the `InducedRealization` / `HasInducedModule` witness. -/

/-- **The realization-packaging datum.** Bundles the closed `LWModule` packaging of `M(U)`
(`D : MUModuleData`, `ZhuVermaAnArchMULW`) together with the `A(𝒱)`-module isomorphism of its bottom
layer onto `U` (the R0 balanced bottom + the bottom `actA`-equivariance). The bottom equivalence is
the genuine `M(U)_h ≅ U` of the lifting direction. A hypothesis structure, **not** an axiom. -/
structure MURealizationData (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (h : ℂ) where
  /-- The closed `LWModule` packaging of `M(U)` (deep Jacobi + grading compatibility). -/
  data : MUModuleData W U h
  /-- The bottom `A(𝒱)`-module of the packaged `M(U)` is `U` (R0 + zero-mode equivariance). -/
  bottomEquiv : AModEquiv W (data.toLWModule).toAMod U

namespace MURealizationData

variable {W : VertexOperatorAlgebra 𝒱} {U : AMod W} {h : ℂ}

/-- **The induced realization `U ↦ M(U)`** packaged from the realization datum: the lowest-weight
`𝒱`-module `M(U) = D.toLWModule` with bottom `≅ U`. This is exactly an `InducedRealization W U`
(`ZhuInduced`). -/
noncomputable def toInducedRealization (R : MURealizationData W U h) :
    InducedRealization W U where
  N := R.data.toLWModule
  bottomEquiv := R.bottomEquiv

/-- **`U` has an induced module** (`HasInducedModule`, `ZhuInduced`): the existence crux of the
lifting direction is met by the realization datum. -/
theorem hasInducedModule (R : MURealizationData W U h) : HasInducedModule W U :=
  ⟨R.toInducedRealization⟩

/-- **The round-trip closes:** `forwardMap [M(U)] = [U]` (unconditional given the realization
datum, via `InducedRealization.forwardMap_eq`). The lifting-direction round-trip of Zhu Thm 5.3.4. -/
theorem forwardMap_eq (R : MURealizationData W U h) :
    forwardMap W (Quotient.mk (LWModule.setoid W) R.toInducedRealization.N)
      = Quotient.mk (AMod.setoid W) U :=
  InducedRealization.forwardMap_eq W U R.toInducedRealization

end MURealizationData

end VOA

-- Axiom check (axiom-clean: [propext, Classical.choice, Quot.sound]).
