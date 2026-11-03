/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modules.ModuleRestrict

/-!
# Ordinary modules restricted to a sub-VOA

`Modules.ModuleRestrict` restricts a weak module along the inclusion of a vertex operator
subalgebra.  The same construction preserves an ordinary module without any new
representation-theoretic input: its weight spaces, internal direct-sum decomposition,
finite-dimensionality and lower bound are unchanged, while the conformal vector of the
subalgebra is the ambient conformal vector.

The second part records the canonical inclusion of a sub-VOA's adjoint module into the ambient
carrier equipped with the restricted action.  Its range is packaged as a weak submodule.  These
are the elementary module-theoretic endpoints needed before one can formulate a screening
sequence on an ambient lattice carrier.

No exactness, Felder resolution or logarithmic module is claimed here.
-/

namespace VOA

open Module (End)

universe u v

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace VOASubalgebra

variable {W : VertexOperatorAlgebra 𝒱} (S : VOASubalgebra W)

/-- Restriction of an ordinary module along a sub-VOA.  The grading data are inherited verbatim;
the `L₀` condition agrees because `S.toVOA` has the same conformal vector as `W`. -/
noncomputable def restrictOrdVModule {M : Type v} [AddCommGroup M] [Module ℂ M]
    (N : OrdVModule W M) : OrdVModule S.toVOA M where
  toWeakModule := S.restrictWeakModule N.toWeakModule
  weight := N.weight
  isInternal := N.isInternal
  L0_weight := N.L0_weight
  finrank := N.finrank
  boundedBelow := N.boundedBelow

@[simp] theorem restrictOrdVModule_toWeakModule {M : Type v} [AddCommGroup M] [Module ℂ M]
    (N : OrdVModule W M) :
    (S.restrictOrdVModule N).toWeakModule = S.restrictWeakModule N.toWeakModule := rfl

@[simp] theorem restrictOrdVModule_YM {M : Type v} [AddCommGroup M] [Module ℂ M]
    (N : OrdVModule W M) (u : S.carrier) :
    (S.restrictOrdVModule N).YM u = N.YM (u : 𝒱) := rfl

@[simp] theorem restrictOrdVModule_act {M : Type v} [AddCommGroup M] [Module ℂ M]
    (N : OrdVModule W M) (u : S.carrier) (n : ℤ) (x : M) :
    (S.restrictOrdVModule N).act u n x = N.act (u : 𝒱) n x := rfl

@[simp] theorem restrictOrdVModule_weight {M : Type v} [AddCommGroup M] [Module ℂ M]
    (N : OrdVModule W M) (α : ℂ) : (S.restrictOrdVModule N).weight α = N.weight α := rfl

/-- The ambient VOA carrier, with its ordinary adjoint module restricted to `S`. -/
noncomputable def adjointRestrictOrd : OrdVModule S.toVOA 𝒱 :=
  S.restrictOrdVModule (adjointModule W)

@[simp] theorem adjointRestrictOrd_toWeakModule :
    S.adjointRestrictOrd.toWeakModule = S.adjointRestrict := rfl

@[simp] theorem adjointRestrictOrd_act (u : S.carrier) (n : ℤ) (x : 𝒱) :
    S.adjointRestrictOrd.act u n x = W.smul (u : 𝒱) n x := rfl

/-- The canonical inclusion from the adjoint weak module of `S` to the restricted ambient
module.  It intertwines all modes because the product of the sub-VOA is the ambient product. -/
noncomputable def adjointInclusion :
    WeakModule.Hom (adjointWeakModule S.toVOA) S.adjointRestrict where
  toLinearMap := S.carrier.subtype
  map_act := by
    intro u n x
    rfl

@[simp] theorem adjointInclusion_apply (x : S.carrier) :
    S.adjointInclusion.toLinearMap x = (x : 𝒱) := rfl

theorem adjointInclusion_injective : Function.Injective S.adjointInclusion.toLinearMap :=
  S.carrier.subtype_injective

/-- The sub-VOA carrier as a weak submodule of the restricted ambient adjoint module. -/
noncomputable def carrierWeakSubmodule : WeakModule.Submodule' S.adjointRestrict where
  carrier := S.carrier
  act_mem := by
    intro u n x hx
    exact S.smul_mem (u : 𝒱) u.property n x hx

@[simp] theorem carrierWeakSubmodule_carrier : S.carrierWeakSubmodule.carrier = S.carrier := rfl

end VOASubalgebra

end VOA
