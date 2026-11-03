/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchDLM3PBWIndependence
import VOA.Foundations.AffineLie

/-!
# The VOA consequence of the PBW theorem `VOA.pbw`

`VOA.pbw` is a theorem. Its type is the
explicit bundled `PBWPrinciple`: affine-vacuum nonvanishing and the generic Lie-induction bottom
embedding are separate fields. This file specializes the generic field
to VOA mode-Lie parabolic induction; it declares no axiom.

The exact remaining consequence needed by the current formalization is injectivity of the
canonical bottom map

`U -> U(VHat) tensor_[U(P_n)] U`, `u |-> [1 tensor u]`.

This is proved: `VOA.pbw.inducedBottom` is `PBWTheorem.bottom_injective`
(`Foundations/PBWTheorem/Induced.lean`, relative PBW). The Euler-operator theorem
`levCover_iSupIndep` is already unconditional; consequently full `PBWFreeness` and, at level zero,
`BottomProjection` are derived theorems.

`#print axioms` reports only Lean's standard `[propext, Classical.choice, Quot.sound]`.
-/

namespace VOA

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace VHat
namespace DLM3

variable {W : VertexOperatorAlgebra 𝒱} {n : ℕ}
variable {U : Type u} [AddCommGroup U] [Module ℂ U]

/-- The generic relative-induction balancing submodule is definitionally the DLM3 one. -/
@[simp] theorem pbwInduction_balancing_eq (P : ParabolicRep W n U) :
    VOA.PBWInduction.balancing (Pn W n) P.act = balancing P := rfl

/-- The generic relative-induction bottom map is definitionally the DLM3 one. -/
@[simp] theorem pbwInduction_bottom_eq (P : ParabolicRep W n U) :
    VOA.PBWInduction.bottom (Pn W n) P.act = indBottom P := rfl

/-- **VOA-side bottom injectivity from the PBW theorem `VOA.pbw`.**

For parabolic induction, the canonical bottom map `u ↦ [1 ⊗ u]` is injective.  This is the exact
right-freeness consequence of PBW needed after the unconditional Euler proof of level
independence. The generic quotient `PBWInduction.bottom (Pn W n) P.act` is definitionally the same
map as `indBottom P`, so this is a direct specialization of `VOA.pbw.inducedBottom`. -/
theorem voaPBWBottomInjective (P : ParabolicRep W n U) :
    Function.Injective (indBottom P) :=
  VOA.PBWPrinciple.inducedBottom
    (VOA.pbw : VOA.PBWPrinciple.{u}) (Pn W n) P.act

/-- Full DLM3 `PBWFreeness` from the PBW theorem `VOA.pbw` and the proved
Euler-operator independence theorem. -/
theorem voaPBWFreeness (P : ParabolicRep W n U) : PBWFreeness P :=
  pbwFreeness_of_bottom_injective P (voaPBWBottomInjective P)

section LevelZero

variable {U : Type u} [AddCommGroup U] [Module ℂ U]

/-- The level-zero bottom projection supplied by the PBW theorem `VOA.pbw`. -/
noncomputable def voaPBWBottomProjection (Q : ParabolicRep W 0 U) : BottomProjection Q :=
  bottomProjectionOfInjective Q (voaPBWBottomInjective Q)

@[simp] theorem voaPBWBottomProjection_bottom (Q : ParabolicRep W 0 U) (u : U) :
    (voaPBWBottomProjection Q).proj (indBottom Q u) = u :=
  (voaPBWBottomProjection Q).proj_bottom u

end LevelZero

end DLM3
end VHat

end VOA

-- `VOA.pbw` is a theorem, so these wrappers use only Lean's three standard axioms.
