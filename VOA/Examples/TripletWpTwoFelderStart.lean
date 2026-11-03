/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Examples.TripletWp
import VOA.Modules.ModuleRestrictOrd

/-!
# The ambient ordinary module for lattice `W(2)`

This file instantiates ordinary restriction for the lattice realization of the triplet algebra.
The full background-charge lattice carrier is an ordinary module over the generated sub-VOA
`tripletWVOA 2 hp`, and the triplet carrier embeds as a weak submodule of it.

This is only the degree-zero module-theoretic starting point for a future screening sequence.  It
does not construct charged Fock modules, a Felder differential, exactness, or a logarithmic
Jordan block.
-/

namespace VOA.LatGen.Wp

open VOA
open VOA.LatGen.Triplet

/-- The background-charge lattice VOA carrier, regarded as an ordinary module over lattice
`W(2)` by restriction along `tripletW 2 hp`. -/
noncomputable def tripletAmbientOrdModuleTwo (hp : 1 ≤ 2) :
    OrdVModule (tripletWVOA 2 hp) (LatModuleGen (latP 2)) :=
  (tripletW 2 hp).adjointRestrictOrd

@[simp] theorem tripletAmbientOrdModuleTwo_act (hp : 1 ≤ 2)
    (u : (tripletW 2 hp).carrier) (n : ℤ) (x : LatModuleGen (latP 2)) :
    (tripletAmbientOrdModuleTwo hp).act u n x =
      (tripletLatticeVOA 2 hp).smul (u : LatModuleGen (latP 2)) n x := rfl

/-- The triplet carrier includes into its ambient lattice ordinary module as a weak-module
homomorphism. -/
noncomputable def tripletCarrierInclusionTwo (hp : 1 ≤ 2) :
    WeakModule.Hom (adjointWeakModule (tripletWVOA 2 hp))
      (tripletAmbientOrdModuleTwo hp).toWeakModule :=
  (tripletW 2 hp).adjointInclusion

@[simp] theorem tripletCarrierInclusionTwo_apply (hp : 1 ≤ 2)
    (x : (tripletW 2 hp).carrier) :
    (tripletCarrierInclusionTwo hp).toLinearMap x = (x : LatModuleGen (latP 2)) := rfl

theorem tripletCarrierInclusionTwo_injective (hp : 1 ≤ 2) :
    Function.Injective (tripletCarrierInclusionTwo hp).toLinearMap :=
  (tripletW 2 hp).adjointInclusion_injective

/-- The image of lattice `W(2)` inside the ambient lattice carrier, packaged as a weak
submodule for the restricted action. -/
noncomputable def tripletCarrierWeakSubmoduleTwo (hp : 1 ≤ 2) :
    WeakModule.Submodule' (tripletAmbientOrdModuleTwo hp).toWeakModule :=
  (tripletW 2 hp).carrierWeakSubmodule

@[simp] theorem tripletCarrierWeakSubmoduleTwo_carrier (hp : 1 ≤ 2) :
    (tripletCarrierWeakSubmoduleTwo hp).carrier = (tripletW 2 hp).carrier := rfl

end VOA.LatGen.Wp
