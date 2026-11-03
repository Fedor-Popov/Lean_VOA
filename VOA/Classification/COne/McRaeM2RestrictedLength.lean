/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Classification.COne.McRaeM1Cover

/-! # Finite length for the actual restricted weak-module action

The actual weak-submodule lattice embeds strictly into the interval of ambient
mode-algebra submodules below its carrier. The ambient finite-length bound thus
transfers to its own mode algebra, including logarithmic weak modules.
-/

namespace VOA.C2Rigid.Restriction
open VOA.Classification.COne VOA.Classification.COne.PlusSplitting
open VOA.Classification.COne.McRaeM1
universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}

noncomputable def inclusion (B : WeakModule W M) (P : Submodule (modeAlg B) M) :
    (WeakModule.submodule B (ofR B P)).Hom B where
  toLinearMap := (ofR B P).carrier.subtype
  map_act _ _ _ := rfl

/-- Ambient mode-algebra finite length transfers to the genuine weak-module action
on the actual restricted submodule. -/
theorem finiteLength_restricted_submodule (B : WeakModule W M) (P : Submodule (modeAlg B) M)
    (hP : IsFiniteLength (modeAlg B) P) :
    IsFiniteLength (modeAlg (WeakModule.submodule B (ofR B P))) (ofR B P).carrier := by
  haveI : IsNoetherian (modeAlg B) P := (isFiniteLength_iff_isNoetherian_isArtinian.mp hP).1
  haveI : IsArtinian (modeAlg B) P := (isFiniteLength_iff_isNoetherian_isArtinian.mp hP).2
  haveI : WellFoundedLT (Submodule (modeAlg B) P) := inferInstance
  haveI : WellFoundedGT (Submodule (modeAlg B) P) := isNoetherian_iff'.mp inferInstance
  haveI : WellFoundedLT (Set.Iic P) := (Submodule.mapIic P).symm.strictMono.wellFoundedLT
  haveI : WellFoundedGT (Set.Iic P) := (Submodule.mapIic P).symm.strictMono.wellFoundedGT
  let phi : Submodule (modeAlg (WeakModule.submodule B (ofR B P))) (ofR B P).carrier → Set.Iic P :=
    fun Q => ⟨modeMap (inclusion B P) Q,by rintro _ ⟨x,hx,rfl⟩; exact x.2⟩
  have hi : Function.Injective (inclusion B P).toLinearMap := Subtype.val_injective
  have hs : StrictMono phi := fun Q R h =>
    (modeMap_mono (inclusion B P)).strictMono_of_injective (modeMap_injective (inclusion B P) hi) h
  haveI : WellFoundedLT
    (Submodule (modeAlg (WeakModule.submodule B (ofR B P))) (ofR B P).carrier) := hs.wellFoundedLT
  haveI : WellFoundedGT
    (Submodule (modeAlg (WeakModule.submodule B (ofR B P))) (ofR B P).carrier) := hs.wellFoundedGT
  exact isFiniteLength_iff_isNoetherian_isArtinian.mpr
    ⟨isNoetherian_iff'.mpr inferInstance,inferInstance⟩

end VOA.C2Rigid.Restriction
