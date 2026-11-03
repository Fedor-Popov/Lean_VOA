/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modules.LogTensorPzHomFinite
import VOA.Modules.LogTensorFinLength
import VOA.Classification.COne.McRaeM2Swap

/-! # Actual simple-source Hom-finiteness for the maximal compatible module

The actual simple weak source obtains its canonical generalized grading from
C₂-cofiniteness. Its genuine contragredient has finite length and is finitely
generated. Thus the Hom-finiteness theorem applies without asking for a grading
or a dual-finiteness input on the simple source.
-/

namespace VOA.LogTensor.Pz
open VOA.Classification.COne
universe u
variable {V M₁ M₂ R : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup R] [Module ℂ R] {W : VertexOperatorAlgebra V}

/-- Finite length of a generalized source proves finite generation of its actual dual. -/
theorem finGen_contraLog_of_finiteLength (N : LogVModule W R)
    (hN : IsFiniteLength (modeAlg N.toWeakModule) R) : FinGen (contraLog N).toWeakModule := by
  have hdual := C2Rigid.isFiniteLength_contra N.toGW
    (fun a => N.weight_le_maxGenEigenspace a) hN
  haveI : IsNoetherian (modeAlg (contraLog N).toWeakModule) (C2Rigid.RestrictedDual N.toGW) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hdual).1
  exact LogFin.finGen_of_isNoetherian (contraLog N).toWeakModule

/-- Genuine Hom-finiteness from every simple actual weak module into the maximal
compatible module. All generalized grading and dual-finiteness obligations are proved. -/
theorem finiteDimensional_maximalHomSpace_from_simple (hC2 : C2Cofinite W)
    (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂)
    (h₁ : FinGen N₁.toWeakModule) (h₂ : FinGen N₂.toWeakModule)
    (B : WeakModule W R) (hB : IsSimpleModule (modeAlg B) R) :
    FiniteDimensional ℂ
      (moduleHomSpace B (maximalWeakModule N₁.toWeakModule N₂.toWeakModule)) := by
  let N := LogFin.logOfFiniteLength hC2 B (C2Rigid.finiteLength_of_simple hB)
  exact finiteDimensional_maximalHomSpace_of_c2Cofinite N₁ N₂ N hC2 h₁ h₂
    (finGen_contraLog_of_finiteLength N (C2Rigid.finiteLength_of_simple hB))

end VOA.LogTensor.Pz
