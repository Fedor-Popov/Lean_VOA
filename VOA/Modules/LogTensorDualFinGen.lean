/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modules.LogTensorPzSimpleHomFinite
import VOA.Classification.COne.PlusFiniteLengthCyclic

/-! Actual finite generation and dual closure under C2-cofiniteness. -/
namespace VOA.LogTensor.Pz
open Classification.COne Classification.COne.PlusSplitting Classification.COne.PlusFiniteLength
universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}

/-- Actual finite weak generation implies finite mode-algebra length under C2. -/
theorem finiteLength_of_finGen (hC2 : C2Cofinite W) (B : WeakModule W M) (hgen : FinGen B) :
    IsFiniteLength (modeAlg B) M := by
  obtain ⟨S,hS,hgen⟩ := hgen
  let P := Submodule.span (modeAlg B) S
  have hPt : P.restrictScalars ℂ = ⊤ := hgen (P.restrictScalars ℂ)
    (fun _ hx => Submodule.subset_span hx) (fun a n x hx => (ofR B P).act_mem a n hx)
  have hP : P = ⊤ := by
    apply eq_top_iff.mpr
    intro x _
    have hx : x ∈ P.restrictScalars ℂ := hPt ▸ Submodule.mem_top
    exact hx
  have hfg : (⊤ : Submodule (modeAlg B) M).FG := Submodule.fg_def.mpr ⟨S,hS,hP⟩
  exact Submodule.topEquiv.isFiniteLength (finiteLength_fg_of_c2Cofinite hC2 B ⊤ hfg)

/-- The genuine contragredient is finitely generated for every actual finite module. -/
theorem finGen_contraLog_of_finGen (hC2 : C2Cofinite W) (N : LogVModule W M)
    (hN : FinGen N.toWeakModule) : FinGen (contraLog N).toWeakModule :=
  finGen_contraLog_of_finiteLength N (finiteLength_of_finGen hC2 N.toWeakModule hN)

end VOA.LogTensor.Pz
