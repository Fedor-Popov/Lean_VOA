/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.HarmonicMetricBridge

/-!
# The explicit vacuum representative has norm one

* `repVacuumNormalized_proved : RepVacuumNormalized` — the explicit vacuum representative
  `(|0⟩_A ⊗ |0⟩_B ⊗ |0⟩_U) ⊗ |0⟩_gh` has `B_M ⊗ B_G`-norm one: each matter form is normalized
  and `B_G(|0⟩_gh, |0⟩_gh) = 1` (the empty Fock monomial has weight `1` in every colour).

Everything is proved outright.
-/

namespace VOA.ConcreteHodge

open Sl2CosetConcrete Sl2SemiInfinite AffineSl2GeneralRigidity AffineSl2BelowCritical
open VOA.GradedUnitaryCohomology VOA.LeeYangCosetTransfer VOA.VertexOperatorAlgebra
open VOA.LeeYangTransferAssembly LeeYangShortcut VirModule LeeYang VirGradedUnitarity
open VOA.SympFerm VOA.Ghost AffineVOA
open scoped TensorProduct

noncomputable section

theorem fockForm_vac (w : Finset ModeIdx → ℝ) :
    fockForm w (stWordSF []) (stWordSF []) = (w ∅ : ℂ) := by
  rw [← fockWord_empty, ← fockBasis_eq_word]
  exact basisForm_basis_self _ _ _

theorem bgPG_gvac : bgPG gvac gvac = 1 := by
  rw [gvac, W3, bgPG_tmul3, fockForm_vac, fockForm_vac, fockForm_vac]
  simp [bgColourWeight]

theorem ghostB_gvac : ghostB gvac gvac = 1 := by
  rw [ghostB_apply, ghostConj_gvac, ghostIR_eigen gvac_mem]
  simpa using bgPG_gvac

theorem cosetVacuum_val : ((cosetVOA.vacuum : CosetSpace) : ASpace ⊗[ℂ] BSpace) =
    ASVA.vacuum ⊗ₜ[ℂ] BSVA.vacuum := rfl

/-- **The explicit vacuum representative has norm one.** -/
theorem repVacuumNormalized_proved : RepVacuumNormalized := by
  rw [RepVacuumNormalized, repVec, virasoroToCoset_vacuum, cosetToComplex_apply,
    cosetVacuum_val, ← gvac_eq]
  rw [ghBBRST, bilinTmul_tmul, ghostB_gvac, mul_one, matterB, bilinTmul_tmul, bilinTmul_tmul]
  rw [show affineForm.form ASVA.vacuum ASVA.vacuum = 1 from affineForm_normalized,
    show bForm.form BSVA.vacuum BSVA.vacuum = 1 from simpleForm_normalized 1 bNoncritical,
    show auxiliaryForm.form USVA.vacuum USVA.vacuum = 1 from
      universalForm_normalized (-11 / 3) uNoncritical]
  norm_num

end

end VOA.ConcreteHodge
