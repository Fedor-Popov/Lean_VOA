/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Classification.COne.McRaeM2TensorRightUnit
import VOA.Modules.LogTensorUnitCreation

/-! # Genuine tensor-unit vacuum creation

Actual unit equivalences transfer the full logarithmic vacuum formulas to the
canonical tensor operator. Every positive logarithmic coefficient vanishes,
and the right vacuum modes are the factorial translation coefficients of the
actual inverse unit morphism.
-/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.C2Rigid.LocalInjective
open VOA.Classification.COne VOA.Classification.COne.McRaeM1
open VOA.LogTensor VOA.LogTensor.Pz
universe u
variable {V R : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup R] [Module ℂ R] {W : VertexOperatorAlgebra V}

/-- The actual tensor-unit vacuum belongs to its true generalized weight zero. -/
theorem adjoint_log_vacuum_mem_weight :
    W.vacuum ∈ (adjointModule W).toLog.weight 0 := by
  change W.vacuum ∈ adjWeight W 0
  rw [show (0 : ℂ) = ((0 : ℤ) : ℂ) by norm_num, adjWeight_cast]
  exact W.vacuum_mem_grading_zero

/-- The same vacuum weight in the actual graded-weak bridge. -/
theorem adjoint_GW_vacuum_mem_weight :
    W.vacuum ∈ (adjointModule W).toLog.toGW.weight 0 :=
  adjoint_log_vacuum_mem_weight

/-- The genuine right unit operator has no positive logarithmic coefficients. -/
theorem rightUnitIntertwiner_vacuum_positive_log_zero
    (N : LogVModule W R) (n : ℂ) (k : ℕ) (hk : 0 < k) (x : R) :
    (rightUnitIntertwiner N).1 n k x W.vacuum = 0 := by
  change omega N.toWeakModule (-1) (logModuleIntertwiner N.toWeakModule).1
    n k x W.vacuum = 0
  exact omega_module_vacuum_positive_log_zero N.toWeakModule (-1) n k hk x

/-- The genuine right unit operator vanishes away from the creation indices. -/
theorem rightUnitIntertwiner_vacuum_zero_of_no_index
    (N : LogVModule W R) (n : ℂ) (hn : ∀ j : ℕ, n ≠ -1 - (j : ℂ)) (x : R) :
    (rightUnitIntertwiner N).1 n 0 x W.vacuum = 0 := by
  change omega N.toWeakModule (-1) (logModuleIntertwiner N.toWeakModule).1
    n 0 x W.vacuum = 0
  exact omega_module_vacuum_zero_of_no_index N.toWeakModule (-1) n hn x

/-- Its actual creation coefficients, with every logarithmic shift accounted for. -/
theorem rightUnitIntertwiner_vacuum_creation
    (N : LogVModule W R) (j : ℕ) (x : R) :
    (rightUnitIntertwiner N).1 (-1 - (j : ℂ)) 0 x W.vacuum =
      (j.factorial : ℂ)⁻¹ • (Lm1 N.toWeakModule ^ j) x := by
  change omega N.toWeakModule (-1) (logModuleIntertwiner N.toWeakModule).1
    (-1 - (j : ℂ)) 0 x W.vacuum = _
  exact omega_module_vacuum_creation N.toWeakModule (-1) j x

variable (hC2 : C2Cofinite W)
  (N : LogVModule W R) (hN : FinGen N.toWeakModule)

/-- Every actual canonical left-unit vacuum coefficient is the genuine inverse
unit map at the constant coefficient, and zero elsewhere. -/
theorem tensorLeftUnit_vacuum_modes (n : ℂ) (k : ℕ) (x : R) :
    (tensorIntertwiner hC2 (adjointModule W).toLog N finGen_adjoint hN).1
      n k W.vacuum x =
    if n = -1 ∧ k = 0 then (tensorLeftUnitInvHom hC2 N hN).toLinearMap x else 0 := by
  classical
  apply (tensorLeftUnitEquiv hC2 N hN).injective
  have he := congrArg (fun Y : LogIntertwiningOperator (adjointModule W).toWeakModule
      N.toWeakModule N.toWeakModule => Y.1 n k W.vacuum x)
    (tensorLeftUnit_intertwiner hC2 N hN)
  dsimp only at he
  rw [postcompose_apply, logModuleIntertwiner_vacuum_modes] at he
  change (tensorLeftUnitHom hC2 N hN).toLinearMap _ = _
  rw [he]
  split_ifs with hn
  · exact (tensorLeftUnit_hom_inv hC2 N hN x).symm
  · exact (map_zero (tensorLeftUnitHom hC2 N hN).toLinearMap).symm

private theorem tensorRightUnit_vacuum_realization (n : ℂ) (k : ℕ) (x : R) :
    (tensorRightUnitHom hC2 N hN).toLinearMap
      ((tensorIntertwiner hC2 N (adjointModule W).toLog hN finGen_adjoint).1
        n k x W.vacuum) = (rightUnitIntertwiner N).1 n k x W.vacuum := by
  have he := congrArg (fun Y : LogIntertwiningOperator N.toWeakModule
      (adjointModule W).toWeakModule N.toWeakModule => Y.1 n k x W.vacuum)
    (tensorRightUnit_intertwiner hC2 N hN)
  dsimp only at he
  rw [postcompose_apply] at he
  exact he

/-- The canonical right-unit tensor operator has no positive logarithmic terms. -/
theorem tensorRightUnit_vacuum_positive_log_zero
    (n : ℂ) (k : ℕ) (hk : 0 < k) (x : R) :
    (tensorIntertwiner hC2 N (adjointModule W).toLog hN finGen_adjoint).1
      n k x W.vacuum = 0 := by
  apply (tensorRightUnitEquiv hC2 N hN).injective
  change (tensorRightUnitHom hC2 N hN).toLinearMap _ = _
  rw [tensorRightUnit_vacuum_realization, rightUnitIntertwiner_vacuum_positive_log_zero N n k hk x]
  exact (map_zero (tensorRightUnitHom hC2 N hN).toLinearMap).symm

/-- Every canonical right-unit mode outside the actual creation indices vanishes. -/
theorem tensorRightUnit_vacuum_zero_of_no_index
    (n : ℂ) (hn : ∀ j : ℕ, n ≠ -1 - (j : ℂ)) (x : R) :
    (tensorIntertwiner hC2 N (adjointModule W).toLog hN finGen_adjoint).1
      n 0 x W.vacuum = 0 := by
  apply (tensorRightUnitEquiv hC2 N hN).injective
  change (tensorRightUnitHom hC2 N hN).toLinearMap _ = _
  rw [tensorRightUnit_vacuum_realization, rightUnitIntertwiner_vacuum_zero_of_no_index N n hn x]
  exact (map_zero (tensorRightUnitHom hC2 N hN).toLinearMap).symm

/-- The literal canonical creation coefficient is the inverse unit map applied
to the actual factorial translation coefficient. -/
theorem tensorRightUnit_vacuum_creation (j : ℕ) (x : R) :
    (tensorIntertwiner hC2 N (adjointModule W).toLog hN finGen_adjoint).1
      (-1 - (j : ℂ)) 0 x W.vacuum =
      (tensorRightUnitInvHom hC2 N hN).toLinearMap
        ((j.factorial : ℂ)⁻¹ • (Lm1 N.toWeakModule ^ j) x) := by
  apply (tensorRightUnitEquiv hC2 N hN).injective
  change (tensorRightUnitHom hC2 N hN).toLinearMap _ = _
  rw [tensorRightUnit_vacuum_realization, rightUnitIntertwiner_vacuum_creation]
  exact (tensorRightUnit_hom_inv hC2 N hN _).symm

/-- The equivalent creation formula in the actual tensor module itself. -/
theorem tensorRightUnit_vacuum_creation_tensor (j : ℕ) (x : R) :
    (tensorIntertwiner hC2 N (adjointModule W).toLog hN finGen_adjoint).1
      (-1 - (j : ℂ)) 0 x W.vacuum =
      (j.factorial : ℂ)⁻¹ • (Lm1 (rightUnitTensor hC2 N hN).toWeakModule ^ j)
        ((tensorRightUnitInvHom hC2 N hN).toLinearMap x) := by
  rw [tensorRightUnit_vacuum_creation, map_smul, hom_Lm1_pow]

/-- The canonical vacuum constant is exactly the actual inverse right-unit map. -/
theorem tensorRightUnit_vacuum_constant (x : R) :
    (tensorIntertwiner hC2 N (adjointModule W).toLog hN finGen_adjoint).1
      (-1) 0 x W.vacuum = (tensorRightUnitInvHom hC2 N hN).toLinearMap x := by
  simpa using tensorRightUnit_vacuum_creation hC2 N hN 0 x

end VOA.C2Rigid.LocalInjective
