/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modules.LogTensorArDualPairing
import VOA.Modules.LogTensorPzNilCovariance
import VOA.Modules.LogTensorSkewNatural

/-! # Genuine logarithmic A-coordinate pairing

The actual logarithmic A-operator, evaluated at an arbitrary formal logarithm
branch, obeys the genuine FHL opposite-coordinate formula. The proof retains
the Jordan half-turn, inverse logarithm shift, and all finite L(1) terms.
-/
set_option maxHeartbeats 1000000
namespace VOA.LogTensor.Ar
open Module (End Dual)
open scoped BigOperators
open Pz Contra
noncomputable section
universe u
variable {V M₁ M₂ M₃ : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] {W : VertexOperatorAlgebra V}
variable (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
variable (Y : LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule)

/-- The actual Jordan half-turn and two inverse source shifts give the opposite coordinate. -/
theorem first_nil_coordinate (ell : ℂ) (j : ℕ) (x : M₁) :
    nilExp N₁ (phase 0) ((L1w N₁.toGW.toWeakModule ^ j) (nilExp N₁ (-ell) x)) =
      nilExp N₁ ell ((L1w N₁.toGW.toWeakModule ^ j) (nilExp N₁ (phase 0-2*ell) x)) := by
  change nilExp N₁ (phase 0) ((L1w N₁.toWeakModule ^ j) (nilExp N₁ (-ell) x)) =
    nilExp N₁ ell ((L1w N₁.toWeakModule ^ j) (nilExp N₁ (phase 0-2*ell) x))
  rw [nilExp_L1_pow,nilExp_L1_pow,nilExp_add,nilExp_add]
  congr 2
  ring

/-- Actual original logarithmic coefficients transport under the Jordan opposite coordinate. -/
theorem prepared_inverse_coordinate (ell q : ℂ) (j : ℕ) (x : M₁) (y : M₂) :
    nilExp N₃ (-ell) (zeroFamily N₁ N₂ N₃ (prepared N₁ N₂ N₃ Y) q
      ((L1w N₁.toGW.toWeakModule ^ j) (nilExp N₁ (-ell) x)) (nilExp N₂ ell y)) =
      logShift (-ell) Y.1 q 0 ((L1w N₁.toGW.toWeakModule ^ j) (nilExp N₁ (phase 0-2*ell) x)) y := by
  change nilExp N₃ (-ell) (Y.1 q 0
      (nilExp N₁ (phase 0) ((L1w N₁.toGW.toWeakModule ^ j) (nilExp N₁ (-ell) x)))
      (nilExp N₂ ell y)) = _
  rw [first_nil_coordinate]
  have h := nilExp_logShift N₁ N₂ N₃ Y (-ell) q
    ((L1w N₁.toGW.toWeakModule ^ j) (nilExp N₁ (phase 0-2*ell) x)) y
  simpa only [neg_neg] using h

/-- Genuine A0 at every logarithm branch has the full FHL opposite-coordinate pairing.
No ordinary grading, finite-generation, or C2 assumption is imposed. -/
theorem transform_logShift_pair (ell n : ℂ) {a : ℂ} {x : M₁}
    (hx : x ∈ N₁.weight a) (t : C2Rigid.RestrictedDual N₃.toGW) (y : M₂) :
    C2Rigid.dualPairing N₂.toGW y (logShift ell (transform N₁ N₂ N₃ Y).1 n 0 x t) =
      statePhase a • ∑ j ∈ Finset.range (L1Cutoff N₁ a), (j.factorial:ℂ)⁻¹ •
        C2Rigid.dualPairing N₃.toGW
          (logShift (-ell) Y.1 (2*a-n-2-j) 0
            ((L1w N₁.toGW.toWeakModule ^ j) (nilExp N₁ (phase 0-2*ell) x)) y) t := by
  have hxe := nilExp_mem_weight N₁ (-ell) hx
  rw [← nilExp_logShift N₁ (contraLog N₃) (contraLog N₂) (transform N₁ N₂ N₃ Y) ell n x t,
    pair_contra_nilExp N₂ ell,transform_logZero,pair_modes_zero N₁ N₂ N₃ Y n hxe,
    pair_contra_nilExp N₃ (-ell)]
  have hJ : ∀ j, L1Cutoff N₁ a ≤ j → (L1w N₁.toGW.toWeakModule ^ j) (nilExp N₁ (-ell) x)=0 :=
    fun j hj => L1Cutoff_spec N₁ a j hj _ hxe
  rw [twI_apply_eq_sum N₁.toGW _ a n hJ (nilExp N₂ ell y),map_smul,map_sum]
  simp only [map_smul]
  change C2Rigid.dualPairingFlip N₃.toGW t
      (statePhase a • ∑ j ∈ Finset.range (L1Cutoff N₁ a), (j.factorial:ℂ)⁻¹ •
        nilExp N₃ (-ell) (zeroFamily N₁ N₂ N₃ (prepared N₁ N₂ N₃ Y) (2*a-n-2-j)
          ((L1w N₁.toGW.toWeakModule ^ j) (nilExp N₁ (-ell) x)) (nilExp N₂ ell y))) = _
  rw [map_smul,map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_smul,C2Rigid.dualPairingFlip_apply,prepared_inverse_coordinate]

/-- Genuine branch turns combine with inverse logarithmic state shifts, including Jordan terms. -/
theorem nilExp_branch_coordinate (r : ℤ) (ell : ℂ) {a : ℂ} {x : M₁}
    (hx : x ∈ N₁.weight a) :
    nilExp N₁ (phase 0-2*ell) (branchTurn N₁ r x) =
      Complex.exp (((r:ℂ)*(2*Real.pi*Complex.I))*a) • nilExp N₁ (phase r-2*ell) x := by
  rw [branchTurn,L0exp_apply_of_mem N₁ _ hx,map_smul,nilExp_add]
  congr 2
  unfold phase
  push_cast
  ring

/-- Genuine FHL logarithmic coordinate pairing for every integer A_r branch and every ell. -/
theorem transformBranch_logShift_pair (r : ℤ) (ell n : ℂ) {a : ℂ} {x : M₁}
    (hx : x ∈ N₁.weight a) (t : C2Rigid.RestrictedDual N₃.toGW) (y : M₂) :
    C2Rigid.dualPairing N₂.toGW y (logShift ell (transformBranch N₁ N₂ N₃ Y r).1 n 0 x t) =
      Complex.exp (phase r*a) • ∑ j ∈ Finset.range (L1Cutoff N₁ a), (j.factorial:ℂ)⁻¹ •
        C2Rigid.dualPairing N₃.toGW
          (logShift (-ell) Y.1 (2*a-n-2-j) 0
            ((L1w N₁.toGW.toWeakModule ^ j) (nilExp N₁ (phase r-2*ell) x)) y) t := by
  change C2Rigid.dualPairing N₂.toGW y
    (logShift ell (preModes (branchTurn N₁ r).toLinearMap LinearMap.id (transform N₁ N₂ N₃ Y).1) n 0 x t) = _
  rw [logShift_preModes (transform N₁ N₂ N₃ Y).2.logFinite,preModes_apply,LinearMap.id_apply]
  simp only [LinearEquiv.coe_coe]
  have hbt : branchTurn N₁ r x ∈ N₁.weight a := L0exp_mem_weight N₁ _ hx
  rw [transform_logShift_pair N₁ N₂ N₃ Y ell n hbt,nilExp_branch_coordinate N₁ r ell hx,
    Finset.smul_sum,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [map_smul,LinearMap.smul_apply,C2Rigid.dualPairing_smul_left]
  have he : statePhase a * Complex.exp (((r:ℂ)*(2*Real.pi*Complex.I))*a) = Complex.exp (phase r*a) := by
    unfold statePhase
    rw [← Complex.exp_add]
    congr 1
    unfold phase
    push_cast
    ring
  simp only [smul_eq_mul]
  rw [← he]
  ring

/-- The literal coefficient state operator evaluates at the full nilpotent opposite coordinate. -/
theorem firstTermEnd_nil_coordinate (r : ℤ) (ell : ℂ) (j : ℕ) {a : ℂ} {x : M₁}
    (hx : x ∈ N₁.weight a) :
    firstTermEnd N₁ (phase r) j 0 (nilExp N₁ (-2*ell) x) =
      Complex.exp (phase r*a) • (L1w N₁.toGW.toWeakModule ^ j) (nilExp N₁ (phase r-2*ell) x) := by
  change (L1w N₁.toGW.toWeakModule ^ j) (L0exp N₁ (phase r) (nilExp N₁ (-2*ell) x)) = _
  rw [L0exp_apply_of_mem N₁ (phase r) (nilExp_mem_weight N₁ (-2*ell) hx),map_smul,nilExp_add]
  congr 3
  ring

/-- The actual FHL coordinate pairing expressed directly in the literal coefficient state terms. -/
theorem transformBranch_logShift_pair_terms (r : ℤ) (ell n : ℂ) {a : ℂ} {x : M₁}
    (hx : x ∈ N₁.weight a) (t : C2Rigid.RestrictedDual N₃.toGW) (y : M₂) :
    C2Rigid.dualPairing N₂.toGW y (logShift ell (transformBranch N₁ N₂ N₃ Y r).1 n 0 x t) =
      ∑ j ∈ Finset.range (L1Cutoff N₁ a), (j.factorial:ℂ)⁻¹ •
        C2Rigid.dualPairing N₃.toGW
          (logShift (-ell) Y.1 (2*a-j-n-2) 0
            (firstTermEnd N₁ (phase r) j 0 (nilExp N₁ (-2*ell) x)) y) t := by
  rw [transformBranch_logShift_pair N₁ N₂ N₃ Y r ell n hx,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [firstTermEnd_nil_coordinate N₁ r ell j hx,
    show 2*a-n-2-j=2*a-j-n-2 by ring]
  simp only [map_smul,LinearMap.smul_apply,C2Rigid.dualPairing_smul_left,smul_eq_mul]
  ring

/-- Actual finite first-state nilpotent exponentials have the exact coefficient expansion. -/
theorem firstTermEnd_nil_finite (r : ℤ) (ell : ℂ) (j : ℕ) {a : ℂ} {x : M₁}
    (hx : x ∈ N₁.weight a) :
    firstTermEnd N₁ (phase r) j 0 (nilExp N₁ (-2*ell) x) =
      ∑ l ∈ Finset.range (Module.finrank ℂ (N₁.weight a)), ((-2*ell)^l/(l.factorial:ℂ)) •
        firstTermEnd N₁ (phase r) j l x := by
  rw [nilExp_finite N₁ (-2*ell) (nilpotent_weight_bound N₁ hx),map_sum]
  apply Finset.sum_congr rfl
  intro l hl
  rw [map_smul]
  rfl

end
end VOA.LogTensor.Ar
