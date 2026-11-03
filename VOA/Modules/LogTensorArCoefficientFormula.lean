/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modules.LogTensorArCoefficientBounds

/-! # Every genuine logarithmic A coefficient is the literal full FHL formula

The genuine opposite-coordinate polynomial identity, finite Jordan/log
bounds, and scalar polynomial uniqueness identify every coefficient.
Thus the explicit finite FHL A_r modes satisfy all genuine logarithmic axioms.
-/
set_option maxSynthPendingDepth 3
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

/-- The literal finite FHL scalar polynomial is the actual genuine A-coordinate evaluation. -/
theorem functional_logPolynomial_eval (r : ℤ) (ell n : ℂ) {a b : ℂ} {x : M₁} {y : M₂}
    (hx : x ∈ N₁.weight a) (hy : y ∈ N₂.weight b) (t : C2Rigid.RestrictedDual N₃.toGW) :
    (∑ k ∈ Finset.range (Module.finrank ℂ (N₁.weight a)+coordinateLogBound N₁ N₂ N₃ n a b),
      ell^k * functional N₁ N₂ N₃ Y r n k a x t y) =
      C2Rigid.dualPairing N₂.toGW y (logShift ell (transformBranch N₁ N₂ N₃ Y r).1 n 0 x t) := by
  classical
  let D := Module.finrank ℂ (N₁.weight a)
  let Q := coordinateLogBound N₁ N₂ N₃ n a b
  have hfun : (∑ k ∈ Finset.range (D+Q), ell^k * functional N₁ N₂ N₃ Y r n k a x t y) =
      ∑ j ∈ Finset.range (L1Cutoff N₁ a), (j.factorial:ℂ)⁻¹ *
        (∑ k ∈ Finset.range (D+Q), ell^k * ∑ l ∈ Finset.range (k+1),
          ((-2:ℂ)^l/(l.factorial:ℂ)) * (-1:ℂ)^(k-l) *
            matrixTerm N₁ N₂ N₃ Y (phase r) (2*a-j-n-2) (k-l) j l x t y) := by
    simp only [functional,LinearMap.coe_sum,Finset.sum_apply,LinearMap.smul_apply,smul_eq_mul,
      Finset.mul_sum,coefficient,div_eq_mul_inv]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro l hl
    ring
  rw [hfun,transformBranch_logShift_pair_terms N₁ N₂ N₃ Y r ell n hx]
  apply Finset.sum_congr rfl
  intro j hj
  rw [coordinate_term_eval_sum N₁ N₂ N₃ Y r ell n hx hy t hj]
  change (j.factorial:ℂ)⁻¹ * _ = (j.factorial:ℂ)⁻¹ * _
  congr 1
  let g : ℕ → ℕ → ℂ := fun l q =>
    matrixTerm N₁ N₂ N₃ Y (phase r) (2*a-j-n-2) q j l x t y
  have hD : ∀ l q, D ≤ l → g l q=0 := by
    intro l q hl
    dsimp only [g]
    rw [matrixTerm_apply,firstTermEnd_zero_of_nil_bound N₁ (phase r) j l hx hl,map_zero,LinearMap.zero_apply]
    exact map_zero (C2Rigid.dualPairingFlip N₃.toGW t)
  have hQ : ∀ l q, Q ≤ q → g l q=0 := by
    intro l q hq
    exact matrixTerm_high_log_zero N₁ N₂ N₃ Y r n hx hy t hj hq
  exact finite_log_convolution (-2) ell g D Q hD hQ

/-- Every actual A coefficient pairing equals the literal finite FHL coefficient functional. -/
theorem transformBranch_coefficient_pair (r : ℤ) (n : ℂ) (k : ℕ) {a b : ℂ} {x : M₁} {y : M₂}
    (hx : x ∈ N₁.weight a) (hy : y ∈ N₂.weight b) (t : C2Rigid.RestrictedDual N₃.toGW) :
    C2Rigid.dualPairing N₂.toGW y ((transformBranch N₁ N₂ N₃ Y r).1 n k x t) =
      functional N₁ N₂ N₃ Y r n k a x t y := by
  let f : ℕ → ℂ := fun k => C2Rigid.dualPairing N₂.toGW y ((transformBranch N₁ N₂ N₃ Y r).1 n k x t)
  let g : ℕ → ℂ := fun k => functional N₁ N₂ N₃ Y r n k a x t y
  obtain ⟨K,hK⟩ := (transformBranch N₁ N₂ N₃ Y r).2.logFinite x t n
  let L := Module.finrank ℂ (N₁.weight a)+coordinateLogBound N₁ N₂ N₃ n a b
  have hf : ∀ k, K ≤ k → f k=0 := by
    intro k hk
    dsimp only [f]
    rw [hK k hk,map_zero]
  have hg : ∀ k, L ≤ k → g k=0 :=
    fun k hk => functional_high_log_zero N₁ N₂ N₃ Y r n hx hy t hk
  have heval : ∀ ell : ℂ, (∑ k ∈ Finset.range K, f k*ell^k) = ∑ k ∈ Finset.range L, g k*ell^k := by
    intro ell
    have ht := functional_logPolynomial_eval N₁ N₂ N₃ Y r ell n hx hy t
    rw [logShift_eq_sum (transformBranch N₁ N₂ N₃ Y r).2.logFinite K hK,map_sum] at ht
    simp only [map_smul,shc,Nat.choose_zero_right,Nat.cast_one,one_mul,Nat.sub_zero,smul_eq_mul] at ht
    simp only [f,g,L]
    simpa only [mul_comm] using ht.symm
  have he := finite_coefficient_ext f g K L hf hg heval
  exact congrFun he k

/-- Every actual logarithmic A_r coefficient is exactly the full finite FHL mode formula. -/
theorem transformBranch_modes (r : ℤ) :
    (transformBranch N₁ N₂ N₃ Y r).1 = modes N₁ N₂ N₃ Y r := by
  funext n k
  apply bilinear_ext_homogeneous N₁ (contraLog N₃)
  intro a c x t hx ht
  apply C2Rigid.restrictedDual_ext_of_pairing N₂.toGW
  intro b y hy
  rw [pair_modes N₁ N₂ N₃ Y r n k hx hy ht]
  split_ifs with hbc
  · exact transformBranch_coefficient_pair N₁ N₂ N₃ Y r n k hx hy t
  · have hm := (transformBranch N₁ N₂ N₃ Y r).2.mem_weight hx ht n k
    exact pair_weights_zero N₂ hy hm (Ne.symm hbc)

/-- The literal full-Jordan FHL A_r modes satisfy EVERY genuine logarithmic intertwiner axiom. -/
theorem isLogIntertwining_modes (r : ℤ) :
    IsLogIntertwining N₁.toWeakModule (contraLog N₃).toWeakModule (contraLog N₂).toWeakModule
      (modes N₁ N₂ N₃ Y r) := by
  rw [← transformBranch_modes N₁ N₂ N₃ Y r]
  exact (transformBranch N₁ N₂ N₃ Y r).2

end
end VOA.LogTensor.Ar
