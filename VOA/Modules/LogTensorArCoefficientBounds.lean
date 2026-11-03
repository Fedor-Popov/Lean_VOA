/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modules.LogTensorArCoordinates
import VOA.Modules.LogTensorArPolynomial

/-! # Genuine coefficient bounds for the FHL A-coordinate polynomial -/
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

/-- A uniform genuine original log bound along the finite first-state L(1) tower. -/
def coordinateLogBound (n a b : ℂ) : ℕ :=
  (∑ j ∈ Finset.range (L1Cutoff N₁ a), Module.finrank ℂ (N₁.weight (a-j))) +
    Module.finrank ℂ (N₂.weight b)+Module.finrank ℂ (N₃.weight (b+n+1-a))

/-- Actual original coefficients vanish uniformly along every first nilpotent term. -/
theorem firstTerm_high_log_zero (r : ℤ) (n : ℂ) {a b : ℂ} {x : M₁} {y : M₂}
    (hx : x ∈ N₁.weight a) (hy : y ∈ N₂.weight b) {j l q : ℕ}
    (hj : j ∈ Finset.range (L1Cutoff N₁ a)) (hq : coordinateLogBound N₁ N₂ N₃ n a b ≤ q) :
    Y.1 (2*a-j-n-2) q (firstTermEnd N₁ (phase r) j l x) y=0 := by
  have hS : Module.finrank ℂ (N₁.weight (a-j)) ≤
      ∑ j ∈ Finset.range (L1Cutoff N₁ a), Module.finrank ℂ (N₁.weight (a-j)) :=
    Finset.single_le_sum (fun (z : ℕ) _ => Nat.zero_le (Module.finrank ℂ (N₁.weight (a-(z:ℂ))))) hj
  apply Y.2.log_degree_le (firstTermEnd_weight N₁ (phase r) j l hx) hy
  rw [show (a-j)+b-(2*a-j-n-2)-1=b+n+1-a by ring]
  dsimp [coordinateLogBound] at hq
  omega

/-- The scalar paired coordinate matrices have the same actual uniform finite log bound. -/
theorem matrixTerm_high_log_zero (r : ℤ) (n : ℂ) {a b : ℂ} {x : M₁} {y : M₂}
    (hx : x ∈ N₁.weight a) (hy : y ∈ N₂.weight b) (t : C2Rigid.RestrictedDual N₃.toGW)
    {j l q : ℕ} (hj : j ∈ Finset.range (L1Cutoff N₁ a))
    (hq : coordinateLogBound N₁ N₂ N₃ n a b ≤ q) :
    matrixTerm N₁ N₂ N₃ Y (phase r) (2*a-j-n-2) q j l x t y=0 := by
  rw [matrixTerm_apply,firstTerm_high_log_zero N₁ N₂ N₃ Y r n hx hy hj hq]
  exact map_zero (C2Rigid.dualPairingFlip N₃.toGW t)

/-- Every paired literal FHL coefficient is cut off by the genuine first Jordan and log bounds. -/
theorem functional_high_log_zero (r : ℤ) (n : ℂ) {a b : ℂ} {x : M₁} {y : M₂}
    (hx : x ∈ N₁.weight a) (hy : y ∈ N₂.weight b) (t : C2Rigid.RestrictedDual N₃.toGW)
    {k : ℕ} (hk : Module.finrank ℂ (N₁.weight a)+coordinateLogBound N₁ N₂ N₃ n a b ≤ k) :
    functional N₁ N₂ N₃ Y r n k a x t y=0 := by
  simp only [functional,LinearMap.coe_sum,Finset.sum_apply,LinearMap.smul_apply,smul_eq_mul]
  apply Finset.sum_eq_zero
  intro j hj
  apply Finset.sum_eq_zero
  intro l hl
  by_cases hDl : Module.finrank ℂ (N₁.weight a) ≤ l
  · rw [matrixTerm_apply,firstTermEnd_zero_of_nil_bound N₁ (phase r) j l hx hDl,map_zero,LinearMap.zero_apply]
    change coefficient k j l * C2Rigid.dualPairingFlip N₃.toGW t 0=0
    rw [map_zero,mul_zero]
  · rw [matrixTerm_high_log_zero N₁ N₂ N₃ Y r n hx hy t hj (by omega),mul_zero]

/-- The actual inverse-log coordinate term has its literal finite double coefficient expansion. -/
theorem coordinate_term_eval_sum (r : ℤ) (ell n : ℂ) {a b : ℂ} {x : M₁} {y : M₂}
    (hx : x ∈ N₁.weight a) (hy : y ∈ N₂.weight b) (t : C2Rigid.RestrictedDual N₃.toGW)
    {j : ℕ} (hj : j ∈ Finset.range (L1Cutoff N₁ a)) :
    C2Rigid.dualPairing N₃.toGW
      (logShift (-ell) Y.1 (2*a-j-n-2) 0
        (firstTermEnd N₁ (phase r) j 0 (nilExp N₁ (-2*ell) x)) y) t =
      ∑ l ∈ Finset.range (Module.finrank ℂ (N₁.weight a)), ((-2*ell)^l/(l.factorial:ℂ)) *
        ∑ q ∈ Finset.range (coordinateLogBound N₁ N₂ N₃ n a b), (-ell)^q *
          matrixTerm N₁ N₂ N₃ Y (phase r) (2*a-j-n-2) q j l x t y := by
  have hcut : ∀ q, coordinateLogBound N₁ N₂ N₃ n a b ≤ q →
      Y.1 (2*a-j-n-2) q (firstTermEnd N₁ (phase r) j 0 (nilExp N₁ (-2*ell) x)) y=0 := by
    intro q hq
    exact firstTerm_high_log_zero N₁ N₂ N₃ Y r n (nilExp_mem_weight N₁ (-2*ell) hx) hy hj hq
  rw [logShift_eq_sum Y.2.logFinite (coordinateLogBound N₁ N₂ N₃ n a b) hcut,
    firstTermEnd_nil_finite N₁ r ell j hx]
  change C2Rigid.dualPairingFlip N₃.toGW t
    (∑ q ∈ Finset.range (coordinateLogBound N₁ N₂ N₃ n a b), shc (-ell) q 0 •
      Y.1 (2*a-j-n-2) q (∑ l ∈ Finset.range (Module.finrank ℂ (N₁.weight a)),
        ((-2*ell)^l/(l.factorial:ℂ)) • firstTermEnd N₁ (phase r) j l x) y) = _
  simp only [map_sum,map_smul,LinearMap.sum_apply,LinearMap.smul_apply,
    Finset.smul_sum,C2Rigid.dualPairingFlip_apply,shc,Nat.choose_zero_right,Nat.cast_one,
    one_mul,Nat.sub_zero,smul_eq_mul,Finset.mul_sum,matrixTerm_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l hl
  apply Finset.sum_congr rfl
  intro q hq
  ring

end
end VOA.LogTensor.Ar
