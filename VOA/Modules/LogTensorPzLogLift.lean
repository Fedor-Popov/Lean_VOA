/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modules.LogTensorPzJacobiModes

/-! # Logarithmic coefficients reconstructed by the actual nilpotent defect -/

namespace VOA.LogTensor.Pz
open Module (End)
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable {M₁ M₂ M₃ : Type u} [AddCommGroup M₁] [Module ℂ M₁]
  [AddCommGroup M₂] [Module ℂ M₂] [AddCommGroup M₃] [Module ℂ M₃]
variable (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)

/-- The actual finite logarithmic reconstruction of a mode family. -/
noncomputable def logLift (F : ModeFamily (M₁ := M₁) (M₂ := M₂) (M₃ := M₃)) :
    LogModes M₁ M₂ M₃ := fun n k => (k.factorial:ℂ)⁻¹ • (nilDefect N₁ N₂ N₃ ^ k) (F n)

@[simp] theorem logLift_zero (F : ModeFamily (M₁ := M₁) (M₂ := M₂) (M₃ := M₃)) (n : ℂ) :
    logLift N₁ N₂ N₃ F n 0 = F n := by simp [logLift]

/-- The constructed coefficients have the genuine mode weight law. -/
theorem logLift_weight {F : ModeFamily (M₁ := M₁) (M₂ := M₂) (M₃ := M₃)}
    (hF : ∀ n, HasModeWeight N₁ N₂ N₃ n (F n)) (n : ℂ) (k : ℕ) :
    HasModeWeight N₁ N₂ N₃ n (logLift N₁ N₂ N₃ F n k) := by
  intro a b x y hx hy
  exact (N₃.weight (a+b-n-1)).smul_mem _ (nilDefect_pow_weight N₁ N₂ N₃ (hF n) k hx hy)

/-- Logarithmic finiteness is a theorem from the three actual Jordan bounds. -/
theorem logLift_logFinite {F : ModeFamily (M₁ := M₁) (M₂ := M₂) (M₃ := M₃)}
    (hF : ∀ n, HasModeWeight N₁ N₂ N₃ n (F n)) (x : M₁) (y : M₂) (n : ℂ) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → logLift N₁ N₂ N₃ F n k x y = 0 := by
  refine LogFin.induction_on N₁
    (C := fun x => ∃ K : ℕ, ∀ k : ℕ, K ≤ k → logLift N₁ N₂ N₃ F n k x y = 0)
    x ?_ ⟨0,fun _ _ => by simp⟩ ?_
  · intro a x hx
    refine LogFin.induction_on N₂
      (C := fun y => ∃ K : ℕ, ∀ k : ℕ, K ≤ k → logLift N₁ N₂ N₃ F n k x y = 0)
      y ?_ ⟨0,fun _ _ => by simp⟩ ?_
    · intro b y hy
      refine ⟨Module.finrank ℂ (N₁.weight a) + Module.finrank ℂ (N₂.weight b) +
        Module.finrank ℂ (N₃.weight (a+b-n-1)),fun k hk => ?_⟩
      simp only [logLift,LinearMap.smul_apply,LinearMap.add_apply]
      rw [nilDefect_pow_eq_zero N₁ N₂ N₃ (hF n) hx hy (by omega),smul_zero]
    · rintro y z ⟨K,hK⟩ ⟨L,hL⟩
      exact ⟨max K L,fun k hk => by rw [map_add,hK k (le_trans (le_max_left _ _) hk),
        hL k (le_trans (le_max_right _ _) hk),add_zero]⟩
  · rintro x z ⟨K,hK⟩ ⟨L,hL⟩
    exact ⟨max K L,fun k hk => by rw [map_add,LinearMap.add_apply,
      hK k (le_trans (le_max_left _ _) hk),hL k (le_trans (le_max_right _ _) hk),add_zero]⟩

/-- Lower truncation is uniform in logarithmic degree because all coefficients land
in the same actual output weight. -/
theorem logLift_truncated {F : ModeFamily (M₁ := M₁) (M₂ := M₂) (M₃ := M₃)}
    (hF : ∀ n, HasModeWeight N₁ N₂ N₃ n (F n)) (x : M₁) (y : M₂) (n : ℂ) :
    ∃ K : ℤ, ∀ j : ℤ, K ≤ j → ∀ k : ℕ, logLift N₁ N₂ N₃ F (n+j) k x y = 0 := by
  refine LogFin.induction_on N₁
    (C := fun x => ∃ K : ℤ, ∀ j : ℤ, K ≤ j → ∀ k : ℕ,
      logLift N₁ N₂ N₃ F (n+j) k x y = 0) x ?_ ⟨0,fun _ _ _ => by simp⟩ ?_
  · intro a x hx
    refine LogFin.induction_on N₂
      (C := fun y => ∃ K : ℤ, ∀ j : ℤ, K ≤ j → ∀ k : ℕ,
        logLift N₁ N₂ N₃ F (n+j) k x y = 0) y ?_ ⟨0,fun _ _ _ => by simp⟩ ?_
    · intro b y hy
      obtain ⟨B,hB⟩ := N₃.boundedBelow
      let K : ℤ := ⌈(a+b-n-1).re-B⌉
      have hK : (a+b-n-1).re-B ≤ (K:ℝ) := Int.le_ceil _
      refine ⟨K+1,fun j hj k => ?_⟩
      have hm := logLift_weight N₁ N₂ N₃ hF (n+j) k hx hy
      have hbot : N₃.weight (a+b-(n+j)-1) = ⊥ := by
        by_contra h
        have hb := hB _ h
        have hj' : ((K+1:ℤ):ℝ) ≤ (j:ℝ) := by exact_mod_cast hj
        simp only [Complex.sub_re,Complex.add_re,Complex.intCast_re,Complex.one_re] at hb hK
        push_cast at hj'
        linarith
      rwa [hbot,Submodule.mem_bot] at hm
    · rintro y z ⟨K,hK⟩ ⟨L,hL⟩
      exact ⟨max K L,fun j hj k => by rw [map_add,hK j (le_trans (le_max_left _ _) hj) k,
        hL j (le_trans (le_max_right _ _) hj) k,add_zero]⟩
  · rintro x z ⟨K,hK⟩ ⟨L,hL⟩
    exact ⟨max K L,fun j hj k => by rw [map_add,LinearMap.add_apply,
      hK j (le_trans (le_max_left _ _) hj) k,hL j (le_trans (le_max_right _ _) hj) k,add_zero]⟩

/-- Every reconstructed coefficient satisfies the genuine intertwiner Jacobi identity. -/
theorem logLift_jacobi {F : ModeFamily (M₁ := M₁) (M₂ := M₂) (M₃ := M₃)}
    (hF : IsJacobiFamily N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule F)
    (u : V) (x : M₁) (y : M₂) (ell m : ℤ) (n : ℂ) (k : ℕ) :
    (∑ᶠ i : ℤ, (negOnePow i * cbz ell i) •
      (mode (N₃.YM u) (ell+m-i) (logLift N₁ N₂ N₃ F (n+i) k x y) -
        negOnePow ell • logLift N₁ N₂ N₃ F (ell+n-i) k x (mode (N₂.YM u) (m+i) y))) =
      ∑ᶠ i : ℤ, cbz m i • logLift N₁ N₂ N₃ F (m+n-i) k (mode (N₁.YM u) (ell+i) x) y := by
  have h := hF.nilDefect_pow N₁ N₂ N₃ k
  have hs := (jacobiFamilies N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule).smul_mem
    (k.factorial:ℂ)⁻¹ h
  exact hs.jacobi u x y ell m n

/-- Precomposition with the actual L(-1) operator. -/
noncomputable def preLm1 : End ℂ (M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] M₃) where
  toFun F := F ∘ₗ Lm1 N₁.toWeakModule
  map_add' F G := by ext x y; simp
  map_smul' s F := by ext x y; simp

/-- The nilpotent defect commutes with L(-1) in the first input slot. -/
theorem nilDefect_comm_preLm1 : Commute (nilDefect N₁ N₂ N₃)
    (preLm1 (M₂ := M₂) (M₃ := M₃) N₁) := by
  ext F x y
  change N₃.L0nil (F (Lm1 N₁.toWeakModule x) y) -
    F (Lm1 N₁.toWeakModule (N₁.L0nil x)) y - F (Lm1 N₁.toWeakModule x) (N₂.L0nil y) =
    N₃.L0nil (F (Lm1 N₁.toWeakModule x) y) -
      F (N₁.L0nil (Lm1 N₁.toWeakModule x)) y - F (Lm1 N₁.toWeakModule x) (N₂.L0nil y)
  have h := DFunLike.congr_fun (Contra.L0nil_comm_mode N₁ W.conformalVector 0) x
  simp only [Module.End.mul_apply] at h
  rw [h]

/-- The coupled zeroth derivative equation supplied by P(1) compatibility. -/
def BaseDerivative (F : ModeFamily (M₁ := M₁) (M₂ := M₂) (M₃ := M₃)) : Prop :=
  ∀ n, preLm1 (M₂ := M₂) (M₃ := M₃) N₁ (F n) =
    (-n) • F (n-1) + nilDefect N₁ N₂ N₃ (F (n-1))

/-- The reconstructed coefficients satisfy exactly the logarithmic derivative law. -/
theorem logLift_derivative {F : ModeFamily (M₁ := M₁) (M₂ := M₂) (M₃ := M₃)}
    (hF : BaseDerivative N₁ N₂ N₃ F) (x : M₁) (n : ℂ) (k : ℕ) :
    logLift N₁ N₂ N₃ F n k (Lm1 N₁.toWeakModule x) =
      (-n) • logLift N₁ N₂ N₃ F (n-1) k x + ((k:ℂ)+1) • logLift N₁ N₂ N₃ F (n-1) (k+1) x := by
  have hc := (nilDefect_comm_preLm1 N₁ N₂ N₃).pow_left k
  have he := DFunLike.congr_fun hc (F n)
  rw [Module.End.mul_apply,Module.End.mul_apply,hF n,map_add,map_smul] at he
  have hpow : (nilDefect N₁ N₂ N₃ ^ k) (nilDefect N₁ N₂ N₃ (F (n-1))) =
      (nilDefect N₁ N₂ N₃ ^ (k+1)) (F (n-1)) := by rw [pow_succ,Module.End.mul_apply]
  rw [hpow] at he
  ext y
  have hh := congrArg (fun G : M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] M₃ => G x y) he
  change (-n) • ((nilDefect N₁ N₂ N₃ ^ k) (F (n-1))) x y +
    ((nilDefect N₁ N₂ N₃ ^ (k+1)) (F (n-1))) x y =
    ((nilDefect N₁ N₂ N₃ ^ k) (F n)) (Lm1 N₁.toWeakModule x) y at hh
  simp only [logLift,LinearMap.smul_apply,LinearMap.add_apply]
  rw [← hh,smul_add,smul_comm (k.factorial:ℂ)⁻¹ (-n)]
  congr 1
  rw [smul_smul]
  congr 1
  rw [Nat.factorial_succ]
  push_cast
  field_simp

/-- Actual logarithmic reconstruction: the four defining intertwiner axioms follow
from concrete base Jacobi, weight, and coupled derivative equations. -/
theorem isLogIntertwining_logLift {F : ModeFamily (M₁ := M₁) (M₂ := M₂) (M₃ := M₃)}
    (hJ : IsJacobiFamily N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule F)
    (hW : ∀ n, HasModeWeight N₁ N₂ N₃ n (F n))
    (hD : BaseDerivative N₁ N₂ N₃ F) :
    IsLogIntertwining N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule
      (logLift N₁ N₂ N₃ F) where
  logFinite := logLift_logFinite N₁ N₂ N₃ hW
  truncation := logLift_truncated N₁ N₂ N₃ hW
  L_neg_one := logLift_derivative N₁ N₂ N₃ hD
  jacobi := logLift_jacobi N₁ N₂ N₃ hJ

end VOA.LogTensor.Pz
