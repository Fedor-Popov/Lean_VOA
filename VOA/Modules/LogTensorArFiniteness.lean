/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modules.LogTensorArModes
import VOA.Modules.LogTensorModeWeightBounds

/-! # Genuine polynomial-log finiteness and uniform truncation of A_r

The first nilpotent order bounds l. The genuine logarithmic weight-triple bound
then kills each remaining degree k-l in its finite L(1) tower. The actual target
lower weight bound gives truncation uniform in every logarithmic degree.
-/
namespace VOA.LogTensor.Ar
open Module (End Dual)
open scoped BigOperators
open Pz Contra
universe u
variable {V M₁ M₂ M₃ : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] {W : VertexOperatorAlgebra V}

/-- Each genuine opposite-coordinate first term has weight a-j. -/
theorem firstTermEnd_weight (N : LogVModule W M₁) (s : ℂ) (j l : ℕ)
    {a : ℂ} {x : M₁} (hx : x ∈ N.weight a) :
    firstTermEnd N s j l x ∈ N.weight (a-j) :=
  L1_pow_mem_weight N.toGW (L0exp_mem_weight N s (L0nil_pow_mem_weight N hx l)) j

/-- The actual nilpotent dimension bound kills every coefficient with large l. -/
theorem firstTermEnd_zero_of_nil_bound (N : LogVModule W M₁) (s : ℂ) (j l : ℕ)
    {a : ℂ} {x : M₁} (hx : x ∈ N.weight a)
    (hl : Module.finrank ℂ (N.weight a) ≤ l) : firstTermEnd N s j l x = 0 := by
  change (L1 N.toGW ^ j) (L0exp N s ((N.L0nil ^ l) x)) = 0
  rw [VOA.pow_apply_eq_zero_of_le (nilpotent_weight_bound N hx) hl,map_zero,map_zero]

variable (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
variable (Y : LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule)

/-- The A_r log polynomial is finite on a genuine homogeneous input pair, by the
actual first Jordan bound and actual original-intertwiner log-degree bounds. -/
theorem modes_logFinite_homogeneous (r : ℤ) (n : ℂ) {a c : ℂ}
    {x : M₁} {t : C2Rigid.RestrictedDual N₃.toGW}
    (hx : x ∈ N₁.weight a) (ht : t ∈ (contraLog N₃).weight c) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → modes N₁ N₂ N₃ Y r n k x t = 0 := by
  classical
  let b : ℂ := a+c-n-1
  let D := Module.finrank ℂ (N₁.weight a)
  let S := ∑ j ∈ Finset.range (L1Cutoff N₁ a), Module.finrank ℂ (N₁.weight (a-j))
  let K := S+Module.finrank ℂ (N₂.weight b)+Module.finrank ℂ (N₃.weight c)+D
  refine ⟨K,fun k hk => ?_⟩
  rw [modes_homogeneous N₁ N₂ N₃ Y r n k hx ht]
  have hz : (functional N₁ N₂ N₃ Y r n k a x t).comp (N₂.weight b).subtype = 0 := by
    apply LinearMap.ext
    intro y
    change functional N₁ N₂ N₃ Y r n k a x t y = 0
    simp only [functional,LinearMap.coe_sum,Finset.sum_apply,LinearMap.smul_apply,
      smul_eq_mul]
    apply Finset.sum_eq_zero
    intro j hj
    apply Finset.sum_eq_zero
    intro l hl
    rw [matrixTerm_apply]
    by_cases hD : D ≤ l
    · rw [firstTermEnd_zero_of_nil_bound N₁ (phase r) j l hx hD,map_zero,
        LinearMap.zero_apply]
      change coefficient k j l * C2Rigid.dualPairingFlip N₃.toGW t 0 = 0
      rw [map_zero,mul_zero]
    · have hS : Module.finrank ℂ (N₁.weight (a-j)) ≤ S :=
        Finset.single_le_sum
          (fun (z : ℕ) _ => Nat.zero_le (Module.finrank ℂ (N₁.weight (a-(z:ℂ))))) hj
      have hweight : (a-j)+b-(2*a-j-n-2)-1 = c := by dsimp [b]; ring
      have hlog : Y.1 (2*a-j-n-2) (k-l) (firstTermEnd N₁ (phase r) j l x) y = 0 := by
        apply Y.2.log_degree_le (firstTermEnd_weight N₁ (phase r) j l hx) y.2
        rw [hweight]
        dsimp [K] at hk
        omega
      rw [hlog]
      change coefficient k j l * C2Rigid.dualPairingFlip N₃.toGW t 0 = 0
      rw [map_zero,mul_zero]
  change DirectSum.lof ℂ ℂ (fun b => Dual ℂ (N₂.weight b)) b
    ((functional N₁ N₂ N₃ Y r n k a x t).comp (N₂.weight b).subtype) = 0
  rw [hz,map_zero]

/-- Genuine A_r coefficients have finite log degree on all actual inputs. -/
theorem modes_logFinite (r : ℤ) (x : M₁) (t : C2Rigid.RestrictedDual N₃.toGW) (n : ℂ) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → modes N₁ N₂ N₃ Y r n k x t = 0 := by
  refine LogFin.induction_on N₁ (C := fun x =>
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → modes N₁ N₂ N₃ Y r n k x t = 0) x ?_
      ⟨0,fun _ _ => by simp⟩ ?_
  · intro a x hx
    refine LogFin.induction_on (contraLog N₃) (C := fun t =>
      ∃ K : ℕ, ∀ k : ℕ, K ≤ k → modes N₁ N₂ N₃ Y r n k x t = 0) t ?_
        ⟨0,fun _ _ => by simp⟩ ?_
    · intro c t ht
      exact modes_logFinite_homogeneous N₁ N₂ N₃ Y r n hx ht
    · rintro t z ⟨K,hK⟩ ⟨L,hL⟩
      exact ⟨max K L,fun k hk => by rw [map_add,hK k (le_trans (le_max_left _ _) hk),
        hL k (le_trans (le_max_right _ _) hk),add_zero]⟩
  · rintro x z ⟨K,hK⟩ ⟨L,hL⟩
    exact ⟨max K L,fun k hk => by rw [map_add,LinearMap.add_apply,
      hK k (le_trans (le_max_left _ _) hk),hL k (le_trans (le_max_right _ _) hk),add_zero]⟩

/-- Genuine A_r truncation is uniform in all actual logarithmic coefficients. -/
theorem modes_truncated (r : ℤ) (x : M₁) (t : C2Rigid.RestrictedDual N₃.toGW) (n : ℂ) :
    ∃ K : ℤ, ∀ j : ℤ, K ≤ j → ∀ k : ℕ, modes N₁ N₂ N₃ Y r (n+j) k x t = 0 :=
  truncation_of_mode_weight N₁ (contraLog N₃) (contraLog N₂)
    (modes N₁ N₂ N₃ Y r) (modes_weight N₁ N₂ N₃ Y r) x t n

end VOA.LogTensor.Ar
