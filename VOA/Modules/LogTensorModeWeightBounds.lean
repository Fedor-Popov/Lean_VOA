/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modules.LogTensorPzNilDefect

/-! # A genuine output-weight bound gives uniform logarithmic truncation

This applies to any actual bilinear logarithmic coefficient data whose output
weights obey the genuine mode law, independently of its Jacobi identity.
-/
namespace VOA.LogTensor.Pz
universe u
variable {V M₁ M₂ M₃ : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] {W : VertexOperatorAlgebra V}

/-- The actual lower output-weight bound is uniform in logarithmic degree. -/
theorem truncation_of_mode_weight (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂)
    (N₃ : LogVModule W M₃) (Y : LogModes M₁ M₂ M₃)
    (hY : ∀ n k, HasModeWeight N₁ N₂ N₃ n (Y n k)) (x : M₁) (y : M₂) (n : ℂ) :
    ∃ K : ℤ, ∀ j : ℤ, K ≤ j → ∀ k : ℕ, Y (n+j) k x y = 0 := by
  refine LogFin.induction_on N₁ (C := fun x =>
    ∃ K : ℤ, ∀ j : ℤ, K ≤ j → ∀ k : ℕ, Y (n+j) k x y = 0) x ?_
      ⟨0,fun _ _ _ => by simp⟩ ?_
  · intro a x hx
    refine LogFin.induction_on N₂ (C := fun y =>
      ∃ K : ℤ, ∀ j : ℤ, K ≤ j → ∀ k : ℕ, Y (n+j) k x y = 0) y ?_
        ⟨0,fun _ _ _ => by simp⟩ ?_
    · intro b y hy
      obtain ⟨B,hB⟩ := N₃.boundedBelow
      let K : ℤ := ⌈(a+b-n-1).re-B⌉
      have hK : (a+b-n-1).re-B ≤ (K:ℝ) := Int.le_ceil _
      refine ⟨K+1,fun j hj k => ?_⟩
      have hm := hY (n+j) k hx hy
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

end VOA.LogTensor.Pz
