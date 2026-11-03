/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modules.LogTensorPzReconstruction
import VOA.Modules.LogTensorContraNilModes

/-! # The nilpotent defect reconstructing logarithmic mode coefficients

The three actual nilpotent L(0) parts act on bilinear maps by postcomposition
and the two precompositions. Their difference preserves the mode weight law
and is locally nilpotent on each finite triple of generalized weight spaces.
-/

namespace VOA.LogTensor.Pz
open Module (End)
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable {M₁ M₂ M₃ : Type u} [AddCommGroup M₁] [Module ℂ M₁]
  [AddCommGroup M₂] [Module ℂ M₂] [AddCommGroup M₃] [Module ℂ M₃]

/-- The three-slot defect for arbitrary actual linear endomorphisms. -/
noncomputable def bilinearDefect (E₁ : End ℂ M₁) (E₂ : End ℂ M₂) (E₃ : End ℂ M₃) :
    End ℂ (M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] M₃) where
  toFun F := LinearMap.mk₂ ℂ (fun x y => E₃ (F x y) - F (E₁ x) y - F x (E₂ y))
    (fun x x' y => by dsimp only; simp only [map_add,LinearMap.add_apply]; module)
    (fun s x y => by dsimp only; simp only [map_smul,LinearMap.smul_apply]; module)
    (fun x y y' => by dsimp only; simp only [map_add]; module)
    (fun s x y => by dsimp only; simp only [map_smul]; module)
  map_add' F G := by
    ext x y
    simp only [LinearMap.mk₂_apply,LinearMap.add_apply,map_add]
    module
  map_smul' s F := by
    ext x y
    simp only [LinearMap.mk₂_apply,LinearMap.smul_apply,map_smul,RingHom.id_apply]
    module

@[simp] theorem bilinearDefect_apply (E₁ : End ℂ M₁) (E₂ : End ℂ M₂) (E₃ : End ℂ M₃)
    (F : M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] M₃) (x : M₁) (y : M₂) :
    bilinearDefect E₁ E₂ E₃ F x y = E₃ (F x y) - F (E₁ x) y - F x (E₂ y) := rfl

variable (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)

/-- The actual logarithmic defect uses the genuine nilpotent Jordan parts. -/
noncomputable def nilDefect : End ℂ (M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] M₃) :=
  bilinearDefect N₁.L0nil N₂.L0nil N₃.L0nil

/-- The mode's actual generalized weight-shift law. -/
def HasModeWeight (n : ℂ) (F : M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] M₃) : Prop :=
  ∀ {a b : ℂ} {x : M₁} {y : M₂}, x ∈ N₁.weight a → y ∈ N₂.weight b →
    F x y ∈ N₃.weight (a+b-n-1)

/-- Every power of the logarithmic defect preserves the same actual output weight. -/
theorem nilDefect_pow_weight {n : ℂ} {F : M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] M₃}
    (hF : HasModeWeight N₁ N₂ N₃ n F) (k : ℕ) :
    HasModeWeight N₁ N₂ N₃ n ((nilDefect N₁ N₂ N₃ ^ k) F) := by
  induction k with
  | zero =>
    intro a b x y hx hy
    simpa using hF hx hy
  | succ k ih =>
    intro a b x y hx hy
    rw [pow_succ',Module.End.mul_apply]
    change N₃.L0nil (((nilDefect N₁ N₂ N₃ ^ k) F) x y) -
      ((nilDefect N₁ N₂ N₃ ^ k) F) (N₁.L0nil x) y -
      ((nilDefect N₁ N₂ N₃ ^ k) F) x (N₂.L0nil y) ∈ N₃.weight (a+b-n-1)
    exact Submodule.sub_mem _ (Submodule.sub_mem _
      (N₃.L0nil_mem_weight (ih hx hy)) (ih (N₁.L0nil_mem_weight hx) hy))
      (ih hx (N₂.L0nil_mem_weight hy))

/-- On a genuine finite generalized weight space the nilpotent part is killed
by the dimension of that space. -/
theorem nilpotent_weight_bound {M : Type u} [AddCommGroup M] [Module ℂ M]
    (N : LogVModule W M) {a : ℂ} {x : M} (hx : x ∈ N.weight a) :
    (N.L0nil ^ Module.finrank ℂ (N.weight a)) x = 0 := by
  rw [N.L0nil_pow_apply_of_mem _ hx]
  haveI := N.finrank a
  haveI : FiniteDimensional ℂ (N.L0op.maxGenEigenspace a) := by
    rw [← N.weight_eq_maxGenEigenspace]; infer_instance
  have h := sub_pow_finrank_apply_eq_zero N.L0op a (N.weight_le_maxGenEigenspace' a hx)
  rwa [← N.weight_eq_maxGenEigenspace] at h

/-- The pointwise nilpotence engine. Output powers plus logarithmic-defect powers
vanish once the three Jordan-block bounds are exceeded. -/
theorem nilDefect_vanish {n : ℂ} {F : M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] M₃}
    (hF : HasModeWeight N₁ N₂ N₃ n F) (a b : ℂ) (r : ℕ)
    (hr : ∀ z ∈ N₃.weight (a+b-n-1), (N₃.L0nil ^ r) z = 0) :
    ∀ (k t p q : ℕ) (x : M₁) (y : M₂), x ∈ N₁.weight a → y ∈ N₂.weight b →
      (N₁.L0nil ^ p) x = 0 → (N₂.L0nil ^ q) y = 0 → r+p+q ≤ t+k+2 →
      (N₃.L0nil ^ t) (((nilDefect N₁ N₂ N₃ ^ k) F) x y) = 0 := by
  intro k
  induction k with
  | zero =>
    intro t p q x y hx hy hp hq hle
    rcases Nat.eq_zero_or_pos p with rfl | hp0
    · rw [pow_zero,Module.End.one_apply] at hp
      simp [hp]
    rcases Nat.eq_zero_or_pos q with rfl | hq0
    · rw [pow_zero,Module.End.one_apply] at hq
      simp [hq]
    rw [pow_zero,Module.End.one_apply,show t=(t-r)+r by omega,pow_add,Module.End.mul_apply,
      hr _ (hF hx hy),map_zero]
  | succ k ih =>
    intro t p q x y hx hy hp hq hle
    rcases Nat.eq_zero_or_pos p with rfl | hp0
    · rw [pow_zero,Module.End.one_apply] at hp
      simp [hp]
    rcases Nat.eq_zero_or_pos q with rfl | hq0
    · rw [pow_zero,Module.End.one_apply] at hq
      simp [hq]
    obtain ⟨p',rfl⟩ : ∃ p',p=p'+1 := ⟨p-1,by omega⟩
    obtain ⟨q',rfl⟩ : ∃ q',q=q'+1 := ⟨q-1,by omega⟩
    have h₀ : (N₃.L0nil ^ t) (N₃.L0nil (((nilDefect N₁ N₂ N₃ ^ k) F) x y)) = 0 := by
      rw [← Module.End.mul_apply,← pow_succ]
      exact ih (t+1) (p'+1) (q'+1) x y hx hy hp hq (by omega)
    have h₁ : (N₃.L0nil ^ t) (((nilDefect N₁ N₂ N₃ ^ k) F) (N₁.L0nil x) y) = 0 :=
      ih t p' (q'+1) _ y (N₁.L0nil_mem_weight hx) hy
        (by rw [← Module.End.mul_apply,← pow_succ]; exact hp) hq (by omega)
    have h₂ : (N₃.L0nil ^ t) (((nilDefect N₁ N₂ N₃ ^ k) F) x (N₂.L0nil y)) = 0 :=
      ih t (p'+1) q' x _ hx (N₂.L0nil_mem_weight hy)
        hp (by rw [← Module.End.mul_apply,← pow_succ]; exact hq) (by omega)
    rw [pow_succ',Module.End.mul_apply]
    change (N₃.L0nil ^ t) (N₃.L0nil (((nilDefect N₁ N₂ N₃ ^ k) F) x y) -
      ((nilDefect N₁ N₂ N₃ ^ k) F) (N₁.L0nil x) y -
      ((nilDefect N₁ N₂ N₃ ^ k) F) x (N₂.L0nil y)) = 0
    rw [map_sub,map_sub,h₀,h₁,h₂,sub_zero,sub_zero]

/-- A finite log-degree bound derived from the actual three generalized weight spaces. -/
theorem nilDefect_pow_eq_zero {n : ℂ} {F : M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] M₃}
    (hF : HasModeWeight N₁ N₂ N₃ n F) {a b : ℂ} {x : M₁} {y : M₂}
    (hx : x ∈ N₁.weight a) (hy : y ∈ N₂.weight b) {k : ℕ}
    (hk : Module.finrank ℂ (N₁.weight a) + Module.finrank ℂ (N₂.weight b) +
      Module.finrank ℂ (N₃.weight (a+b-n-1)) ≤ k+2) :
    ((nilDefect N₁ N₂ N₃ ^ k) F) x y = 0 := by
  have h := nilDefect_vanish N₁ N₂ N₃ hF a b (Module.finrank ℂ (N₃.weight (a+b-n-1)))
    (fun z hz => nilpotent_weight_bound N₃ hz) k 0
    (Module.finrank ℂ (N₁.weight a)) (Module.finrank ℂ (N₂.weight b)) x y hx hy
    (nilpotent_weight_bound N₁ hx) (nilpotent_weight_bound N₂ hy) (by omega)
  simpa using h

end VOA.LogTensor.Pz
