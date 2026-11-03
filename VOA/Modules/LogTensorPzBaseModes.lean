/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modules.LogTensorPzReconstruction
import VOA.Modules.LogTensorPzMaximal
import VOA.Modules.LogTensorContraCoordinates
import VOA.Modules.C2RigidContraClose

/-! # Zeroth logarithmic modes from actual compatible generalized-module maps

The compatible-map datum is expressed in the actual algebraic tensor dual and
uses the genuine weak-module modes of its generalized source. Its homogeneous
matrix coefficients define zeroth logarithmic modes into the genuine restricted
dual, with the exact weight law and lower truncation.
-/

namespace VOA.LogTensor.Pz
open Module (End Dual)
open scoped BigOperators
open VOA.Huang.PzTensorRho
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable {M₁ M₂ R : Type u} [AddCommGroup M₁] [Module ℂ M₁]
  [AddCommGroup M₂] [Module ℂ M₂] [AddCommGroup R] [Module ℂ R]
variable (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N : LogVModule W R)

/-- A map from a genuine generalized module into compatible tensor-dual forms.
The intertwining condition uses its actual mode action and the actual coproduct twist. -/
structure CompatibleMap (psi : R →ₗ[ℂ] BilinearDual (M₁ := M₁) (M₂ := M₂)) : Prop where
  map_mode : ∀ (d : ℤ) (u : V), u ∈ W.grading d → ∀ (p : ℤ) (r : R),
    psi (mode (N.YM u) p r) = tauHat N₁.toWeakModule N₂.toWeakModule d u p (psi r)
  truncated : ∀ r : R, ∀ (d : ℤ) (u : V), u ∈ W.grading d →
    TruncAt N₁.toWeakModule N₂.toWeakModule u (psi r)
  compatible : ∀ r : R, ∀ (d : ℤ) (u : V), u ∈ W.grading d →
    CompatAt N₁.toWeakModule N₂.toWeakModule u (psi r)

variable (psi : R →ₗ[ℂ] BilinearDual (M₁ := M₁) (M₂ := M₂))

/-- A homogeneous matrix coefficient as a functional on the actual source module's
weight space. -/
noncomputable def baseFunctional (a b c : ℂ) (x : N₁.weight a) (y : N₂.weight b) :
    Dual ℂ (N.weight c) where
  toFun r := psi r.1 x y
  map_add' r s := by simp only [Submodule.coe_add, map_add, LinearMap.add_apply]
  map_smul' s r := by
    simp only [Submodule.coe_smul, map_smul, LinearMap.smul_apply, RingHom.id_apply]

/-- The matrix coefficient placed at its genuine output generalized weight. -/
noncomputable def baseModeBlock (n a b : ℂ) :
    N₁.weight a →ₗ[ℂ] N₂.weight b →ₗ[ℂ] C2Rigid.RestrictedDual N.toGW :=
  LinearMap.mk₂ ℂ (fun x y =>
    DirectSum.lof ℂ ℂ (fun c => Dual ℂ (N.weight c)) (a+b-n-1)
      (baseFunctional N₁ N₂ N psi a b (a+b-n-1) x y))
    (fun x x' y => by
      dsimp only
      have h : baseFunctional N₁ N₂ N psi a b (a+b-n-1) (x+x') y =
        baseFunctional N₁ N₂ N psi a b (a+b-n-1) x y +
        baseFunctional N₁ N₂ N psi a b (a+b-n-1) x' y := by ext r; simp [baseFunctional]
      rw [h, map_add]; rfl)
    (fun s x y => by
      dsimp only
      have h : baseFunctional N₁ N₂ N psi a b (a+b-n-1) (s • x) y =
        s • baseFunctional N₁ N₂ N psi a b (a+b-n-1) x y := by ext r; simp [baseFunctional]
      rw [h, map_smul]; rfl)
    (fun x y y' => by
      dsimp only
      have h : baseFunctional N₁ N₂ N psi a b (a+b-n-1) x (y+y') =
        baseFunctional N₁ N₂ N psi a b (a+b-n-1) x y +
        baseFunctional N₁ N₂ N psi a b (a+b-n-1) x y' := by ext r; simp [baseFunctional]
      rw [h, map_add]; rfl)
    (fun s x y => by
      dsimp only
      have h : baseFunctional N₁ N₂ N psi a b (a+b-n-1) x (s • y) =
        s • baseFunctional N₁ N₂ N psi a b (a+b-n-1) x y := by ext r; simp [baseFunctional]
      rw [h, map_smul]; rfl)

/-- Zeroth logarithmic modes on arbitrary inputs, assembled from actual generalized
weight spaces. -/
noncomputable def baseModes (n : ℂ) : M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] C2Rigid.RestrictedDual N.toGW :=
  fromBlocks N₁ N₂ (baseModeBlock N₁ N₂ N psi n)

theorem baseModes_homogeneous (n : ℂ) {a b : ℂ} {x : M₁} {y : M₂}
    (hx : x ∈ N₁.weight a) (hy : y ∈ N₂.weight b) :
    baseModes N₁ N₂ N psi n x y =
      DirectSum.lof ℂ ℂ (fun c => Dual ℂ (N.weight c)) (a+b-n-1)
        (baseFunctional N₁ N₂ N psi a b (a+b-n-1) ⟨x,hx⟩ ⟨y,hy⟩) := by
  rw [baseModes, fromBlocks_homogeneous N₁ N₂ _ hx hy]
  rfl

/-- The defining paired matrix coefficient, including the vanishing of every foreign
output weight. -/
theorem pair_baseModes (n : ℂ) {a b c : ℂ} {x : M₁} {y : M₂} {r : R}
    (hx : x ∈ N₁.weight a) (hy : y ∈ N₂.weight b) (hr : r ∈ N.weight c) :
    C2Rigid.dualPairing N.toGW r (baseModes N₁ N₂ N psi n x y) =
      if c = a+b-n-1 then psi r x y else 0 := by
  rw [baseModes_homogeneous N₁ N₂ N psi n hx hy]
  erw [C2Rigid.dualPairing_lof N.toGW r (a+b-n-1)]
  split_ifs with h
  · subst c
    change psi (internalProjTo N.toGW.isInternal (a+b-n-1) r : R) x y = psi r x y
    rw [C2Rigid.internalProjTo_coe_mem N.toGW hr]
  · rw [C2Rigid.internalProjTo_eq_zero_of_ne N.toGW hr (Ne.symm h), map_zero]

private theorem dual_eq_zero_of_bot {c : ℂ} (hc : N.weight c = ⊥)
    (f : Dual ℂ (N.weight c)) : f = 0 := by
  ext r
  have h : (r:R) = 0 := (Submodule.eq_bot_iff _).mp hc r r.2
  have hr : r = 0 := Subtype.ext h
  rw [hr, map_zero]
  rfl

/-- Lower truncation follows solely from the actual lower bound of the target
restricted dual. It does not require semisimplicity of any L(0) operator. -/
theorem baseModes_truncated_homogeneous {a b : ℂ} {x : M₁} {y : M₂}
    (hx : x ∈ N₁.weight a) (hy : y ∈ N₂.weight b) (n : ℂ) :
    ∃ K : ℤ, ∀ j : ℤ, K ≤ j → baseModes N₁ N₂ N psi (n+j) x y = 0 := by
  obtain ⟨B,hB⟩ := N.boundedBelow
  let K : ℤ := ⌈(a+b-n-1).re-B⌉
  have hK : (a+b-n-1).re-B ≤ (K:ℝ) := Int.le_ceil _
  refine ⟨K+1,fun j hj => ?_⟩
  rw [baseModes_homogeneous N₁ N₂ N psi (n+j) hx hy]
  have hbot : N.weight (a+b-(n+j)-1) = ⊥ := by
    by_contra h
    have hb := hB _ h
    have hj' : ((K+1:ℤ):ℝ) ≤ (j:ℝ) := by exact_mod_cast hj
    simp only [Complex.sub_re, Complex.add_re, Complex.intCast_re, Complex.one_re] at hb hK
    push_cast at hj'
    linarith
  have hz := dual_eq_zero_of_bot N hbot
    (baseFunctional N₁ N₂ N psi a b (a+b-(n+j)-1) ⟨x,hx⟩ ⟨y,hy⟩)
  rw [hz, map_zero]
  rfl

theorem baseModes_truncated (x : M₁) (y : M₂) (n : ℂ) :
    ∃ K : ℤ, ∀ j : ℤ, K ≤ j → baseModes N₁ N₂ N psi (n+j) x y = 0 := by
  refine LogFin.induction_on N₁
    (C := fun x => ∃ K : ℤ, ∀ j : ℤ, K ≤ j → baseModes N₁ N₂ N psi (n+j) x y = 0)
    x ?_ ⟨0,fun _ _ => by simp⟩ ?_
  · intro a x hx
    refine LogFin.induction_on N₂
      (C := fun y => ∃ K : ℤ, ∀ j : ℤ, K ≤ j → baseModes N₁ N₂ N psi (n+j) x y = 0)
      y (fun b y hy => baseModes_truncated_homogeneous N₁ N₂ N psi hx hy n)
      ⟨0,fun _ _ => by simp⟩ ?_
    rintro y y' ⟨K,hK⟩ ⟨L,hL⟩
    exact ⟨max K L,fun j hj => by
      rw [map_add,hK j (le_trans (le_max_left _ _) hj),hL j (le_trans (le_max_right _ _) hj),add_zero]⟩
  · rintro x x' ⟨K,hK⟩ ⟨L,hL⟩
    exact ⟨max K L,fun j hj => by
      rw [map_add,LinearMap.add_apply,hK j (le_trans (le_max_left _ _) hj),
        hL j (le_trans (le_max_right _ _) hj),add_zero]⟩

end VOA.LogTensor.Pz
