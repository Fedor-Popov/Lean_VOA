/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modules.LogTensorSkewEquiv
import VOA.Modules.LogTensorPrecompose

/-! # Genuine logarithmic skew naturality

Actual weak-module maps commute with the finite translation sums and finite
logarithmic shift polynomials defining Ω. This proves naturality in the output
and exchange of the two source maps without an ordinary-module premise.
-/
namespace VOA.LogTensor
open Module (End)
open scoped BigOperators
open VOA.LogSkew
universe u
variable {V M₁ M₂ M₃ M₄ X₁ X₂ : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] [AddCommGroup M₄] [Module ℂ M₄]
  [AddCommGroup X₁] [Module ℂ X₁] [AddCommGroup X₂] [Module ℂ X₂]
  {W : VertexOperatorAlgebra V}
variable {A₁ : WeakModule W M₁} {A₂ : WeakModule W M₂} {A₃ : WeakModule W M₃}
  {A₄ : WeakModule W M₄} {B₁ : WeakModule W X₁} {B₂ : WeakModule W X₂}

/-- Actual module maps commute with every translation power. -/
theorem hom_Lm1_pow (f : A₃.Hom A₄) (j : ℕ) (x : M₃) :
    f.toLinearMap ((Lm1 A₃ ^ j) x) = (Lm1 A₄ ^ j) (f.toLinearMap x) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [pow_succ',Module.End.mul_apply,pow_succ',Module.End.mul_apply]
    have hf : ∀ z, f.toLinearMap (Lm1 A₃ z) = Lm1 A₄ (f.toLinearMap z) :=
      f.map_act W.conformalVector 0
    rw [hf,ih]

/-- The finite FHL translation sum is natural in the genuine output module. -/
theorem skewK_postcompose (Y : LogIntertwiningOperator A₁ A₂ A₃) (f : A₃.Hom A₄)
    (c : ℂ → ℂ) : skewK A₄ c (postcompose f Y).1 = postModes f.toLinearMap (skewK A₃ c Y.1) := by
  funext n k
  ext y x
  obtain ⟨K,hK⟩ := (Y.2.trunc_comp k).bound x y n
  have hK' : ∀ j : ℕ, K ≤ j → (postcompose f Y).1 (n+j) k x y = 0 := by
    intro j hj
    rw [postcompose_apply]
    change f.toLinearMap (comp Y.1 k (n+j) x y) = 0
    rw [hK j hj,map_zero]
  rw [(postcompose f Y).2.skewK_eq_sum c n k y x K hK',postModes_apply,
    Y.2.skewK_eq_sum c n k y x K hK,map_smul,map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [postcompose_apply,map_smul,hom_Lm1_pow]

/-- The finite FHL translation sum exchanges the two actual input maps. -/
theorem skewK_precompose (Y : LogIntertwiningOperator A₁ A₂ A₃)
    (f : B₁.Hom A₁) (g : B₂.Hom A₂) (c : ℂ → ℂ) :
    skewK A₃ c (precompose f g Y).1 = preModes g.toLinearMap f.toLinearMap (skewK A₃ c Y.1) := by
  funext n k
  ext y x
  obtain ⟨K,hK⟩ := (Y.2.trunc_comp k).bound (f.toLinearMap x) (g.toLinearMap y) n
  rw [(precompose f g Y).2.skewK_eq_sum c n k y x K hK,preModes_apply,
    Y.2.skewK_eq_sum c n k (g.toLinearMap y) (f.toLinearMap x) K hK]
  rfl

/-- Finite logarithmic shifts commute with an actual output linear map. -/
theorem logShift_postModes {Y : LogModes M₁ M₂ M₃} (hY : LogFin Y)
    (f : M₃ →ₗ[ℂ] M₄) (a : ℂ) :
    logShift a (postModes f Y) = postModes f (logShift a Y) := by
  have hF : LogFin (postModes f Y) := by
    intro x y n
    obtain ⟨K,hK⟩ := hY x y n
    exact ⟨K,fun k hk => by rw [postModes_apply,hK k hk,map_zero]⟩
  funext n k
  ext x y
  obtain ⟨K,hK⟩ := hY x y n
  have hK' : ∀ j : ℕ, K ≤ j → postModes f Y n j x y = 0 :=
    fun j hj => by rw [postModes_apply,hK j hj,map_zero]
  rw [logShift_eq_sum hF K hK',postModes_apply,logShift_eq_sum hY K hK,map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [postModes_apply,map_smul]

/-- Finite logarithmic shifts commute with both actual source linear maps. -/
theorem logShift_preModes {Y : LogModes M₁ M₂ M₃} (hY : LogFin Y)
    (f : X₁ →ₗ[ℂ] M₁) (g : X₂ →ₗ[ℂ] M₂) (a : ℂ) :
    logShift a (preModes f g Y) = preModes f g (logShift a Y) := by
  have hF : LogFin (preModes f g Y) := fun x y n => hY (f x) (g y) n
  funext n k
  ext x y
  obtain ⟨K,hK⟩ := hY (f x) (g y) n
  rw [logShift_eq_sum hF K hK,preModes_apply,logShift_eq_sum hY K hK]
  rfl

/-- Genuine Ω is natural in the actual output module. -/
theorem omega_postcompose (Y : LogIntertwiningOperator A₁ A₂ A₃) (f : A₃.Hom A₄) (r : ℤ) :
    omegaEquiv A₁ A₂ A₄ r (postcompose f Y) =
      postcompose f (omegaEquiv A₁ A₂ A₃ r Y) := by
  apply Subtype.ext
  change omega A₄ r (postcompose f Y).1 = postModes f.toLinearMap (omega A₃ r Y.1)
  unfold omega
  rw [skewK_postcompose]
  exact logShift_postModes
    (Y.2.isLogIntertwining_skewK (omegaPhase_succ r) (omegaPhase_ne_zero r)).logFin _ _

/-- Genuine Ω exchanges both actual source maps. -/
theorem omega_precompose (Y : LogIntertwiningOperator A₁ A₂ A₃)
    (f : B₁.Hom A₁) (g : B₂.Hom A₂) (r : ℤ) :
    omegaEquiv B₁ B₂ A₃ r (precompose f g Y) =
      precompose g f (omegaEquiv A₁ A₂ A₃ r Y) := by
  apply Subtype.ext
  change omega A₃ r (precompose f g Y).1 =
    preModes g.toLinearMap f.toLinearMap (omega A₃ r Y.1)
  unfold omega
  rw [skewK_precompose]
  exact logShift_preModes
    (Y.2.isLogIntertwining_skewK (omegaPhase_succ r) (omegaPhase_ne_zero r)).logFin _ _ _

end VOA.LogTensor
