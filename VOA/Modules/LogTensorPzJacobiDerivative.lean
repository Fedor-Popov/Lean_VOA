/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modules.LogTensorPzL0
import VOA.Modules.LogTensorPzLogLift

/-! # Genuine Jacobi and actual weights give the coupled logarithmic derivative

The conformal commutator identifies L(-1) insertion with the actual full L(0)
defect. On correct generalized weights that is precisely the Jordan defect.
Thus the genuine logarithmic reconstruction requires no extra derivative input.
-/
namespace VOA.LogTensor.Pz
open scoped BigOperators
universe u
variable {V M₁ M₂ M₃ : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] {W : VertexOperatorAlgebra V}
variable {A₁ : WeakModule W M₁} {A₂ : WeakModule W M₂} {A₃ : WeakModule W M₃}
  {F : ModeFamily (M₁ := M₁) (M₂ := M₂) (M₃ := M₃)}

/-- The genuine coefficient-family commutator, from Jacobi at ell=0. -/
theorem IsJacobiFamily.commutator (hF : IsJacobiFamily A₁ A₂ A₃ F)
    (u : V) (x : M₁) (y : M₂) (p : ℤ) (n : ℂ) :
    mode (A₃.YM u) p (F n x y) - F n x (mode (A₂.YM u) p y) =
      ∑ᶠ i : ℤ, cbz p i • F (p+n-i) (mode (A₁.YM u) i x) y := by
  have h := hF.jacobi u x y 0 p n
  rw [finsum_eq_single _ (0:ℤ)] at h
  · simpa [cbz_zero_left,negOnePow] using h
  · intro i hi
    simp [cbz_zero_left,hi]

/-- The actual conformal L(0) commutator for a genuine Jacobi family. -/
theorem IsJacobiFamily.L0_commutator (hF : IsJacobiFamily A₁ A₂ A₃ F)
    (x : M₁) (y : M₂) (n : ℂ) :
    L0 A₃ (F n x y) - F n x (L0 A₂ y) = F (n+1) (Lm1 A₁ x) y + F n (L0 A₁ x) y := by
  have h := hF.commutator W.conformalVector x y 1 n
  rw [finsum_eq_sum_of_support_subset _ (s := ({0,1}:Finset ℤ)) (by
    intro i hi
    simp only [Function.mem_support] at hi
    simp only [Finset.coe_insert,Finset.coe_singleton,Set.mem_insert_iff,Set.mem_singleton_iff]
    by_contra hc
    exact hi (by rw [IsLogIntertwining.cbz_one_eq,if_neg hc,zero_smul])),
    Finset.sum_insert (by norm_num),Finset.sum_singleton,
    IsLogIntertwining.cbz_one_eq,IsLogIntertwining.cbz_one_eq,
    if_pos (Or.inl rfl),if_pos (Or.inr rfl),one_smul,one_smul] at h
  rw [h,show ((1:ℤ):ℂ)+n-((0:ℤ):ℂ) = n+1 by push_cast; ring,
    show ((1:ℤ):ℂ)+n-((1:ℤ):ℂ) = n by push_cast; ring]

/-- Genuine Jacobi and actual generalized mode weights force the coupled zeroth
logarithmic derivative, including the full nilpotent defect. -/
theorem baseDerivative_of_jacobi_weight (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂)
    (N₃ : LogVModule W M₃) (hF : IsJacobiFamily N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule F)
    (hweight : ∀ n, HasModeWeight N₁ N₂ N₃ n (F n)) : BaseDerivative N₁ N₂ N₃ F := by
  intro n
  rw [nilDefect_eq_modeDefect N₁ N₂ N₃ (hweight (n-1))]
  ext x y
  change F n (Lm1 N₁.toWeakModule x) y = (-n) • F (n-1) x y +
    (L0 N₃.toWeakModule (F (n-1) x y) - F (n-1) (L0 N₁.toWeakModule x) y -
      F (n-1) x (L0 N₂.toWeakModule y) + ((n-1)+1) • F (n-1) x y)
  have h := hF.L0_commutator x y (n-1)
  rw [sub_add_cancel] at h ⊢
  linear_combination (norm := module) -h

/-- A genuine weighted truncated Jacobi family reconstructs a genuine logarithmic
intertwiner, with all four axioms discharged. -/
theorem isLogIntertwining_logLift_of_jacobi_weight
    (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
    (hF : IsJacobiFamily N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule F)
    (hweight : ∀ n, HasModeWeight N₁ N₂ N₃ n (F n)) :
    IsLogIntertwining N₁.toWeakModule N₂.toWeakModule N₃.toWeakModule (logLift N₁ N₂ N₃ F) :=
  isLogIntertwining_logLift N₁ N₂ N₃ hF hweight
    (baseDerivative_of_jacobi_weight N₁ N₂ N₃ hF hweight)

end VOA.LogTensor.Pz
