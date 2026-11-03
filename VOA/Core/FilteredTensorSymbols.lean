/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Core.PolynomialMinimumSymbol
import Mathlib.LinearAlgebra.TensorProduct.Map

/-!
# Tensor products of actual creation-length filtrations

The tensor filtration adds the lengths of the two factors. Multiplying
their polynomial coordinates is a linear map on the tensor product.
One-step operator errors are transported through this map using only the
proved factor bounds; no injectivity or representation hypothesis is hidden.
-/
namespace VOA
noncomputable section
open scoped TensorProduct
open MvPolynomial
open Module (End)
variable {V W σ : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- Total creation length on an algebraic tensor product, defined by finite spans. -/
def tensorLength (F : ℕ → Submodule ℂ V) (G : ℕ → Submodule ℂ W) (d : ℕ) :
    Submodule ℂ (V ⊗[ℂ] W) := Submodule.span ℂ
  {z | ∃ i j v w,i+j≤d ∧ v∈F i ∧ w∈G j ∧ z=v⊗ₜ[ℂ]w}

/-- A pure tensor belongs when its two factor lengths fit the total bound. -/
theorem tmul_mem_tensorLength (F : ℕ → Submodule ℂ V) (G : ℕ → Submodule ℂ W)
    {i j d : ℕ} {v : V} {w : W} (hd : i+j≤d) (hv : v∈F i) (hw : w∈G j) :
    v⊗ₜ[ℂ]w∈tensorLength F G d := Submodule.subset_span ⟨i,j,v,w,hd,hv,hw,rfl⟩

/-- The total-length subspaces increase with the permitted bound. -/
theorem tensorLength_mono (F : ℕ → Submodule ℂ V) (G : ℕ → Submodule ℂ W)
    {d e : ℕ} (h : d≤e) : tensorLength F G d≤tensorLength F G e := by
  apply Submodule.span_mono
  rintro z ⟨i,j,v,w,hij,hv,hw,rfl⟩
  exact ⟨i,j,v,w,hij.trans h,hv,hw,rfl⟩

/-- Raising the first factor's length by one raises total length by at most one. -/
theorem rTensor_length (F : ℕ → Submodule ℂ V) (G : ℕ → Submodule ℂ W)
    (T : End ℂ V) (hT : ∀ d v,v∈F d → T v∈F (d+1))
    (d : ℕ) {z : V⊗[ℂ]W} (hz : z∈tensorLength F G d) :
    T.rTensor W z∈tensorLength F G (d+1) := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨i,j,v,w,hij,hv,hw,rfl⟩ := hz
      rw [LinearMap.rTensor_tmul]
      exact tmul_mem_tensorLength F G (by omega) (hT i v hv) hw
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add v w hv hw ihv ihw => rw [map_add]; exact Submodule.add_mem _ ihv ihw
  | smul c v hv ih => rw [map_smul]; exact Submodule.smul_mem _ c ih

/-- The corresponding total-length bound for an operator on the second factor. -/
theorem lTensor_length (F : ℕ → Submodule ℂ V) (G : ℕ → Submodule ℂ W)
    (T : End ℂ W) (hT : ∀ d v,v∈G d → T v∈G (d+1))
    (d : ℕ) {z : V⊗[ℂ]W} (hz : z∈tensorLength F G d) :
    T.lTensor V z∈tensorLength F G (d+1) := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨i,j,v,w,hij,hv,hw,rfl⟩ := hz
      rw [LinearMap.lTensor_tmul]
      exact tmul_mem_tensorLength F G (by omega) hv (hT j w hw)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add v w hv hw ihv ihw => rw [map_add]; exact Submodule.add_mem _ ihv ihw
  | smul c v hv ih => rw [map_smul]; exact Submodule.smul_mem _ c ih

/-- Multiplication of two polynomial coordinate maps descends to a linear tensor map. -/
def tensorPolynomialProduct (φ : V →ₗ[ℂ] MvPolynomial σ ℂ)
    (ψ : W →ₗ[ℂ] MvPolynomial σ ℂ) : V⊗[ℂ]W →ₗ[ℂ] MvPolynomial σ ℂ :=
  TensorProduct.lift
    { toFun := fun v =>
        { toFun := fun w => φ v*ψ w
          map_add' := by intros; simp [mul_add]
          map_smul' := by intros; simp [mul_smul_comm] }
      map_add' := by intros; ext; simp [add_mul]
      map_smul' := by intros; ext; simp [smul_mul_assoc] }

/-- Pure tensors are sent to the product of their actual factor coordinates. -/
theorem tensorPolynomialProduct_tmul (φ : V →ₗ[ℂ] MvPolynomial σ ℂ)
    (ψ : W →ₗ[ℂ] MvPolynomial σ ℂ) (v : V) (w : W) :
    tensorPolynomialProduct φ ψ (v⊗ₜ[ℂ]w)=φ v*ψ w := rfl

/-- Bounds for factor coordinates give a bound for all finite tensor combinations. -/
theorem tensorPolynomialProduct_length (F : ℕ → Submodule ℂ V) (G : ℕ → Submodule ℂ W)
    (φ : V →ₗ[ℂ] MvPolynomial σ ℂ) (ψ : W →ₗ[ℂ] MvPolynomial σ ℂ)
    (hφ : ∀ d v,v∈F d → φ v∈PolynomialMinimum.AtLeast (fun _ => (-1 : ℤ)) (-(d : ℤ)))
    (hψ : ∀ d w,w∈G d → ψ w∈PolynomialMinimum.AtLeast (fun _ => (-1 : ℤ)) (-(d : ℤ)))
    (d : ℕ) {z : V⊗[ℂ]W} (hz : z∈tensorLength F G d) :
    tensorPolynomialProduct φ ψ z∈PolynomialMinimum.AtLeast (fun _ => (-1 : ℤ)) (-(d : ℤ)) := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨i,j,v,w,hij,hv,hw,rfl⟩ := hz
      exact PolynomialMinimum.mono (by omega) (PolynomialMinimum.mul_mem (hφ i v hv) (hψ j w hw))
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add v w hv hw ihv ihw => rw [map_add]; exact Submodule.add_mem _ ihv ihw
  | smul c v hv ih => rw [map_smul]; exact Submodule.smul_mem _ c ih

/-- A first-factor operator's length-preserving error stays length-preserving
in the full tensor action after multiplication by the second coordinate. -/
theorem rTensor_polynomial_error (F : ℕ → Submodule ℂ V) (G : ℕ → Submodule ℂ W)
    (φ : V →ₗ[ℂ] MvPolynomial σ ℂ) (ψ : W →ₗ[ℂ] MvPolynomial σ ℂ)
    (T : End ℂ V) (f : MvPolynomial σ ℂ)
    (hT : ∀ d v,v∈F d → φ (T v)-f*φ v∈PolynomialMinimum.AtLeast (fun _ => (-1 : ℤ)) (-(d : ℤ)))
    (hψ : ∀ d w,w∈G d → ψ w∈PolynomialMinimum.AtLeast (fun _ => (-1 : ℤ)) (-(d : ℤ)))
    (d : ℕ) {z : V⊗[ℂ]W} (hz : z∈tensorLength F G d) :
    tensorPolynomialProduct φ ψ (T.rTensor W z)-f*tensorPolynomialProduct φ ψ z ∈
      PolynomialMinimum.AtLeast (fun _ => (-1 : ℤ)) (-(d : ℤ)) := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨i,j,v,w,hij,hv,hw,rfl⟩ := hz
      rw [LinearMap.rTensor_tmul,tensorPolynomialProduct_tmul,tensorPolynomialProduct_tmul]
      rw [← mul_assoc,← sub_mul]
      exact PolynomialMinimum.mono (by omega) (PolynomialMinimum.mul_mem (hT i v hv) (hψ j w hw))
  | zero => simp only [map_zero,mul_zero,sub_zero]; exact Submodule.zero_mem _
  | add v w hv hw ihv ihw =>
      simp only [map_add,mul_add]
      convert (PolynomialMinimum.AtLeast (fun _ : σ => (-1 : ℤ)) (-(d : ℤ))).add_mem ihv ihw using 1 <;> abel
  | smul c v hv ih =>
      simpa only [map_smul,mul_smul_comm,← smul_sub] using
        (PolynomialMinimum.AtLeast (fun _ : σ => (-1 : ℤ)) (-(d : ℤ))).smul_mem c ih

/-- The symmetric transport of a second-factor operator error. -/
theorem lTensor_polynomial_error (F : ℕ → Submodule ℂ V) (G : ℕ → Submodule ℂ W)
    (φ : V →ₗ[ℂ] MvPolynomial σ ℂ) (ψ : W →ₗ[ℂ] MvPolynomial σ ℂ)
    (T : End ℂ W) (f : MvPolynomial σ ℂ)
    (hφ : ∀ d v,v∈F d → φ v∈PolynomialMinimum.AtLeast (fun _ => (-1 : ℤ)) (-(d : ℤ)))
    (hT : ∀ d w,w∈G d → ψ (T w)-f*ψ w∈PolynomialMinimum.AtLeast (fun _ => (-1 : ℤ)) (-(d : ℤ)))
    (d : ℕ) {z : V⊗[ℂ]W} (hz : z∈tensorLength F G d) :
    tensorPolynomialProduct φ ψ (T.lTensor V z)-f*tensorPolynomialProduct φ ψ z ∈
      PolynomialMinimum.AtLeast (fun _ => (-1 : ℤ)) (-(d : ℤ)) := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨i,j,v,w,hij,hv,hw,rfl⟩ := hz
      rw [LinearMap.lTensor_tmul,tensorPolynomialProduct_tmul,tensorPolynomialProduct_tmul]
      have he : φ v*ψ (T w)-f*(φ v*ψ w)=φ v*(ψ (T w)-f*ψ w) := by ring
      rw [he]
      exact PolynomialMinimum.mono (by omega) (PolynomialMinimum.mul_mem (hφ i v hv) (hT j w hw))
  | zero => simp only [map_zero,mul_zero,sub_zero]; exact Submodule.zero_mem _
  | add v w hv hw ihv ihw =>
      simp only [map_add,mul_add]
      convert (PolynomialMinimum.AtLeast (fun _ : σ => (-1 : ℤ)) (-(d : ℤ))).add_mem ihv ihw using 1 <;> abel
  | smul c v hv ih =>
      simpa only [map_smul,mul_smul_comm,← smul_sub] using
        (PolynomialMinimum.AtLeast (fun _ : σ => (-1 : ℤ)) (-(d : ℤ))).smul_mem c ih

/-- Renaming variables preserves the constant-minus-one weight, even when
variables are identified, since their multiplicities add. -/
theorem minusLength_weight_mapDomain {τ : Type*} (f : σ → τ) (e : σ →₀ ℕ) :
    Finsupp.weight (fun _ : τ => (-1 : ℤ)) (e.mapDomain f)=
      Finsupp.weight (fun _ : σ => (-1 : ℤ)) e := by
  simp only [Finsupp.weight_apply]
  exact Finsupp.sum_mapDomain_index (by simp) (by intros; simp [add_comm])

/-- Variable relabelling preserves every constant-minus-one weight bound. -/
theorem rename_minusLength {τ : Type*} (f : σ → τ) (d : ℤ)
    {P : MvPolynomial σ ℂ} (hP : P∈PolynomialMinimum.AtLeast (fun _ => (-1 : ℤ)) d) :
    rename f P∈PolynomialMinimum.AtLeast (fun _ => (-1 : ℤ)) d := by
  induction hP using Submodule.span_induction with
  | mem P hP =>
      obtain ⟨e,he,rfl⟩ := hP
      rw [rename_monomial]
      exact PolynomialMinimum.monomial_mem _ (by rwa [minusLength_weight_mapDomain])
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add P Q hP hQ ihP ihQ => rw [map_add]; exact Submodule.add_mem _ ihP ihQ
  | smul c P hP ih => rw [map_smul]; exact Submodule.smul_mem _ c ih


/-- The sum of the two factor actions raises total length by at most one. -/
theorem tensorSum_length (F : ℕ → Submodule ℂ V) (G : ℕ → Submodule ℂ W)
    (T : End ℂ V) (U : End ℂ W)
    (hT : ∀ d v,v∈F d → T v∈F (d+1))
    (hU : ∀ d w,w∈G d → U w∈G (d+1))
    (d : ℕ) {z : V⊗[ℂ]W} (hz : z∈tensorLength F G d) :
    (T.rTensor W+U.lTensor V) z∈tensorLength F G (d+1) :=
  Submodule.add_mem _ (rTensor_length F G T hT d hz) (lTensor_length F G U hU d hz)

/-- The sum action has the sum of the factor symbols, with a proved
total-length-preserving error on every tensor vector. -/
theorem tensorSum_polynomial_error (F : ℕ → Submodule ℂ V) (G : ℕ → Submodule ℂ W)
    (φ : V →ₗ[ℂ] MvPolynomial σ ℂ) (ψ : W →ₗ[ℂ] MvPolynomial σ ℂ)
    (T : End ℂ V) (U : End ℂ W) (f g : MvPolynomial σ ℂ)
    (hφ : ∀ d v,v∈F d → φ v∈PolynomialMinimum.AtLeast (fun _ => (-1 : ℤ)) (-(d : ℤ)))
    (hψ : ∀ d w,w∈G d → ψ w∈PolynomialMinimum.AtLeast (fun _ => (-1 : ℤ)) (-(d : ℤ)))
    (hT : ∀ d v,v∈F d → φ (T v)-f*φ v∈PolynomialMinimum.AtLeast (fun _ => (-1 : ℤ)) (-(d : ℤ)))
    (hU : ∀ d w,w∈G d → ψ (U w)-g*ψ w∈PolynomialMinimum.AtLeast (fun _ => (-1 : ℤ)) (-(d : ℤ)))
    (d : ℕ) {z : V⊗[ℂ]W} (hz : z∈tensorLength F G d) :
    tensorPolynomialProduct φ ψ ((T.rTensor W+U.lTensor V) z)-
        (f+g)*tensorPolynomialProduct φ ψ z ∈
      PolynomialMinimum.AtLeast (fun _ => (-1 : ℤ)) (-(d : ℤ)) := by
  have ht := rTensor_polynomial_error F G φ ψ T f hT hψ d hz
  have hu := lTensor_polynomial_error F G φ ψ U g hφ hU d hz
  simp only [LinearMap.add_apply,map_add,add_mul]
  convert (PolynomialMinimum.AtLeast (fun _ : σ => (-1 : ℤ)) (-(d : ℤ))).add_mem ht hu using 1 <;> abel


end
end VOA
