/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.LeeYangCosetTransferHodge
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Tensor products of positive sesquilinear forms

First layer of the concrete Beem–Garner instantiation (weak graded unitarity of the product
`A ⊗ B ⊗ U ⊗ ghosts`, Beem–Garner arXiv 2509.10364, the tensor-positivity step of the good-action and harmonic-bound argument).

* `SesqForm.tensor P Q` — the product sesquilinear form on `V ⊗[ℂ] W`, characterised by
  `tensor_tmul : (P.tensor Q) (v ⊗ w) (v' ⊗ w') = P v v' * Q w w'`.
* `SesqForm.herm_of_isPosOn` — a sesquilinear form positive on all of `V` is Hermitian
  (polarization).
* `SesqForm.isPosOn_tensor` (**tensor positivity**): if `P` and `Q` are positive definite on the
  whole spaces, so is `P.tensor Q`. No finite-dimensionality is assumed on either factor: a
  tensor is a finite sum, so it lives in `S ⊗ W` for a finite-dimensional `S ≤ V`, where the
  restriction of `P` has an orthonormal basis.
* `SesqForm.restrict`, `isPosOn_restrict`, `SesqForm.ofLinearEquiv` — transport along
  submodules and linear equivalences (to restrict a product form to a relative subcomplex).

Everything is proved outright. Nothing here identifies the factor forms with the modified forms
of the concrete VOAs; that is done in `ConcreteHodgeLayers` and `ConcreteHodgeProduct`.
-/

namespace VOA.ConcreteHodge

noncomputable section

open scoped TensorProduct
open Module (finrank)

universe u v

section Herm

variable {V : Type u} [AddCommGroup V] [Module ℂ V]

theorem _root_.VOA.SesqForm.self_re_im (P : SesqForm V) (hP : IsPosOn P ⊤) (x : V) :
    0 ≤ (P x x).re ∧ (P x x).im = 0 := by
  by_cases hx : x = 0
  · subst hx; simp [P.zero_left]
  · obtain ⟨r, hr, hrx⟩ := hP x Submodule.mem_top hx
    rw [hrx]; simp [le_of_lt hr]

/-- **Hermitian symmetry from positivity** (polarization). -/
theorem _root_.VOA.SesqForm.herm_of_isPosOn (P : SesqForm V) (hP : IsPosOn P ⊤) (x y : V) :
    (starRingEnd ℂ) (P y x) = P x y := by
  have h1 := (P.self_re_im hP (x + y)).2
  have h2 := (P.self_re_im hP (x + Complex.I • y)).2
  have hx := (P.self_re_im hP x).2
  have hy := (P.self_re_im hP y).2
  simp only [P.add_left, P.add_right, P.smul_left, P.smul_right, Complex.add_im,
    Complex.mul_im, Complex.conj_I, Complex.neg_re, Complex.neg_im, Complex.I_re,
    Complex.I_im, Complex.mul_re] at h1 h2
  apply Complex.ext <;> simp only [Complex.conj_re, Complex.conj_im] <;> nlinarith

/-- Restriction of a sesquilinear form to a submodule. -/
def _root_.VOA.SesqForm.restrict (P : SesqForm V) (S : Submodule ℂ V) : SesqForm S where
  toFun a b := P a b
  add_left _ _ _ := P.add_left _ _ _
  smul_left z _ _ := P.smul_left z _ _
  add_right _ _ _ := P.add_right _ _ _
  smul_right z _ _ := P.smul_right z _ _

@[simp] theorem _root_.VOA.SesqForm.restrict_apply (P : SesqForm V) (S : Submodule ℂ V)
    (a b : S) : P.restrict S a b = P a b := rfl

theorem _root_.VOA.SesqForm.isPosOn_restrict (P : SesqForm V) (hP : IsPosOn P ⊤)
    (S : Submodule ℂ V) : IsPosOn (P.restrict S) ⊤ := by
  intro x _ hx
  have hx' : (x : V) ≠ 0 := fun h => hx (Subtype.ext h)
  exact hP x Submodule.mem_top hx'

variable {V' : Type v} [AddCommGroup V'] [Module ℂ V']

/-- Pull back a sesquilinear form along a linear map. -/
def _root_.VOA.SesqForm.comap (P : SesqForm V) (f : V' →ₗ[ℂ] V) : SesqForm V' where
  toFun a b := P (f a) (f b)
  add_left a a' b := by rw [map_add, P.add_left]
  smul_left z a b := by rw [map_smul, P.smul_left]
  add_right a b b' := by rw [map_add, P.add_right]
  smul_right z a b := by rw [map_smul, P.smul_right]

@[simp] theorem _root_.VOA.SesqForm.comap_apply (P : SesqForm V) (f : V' →ₗ[ℂ] V) (a b : V') :
    P.comap f a b = P (f a) (f b) := rfl

/-- Positivity pulls back along injective maps. -/
theorem _root_.VOA.SesqForm.isPosOn_comap (P : SesqForm V) (hP : IsPosOn P ⊤) (f : V' →ₗ[ℂ] V)
    (hf : Function.Injective f) : IsPosOn (P.comap f) ⊤ := by
  intro x _ hx
  have : f x ≠ 0 := fun h => hx (hf (h.trans (map_zero f).symm))
  exact hP (f x) Submodule.mem_top this

end Herm

section Tensor

variable {V : Type u} [AddCommGroup V] [Module ℂ V]
variable {W : Type v} [AddCommGroup W] [Module ℂ W]

/-- For fixed `v, w`, the linear functional `v' ⊗ w' ↦ P v v' * Q w w'`. -/
def tensorFunctional (P : SesqForm V) (Q : SesqForm W) (v : V) (w : W) :
    V ⊗[ℂ] W →ₗ[ℂ] ℂ :=
  TensorProduct.lift (LinearMap.mk₂ ℂ (fun v' w' => P v v' * Q w w')
    (fun a a' b => by simp only [P.add_right]; ring)
    (fun c a b => by simp only [P.smul_right, smul_eq_mul]; ring)
    (fun a b b' => by simp only [Q.add_right]; ring)
    (fun c a b => by simp only [Q.smul_right, smul_eq_mul]; ring))

@[simp] theorem tensorFunctional_tmul (P : SesqForm V) (Q : SesqForm W) (v : V) (w : W)
    (v' : V) (w' : W) : tensorFunctional P Q v w (v' ⊗ₜ w') = P v v' * Q w w' := rfl

theorem tensorFunctional_smul_left (P : SesqForm V) (Q : SesqForm W) (r : ℂ) (v : V) (w : W) :
    tensorFunctional P Q (r • v) w = (starRingEnd ℂ) r • tensorFunctional P Q v w := by
  apply TensorProduct.ext'
  intro v' w'
  simp [P.smul_left, mul_assoc]

theorem tensorFunctional_smul_right (P : SesqForm V) (Q : SesqForm W) (r : ℂ) (v : V) (w : W) :
    tensorFunctional P Q v (r • w) = (starRingEnd ℂ) r • tensorFunctional P Q v w := by
  apply TensorProduct.ext'
  intro v' w'
  simp [Q.smul_left]; ring

/-- The bi-additive map `(v, w) ↦ tensorFunctional P Q v w`. -/
def tensorFunctionalHom (P : SesqForm V) (Q : SesqForm W) :
    V →+ W →+ (V ⊗[ℂ] W →ₗ[ℂ] ℂ) :=
  AddMonoidHom.mk' (fun v => AddMonoidHom.mk' (fun w => tensorFunctional P Q v w)
    (fun w w' => by
      apply TensorProduct.ext'; intro a b; simp [Q.add_left]; ring))
    (fun v v' => by
      ext w : 1
      apply TensorProduct.ext'; intro a b; simp [P.add_left]; ring)

/-- The additive map `x ↦ (P ⊗ Q)(x, -)`. -/
def tensorLeft (P : SesqForm V) (Q : SesqForm W) : V ⊗[ℂ] W →+ (V ⊗[ℂ] W →ₗ[ℂ] ℂ) :=
  TensorProduct.liftAddHom (tensorFunctionalHom P Q) (fun r v w => by
    change tensorFunctional P Q (r • v) w = tensorFunctional P Q v (r • w)
    rw [tensorFunctional_smul_left, tensorFunctional_smul_right])

@[simp] theorem tensorLeft_tmul (P : SesqForm V) (Q : SesqForm W) (v : V) (w : W) :
    tensorLeft P Q (v ⊗ₜ w) = tensorFunctional P Q v w := rfl

theorem tensorLeft_smul (P : SesqForm V) (Q : SesqForm W) (r : ℂ) (x : V ⊗[ℂ] W) :
    tensorLeft P Q (r • x) = (starRingEnd ℂ) r • tensorLeft P Q x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v w =>
      rw [TensorProduct.smul_tmul', tensorLeft_tmul, tensorLeft_tmul,
        tensorFunctional_smul_left]
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

/-- **The product sesquilinear form** on `V ⊗[ℂ] W`. -/
def _root_.VOA.SesqForm.tensor (P : SesqForm V) (Q : SesqForm W) : SesqForm (V ⊗[ℂ] W) where
  toFun x y := tensorLeft P Q x y
  add_left x x' y := by rw [map_add, LinearMap.add_apply]
  smul_left z x y := by rw [tensorLeft_smul, LinearMap.smul_apply, smul_eq_mul]
  add_right x y y' := map_add _ _ _
  smul_right z x y := by rw [map_smul, smul_eq_mul]

@[simp] theorem _root_.VOA.SesqForm.tensor_tmul (P : SesqForm V) (Q : SesqForm W) (v v' : V)
    (w w' : W) : P.tensor Q (v ⊗ₜ w) (v' ⊗ₜ w') = P v v' * Q w w' := rfl

theorem _root_.VOA.SesqForm.tensor_sum_sum {ι : Type*} (s : Finset ι) (P : SesqForm V)
    (Q : SesqForm W) (v : ι → V) (w : ι → W) :
    P.tensor Q (∑ i ∈ s, v i ⊗ₜ w i) (∑ j ∈ s, v j ⊗ₜ w j) =
      ∑ i ∈ s, ∑ j ∈ s, P (v i) (v j) * Q (w i) (w j) := by
  change tensorLeft P Q (∑ i ∈ s, v i ⊗ₜ w i) (∑ j ∈ s, v j ⊗ₜ w j) = _
  rw [map_sum (tensorLeft P Q), LinearMap.coe_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [tensorLeft_tmul, map_sum]
  rfl

/-- A positive sesquilinear form on a finite-dimensional space has an orthonormal basis. -/
theorem exists_orthonormal_basis {S : Type*} [AddCommGroup S] [Module ℂ S]
    [FiniteDimensional ℂ S] (P : SesqForm S) (hP : IsPosOn P ⊤) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℂ S), ∀ i j, P (b i) (b j) = if i = j then 1 else 0 := by
  letI core : InnerProductSpace.Core ℂ S :=
    { inner := P
      conj_inner_symm := P.herm_of_isPosOn hP
      re_inner_nonneg := fun x => (P.self_re_im hP x).1
      add_left := P.add_left
      smul_left := fun x y c => P.smul_left c x y
      definite := fun x hx => LeeYangCosetTransfer.eq_zero_of_sesq_self_eq_zero P hP hx }
  letI : NormedAddCommGroup S := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  letI : InnerProductSpace ℂ S := InnerProductSpace.ofCore core.toCore
  let b := stdOrthonormalBasis ℂ S
  refine ⟨_, b.toBasis, fun i j => ?_⟩
  rw [OrthonormalBasis.coe_toBasis]
  exact orthonormal_iff_ite.mp b.orthonormal i j

/-- **Tensor positivity.** The product of two positive definite sesquilinear forms is positive
definite on the whole tensor product. -/
theorem _root_.VOA.SesqForm.isPosOn_tensor (P : SesqForm V) (Q : SesqForm W) (hP : IsPosOn P ⊤)
    (hQ : IsPosOn Q ⊤) : IsPosOn (P.tensor Q) ⊤ := by
  intro x _ hx
  obtain ⟨S, hSfin, hxS⟩ :=
    TensorProduct.exists_finite_submodule_left_of_setFinite ({x} : Set (V ⊗[ℂ] W))
      (Set.finite_singleton x)
  obtain ⟨x', hx'⟩ := hxS (Set.mem_singleton x)
  obtain ⟨n, b, hb⟩ := exists_orthonormal_basis (P.restrict S) (P.isPosOn_restrict hP S)
  classical
  set u := TensorProduct.equivFinsuppOfBasisLeft b x' with hu
  have hx'u : x' = ∑ i, b i ⊗ₜ[ℂ] u i := by
    rw [← (TensorProduct.equivFinsuppOfBasisLeft b).symm_apply_apply x', ← hu,
      TensorProduct.equivFinsuppOfBasisLeft_symm_apply, Finsupp.sum_fintype _ _ (by simp)]
  have hxu : x = ∑ i, (b i : V) ⊗ₜ[ℂ] u i := by
    rw [← hx', hx'u, map_sum]
    rfl
  have hval : P.tensor Q x x = ∑ i, Q (u i) (u i) := by
    rw [hxu, SesqForm.tensor_sum_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i]
    · have := hb i i
      rw [if_pos rfl] at this
      change P (b i : V) (b i) = 1 at this
      rw [this, one_mul]
    · intro j _ hji
      have := hb i j
      rw [if_neg (Ne.symm hji)] at this
      change P (b i : V) (b j) = 0 at this
      rw [this, zero_mul]
    · simp
  -- some coefficient is nonzero
  have hne : ∃ i, u i ≠ 0 := by
    by_contra h
    push Not at h
    apply hx
    rw [hxu]
    simp [h]
  obtain ⟨i0, hi0⟩ := hne
  have hterm : ∀ i, ∃ r : ℝ, 0 ≤ r ∧ Q (u i) (u i) = r := by
    intro i
    by_cases hi : u i = 0
    · exact ⟨0, le_refl _, by rw [hi, Q.zero_left]; simp⟩
    · obtain ⟨r, hr, hrx⟩ := hQ (u i) Submodule.mem_top hi
      exact ⟨r, le_of_lt hr, hrx⟩
  choose r hr0 hr using hterm
  obtain ⟨r0, hr0pos, hr0eq⟩ := hQ (u i0) Submodule.mem_top hi0
  have hri0 : r i0 = r0 := by
    have := (hr i0).symm.trans hr0eq
    exact_mod_cast this
  refine ⟨∑ i, r i, ?_, ?_⟩
  · calc (0 : ℝ) < r i0 := hri0 ▸ hr0pos
      _ ≤ ∑ i, r i := Finset.single_le_sum (fun i _ => hr0 i) (Finset.mem_univ i0)
  · rw [hval, Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun i _ => hr i

/-- Tensor positivity, in the form used for the relative subcomplex: the product form
restricted to any submodule of `V ⊗ W` is positive definite. -/
theorem _root_.VOA.SesqForm.isPosOn_tensor_restrict (P : SesqForm V) (Q : SesqForm W)
    (hP : IsPosOn P ⊤) (hQ : IsPosOn Q ⊤) (K : Submodule ℂ (V ⊗[ℂ] W)) :
    IsPosOn ((P.tensor Q).restrict K) ⊤ :=
  (P.tensor Q).isPosOn_restrict (P.isPosOn_tensor Q hP hQ) K

end Tensor

end

end VOA.ConcreteHodge
