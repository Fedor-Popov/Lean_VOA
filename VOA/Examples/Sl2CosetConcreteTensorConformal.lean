/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Examples.Sl2CosetConcreteFactors
import VOA.Examples.Sl2CosetConcreteOmega
import VOA.Examples.Sl2CosetConcreteTranslation

/-! # Conformal modes of the tensor of two ordinary VOAs -/

namespace VOA.Sl2CosetConcrete

open Sl2SemiInfinite
open Module (End)
open scoped TensorProduct

universe u v
variable {M : Type u} {N : Type v}
  [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]

noncomputable section

/-- The ordinary sum of factor conformal vectors. -/
def tensorConformal (V : VertexOperatorAlgebra M) (W : VertexOperatorAlgebra N) :
    M ⊗[ℂ] N := V.conformalVector ⊗ₜ[ℂ] W.vacuum + V.vacuum ⊗ₜ[ℂ] W.conformalVector

theorem tensorConformal_mode_tmul (V : VertexOperatorAlgebra M)
    (W : VertexOperatorAlgebra N) (r : ℤ) (x : M) (y : N) :
    mode (TensorVA.tenY V.toPreVertexAlgebra.toSuper W.toPreVertexAlgebra.toSuper
      (tensorConformal V W)) r (x ⊗ₜ[ℂ] y) =
      mode (V.Y V.conformalVector) r x ⊗ₜ[ℂ] y +
        x ⊗ₜ[ℂ] mode (W.Y W.conformalVector) r y := by
  unfold tensorConformal
  rw [map_add, mode_add, LinearMap.add_apply]
  change TensorVA.tenY _ _ (V.conformalVector ⊗ₜ[ℂ] W.vacuum) (-r - 1) (x ⊗ₜ[ℂ] y) +
    TensorVA.tenY _ _ (V.vacuum ⊗ₜ[ℂ] W.conformalVector) (-r - 1) (x ⊗ₜ[ℂ] y) = _
  exact congrArg₂ (· + ·)
    (tenY_left_unit V.toPreVertexAlgebra.toSuper W.toPreVertexAlgebra.toSuper
      V.conformalVector x y (-r - 1))
    (tenY_right_unit_even V.toPreVertexAlgebra.toSuper W.toPreVertexAlgebra.toSuper
      (DSMor.mem_parity_zero_toSuper W.toPreVertexAlgebra W.conformalVector) x y (-r - 1))

theorem tensorConformal_mode (V : VertexOperatorAlgebra M)
    (W : VertexOperatorAlgebra N) (r : ℤ) :
    mode (TensorVA.tenY V.toPreVertexAlgebra.toSuper W.toPreVertexAlgebra.toSuper
      (tensorConformal V W)) r =
      LinearMap.rTensor N (mode (V.Y V.conformalVector) r) +
        LinearMap.lTensor M (mode (W.Y W.conformalVector) r) := by
  apply TensorProduct.ext'
  intro x y
  exact tensorConformal_mode_tmul V W r x y

/-- The complex-weight reading of an ordinary VOA still diagonalizes `L₀`. -/
theorem voa_L0_complex_grading (V : VertexOperatorAlgebra M) (h : ℂ)
    (x : M) (hx : x ∈ V.toPreVertexAlgebra.toSuper.grading h) :
    mode (V.Y V.conformalVector) 1 x = h • x := by
  by_cases hh : ∃ n : ℤ, (n : ℂ) = h
  · obtain ⟨n, rfl⟩ := hh
    change x ∈ V.toPreVertexAlgebra.gradingC (n : ℂ) at hx
    rw [V.toPreVertexAlgebra.gradingC_intCast] at hx
    exact V.L0_grading x hx
  · change x ∈ V.toPreVertexAlgebra.gradingC h at hx
    rw [V.toPreVertexAlgebra.gradingC_of_not_int hh, Submodule.mem_bot] at hx
    simp [hx]

/-- The ambient tensor conformal zero mode realizes the convolution grading. -/
theorem tensorConformal_L0 (V : VertexOperatorAlgebra M) (W : VertexOperatorAlgebra N)
    (h : ℂ) (x : M ⊗[ℂ] N)
    (hx : x ∈ TensorVA.tenGrading V.toPreVertexAlgebra.toSuper W.toPreVertexAlgebra.toSuper h) :
    mode (TensorVA.tenY V.toPreVertexAlgebra.toSuper W.toPreVertexAlgebra.toSuper
      (tensorConformal V W)) 1 x = h • x := by
  refine TensorVA.tenGrading_induction V.toPreVertexAlgebra.toSuper W.toPreVertexAlgebra.toSuper
    (motive := fun z => mode (TensorVA.tenY V.toPreVertexAlgebra.toSuper W.toPreVertexAlgebra.toSuper
      (tensorConformal V W)) 1 z = h • z) ?_ ?_ ?_ ?_ hx
  · simp
  · intro x y hx hy
    simp only [map_add, hx, hy, smul_add]
  · intro c x hx
    simp only [map_smul, hx, smul_comm c h]
  · intro a x hx y hy
    rw [tensorConformal_mode_tmul, voa_L0_complex_grading V a x hx,
      voa_L0_complex_grading W (h - a) y hy]
    simp only [TensorProduct.smul_tmul', TensorProduct.tmul_smul]
    rw [← TensorProduct.add_tmul, ← add_smul]
    congr 2
    ring

/-- The ambient tensor translation is the sum of the factor translations. -/
theorem tensorConformal_zero_mode (V : VertexOperatorAlgebra M)
    (W : VertexOperatorAlgebra N) :
    mode (TensorVA.tenY V.toPreVertexAlgebra.toSuper W.toPreVertexAlgebra.toSuper
      (tensorConformal V W)) 0 =
      TensorFieldLift.tensorTranslation (V.L (-1)) (W.L (-1)) :=
  tensorConformal_mode V W 0

/-- An even conformal state whose residue is the translation datum gives the
state-translation identity, without an additional assumption on its fields. -/
theorem Y_translation_of_zero_mode {P : Type*} [AddCommGroup P] [Module ℂ P]
    {S : SuperVertexAlgebra P} (H : TranslationCovariant S) {w : P}
    (hw : w ∈ S.parity 0) (hT : mode (S.Y w) 0 = H.T) (x : P) :
    S.Y (H.T x) = deriv (S.Y x) := by
  apply FormalDist.ext
  intro s
  apply LinearMap.ext
  intro y
  have hd := even_zeroMode_deriv (zeroModeCommutator_of_translation H) hw x y (-s - 1)
  rw [hT] at hd
  have hc := congrArg (fun f : End ℂ P => f y) (H.covariant x s)
  simp only [mode_apply, show -(-s - 1) - 1 = s by omega] at hd
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] at hc
  change S.Y (H.T x) s y = (s + 1) • S.Y x (s + 1) y
  rw [← hc, hd]
  abel

/-- Ambient tensor conformal modes satisfy Virasoro with additive central charge. -/
theorem tensorConformal_virasoro (V : VertexOperatorAlgebra M)
    (W : VertexOperatorAlgebra N) (m n : ℤ) :
    ⁅mode (TensorVA.tenY V.toPreVertexAlgebra.toSuper W.toPreVertexAlgebra.toSuper
        (tensorConformal V W)) (m + 1),
      mode (TensorVA.tenY V.toPreVertexAlgebra.toSuper W.toPreVertexAlgebra.toSuper
        (tensorConformal V W)) (n + 1)⁆ =
      ((m : ℂ) - n) • mode (TensorVA.tenY V.toPreVertexAlgebra.toSuper W.toPreVertexAlgebra.toSuper
        (tensorConformal V W)) (m + n + 1) +
      if m + n = 0 then (((m : ℂ) ^ 3 - m) / 12 * (V.centralCharge + W.centralCharge)) •
        (1 : End ℂ (M ⊗[ℂ] N)) else 0 := by
  apply TensorProduct.ext'
  intro x y
  have hV := congrArg (fun f : End ℂ M => f x) (V.virasoro m n)
  have hW := congrArg (fun f : End ℂ N => f y) (W.virasoro m n)
  simp only [LieRing.of_associative_ring_bracket, LinearMap.sub_apply, Module.End.mul_apply,
    LinearMap.add_apply, LinearMap.smul_apply] at hV hW ⊢
  simp only [tensorConformal_mode_tmul, map_add]
  have hsplit :
      (mode (V.Y V.conformalVector) (m + 1)
          (mode (V.Y V.conformalVector) (n + 1) x) ⊗ₜ[ℂ] y +
        mode (V.Y V.conformalVector) (n + 1) x ⊗ₜ[ℂ]
          mode (W.Y W.conformalVector) (m + 1) y +
        (mode (V.Y V.conformalVector) (m + 1) x ⊗ₜ[ℂ]
          mode (W.Y W.conformalVector) (n + 1) y +
          x ⊗ₜ[ℂ] mode (W.Y W.conformalVector) (m + 1)
            (mode (W.Y W.conformalVector) (n + 1) y))) -
      (mode (V.Y V.conformalVector) (n + 1)
          (mode (V.Y V.conformalVector) (m + 1) x) ⊗ₜ[ℂ] y +
        mode (V.Y V.conformalVector) (m + 1) x ⊗ₜ[ℂ]
          mode (W.Y W.conformalVector) (n + 1) y +
        (mode (V.Y V.conformalVector) (n + 1) x ⊗ₜ[ℂ]
          mode (W.Y W.conformalVector) (m + 1) y +
          x ⊗ₜ[ℂ] mode (W.Y W.conformalVector) (n + 1)
            (mode (W.Y W.conformalVector) (m + 1) y))) =
      (mode (V.Y V.conformalVector) (m + 1)
          (mode (V.Y V.conformalVector) (n + 1) x) -
        mode (V.Y V.conformalVector) (n + 1)
          (mode (V.Y V.conformalVector) (m + 1) x)) ⊗ₜ[ℂ] y +
      x ⊗ₜ[ℂ] (mode (W.Y W.conformalVector) (m + 1)
          (mode (W.Y W.conformalVector) (n + 1) y) -
        mode (W.Y W.conformalVector) (n + 1)
          (mode (W.Y W.conformalVector) (m + 1) y)) := by
    simp only [TensorProduct.sub_tmul, TensorProduct.tmul_sub]
    abel
  rw [hsplit, hV, hW]
  simp only [TensorProduct.add_tmul, TensorProduct.tmul_add,
    TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_add]
  by_cases hmn : m + n = 0
  · simp only [if_pos hmn, LinearMap.smul_apply, Module.End.one_apply,
      TensorProduct.smul_tmul', TensorProduct.tmul_smul, mul_add, add_smul,
      LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply]
    abel
  · simp only [if_neg hmn, LinearMap.zero_apply,
      TensorProduct.zero_tmul, TensorProduct.tmul_zero, add_zero]

end

section Concrete

open Sl2Coset

/-- The concrete ambient conformal vector has exactly the factor-sum modes. -/
theorem ambientConformal_eq_tensorConformal :
    ambientConformal = tensorConformal AVOA BVOA := rfl

theorem ambientConformal_zero_mode :
    mode (abSVA.Y ambientConformal) 0 = diagonalAction.translation.T :=
  tensorConformal_zero_mode AVOA BVOA

/-- Diagonal Sugawara contributes zero to conformal weight on the commutant. -/
theorem cosetOmega_L0 (h : ℂ) (x : ASpace ⊗[ℂ] BSpace)
    (hx : x ∈ abSVA.grading h) (hc : x ∈ cosetSubspace diagonalAction.toAffineSl2Action) :
    mode (abSVA.Y cosetOmega) 1 x = h • x := by
  rw [cosetOmega, map_sub, mode_sub, LinearMap.sub_apply]
  have hz := sugawara_mode_coset diagonalAction.toAffineSl2Action
    diagonalAction.translation hc 1 (by norm_num)
  change mode (abSVA.Y ambientConformal) 1 x -
    mode (abSVA.Y (sugawaraState diagonalAction.toAffineSl2Action)) 1 x = _
  rw [hz, sub_zero]
  exact tensorConformal_L0 AVOA BVOA h x hx

/-- The coset conformal translation is the restriction of ambient translation. -/
theorem cosetOmega_zero_mode (x : ASpace ⊗[ℂ] BSpace)
    (hc : x ∈ cosetSubspace diagonalAction.toAffineSl2Action) :
    mode (abSVA.Y cosetOmega) 0 x = diagonalAction.translation.T x := by
  rw [cosetOmega, map_sub, mode_sub, LinearMap.sub_apply]
  have hz := sugawara_mode_coset diagonalAction.toAffineSl2Action
    diagonalAction.translation hc 0 (by norm_num)
  change mode (abSVA.Y ambientConformal) 0 x -
    mode (abSVA.Y (sugawaraState diagonalAction.toAffineSl2Action)) 0 x = _
  rw [hz, sub_zero, ambientConformal_zero_mode]

/-- The conformal difference implements differentiation of every coset field. -/
theorem cosetOmega_translation (x : ASpace ⊗[ℂ] BSpace)
    (hc : x ∈ cosetSubspace diagonalAction.toAffineSl2Action) :
    abSVA.Y (mode (abSVA.Y cosetOmega) 0 x) = deriv (abSVA.Y x) := by
  rw [cosetOmega_zero_mode x hc]
  exact translation_state diagonalAction.translation x

end Concrete
end VOA.Sl2CosetConcrete
