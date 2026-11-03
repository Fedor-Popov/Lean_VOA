/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Examples.InverseDSScreeningRaising
import VOA.Core.TensorFieldLift

/-!
# Heterotypic tensor convolution for the inverse-DS screening

The Adamović--Milas screening current is the tensor product of a Virasoro intertwining field
and the Pi exponential `exp(nu)`.  Neither factor is an endomorphism field, and both naturally
carry half-integral powers.  A coefficient of their tensor product therefore cannot be defined
as a `finsum` of linear maps: the operator family need not have globally finite support even
though it is finite on every vector.

This file constructs the correct pointwise-finite linear map.  Coefficients are indexed by
half-power numerators, so the ordinary residue is coefficient `-2`.  It proves that the tensor
convolution is lower truncated and that every Pi-current intertwining identity lifts through an
arbitrary Virasoro intertwining factor.  Consequently the Cartan screening identity is complete,
and the raising identity is complete modulo the single odd-pairing Newton identity isolated in
`InverseDSScreeningRaising`.
-/

set_option linter.style.longLine false

namespace VOA
namespace InverseDS
namespace ScreeningTensor

open Module (End)
open scoped TensorProduct
open HalfLattice
open ScreeningCoset

noncomputable section

universe u₁ u₂ u₃ u₄

variable {A : Type u₁} {A' : Type u₂} {B : Type u₃} {B' : Type u₄}
variable [AddCommGroup A] [Module ℂ A] [AddCommGroup A'] [Module ℂ A']
variable [AddCommGroup B] [Module ℂ B] [AddCommGroup B'] [Module ℂ B']

/-! ## Pointwise finite tensor coefficients -/

/-- One coefficient in the tensor product of two heterotypic fields. -/
def heterotypicTensorMap (f : A →ₗ[ℂ] A') (g : B →ₗ[ℂ] B') :
    A ⊗[ℂ] B →ₗ[ℂ] A' ⊗[ℂ] B' :=
  TensorProduct.map f g

@[simp] theorem heterotypicTensorMap_tmul (f : A →ₗ[ℂ] A')
    (g : B →ₗ[ℂ] B') (a : A) (b : B) :
    heterotypicTensorMap f g (a ⊗ₜ[ℂ] b) = f a ⊗ₜ[ℂ] g b := by
  rw [heterotypicTensorMap, TensorProduct.map_tmul]

/-- The diagonal family whose pointwise `finsum` is the tensor-product coefficient of total
half-power numerator `t`. -/
def tensorConvolutionTerm
    (I : FormalDist (A →ₗ[ℂ] A')) (S : FormalDist (B →ₗ[ℂ] B'))
    (t m : ℤ) (x : A ⊗[ℂ] B) : A' ⊗[ℂ] B' :=
  heterotypicTensorMap (I m) (S (t - m)) x

/-- Explicit finiteness condition needed to assemble a heterotypic tensor convolution.
It is pointwise in the input vector, rather than global in the operator coefficients. -/
def TensorConvolutionFinite
    (I : FormalDist (A →ₗ[ℂ] A')) (S : FormalDist (B →ₗ[ℂ] B')) : Prop :=
  ∀ t x, (Function.support (fun m : ℤ => tensorConvolutionTerm I S t m x)).Finite

theorem tensorConvolutionTerm_support_tmul_finite
    {I : FormalDist (A →ₗ[ℂ] A')} {S : FormalDist (B →ₗ[ℂ] B')}
    (hI : ScreeningCoset.IsHeterotypicField I)
    (hS : ScreeningCoset.IsHeterotypicField S)
    (t : ℤ) (a : A) (b : B) :
    (Function.support (fun m : ℤ =>
      tensorConvolutionTerm I S t m (a ⊗ₜ[ℂ] b))).Finite := by
  obtain ⟨BI, hBI⟩ := hI a
  obtain ⟨BS, hBS⟩ := hS b
  apply Set.Finite.subset (Set.finite_Icc BI (t - BS))
  intro m hm
  rw [Set.mem_Icc]
  constructor
  · by_contra h
    apply hm
    change heterotypicTensorMap (I m) (S (t - m)) (a ⊗ₜ[ℂ] b) = 0
    rw [heterotypicTensorMap_tmul, hBI m (by omega),
      TensorProduct.zero_tmul]
  · by_contra h
    apply hm
    change heterotypicTensorMap (I m) (S (t - m)) (a ⊗ₜ[ℂ] b) = 0
    rw [heterotypicTensorMap_tmul, hBS (t - m) (by omega),
      TensorProduct.tmul_zero]

/-- Two lower-truncated heterotypic fields always satisfy pointwise diagonal finiteness. -/
theorem tensorConvolutionFinite_of_isHeterotypicField
    {I : FormalDist (A →ₗ[ℂ] A')} {S : FormalDist (B →ₗ[ℂ] B')}
    (hI : ScreeningCoset.IsHeterotypicField I)
    (hS : ScreeningCoset.IsHeterotypicField S) :
    TensorConvolutionFinite I S := by
  intro t x
  induction x using TensorProduct.induction_on with
  | zero =>
      have hz : (fun m : ℤ => tensorConvolutionTerm I S t m 0) = 0 := by
        funext m
        exact (heterotypicTensorMap (I m) (S (t - m))).map_zero
      rw [hz, Function.support_zero]
      exact Set.finite_empty
  | add x y hx hy =>
      apply Set.Finite.subset (hx.union hy)
      intro m hm
      rw [Set.mem_union]
      by_cases hx0 : tensorConvolutionTerm I S t m x = 0
      · right
        rw [Function.mem_support]
        intro hy0
        apply hm
        change heterotypicTensorMap (I m) (S (t - m)) (x + y) = 0
        rw [map_add]
        change tensorConvolutionTerm I S t m x +
          tensorConvolutionTerm I S t m y = 0
        rw [hx0, hy0, add_zero]
      · left
        exact Function.mem_support.mpr hx0
  | tmul a b => exact tensorConvolutionTerm_support_tmul_finite hI hS t a b

/-- The pointwise tensor-convolution coefficient as a genuine linear map. -/
def tensorConvolutionCoeff
    (I : FormalDist (A →ₗ[ℂ] A')) (S : FormalDist (B →ₗ[ℂ] B'))
    (hfin : TensorConvolutionFinite I S) (t : ℤ) :
    A ⊗[ℂ] B →ₗ[ℂ] A' ⊗[ℂ] B' where
  toFun x := ∑ᶠ m : ℤ, tensorConvolutionTerm I S t m x
  map_add' x y := by
    rw [← finsum_add_distrib (hfin t x) (hfin t y)]
    exact finsum_congr fun m => by
      rw [tensorConvolutionTerm, map_add]
      rfl
  map_smul' c x := by
    rw [RingHom.id_apply, smul_finsum' c (hfin t x)]
    exact finsum_congr fun m => by
      rw [tensorConvolutionTerm, map_smul]
      rfl

@[simp] theorem tensorConvolutionCoeff_apply
    (I : FormalDist (A →ₗ[ℂ] A')) (S : FormalDist (B →ₗ[ℂ] B'))
    (hfin : TensorConvolutionFinite I S) (t : ℤ) (x : A ⊗[ℂ] B) :
    tensorConvolutionCoeff I S hfin t x =
      ∑ᶠ m : ℤ, tensorConvolutionTerm I S t m x := rfl

/-- Tensor product of two half-power heterotypic fields. -/
def tensorConvolutionField
    (I : FormalDist (A →ₗ[ℂ] A')) (S : FormalDist (B →ₗ[ℂ] B'))
    (hfin : TensorConvolutionFinite I S) :
    FormalDist ((A ⊗[ℂ] B) →ₗ[ℂ] (A' ⊗[ℂ] B')) :=
  fun t => tensorConvolutionCoeff I S hfin t

theorem tensorConvolutionField_tmul
    (I : FormalDist (A →ₗ[ℂ] A')) (S : FormalDist (B →ₗ[ℂ] B'))
    (hfin : TensorConvolutionFinite I S) (t : ℤ) (a : A) (b : B) :
    tensorConvolutionField I S hfin t (a ⊗ₜ[ℂ] b) =
      ∑ᶠ m : ℤ, I m a ⊗ₜ[ℂ] S (t - m) b := by
  rw [tensorConvolutionField, tensorConvolutionCoeff_apply]
  exact finsum_congr fun m => heterotypicTensorMap_tmul _ _ _ _

/-- The tensor convolution remains lower truncated. -/
theorem tensorConvolutionField_isHeterotypicField
    {I : FormalDist (A →ₗ[ℂ] A')} {S : FormalDist (B →ₗ[ℂ] B')}
    (hI : ScreeningCoset.IsHeterotypicField I)
    (hS : ScreeningCoset.IsHeterotypicField S) :
    ScreeningCoset.IsHeterotypicField
      (tensorConvolutionField I S
        (tensorConvolutionFinite_of_isHeterotypicField hI hS)) := by
  intro x
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, fun n _ => map_zero _⟩
  | add x y hx hy =>
      obtain ⟨Bx, hBx⟩ := hx
      obtain ⟨By, hBy⟩ := hy
      refine ⟨min Bx By, fun n hn => ?_⟩
      rw [map_add, hBx n (lt_of_lt_of_le hn (min_le_left _ _)),
        hBy n (lt_of_lt_of_le hn (min_le_right _ _)), add_zero]
  | tmul a b =>
      obtain ⟨BI, hBI⟩ := hI a
      obtain ⟨BS, hBS⟩ := hS b
      refine ⟨BI + BS, fun t ht => ?_⟩
      rw [tensorConvolutionField_tmul]
      refine finsum_eq_zero_of_forall_eq_zero fun m => ?_
      by_cases hm : m < BI
      · rw [hBI m hm, TensorProduct.zero_tmul]
      · rw [hBS (t - m) (by omega), TensorProduct.tmul_zero]

/-! ## Lifting Pi-current intertwining through the Virasoro factor -/

def sourceSecondCurrent (J : End ℂ B) : End ℂ (A ⊗[ℂ] B) :=
  LinearMap.lTensor A J

def targetSecondCurrent (J : End ℂ B') : End ℂ (A' ⊗[ℂ] B') :=
  LinearMap.lTensor A' J

theorem tensorMap_intertwines_second
    (f : A →ₗ[ℂ] A') (g : B →ₗ[ℂ] B') (JS : End ℂ B) (JT : End ℂ B')
    (h : JT.comp g = g.comp JS) :
    (targetSecondCurrent JT).comp (heterotypicTensorMap f g) =
      (heterotypicTensorMap f g).comp (sourceSecondCurrent JS) := by
  refine LinearMap.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a b =>
      simp only [LinearMap.comp_apply, heterotypicTensorMap_tmul,
        targetSecondCurrent, sourceSecondCurrent, LinearMap.lTensor_tmul]
      exact congrArg (fun y => f a ⊗ₜ[ℂ] y) (LinearMap.congr_fun h b)

theorem tensorConvolution_intertwines_second
    {I : FormalDist (A →ₗ[ℂ] A')} {S : FormalDist (B →ₗ[ℂ] B')}
    (hfin : TensorConvolutionFinite I S) (JS : End ℂ B) (JT : End ℂ B')
    (hS : ∀ n, heterotypicBracketCoeff JT (S n) JS = 0) (t : ℤ) :
    heterotypicBracketCoeff (targetSecondCurrent JT)
      (tensorConvolutionField I S hfin t) (sourceSecondCurrent JS) = 0 := by
  refine LinearMap.ext fun x => ?_
  change targetSecondCurrent JT (tensorConvolutionField I S hfin t x) -
      tensorConvolutionField I S hfin t (sourceSecondCurrent JS x) = 0
  rw [tensorConvolutionField, tensorConvolutionCoeff_apply,
    map_finsum (targetSecondCurrent JT) (hfin t x),
    tensorConvolutionCoeff_apply]
  have hterm : ∀ m : ℤ,
      targetSecondCurrent JT (tensorConvolutionTerm I S t m x) =
        tensorConvolutionTerm I S t m (sourceSecondCurrent JS x) := by
    intro m
    have hm := hS (t - m)
    rw [heterotypicBracketCoeff, sub_eq_zero] at hm
    exact LinearMap.congr_fun
      (tensorMap_intertwines_second (I m) (S (t - m)) JS JT hm) x
  rw [finsum_congr hterm, sub_self]

/-! ## The full k=-8/5 screening field -/

section Concrete

variable {Vir : Type u₁} {ShiftedVir : Type u₂}
variable [AddCommGroup Vir] [Module ℂ Vir]
variable [AddCommGroup ShiftedVir] [Module ℂ ShiftedVir]

/-- The full half-power screening field `I_Vir(v^(k),z) tensor Y(exp(nu),z)`.
The Virasoro factor is kept abstract, but the Pi factor and shifted Pi codomain are concrete. -/
def fullScreeningHalfField
    (I : FormalDist (Vir →ₗ[ℂ] ShiftedVir))
    (hI : ScreeningCoset.IsHeterotypicField I) :
    FormalDist ((Vir ⊗[ℂ] PiHalfFockCarrier) →ₗ[ℂ]
      (ShiftedVir ⊗[ℂ] PiNuCosetCarrier)) :=
  tensorConvolutionField I nuExponentialHalfField
    (tensorConvolutionFinite_of_isHeterotypicField hI
      nuExponentialHalfField_isHeterotypicField)

/-- The genuine ordinary residue is total half-power numerator `-2`.  In particular, an odd Pi
charge sector can contribute: its half-integral Pi power is paired with the complementary
half-integral Virasoro-intertwiner power. -/
def fullScreeningResidue
    (I : FormalDist (Vir →ₗ[ℂ] ShiftedVir))
    (hI : ScreeningCoset.IsHeterotypicField I) :
    (Vir ⊗[ℂ] PiHalfFockCarrier) →ₗ[ℂ]
      (ShiftedVir ⊗[ℂ] PiNuCosetCarrier) :=
  fullScreeningHalfField I hI (-2)

theorem fullScreeningResidue_tmul
    (I : FormalDist (Vir →ₗ[ℂ] ShiftedVir))
    (hI : ScreeningCoset.IsHeterotypicField I)
    (v : Vir) (p : PiHalfFockCarrier) :
    fullScreeningResidue I hI (v ⊗ₜ[ℂ] p) =
      ∑ᶠ m : ℤ, I m v ⊗ₜ[ℂ] nuExponentialHalfField (-2 - m) p := by
  rw [fullScreeningResidue, fullScreeningHalfField]
  exact tensorConvolutionField_tmul _ _ _ _ _ _

/-- The Cartan-current identity lifts through every Virasoro intertwining factor. -/
theorem fullScreening_intertwines_h
    (I : FormalDist (Vir →ₗ[ℂ] ShiftedVir))
    (hI : ScreeningCoset.IsHeterotypicField I) (j t : ℤ) :
    heterotypicBracketCoeff
      (targetSecondCurrent ((2 : ℂ) • targetMuCurrentField j))
      (fullScreeningHalfField I hI t)
      (sourceSecondCurrent ((2 : ℂ) • sourceMuCurrentField j)) = 0 := by
  apply tensorConvolution_intertwines_second
  intro n
  exact hCurrent_intertwines_nuExponential j n

/-- The raising-current identity lifts through every Virasoro intertwining factor, conditional
only on the explicit odd-pairing Newton identity. -/
theorem fullScreening_intertwines_e
    (hcross : EtaNuOddCrossIdentity)
    (I : FormalDist (Vir →ₗ[ℂ] ShiftedVir))
    (hI : ScreeningCoset.IsHeterotypicField I) (j t : ℤ) :
    heterotypicBracketCoeff
      (targetSecondCurrent (targetEtaExponentialField j))
      (fullScreeningHalfField I hI t)
      (sourceSecondCurrent (sourceEtaExponentialField j)) = 0 := by
  apply tensorConvolution_intertwines_second
  intro n
  exact raisingCurrent_intertwines_nuExponential hcross j n

end Concrete

end
end ScreeningTensor
end InverseDS
end VOA
