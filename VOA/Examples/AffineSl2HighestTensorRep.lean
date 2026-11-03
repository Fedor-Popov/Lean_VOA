/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2HighestTensorDegree

/-!
# Full affine Lie representations with independent highest creation words

The concrete triple tensor construction includes the centre and derivation,
not only the three current colours. It realizes arbitrary level and highest
weight with actual independent occupation words and a nonzero highest vector.
-/
namespace VOA.Wak.Charged
open Module (End)
open MvPolynomial AffineVOA
open AffineVOA.HighestNormalOrdering
open AffineVOA.NormalOrdering (currentWord)
open scoped TensorProduct
noncomputable section

/-- Explicit scalar bilinearity for the actual tensor endomorphism bracket. -/
private theorem tensor_lie_smul (z : ℂ) (S T : End ℂ HighestTensorFock) :
    ⁅S,z • T⁆=z • ⁅S,T⁆ := by
  rw [Ring.lie_def,Ring.lie_def,mul_smul_comm,smul_mul_assoc,smul_sub]

/-- The same scalar bilinearity in the first operator. -/
private theorem tensor_smul_lie (z : ℂ) (S T : End ℂ HighestTensorFock) :
    ⁅z • S,T⁆=z • ⁅S,T⁆ := by
  rw [Ring.lie_def,Ring.lie_def,mul_smul_comm,smul_mul_assoc,smul_sub]

/-- Scalar identities are central on the actual tensor carrier. -/
private theorem tensor_scalar_central (z : ℂ) (T : End ℂ HighestTensorFock) :
    ⁅z • (1 : End ℂ HighestTensorFock),T⁆=0 := by
  rw [Ring.lie_def,mul_smul_comm,smul_mul_assoc,one_mul,mul_one,sub_self]

/-- Linear extension of the three actual tensor currents to an sl2 loop. -/
def highestTensorLoop (a b c : ℂ) (n : ℤ) : Sl2→ₗ[ℂ]End ℂ HighestTensorFock where
  toFun x := ∑ i,x i • highestTensorJ a b c i n
  map_add' x y := by simp [Pi.add_apply,add_smul,Finset.sum_add_distrib]
  map_smul' z x := by simp [Pi.smul_apply,smul_smul,Finset.smul_sum]

/-- Evaluation of the colour-linear loop action. -/
theorem highestTensorLoop_apply (a b c : ℂ) (n : ℤ) (x : Sl2) :
    highestTensorLoop a b c n x=∑ i,x i • highestTensorJ a b c i n := rfl

/-- The actual loop bracket is the sl2 bracket plus the scalar affine
cocycle at the sum level. No extra representation premise is introduced. -/
theorem highestTensorLoop_comm (a b c : ℂ) (ha : a+2≠0) (hb : b+2≠0) (hc : c+2≠0)
    (x y : Sl2) (m n : ℤ) :
    ⁅highestTensorLoop a b c m x,highestTensorLoop a b c n y⁆=
      highestTensorLoop a b c (m+n) ⁅x,y⁆+
      if m+n=0 then ((m : ℂ)*kappaForm x y) •
        ((2*a+3*b+4*c) • (1 : End ℂ HighestTensorFock)) else 0 := by
  simp only [highestTensorLoop_apply,bracket_apply,kappaForm_apply,Fin.sum_univ_three,
    add_lie,lie_add,tensor_smul_lie,tensor_lie_smul,highestTensorJ_comm a b c ha hb hc,
    smul_add,fabc,kappa]
  by_cases hz : m+n=0
  · simp only [if_pos hz,smul_smul]; module
  · simp only [if_neg hz,smul_zero,add_zero]; module

/-- The actual degree differentiates every colour-linear loop. -/
theorem highestTensorLoop_degree (a b c : ℂ) (x : Sl2) (n : ℤ) :
    ⁅highestTensorDegree,highestTensorLoop a b c n x⁆=
      (n : ℂ) • highestTensorLoop a b c n x := by
  simp only [highestTensorLoop_apply,Fin.sum_univ_three,lie_add,tensor_lie_smul,
    highestTensorDegree_comm]
  module

/-- Fully checked current data for the affine Lie algebra, including its
actual scalar centre and derivation. -/
def highestTensorData (a b c : ℂ) (ha : a+2≠0) (hb : b+2≠0) (hc : c+2≠0) :
    AffineCentralCurrentData HighestTensorFock where
  loopMode := highestTensorLoop a b c
  degree := highestTensorDegree
  central := (2*a+3*b+4*c) • 1
  loop_comm := highestTensorLoop_comm a b c ha hb hc
  degree_comm := highestTensorLoop_degree a b c
  central_comm x n := tensor_scalar_central _ _
  central_degree := tensor_scalar_central _ _

/-- The ACTUAL full affine Lie representation on the tensor carrier. -/
def highestTensorRho (a b c : ℂ) (ha : a+2≠0) (hb : b+2≠0) (hc : c+2≠0) :
    AffSl2→ₗ⁅ℂ⁆End ℂ HighestTensorFock := (highestTensorData a b c ha hb hc).rho

/-- The representation on a basis-coloured loop is its actual current. -/
theorem highestTensorRho_mode (a b c : ℂ) (ha : a+2≠0) (hb : b+2≠0) (hc : c+2≠0)
    (i : Fin 3) (n : ℤ) :
    highestTensorRho a b c ha hb hc (AffineLie.ofLoop kappaForm kappaForm_isInvariant (basis i) n)=
      highestTensorJ a b c i n := by
  rw [highestTensorRho,AffineCentralCurrentData.rho_ofLoop]
  change (∑ j,basis i j • highestTensorJ a b c j n)=_
  simp [basis]

/-- The affine centre acts on the whole actual tensor carrier by its sum level. -/
theorem highestTensorRho_central (a b c : ℂ) (ha : a+2≠0) (hb : b+2≠0) (hc : c+2≠0) :
    highestTensorRho a b c ha hb hc (AffineLie.C kappaForm kappaForm_isInvariant)=
      (2*a+3*b+4*c) • (1 : End ℂ HighestTensorFock) :=
  (highestTensorData a b c ha hb hc).rho_C

/-- The affine derivation is the actual tensor degree operator. -/
theorem highestTensorRho_degree (a b c : ℂ) (ha : a+2≠0) (hb : b+2≠0) (hc : c+2≠0) :
    highestTensorRho a b c ha hb hc (AffineLie.ell0 kappaForm kappaForm_isInvariant)=highestTensorDegree :=
  (highestTensorData a b c ha hb hc).rho_ell0

/-- The actual tensor highest vector is nonzero, as its proved projection
is polynomial one. -/
theorem highestTensorVacuum_ne_zero : highestTensorVacuum≠0 := by
  intro h
  have he := congrArg highestTensorProjection h
  rw [highestTensorProjection_vacuum,map_zero] at he
  exact one_ne_zero he

/-- For EVERY level and highest weight there is an ACTUAL full affine Lie
representation with the required highest vector and independent creation
occupation words. No determinant, singular existence or PBW premise occurs. -/
theorem exists_independent_highest_realization (k h : ℂ) :
    ∃ R : AffSl2→ₗ⁅ℂ⁆End ℂ HighestTensorFock,
      R (AffineLie.C kappaForm kappaForm_isInvariant)=k • (1 : End ℂ HighestTensorFock) ∧
      R (AffineLie.ell0 kappaForm kappaForm_isInvariant) highestTensorVacuum=0 ∧
      (∀ i n,¬IsLower i n →
        R (AffineLie.ofLoop kappaForm kappaForm_isInvariant (basis i) n) highestTensorVacuum=
          if n=0 ∧ i=2 then h • highestTensorVacuum else 0) ∧
      LinearIndependent ℂ (fun d : Occupation => currentWord
        (fun i n => R (AffineLie.ofLoop kappaForm kappaForm_isInvariant (basis i) n))
        (occupationWord d) highestTensorVacuum) := by
  obtain ⟨a,b,c,ha,hb,hc,hk,hh⟩ := exists_highest_tensor_levels k h
  refine ⟨highestTensorRho a b c ha hb hc,?_,?_,?_,?_⟩
  · rw [highestTensorRho_central,hk]
  · rw [highestTensorRho_degree,highestTensorDegree_vacuum]
  · intro i n hn
    rw [highestTensorRho_mode,highestTensorJ_highest a b c i n hn,hh]
  · simpa only [highestTensorRho_mode] using highestTensor_words_independent a b c

end
end VOA.Wak.Charged
