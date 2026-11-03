/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2VermaHighestCoordinate

/-!
# Actual Chevalley dual of the affine Verma module

Transpose opposite-index currents while interchanging E and F. This is a
bilinear algebraic dual: no complex conjugation is present. Both scalar
parameters are preserved, as is the self-adjoint degree operator.
-/
namespace VOA.AffineVOA.HighestModule
open Module (End)
noncomputable section

/-- Chevalley colour reversal exchanges E,F and fixes H. -/
def adjointColour (a : Fin 3) : Fin 3 := if a=0 then 1 else if a=1 then 0 else 2

/-- The Chevalley colour reversal is an involution. -/
theorem adjointColour_involutive (a : Fin 3) : adjointColour (adjointColour a)=a := by
  fin_cases a <;> rfl

/-- Actual opposite-mode transpose on the full algebraic dual. -/
def dualMode (k h : ℂ) (a : Fin 3) (n : ℤ) : End ℂ (Module.Dual ℂ (Verma k h)) :=
  (mode k h (adjointColour a) (-n)).dualMap

/-- The degree operator is self-adjoint under the contravariant convention. -/
def dualDegree (k h : ℂ) : End ℂ (Module.Dual ℂ (Verma k h)) :=
  (rho k h (AffineLie.ell0 kappaForm kappaForm_isInvariant)).dualMap

/-- Opposite-index Chevalley transposes satisfy the actual affine current
relations with the original central level. -/
theorem dualMode_comm (k h : ℂ) (a b : Fin 3) (m n : ℤ) :
    ⁅dualMode k h a m,dualMode k h b n⁆=
      (∑ c,fabc a b c • dualMode k h c (m+n))+
      if m+n=0 then ((m : ℂ)*k*kappa a b) • (1 : End ℂ (Module.Dual ℂ (Verma k h))) else 0 := by
  apply LinearMap.ext
  intro f
  apply LinearMap.ext
  intro v
  have hc := congrArg (fun T : End ℂ (Verma k h) => f (T v))
    (mode_comm k h (adjointColour b) (adjointColour a) (-n) (-m))
  dsimp only at hc
  simp only [Ring.lie_def,LinearMap.sub_apply,Module.End.mul_apply,LinearMap.add_apply,
    LinearMap.sum_apply,LinearMap.smul_apply,map_sub,map_add,map_sum,map_smul] at hc
  change f (mode k h (adjointColour b) (-n) (mode k h (adjointColour a) (-m) v))-
    f (mode k h (adjointColour a) (-m) (mode k h (adjointColour b) (-n) v))=_
  simp only [LinearMap.add_apply,LinearMap.sum_apply,LinearMap.smul_apply,dualMode,
    LinearMap.dualMap_apply]
  by_cases hz : m+n=0
  · have hn : n = -m := by omega
    subst n
    simp only [neg_neg,add_neg_cancel,neg_add_cancel,if_true,LinearMap.smul_apply,
      Module.End.one_apply,map_smul,Int.cast_neg] at hc ⊢
    fin_cases a <;> fin_cases b <;>
      norm_num [adjointColour,fabc,kappa,Fin.sum_univ_three,show (2 : Fin 3)≠0 by decide,show (2 : Fin 3)≠1 by decide] at hc ⊢ <;> linear_combination hc
  · have hh : -n + -m≠0 := by omega
    have hi : -n + -m=-(m+n) := by omega
    simp only [if_neg hh,LinearMap.zero_apply,map_zero,add_zero,hi] at hc
    simp only [if_neg hz,LinearMap.zero_apply,add_zero]
    fin_cases a <;> fin_cases b <;>
      norm_num [adjointColour,fabc,kappa,Fin.sum_univ_three,show (2 : Fin 3)≠0 by decide,show (2 : Fin 3)≠1 by decide,hh,neg_ne_zero.mpr hz] at hc ⊢ <;> linear_combination hc

/-- The transposed degree has the required commutator with every dual mode. -/
theorem dualDegree_comm (k h : ℂ) (a : Fin 3) (n : ℤ) :
    ⁅dualDegree k h,dualMode k h a n⁆=(n : ℂ) • dualMode k h a n := by
  apply LinearMap.ext
  intro f
  apply LinearMap.ext
  intro v
  have hc := congrArg (fun T : End ℂ (Verma k h) => f (T v))
    (degree_mode_comm k h (adjointColour a) (-n))
  dsimp only at hc
  simp only [Ring.lie_def,LinearMap.sub_apply,Module.End.mul_apply,
    LinearMap.smul_apply,map_sub,map_smul,Int.cast_neg] at hc
  change f (mode k h (adjointColour a) (-n) (rho k h _ v))-
    f (rho k h _ (mode k h (adjointColour a) (-n) v))=(n : ℂ)*f (mode k h (adjointColour a) (-n) v)
  linear_combination -hc

/-- Linear extension of the three dual currents to a general sl2 element. -/
def dualLoop (k h : ℂ) (n : ℤ) : Sl2→ₗ[ℂ]End ℂ (Module.Dual ℂ (Verma k h)) where
  toFun x := ∑ i,x i • dualMode k h i n
  map_add' x y := by simp [Pi.add_apply,add_smul,Finset.sum_add_distrib]
  map_smul' z x := by simp [Pi.smul_apply,smul_smul,Finset.smul_sum]

/-- Scalar bilinearity of the actual dual endomorphism bracket. -/
private theorem end_lie_smul {E : Type*} [AddCommGroup E] [Module ℂ E]
    (z : ℂ) (S T : End ℂ E) : ⁅S,z • T⁆=z • ⁅S,T⁆ := by
  rw [Ring.lie_def,Ring.lie_def,mul_smul_comm,smul_mul_assoc,smul_sub]

/-- Scalar bilinearity in the first dual endomorphism. -/
private theorem end_smul_lie {E : Type*} [AddCommGroup E] [Module ℂ E]
    (z : ℂ) (S T : End ℂ E) : ⁅z • S,T⁆=z • ⁅S,T⁆ := by
  rw [Ring.lie_def,Ring.lie_def,mul_smul_comm,smul_mul_assoc,smul_sub]

/-- Scalar identity operators commute with every actual operator. -/
private theorem end_scalar_central {E : Type*} [AddCommGroup E] [Module ℂ E]
    (z : ℂ) (T : End ℂ E) : ⁅z • (1 : End ℂ E),T⁆=0 := by
  rw [Ring.lie_def,mul_smul_comm,smul_mul_assoc,one_mul,mul_one,sub_self]

/-- The colour-linear dual loops satisfy the full affine cocycle formula. -/
theorem dualLoop_comm (k h : ℂ) (x y : Sl2) (m n : ℤ) :
    ⁅dualLoop k h m x,dualLoop k h n y⁆=dualLoop k h (m+n) ⁅x,y⁆+
      if m+n=0 then ((m : ℂ)*kappaForm x y) • (k • (1 : End ℂ (Module.Dual ℂ (Verma k h)))) else 0 := by
  simp only [dualLoop,LinearMap.coe_mk,AddHom.coe_mk,bracket_apply,kappaForm_apply,Fin.sum_univ_three,
    add_lie,lie_add,end_smul_lie,end_lie_smul,dualMode_comm,smul_add,fabc,kappa]
  by_cases hz : m+n=0
  · simp only [if_pos hz,smul_smul]; module
  · simp only [if_neg hz,smul_zero,add_zero]; module

/-- The degree relation also holds after colour-linear extension. -/
theorem dualLoop_degree (k h : ℂ) (x : Sl2) (n : ℤ) :
    ⁅dualDegree k h,dualLoop k h n x⁆=(n : ℂ) • dualLoop k h n x := by
  simp only [dualLoop,LinearMap.coe_mk,AddHom.coe_mk,Fin.sum_univ_three,
    lie_add,end_lie_smul,dualDegree_comm]
  module

/-- Complete actual affine current data on the algebraic dual. -/
def dualData (k h : ℂ) : AffineCentralCurrentData (Module.Dual ℂ (Verma k h)) where
  loopMode := dualLoop k h
  degree := dualDegree k h
  central := k • 1
  loop_comm := dualLoop_comm k h
  degree_comm := dualLoop_degree k h
  central_comm x n := end_scalar_central _ _
  central_degree := end_scalar_central _ _

/-- The full actual affine Lie representation on the algebraic dual. -/
def dualRho (k h : ℂ) : AffSl2→ₗ⁅ℂ⁆End ℂ (Module.Dual ℂ (Verma k h)) := (dualData k h).rho

/-- The full dual action agrees with the prescribed basis-coloured modes. -/
theorem dualRho_mode (k h : ℂ) (a : Fin 3) (n : ℤ) :
    dualRho k h (modeElement a n)=dualMode k h a n := by
  rw [dualRho,modeElement,AffineCentralCurrentData.rho_ofLoop]
  change (∑ i,basis a i • dualMode k h i n)=_
  simp [basis]

/-- The centre acts by the original level in the dual. -/
theorem dualRho_central (k h : ℂ) :
    dualRho k h (AffineLie.C kappaForm kappaForm_isInvariant)=k • (1 : End ℂ (Module.Dual ℂ (Verma k h))) :=
  (dualData k h).rho_C

/-- The full dual derivation is the stated transpose. -/
theorem dualRho_degree (k h : ℂ) :
    dualRho k h (AffineLie.ell0 kappaForm kappaForm_isInvariant)=dualDegree k h :=
  (dualData k h).rho_ell0

end
end VOA.AffineVOA.HighestModule
