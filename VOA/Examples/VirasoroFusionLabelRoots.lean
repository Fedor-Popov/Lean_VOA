/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroFusionRoots

/-!
# Label arithmetic for the proved fusion-root restriction

On the (u,0) incoming curve, the possible resonance indices obey a linear
equation in t. For nonreal t every strictly intermediate coefficient is
nonresonant. This is an ordinary scalar nonvanishing result, not construction
of a fusion state or a theorem about rational minimal-model specialization.
-/
namespace VOA.InverseDS.VirasoroVerma

/-- The standard two-label highest-weight expression, with complex labels
so its arithmetic can be used before integer specialization. -/
noncomputable def fusionKacWeight (u v t : ℂ) : ℂ :=
  ((u*t-v)^2-(t-1)^2)/(4*t)

/-- A gauge exponent on the incoming (u,0) highest-weight curve. -/
noncomputable def fusionLabelGauge (u t : ℂ) : ℂ := (1+(u-1)*t)/2

/-- The displayed gauge exponent solves the required quadratic exactly. -/
theorem fusionLabelGauge_quadratic (u t : ℂ) (ht : t≠0) :
    (fusionLabelGauge u t)^2+(t-1)*fusionLabelGauge u t-t*fusionKacWeight u 0 t=0 := by
  unfold fusionLabelGauge fusionKacWeight
  field_simp
  ring

/-- The root condition becomes the explicit linear-in-t resonance equation
used by the general coefficient recursion. Signs and normalizations follow
from the actual scalar, rather than an imported fusion formula. -/
theorem fusionLabel_root_iff (u t : ℂ) (N i r : ℕ) (ht : t≠0) :
    fusionKacWeight u ((N:ℂ)-1) t+(r:ℂ)-vermaBSAWeight N t=
      fusionRoot (fusionKacWeight u 0 t) t (fusionLabelGauge u t) N i ↔
      ((i:ℂ)*u-(r:ℂ))*t=(i:ℂ)*((N:ℂ)-1-(i:ℂ)) := by
  have he : (fusionKacWeight u ((N:ℂ)-1) t+(r:ℂ)-vermaBSAWeight N t-
      fusionRoot (fusionKacWeight u 0 t) t (fusionLabelGauge u t) N i)*t=
      (r:ℂ)*t-(i:ℂ)*u*t+(i:ℂ)*((N:ℂ)-1-(i:ℂ)) := by
    unfold fusionKacWeight vermaBSAWeight fusionRoot fusionLabelGauge
    field_simp
    ring
  constructor
  · intro hh
    rw [hh,sub_self,zero_mul] at he
    linear_combination he
  · intro hh
    have hz : (fusionKacWeight u ((N:ℂ)-1) t+(r:ℂ)-vermaBSAWeight N t-
        fusionRoot (fusionKacWeight u 0 t) t (fusionLabelGauge u t) N i)*t=0 := by
      rw [he]
      linear_combination -hh
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right ht)

/-- Nonreal parameters avoid every strictly intermediate resonance for
positive integer labels. This does not assert the same at rational t. -/
theorem fusionLabel_intermediate_nonresonant (A N r i : ℕ) (t : ℂ)
    (him : t.im≠0) (hi : i<N) (hr : 0<r) (hrN : r<A*(N-1)) :
    ((i:ℂ)*(A:ℂ)-(r:ℂ))*t≠(i:ℂ)*((N:ℂ)-1-(i:ℂ)) := by
  intro he
  have himEq := congrArg Complex.im he
  simp only [Complex.mul_re,Complex.mul_im,Complex.sub_im,Complex.natCast_im,Complex.natCast_re,
    Complex.sub_re,Complex.one_im,Complex.one_re,mul_zero,zero_mul,sub_zero,zero_sub,
    add_zero,zero_add] at himEq
  have hiR : (i:ℝ)*(A:ℝ)-(r:ℝ)=0 := (mul_eq_zero.mp himEq).resolve_right him
  have hir : i*A=r := by exact_mod_cast (sub_eq_zero.mp hiR)
  have hre := congrArg Complex.re he
  simp only [Complex.mul_re,Complex.mul_im,Complex.sub_re,Complex.sub_im,
    Complex.natCast_im,Complex.natCast_re,Complex.one_re,Complex.one_im,
    mul_zero,zero_mul,sub_zero,zero_sub,add_zero,zero_add] at hre
  rw [hiR,zero_mul] at hre
  rcases mul_eq_zero.mp hre.symm with hzero | hlast
  · have iz : i=0 := by exact_mod_cast hzero
    subst i
    simp at hir
    omega
  · have hlast' : (N:ℤ)-1-(i:ℤ)=0 := by exact_mod_cast hlast
    have hn : N=i+1 := by omega
    rw [hn,Nat.add_sub_cancel] at hrN
    have hir' : r=A*i := by simpa [Nat.mul_comm] using hir.symm
    omega

/-- The ACTUAL BSA source diagonal is nonzero at every strictly intermediate
coefficient for nonreal t on the intended general-label curves. This supplies
generic scalar invertibility, but not a recursively constructed kernel. -/
theorem wardBSASourceDiagonal_nonreal_intermediate (A N r : ℕ) (t : ℂ)
    (him : t.im≠0) (hN : 0<N) (hr : 0<r) (hrN : r<A*(N-1)) :
    wardBSASourceDiagonal (fusionKacWeight (A:ℂ) ((N:ℂ)-1) t)
      (fusionKacWeight (A:ℂ) 0 t) t N r N (vermaBSAWeight N t+(N:ℂ))≠0 := by
  have ht : t≠0 := by intro hz; apply him; simp [hz]
  apply wardBSASourceDiagonal_ne_zero_of_avoid_roots _ _ _ _ (fusionLabelGauge (A:ℂ) t) N r hN ht
    (fusionLabelGauge_quadratic (A:ℂ) t ht)
  intro i hi he
  exact fusionLabel_intermediate_nonresonant A N r i t him hi hr hrN
    ((fusionLabel_root_iff (A:ℂ) t N i r ht).mp he)
end VOA.InverseDS.VirasoroVerma
