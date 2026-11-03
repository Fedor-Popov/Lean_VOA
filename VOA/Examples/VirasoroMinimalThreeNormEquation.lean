/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroMinimalThreePullback

/-!
# The actual scalar Ward recurrence as a formal differential equation

Third finite differences remove the quadratic convolution kernel. The
terminal residual stays undivided. Thus its hypothetical vanishing would
force the actual norm series to satisfy the cleared differential equation
through the resonant index.
-/
namespace VOA.InverseDS.VirasoroVerma
open VirModule PowerSeries

/-- The full finite Ward sum for an arbitrary scalar sequence. -/
noncomputable def minimalThreeWardSum (a : ℂ) (q : ℕ → ℂ) (r : ℕ) : ℂ :=
  ∑ j : Fin r, minimalThreeWardKernel a r j*q j

/-- The quadratic kernel has vanishing third finite difference. -/
theorem minimalThreeWardKernel_third_difference (a : ℂ) (r j : ℕ) :
    minimalThreeWardKernel a (r+3) j-3*minimalThreeWardKernel a (r+2) j+
      3*minimalThreeWardKernel a (r+1) j-minimalThreeWardKernel a r j=0 := by
  unfold minimalThreeWardKernel
  push_cast
  ring

/-- The Ward sum's third difference involves only the newest three
values; every older coefficient cancels exactly. -/
theorem minimalThreeWardSum_third_difference (a : ℂ) (q : ℕ → ℂ) (r : ℕ) :
    minimalThreeWardSum a q (r+3)-3*minimalThreeWardSum a q (r+2)+
      3*minimalThreeWardSum a q (r+1)-minimalThreeWardSum a q r=
      (3*a*((r:ℂ)+2)-2*((r:ℂ)+2)^2)*q (r+2)+
      (4*a^2-7*a*((r:ℂ)+1)+4*((r:ℂ)+1)^2)*q (r+1)+
      (-2*a^2+4*a*(r:ℂ)-2*(r:ℂ)^2)*q r := by
  classical
  unfold minimalThreeWardSum
  simp only [show r+3=(r+1)+1+1 by omega,show r+2=(r+1)+1 by omega,
    Fin.sum_univ_castSucc,Fin.val_castSucc,Fin.val_last]
  have hs : (∑ j : Fin r, minimalThreeWardKernel a (r+1+1+1) j*q j)-
      3*(∑ j : Fin r, minimalThreeWardKernel a (r+1+1) j*q j)+
      3*(∑ j : Fin r, minimalThreeWardKernel a (r+1) j*q j)-
      (∑ j : Fin r, minimalThreeWardKernel a r j*q j)=0 := by
    rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
    apply Finset.sum_eq_zero
    intro j hj
    have h := minimalThreeWardKernel_third_difference a r j
    linear_combination h*q j
  unfold minimalThreeWardKernel at hs ⊢
  push_cast at hs ⊢
  linear_combination hs

/-- The diagonal plus Ward sum, kept without division at every index. -/
noncomputable def minimalThreeScalarResidual (a : ℂ) (q : ℕ → ℂ) (r : ℕ) : ℂ :=
  (r:ℂ)*((r:ℂ)-a)*((r:ℂ)-3*a-1)*q r+(a+1)*minimalThreeWardSum a q r

/-- Expanding the cleared operator gives shifts by at most three.
This polynomial identity is valid on every formal series. -/
theorem minimalThreeNormOperator_expand (a : ℂ) (F : PowerSeries ℂ) :
    minimalThreeNormOperator a F=
      (bsaEuler (bsaEuler (bsaEuler F))-PowerSeries.C (4*a+1)*bsaEuler (bsaEuler F)+
        PowerSeries.C (a*(3*a+1))*bsaEuler F)-
      X*(3*(bsaEuler (bsaEuler (bsaEuler F))-PowerSeries.C (4*a+1)*bsaEuler (bsaEuler F)+
        PowerSeries.C (a*(3*a+1))*bsaEuler F)-
        PowerSeries.C (a+1)*(PowerSeries.C (3*a)*bsaEuler F-2*bsaEuler (bsaEuler F)))+
      X*(X*(3*(bsaEuler (bsaEuler (bsaEuler F))-PowerSeries.C (4*a+1)*bsaEuler (bsaEuler F)+
        PowerSeries.C (a*(3*a+1))*bsaEuler F)+
        PowerSeries.C (a+1)*(PowerSeries.C (4*a^2)*F-PowerSeries.C (7*a)*bsaEuler F+4*bsaEuler (bsaEuler F))))-
      X*(X*(X*((bsaEuler (bsaEuler (bsaEuler F))-PowerSeries.C (4*a+1)*bsaEuler (bsaEuler F)+
        PowerSeries.C (a*(3*a+1))*bsaEuler F)+
        PowerSeries.C (a+1)*(PowerSeries.C (2*a^2)*F-PowerSeries.C (4*a)*bsaEuler F+2*bsaEuler (bsaEuler F))))) := by
  unfold minimalThreeNormOperator
  simp only [map_mul,map_pow,map_ofNat]
  ring

/-- Every coefficient beyond the first three is the third difference of
the undivided Ward residual. -/
theorem minimalThreeNormOperator_coeff (a : ℂ) (q : ℕ → ℂ) (r : ℕ) :
    coeff (r+3) (minimalThreeNormOperator a (PowerSeries.mk q))=
      minimalThreeScalarResidual a q (r+3)-3*minimalThreeScalarResidual a q (r+2)+
        3*minimalThreeScalarResidual a q (r+1)-minimalThreeScalarResidual a q r := by
  rw [minimalThreeNormOperator_expand]
  simp only [show r+3=(r+1)+1+1 by omega,map_add,map_sub,add_mul,sub_mul,
    mul_assoc,coeff_C_mul,coeff_succ_X_mul,two_mul,show (3:PowerSeries ℂ)=1+1+1 by norm_num,
    show (4:PowerSeries ℂ)=1+1+1+1 by norm_num,one_mul,bsaEuler_coeff,coeff_mk]
  have hs := minimalThreeWardSum_third_difference a q r
  unfold minimalThreeScalarResidual
  push_cast
  linear_combination -(a+1)*hs

/-- A vanishing terminal residual extends the actual recurrence through
its singular index, without assigning a terminal norm by division. -/
theorem minimalThreeScalarResidual_vanish (p : ℕ) (hp : 2≤p) (hcop : Nat.Coprime p 3)
    (hz : minimalThreeNormResidual p=0) (r : ℕ) (hr : r≤(p-1)*2) :
    minimalThreeScalarResidual (vermaBSAWeight 3 ((3:ℂ)/(p:ℂ)))
      (minimalThreeNormCoefficient p) r=0 := by
  rcases lt_or_eq_of_le hr with hr | rfl
  · exact minimalThreeNormCoefficient_scaled_recursion p hp hcop r hr
  · have ht := minimalThree_terminal_index p hp
    unfold minimalThreeScalarResidual
    have he : (((p-1)*2:ℕ):ℂ)-3*vermaBSAWeight 3 ((3:ℂ)/(p:ℂ))-1=0 := by
      linear_combination -ht
    rw [he,mul_zero,zero_mul,zero_add]
    exact hz

/-- If the terminal residual vanished, the genuine intermediate norm
series would solve the differential equation through resonance. -/
theorem minimalThreeNormOperator_vanish_through (p : ℕ) (hp : 2≤p) (hcop : Nat.Coprime p 3)
    (hz : minimalThreeNormResidual p=0) (r : ℕ) (hr : r≤(p-1)*2) :
    coeff r (minimalThreeNormOperator (vermaBSAWeight 3 ((3:ℂ)/(p:ℂ)))
      (PowerSeries.mk (minimalThreeNormCoefficient p)))=0 := by
  let a := vermaBSAWeight 3 ((3:ℂ)/(p:ℂ))
  let q := minimalThreeNormCoefficient p
  have hw := minimalThreeScalarResidual_vanish p hp hcop hz
  change coeff r (minimalThreeNormOperator a (PowerSeries.mk q))=0
  by_cases h3 : 3≤r
  · obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le h3
    rw [show 3+n=n+3 by omega,minimalThreeNormOperator_coeff]
    rw [hw _ (by omega),hw _ (by omega),hw _ (by omega),hw _ (by omega)]
    ring
  · interval_cases r
    all_goals
      have hw0 := hw 0 (by omega)
      have hw1 := hw 1 (by omega)
      have hw2 := hw 2 (by omega)
      change minimalThreeScalarResidual a q 0=0 at hw0
      change minimalThreeScalarResidual a q 1=0 at hw1
      change minimalThreeScalarResidual a q 2=0 at hw2
      norm_num only [minimalThreeScalarResidual,minimalThreeWardSum,Fin.sum_univ_zero,
        Fin.sum_univ_one,Fin.sum_univ_two,Fin.val_zero,Fin.val_one,minimalThreeWardKernel,
        Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat] at hw0 hw1 hw2
      rw [minimalThreeNormOperator_expand]
      simp only [map_add,map_sub,add_mul,sub_mul,mul_assoc,coeff_C_mul,
        coeff_succ_X_mul,coeff_zero_X_mul,two_mul,
        show (3:PowerSeries ℂ)=1+1+1 by norm_num,
        show (4:PowerSeries ℂ)=1+1+1+1 by norm_num,one_mul,bsaEuler_coeff,coeff_mk]
      norm_num
      all_goals first | linear_combination hw1 | linear_combination hw2-3*hw1

end VOA.InverseDS.VirasoroVerma
