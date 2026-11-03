/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroMinimalThreeNormResponse

/-!
# The full seed-three state recurrence

Expanding the cubic descendant source leaves a scalar diagonal and a
single finite sum of negative modes on earlier coefficients. This gives
a concrete recurrence for actual states, beyond the
one-dimensional survival functional.
-/
namespace VOA.InverseDS.VirasoroVerma

/-- The cubic source's diagonal, written without its finite operator recursion. -/
noncomputable def threeStateDiagonal (h b t a : ℂ) (r : ℕ) : ℂ :=
  (h-3*b-a+(r:ℂ))-(t/2)*
    ((h-b-a+(r:ℂ)-2)*(2*b+a-h-(r:ℂ))+
      (2*b+a+1-h-(r:ℂ))*(h-b-a+(r:ℂ)))+
    (t^2/4)*(h-b-a+(r:ℂ))*(h-b-a+(r:ℂ)-1)*(h-b-a+(r:ℂ)-2)

/-- The off-diagonal multiplier of L_(j-r) acting on coefficient j.
It is affine in both the output and input indices. -/
noncomputable def threeStateCoefficient (h b t a : ℂ) (r j : ℕ) : ℂ :=
  ((r:ℂ)-(j:ℂ)-2)-(t/2)*(2*(h-b-a)+(r:ℂ)+(j:ℂ)-2)

/-- The explicit cubic diagonal equals the actual
source diagonal constructed earlier, so all established nonresonance results apply to it. -/
theorem threeStateDiagonal_eq (h b t a : ℂ) (r : ℕ) :
    threeStateDiagonal h b t a r=wardBSASourceDiagonal h b t 3 r 3 (a+3) := by
  simp only [wardBSASourceDiagonal,Fin.sum_univ_three]
  iterate 4
    norm_num [wardBSADiagonal,Fin.sum_univ_two,Fin.sum_univ_one,wardCreationDiagonal]
    try simp only [Fin.sum_univ_succ,Fin.sum_univ_zero]
  unfold threeStateDiagonal
  ring

/-- The full actual source consists of its scalar diagonal plus one
negative-mode sum. No positive Ward equation is assumed for the input. -/
theorem wardSourceAt_three_state_recursion (c h b t a : ℂ)
    (f : wardSequenceSpace c h) (r : ℕ) :
    (wardSourceAt c h b t a 3 f).val r =
      threeStateDiagonal h b t a r • f.val r+
      ∑ j : Fin r, threeStateCoefficient h b t a r j •
        vermaMode c h ((j:ℤ)-(r:ℤ)) (f.val j) := by
  have hd : wardNegative c h b 1=wardA c h b*wardB c h b-wardB c h b*wardA c h b := by
    simp [wardNegative,DescendantTower.tower,LieRing.of_associative_ring_bracket]
  change (wardBSASourceOperator c h b t 3 3 (wardFieldLift c h a f) (a+3)).val r = _
  rw [wardBSASourceOperator_three,hd]
  simp only [LinearMap.add_apply,LinearMap.sub_apply,LinearMap.smul_apply,Module.End.mul_apply,
    Pi.add_apply,Pi.sub_apply,Pi.smul_apply,Submodule.coe_add,Submodule.coe_sub,Submodule.coe_smul]
  simp only [wardA,wardB,wardShift,wardD1Map,wardD2Map,wardDescendant1,wardDescendant2,
    LinearMap.coe_mk,AddHom.coe_mk,wardSource]
  have h1 : a+3-1-2=a := by ring
  have h2 : a+3-2-1=a := by ring
  have h3 : a+3-1-1-1=a := by ring
  simp only [h1,h2,h3,wardFieldLift,LinearMap.coe_mk,AddHom.coe_mk,ite_true,
    map_smul,Finset.smul_sum,smul_add,smul_sub,smul_smul]
  have hs : (∑ j : Fin r, threeStateCoefficient h b t a r j •
      vermaMode c h ((j:ℤ)-(r:ℤ)) (f.val j)) =
      (∑ j : Fin r, (h-b-(a+3-1)+(r:ℂ)) • vermaMode c h ((j:ℤ)-(r:ℤ)) (f.val j))-
      (∑ j : Fin r, (h-b-a+(j:ℂ)) • vermaMode c h ((j:ℤ)-(r:ℤ)) (f.val j))-
      ((∑ j : Fin r, (t/2*(h-b-a+(j:ℂ))) • vermaMode c h ((j:ℤ)-(r:ℤ)) (f.val j))+
      (∑ j : Fin r, (t/2*(h-b-(a+3-1)+(r:ℂ))) • vermaMode c h ((j:ℤ)-(r:ℤ)) (f.val j))) := by
    rw [← Finset.sum_add_distrib,← Finset.sum_sub_distrib,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    unfold threeStateCoefficient
    module
  rw [hs]
  unfold threeStateDiagonal
  module

end VOA.InverseDS.VirasoroVerma
