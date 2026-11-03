/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroVacuumProjection
import VOA.Examples.VirasoroBSATopRecursion

/-!
# The actual fusion source under the vacuum survival functional

The scalar test is applied to actual states before quotienting. Its source
sum has only the term two levels earlier. This isolates the even-step
recursion relevant to the q=3 vacuum parameters.
-/
namespace VOA.InverseDS.VirasoroVerma

/-- In the finite negative-mode sum only L minus two survives. This is
an identity of actual Verma evaluations, not a proposed coordinate formula. -/
theorem vermaVacuumSurvival_source (c : ℂ) (f : ℕ → Verma c 0) (r : ℕ) :
    vermaVacuumSurvival c (wardSource c 0 f (r+2))=
      (2:ℂ)⁻¹*vermaVacuumSurvival c (f r) := by
  classical
  rw [wardSource,map_sum]
  have hh (j : Fin (r+2)) :
      vermaVacuumSurvival c (vermaMode c 0 ((j:ℤ)-((r+2:ℕ):ℤ)) (f j))=
      if (j:ℕ)=r then (2:ℂ)⁻¹*vermaVacuumSurvival c (f r) else 0 := by
    have he : (j:ℤ)-((r+2:ℕ):ℤ)=-((r+1-j.val:ℕ):ℤ)-1 := by omega
    rw [he,vermaVacuumSurvival_mode]
    by_cases hj : (j:ℕ)=r
    · simp [hj]
    · rw [if_neg (by omega),if_neg hj,zero_mul]
  simp only [hh]
  exact Finset.sum_eq_single (⟨r,by omega⟩ : Fin (r+2))
    (by intro b hb hne; rw [if_neg (by intro he; apply hne; exact Fin.ext he)])
    (by simp) |>.trans (by simp)

/-- The first global negative descendant remains diagonal under the
survival test, with its actual field-weight shift retained. -/
theorem vermaVacuumSurvival_A (c b a : ℂ) (f : ℂ → wardSequenceSpace c 0) (r : ℕ) :
    vermaVacuumSurvival c ((wardA c 0 b f a).val r)=
      (-b-(a-1)+(r:ℂ))*vermaVacuumSurvival c ((f (a-1)).val r) := by
  change vermaVacuumSurvival c ((0-b-(a-1)+(r:ℂ)) • (f (a-1)).val r)=_
  simp [map_smul,smul_eq_mul]

/-- The second descendant has precisely one off-diagonal contribution,
two coefficients earlier, with scalar one half. -/
theorem vermaVacuumSurvival_B (c b a : ℂ) (f : ℂ → wardSequenceSpace c 0) (r : ℕ) :
    vermaVacuumSurvival c ((wardB c 0 b f a).val (r+2))=
      (2:ℂ)⁻¹*vermaVacuumSurvival c ((f (a-2)).val r)+
      (2*b+(a-2)-((r+2:ℕ):ℂ))*vermaVacuumSurvival c ((f (a-2)).val (r+2)) := by
  change vermaVacuumSurvival c (wardSource c 0 (f (a-2)).val (r+2)+
    (2*b+(a-2)-0-((r+2:ℕ):ℂ)) • (f (a-2)).val (r+2))=_
  simp only [map_add,map_smul,smul_eq_mul,sub_zero,vermaVacuumSurvival_source]

/-- The commutator defining the third negative descendant cancels the
two-level-earlier term exactly. Only its scalar diagonal remains. -/
theorem vermaVacuumSurvival_D3 (c b a : ℂ) (f : ℂ → wardSequenceSpace c 0) (r : ℕ) :
    vermaVacuumSurvival c ((wardNegative c 0 b 1 f a).val (r+2))=
      -(3*b+a-3-((r+2:ℕ):ℂ))*vermaVacuumSurvival c ((f (a-3)).val (r+2)) := by
  have he : wardNegative c 0 b 1=wardA c 0 b*wardB c 0 b-wardB c 0 b*wardA c 0 b := by
    simp [wardNegative,DescendantTower.tower,LieRing.of_associative_ring_bracket]
  rw [he]
  simp only [LinearMap.sub_apply,Module.End.mul_apply,Pi.sub_apply,Submodule.coe_sub,
    Pi.sub_apply,map_sub,vermaVacuumSurvival_A,vermaVacuumSurvival_B]
  simp only [show a-1-2=a-3 by ring,show a-2-1=a-3 by ring]
  push_cast
  ring

/-- At seed index three, the actual undivided source is its explicit
cubic word operator. This expansion does not assume primary covariance. -/
theorem wardBSASourceOperator_three (c h b t : ℂ) :
    wardBSASourceOperator c h b t 3 3=wardNegative c h b 1-
      (t/2) • (wardB c h b*wardA c h b+wardA c h b*wardB c h b)+
      (t^2/4) • (wardA c h b*wardA c h b*wardA c h b) := by
  have h1 : wardTransportMode c h b (-1)=wardA c h b := rfl
  have h2 : wardTransportMode c h b (-2)=wardB c h b := rfl
  have h3 : wardTransportMode c h b (-3)=wardNegative c h b 1 := rfl
  simp only [wardBSASourceOperator,Fin.sum_univ_three]
  iterate 4
    norm_num [wardBSAOperator,Fin.sum_univ_two,Fin.sum_univ_one,h1,h2,h3]
    try simp only [Fin.sum_univ_succ,Fin.sum_univ_zero]
  simp only [show (LinearMap.id : Module.End ℂ (ℂ → wardSequenceSpace c h))=1 from rfl,mul_one]
  simp only [mul_add,smul_add,mul_smul_comm,smul_mul_assoc,smul_smul,mul_assoc]
  module

/-- The actual cubic source has a two-step scalar recurrence under vacuum
projection. Its off-diagonal is computed from the operators, not inferred
from a putative singular-vector formula. -/
theorem vermaVacuumSurvival_source_three (c b t a : ℂ)
    (f : ℂ → wardSequenceSpace c 0) (r : ℕ) :
    vermaVacuumSurvival c ((wardBSASourceOperator c 0 b t 3 3 f (a+3)).val (r+2))=
      wardBSASourceDiagonal 0 b t 3 (r+2) 3 (a+3)*
        vermaVacuumSurvival c ((f a).val (r+2))+
      (t/2)*(b+a+2-((r+2:ℕ):ℂ))*vermaVacuumSurvival c ((f a).val r) := by
  rw [wardBSASourceOperator_three]
  simp only [LinearMap.add_apply,LinearMap.sub_apply,LinearMap.smul_apply,
    Module.End.mul_apply,Pi.add_apply,Pi.sub_apply,Pi.smul_apply,Submodule.coe_add,
    Submodule.coe_sub,Submodule.coe_smul,map_add,map_sub,map_smul,smul_eq_mul,
    vermaVacuumSurvival_A,vermaVacuumSurvival_B,vermaVacuumSurvival_D3]
  simp only [show a+3-3=a by ring,show a+3-1-2=a by ring,
    show a+3-2-1=a by ring,show a+3-1-1-1=a by ring]
  iterate 4
    norm_num [wardBSASourceDiagonal,wardBSADiagonal,wardCreationDiagonal,
      Fin.sum_univ_three,Fin.sum_univ_two,Fin.sum_univ_one]
    try simp only [Fin.sum_univ_succ,Fin.sum_univ_zero]
  ring

/-- After placing a sequence at its input field weight, the same scalar
recurrence holds for the actual source operator on level sequences. -/
theorem vermaVacuumSurvival_sourceAt_three (c b t a : ℂ)
    (f : wardSequenceSpace c 0) (r : ℕ) :
    vermaVacuumSurvival c ((wardSourceAt c 0 b t a 3 f).val (r+2))=
      wardBSASourceDiagonal 0 b t 3 (r+2) 3 (a+3)*
        vermaVacuumSurvival c (f.val (r+2))+
      (t/2)*(b+a+2-((r+2:ℕ):ℂ))*vermaVacuumSurvival c (f.val r) := by
  have hh := vermaVacuumSurvival_source_three c b t a (wardFieldLift c 0 a f) r
  simpa [wardSourceAt,wardFieldLift] using hh

end VOA.InverseDS.VirasoroVerma
