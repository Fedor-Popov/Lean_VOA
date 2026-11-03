/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroVacuumFusionSource
import VOA.Examples.VirasoroFusionSecondWard

/-!
# The seed-three Ward defect at arbitrary central charge

Keep the seed parameter and field weight fixed while changing the actual
module charge. The second Ward identity then acquires a precisely computed
central error. Both input defects are retained. This does not assert that
the resulting response has a nonzero canonical pairing.
-/
set_option maxHeartbeats 800000

namespace VOA.InverseDS.VirasoroVerma

/-- The seed-three error on the first positive input defect is an explicit
quadratic operator. This identifies the finite error recursion at this seed. -/
theorem wardSecondSourceError_three (c h b t : ℂ) :
    wardSecondSourceError c h b t 3 3=
      (9*t^2/4) • (wardA c h b*wardA c h b)-(3*t) • wardB c h b := by
  have h1 : wardTransportMode c h b (-1)=wardA c h b := rfl
  have h2 : wardTransportMode c h b (-2)=wardB c h b := rfl
  have h3 : wardTransportMode c h b (-3)=wardNegative c h b 1 := rfl
  simp only [wardSecondSourceError,Fin.sum_univ_three]
  iterate 5
    norm_num [wardSecondError,wardBSAOperator,Fin.sum_univ_two,Fin.sum_univ_one,h1,h2,h3]
    try simp only [Fin.sum_univ_succ,Fin.sum_univ_zero]
  simp only [show (LinearMap.id : Module.End ℂ (ℂ → wardSequenceSpace c h))=1 from rfl,mul_one,
    mul_add,smul_add,mul_smul_comm,smul_mul_assoc,smul_smul,mul_assoc]
  module

/-- The full second commutator is put in normal order with the first
positive defect and weight operator at the right. The charge appears
explicitly, without assuming the seed's special central value. -/
theorem wardSource_three_commutator (c h b t : ℂ) :
    ⁅wardQ c h b,wardBSASourceOperator c h b t 3 3⁆=
      wardSecondSourceError c h b t 3 3*wardP c h b+
      (9*t^2/2-4*t) • (wardA c h b*wardWeight c h)+
      (5-13*t/2-t*c/2+3*t^2/2) • wardA c h b := by
  let A := wardA c h b
  let B := wardB c h b
  let P := wardP c h b
  let W := wardWeight c h
  have hPA : P*A=A*P+(2:ℂ) • W := by
    have hh := wardP_A c h b
    rw [LieRing.of_associative_ring_bracket] at hh
    change P*A-A*P=(2:ℂ) • W at hh
    rw [← hh]; abel
  have hPB : P*B=B*P+(3:ℂ) • A := by
    have hh := wardP_B c h b
    rw [LieRing.of_associative_ring_bracket] at hh
    change P*B-B*P=(3:ℂ) • A at hh
    rw [← hh]; abel
  have hWA : W*A=A*W+A := by
    have hh := wardWeight_A c h b
    rw [LieRing.of_associative_ring_bracket] at hh
    change W*A-A*W=A at hh
    exact (sub_eq_iff_eq_add.mp hh).trans (add_comm _ _)
  have hm (X Y : Module.End ℂ (ℂ → wardSequenceSpace c h)) :
      ⁅wardQ c h b,X*Y⁆=⁅wardQ c h b,X⁆*Y+X*⁅wardQ c h b,Y⁆ := by
    apply LinearMap.ext
    intro v
    simp only [LieRing.of_associative_ring_bracket,LinearMap.sub_apply,LinearMap.add_apply,
      Module.End.mul_apply,map_sub]
    abel
  have hl (X Y Z : Module.End ℂ (ℂ → wardSequenceSpace c h)) (z w : ℂ) :
      ⁅wardQ c h b,X-z • Y+w • Z⁆=
        ⁅wardQ c h b,X⁆-z • ⁅wardQ c h b,Y⁆+w • ⁅wardQ c h b,Z⁆ := by
    apply LinearMap.ext
    intro v
    simp only [LieRing.of_associative_ring_bracket,LinearMap.sub_apply,LinearMap.add_apply,
      LinearMap.smul_apply,Module.End.mul_apply,map_sub,map_add,map_smul]
    module
  have ha (X Y : Module.End ℂ (ℂ → wardSequenceSpace c h)) :
      ⁅wardQ c h b,X+Y⁆=⁅wardQ c h b,X⁆+⁅wardQ c h b,Y⁆ := by
    apply LinearMap.ext
    intro v
    simp only [LieRing.of_associative_ring_bracket,LinearMap.sub_apply,LinearMap.add_apply,
      Module.End.mul_apply,map_add]
    abel
  rw [wardBSASourceOperator_three,hl,ha,hm,hm,hm,hm,
    wardQ_negative_one,wardQ_A,wardQ_B,wardSecondSourceError_three]
  change _ = ((9*t^2/4) • (A*A)-(3*t) • B)*P+
    (9*t^2/2-4*t) • (A*W)+(5-13*t/2-t*c/2+3*t^2/2) • A
  change (5:ℂ) • A-(t/2) • (((4:ℂ) • W+(c/2) • LinearMap.id)*A+B*((3:ℂ) • P)+
    (((3:ℂ) • P)*B+A*((4:ℂ) • W+(c/2) • LinearMap.id)))+
    (t^2/4) • ((((3:ℂ) • P)*A+A*((3:ℂ) • P))*A+(A*A)*((3:ℂ) • P))=_
  simp only [show (LinearMap.id : Module.End ℂ (ℂ → wardSequenceSpace c h))=1 from rfl,
    mul_add,add_mul,sub_mul,mul_smul_comm,smul_mul_assoc,one_mul,mul_one,smul_add,smul_smul]
  rw [hPA,hPB,hWA]
  simp only [add_mul,mul_add,smul_mul_assoc,mul_smul_comm,smul_add,smul_smul,mul_assoc]
  rw [hPA]
  simp only [mul_add,mul_smul_comm,smul_add,smul_smul,mul_assoc,hWA]
  apply LinearMap.ext
  intro v
  simp only [LinearMap.sub_apply,LinearMap.add_apply,LinearMap.smul_apply,
    Module.End.mul_apply]
  module

/-- On the correct field-weight component, the full actual second Ward
identity has precisely the charge error -(t/2)(c-c(t))D1. No primary
input equation or special-charge hypothesis is assumed. -/
theorem wardSource_three_charge_defect (c h b t : ℂ) (ht : t ≠ 0)
    (f : ℂ → wardSequenceSpace c h)
    (hw : wardWeight c h f = vermaBSAWeight 3 t • f) :
    wardQ c h b (wardBSASourceOperator c h b t 3 3 f)=
      wardBSASourceOperator c h b t 3 3 (wardQ c h b f)+
      wardSecondSourceError c h b t 3 3 (wardP c h b f)-
      ((t/2)*(c-vermaBSACharge t)) • wardA c h b f := by
  have hh := congrArg (fun T : Module.End ℂ (ℂ → wardSequenceSpace c h) => T f)
    (wardSource_three_commutator c h b t)
  simp only [LieRing.of_associative_ring_bracket,LinearMap.sub_apply,LinearMap.add_apply,
    LinearMap.smul_apply,Module.End.mul_apply,hw,map_smul,smul_smul] at hh
  have he : (9*t^2/2-4*t)*vermaBSAWeight 3 t+(5-13*t/2-t*c/2+3*t^2/2)=
      -(t/2)*(c-vermaBSACharge t) := by
    unfold vermaBSAWeight vermaBSACharge
    norm_num
    field_simp
    ring
  rw [add_assoc,← add_smul,he] at hh
  rw [neg_mul,neg_smul] at hh
  rw [sub_eq_iff_eq_add] at hh
  rw [hh]
  module

/-- Evaluating the arbitrary-charge identity gives the actual level-sequence
Ward equation, including its explicit central error and both input defects.
This is the equation needed for a charge response of the triangular kernel. -/
theorem wardSourceAt_three_charge_defect (c h b t : ℂ) (ht : t ≠ 0)
    (f : wardSequenceSpace c h) :
    wardP2Map c h b (vermaBSAWeight 3 t+3)
      (wardSourceAt c h b t (vermaBSAWeight 3 t) 3 f) =
    wardSourceAt c h b t (vermaBSAWeight 3 t-2) 3
      (wardP2Map c h b (vermaBSAWeight 3 t) f)+
    wardSourceErrorAt c h b t (vermaBSAWeight 3 t) 3 f-
      ((t/2)*(c-vermaBSACharge t)) • wardD1Map c h b (vermaBSAWeight 3 t) f := by
  have hh := wardSource_three_charge_defect c h b t ht
    (wardFieldLift c h (vermaBSAWeight 3 t) f)
    (wardFieldLift_weight c h (vermaBSAWeight 3 t) f)
  rw [wardFieldLift_first,wardFieldLift_second] at hh
  have he := congrArg (fun F : ℂ → wardSequenceSpace c h =>
    F (vermaBSAWeight 3 t+3-2)) hh
  have ha : vermaBSAWeight 3 t+3-2=(vermaBSAWeight 3 t-2)+3 := by ring
  have hb : vermaBSAWeight 3 t+3-2-1=vermaBSAWeight 3 t := by ring
  change wardP2Map c h b ((vermaBSAWeight 3 t+3-2)-(-2))
    (wardBSASourceOperator c h b t 3 3
      (wardFieldLift c h (vermaBSAWeight 3 t) f)
      ((vermaBSAWeight 3 t+3-2)-(-2))) =
    wardBSASourceOperator c h b t 3 3
      (wardFieldLift c h (vermaBSAWeight 3 t-2)
        (wardP2Map c h b (vermaBSAWeight 3 t) f))
      (vermaBSAWeight 3 t+3-2)+
    wardSourceErrorAt c h b t (vermaBSAWeight 3 t) 3 f-
    ((t/2)*(c-vermaBSACharge t)) •
      wardD1Map c h b (vermaBSAWeight 3 t+3-2-1)
        (wardFieldLift c h (vermaBSAWeight 3 t) f
          (vermaBSAWeight 3 t+3-2-1)) at he
  simp only [sub_neg_eq_add,sub_add_cancel,hb,wardFieldLift,LinearMap.coe_mk,
    AddHom.coe_mk,ite_true] at he
  rw [ha] at he
  exact he

end VOA.InverseDS.VirasoroVerma
