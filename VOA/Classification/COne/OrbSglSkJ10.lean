import VOA.Classification.COne.OrbSglSkew

/-! # OrbSgl: certified two-stage evaluation of `C(15,10) (u₍10₎a)₍-4₎a`, `a = J`
(machine-generated) -/

set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option Elab.async false
set_option linter.style.longLine false

namespace VOA.Classification.COne.OrbSgl

open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational OrbC2g OrbC2h OrbC2c PlusC2 PlusC2Eval PlusUnitary OrbC2e

def skP_J10_0 : SectorVector := [(1, []), (-1, [])]

def skP_J10_1 : SectorVector := [(-1, []), (1, [])]

def skP_J10_2 : SectorVector := [(1, []), (-1, [])]

def skY_J10 : SectorVector := [(-1, []), (1, [])]

def skQ_J10_0 : SectorVector := [(1, []), (-1, [])]

def skQ_J10_1 : SectorVector := [(-1, []), (1, [])]

def skQ_J10_2 : SectorVector := [(1, []), (-1, [])]

def skQ_J10_3 : SectorVector := [(-1, []), (1, [])]

def skQ_J10_4 : SectorVector := [(1, []), (-1, [])]

def skQ_J10_5 : SectorVector := [(-1, []), (1, [])]

def skQ_J10_6 : SectorVector := [(1, []), (-1, [])]

def skQ_J10_7 : SectorVector := [(-1, []), (1, [])]

def skQ_J10_8 : SectorVector := [(1, []), (-1, [])]

def skQ_J10_9 : SectorVector := [(-1, []), (1, [])]

def skPf_J10 : ℕ → SectorVector
  | 0 => skP_J10_0
  | 1 => skP_J10_1
  | 2 => skP_J10_2
  | _ => []

def skQf_J10 : ℕ → SectorVector
  | 0 => skQ_J10_0
  | 1 => skQ_J10_1
  | 2 => skQ_J10_2
  | 3 => skQ_J10_3
  | 4 => skQ_J10_4
  | 5 => skQ_J10_5
  | 6 => skQ_J10_6
  | 7 => skQ_J10_7
  | 8 => skQ_J10_8
  | 9 => skQ_J10_9
  | _ => []

set_option maxHeartbeats 4000000 in
theorem skP_J10_0_cert : VectorCertificate (OrbSgl.uTerm true 10 0) skP_J10_0 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_J10_1_cert : VectorCertificate (OrbSgl.uTerm true 10 1) skP_J10_1 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_J10_2_cert : VectorCertificate (OrbSgl.uTerm true 10 2) skP_J10_2 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skY_J10_cert : VectorCertificate (OrbSgl.uSum 10 skPf_J10) skY_J10 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J10_0_cert : VectorCertificate (OrbSgl.vTerm true skY_J10 10 0) skQ_J10_0 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J10_1_cert : VectorCertificate (OrbSgl.vTerm true skY_J10 10 1) skQ_J10_1 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J10_2_cert : VectorCertificate (OrbSgl.vTerm true skY_J10 10 2) skQ_J10_2 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J10_3_cert : VectorCertificate (OrbSgl.vTerm true skY_J10 10 3) skQ_J10_3 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J10_4_cert : VectorCertificate (OrbSgl.vTerm true skY_J10 10 4) skQ_J10_4 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J10_5_cert : VectorCertificate (OrbSgl.vTerm true skY_J10 10 5) skQ_J10_5 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J10_6_cert : VectorCertificate (OrbSgl.vTerm true skY_J10 10 6) skQ_J10_6 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J10_7_cert : VectorCertificate (OrbSgl.vTerm true skY_J10 10 7) skQ_J10_7 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J10_8_cert : VectorCertificate (OrbSgl.vTerm true skY_J10 10 8) skQ_J10_8 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J10_9_cert : VectorCertificate (OrbSgl.vTerm true skY_J10 10 9) skQ_J10_9 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skT_J10_cert : VectorCertificate (OrbSgl.vSum 10 skQf_J10) termJ_10 := by decide +kernel

theorem skY_J10_value : evaluate skY_J10 =
    (V2m 4 four_ge_one).smul (weightNine : LatModuleGen (latP 4)) 10 (aVec true : LatModuleGen (latP 4)) := by
  rw [← vector_eq_of_certificate _ _ skY_J10_cert]
  apply evaluate_uSum true 10 (by norm_num)
  intro i hi
  interval_cases i
  · exact (vector_eq_of_certificate _ _ skP_J10_0_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_J10_1_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_J10_2_cert).symm

/-- The certified value of `termJ_10`. -/
theorem sk_J10 : evaluate termJ_10 = ((Nat.choose 15 10 : ℕ) : ℂ) •
    (V2m 4 four_ge_one).smul ((V2m 4 four_ge_one).smul (weightNine : LatModuleGen (latP 4)) 10 (aVec true))
      (6 - (10 : ℕ)) (aVec true : LatModuleGen (latP 4)) := by
  rw [← vector_eq_of_certificate _ _ skT_J10_cert]
  apply evaluate_vSum true 10 (by norm_num) skY_J10 skY_J10_value
  intro j hj
  interval_cases j
  · exact (vector_eq_of_certificate _ _ skQ_J10_0_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J10_1_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J10_2_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J10_3_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J10_4_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J10_5_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J10_6_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J10_7_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J10_8_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J10_9_cert).symm

end VOA.Classification.COne.OrbSgl
