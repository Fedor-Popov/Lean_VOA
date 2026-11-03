import VOA.Classification.COne.OrbSglSkew

/-! # OrbSgl: certified two-stage evaluation of `C(15,12) (u₍12₎a)₍-6₎a`, `a = J`
(machine-generated) -/

set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option Elab.async false
set_option linter.style.longLine false

namespace VOA.Classification.COne.OrbSgl

open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational OrbC2g OrbC2h OrbC2c PlusC2 PlusC2Eval PlusUnitary OrbC2e

def skP_J12_0 : SectorVector := [(1, []), (-1, [])]

def skY_J12 : SectorVector := [(-1, []), (1, [])]

def skQ_J12_0 : SectorVector := [(1, []), (-1, [])]

def skQ_J12_1 : SectorVector := [(-1, []), (1, [])]

def skQ_J12_2 : SectorVector := [(1, []), (-1, [])]

def skQ_J12_3 : SectorVector := [(-1, []), (1, [])]

def skQ_J12_4 : SectorVector := [(1, []), (-1, [])]

def skQ_J12_5 : SectorVector := [(-1, []), (1, [])]

def skQ_J12_6 : SectorVector := [(1, []), (-1, [])]

def skQ_J12_7 : SectorVector := [(-1, []), (1, [])]

def skQ_J12_8 : SectorVector := [(1, []), (-1, [])]

def skQ_J12_9 : SectorVector := [(-1, []), (1, [])]

def skPf_J12 : ℕ → SectorVector
  | 0 => skP_J12_0
  | _ => []

def skQf_J12 : ℕ → SectorVector
  | 0 => skQ_J12_0
  | 1 => skQ_J12_1
  | 2 => skQ_J12_2
  | 3 => skQ_J12_3
  | 4 => skQ_J12_4
  | 5 => skQ_J12_5
  | 6 => skQ_J12_6
  | 7 => skQ_J12_7
  | 8 => skQ_J12_8
  | 9 => skQ_J12_9
  | _ => []

set_option maxHeartbeats 4000000 in
theorem skP_J12_0_cert : VectorCertificate (OrbSgl.uTerm true 12 0) skP_J12_0 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skY_J12_cert : VectorCertificate (OrbSgl.uSum 12 skPf_J12) skY_J12 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J12_0_cert : VectorCertificate (OrbSgl.vTerm true skY_J12 12 0) skQ_J12_0 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J12_1_cert : VectorCertificate (OrbSgl.vTerm true skY_J12 12 1) skQ_J12_1 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J12_2_cert : VectorCertificate (OrbSgl.vTerm true skY_J12 12 2) skQ_J12_2 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J12_3_cert : VectorCertificate (OrbSgl.vTerm true skY_J12 12 3) skQ_J12_3 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J12_4_cert : VectorCertificate (OrbSgl.vTerm true skY_J12 12 4) skQ_J12_4 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J12_5_cert : VectorCertificate (OrbSgl.vTerm true skY_J12 12 5) skQ_J12_5 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J12_6_cert : VectorCertificate (OrbSgl.vTerm true skY_J12 12 6) skQ_J12_6 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J12_7_cert : VectorCertificate (OrbSgl.vTerm true skY_J12 12 7) skQ_J12_7 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J12_8_cert : VectorCertificate (OrbSgl.vTerm true skY_J12 12 8) skQ_J12_8 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J12_9_cert : VectorCertificate (OrbSgl.vTerm true skY_J12 12 9) skQ_J12_9 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skT_J12_cert : VectorCertificate (OrbSgl.vSum 12 skQf_J12) termJ_12 := by decide +kernel

theorem skY_J12_value : evaluate skY_J12 =
    (V2m 4 four_ge_one).smul (weightNine : LatModuleGen (latP 4)) 12 (aVec true : LatModuleGen (latP 4)) := by
  rw [← vector_eq_of_certificate _ _ skY_J12_cert]
  apply evaluate_uSum true 12 (by norm_num)
  intro i hi
  interval_cases i
  · exact (vector_eq_of_certificate _ _ skP_J12_0_cert).symm

/-- The certified value of `termJ_12`. -/
theorem sk_J12 : evaluate termJ_12 = ((Nat.choose 15 12 : ℕ) : ℂ) •
    (V2m 4 four_ge_one).smul ((V2m 4 four_ge_one).smul (weightNine : LatModuleGen (latP 4)) 12 (aVec true))
      (6 - (12 : ℕ)) (aVec true : LatModuleGen (latP 4)) := by
  rw [← vector_eq_of_certificate _ _ skT_J12_cert]
  apply evaluate_vSum true 12 (by norm_num) skY_J12 skY_J12_value
  intro j hj
  interval_cases j
  · exact (vector_eq_of_certificate _ _ skQ_J12_0_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J12_1_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J12_2_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J12_3_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J12_4_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J12_5_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J12_6_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J12_7_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J12_8_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J12_9_cert).symm

end VOA.Classification.COne.OrbSgl
