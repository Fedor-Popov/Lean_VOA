import VOA.Classification.COne.OrbSglSkew

/-! # OrbSgl: certified two-stage evaluation of `C(15,12) (u₍12₎a)₍-6₎a`, `a = E`
(machine-generated) -/

set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option Elab.async false
set_option linter.style.longLine false

namespace VOA.Classification.COne.OrbSgl

open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational OrbC2g OrbC2h OrbC2c PlusC2 PlusC2Eval PlusUnitary OrbC2e

def skP_E12_0 : SectorVector := [(0, []), (-2, []), (2, [])]

def skY_E12 : SectorVector := [(2, []), (-2, []), (0, [])]

def skQ_E12_0 : SectorVector := [(-1, []), (-3, []), (1, []), (3, [])]

def skQ_E12_1 : SectorVector := [(3, []), (1, []), (-3, []), (-1, [])]

def skQ_E12_2 : SectorVector := [(-1, []), (-3, []), (1, []), (3, [])]

def skQ_E12_3 : SectorVector := [(3, []), (1, []), (-3, []), (-1, [])]

def skQ_E12_4 : SectorVector := [(-1, []), (-3, []), (1, []), (3, [])]

def skQ_E12_5 : SectorVector := [(3, []), (1, []), (-3, []), (-1, [])]

def skQ_E12_6 : SectorVector := [(-1, []), (-3, []), (1, []), (3, [])]

def skQ_E12_7 : SectorVector := [(3, []), (1, []), (-3, []), (-1, [])]

def skQ_E12_8 : SectorVector := [(-1, []), (-3, []), (1, []), (3, [])]

def skQ_E12_9 : SectorVector := [(3, []), (1, []), (-3, []), (-1, [])]

def skPf_E12 : ℕ → SectorVector
  | 0 => skP_E12_0
  | _ => []

def skQf_E12 : ℕ → SectorVector
  | 0 => skQ_E12_0
  | 1 => skQ_E12_1
  | 2 => skQ_E12_2
  | 3 => skQ_E12_3
  | 4 => skQ_E12_4
  | 5 => skQ_E12_5
  | 6 => skQ_E12_6
  | 7 => skQ_E12_7
  | 8 => skQ_E12_8
  | 9 => skQ_E12_9
  | _ => []

set_option maxHeartbeats 4000000 in
theorem skP_E12_0_cert : VectorCertificate (OrbSgl.uTerm false 12 0) skP_E12_0 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skY_E12_cert : VectorCertificate (OrbSgl.uSum 12 skPf_E12) skY_E12 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E12_0_cert : VectorCertificate (OrbSgl.vTerm false skY_E12 12 0) skQ_E12_0 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E12_1_cert : VectorCertificate (OrbSgl.vTerm false skY_E12 12 1) skQ_E12_1 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E12_2_cert : VectorCertificate (OrbSgl.vTerm false skY_E12 12 2) skQ_E12_2 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E12_3_cert : VectorCertificate (OrbSgl.vTerm false skY_E12 12 3) skQ_E12_3 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E12_4_cert : VectorCertificate (OrbSgl.vTerm false skY_E12 12 4) skQ_E12_4 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E12_5_cert : VectorCertificate (OrbSgl.vTerm false skY_E12 12 5) skQ_E12_5 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E12_6_cert : VectorCertificate (OrbSgl.vTerm false skY_E12 12 6) skQ_E12_6 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E12_7_cert : VectorCertificate (OrbSgl.vTerm false skY_E12 12 7) skQ_E12_7 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E12_8_cert : VectorCertificate (OrbSgl.vTerm false skY_E12 12 8) skQ_E12_8 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E12_9_cert : VectorCertificate (OrbSgl.vTerm false skY_E12 12 9) skQ_E12_9 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skT_E12_cert : VectorCertificate (OrbSgl.vSum 12 skQf_E12) termE_12 := by decide +kernel

theorem skY_E12_value : evaluate skY_E12 =
    (V2m 4 four_ge_one).smul (weightNine : LatModuleGen (latP 4)) 12 (aVec false : LatModuleGen (latP 4)) := by
  rw [← vector_eq_of_certificate _ _ skY_E12_cert]
  apply evaluate_uSum false 12 (by norm_num)
  intro i hi
  interval_cases i
  · exact (vector_eq_of_certificate _ _ skP_E12_0_cert).symm

/-- The certified value of `termE_12`. -/
theorem sk_E12 : evaluate termE_12 = ((Nat.choose 15 12 : ℕ) : ℂ) •
    (V2m 4 four_ge_one).smul ((V2m 4 four_ge_one).smul (weightNine : LatModuleGen (latP 4)) 12 (aVec false))
      (6 - (12 : ℕ)) (aVec false : LatModuleGen (latP 4)) := by
  rw [← vector_eq_of_certificate _ _ skT_E12_cert]
  apply evaluate_vSum false 12 (by norm_num) skY_E12 skY_E12_value
  intro j hj
  interval_cases j
  · exact (vector_eq_of_certificate _ _ skQ_E12_0_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_E12_1_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_E12_2_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_E12_3_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_E12_4_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_E12_5_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_E12_6_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_E12_7_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_E12_8_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_E12_9_cert).symm

end VOA.Classification.COne.OrbSgl
