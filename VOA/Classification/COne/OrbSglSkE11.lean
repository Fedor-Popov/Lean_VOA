import VOA.Classification.COne.OrbSglSkew

/-! # OrbSgl: certified two-stage evaluation of `C(15,11) (u₍11₎a)₍-5₎a`, `a = E`
(machine-generated) -/

set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option Elab.async false
set_option linter.style.longLine false

namespace VOA.Classification.COne.OrbSgl

open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational OrbC2g OrbC2h OrbC2c PlusC2 PlusC2Eval PlusUnitary OrbC2e

def skP_E11_0 : SectorVector := [(0, []), (-2, []), (2, [])]

def skP_E11_1 : SectorVector := [(2, []), (-2, []), (0, [])]

def skY_E11 : SectorVector := [(0, []), (-2, []), (2, [])]

def skQ_E11_0 : SectorVector := [(1, []), (-3, []), (-1, []), (3, [])]

def skQ_E11_1 : SectorVector := [(3, []), (-1, []), (-3, []), (1, [])]

def skQ_E11_2 : SectorVector := [(1, []), (-3, []), (-1, []), (3, [])]

def skQ_E11_3 : SectorVector := [(3, []), (-1, []), (-3, []), (1, [])]

def skQ_E11_4 : SectorVector := [(1, []), (-3, []), (-1, []), (3, [])]

def skQ_E11_5 : SectorVector := [(3, []), (-1, []), (-3, []), (1, [])]

def skQ_E11_6 : SectorVector := [(1, []), (-3, []), (-1, []), (3, [])]

def skQ_E11_7 : SectorVector := [(3, []), (-1, []), (-3, []), (1, [])]

def skQ_E11_8 : SectorVector := [(1, []), (-3, []), (-1, []), (3, [])]

def skQ_E11_9 : SectorVector := [(3, []), (-1, []), (-3, []), (1, [])]

def skPf_E11 : ℕ → SectorVector
  | 0 => skP_E11_0
  | 1 => skP_E11_1
  | _ => []

def skQf_E11 : ℕ → SectorVector
  | 0 => skQ_E11_0
  | 1 => skQ_E11_1
  | 2 => skQ_E11_2
  | 3 => skQ_E11_3
  | 4 => skQ_E11_4
  | 5 => skQ_E11_5
  | 6 => skQ_E11_6
  | 7 => skQ_E11_7
  | 8 => skQ_E11_8
  | 9 => skQ_E11_9
  | _ => []

set_option maxHeartbeats 4000000 in
theorem skP_E11_0_cert : VectorCertificate (OrbSgl.uTerm false 11 0) skP_E11_0 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_E11_1_cert : VectorCertificate (OrbSgl.uTerm false 11 1) skP_E11_1 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skY_E11_cert : VectorCertificate (OrbSgl.uSum 11 skPf_E11) skY_E11 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E11_0_cert : VectorCertificate (OrbSgl.vTerm false skY_E11 11 0) skQ_E11_0 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E11_1_cert : VectorCertificate (OrbSgl.vTerm false skY_E11 11 1) skQ_E11_1 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E11_2_cert : VectorCertificate (OrbSgl.vTerm false skY_E11 11 2) skQ_E11_2 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E11_3_cert : VectorCertificate (OrbSgl.vTerm false skY_E11 11 3) skQ_E11_3 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E11_4_cert : VectorCertificate (OrbSgl.vTerm false skY_E11 11 4) skQ_E11_4 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E11_5_cert : VectorCertificate (OrbSgl.vTerm false skY_E11 11 5) skQ_E11_5 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E11_6_cert : VectorCertificate (OrbSgl.vTerm false skY_E11 11 6) skQ_E11_6 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E11_7_cert : VectorCertificate (OrbSgl.vTerm false skY_E11 11 7) skQ_E11_7 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E11_8_cert : VectorCertificate (OrbSgl.vTerm false skY_E11 11 8) skQ_E11_8 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E11_9_cert : VectorCertificate (OrbSgl.vTerm false skY_E11 11 9) skQ_E11_9 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skT_E11_cert : VectorCertificate (OrbSgl.vSum 11 skQf_E11) termE_11 := by decide +kernel

theorem skY_E11_value : evaluate skY_E11 =
    (V2m 4 four_ge_one).smul (weightNine : LatModuleGen (latP 4)) 11 (aVec false : LatModuleGen (latP 4)) := by
  rw [← vector_eq_of_certificate _ _ skY_E11_cert]
  apply evaluate_uSum false 11 (by norm_num)
  intro i hi
  interval_cases i
  · exact (vector_eq_of_certificate _ _ skP_E11_0_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_E11_1_cert).symm

/-- The certified value of `termE_11`. -/
theorem sk_E11 : evaluate termE_11 = ((Nat.choose 15 11 : ℕ) : ℂ) •
    (V2m 4 four_ge_one).smul ((V2m 4 four_ge_one).smul (weightNine : LatModuleGen (latP 4)) 11 (aVec false))
      (6 - (11 : ℕ)) (aVec false : LatModuleGen (latP 4)) := by
  rw [← vector_eq_of_certificate _ _ skT_E11_cert]
  apply evaluate_vSum false 11 (by norm_num) skY_E11 skY_E11_value
  intro j hj
  interval_cases j
  · exact (vector_eq_of_certificate _ _ skQ_E11_0_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_E11_1_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_E11_2_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_E11_3_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_E11_4_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_E11_5_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_E11_6_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_E11_7_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_E11_8_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_E11_9_cert).symm

end VOA.Classification.COne.OrbSgl
