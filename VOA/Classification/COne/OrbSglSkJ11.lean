import VOA.Classification.COne.OrbSglSkew

/-! # OrbSgl: certified two-stage evaluation of `C(15,11) (u₍11₎a)₍-5₎a`, `a = J`
(machine-generated) -/

set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option Elab.async false
set_option linter.style.longLine false

namespace VOA.Classification.COne.OrbSgl

open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational OrbC2g OrbC2h OrbC2c PlusC2 PlusC2Eval PlusUnitary OrbC2e

def skP_J11_0 : SectorVector := [(1, []), (-1, [])]

def skP_J11_1 : SectorVector := [(-1, []), (1, [])]

def skY_J11 : SectorVector := [(1, []), (-1, [])]

def skQ_J11_0 : SectorVector := [(-1, []), (1, [])]

def skQ_J11_1 : SectorVector := [(1, []), (-1, [])]

def skQ_J11_2 : SectorVector := [(-1, []), (1, [])]

def skQ_J11_3 : SectorVector := [(1, []), (-1, [])]

def skQ_J11_4 : SectorVector := [(-1, []), (1, [])]

def skQ_J11_5 : SectorVector := [(1, []), (-1, [])]

def skQ_J11_6 : SectorVector := [(-1, []), (1, [])]

def skQ_J11_7 : SectorVector := [(1, []), (-1, [])]

def skQ_J11_8 : SectorVector := [(-1, []), (1, [])]

def skQ_J11_9 : SectorVector := [(1, []), (-1, [])]

def skPf_J11 : ℕ → SectorVector
  | 0 => skP_J11_0
  | 1 => skP_J11_1
  | _ => []

def skQf_J11 : ℕ → SectorVector
  | 0 => skQ_J11_0
  | 1 => skQ_J11_1
  | 2 => skQ_J11_2
  | 3 => skQ_J11_3
  | 4 => skQ_J11_4
  | 5 => skQ_J11_5
  | 6 => skQ_J11_6
  | 7 => skQ_J11_7
  | 8 => skQ_J11_8
  | 9 => skQ_J11_9
  | _ => []

set_option maxHeartbeats 4000000 in
theorem skP_J11_0_cert : VectorCertificate (OrbSgl.uTerm true 11 0) skP_J11_0 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_J11_1_cert : VectorCertificate (OrbSgl.uTerm true 11 1) skP_J11_1 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skY_J11_cert : VectorCertificate (OrbSgl.uSum 11 skPf_J11) skY_J11 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J11_0_cert : VectorCertificate (OrbSgl.vTerm true skY_J11 11 0) skQ_J11_0 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J11_1_cert : VectorCertificate (OrbSgl.vTerm true skY_J11 11 1) skQ_J11_1 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J11_2_cert : VectorCertificate (OrbSgl.vTerm true skY_J11 11 2) skQ_J11_2 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J11_3_cert : VectorCertificate (OrbSgl.vTerm true skY_J11 11 3) skQ_J11_3 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J11_4_cert : VectorCertificate (OrbSgl.vTerm true skY_J11 11 4) skQ_J11_4 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J11_5_cert : VectorCertificate (OrbSgl.vTerm true skY_J11 11 5) skQ_J11_5 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J11_6_cert : VectorCertificate (OrbSgl.vTerm true skY_J11 11 6) skQ_J11_6 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J11_7_cert : VectorCertificate (OrbSgl.vTerm true skY_J11 11 7) skQ_J11_7 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J11_8_cert : VectorCertificate (OrbSgl.vTerm true skY_J11 11 8) skQ_J11_8 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J11_9_cert : VectorCertificate (OrbSgl.vTerm true skY_J11 11 9) skQ_J11_9 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skT_J11_cert : VectorCertificate (OrbSgl.vSum 11 skQf_J11) termJ_11 := by decide +kernel

theorem skY_J11_value : evaluate skY_J11 =
    (V2m 4 four_ge_one).smul (weightNine : LatModuleGen (latP 4)) 11 (aVec true : LatModuleGen (latP 4)) := by
  rw [← vector_eq_of_certificate _ _ skY_J11_cert]
  apply evaluate_uSum true 11 (by norm_num)
  intro i hi
  interval_cases i
  · exact (vector_eq_of_certificate _ _ skP_J11_0_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_J11_1_cert).symm

/-- The certified value of `termJ_11`. -/
theorem sk_J11 : evaluate termJ_11 = ((Nat.choose 15 11 : ℕ) : ℂ) •
    (V2m 4 four_ge_one).smul ((V2m 4 four_ge_one).smul (weightNine : LatModuleGen (latP 4)) 11 (aVec true))
      (6 - (11 : ℕ)) (aVec true : LatModuleGen (latP 4)) := by
  rw [← vector_eq_of_certificate _ _ skT_J11_cert]
  apply evaluate_vSum true 11 (by norm_num) skY_J11 skY_J11_value
  intro j hj
  interval_cases j
  · exact (vector_eq_of_certificate _ _ skQ_J11_0_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J11_1_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J11_2_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J11_3_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J11_4_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J11_5_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J11_6_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J11_7_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J11_8_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J11_9_cert).symm

end VOA.Classification.COne.OrbSgl
