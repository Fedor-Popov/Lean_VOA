import VOA.Classification.COne.OrbSglSkew

/-! # OrbSgl: certified two-stage evaluation of `C(15,6) (u₍6₎a)₍0₎a`, `a = J`
(machine-generated) -/

set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option Elab.async false
set_option linter.style.longLine false

namespace VOA.Classification.COne.OrbSgl

open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational OrbC2g OrbC2h OrbC2c PlusC2 PlusC2Eval PlusUnitary OrbC2e

def skP_J6_0 : SectorVector := [(1, [(2160, [0, 2]), (-2160, [1, 1])]), (-1, [(-2160, [0, 2]), (-2160, [1, 1])])]

def skP_J6_1 : SectorVector := [(-1, [(1350, [0, 2]), (-10800, [1, 1])]), (1, [(-1350, [0, 2]), (-10800, [1, 1])])]

def skP_J6_2 : SectorVector := [(1, [(10800, [0, 2]), (86400, [1, 1])]), (-1, [(-10800, [0, 2]), (86400, [1, 1])])]

def skP_J6_3 : SectorVector := [(-1, []), (1, [])]

def skP_J6_4 : SectorVector := [(1, []), (-1, [])]

def skP_J6_5 : SectorVector := [(-1, []), (1, [])]

def skP_J6_6 : SectorVector := [(1, []), (-1, [])]

def skY_J6 : SectorVector := [(-1, [(8910, [0, 2]), (-51840, [1, 1])]), (1, [(-8910, [0, 2]), (-51840, [1, 1])])]

def skQ_J6_0 : SectorVector := [(1,
  [(-207360, [0, 1, 1, 1, 1, 1]),
   (-3842640, [0, 1, 1, 3]),
   (-2313360, [0, 1, 2, 2]),
   (-1885680, [0, 5]),
   (-6505920, [1, 1, 1, 2]),
   (-11508480, [1, 4]),
   (-6233760, [2, 3])]),
 (-1,
  [(207360, [0, 1, 1, 1, 1, 1]),
   (3842640, [0, 1, 1, 3]),
   (2313360, [0, 1, 2, 2]),
   (1885680, [0, 5]),
   (-6505920, [1, 1, 1, 2]),
   (-11508480, [1, 4]),
   (-6233760, [2, 3])])]

def skQ_J6_1 : SectorVector := [(-1,
  [(2903040, [0, 1, 1, 1, 1, 1]),
   (21604320, [0, 1, 1, 3]),
   (13316400, [0, 1, 2, 2]),
   (8611920, [0, 5]),
   (-47848320, [1, 1, 1, 2]),
   (-54859680, [1, 4]),
   (-29574720, [2, 3])]),
 (1,
  [(-2903040, [0, 1, 1, 1, 1, 1]),
   (-21604320, [0, 1, 1, 3]),
   (-13316400, [0, 1, 2, 2]),
   (-8611920, [0, 5]),
   (-47848320, [1, 1, 1, 2]),
   (-54859680, [1, 4]),
   (-29574720, [2, 3])])]

def skQ_J6_2 : SectorVector := [(1,
  [(-22965120, [0, 1, 1, 1, 1, 1]),
   (-98353440, [0, 1, 1, 3]),
   (-63763200, [0, 1, 2, 2]),
   (-28615680, [0, 5]),
   (-284860800, [1, 1, 1, 2]),
   (-207541440, [1, 4]),
   (-112155840, [2, 3])]),
 (-1,
  [(22965120, [0, 1, 1, 1, 1, 1]),
   (98353440, [0, 1, 1, 3]),
   (63763200, [0, 1, 2, 2]),
   (28615680, [0, 5]),
   (-284860800, [1, 1, 1, 2]),
   (-207541440, [1, 4]),
   (-112155840, [2, 3])])]

def skQ_J6_3 : SectorVector := [(-1,
  [(118195200, [0, 1, 1, 1, 1, 1]),
   (356374080, [0, 1, 1, 3]),
   (252059040, [0, 1, 2, 2]),
   (74766240, [0, 5]),
   (-1263133440, [1, 1, 1, 2]),
   (-625890240, [1, 4]),
   (-376669440, [2, 3])]),
 (1,
  [(-118195200, [0, 1, 1, 1, 1, 1]),
   (-356374080, [0, 1, 1, 3]),
   (-252059040, [0, 1, 2, 2]),
   (-74766240, [0, 5]),
   (-1263133440, [1, 1, 1, 2]),
   (-625890240, [1, 4]),
   (-376669440, [2, 3])])]

def skQ_J6_4 : SectorVector := [(1,
  [(-374492160, [0, 1, 1, 1, 1, 1]),
   (-936230400, [0, 1, 1, 3]),
   (-702172800, [0, 1, 2, 2]),
   (-140434560, [0, 5]),
   (-3744921600, [1, 1, 1, 2]),
   (-1404345600, [1, 4]),
   (-936230400, [2, 3])]),
 (-1,
  [(374492160, [0, 1, 1, 1, 1, 1]),
   (936230400, [0, 1, 1, 3]),
   (702172800, [0, 1, 2, 2]),
   (140434560, [0, 5]),
   (-3744921600, [1, 1, 1, 2]),
   (-1404345600, [1, 4]),
   (-936230400, [2, 3])])]

def skQ_J6_5 : SectorVector := [(-1,
  [(564848640, [0, 1, 1, 1, 1, 1]),
   (1412121600, [0, 1, 1, 3]),
   (1059091200, [0, 1, 2, 2]),
   (211818240, [0, 5]),
   (-5648486400, [1, 1, 1, 2]),
   (-2118182400, [1, 4]),
   (-1412121600, [2, 3])]),
 (1,
  [(-564848640, [0, 1, 1, 1, 1, 1]),
   (-1412121600, [0, 1, 1, 3]),
   (-1059091200, [0, 1, 2, 2]),
   (-211818240, [0, 5]),
   (-5648486400, [1, 1, 1, 2]),
   (-2118182400, [1, 4]),
   (-1412121600, [2, 3])])]

def skQ_J6_6 : SectorVector := [(1, []), (-1, [])]

def skQ_J6_7 : SectorVector := [(-1, []), (1, [])]

def skQ_J6_8 : SectorVector := [(1, []), (-1, [])]

def skQ_J6_9 : SectorVector := [(-1, []), (1, [])]

def skPf_J6 : ℕ → SectorVector
  | 0 => skP_J6_0
  | 1 => skP_J6_1
  | 2 => skP_J6_2
  | 3 => skP_J6_3
  | 4 => skP_J6_4
  | 5 => skP_J6_5
  | 6 => skP_J6_6
  | _ => []

def skQf_J6 : ℕ → SectorVector
  | 0 => skQ_J6_0
  | 1 => skQ_J6_1
  | 2 => skQ_J6_2
  | 3 => skQ_J6_3
  | 4 => skQ_J6_4
  | 5 => skQ_J6_5
  | 6 => skQ_J6_6
  | 7 => skQ_J6_7
  | 8 => skQ_J6_8
  | 9 => skQ_J6_9
  | _ => []

set_option maxHeartbeats 4000000 in
theorem skP_J6_0_cert : VectorCertificate (OrbSgl.uTerm true 6 0) skP_J6_0 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_J6_1_cert : VectorCertificate (OrbSgl.uTerm true 6 1) skP_J6_1 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_J6_2_cert : VectorCertificate (OrbSgl.uTerm true 6 2) skP_J6_2 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_J6_3_cert : VectorCertificate (OrbSgl.uTerm true 6 3) skP_J6_3 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_J6_4_cert : VectorCertificate (OrbSgl.uTerm true 6 4) skP_J6_4 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_J6_5_cert : VectorCertificate (OrbSgl.uTerm true 6 5) skP_J6_5 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_J6_6_cert : VectorCertificate (OrbSgl.uTerm true 6 6) skP_J6_6 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skY_J6_cert : VectorCertificate (OrbSgl.uSum 6 skPf_J6) skY_J6 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J6_0_cert : VectorCertificate (OrbSgl.vTerm true skY_J6 6 0) skQ_J6_0 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J6_1_cert : VectorCertificate (OrbSgl.vTerm true skY_J6 6 1) skQ_J6_1 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J6_2_cert : VectorCertificate (OrbSgl.vTerm true skY_J6 6 2) skQ_J6_2 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J6_3_cert : VectorCertificate (OrbSgl.vTerm true skY_J6 6 3) skQ_J6_3 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J6_4_cert : VectorCertificate (OrbSgl.vTerm true skY_J6 6 4) skQ_J6_4 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J6_5_cert : VectorCertificate (OrbSgl.vTerm true skY_J6 6 5) skQ_J6_5 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J6_6_cert : VectorCertificate (OrbSgl.vTerm true skY_J6 6 6) skQ_J6_6 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J6_7_cert : VectorCertificate (OrbSgl.vTerm true skY_J6 6 7) skQ_J6_7 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J6_8_cert : VectorCertificate (OrbSgl.vTerm true skY_J6 6 8) skQ_J6_8 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J6_9_cert : VectorCertificate (OrbSgl.vTerm true skY_J6 6 9) skQ_J6_9 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skT_J6_cert : VectorCertificate (OrbSgl.vSum 6 skQf_J6) termJ_6 := by decide +kernel

theorem skY_J6_value : evaluate skY_J6 =
    (V2m 4 four_ge_one).smul (weightNine : LatModuleGen (latP 4)) 6 (aVec true : LatModuleGen (latP 4)) := by
  rw [← vector_eq_of_certificate _ _ skY_J6_cert]
  apply evaluate_uSum true 6 (by norm_num)
  intro i hi
  interval_cases i
  · exact (vector_eq_of_certificate _ _ skP_J6_0_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_J6_1_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_J6_2_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_J6_3_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_J6_4_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_J6_5_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_J6_6_cert).symm

/-- The certified value of `termJ_6`. -/
theorem sk_J6 : evaluate termJ_6 = ((Nat.choose 15 6 : ℕ) : ℂ) •
    (V2m 4 four_ge_one).smul ((V2m 4 four_ge_one).smul (weightNine : LatModuleGen (latP 4)) 6 (aVec true))
      (6 - (6 : ℕ)) (aVec true : LatModuleGen (latP 4)) := by
  rw [← vector_eq_of_certificate _ _ skT_J6_cert]
  apply evaluate_vSum true 6 (by norm_num) skY_J6 skY_J6_value
  intro j hj
  interval_cases j
  · exact (vector_eq_of_certificate _ _ skQ_J6_0_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J6_1_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J6_2_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J6_3_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J6_4_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J6_5_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J6_6_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J6_7_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J6_8_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J6_9_cert).symm

end VOA.Classification.COne.OrbSgl
