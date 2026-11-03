import VOA.Classification.COne.OrbSglSkew

/-! # OrbSgl: certified two-stage evaluation of `C(15,4) (u₍4₎a)₍2₎a`, `a = E`
(machine-generated) -/

set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option Elab.async false
set_option linter.style.longLine false

namespace VOA.Classification.COne.OrbSgl

open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational OrbC2g OrbC2h OrbC2c PlusC2 PlusC2Eval PlusUnitary OrbC2e

def skP_E4_0 : SectorVector := [(0,
  [((192 : Rat)/7, [1, 1, 1, 1, 1, 1, 1, 1]),
   (-336, [1, 1, 1, 1, 1, 3]),
   (240, [1, 1, 1, 1, 2, 2]),
   (-64, [1, 1, 1, 5]),
   (-480, [1, 1, 2, 4]),
   (480, [1, 1, 3, 3]),
   (360, [1, 2, 2, 3]),
   ((480 : Rat)/7, [1, 7]),
   (-280, [2, 2, 2, 2]),
   (-160, [2, 6]),
   (224, [3, 5]),
   (-120, [4, 4])]),
 (-2, []),
 (2, [])]

def skP_E4_1 : SectorVector := [(2, []),
 (-2, []),
 (0,
  [(-48, [1, 1, 1, 1, 1, 3]),
   (-120, [1, 1, 1, 1, 2, 2]),
   (-2560, [1, 1, 1, 5]),
   (1680, [1, 1, 2, 4]),
   (2400, [1, 1, 3, 3]),
   (-1080, [1, 2, 2, 3]),
   (480, [1, 7]),
   (-580, [2, 2, 2, 2]),
   (-640, [2, 6]),
   (32, [3, 5]),
   (240, [4, 4])])]

def skP_E4_2 : SectorVector := [(0,
  [(-576, [1, 1, 1, 1, 1, 3]),
   (-1440, [1, 1, 1, 1, 2, 2]),
   (-1920, [1, 1, 1, 5]),
   (-1440, [1, 1, 2, 4]),
   (1440, [1, 2, 2, 3]),
   (5760, [1, 7]),
   (240, [2, 2, 2, 2]),
   (-7680, [2, 6]),
   (384, [3, 5]),
   (2880, [4, 4])]),
 (-2, []),
 (2, [])]

def skP_E4_3 : SectorVector := [(2, []),
 (-2, []),
 (0,
  [(4800, [1, 1, 1, 5]),
   (14400, [1, 1, 2, 4]),
   (7200, [1, 1, 3, 3]),
   (14400, [1, 2, 2, 3]),
   (-36000, [1, 7]),
   (1200, [2, 2, 2, 2]),
   (-6000, [2, 6]),
   (12000, [3, 5]),
   (9000, [4, 4])])]

def skP_E4_4 : SectorVector := [(0,
  [(-38400, [1, 1, 1, 5]),
   (-115200, [1, 1, 2, 4]),
   (-57600, [1, 1, 3, 3]),
   (-115200, [1, 2, 2, 3]),
   (288000, [1, 7]),
   (-9600, [2, 2, 2, 2]),
   (48000, [2, 6]),
   (-96000, [3, 5]),
   (-72000, [4, 4])]),
 (-2, []),
 (2, [])]

def skP_E4_5 : SectorVector := [(2, []), (-2, []), (0, [])]

def skP_E4_6 : SectorVector := [(0, []), (-2, []), (2, [])]

def skP_E4_7 : SectorVector := [(2, []), (-2, []), (0, [])]

def skP_E4_8 : SectorVector := [(0, []), (-2, []), (2, [])]

def skY_E4 : SectorVector := [(2, []),
 (-2, []),
 (0,
  [((-192 : Rat)/7, [1, 1, 1, 1, 1, 1, 1, 1]),
   (576, [1, 1, 1, 1, 1, 3]),
   (360, [1, 1, 1, 1, 2, 2]),
   (864, [1, 1, 1, 5]),
   (10080, [1, 1, 2, 4]),
   (5520, [1, 1, 3, 3]),
   (5040, [1, 2, 2, 3]),
   ((-143280 : Rat)/7, [1, 7]),
   (180, [2, 2, 2, 2]),
   (360, [2, 6]),
   (5616, [3, 5]),
   (3420, [4, 4])])]

def skQ_E4_0 : SectorVector := [(-1,
  [(-96768, [0, 1, 1, 1, 1, 1]),
   (-756000, [0, 1, 1, 3]),
   (-626400, [0, 1, 2, 2]),
   (-320688, [0, 5]),
   (1906560, [1, 1, 1, 2]),
   (1884960, [1, 4]),
   (1048320, [2, 3])]),
 (-3, []),
 (1,
  [(96768, [0, 1, 1, 1, 1, 1]),
   (756000, [0, 1, 1, 3]),
   (626400, [0, 1, 2, 2]),
   (320688, [0, 5]),
   (1906560, [1, 1, 1, 2]),
   (1884960, [1, 4]),
   (1048320, [2, 3])]),
 (3, [])]

def skQ_E4_1 : SectorVector := [(3, []),
 (1,
  [(855360, [0, 1, 1, 1, 1, 1]),
   (4608000, [0, 1, 1, 3]),
   (3228480, [0, 1, 2, 2]),
   (1316160, [0, 5]),
   (12798720, [1, 1, 1, 2]),
   (9423360, [1, 4]),
   (5800320, [2, 3])]),
 (-3, []),
 (-1,
  [(-855360, [0, 1, 1, 1, 1, 1]),
   (-4608000, [0, 1, 1, 3]),
   (-3228480, [0, 1, 2, 2]),
   (-1316160, [0, 5]),
   (12798720, [1, 1, 1, 2]),
   (9423360, [1, 4]),
   (5800320, [2, 3])])]

def skQ_E4_2 : SectorVector := [(-1,
  [(-5625600, [0, 1, 1, 1, 1, 1]),
   (-21554880, [0, 1, 1, 3]),
   (-14915520, [0, 1, 2, 2]),
   (-4610880, [0, 5]),
   (67902720, [1, 1, 1, 2]),
   (39836160, [1, 4]),
   (24466560, [2, 3])]),
 (-3, []),
 (1,
  [(5625600, [0, 1, 1, 1, 1, 1]),
   (21554880, [0, 1, 1, 3]),
   (14915520, [0, 1, 2, 2]),
   (4610880, [0, 5]),
   (67902720, [1, 1, 1, 2]),
   (39836160, [1, 4]),
   (24466560, [2, 3])]),
 (3, [])]

def skQ_E4_3 : SectorVector := [(3, []),
 (1,
  [(26311680, [0, 1, 1, 1, 1, 1]),
   (75784320, [0, 1, 1, 3]),
   (54336960, [0, 1, 2, 2]),
   (14869440, [0, 5]),
   (276456960, [1, 1, 1, 2]),
   (128684160, [1, 4]),
   (79119360, [2, 3])]),
 (-3, []),
 (-1,
  [(-26311680, [0, 1, 1, 1, 1, 1]),
   (-75784320, [0, 1, 1, 3]),
   (-54336960, [0, 1, 2, 2]),
   (-14869440, [0, 5]),
   (276456960, [1, 1, 1, 2]),
   (128684160, [1, 4]),
   (79119360, [2, 3])])]

def skQ_E4_4 : SectorVector := [(-1,
  [(-77552640, [0, 1, 1, 1, 1, 1]),
   (-193881600, [0, 1, 1, 3]),
   (-145411200, [0, 1, 2, 2]),
   (-29082240, [0, 5]),
   (775526400, [1, 1, 1, 2]),
   (290822400, [1, 4]),
   (193881600, [2, 3])]),
 (-3, []),
 (1,
  [(77552640, [0, 1, 1, 1, 1, 1]),
   (193881600, [0, 1, 1, 3]),
   (145411200, [0, 1, 2, 2]),
   (29082240, [0, 5]),
   (775526400, [1, 1, 1, 2]),
   (290822400, [1, 4]),
   (193881600, [2, 3])]),
 (3, [])]

def skQ_E4_5 : SectorVector := [(3, []),
 (1,
  [(106629120, [0, 1, 1, 1, 1, 1]),
   (266572800, [0, 1, 1, 3]),
   (199929600, [0, 1, 2, 2]),
   (39985920, [0, 5]),
   (1066291200, [1, 1, 1, 2]),
   (399859200, [1, 4]),
   (266572800, [2, 3])]),
 (-3, []),
 (-1,
  [(-106629120, [0, 1, 1, 1, 1, 1]),
   (-266572800, [0, 1, 1, 3]),
   (-199929600, [0, 1, 2, 2]),
   (-39985920, [0, 5]),
   (1066291200, [1, 1, 1, 2]),
   (399859200, [1, 4]),
   (266572800, [2, 3])])]

def skQ_E4_6 : SectorVector := [(-1, []), (-3, []), (1, []), (3, [])]

def skQ_E4_7 : SectorVector := [(3, []), (1, []), (-3, []), (-1, [])]

def skQ_E4_8 : SectorVector := [(-1, []), (-3, []), (1, []), (3, [])]

def skQ_E4_9 : SectorVector := [(3, []), (1, []), (-3, []), (-1, [])]

def skPf_E4 : ℕ → SectorVector
  | 0 => skP_E4_0
  | 1 => skP_E4_1
  | 2 => skP_E4_2
  | 3 => skP_E4_3
  | 4 => skP_E4_4
  | 5 => skP_E4_5
  | 6 => skP_E4_6
  | 7 => skP_E4_7
  | 8 => skP_E4_8
  | _ => []

def skQf_E4 : ℕ → SectorVector
  | 0 => skQ_E4_0
  | 1 => skQ_E4_1
  | 2 => skQ_E4_2
  | 3 => skQ_E4_3
  | 4 => skQ_E4_4
  | 5 => skQ_E4_5
  | 6 => skQ_E4_6
  | 7 => skQ_E4_7
  | 8 => skQ_E4_8
  | 9 => skQ_E4_9
  | _ => []

set_option maxHeartbeats 4000000 in
theorem skP_E4_0_cert : VectorCertificate (OrbSgl.uTerm false 4 0) skP_E4_0 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_E4_1_cert : VectorCertificate (OrbSgl.uTerm false 4 1) skP_E4_1 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_E4_2_cert : VectorCertificate (OrbSgl.uTerm false 4 2) skP_E4_2 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_E4_3_cert : VectorCertificate (OrbSgl.uTerm false 4 3) skP_E4_3 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_E4_4_cert : VectorCertificate (OrbSgl.uTerm false 4 4) skP_E4_4 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_E4_5_cert : VectorCertificate (OrbSgl.uTerm false 4 5) skP_E4_5 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_E4_6_cert : VectorCertificate (OrbSgl.uTerm false 4 6) skP_E4_6 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_E4_7_cert : VectorCertificate (OrbSgl.uTerm false 4 7) skP_E4_7 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_E4_8_cert : VectorCertificate (OrbSgl.uTerm false 4 8) skP_E4_8 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skY_E4_cert : VectorCertificate (OrbSgl.uSum 4 skPf_E4) skY_E4 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E4_0_cert : VectorCertificate (OrbSgl.vTerm false skY_E4 4 0) skQ_E4_0 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E4_1_cert : VectorCertificate (OrbSgl.vTerm false skY_E4 4 1) skQ_E4_1 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E4_2_cert : VectorCertificate (OrbSgl.vTerm false skY_E4 4 2) skQ_E4_2 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E4_3_cert : VectorCertificate (OrbSgl.vTerm false skY_E4 4 3) skQ_E4_3 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E4_4_cert : VectorCertificate (OrbSgl.vTerm false skY_E4 4 4) skQ_E4_4 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E4_5_cert : VectorCertificate (OrbSgl.vTerm false skY_E4 4 5) skQ_E4_5 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E4_6_cert : VectorCertificate (OrbSgl.vTerm false skY_E4 4 6) skQ_E4_6 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E4_7_cert : VectorCertificate (OrbSgl.vTerm false skY_E4 4 7) skQ_E4_7 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E4_8_cert : VectorCertificate (OrbSgl.vTerm false skY_E4 4 8) skQ_E4_8 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E4_9_cert : VectorCertificate (OrbSgl.vTerm false skY_E4 4 9) skQ_E4_9 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skT_E4_cert : VectorCertificate (OrbSgl.vSum 4 skQf_E4) termE_4 := by decide +kernel

theorem skY_E4_value : evaluate skY_E4 =
    (V2m 4 four_ge_one).smul (weightNine : LatModuleGen (latP 4)) 4 (aVec false : LatModuleGen (latP 4)) := by
  rw [← vector_eq_of_certificate _ _ skY_E4_cert]
  apply evaluate_uSum false 4 (by norm_num)
  intro i hi
  interval_cases i
  · exact (vector_eq_of_certificate _ _ skP_E4_0_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_E4_1_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_E4_2_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_E4_3_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_E4_4_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_E4_5_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_E4_6_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_E4_7_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_E4_8_cert).symm

/-- The certified value of `termE_4`. -/
theorem sk_E4 : evaluate termE_4 = ((Nat.choose 15 4 : ℕ) : ℂ) •
    (V2m 4 four_ge_one).smul ((V2m 4 four_ge_one).smul (weightNine : LatModuleGen (latP 4)) 4 (aVec false))
      (6 - (4 : ℕ)) (aVec false : LatModuleGen (latP 4)) := by
  rw [← vector_eq_of_certificate _ _ skT_E4_cert]
  apply evaluate_vSum false 4 (by norm_num) skY_E4 skY_E4_value
  intro j hj
  interval_cases j
  · exact (vector_eq_of_certificate _ _ skQ_E4_0_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_E4_1_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_E4_2_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_E4_3_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_E4_4_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_E4_5_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_E4_6_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_E4_7_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_E4_8_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_E4_9_cert).symm

end VOA.Classification.COne.OrbSgl
