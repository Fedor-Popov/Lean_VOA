import VOA.Classification.COne.OrbSglSkew

/-! # OrbSgl: certified two-stage evaluation of `C(15,3) (u₍3₎a)₍3₎a`, `a = E`
(machine-generated) -/

set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option Elab.async false
set_option linter.style.longLine false

namespace VOA.Classification.COne.OrbSgl

open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational OrbC2g OrbC2h OrbC2c PlusC2 PlusC2Eval PlusUnitary OrbC2e

def skP_E3_0 : SectorVector := [(0,
  [((288 : Rat)/7, [1, 1, 1, 1, 1, 1, 1, 2]),
   (-252, [1, 1, 1, 1, 1, 4]),
   (120, [1, 1, 1, 2, 2, 2]),
   (-160, [1, 1, 1, 6]),
   (384, [1, 1, 2, 5]),
   (-120, [1, 1, 3, 4]),
   (-750, [1, 2, 2, 4]),
   (960, [1, 2, 3, 3]),
   (60, [1, 8]),
   (-280, [2, 2, 2, 3]),
   ((-960 : Rat)/7, [2, 7]),
   (160, [3, 6]),
   (-72, [4, 5])]),
 (-2, []),
 (2, [])]

def skP_E3_1 : SectorVector := [(2, []),
 (-2, []),
 (0,
  [((1536 : Rat)/7, [1, 1, 1, 1, 1, 1, 1, 2]),
   (-1008, [1, 1, 1, 1, 1, 4]),
   (-720, [1, 1, 1, 1, 2, 3]),
   (960, [1, 1, 1, 2, 2, 2]),
   (-320, [1, 1, 1, 6]),
   (-2112, [1, 1, 2, 5]),
   (1920, [1, 1, 3, 4]),
   (120, [1, 2, 2, 4]),
   (2400, [1, 2, 3, 3]),
   (480, [1, 8]),
   (-1880, [2, 2, 2, 3]),
   ((-6240 : Rat)/7, [2, 7]),
   (800, [3, 6]),
   (-288, [4, 5])])]

def skP_E3_2 : SectorVector := [(0,
  [(-144, [1, 1, 1, 1, 1, 4]),
   (-720, [1, 1, 1, 1, 2, 3]),
   (-480, [1, 1, 1, 2, 2, 2]),
   (-12800, [1, 1, 1, 6]),
   (-960, [1, 1, 2, 5]),
   (17760, [1, 1, 3, 4]),
   (120, [1, 2, 2, 4]),
   (480, [1, 2, 3, 3]),
   (3360, [1, 8]),
   (-5720, [2, 2, 2, 3]),
   (-3360, [2, 7]),
   (-1120, [3, 6]),
   (2016, [4, 5])]),
 (-2, []),
 (2, [])]

def skP_E3_3 : SectorVector := [(2, []),
 (-2, []),
 (0,
  [(-1728, [1, 1, 1, 1, 1, 4]),
   (-8640, [1, 1, 1, 1, 2, 3]),
   (-5760, [1, 1, 1, 2, 2, 2]),
   (-9600, [1, 1, 1, 6]),
   (-11520, [1, 1, 2, 5]),
   (-2880, [1, 1, 3, 4]),
   (1440, [1, 2, 2, 4]),
   (5760, [1, 2, 3, 3]),
   (40320, [1, 8]),
   (3360, [2, 2, 2, 3]),
   (-40320, [2, 7]),
   (-13440, [3, 6]),
   (24192, [4, 5])])]

def skP_E3_4 : SectorVector := [(0,
  [(24000, [1, 1, 1, 6]),
   (72000, [1, 1, 2, 5]),
   (72000, [1, 1, 3, 4]),
   (72000, [1, 2, 2, 4]),
   (72000, [1, 2, 3, 3]),
   (-252000, [1, 8]),
   (24000, [2, 2, 2, 3]),
   (-72000, [2, 7]),
   (48000, [3, 6]),
   (108000, [4, 5])]),
 (-2, []),
 (2, [])]

def skP_E3_5 : SectorVector := [(2, []),
 (-2, []),
 (0,
  [(-192000, [1, 1, 1, 6]),
   (-576000, [1, 1, 2, 5]),
   (-576000, [1, 1, 3, 4]),
   (-576000, [1, 2, 2, 4]),
   (-576000, [1, 2, 3, 3]),
   (2016000, [1, 8]),
   (-192000, [2, 2, 2, 3]),
   (576000, [2, 7]),
   (-384000, [3, 6]),
   (-864000, [4, 5])])]

def skP_E3_6 : SectorVector := [(0, []), (-2, []), (2, [])]

def skP_E3_7 : SectorVector := [(2, []), (-2, []), (0, [])]

def skP_E3_8 : SectorVector := [(0, []), (-2, []), (2, [])]

def skP_E3_9 : SectorVector := [(2, []), (-2, []), (0, [])]

def skY_E3 : SectorVector := [(0,
  [((-1248 : Rat)/7, [1, 1, 1, 1, 1, 1, 1, 2]),
   (972, [1, 1, 1, 1, 1, 4]),
   (1800, [1, 1, 1, 1, 2, 3]),
   (-120, [1, 1, 1, 2, 2, 2]),
   (-2040, [1, 1, 1, 6]),
   (11736, [1, 1, 2, 5]),
   (15120, [1, 1, 3, 4]),
   (6750, [1, 2, 2, 4]),
   (5640, [1, 2, 3, 3]),
   (-32760, [1, 8]),
   (780, [2, 2, 2, 3]),
   ((-14040 : Rat)/7, [2, 7]),
   (6240, [3, 6]),
   (8892, [4, 5])]),
 (-2, []),
 (2, [])]

def skQ_E3_0 : SectorVector := [(1,
  [(198900, [0, 1, 1, 1, 1, 1]),
   (1566000, [0, 1, 1, 3]),
   (1384650, [0, 1, 2, 2]),
   (477540, [0, 5]),
   (4197600, [1, 1, 1, 2]),
   (3327840, [1, 4]),
   (2031840, [2, 3])]),
 (-3, []),
 (-1,
  [(-198900, [0, 1, 1, 1, 1, 1]),
   (-1566000, [0, 1, 1, 3]),
   (-1384650, [0, 1, 2, 2]),
   (-477540, [0, 5]),
   (4197600, [1, 1, 1, 2]),
   (3327840, [1, 4]),
   (2031840, [2, 3])]),
 (3, [])]

def skQ_E3_1 : SectorVector := [(3, []),
 (-1,
  [(-1743840, [0, 1, 1, 1, 1, 1]),
   (-9395280, [0, 1, 1, 3]),
   (-6953760, [0, 1, 2, 2]),
   (-1917360, [0, 5]),
   (27218880, [1, 1, 1, 2]),
   (16837920, [1, 4]),
   (11905920, [2, 3])]),
 (-3, []),
 (1,
  [(1743840, [0, 1, 1, 1, 1, 1]),
   (9395280, [0, 1, 1, 3]),
   (6953760, [0, 1, 2, 2]),
   (1917360, [0, 5]),
   (27218880, [1, 1, 1, 2]),
   (16837920, [1, 4]),
   (11905920, [2, 3])])]

def skQ_E3_2 : SectorVector := [(1,
  [(11578560, [0, 1, 1, 1, 1, 1]),
   (43132560, [0, 1, 1, 3]),
   (30750480, [0, 1, 2, 2]),
   (7539840, [0, 5]),
   (139894080, [1, 1, 1, 2]),
   (74292480, [1, 4]),
   (49159680, [2, 3])]),
 (-3, []),
 (-1,
  [(-11578560, [0, 1, 1, 1, 1, 1]),
   (-43132560, [0, 1, 1, 3]),
   (-30750480, [0, 1, 2, 2]),
   (-7539840, [0, 5]),
   (139894080, [1, 1, 1, 2]),
   (74292480, [1, 4]),
   (49159680, [2, 3])]),
 (3, [])]

def skQ_E3_3 : SectorVector := [(3, []),
 (-1,
  [(-53521920, [0, 1, 1, 1, 1, 1]),
   (-150600960, [0, 1, 1, 3]),
   (-108751680, [0, 1, 2, 2]),
   (-28468800, [0, 5]),
   (557614080, [1, 1, 1, 2]),
   (251095680, [1, 4]),
   (156199680, [2, 3])]),
 (-3, []),
 (1,
  [(53521920, [0, 1, 1, 1, 1, 1]),
   (150600960, [0, 1, 1, 3]),
   (108751680, [0, 1, 2, 2]),
   (28468800, [0, 5]),
   (557614080, [1, 1, 1, 2]),
   (251095680, [1, 4]),
   (156199680, [2, 3])])]

def skQ_E3_4 : SectorVector := [(1,
  [(150059520, [0, 1, 1, 1, 1, 1]),
   (375148800, [0, 1, 1, 3]),
   (281361600, [0, 1, 2, 2]),
   (56272320, [0, 5]),
   (1500595200, [1, 1, 1, 2]),
   (562723200, [1, 4]),
   (375148800, [2, 3])]),
 (-3, []),
 (-1,
  [(-150059520, [0, 1, 1, 1, 1, 1]),
   (-375148800, [0, 1, 1, 3]),
   (-281361600, [0, 1, 2, 2]),
   (-56272320, [0, 5]),
   (1500595200, [1, 1, 1, 2]),
   (562723200, [1, 4]),
   (375148800, [2, 3])]),
 (3, [])]

def skQ_E3_5 : SectorVector := [(3, []),
 (-1,
  [(-185702400, [0, 1, 1, 1, 1, 1]),
   (-464256000, [0, 1, 1, 3]),
   (-348192000, [0, 1, 2, 2]),
   (-69638400, [0, 5]),
   (1857024000, [1, 1, 1, 2]),
   (696384000, [1, 4]),
   (464256000, [2, 3])]),
 (-3, []),
 (1,
  [(185702400, [0, 1, 1, 1, 1, 1]),
   (464256000, [0, 1, 1, 3]),
   (348192000, [0, 1, 2, 2]),
   (69638400, [0, 5]),
   (1857024000, [1, 1, 1, 2]),
   (696384000, [1, 4]),
   (464256000, [2, 3])])]

def skQ_E3_6 : SectorVector := [(1, []), (-3, []), (-1, []), (3, [])]

def skQ_E3_7 : SectorVector := [(3, []), (-1, []), (-3, []), (1, [])]

def skQ_E3_8 : SectorVector := [(1, []), (-3, []), (-1, []), (3, [])]

def skQ_E3_9 : SectorVector := [(3, []), (-1, []), (-3, []), (1, [])]

def skPf_E3 : ℕ → SectorVector
  | 0 => skP_E3_0
  | 1 => skP_E3_1
  | 2 => skP_E3_2
  | 3 => skP_E3_3
  | 4 => skP_E3_4
  | 5 => skP_E3_5
  | 6 => skP_E3_6
  | 7 => skP_E3_7
  | 8 => skP_E3_8
  | 9 => skP_E3_9
  | _ => []

def skQf_E3 : ℕ → SectorVector
  | 0 => skQ_E3_0
  | 1 => skQ_E3_1
  | 2 => skQ_E3_2
  | 3 => skQ_E3_3
  | 4 => skQ_E3_4
  | 5 => skQ_E3_5
  | 6 => skQ_E3_6
  | 7 => skQ_E3_7
  | 8 => skQ_E3_8
  | 9 => skQ_E3_9
  | _ => []

set_option maxHeartbeats 4000000 in
theorem skP_E3_0_cert : VectorCertificate (OrbSgl.uTerm false 3 0) skP_E3_0 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_E3_1_cert : VectorCertificate (OrbSgl.uTerm false 3 1) skP_E3_1 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_E3_2_cert : VectorCertificate (OrbSgl.uTerm false 3 2) skP_E3_2 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_E3_3_cert : VectorCertificate (OrbSgl.uTerm false 3 3) skP_E3_3 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_E3_4_cert : VectorCertificate (OrbSgl.uTerm false 3 4) skP_E3_4 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_E3_5_cert : VectorCertificate (OrbSgl.uTerm false 3 5) skP_E3_5 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_E3_6_cert : VectorCertificate (OrbSgl.uTerm false 3 6) skP_E3_6 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_E3_7_cert : VectorCertificate (OrbSgl.uTerm false 3 7) skP_E3_7 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_E3_8_cert : VectorCertificate (OrbSgl.uTerm false 3 8) skP_E3_8 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_E3_9_cert : VectorCertificate (OrbSgl.uTerm false 3 9) skP_E3_9 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skY_E3_cert : VectorCertificate (OrbSgl.uSum 3 skPf_E3) skY_E3 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E3_0_cert : VectorCertificate (OrbSgl.vTerm false skY_E3 3 0) skQ_E3_0 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E3_1_cert : VectorCertificate (OrbSgl.vTerm false skY_E3 3 1) skQ_E3_1 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E3_2_cert : VectorCertificate (OrbSgl.vTerm false skY_E3 3 2) skQ_E3_2 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E3_3_cert : VectorCertificate (OrbSgl.vTerm false skY_E3 3 3) skQ_E3_3 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E3_4_cert : VectorCertificate (OrbSgl.vTerm false skY_E3 3 4) skQ_E3_4 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E3_5_cert : VectorCertificate (OrbSgl.vTerm false skY_E3 3 5) skQ_E3_5 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E3_6_cert : VectorCertificate (OrbSgl.vTerm false skY_E3 3 6) skQ_E3_6 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E3_7_cert : VectorCertificate (OrbSgl.vTerm false skY_E3 3 7) skQ_E3_7 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E3_8_cert : VectorCertificate (OrbSgl.vTerm false skY_E3 3 8) skQ_E3_8 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E3_9_cert : VectorCertificate (OrbSgl.vTerm false skY_E3 3 9) skQ_E3_9 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skT_E3_cert : VectorCertificate (OrbSgl.vSum 3 skQf_E3) termE_3 := by decide +kernel

theorem skY_E3_value : evaluate skY_E3 =
    (V2m 4 four_ge_one).smul (weightNine : LatModuleGen (latP 4)) 3 (aVec false : LatModuleGen (latP 4)) := by
  rw [← vector_eq_of_certificate _ _ skY_E3_cert]
  apply evaluate_uSum false 3 (by norm_num)
  intro i hi
  interval_cases i
  · exact (vector_eq_of_certificate _ _ skP_E3_0_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_E3_1_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_E3_2_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_E3_3_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_E3_4_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_E3_5_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_E3_6_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_E3_7_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_E3_8_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_E3_9_cert).symm

/-- The certified value of `termE_3`. -/
theorem sk_E3 : evaluate termE_3 = ((Nat.choose 15 3 : ℕ) : ℂ) •
    (V2m 4 four_ge_one).smul ((V2m 4 four_ge_one).smul (weightNine : LatModuleGen (latP 4)) 3 (aVec false))
      (6 - (3 : ℕ)) (aVec false : LatModuleGen (latP 4)) := by
  rw [← vector_eq_of_certificate _ _ skT_E3_cert]
  apply evaluate_vSum false 3 (by norm_num) skY_E3 skY_E3_value
  intro j hj
  interval_cases j
  · exact (vector_eq_of_certificate _ _ skQ_E3_0_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_E3_1_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_E3_2_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_E3_3_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_E3_4_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_E3_5_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_E3_6_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_E3_7_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_E3_8_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_E3_9_cert).symm

end VOA.Classification.COne.OrbSgl
