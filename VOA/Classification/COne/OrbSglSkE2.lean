import VOA.Classification.COne.OrbSglSkew

/-! # OrbSgl: certified two-stage evaluation of `C(15,2) (u₍2₎a)₍4₎a`, `a = E`
(machine-generated) -/

set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option Elab.async false
set_option linter.style.longLine false

namespace VOA.Classification.COne.OrbSgl

open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational OrbC2g OrbC2h OrbC2c PlusC2 PlusC2Eval PlusUnitary OrbC2e

def skP_E2_0 : SectorVector := [(0,
  [((5504 : Rat)/945, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1]),
   ((-1472 : Rat)/63, [1, 1, 1, 1, 1, 1, 1, 3]),
   ((176 : Rat)/3, [1, 1, 1, 1, 1, 1, 2, 2]),
   ((-368 : Rat)/5, [1, 1, 1, 1, 1, 5]),
   (-320, [1, 1, 1, 1, 2, 4]),
   ((-2240 : Rat)/9, [1, 1, 1, 1, 3, 3]),
   ((2080 : Rat)/3, [1, 1, 1, 2, 2, 3]),
   ((-960 : Rat)/7, [1, 1, 1, 7]),
   (-200, [1, 1, 2, 2, 2, 2]),
   (160, [1, 1, 2, 6]),
   (416, [1, 1, 3, 5]),
   (-360, [1, 1, 4, 4]),
   (-168, [1, 2, 2, 5]),
   (160, [1, 2, 3, 4]),
   ((8320 : Rat)/27, [1, 3, 3, 3]),
   ((160 : Rat)/3, [1, 9]),
   (-440, [2, 2, 2, 4]),
   ((320 : Rat)/3, [2, 2, 3, 3]),
   (-120, [2, 8]),
   ((960 : Rat)/7, [3, 7]),
   (-80, [4, 6]),
   ((96 : Rat)/5, [5, 5])]),
 (-2, []),
 (2, [])]

def skP_E2_1 : SectorVector := [(2, []),
 (-2, []),
 (0,
  [((576 : Rat)/7, [1, 1, 1, 1, 1, 1, 1, 3]),
   (288, [1, 1, 1, 1, 1, 1, 2, 2]),
   (-1008, [1, 1, 1, 1, 1, 5]),
   (-1260, [1, 1, 1, 1, 2, 4]),
   (720, [1, 1, 1, 2, 2, 3]),
   (-960, [1, 1, 1, 7]),
   (360, [1, 1, 2, 2, 2, 2]),
   (1440, [1, 1, 2, 6]),
   (288, [1, 1, 3, 5]),
   (-360, [1, 1, 4, 4]),
   (-2232, [1, 2, 2, 5]),
   (2520, [1, 2, 3, 4]),
   (1920, [1, 3, 3, 3]),
   (480, [1, 9]),
   (-1590, [2, 2, 2, 4]),
   (-720, [2, 2, 3, 3]),
   (-900, [2, 8]),
   ((4800 : Rat)/7, [3, 7]),
   (120, [4, 6]),
   (-288, [5, 5])])]

def skP_E2_2 : SectorVector := [(0,
  [((3072 : Rat)/7, [1, 1, 1, 1, 1, 1, 1, 3]),
   (1536, [1, 1, 1, 1, 1, 1, 2, 2]),
   (-4032, [1, 1, 1, 1, 1, 5]),
   (-7200, [1, 1, 1, 1, 2, 4]),
   (-1440, [1, 1, 1, 1, 3, 3]),
   (2880, [1, 1, 1, 2, 2, 3]),
   (-1920, [1, 1, 1, 7]),
   (2880, [1, 1, 2, 2, 2, 2]),
   (-11520, [1, 1, 2, 6]),
   (3456, [1, 1, 3, 5]),
   (5760, [1, 1, 4, 4]),
   (-3744, [1, 2, 2, 5]),
   (18720, [1, 2, 3, 4]),
   (4800, [1, 3, 3, 3]),
   (3840, [1, 9]),
   (-5520, [2, 2, 2, 4]),
   (-8880, [2, 2, 3, 3]),
   (-5760, [2, 8]),
   ((21120 : Rat)/7, [3, 7]),
   (960, [4, 6]),
   (-1152, [5, 5])]),
 (-2, []),
 (2, [])]

def skP_E2_3 : SectorVector := [(2, []),
 (-2, []),
 (0,
  [(-576, [1, 1, 1, 1, 1, 5]),
   (-2880, [1, 1, 1, 1, 2, 4]),
   (-1440, [1, 1, 1, 1, 3, 3]),
   (-5760, [1, 1, 1, 2, 2, 3]),
   (-76800, [1, 1, 1, 7]),
   (-1440, [1, 1, 2, 2, 2, 2]),
   (-43200, [1, 1, 2, 6]),
   (69120, [1, 1, 3, 5]),
   (53280, [1, 1, 4, 4]),
   (-1440, [1, 2, 2, 5]),
   (38880, [1, 2, 3, 4]),
   (960, [1, 3, 3, 3]),
   (26880, [1, 9]),
   (-17040, [2, 2, 2, 4]),
   (-33840, [2, 2, 3, 3]),
   (-20160, [2, 8]),
   (-13440, [3, 7]),
   (6720, [4, 6]),
   (8064, [5, 5])])]

def skP_E2_4 : SectorVector := [(0,
  [(-6912, [1, 1, 1, 1, 1, 5]),
   (-34560, [1, 1, 1, 1, 2, 4]),
   (-17280, [1, 1, 1, 1, 3, 3]),
   (-69120, [1, 1, 1, 2, 2, 3]),
   (-57600, [1, 1, 1, 7]),
   (-17280, [1, 1, 2, 2, 2, 2]),
   (-86400, [1, 1, 2, 6]),
   (-34560, [1, 1, 3, 5]),
   (-8640, [1, 1, 4, 4]),
   (-17280, [1, 2, 2, 5]),
   (34560, [1, 2, 3, 4]),
   (11520, [1, 3, 3, 3]),
   (322560, [1, 9]),
   (11520, [2, 2, 2, 4]),
   (25920, [2, 2, 3, 3]),
   (-241920, [2, 8]),
   (-161280, [3, 7]),
   (80640, [4, 6]),
   (96768, [5, 5])]),
 (-2, []),
 (2, [])]

def skP_E2_5 : SectorVector := [(2, []),
 (-2, []),
 (0,
  [(144000, [1, 1, 1, 7]),
   (432000, [1, 1, 2, 6]),
   (432000, [1, 1, 3, 5]),
   (216000, [1, 1, 4, 4]),
   (432000, [1, 2, 2, 5]),
   (864000, [1, 2, 3, 4]),
   (144000, [1, 3, 3, 3]),
   (-2016000, [1, 9]),
   (144000, [2, 2, 2, 4]),
   (216000, [2, 2, 3, 3]),
   (-756000, [2, 8]),
   (144000, [3, 7]),
   (684000, [4, 6]),
   (432000, [5, 5])])]

def skP_E2_6 : SectorVector := [(0,
  [(-1152000, [1, 1, 1, 7]),
   (-3456000, [1, 1, 2, 6]),
   (-3456000, [1, 1, 3, 5]),
   (-1728000, [1, 1, 4, 4]),
   (-3456000, [1, 2, 2, 5]),
   (-6912000, [1, 2, 3, 4]),
   (-1152000, [1, 3, 3, 3]),
   (16128000, [1, 9]),
   (-1152000, [2, 2, 2, 4]),
   (-1728000, [2, 2, 3, 3]),
   (6048000, [2, 8]),
   (-1152000, [3, 7]),
   (-5472000, [4, 6]),
   (-3456000, [5, 5])]),
 (-2, []),
 (2, [])]

def skP_E2_7 : SectorVector := [(2, []), (-2, []), (0, [])]

def skP_E2_8 : SectorVector := [(0, []), (-2, []), (2, [])]

def skP_E2_9 : SectorVector := [(2, []), (-2, []), (0, [])]

def skP_E2_10 : SectorVector := [(0, []), (-2, []), (2, [])]

def skY_E2 : SectorVector := [(2, []),
 (-2, []),
 (0,
  [((-5504 : Rat)/945, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1]),
   ((-1024 : Rat)/9, [1, 1, 1, 1, 1, 1, 1, 3]),
   ((-1616 : Rat)/3, [1, 1, 1, 1, 1, 1, 2, 2]),
   ((6368 : Rat)/5, [1, 1, 1, 1, 1, 5]),
   (3620, [1, 1, 1, 1, 2, 4]),
   ((13040 : Rat)/9, [1, 1, 1, 1, 3, 3]),
   ((1520 : Rat)/3, [1, 1, 1, 2, 2, 3]),
   ((-52240 : Rat)/7, [1, 1, 1, 7]),
   (-400, [1, 1, 2, 2, 2, 2]),
   (11840, [1, 1, 2, 6]),
   (19504, [1, 1, 3, 5]),
   (10560, [1, 1, 4, 4]),
   (8688, [1, 2, 2, 5]),
   (14840, [1, 2, 3, 4]),
   ((45680 : Rat)/27, [1, 3, 3, 3]),
   ((-148960 : Rat)/3, [1, 9]),
   (1090, [2, 2, 2, 4]),
   ((3280 : Rat)/3, [2, 2, 3, 3]),
   (-5880, [2, 8]),
   (6320, [3, 7]),
   (10780, [4, 6]),
   ((29904 : Rat)/5, [5, 5])])]

def skQ_E2_0 : SectorVector := [(-1,
  [(-361216, [0, 1, 1, 1, 1, 1]),
   (-3008080, [0, 1, 1, 3]),
   (-2871360, [0, 1, 2, 2]),
   (-508416, [0, 5]),
   (8264000, [1, 1, 1, 2]),
   (5159520, [1, 4]),
   (3652160, [2, 3])]),
 (-3, []),
 (1,
  [(361216, [0, 1, 1, 1, 1, 1]),
   (3008080, [0, 1, 1, 3]),
   (2871360, [0, 1, 2, 2]),
   (508416, [0, 5]),
   (8264000, [1, 1, 1, 2]),
   (5159520, [1, 4]),
   (3652160, [2, 3])]),
 (3, [])]

def skQ_E2_1 : SectorVector := [(3, []),
 (1,
  [(3281440, [0, 1, 1, 1, 1, 1]),
   (17570560, [0, 1, 1, 3]),
   (13589040, [0, 1, 2, 2]),
   (1981680, [0, 5]),
   (52627840, [1, 1, 1, 2]),
   (27048480, [1, 4]),
   (22549120, [2, 3])]),
 (-3, []),
 (-1,
  [(-3281440, [0, 1, 1, 1, 1, 1]),
   (-17570560, [0, 1, 1, 3]),
   (-13589040, [0, 1, 2, 2]),
   (-1981680, [0, 5]),
   (52627840, [1, 1, 1, 2]),
   (27048480, [1, 4]),
   (22549120, [2, 3])])]

def skQ_E2_2 : SectorVector := [(-1,
  [(-21910400, [0, 1, 1, 1, 1, 1]),
   (-79339040, [0, 1, 1, 3]),
   (-58331040, [0, 1, 2, 2]),
   (-10562880, [0, 5]),
   (265101440, [1, 1, 1, 2]),
   (126048000, [1, 4]),
   (90838400, [2, 3])]),
 (-3, []),
 (1,
  [(21910400, [0, 1, 1, 1, 1, 1]),
   (79339040, [0, 1, 1, 3]),
   (58331040, [0, 1, 2, 2]),
   (10562880, [0, 5]),
   (265101440, [1, 1, 1, 2]),
   (126048000, [1, 4]),
   (90838400, [2, 3])]),
 (3, [])]

def skQ_E2_3 : SectorVector := [(3, []),
 (1,
  [(98841600, [0, 1, 1, 1, 1, 1]),
   (270691200, [0, 1, 1, 3]),
   (197121600, [0, 1, 2, 2]),
   (48859200, [0, 5]),
   (1019865600, [1, 1, 1, 2]),
   (441417600, [1, 4]),
   (278553600, [2, 3])]),
 (-3, []),
 (-1,
  [(-98841600, [0, 1, 1, 1, 1, 1]),
   (-270691200, [0, 1, 1, 3]),
   (-197121600, [0, 1, 2, 2]),
   (-48859200, [0, 5]),
   (1019865600, [1, 1, 1, 2]),
   (441417600, [1, 4]),
   (278553600, [2, 3])])]

def skQ_E2_4 : SectorVector := [(-1,
  [(-258785280, [0, 1, 1, 1, 1, 1]),
   (-646963200, [0, 1, 1, 3]),
   (-485222400, [0, 1, 2, 2]),
   (-97044480, [0, 5]),
   (2587852800, [1, 1, 1, 2]),
   (970444800, [1, 4]),
   (646963200, [2, 3])]),
 (-3, []),
 (1,
  [(258785280, [0, 1, 1, 1, 1, 1]),
   (646963200, [0, 1, 1, 3]),
   (485222400, [0, 1, 2, 2]),
   (97044480, [0, 5]),
   (2587852800, [1, 1, 1, 2]),
   (970444800, [1, 4]),
   (646963200, [2, 3])]),
 (3, [])]

def skQ_E2_5 : SectorVector := [(3, []),
 (1,
  [(264775680, [0, 1, 1, 1, 1, 1]),
   (661939200, [0, 1, 1, 3]),
   (496454400, [0, 1, 2, 2]),
   (99290880, [0, 5]),
   (2647756800, [1, 1, 1, 2]),
   (992908800, [1, 4]),
   (661939200, [2, 3])]),
 (-3, []),
 (-1,
  [(-264775680, [0, 1, 1, 1, 1, 1]),
   (-661939200, [0, 1, 1, 3]),
   (-496454400, [0, 1, 2, 2]),
   (-99290880, [0, 5]),
   (2647756800, [1, 1, 1, 2]),
   (992908800, [1, 4]),
   (661939200, [2, 3])])]

def skQ_E2_6 : SectorVector := [(-1, []), (-3, []), (1, []), (3, [])]

def skQ_E2_7 : SectorVector := [(3, []), (1, []), (-3, []), (-1, [])]

def skQ_E2_8 : SectorVector := [(-1, []), (-3, []), (1, []), (3, [])]

def skQ_E2_9 : SectorVector := [(3, []), (1, []), (-3, []), (-1, [])]

def skPf_E2 : ℕ → SectorVector
  | 0 => skP_E2_0
  | 1 => skP_E2_1
  | 2 => skP_E2_2
  | 3 => skP_E2_3
  | 4 => skP_E2_4
  | 5 => skP_E2_5
  | 6 => skP_E2_6
  | 7 => skP_E2_7
  | 8 => skP_E2_8
  | 9 => skP_E2_9
  | 10 => skP_E2_10
  | _ => []

def skQf_E2 : ℕ → SectorVector
  | 0 => skQ_E2_0
  | 1 => skQ_E2_1
  | 2 => skQ_E2_2
  | 3 => skQ_E2_3
  | 4 => skQ_E2_4
  | 5 => skQ_E2_5
  | 6 => skQ_E2_6
  | 7 => skQ_E2_7
  | 8 => skQ_E2_8
  | 9 => skQ_E2_9
  | _ => []

set_option maxHeartbeats 4000000 in
theorem skP_E2_0_cert : VectorCertificate (OrbSgl.uTerm false 2 0) skP_E2_0 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_E2_1_cert : VectorCertificate (OrbSgl.uTerm false 2 1) skP_E2_1 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_E2_2_cert : VectorCertificate (OrbSgl.uTerm false 2 2) skP_E2_2 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_E2_3_cert : VectorCertificate (OrbSgl.uTerm false 2 3) skP_E2_3 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_E2_4_cert : VectorCertificate (OrbSgl.uTerm false 2 4) skP_E2_4 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_E2_5_cert : VectorCertificate (OrbSgl.uTerm false 2 5) skP_E2_5 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_E2_6_cert : VectorCertificate (OrbSgl.uTerm false 2 6) skP_E2_6 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_E2_7_cert : VectorCertificate (OrbSgl.uTerm false 2 7) skP_E2_7 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_E2_8_cert : VectorCertificate (OrbSgl.uTerm false 2 8) skP_E2_8 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_E2_9_cert : VectorCertificate (OrbSgl.uTerm false 2 9) skP_E2_9 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_E2_10_cert : VectorCertificate (OrbSgl.uTerm false 2 10) skP_E2_10 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skY_E2_cert : VectorCertificate (OrbSgl.uSum 2 skPf_E2) skY_E2 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E2_0_cert : VectorCertificate (OrbSgl.vTerm false skY_E2 2 0) skQ_E2_0 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E2_1_cert : VectorCertificate (OrbSgl.vTerm false skY_E2 2 1) skQ_E2_1 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E2_2_cert : VectorCertificate (OrbSgl.vTerm false skY_E2 2 2) skQ_E2_2 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E2_3_cert : VectorCertificate (OrbSgl.vTerm false skY_E2 2 3) skQ_E2_3 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E2_4_cert : VectorCertificate (OrbSgl.vTerm false skY_E2 2 4) skQ_E2_4 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E2_5_cert : VectorCertificate (OrbSgl.vTerm false skY_E2 2 5) skQ_E2_5 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E2_6_cert : VectorCertificate (OrbSgl.vTerm false skY_E2 2 6) skQ_E2_6 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E2_7_cert : VectorCertificate (OrbSgl.vTerm false skY_E2 2 7) skQ_E2_7 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E2_8_cert : VectorCertificate (OrbSgl.vTerm false skY_E2 2 8) skQ_E2_8 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_E2_9_cert : VectorCertificate (OrbSgl.vTerm false skY_E2 2 9) skQ_E2_9 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skT_E2_cert : VectorCertificate (OrbSgl.vSum 2 skQf_E2) termE_2 := by decide +kernel

theorem skY_E2_value : evaluate skY_E2 =
    (V2m 4 four_ge_one).smul (weightNine : LatModuleGen (latP 4)) 2 (aVec false : LatModuleGen (latP 4)) := by
  rw [← vector_eq_of_certificate _ _ skY_E2_cert]
  apply evaluate_uSum false 2 (by norm_num)
  intro i hi
  interval_cases i
  · exact (vector_eq_of_certificate _ _ skP_E2_0_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_E2_1_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_E2_2_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_E2_3_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_E2_4_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_E2_5_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_E2_6_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_E2_7_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_E2_8_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_E2_9_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_E2_10_cert).symm

/-- The certified value of `termE_2`. -/
theorem sk_E2 : evaluate termE_2 = ((Nat.choose 15 2 : ℕ) : ℂ) •
    (V2m 4 four_ge_one).smul ((V2m 4 four_ge_one).smul (weightNine : LatModuleGen (latP 4)) 2 (aVec false))
      (6 - (2 : ℕ)) (aVec false : LatModuleGen (latP 4)) := by
  rw [← vector_eq_of_certificate _ _ skT_E2_cert]
  apply evaluate_vSum false 2 (by norm_num) skY_E2 skY_E2_value
  intro j hj
  interval_cases j
  · exact (vector_eq_of_certificate _ _ skQ_E2_0_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_E2_1_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_E2_2_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_E2_3_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_E2_4_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_E2_5_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_E2_6_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_E2_7_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_E2_8_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_E2_9_cert).symm

end VOA.Classification.COne.OrbSgl
