import VOA.Classification.COne.OrbSglSkew

/-! # OrbSgl: certified two-stage evaluation of `C(15,2) (u₍2₎a)₍4₎a`, `a = J`
(machine-generated) -/

set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option Elab.async false
set_option linter.style.longLine false

namespace VOA.Classification.COne.OrbSgl

open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational OrbC2g OrbC2h OrbC2c PlusC2 PlusC2Eval PlusUnitary OrbC2e

def skP_J2_0 : SectorVector := [(1,
  [(1140, [0, 1, 1, 1, 1, 2]),
   (3240, [0, 1, 1, 4]),
   (-120, [0, 1, 2, 3]),
   (-390, [0, 2, 2, 2]),
   (6000, [0, 6]),
   (-560, [1, 1, 1, 1, 1, 1]),
   (-4960, [1, 1, 1, 3]),
   (-1080, [1, 1, 2, 2]),
   (-16560, [1, 5]),
   (-720, [2, 4]),
   (640, [3, 3])]),
 (-1,
  [(-1140, [0, 1, 1, 1, 1, 2]),
   (-3240, [0, 1, 1, 4]),
   (120, [0, 1, 2, 3]),
   (390, [0, 2, 2, 2]),
   (-6000, [0, 6]),
   (-560, [1, 1, 1, 1, 1, 1]),
   (-4960, [1, 1, 1, 3]),
   (-1080, [1, 1, 2, 2]),
   (-16560, [1, 5]),
   (-720, [2, 4]),
   (640, [3, 3])])]

def skP_J2_1 : SectorVector := [(-1,
  [(-2970, [0, 1, 1, 1, 1, 2]),
   (9720, [0, 1, 1, 4]),
   (5940, [0, 1, 2, 3]),
   (1215, [0, 2, 2, 2]),
   (-24300, [0, 6]),
   (-2160, [1, 1, 1, 1, 1, 1]),
   (4320, [1, 1, 1, 3]),
   (3240, [1, 1, 2, 2]),
   (6480, [1, 5]),
   (-8100, [2, 4])]),
 (1,
  [(2970, [0, 1, 1, 1, 1, 2]),
   (-9720, [0, 1, 1, 4]),
   (-5940, [0, 1, 2, 3]),
   (-1215, [0, 2, 2, 2]),
   (24300, [0, 6]),
   (-2160, [1, 1, 1, 1, 1, 1]),
   (4320, [1, 1, 1, 3]),
   (3240, [1, 1, 2, 2]),
   (6480, [1, 5]),
   (-8100, [2, 4])])]

def skP_J2_2 : SectorVector := [(1,
  [(10800, [0, 1, 1, 1, 1, 2]),
   (-25920, [0, 1, 1, 4]),
   (-41040, [0, 1, 2, 3]),
   (1080, [0, 2, 2, 2]),
   (108000, [0, 6]),
   (-5760, [1, 1, 1, 1, 1, 1]),
   (-46080, [1, 1, 1, 3]),
   (51840, [1, 1, 2, 2]),
   (181440, [1, 5]),
   (-77760, [2, 4]),
   (-53280, [3, 3])]),
 (-1,
  [(-10800, [0, 1, 1, 1, 1, 2]),
   (25920, [0, 1, 1, 4]),
   (41040, [0, 1, 2, 3]),
   (-1080, [0, 2, 2, 2]),
   (-108000, [0, 6]),
   (-5760, [1, 1, 1, 1, 1, 1]),
   (-46080, [1, 1, 1, 3]),
   (51840, [1, 1, 2, 2]),
   (181440, [1, 5]),
   (-77760, [2, 4]),
   (-53280, [3, 3])])]

def skP_J2_3 : SectorVector := [(-1,
  [(8640, [0, 1, 1, 1, 1, 2]),
   (-123120, [0, 1, 1, 4]),
   (131760, [0, 1, 2, 3]),
   (24840, [0, 2, 2, 2]),
   (-237600, [0, 6]),
   (46080, [1, 1, 1, 1, 1, 1]),
   (-97920, [1, 1, 1, 3]),
   (-311040, [1, 1, 2, 2]),
   (907200, [1, 5]),
   (51840, [2, 4]),
   (-53280, [3, 3])]),
 (1,
  [(-8640, [0, 1, 1, 1, 1, 2]),
   (123120, [0, 1, 1, 4]),
   (-131760, [0, 1, 2, 3]),
   (-24840, [0, 2, 2, 2]),
   (237600, [0, 6]),
   (46080, [1, 1, 1, 1, 1, 1]),
   (-97920, [1, 1, 1, 3]),
   (-311040, [1, 1, 2, 2]),
   (907200, [1, 5]),
   (51840, [2, 4]),
   (-53280, [3, 3])])]

def skP_J2_4 : SectorVector := [(1,
  [(-103680, [0, 1, 1, 1, 1, 2]),
   (505440, [0, 1, 1, 4]),
   (362880, [0, 1, 2, 3]),
   (25920, [0, 2, 2, 2]),
   (259200, [0, 6]),
   (-138240, [1, 1, 1, 1, 1, 1]),
   (552960, [1, 1, 1, 3]),
   (155520, [1, 1, 2, 2]),
   (1555200, [1, 5]),
   (622080, [2, 4]),
   (224640, [3, 3])]),
 (-1,
  [(103680, [0, 1, 1, 1, 1, 2]),
   (-505440, [0, 1, 1, 4]),
   (-362880, [0, 1, 2, 3]),
   (-25920, [0, 2, 2, 2]),
   (-259200, [0, 6]),
   (-138240, [1, 1, 1, 1, 1, 1]),
   (552960, [1, 1, 1, 3]),
   (155520, [1, 1, 2, 2]),
   (1555200, [1, 5]),
   (622080, [2, 4]),
   (224640, [3, 3])])]

def skP_J2_5 : SectorVector := [(-1,
  [(1296000, [0, 1, 1, 1, 1, 2]),
   (972000, [0, 1, 1, 4]),
   (1296000, [0, 1, 2, 3]),
   (162000, [0, 2, 2, 2]),
   (162000, [0, 6]),
   (-691200, [1, 1, 1, 1, 1, 1]),
   (-3456000, [1, 1, 1, 3]),
   (-3888000, [1, 1, 2, 2]),
   (-1555200, [1, 5]),
   (-972000, [2, 4]),
   (-432000, [3, 3])]),
 (1,
  [(-1296000, [0, 1, 1, 1, 1, 2]),
   (-972000, [0, 1, 1, 4]),
   (-1296000, [0, 1, 2, 3]),
   (-162000, [0, 2, 2, 2]),
   (-162000, [0, 6]),
   (-691200, [1, 1, 1, 1, 1, 1]),
   (-3456000, [1, 1, 1, 3]),
   (-3888000, [1, 1, 2, 2]),
   (-1555200, [1, 5]),
   (-972000, [2, 4]),
   (-432000, [3, 3])])]

def skP_J2_6 : SectorVector := [(1,
  [(10368000, [0, 1, 1, 1, 1, 2]),
   (7776000, [0, 1, 1, 4]),
   (10368000, [0, 1, 2, 3]),
   (1296000, [0, 2, 2, 2]),
   (1296000, [0, 6]),
   (5529600, [1, 1, 1, 1, 1, 1]),
   (27648000, [1, 1, 1, 3]),
   (31104000, [1, 1, 2, 2]),
   (12441600, [1, 5]),
   (7776000, [2, 4]),
   (3456000, [3, 3])]),
 (-1,
  [(-10368000, [0, 1, 1, 1, 1, 2]),
   (-7776000, [0, 1, 1, 4]),
   (-10368000, [0, 1, 2, 3]),
   (-1296000, [0, 2, 2, 2]),
   (-1296000, [0, 6]),
   (5529600, [1, 1, 1, 1, 1, 1]),
   (27648000, [1, 1, 1, 3]),
   (31104000, [1, 1, 2, 2]),
   (12441600, [1, 5]),
   (7776000, [2, 4]),
   (3456000, [3, 3])])]

def skP_J2_7 : SectorVector := [(-1, []), (1, [])]

def skP_J2_8 : SectorVector := [(1, []), (-1, [])]

def skP_J2_9 : SectorVector := [(-1, []), (1, [])]

def skP_J2_10 : SectorVector := [(1, []), (-1, [])]

def skY_J2 : SectorVector := [(-1,
  [(25890, [0, 1, 1, 1, 1, 2]),
   (19440, [0, 1, 1, 4]),
   (47580, [0, 1, 2, 3]),
   (9735, [0, 2, 2, 2]),
   (10050, [0, 6]),
   (1280, [1, 1, 1, 1, 1, 1]),
   (-74240, [1, 1, 1, 3]),
   (-155520, [1, 1, 2, 2]),
   (-11520, [1, 5]),
   (-4680, [2, 4]),
   (-640, [3, 3])]),
 (1,
  [(-25890, [0, 1, 1, 1, 1, 2]),
   (-19440, [0, 1, 1, 4]),
   (-47580, [0, 1, 2, 3]),
   (-9735, [0, 2, 2, 2]),
   (-10050, [0, 6]),
   (1280, [1, 1, 1, 1, 1, 1]),
   (-74240, [1, 1, 1, 3]),
   (-155520, [1, 1, 2, 2]),
   (-11520, [1, 5]),
   (-4680, [2, 4]),
   (-640, [3, 3])])]

def skQ_J2_0 : SectorVector := [(1,
  [(-9127440, [0, 1, 1, 1, 1, 1]),
   (-74964240, [0, 1, 1, 3]),
   (-72836280, [0, 1, 2, 2]),
   (-9974880, [0, 5]),
   (-235635840, [1, 1, 1, 2]),
   (-158068800, [1, 4]),
   (-111116160, [2, 3])]),
 (-1,
  [(9127440, [0, 1, 1, 1, 1, 1]),
   (74964240, [0, 1, 1, 3]),
   (72836280, [0, 1, 2, 2]),
   (9974880, [0, 5]),
   (-235635840, [1, 1, 1, 2]),
   (-158068800, [1, 4]),
   (-111116160, [2, 3])])]

def skQ_J2_1 : SectorVector := [(-1,
  [(88598880, [0, 1, 1, 1, 1, 1]),
   (474405120, [0, 1, 1, 3]),
   (366904080, [0, 1, 2, 2]),
   (53505360, [0, 5]),
   (-1420951680, [1, 1, 1, 2]),
   (-730308960, [1, 4]),
   (-608826240, [2, 3])]),
 (1,
  [(-88598880, [0, 1, 1, 1, 1, 1]),
   (-474405120, [0, 1, 1, 3]),
   (-366904080, [0, 1, 2, 2]),
   (-53505360, [0, 5]),
   (-1420951680, [1, 1, 1, 2]),
   (-730308960, [1, 4]),
   (-608826240, [2, 3])])]

def skQ_J2_2 : SectorVector := [(1,
  [(-591580800, [0, 1, 1, 1, 1, 1]),
   (-2142154080, [0, 1, 1, 3]),
   (-1574938080, [0, 1, 2, 2]),
   (-285197760, [0, 5]),
   (-7157738880, [1, 1, 1, 2]),
   (-3403296000, [1, 4]),
   (-2452636800, [2, 3])]),
 (-1,
  [(591580800, [0, 1, 1, 1, 1, 1]),
   (2142154080, [0, 1, 1, 3]),
   (1574938080, [0, 1, 2, 2]),
   (285197760, [0, 5]),
   (-7157738880, [1, 1, 1, 2]),
   (-3403296000, [1, 4]),
   (-2452636800, [2, 3])])]

def skQ_J2_3 : SectorVector := [(-1,
  [(2668723200, [0, 1, 1, 1, 1, 1]),
   (7308662400, [0, 1, 1, 3]),
   (5322283200, [0, 1, 2, 2]),
   (1319198400, [0, 5]),
   (-27536371200, [1, 1, 1, 2]),
   (-11918275200, [1, 4]),
   (-7520947200, [2, 3])]),
 (1,
  [(-2668723200, [0, 1, 1, 1, 1, 1]),
   (-7308662400, [0, 1, 1, 3]),
   (-5322283200, [0, 1, 2, 2]),
   (-1319198400, [0, 5]),
   (-27536371200, [1, 1, 1, 2]),
   (-11918275200, [1, 4]),
   (-7520947200, [2, 3])])]

def skQ_J2_4 : SectorVector := [(1,
  [(-6987202560, [0, 1, 1, 1, 1, 1]),
   (-17468006400, [0, 1, 1, 3]),
   (-13101004800, [0, 1, 2, 2]),
   (-2620200960, [0, 5]),
   (-69872025600, [1, 1, 1, 2]),
   (-26202009600, [1, 4]),
   (-17468006400, [2, 3])]),
 (-1,
  [(6987202560, [0, 1, 1, 1, 1, 1]),
   (17468006400, [0, 1, 1, 3]),
   (13101004800, [0, 1, 2, 2]),
   (2620200960, [0, 5]),
   (-69872025600, [1, 1, 1, 2]),
   (-26202009600, [1, 4]),
   (-17468006400, [2, 3])])]

def skQ_J2_5 : SectorVector := [(-1,
  [(7148943360, [0, 1, 1, 1, 1, 1]),
   (17872358400, [0, 1, 1, 3]),
   (13404268800, [0, 1, 2, 2]),
   (2680853760, [0, 5]),
   (-71489433600, [1, 1, 1, 2]),
   (-26808537600, [1, 4]),
   (-17872358400, [2, 3])]),
 (1,
  [(-7148943360, [0, 1, 1, 1, 1, 1]),
   (-17872358400, [0, 1, 1, 3]),
   (-13404268800, [0, 1, 2, 2]),
   (-2680853760, [0, 5]),
   (-71489433600, [1, 1, 1, 2]),
   (-26808537600, [1, 4]),
   (-17872358400, [2, 3])])]

def skQ_J2_6 : SectorVector := [(1, []), (-1, [])]

def skQ_J2_7 : SectorVector := [(-1, []), (1, [])]

def skQ_J2_8 : SectorVector := [(1, []), (-1, [])]

def skQ_J2_9 : SectorVector := [(-1, []), (1, [])]

def skPf_J2 : ℕ → SectorVector
  | 0 => skP_J2_0
  | 1 => skP_J2_1
  | 2 => skP_J2_2
  | 3 => skP_J2_3
  | 4 => skP_J2_4
  | 5 => skP_J2_5
  | 6 => skP_J2_6
  | 7 => skP_J2_7
  | 8 => skP_J2_8
  | 9 => skP_J2_9
  | 10 => skP_J2_10
  | _ => []

def skQf_J2 : ℕ → SectorVector
  | 0 => skQ_J2_0
  | 1 => skQ_J2_1
  | 2 => skQ_J2_2
  | 3 => skQ_J2_3
  | 4 => skQ_J2_4
  | 5 => skQ_J2_5
  | 6 => skQ_J2_6
  | 7 => skQ_J2_7
  | 8 => skQ_J2_8
  | 9 => skQ_J2_9
  | _ => []

set_option maxHeartbeats 4000000 in
theorem skP_J2_0_cert : VectorCertificate (OrbSgl.uTerm true 2 0) skP_J2_0 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_J2_1_cert : VectorCertificate (OrbSgl.uTerm true 2 1) skP_J2_1 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_J2_2_cert : VectorCertificate (OrbSgl.uTerm true 2 2) skP_J2_2 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_J2_3_cert : VectorCertificate (OrbSgl.uTerm true 2 3) skP_J2_3 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_J2_4_cert : VectorCertificate (OrbSgl.uTerm true 2 4) skP_J2_4 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_J2_5_cert : VectorCertificate (OrbSgl.uTerm true 2 5) skP_J2_5 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_J2_6_cert : VectorCertificate (OrbSgl.uTerm true 2 6) skP_J2_6 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_J2_7_cert : VectorCertificate (OrbSgl.uTerm true 2 7) skP_J2_7 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_J2_8_cert : VectorCertificate (OrbSgl.uTerm true 2 8) skP_J2_8 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_J2_9_cert : VectorCertificate (OrbSgl.uTerm true 2 9) skP_J2_9 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skP_J2_10_cert : VectorCertificate (OrbSgl.uTerm true 2 10) skP_J2_10 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skY_J2_cert : VectorCertificate (OrbSgl.uSum 2 skPf_J2) skY_J2 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J2_0_cert : VectorCertificate (OrbSgl.vTerm true skY_J2 2 0) skQ_J2_0 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J2_1_cert : VectorCertificate (OrbSgl.vTerm true skY_J2 2 1) skQ_J2_1 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J2_2_cert : VectorCertificate (OrbSgl.vTerm true skY_J2 2 2) skQ_J2_2 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J2_3_cert : VectorCertificate (OrbSgl.vTerm true skY_J2 2 3) skQ_J2_3 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J2_4_cert : VectorCertificate (OrbSgl.vTerm true skY_J2 2 4) skQ_J2_4 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J2_5_cert : VectorCertificate (OrbSgl.vTerm true skY_J2 2 5) skQ_J2_5 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J2_6_cert : VectorCertificate (OrbSgl.vTerm true skY_J2 2 6) skQ_J2_6 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J2_7_cert : VectorCertificate (OrbSgl.vTerm true skY_J2 2 7) skQ_J2_7 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J2_8_cert : VectorCertificate (OrbSgl.vTerm true skY_J2 2 8) skQ_J2_8 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skQ_J2_9_cert : VectorCertificate (OrbSgl.vTerm true skY_J2 2 9) skQ_J2_9 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem skT_J2_cert : VectorCertificate (OrbSgl.vSum 2 skQf_J2) termJ_2 := by decide +kernel

theorem skY_J2_value : evaluate skY_J2 =
    (V2m 4 four_ge_one).smul (weightNine : LatModuleGen (latP 4)) 2 (aVec true : LatModuleGen (latP 4)) := by
  rw [← vector_eq_of_certificate _ _ skY_J2_cert]
  apply evaluate_uSum true 2 (by norm_num)
  intro i hi
  interval_cases i
  · exact (vector_eq_of_certificate _ _ skP_J2_0_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_J2_1_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_J2_2_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_J2_3_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_J2_4_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_J2_5_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_J2_6_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_J2_7_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_J2_8_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_J2_9_cert).symm
  · exact (vector_eq_of_certificate _ _ skP_J2_10_cert).symm

/-- The certified value of `termJ_2`. -/
theorem sk_J2 : evaluate termJ_2 = ((Nat.choose 15 2 : ℕ) : ℂ) •
    (V2m 4 four_ge_one).smul ((V2m 4 four_ge_one).smul (weightNine : LatModuleGen (latP 4)) 2 (aVec true))
      (6 - (2 : ℕ)) (aVec true : LatModuleGen (latP 4)) := by
  rw [← vector_eq_of_certificate _ _ skT_J2_cert]
  apply evaluate_vSum true 2 (by norm_num) skY_J2 skY_J2_value
  intro j hj
  interval_cases j
  · exact (vector_eq_of_certificate _ _ skQ_J2_0_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J2_1_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J2_2_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J2_3_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J2_4_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J2_5_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J2_6_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J2_7_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J2_8_cert).symm
  · exact (vector_eq_of_certificate _ _ skQ_J2_9_cert).symm

end VOA.Classification.COne.OrbSgl
