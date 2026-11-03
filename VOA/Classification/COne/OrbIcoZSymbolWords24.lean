import VOA.Classification.COne.OrbIcoZSymbolWords23

/-! Small cached uniform checks for Virasoro words. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option linter.style.longLine false
noncomputable section
namespace VOA.Classification.COne.OrbIcoZ
open VOA OrbOdd OrbZhu Polynomial

def wordCache192 : RawSym := [(0, [[(-388725:ℚ), (-52264:ℚ), (-1227:ℚ), (-8:ℚ)], [(15983:ℚ), (1446:ℚ), (17:ℚ), (0:ℚ)], [(-219:ℚ), (-10:ℚ), (0:ℚ), (0:ℚ)], [(1:ℚ), (0:ℚ), (0:ℚ), (0:ℚ)]]),
 (2, [[(-383250:ℚ), (-46130:ℚ), (-560:ℚ)], [(-590:ℚ), (-688:ℚ), (-16:ℚ)], [(226:ℚ), (18:ℚ), (0:ℚ)], [(-2:ℚ), (0:ℚ), (0:ℚ)]]),
 (4, [[(-86625:ℚ), (-9240:ℚ)], [(-3945:ℚ), (-544:ℚ)], [(-7:ℚ), (-8:ℚ)], [(1:ℚ), (0:ℚ)]]),
 (9, [[(1836800:ℚ), (45360:ℚ), (280:ℚ)], [(-38800:ℚ), (-398:ℚ), (1:ℚ)], [(118:ℚ), (-2:ℚ), (0:ℚ)], [(1:ℚ), (0:ℚ), (0:ℚ)]]),
 (11, [[(1193920:ℚ), (14560:ℚ)], [(35624:ℚ), (612:ℚ)], [(-448:ℚ), (2:ℚ)], [(-2:ℚ), (0:ℚ)]]),
 (13, [[(174720:ℚ)], [(14624:ℚ)], [(330:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache192_check : equalRawCheck
    (rawScale (rawFactor 9 75) wordCache9 ++
      rawScale (rawSecond 9) (rawShift 9 wordCache9)) wordCache192 = true := by
  decide +kernel

theorem wordCache192_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [9, 2, 2]) = evalSym W k a (symMap wordCache192) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache9_sound W k a, wordCache9_sound W (k - (9 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache192_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

def wordCache193 : RawSym := [(0, [[(-383400:ℚ), (-51546:ℚ), (-1136:ℚ)], [(15837:ℚ), (1436:ℚ), (16:ℚ)], [(-218:ℚ), (-10:ℚ), (0:ℚ)], [(1:ℚ), (0:ℚ), (0:ℚ)]]),
 (1, [[(0:ℚ), (0:ℚ), (0:ℚ)], [(5400:ℚ), (726:ℚ), (16:ℚ)], [(-147:ℚ), (-10:ℚ), (0:ℚ)], [(1:ℚ), (0:ℚ), (0:ℚ)]]),
 (3, [[(388500:ℚ), (41440:ℚ)], [(-4880:ℚ), (32:ℚ)], [(-79:ℚ), (-8:ℚ)], [(1:ℚ), (0:ℚ)]]),
 (4, [[(15750:ℚ), (1680:ℚ)], [(-5235:ℚ), (-536:ℚ)], [(-8:ℚ), (-8:ℚ)], [(1:ℚ), (0:ℚ)]]),
 (9, [[(1814400:ℚ), (44800:ℚ)], [(-38600:ℚ), (-400:ℚ)], [(119:ℚ), (-2:ℚ)], [(1:ℚ), (0:ℚ)]]),
 (10, [[(204120:ℚ), (5040:ℚ)], [(-24471:ℚ), (-542:ℚ)], [(190:ℚ), (-2:ℚ)], [(1:ℚ), (0:ℚ)]]),
 (12, [[(-1417640:ℚ)], [(-11223:ℚ)], [(258:ℚ)], [(1:ℚ)]]),
 (13, [[(-204960:ℚ)], [(12988:ℚ)], [(329:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache193_check : equalRawCheck
    (rawScale (rawFactor 9 75) wordCache10 ++
      rawScale (rawSecond 9) (rawShift 9 wordCache10)) wordCache193 = true := by
  decide +kernel

theorem wordCache193_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [9, 3, 1]) = evalSym W k a (symMap wordCache193) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache10_sound W k a, wordCache10_sound W (k - (9 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache193_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

def wordCache194 : RawSym := [(0, [[(-5325:ℚ), (-793:ℚ), (-24:ℚ)], [(146:ℚ), (11:ℚ), (0:ℚ)], [(-1:ℚ), (0:ℚ), (0:ℚ)]]),
 (4, [[(-7875:ℚ), (-840:ℚ)], [(30:ℚ), (-8:ℚ)], [(1:ℚ), (0:ℚ)]]),
 (9, [[(22400:ℚ), (840:ℚ)], [(-200:ℚ), (3:ℚ)], [(-1:ℚ), (0:ℚ)]]),
 (13, [[(26880:ℚ)], [(376:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache194_check : equalRawCheck
    (rawScale (rawFactor 9 75) wordCache11 ++
      rawScale (rawSecond 9) (rawShift 9 wordCache11)) wordCache194 = true := by
  decide +kernel

theorem wordCache194_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [9, 4]) = evalSym W k a (symMap wordCache194) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache11_sound W k a, wordCache11_sound W (k - (9 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache194_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

def wordCache195 : RawSym := [(0, [[(-27615024:ℚ), (-3358584:ℚ)], [(1523950:ℚ), (139959:ℚ)], [(-31535:ℚ), (-1944:ℚ)], [(290:ℚ), (9:ℚ)], [(-1:ℚ), (0:ℚ)]]),
 (1, [[(0:ℚ), (0:ℚ)], [(1166832:ℚ), (141912:ℚ)], [(-47958:ℚ), (-3915:ℚ)], [(657:ℚ), (27:ℚ)], [(-3:ℚ), (0:ℚ)]]),
 (2, [[(0:ℚ), (0:ℚ)], [(16206:ℚ), (1971:ℚ)], [(-16647:ℚ), (-1998:ℚ)], [(444:ℚ), (27:ℚ)], [(-3:ℚ), (0:ℚ)]]),
 (3, [[(0:ℚ), (0:ℚ)], [(148:ℚ), (18:ℚ)], [(-224:ℚ), (-27:ℚ)], [(77:ℚ), (9:ℚ)], [(-1:ℚ), (0:ℚ)]]),
 (10, [[(-173655090:ℚ)], [(5802579:ℚ)], [(-57319:ℚ)], [(69:ℚ)], [(1:ℚ)]]),
 (11, [[(-64316700:ℚ)], [(7786740:ℚ)], [(-140007:ℚ)], [(420:ℚ)], [(3:ℚ)]]),
 (12, [[(-8627850:ℚ)], [(1723695:ℚ)], [(-92721:ℚ)], [(633:ℚ)], [(3:ℚ)]]),
 (13, [[(-415800:ℚ)], [(112710:ℚ)], [(-10033:ℚ)], [(282:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache195_check : equalRawCheck
    (rawScale (rawFactor 10 74) wordCache4 ++
      rawScale (rawSecond 10) (rawShift 10 wordCache4)) wordCache195 = true := by
  decide +kernel

theorem wordCache195_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [10, 1, 1, 1]) = evalSym W k a (symMap wordCache195) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache4_sound W k a, wordCache4_sound W (k - (10 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache195_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

def wordCache196 : RawSym := [(0, [[(-378288:ℚ), (-51262:ℚ), (-639:ℚ)], [(15694:ℚ), (1432:ℚ), (9:ℚ)], [(-217:ℚ), (-10:ℚ), (0:ℚ)], [(1:ℚ), (0:ℚ), (0:ℚ)]]),
 (1, [[(0:ℚ), (0:ℚ), (0:ℚ)], [(5328:ℚ), (722:ℚ), (9:ℚ)], [(-146:ℚ), (-10:ℚ), (0:ℚ)], [(1:ℚ), (0:ℚ), (0:ℚ)]]),
 (2, [[(-189070:ℚ), (-22995:ℚ)], [(-257:ℚ), (-342:ℚ)], [(112:ℚ), (9:ℚ)], [(-1:ℚ), (0:ℚ)]]),
 (3, [[(-5180:ℚ), (-630:ℚ)], [(2512:ℚ), (297:ℚ)], [(41:ℚ), (9:ℚ)], [(-1:ℚ), (0:ℚ)]]),
 (10, [[(-2092230:ℚ), (-25515:ℚ)], [(44703:ℚ), (234:ℚ)], [(-152:ℚ), (1:ℚ)], [(-1:ℚ), (0:ℚ)]]),
 (11, [[(-258300:ℚ), (-3150:ℚ)], [(28160:ℚ), (305:ℚ)], [(-223:ℚ), (1:ℚ)], [(-1:ℚ), (0:ℚ)]]),
 (12, [[(-653625:ℚ)], [(-20345:ℚ)], [(257:ℚ)], [(1:ℚ)]]),
 (13, [[(-94500:ℚ)], [(3795:ℚ)], [(328:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache196_check : equalRawCheck
    (rawScale (rawFactor 10 74) wordCache5 ++
      rawScale (rawSecond 10) (rawShift 10 wordCache5)) wordCache196 = true := by
  decide +kernel

theorem wordCache196_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [10, 2, 1]) = evalSym W k a (symMap wordCache196) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache5_sound W k a, wordCache5_sound W (k - (10 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache196_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

def wordCache197 : RawSym := [(0, [[(-5254:ℚ), (-787:ℚ), (-18:ℚ)], [(145:ℚ), (11:ℚ), (0:ℚ)], [(-1:ℚ), (0:ℚ), (0:ℚ)]]),
 (3, [[(5180:ℚ), (630:ℚ)], [(4:ℚ), (9:ℚ)], [(-1:ℚ), (0:ℚ)]]),
 (10, [[(-25515:ℚ), (-630:ℚ)], [(234:ℚ), (-2:ℚ)], [(1:ℚ), (0:ℚ)]]),
 (13, [[(18900:ℚ)], [(375:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache197_check : equalRawCheck
    (rawScale (rawFactor 10 74) wordCache6 ++
      rawScale (rawSecond 10) (rawShift 10 wordCache6)) wordCache197 = true := by
  decide +kernel

theorem wordCache197_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [10, 3]) = evalSym W k a (symMap wordCache197) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache6_sound W k a, wordCache6_sound W (k - (10 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache197_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

def wordCache198 : RawSym := [(0, [[(-373176:ℚ), (-51120:ℚ)], [(15551:ℚ), (1430:ℚ)], [(-216:ℚ), (-10:ℚ)], [(1:ℚ), (0:ℚ)]]),
 (1, [[(0:ℚ), (0:ℚ)], [(10512:ℚ), (1440:ℚ)], [(-290:ℚ), (-20:ℚ)], [(2:ℚ), (0:ℚ)]]),
 (2, [[(0:ℚ), (0:ℚ)], [(73:ℚ), (10:ℚ)], [(-74:ℚ), (-10:ℚ)], [(1:ℚ), (0:ℚ)]]),
 (11, [[(2382100:ℚ)], [(-50944:ℚ)], [(185:ℚ)], [(1:ℚ)]]),
 (12, [[(639100:ℚ)], [(-63974:ℚ)], [(512:ℚ)], [(2:ℚ)]]),
 (13, [[(46200:ℚ)], [(-7918:ℚ)], [(327:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache198_check : equalRawCheck
    (rawScale (rawFactor 11 73) wordCache2 ++
      rawScale (rawSecond 11) (rawShift 11 wordCache2)) wordCache198 = true := by
  decide +kernel

theorem wordCache198_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [11, 1, 1]) = evalSym W k a (symMap wordCache198) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache2_sound W k a, wordCache2_sound W (k - (11 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache198_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

def wordCache199 : RawSym := [(0, [[(-5183:ℚ), (-783:ℚ), (-10:ℚ)], [(144:ℚ), (11:ℚ), (0:ℚ)], [(-1:ℚ), (0:ℚ), (0:ℚ)]]),
 (2, [[(-2555:ℚ), (-350:ℚ)], [(-38:ℚ), (-10:ℚ)], [(1:ℚ), (0:ℚ)]]),
 (11, [[(28700:ℚ), (350:ℚ)], [(-268:ℚ), (1:ℚ)], [(-1:ℚ), (0:ℚ)]]),
 (13, [[(8400:ℚ)], [(374:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache199_check : equalRawCheck
    (rawScale (rawFactor 11 73) wordCache3 ++
      rawScale (rawSecond 11) (rawShift 11 wordCache3)) wordCache199 = true := by
  decide +kernel

theorem wordCache199_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [11, 2]) = evalSym W k a (symMap wordCache199) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache3_sound W k a, wordCache3_sound W (k - (11 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache199_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

end VOA.Classification.COne.OrbIcoZ
