import VOA.Classification.COne.OrbIcoZSymbolWords02

/-! Small cached uniform checks for Virasoro words. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option linter.style.longLine false
noncomputable section
namespace VOA.Classification.COne.OrbIcoZ
open VOA OrbOdd OrbZhu Polynomial

def wordCache24 : RawSym := [(0, [[(378288:ℚ), (15478:ℚ), (142:ℚ)], [(-15694:ℚ), (-431:ℚ), (-2:ℚ)], [(217:ℚ), (3:ℚ), (0:ℚ)], [(-1:ℚ), (0:ℚ), (0:ℚ)]]),
 (1, [[(0:ℚ), (0:ℚ), (0:ℚ)], [(-5328:ℚ), (-218:ℚ), (-2:ℚ)], [(146:ℚ), (3:ℚ), (0:ℚ)], [(-1:ℚ), (0:ℚ), (0:ℚ)]]),
 (2, [[(189070:ℚ), (5110:ℚ)], [(257:ℚ), (76:ℚ)], [(-112:ℚ), (-2:ℚ)], [(1:ℚ), (0:ℚ)]]),
 (3, [[(-383320:ℚ), (-5040:ℚ)], [(2368:ℚ), (-70:ℚ)], [(38:ℚ), (-1:ℚ)]]),
 (4, [[(-15750:ℚ), (-210:ℚ)], [(5235:ℚ), (67:ℚ)], [(8:ℚ), (1:ℚ)], [(-1:ℚ), (0:ℚ)]]),
 (5, [[(-170240:ℚ)], [(-5512:ℚ)], [(26:ℚ)], [(1:ℚ)]]),
 (6, [[(-11200:ℚ)], [(1730:ℚ)], [(97:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache24_check : equalRawCheck
    (rawScale (rawFactor 3 74) wordCache5 ++
      rawScale (rawSecond 3) (rawShift 3 wordCache5)) wordCache24 = true := by
  decide +kernel

theorem wordCache24_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [3, 2, 1]) = evalSym W k a (symMap wordCache24) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache5_sound W k a, wordCache5_sound W (k - (3 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache24_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

def wordCache25 : RawSym := [(0, [[(5254:ℚ), (290:ℚ), (4:ℚ)], [(-145:ℚ), (-4:ℚ), (0:ℚ)], [(1:ℚ), (0:ℚ), (0:ℚ)]]),
 (3, [[(-10360:ℚ), (-280:ℚ)], [(-8:ℚ), (-4:ℚ)], [(2:ℚ), (0:ℚ)]]),
 (6, [[(4690:ℚ)], [(137:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache25_check : equalRawCheck
    (rawScale (rawFactor 3 74) wordCache6 ++
      rawScale (rawSecond 3) (rawShift 3 wordCache6)) wordCache25 = true := by
  decide +kernel

theorem wordCache25_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [3, 3]) = evalSym W k a (symMap wordCache25) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache6_sound W k a, wordCache6_sound W (k - (3 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache25_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

def wordCache26 : RawSym := [(0, [[(373176:ℚ), (15336:ℚ)], [(-15551:ℚ), (-429:ℚ)], [(216:ℚ), (3:ℚ)], [(-1:ℚ), (0:ℚ)]]),
 (1, [[(0:ℚ), (0:ℚ)], [(-10512:ℚ), (-432:ℚ)], [(290:ℚ), (6:ℚ)], [(-2:ℚ), (0:ℚ)]]),
 (2, [[(0:ℚ), (0:ℚ)], [(-73:ℚ), (-3:ℚ)], [(74:ℚ), (3:ℚ)], [(-1:ℚ), (0:ℚ)]]),
 (4, [[(598500:ℚ)], [(-10155:ℚ)], [(-46:ℚ)], [(1:ℚ)]]),
 (5, [[(63840:ℚ)], [(-16192:ℚ)], [(50:ℚ)], [(2:ℚ)]]),
 (6, [[(2100:ℚ)], [(-925:ℚ)], [(96:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache26_check : equalRawCheck
    (rawScale (rawFactor 4 73) wordCache2 ++
      rawScale (rawSecond 4) (rawShift 4 wordCache2)) wordCache26 = true := by
  decide +kernel

theorem wordCache26_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [4, 1, 1]) = evalSym W k a (symMap wordCache26) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache2_sound W k a, wordCache2_sound W (k - (4 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache26_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

def wordCache27 : RawSym := [(0, [[(5183:ℚ), (286:ℚ), (3:ℚ)], [(-144:ℚ), (-4:ℚ), (0:ℚ)], [(1:ℚ), (0:ℚ), (0:ℚ)]]),
 (2, [[(2555:ℚ), (105:ℚ)], [(38:ℚ), (3:ℚ)], [(-1:ℚ), (0:ℚ)]]),
 (4, [[(7875:ℚ), (105:ℚ)], [(-30:ℚ), (1:ℚ)], [(-1:ℚ), (0:ℚ)]]),
 (6, [[(3255:ℚ)], [(136:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache27_check : equalRawCheck
    (rawScale (rawFactor 4 73) wordCache3 ++
      rawScale (rawSecond 4) (rawShift 4 wordCache3)) wordCache27 = true := by
  decide +kernel

theorem wordCache27_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [4, 2]) = evalSym W k a (symMap wordCache27) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache3_sound W k a, wordCache3_sound W (k - (4 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache27_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

def wordCache28 : RawSym := [(0, [[(5112:ℚ), (284:ℚ)], [(-143:ℚ), (-4:ℚ)], [(1:ℚ), (0:ℚ)]]),
 (1, [[(0:ℚ), (0:ℚ)], [(-72:ℚ), (-4:ℚ)], [(1:ℚ), (0:ℚ)]]),
 (5, [[(-10640:ℚ)], [(64:ℚ)], [(1:ℚ)]]),
 (6, [[(-700:ℚ)], [(135:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache28_check : equalRawCheck
    (rawScale (rawFactor 5 72) wordCache1 ++
      rawScale (rawSecond 5) (rawShift 5 wordCache1)) wordCache28 = true := by
  decide +kernel

theorem wordCache28_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [5, 1]) = evalSym W k a (symMap wordCache28) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache1_sound W k a, wordCache1_sound W (k - (5 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache28_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

def wordCache29 : RawSym := [(0, [[(71:ℚ), (5:ℚ)], [(-1:ℚ), (0:ℚ)]]),
 (6, [[(175:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache29_check : equalRawCheck
    (rawScale (rawFactor 6 71) wordCache0 ++
      rawScale (rawSecond 6) (rawShift 6 wordCache0)) wordCache29 = true := by
  decide +kernel

theorem wordCache29_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [6]) = evalSym W k a (symMap wordCache29) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache0_sound W k a, wordCache0_sound W (k - (6 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache29_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

def wordCache30 : RawSym := [(0, [[(-12120234033600:ℚ)], [(1147347175848:ℚ)], [(-46542418622:ℚ)], [(1048763569:ℚ)], [(-14177660:ℚ)], [(114982:ℚ)], [(-518:ℚ)], [(1:ℚ)]]),
 (1, [[(0:ℚ)], [(1194952651200:ℚ)], [(-96288416616:ℚ)], [(3232514278:ℚ)], [(-57870855:ℚ)], [(582715:ℚ)], [(-3129:ℚ)], [(7:ℚ)]]),
 (2, [[(0:ℚ)], [(49789693800:ℚ)], [(-53110187634:ℚ)], [(3409063959:ℚ)], [(-89751270:ℚ)], [(1189020:ℚ)], [(-7896:ℚ)], [(21:ℚ)]]),
 (3, [[(0:ℚ)], [(2273502000:ℚ)], [(-3530729860:ℚ)], [(1319860220:ℚ)], [(-63850465:ℚ)], [(1228745:ℚ)], [(-10675:ℚ)], [(35:ℚ)]]),
 (4, [[(0:ℚ)], [(92169000:ℚ)], [(-172615170:ℚ)], [(98887775:ℚ)], [(-19088160:ℚ)], [(654710:ℚ)], [(-8190:ℚ)], [(35:ℚ)]]),
 (5, [[(0:ℚ)], [(2949408:ℚ)], [(-6221712:ℚ)], [(4462374:ℚ)], [(-1342425:ℚ)], [(155757:ℚ)], [(-3423:ℚ)], [(21:ℚ)]]),
 (6, [[(0:ℚ)], [(64680:ℚ)], [(-148526:ℚ)], [(123193:ℚ)], [(-47390:ℚ)], [(8680:ℚ)], [(-644:ℚ)], [(7:ℚ)]]),
 (7, [[(0:ℚ)], [(720:ℚ)], [(-1764:ℚ)], [(1624:ℚ)], [(-735:ℚ)], [(175:ℚ)], [(-21:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache30_check : equalRawCheck
    (rawScale (rawFactor 1 77) wordCache19 ++
      rawScale (rawSecond 1) (rawShift 1 wordCache19)) wordCache30 = true := by
  decide +kernel

theorem wordCache30_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [1, 1, 1, 1, 1, 1, 1]) = evalSym W k a (symMap wordCache30) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache19_sound W k a, wordCache19_sound W (k - (1 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache30_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

def wordCache31 : RawSym := [(0, [[(-157405636800:ℚ), (-2071126800:ℚ)], [(12856383624:ℚ), (141911274:ℚ)], [(-437480974:ℚ), (-3889075:ℚ)], [(7938735:ℚ), (53285:ℚ)], [(-81025:ℚ), (-365:ℚ)], [(441:ℚ), (1:ℚ)], [(-1:ℚ), (0:ℚ)]]),
 (1, [[(0:ℚ), (0:ℚ)], [(11084904000:ℚ), (145854000:ℚ)], [(-749253720:ℚ), (-7939470:ℚ)], [(20255650:ℚ), (162055:ℚ)], [(-273775:ℚ), (-1470:ℚ)], [(1850:ℚ), (5:ℚ)], [(-5:ℚ), (0:ℚ)]]),
 (2, [[(-82982823000:ℚ), (0:ℚ)], [(3471132590:ℚ), (4051500:ℚ)], [(-313948141:ℚ), (-4215770:ℚ)], [(14619960:ℚ), (166490:ℚ)], [(-292850:ℚ), (-2230:ℚ)], [(2650:ℚ), (10:ℚ)], [(-9:ℚ), (0:ℚ)]]),
 (3, [[(-11367510000:ℚ), (0:ℚ)], [(5969789300:ℚ), (111000:ℚ)], [(-146549300:ℚ), (-169480:ℚ)], [(1871765:ℚ), (59990:ℚ)], [(-54695:ℚ), (-1520:ℚ)], [(935:ℚ), (10:ℚ)], [(-5:ℚ), (0:ℚ)]]),
 (4, [[(-921690000:ℚ), (0:ℚ)], [(778298700:ℚ), (2250:ℚ)], [(-161749460:ℚ), (-4155:ℚ)], [(1375855:ℚ), (2305:ℚ)], [(70095:ℚ), (-405:ℚ)], [(-1195:ℚ), (5:ℚ)], [(5:ℚ), (0:ℚ)]]),
 (5, [[(-49156800:ℚ), (0:ℚ)], [(53135744:ℚ), (24:ℚ)], [(-18280084:ℚ), (-50:ℚ)], [(1975260:ℚ), (35:ℚ)], [(15055:ℚ), (-10:ℚ)], [(-1184:ℚ), (1:ℚ)], [(9:ℚ), (0:ℚ)]]),
 (6, [[(-1617000:ℚ)], [(2049950:ℚ)], [(-923785:ℚ)], [(172970:ℚ)], [(-10180:ℚ)], [(-280:ℚ)], [(5:ℚ)]]),
 (7, [[(-25200:ℚ)], [(35820:ℚ)], [(-19256:ℚ)], [(4845:ℚ)], [(-545:ℚ)], [(15:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache31_check : equalRawCheck
    (rawScale (rawFactor 2 76) wordCache12 ++
      rawScale (rawSecond 2) (rawShift 2 wordCache12)) wordCache31 = true := by
  decide +kernel

theorem wordCache31_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [2, 1, 1, 1, 1, 1]) = evalSym W k a (symMap wordCache31) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache12_sound W k a, wordCache12_sound W (k - (2 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache31_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

end VOA.Classification.COne.OrbIcoZ
