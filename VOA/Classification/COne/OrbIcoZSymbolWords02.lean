import VOA.Classification.COne.OrbIcoZSymbolWords01

/-! Small cached uniform checks for Virasoro words. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option linter.style.longLine false
noncomputable section
namespace VOA.Classification.COne.OrbIcoZ
open VOA OrbOdd OrbZhu Polynomial

def wordCache16 : RawSym := [(0, [[(-5183:ℚ), (-215:ℚ), (-2:ℚ)], [(144:ℚ), (3:ℚ), (0:ℚ)], [(-1:ℚ), (0:ℚ), (0:ℚ)]]),
 (2, [[(-2555:ℚ), (-70:ℚ)], [(-38:ℚ), (-2:ℚ)], [(1:ℚ), (0:ℚ)]]),
 (3, [[(5180:ℚ), (70:ℚ)], [(4:ℚ), (1:ℚ)], [(-1:ℚ), (0:ℚ)]]),
 (5, [[(2240:ℚ)], [(102:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache16_check : equalRawCheck
    (rawScale (rawFactor 3 73) wordCache3 ++
      rawScale (rawSecond 3) (rawShift 3 wordCache3)) wordCache16 = true := by
  decide +kernel

theorem wordCache16_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [3, 2]) = evalSym W k a (symMap wordCache16) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache3_sound W k a, wordCache3_sound W (k - (3 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache16_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

def wordCache17 : RawSym := [(0, [[(-5112:ℚ), (-213:ℚ)], [(143:ℚ), (3:ℚ)], [(-1:ℚ), (0:ℚ)]]),
 (1, [[(0:ℚ), (0:ℚ)], [(72:ℚ), (3:ℚ)], [(-1:ℚ), (0:ℚ)]]),
 (4, [[(-7875:ℚ)], [(30:ℚ)], [(1:ℚ)]]),
 (5, [[(-420:ℚ)], [(101:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache17_check : equalRawCheck
    (rawScale (rawFactor 4 72) wordCache1 ++
      rawScale (rawSecond 4) (rawShift 4 wordCache1)) wordCache17 = true := by
  decide +kernel

theorem wordCache17_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [4, 1]) = evalSym W k a (symMap wordCache17) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache1_sound W k a, wordCache1_sound W (k - (4 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache17_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

def wordCache18 : RawSym := [(0, [[(-71:ℚ), (-4:ℚ)], [(1:ℚ), (0:ℚ)]]),
 (5, [[(140:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache18_check : equalRawCheck
    (rawScale (rawFactor 5 71) wordCache0 ++
      rawScale (rawSecond 5) (rawShift 5 wordCache0)) wordCache18 = true := by
  decide +kernel

theorem wordCache18_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [5]) = evalSym W k a (symMap wordCache18) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache0_sound W k a, wordCache0_sound W (k - (5 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache18_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

def wordCache19 : RawSym := [(0, [[(157405636800:ℚ)], [(-12856383624:ℚ)], [(437480974:ℚ)], [(-7938735:ℚ)], [(81025:ℚ)], [(-441:ℚ)], [(1:ℚ)]]),
 (1, [[(0:ℚ)], [(-13301884800:ℚ)], [(899104464:ℚ)], [(-24306780:ℚ)], [(328530:ℚ)], [(-2220:ℚ)], [(6:ℚ)]]),
 (2, [[(0:ℚ)], [(-461871000:ℚ)], [(486675030:ℚ)], [(-25303515:ℚ)], [(503955:ℚ)], [(-4485:ℚ)], [(15:ℚ)]]),
 (3, [[(0:ℚ)], [(-16872000:ℚ)], [(25982960:ℚ)], [(-9457440:ℚ)], [(351020:ℚ)], [(-4560:ℚ)], [(20:ℚ)]]),
 (4, [[(0:ℚ)], [(-513000:ℚ)], [(954090:ℚ)], [(-538005:ℚ)], [(99255:ℚ)], [(-2355:ℚ)], [(15:ℚ)]]),
 (5, [[(0:ℚ)], [(-10944:ℚ)], [(22944:ℚ)], [(-16260:ℚ)], [(4770:ℚ)], [(-516:ℚ)], [(6:ℚ)]]),
 (6, [[(0:ℚ)], [(-120:ℚ)], [(274:ℚ)], [(-225:ℚ)], [(85:ℚ)], [(-15:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache19_check : equalRawCheck
    (rawScale (rawFactor 1 76) wordCache12 ++
      rawScale (rawSecond 1) (rawShift 1 wordCache12)) wordCache19 = true := by
  decide +kernel

theorem wordCache19_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [1, 1, 1, 1, 1, 1]) = evalSym W k a (symMap wordCache19) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache12_sound W k a, wordCache12_sound W (k - (1 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache19_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

def wordCache20 : RawSym := [(0, [[(2071126800:ℚ), (27615024:ℚ)], [(-141911274:ℚ), (-1523950:ℚ)], [(3889075:ℚ), (31535:ℚ)], [(-53285:ℚ), (-290:ℚ)], [(365:ℚ), (1:ℚ)], [(-1:ℚ), (0:ℚ)]]),
 (1, [[(0:ℚ), (0:ℚ)], [(-116683200:ℚ), (-1555776:ℚ)], [(6351576:ℚ), (63944:ℚ)], [(-129644:ℚ), (-876:ℚ)], [(1176:ℚ), (4:ℚ)], [(-4:ℚ), (0:ℚ)]]),
 (2, [[(1077699000:ℚ), (0:ℚ)], [(-29515570:ℚ), (-32412:ℚ)], [(2041325:ℚ), (33294:ℚ)], [(-77025:ℚ), (-888:ℚ)], [(1075:ℚ), (6:ℚ)], [(-5:ℚ), (0:ℚ)]]),
 (3, [[(118104000:ℚ), (0:ℚ)], [(-60446720:ℚ), (-592:ℚ)], [(670960:ℚ), (896:ℚ)], [(13520:ℚ), (-308:ℚ)], [(-160:ℚ), (4:ℚ)]]),
 (4, [[(7182000:ℚ), (0:ℚ)], [(-5970510:ℚ), (-6:ℚ)], [(1181205:ℚ), (11:ℚ)], [(5545:ℚ), (-6:ℚ)], [(-645:ℚ), (1:ℚ)], [(5:ℚ), (0:ℚ)]]),
 (5, [[(255360:ℚ)], [(-272704:ℚ)], [(91400:ℚ)], [(-9060:ℚ)], [(-200:ℚ)], [(4:ℚ)]]),
 (6, [[(4200:ℚ)], [(-5270:ℚ)], [(2331:ℚ)], [(-419:ℚ)], [(21:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache20_check : equalRawCheck
    (rawScale (rawFactor 2 75) wordCache7 ++
      rawScale (rawSecond 2) (rawShift 2 wordCache7)) wordCache20 = true := by
  decide +kernel

theorem wordCache20_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [2, 1, 1, 1, 1]) = evalSym W k a (symMap wordCache20) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache7_sound W k a, wordCache7_sound W (k - (2 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache20_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

def wordCache21 : RawSym := [(0, [[(27988200:ℚ), (756576:ℚ), (5112:ℚ)], [(-1539501:ℚ), (-31388:ℚ), (-143:ℚ)], [(31751:ℚ), (434:ℚ), (1:ℚ)], [(-291:ℚ), (-2:ℚ), (0:ℚ)], [(1:ℚ), (0:ℚ), (0:ℚ)]]),
 (1, [[(0:ℚ), (0:ℚ), (0:ℚ)], [(-788400:ℚ), (-21312:ℚ), (-144:ℚ)], [(32262:ℚ), (584:ℚ), (2:ℚ)], [(-440:ℚ), (-4:ℚ), (0:ℚ)], [(2:ℚ), (0:ℚ), (0:ℚ)]]),
 (2, [[(28360500:ℚ), (378140:ℚ), (0:ℚ)], [(-345065:ℚ), (366:ℚ), (-1:ℚ)], [(-11691:ℚ), (-74:ℚ), (1:ℚ)], [(225:ℚ), (0:ℚ), (0:ℚ)], [(-1:ℚ), (0:ℚ), (0:ℚ)]]),
 (3, [[(1554000:ℚ), (20720:ℚ)], [(-774320:ℚ), (-10048:ℚ)], [(-2252:ℚ), (-164:ℚ)], [(464:ℚ), (4:ℚ)], [(-4:ℚ), (0:ℚ)]]),
 (4, [[(6615000:ℚ), (420:ℚ)], [(187425:ℚ), (-338:ℚ)], [(1425:ℚ), (60:ℚ)], [(7:ℚ), (2:ℚ)], [(-1:ℚ), (0:ℚ)]]),
 (5, [[(702240:ℚ)], [(-143456:ℚ)], [(-7962:ℚ)], [(-24:ℚ)], [(2:ℚ)]]),
 (6, [[(23100:ℚ)], [(-9035:ℚ)], [(563:ℚ)], [(59:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache21_check : equalRawCheck
    (rawScale (rawFactor 2 75) wordCache8 ++
      rawScale (rawSecond 2) (rawShift 2 wordCache8)) wordCache21 = true := by
  decide +kernel

theorem wordCache21_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [2, 2, 1, 1]) = evalSym W k a (symMap wordCache21) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache8_sound W k a, wordCache8_sound W (k - (2 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache21_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

def wordCache22 : RawSym := [(0, [[(388725:ℚ), (15983:ℚ), (219:ℚ), (1:ℚ)], [(-15983:ℚ), (-438:ℚ), (-3:ℚ), (0:ℚ)], [(219:ℚ), (3:ℚ), (0:ℚ), (0:ℚ)], [(-1:ℚ), (0:ℚ), (0:ℚ), (0:ℚ)]]),
 (2, [[(574875:ℚ), (15540:ℚ), (105:ℚ)], [(885:ℚ), (234:ℚ), (3:ℚ)], [(-339:ℚ), (-6:ℚ), (0:ℚ)], [(3:ℚ), (0:ℚ), (0:ℚ)]]),
 (4, [[(259875:ℚ), (3465:ℚ)], [(11835:ℚ), (204:ℚ)], [(21:ℚ), (3:ℚ)], [(-3:ℚ), (0:ℚ)]]),
 (6, [[(35805:ℚ)], [(3263:ℚ)], [(99:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache22_check : equalRawCheck
    (rawScale (rawFactor 2 75) wordCache9 ++
      rawScale (rawSecond 2) (rawShift 2 wordCache9)) wordCache22 = true := by
  decide +kernel

theorem wordCache22_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [2, 2, 2]) = evalSym W k a (symMap wordCache22) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache9_sound W k a, wordCache9_sound W (k - (2 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache22_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

def wordCache23 : RawSym := [(0, [[(27615024:ℚ), (746352:ℚ)], [(-1523950:ℚ), (-31102:ℚ)], [(31535:ℚ), (432:ℚ)], [(-290:ℚ), (-2:ℚ)], [(1:ℚ), (0:ℚ)]]),
 (1, [[(0:ℚ), (0:ℚ)], [(-1166832:ℚ), (-31536:ℚ)], [(47958:ℚ), (870:ℚ)], [(-657:ℚ), (-6:ℚ)], [(3:ℚ), (0:ℚ)]]),
 (2, [[(0:ℚ), (0:ℚ)], [(-16206:ℚ), (-438:ℚ)], [(16647:ℚ), (444:ℚ)], [(-444:ℚ), (-6:ℚ)], [(3:ℚ), (0:ℚ)]]),
 (3, [[(-29526000:ℚ), (0:ℚ)], [(759232:ℚ), (-4:ℚ)], [(1348:ℚ), (6:ℚ)], [(-232:ℚ), (-2:ℚ)], [(2:ℚ), (0:ℚ)]]),
 (4, [[(-3591000:ℚ)], [(1240830:ℚ)], [(-13881:ℚ)], [(-252:ℚ)], [(3:ℚ)]]),
 (5, [[(-191520:ℚ)], [(111504:ℚ)], [(-15798:ℚ)], [(-39:ℚ)], [(3:ℚ)]]),
 (6, [[(-4200:ℚ)], [(3230:ℚ)], [(-793:ℚ)], [(58:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache23_check : equalRawCheck
    (rawScale (rawFactor 3 74) wordCache4 ++
      rawScale (rawSecond 3) (rawShift 3 wordCache4)) wordCache23 = true := by
  decide +kernel

theorem wordCache23_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [3, 1, 1, 1]) = evalSym W k a (symMap wordCache23) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache4_sound W k a, wordCache4_sound W (k - (3 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache23_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

end VOA.Classification.COne.OrbIcoZ
