import VOA.Classification.COne.OrbIcoZSymbolWords00

/-! Small cached uniform checks for Virasoro words. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option linter.style.longLine false
noncomputable section
namespace VOA.Classification.COne.OrbIcoZ
open VOA OrbOdd OrbZhu Polynomial

def wordCache8 : RawSym := [(0, [[(373176:ℚ), (5112:ℚ)], [(-15551:ℚ), (-143:ℚ)], [(216:ℚ), (1:ℚ)], [(-1:ℚ), (0:ℚ)]]),
 (1, [[(0:ℚ), (0:ℚ)], [(-10512:ℚ), (-144:ℚ)], [(290:ℚ), (2:ℚ)], [(-2:ℚ), (0:ℚ)]]),
 (2, [[(189070:ℚ), (0:ℚ)], [(184:ℚ), (-1:ℚ)], [(-38:ℚ), (1:ℚ)]]),
 (3, [[(10360:ℚ)], [(-5024:ℚ)], [(-82:ℚ)], [(2:ℚ)]]),
 (4, [[(210:ℚ)], [(-169:ℚ)], [(30:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache8_check : equalRawCheck
    (rawScale (rawFactor 2 73) wordCache2 ++
      rawScale (rawSecond 2) (rawShift 2 wordCache2)) wordCache8 = true := by
  decide +kernel

theorem wordCache8_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [2, 1, 1]) = evalSym W k a (symMap wordCache8) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache2_sound W k a, wordCache2_sound W (k - (2 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache8_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

def wordCache9 : RawSym := [(0, [[(5183:ℚ), (144:ℚ), (1:ℚ)], [(-144:ℚ), (-2:ℚ), (0:ℚ)], [(1:ℚ), (0:ℚ), (0:ℚ)]]),
 (2, [[(5110:ℚ), (70:ℚ)], [(76:ℚ), (2:ℚ)], [(-2:ℚ), (0:ℚ)]]),
 (4, [[(1155:ℚ)], [(68:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache9_check : equalRawCheck
    (rawScale (rawFactor 2 73) wordCache3 ++
      rawScale (rawSecond 2) (rawShift 2 wordCache3)) wordCache9 = true := by
  decide +kernel

theorem wordCache9_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [2, 2]) = evalSym W k a (symMap wordCache9) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache3_sound W k a, wordCache3_sound W (k - (2 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache9_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

def wordCache10 : RawSym := [(0, [[(5112:ℚ), (142:ℚ)], [(-143:ℚ), (-2:ℚ)], [(1:ℚ), (0:ℚ)]]),
 (1, [[(0:ℚ), (0:ℚ)], [(-72:ℚ), (-2:ℚ)], [(1:ℚ), (0:ℚ)]]),
 (3, [[(-5180:ℚ)], [(-4:ℚ)], [(1:ℚ)]]),
 (4, [[(-210:ℚ)], [(67:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache10_check : equalRawCheck
    (rawScale (rawFactor 3 72) wordCache1 ++
      rawScale (rawSecond 3) (rawShift 3 wordCache1)) wordCache10 = true := by
  decide +kernel

theorem wordCache10_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [3, 1]) = evalSym W k a (symMap wordCache10) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache1_sound W k a, wordCache1_sound W (k - (3 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache10_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

def wordCache11 : RawSym := [(0, [[(71:ℚ), (3:ℚ)], [(-1:ℚ), (0:ℚ)]]),
 (4, [[(105:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache11_check : equalRawCheck
    (rawScale (rawFactor 4 71) wordCache0 ++
      rawScale (rawSecond 4) (rawShift 4 wordCache0)) wordCache11 = true := by
  decide +kernel

theorem wordCache11_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [4]) = evalSym W k a (symMap wordCache11) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache0_sound W k a, wordCache0_sound W (k - (4 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache11_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

def wordCache12 : RawSym := [(0, [[(-2071126800:ℚ)], [(141911274:ℚ)], [(-3889075:ℚ)], [(53285:ℚ)], [(-365:ℚ)], [(1:ℚ)]]),
 (1, [[(0:ℚ)], [(145854000:ℚ)], [(-7939470:ℚ)], [(162055:ℚ)], [(-1470:ℚ)], [(5:ℚ)]]),
 (2, [[(0:ℚ)], [(4051500:ℚ)], [(-4215770:ℚ)], [(166490:ℚ)], [(-2230:ℚ)], [(10:ℚ)]]),
 (3, [[(0:ℚ)], [(111000:ℚ)], [(-169480:ℚ)], [(59990:ℚ)], [(-1520:ℚ)], [(10:ℚ)]]),
 (4, [[(0:ℚ)], [(2250:ℚ)], [(-4155:ℚ)], [(2305:ℚ)], [(-405:ℚ)], [(5:ℚ)]]),
 (5, [[(0:ℚ)], [(24:ℚ)], [(-50:ℚ)], [(35:ℚ)], [(-10:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache12_check : equalRawCheck
    (rawScale (rawFactor 1 75) wordCache7 ++
      rawScale (rawSecond 1) (rawShift 1 wordCache7)) wordCache12 = true := by
  decide +kernel

theorem wordCache12_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [1, 1, 1, 1, 1]) = evalSym W k a (symMap wordCache12) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache7_sound W k a, wordCache7_sound W (k - (1 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache12_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

def wordCache13 : RawSym := [(0, [[(-27615024:ℚ), (-373176:ℚ)], [(1523950:ℚ), (15551:ℚ)], [(-31535:ℚ), (-216:ℚ)], [(290:ℚ), (1:ℚ)], [(-1:ℚ), (0:ℚ)]]),
 (1, [[(0:ℚ), (0:ℚ)], [(1166832:ℚ), (15768:ℚ)], [(-47958:ℚ), (-435:ℚ)], [(657:ℚ), (3:ℚ)], [(-3:ℚ), (0:ℚ)]]),
 (2, [[(-14180250:ℚ), (0:ℚ)], [(186001:ℚ), (219:ℚ)], [(-7990:ℚ), (-222:ℚ)], [(257:ℚ), (3:ℚ)], [(-2:ℚ), (0:ℚ)]]),
 (3, [[(-1165500:ℚ), (0:ℚ)], [(580888:ℚ), (2:ℚ)], [(1465:ℚ), (-3:ℚ)], [(-271:ℚ), (1:ℚ)], [(2:ℚ), (0:ℚ)]]),
 (4, [[(-47250:ℚ)], [(38655:ℚ)], [(-7257:ℚ)], [(-135:ℚ)], [(3:ℚ)]]),
 (5, [[(-840:ℚ)], [(886:ℚ)], [(-289:ℚ)], [(26:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache13_check : equalRawCheck
    (rawScale (rawFactor 2 74) wordCache4 ++
      rawScale (rawSecond 2) (rawShift 2 wordCache4)) wordCache13 = true := by
  decide +kernel

theorem wordCache13_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [2, 1, 1, 1]) = evalSym W k a (symMap wordCache13) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache4_sound W k a, wordCache4_sound W (k - (2 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache13_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

def wordCache14 : RawSym := [(0, [[(-378288:ℚ), (-10366:ℚ), (-71:ℚ)], [(15694:ℚ), (288:ℚ), (1:ℚ)], [(-217:ℚ), (-2:ℚ), (0:ℚ)], [(1:ℚ), (0:ℚ), (0:ℚ)]]),
 (1, [[(0:ℚ), (0:ℚ), (0:ℚ)], [(5328:ℚ), (146:ℚ), (1:ℚ)], [(-146:ℚ), (-2:ℚ), (0:ℚ)], [(1:ℚ), (0:ℚ), (0:ℚ)]]),
 (2, [[(-378140:ℚ), (-5110:ℚ)], [(-514:ℚ), (-76:ℚ)], [(224:ℚ), (2:ℚ)], [(-2:ℚ), (0:ℚ)]]),
 (3, [[(-10360:ℚ), (-140:ℚ)], [(5024:ℚ), (66:ℚ)], [(82:ℚ), (2:ℚ)], [(-2:ℚ), (0:ℚ)]]),
 (4, [[(-86625:ℚ)], [(-3945:ℚ)], [(-7:ℚ)], [(1:ℚ)]]),
 (5, [[(-4620:ℚ)], [(883:ℚ)], [(64:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache14_check : equalRawCheck
    (rawScale (rawFactor 2 74) wordCache5 ++
      rawScale (rawSecond 2) (rawShift 2 wordCache5)) wordCache14 = true := by
  decide +kernel

theorem wordCache14_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [2, 2, 1]) = evalSym W k a (symMap wordCache14) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache5_sound W k a, wordCache5_sound W (k - (2 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache14_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

def wordCache15 : RawSym := [(0, [[(-373176:ℚ), (-10224:ℚ)], [(15551:ℚ), (286:ℚ)], [(-216:ℚ), (-2:ℚ)], [(1:ℚ), (0:ℚ)]]),
 (1, [[(0:ℚ), (0:ℚ)], [(10512:ℚ), (288:ℚ)], [(-290:ℚ), (-4:ℚ)], [(2:ℚ), (0:ℚ)]]),
 (2, [[(0:ℚ), (0:ℚ)], [(73:ℚ), (2:ℚ)], [(-74:ℚ), (-2:ℚ)], [(1:ℚ), (0:ℚ)]]),
 (3, [[(388500:ℚ)], [(-4880:ℚ)], [(-79:ℚ)], [(1:ℚ)]]),
 (4, [[(31500:ℚ)], [(-10470:ℚ)], [(-16:ℚ)], [(2:ℚ)]]),
 (5, [[(840:ℚ)], [(-478:ℚ)], [(63:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache15_check : equalRawCheck
    (rawScale (rawFactor 3 73) wordCache2 ++
      rawScale (rawSecond 3) (rawShift 3 wordCache2)) wordCache15 = true := by
  decide +kernel

theorem wordCache15_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [3, 1, 1]) = evalSym W k a (symMap wordCache15) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache2_sound W k a, wordCache2_sound W (k - (3 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache15_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

end VOA.Classification.COne.OrbIcoZ
