import VOA.Classification.COne.OrbIcoZSymbolChecks

/-! Small cached uniform checks for Virasoro words. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option linter.style.longLine false
noncomputable section
namespace VOA.Classification.COne.OrbIcoZ
open VOA OrbOdd OrbZhu Polynomial

def wordCache0 : RawSym := [(0, [[(1:ℚ)]])]

theorem wordCache0_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord []) = evalSym W k a (symMap wordCache0) := by
  simp [wordCache0, symWord, symMap, bp, qp]

def wordCache1 : RawSym := [(0, [[(-71:ℚ)], [(1:ℚ)]]),
 (1, [[(0:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache1_check : equalRawCheck
    (rawScale (rawFactor 1 71) wordCache0 ++
      rawScale (rawSecond 1) (rawShift 1 wordCache0)) wordCache1 = true := by
  decide +kernel

theorem wordCache1_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [1]) = evalSym W k a (symMap wordCache1) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache0_sound W k a, wordCache0_sound W (k - (1 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache1_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

def wordCache2 : RawSym := [(0, [[(5112:ℚ)], [(-143:ℚ)], [(1:ℚ)]]),
 (1, [[(0:ℚ)], [(-144:ℚ)], [(2:ℚ)]]),
 (2, [[(0:ℚ)], [(-1:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache2_check : equalRawCheck
    (rawScale (rawFactor 1 72) wordCache1 ++
      rawScale (rawSecond 1) (rawShift 1 wordCache1)) wordCache2 = true := by
  decide +kernel

theorem wordCache2_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [1, 1]) = evalSym W k a (symMap wordCache2) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache1_sound W k a, wordCache1_sound W (k - (1 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache2_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

def wordCache3 : RawSym := [(0, [[(71:ℚ), (1:ℚ)], [(-1:ℚ), (0:ℚ)]]),
 (2, [[(35:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache3_check : equalRawCheck
    (rawScale (rawFactor 2 71) wordCache0 ++
      rawScale (rawSecond 2) (rawShift 2 wordCache0)) wordCache3 = true := by
  decide +kernel

theorem wordCache3_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [2]) = evalSym W k a (symMap wordCache3) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache0_sound W k a, wordCache0_sound W (k - (2 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache3_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

def wordCache4 : RawSym := [(0, [[(-373176:ℚ)], [(15551:ℚ)], [(-216:ℚ)], [(1:ℚ)]]),
 (1, [[(0:ℚ)], [(15768:ℚ)], [(-435:ℚ)], [(3:ℚ)]]),
 (2, [[(0:ℚ)], [(219:ℚ)], [(-222:ℚ)], [(3:ℚ)]]),
 (3, [[(0:ℚ)], [(2:ℚ)], [(-3:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache4_check : equalRawCheck
    (rawScale (rawFactor 1 73) wordCache2 ++
      rawScale (rawSecond 1) (rawShift 1 wordCache2)) wordCache4 = true := by
  decide +kernel

theorem wordCache4_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [1, 1, 1]) = evalSym W k a (symMap wordCache4) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache2_sound W k a, wordCache2_sound W (k - (1 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache4_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

def wordCache5 : RawSym := [(0, [[(-5112:ℚ), (-71:ℚ)], [(143:ℚ), (1:ℚ)], [(-1:ℚ), (0:ℚ)]]),
 (1, [[(0:ℚ), (0:ℚ)], [(72:ℚ), (1:ℚ)], [(-1:ℚ), (0:ℚ)]]),
 (2, [[(-2555:ℚ)], [(-38:ℚ)], [(1:ℚ)]]),
 (3, [[(-70:ℚ)], [(33:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache5_check : equalRawCheck
    (rawScale (rawFactor 2 72) wordCache1 ++
      rawScale (rawSecond 2) (rawShift 2 wordCache1)) wordCache5 = true := by
  decide +kernel

theorem wordCache5_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [2, 1]) = evalSym W k a (symMap wordCache5) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache1_sound W k a, wordCache1_sound W (k - (2 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache5_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

def wordCache6 : RawSym := [(0, [[(-71:ℚ), (-2:ℚ)], [(1:ℚ), (0:ℚ)]]),
 (3, [[(70:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache6_check : equalRawCheck
    (rawScale (rawFactor 3 71) wordCache0 ++
      rawScale (rawSecond 3) (rawShift 3 wordCache0)) wordCache6 = true := by
  decide +kernel

theorem wordCache6_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [3]) = evalSym W k a (symMap wordCache6) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache0_sound W k a, wordCache0_sound W (k - (3 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache6_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

def wordCache7 : RawSym := [(0, [[(27615024:ℚ)], [(-1523950:ℚ)], [(31535:ℚ)], [(-290:ℚ)], [(1:ℚ)]]),
 (1, [[(0:ℚ)], [(-1555776:ℚ)], [(63944:ℚ)], [(-876:ℚ)], [(4:ℚ)]]),
 (2, [[(0:ℚ)], [(-32412:ℚ)], [(33294:ℚ)], [(-888:ℚ)], [(6:ℚ)]]),
 (3, [[(0:ℚ)], [(-592:ℚ)], [(896:ℚ)], [(-308:ℚ)], [(4:ℚ)]]),
 (4, [[(0:ℚ)], [(-6:ℚ)], [(11:ℚ)], [(-6:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache7_check : equalRawCheck
    (rawScale (rawFactor 1 74) wordCache4 ++
      rawScale (rawSecond 1) (rawShift 1 wordCache4)) wordCache7 = true := by
  decide +kernel

theorem wordCache7_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [1, 1, 1, 1]) = evalSym W k a (symMap wordCache7) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache4_sound W k a, wordCache4_sound W (k - (1 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache7_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

end VOA.Classification.COne.OrbIcoZ
