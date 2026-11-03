import VOA.Classification.COne.OrbIcoZSymbolWords24

/-! Small cached uniform checks for Virasoro words. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option linter.style.longLine false
noncomputable section
namespace VOA.Classification.COne.OrbIcoZ
open VOA OrbOdd OrbZhu Polynomial

def wordCache200 : RawSym := [(0, [[(-5112:ℚ), (-781:ℚ)], [(143:ℚ), (11:ℚ)], [(-1:ℚ), (0:ℚ)]]),
 (1, [[(0:ℚ), (0:ℚ)], [(72:ℚ), (11:ℚ)], [(-1:ℚ), (0:ℚ)]]),
 (12, [[(-31955:ℚ)], [(302:ℚ)], [(1:ℚ)]]),
 (13, [[(-4620:ℚ)], [(373:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache200_check : equalRawCheck
    (rawScale (rawFactor 12 72) wordCache1 ++
      rawScale (rawSecond 12) (rawShift 12 wordCache1)) wordCache200 = true := by
  decide +kernel

theorem wordCache200_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [12, 1]) = evalSym W k a (symMap wordCache200) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache1_sound W k a, wordCache1_sound W (k - (12 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache200_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

def wordCache201 : RawSym := [(0, [[(-71:ℚ), (-12:ℚ)], [(1:ℚ), (0:ℚ)]]),
 (13, [[(420:ℚ)], [(1:ℚ)]])]

set_option maxHeartbeats 2000000 in
-- The kernel checks one recursion step against the already cached tail.
theorem wordCache201_check : equalRawCheck
    (rawScale (rawFactor 13 71) wordCache0 ++
      rawScale (rawSecond 13) (rawShift 13 wordCache0)) wordCache201 = true := by
  decide +kernel

theorem wordCache201_sound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (k : ℤ) (a : ℤ → A W) :
    evalSym W k a (symWord [13]) = evalSym W k a (symMap wordCache201) := by
  rw [symWord, evalSym_normalize, evalSym_append, evalSym_scale, evalSym_scale,
    evalSym_shift, wordCache0_sound W k a, wordCache0_sound W (k - (13 : ℕ)) a]
  have hh := equalRawCheck_sound W k a wordCache201_check
  rw [symMap_append, symMap_scale, symMap_scale, symMap_shift, evalSym_append,
    evalSym_scale, evalSym_scale, evalSym_shift, bp_rawFactor, bp_rawSecond] at hh
  norm_num only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.cast_ofNat] at ⊢
  exact hh

end VOA.Classification.COne.OrbIcoZ
