/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Examples.RRLowerGram
import VOA.Examples.RRLowerReduction

/-!
# The Gram-rank bound for `M(-22/5, 0)` and the Lee–Yang character

Consequences of `gramRank_le_finrank` (`RRLowerGram.lean`):

* `rochaCaridi_of_gramRank` — `LeeYangGramRankBound → LeeYangRochaCaridiLowerBound`;
* `leeYangRRLowerBound_of_gramRank` — and hence `LeeYangRRLowerBound`;
* `gramRank_le_rc` — conversely `rank G_N ≤ rc N` unconditionally, so under the hypothesis
  `rank G_N = dim L_N = rc N` (`gramRank_eq_finrank_eq_rc`).

These consequences are kept separate from `RRLowerGram.lean`, which does not import
`RRLowerReduction`.
-/

namespace VOA.RRLower

open VOA.InverseDS.VirasoroVerma VOA.Classification.COne VOA.VirSimple VOA.LeeYang
open VOA.LeeYangCharacter Finset

noncomputable section

/-- Unconditionally `rank G_N ≤ rc N`. -/
theorem gramRank_le_rc (N : ℕ) : ((vermaGramMatrix leeYangC 0 N).rank : ℤ) ≤ rc N :=
  (Nat.cast_le.mpr (gramRank_le_finrank N)).trans (finrank_le_rc N)

/-- The Gram-rank bound implies the Rocha-Caridi lower bound. -/
theorem rochaCaridi_of_gramRank (h : LeeYangGramRankBound) : LeeYangRochaCaridiLowerBound :=
  fun N => (h N).trans (Nat.cast_le.mpr (gramRank_le_finrank N))

/-- The Gram-rank bound implies the gap-two lower bound used by the Lee–Yang endpoint. -/
theorem leeYangRRLowerBound_of_gramRank (h : LeeYangGramRankBound) : LeeYangRRLowerBound :=
  leeYangRRLowerBound_iff_rochaCaridi.mpr (rochaCaridi_of_gramRank h)

/-- Under the Gram-rank bound all three numbers agree. -/
theorem gramRank_eq_finrank_eq_rc (h : LeeYangGramRankBound) (N : ℕ) :
    ((vermaGramMatrix leeYangC 0 N).rank : ℤ) = rc N ∧
      (Module.finrank ℂ ((virasoroSimple leeYangC).grading (N : ℤ)) : ℤ) = rc N :=
  ⟨le_antisymm (gramRank_le_rc N) (h N),
    le_antisymm (finrank_le_rc N) ((h N).trans (Nat.cast_le.mpr (gramRank_le_finrank N)))⟩

end

end VOA.RRLower
