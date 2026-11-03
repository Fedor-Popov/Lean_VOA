/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Examples.LYGramRank
import VOA.Examples.RRLowerGramBound

/-!
# The Lee–Yang vacuum character, from the Feigin–Fuchs rank bound

From `leeYangGramRankBound_holds` (`LYGramRank.lean`):

* `leeYangRochaCaridiLowerBound_holds`, `leeYangRRLowerBound_holds`,
  `leeYangRochaCaridiCharacter_holds`.

These consequences are kept separate from `LYGramRank.lean`, which does not import
`RRLowerReduction` (through `RRLowerGram`).
-/

namespace VOA.RRLower

open VOA.InverseDS.VirasoroVerma VOA.LeeYang

/-- The Rocha-Caridi lower bound `rc N ≤ dim L(-22/5, 0)_N`, proved. -/
theorem leeYangRochaCaridiLowerBound_holds : LeeYangRochaCaridiLowerBound :=
  rochaCaridi_of_gramRank leeYangGramRankBound_holds

/-- The Rocha-Caridi character of `L(-22/5, 0)`, proved. -/
theorem leeYangRochaCaridiCharacter_holds : LeeYangRochaCaridiCharacter :=
  rochaCaridiLowerBound_iff_character.mp leeYangRochaCaridiLowerBound_holds

/-- The gap-two (Rogers–Ramanujan) lower bound for the Lee–Yang weight spaces, proved. -/
theorem leeYangRRLowerBound_holds : LeeYangCharacter.LeeYangRRLowerBound :=
  leeYangRRLowerBound_of_gramRank leeYangGramRankBound_holds

end VOA.RRLower
