/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Core.SparseRational

/-!
# Independent sparse target for the `p = 2` Adamovic--Milas identity

This is the human-readable 32-term target.  It is deliberately independent of the current-field
recurrence used to compute the screened side.
-/

namespace VOA.LatGen.WpTwoAMExpectedSparse

open VOA.SparseRational

def hProductExpectedRawQ : RawPoly ℕ :=
  [(1 / 12, [0, 0, 0, 1, 1, 2]),
   (1 / 4, [0, 1, 1, 1, 2]),
   (1 / 12, [0, 0, 0, 0, 2, 2]),
   (1 / 4, [0, 0, 1, 2, 2]),
   (1 / 6, [1, 1, 2, 2]),
   (1 / 6, [0, 2, 2, 2]),
   (1 / 6, [0, 0, 0, 0, 1, 3]),
   (1 / 2, [0, 0, 1, 1, 3]),
   (5 / 12, [0, 0, 0, 2, 3]),
   (19 / 12, [0, 1, 2, 3]),
   (5 / 6, [2, 2, 3]),
   (1, [0, 0, 3, 3]),
   (1, [1, 3, 3]),
   (1 / 12, [0, 0, 0, 0, 0, 4]),
   (2 / 3, [0, 0, 0, 1, 4]),
   (5 / 4, [0, 1, 1, 4]),
   (13 / 6, [0, 0, 2, 4]),
   (17 / 6, [1, 2, 4]),
   (4, [0, 3, 4]),
   (2, [4, 4]),
   (5 / 12, [0, 0, 0, 0, 5]),
   (13 / 4, [0, 0, 1, 5]),
   (2, [1, 1, 5]),
   (29 / 6, [0, 2, 5]),
   (4, [3, 5]),
   (17 / 6, [0, 0, 0, 6]),
   (17 / 2, [0, 1, 6]),
   (17 / 3, [2, 6]),
   (9, [0, 0, 7]),
   (9, [1, 7]),
   (22, [0, 8]),
   (26, [9])]

def hProductExpectedSparse : SparseRational.Poly ℕ :=
  normalizeQ hProductExpectedRawQ

theorem hProductExpectedRawQ_length : hProductExpectedRawQ.length = 32 := by rfl

end VOA.LatGen.WpTwoAMExpectedSparse
