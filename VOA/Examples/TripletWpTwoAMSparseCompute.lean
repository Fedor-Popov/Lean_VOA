/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Examples.TripletWpTwoAMClose
import VOA.Core.SparseRational

/-! # Executable sparse current calculation for lattice `W(2)` -/

namespace VOA.LatGen.WpTwoAMSparseCompute

open VOA.SparseRational
open VOA.LatGen.WpTwoAMClose

def prependRawQ (i : ℕ) (P : RawPoly ℕ) : RawPoly ℕ :=
  P.map fun t => (t.1, i :: t.2)

def scaleRawQ (q : ℚ) (P : RawPoly ℕ) : RawPoly ℕ :=
  P.map fun t => (q * t.1, t.2)

def annihilateRawQ (n : ℕ) : List ℕ → RawPoly ℕ
  | [] => []
  | i :: is =>
      (if n = i + 1 then [((4 : ℚ) * n, is)] else []) ++
        prependRawQ i (annihilateRawQ n is)

def aFieldCoeffQ (i : ℕ) (s : ℤ) : ℚ :=
  (((∏ l ∈ Finset.range i, (s + 1 + l) : ℤ) : ℤ) : ℚ) *
    (i.factorial : ℚ)⁻¹

def aFieldModeQ (i : ℕ) (s : ℤ) : ℤ := -(s + i) - 1

def aFieldActMonomialQ (i : ℕ) (s : ℤ) (w : Monomial ℕ) : SparseRational.Poly ℕ :=
  if aFieldModeQ i s < 0 then
    normalizeQ [(aFieldCoeffQ i s, (-aFieldModeQ i s - 1).toNat :: w)]
  else if aFieldModeQ i s = 0 then []
  else
    normalizeQ (scaleRawQ (aFieldCoeffQ i s)
      (annihilateRawQ (aFieldModeQ i s).toNat w))

def aFieldActSparseQ (i : ℕ) (s : ℤ) (P : SparseRational.Poly ℕ) : SparseRational.Poly ℕ :=
  bindQ P fun w q => scaleQ q (aFieldActMonomialQ i s w)

def aWordWeightQ : List ℕ → ℕ
  | [] => 0
  | i :: is => i + 1 + aWordWeightQ is

def natRangeQ : ℕ → List ℕ
  | 0 => []
  | n + 1 => natRangeQ n ++ [n]

def intIccListQ (lo hi : ℤ) : List ℤ :=
  if lo ≤ hi then (natRangeQ (hi - lo + 1).toNat).map fun n => lo + n else []

def sumSparseIcc (lo hi : ℤ) (f : ℤ → SparseRational.Poly ℕ) : SparseRational.Poly ℕ :=
  sumQ ((intIccListQ lo hi).map f)

def aWordActSparseQ : List ℕ → ℤ → ℕ → SparseRational.Poly ℕ → SparseRational.Poly ℕ
  | [], s, _w, P => if s = 0 then P else []
  | i :: is, s, w, P =>
      sumSparseIcc (-((i + 1 + w : ℕ) : ℤ))
          (max (-1) ((aWordWeightQ is + w : ℕ) + s)) fun m =>
        if 0 ≤ m then
          aFieldActSparseQ i m (aWordActSparseQ is (s - m) w P)
        else
          aWordActSparseQ is (s - m) ((i + 1 + w : ℕ) + m).toNat
            (aFieldActSparseQ i m P)

def sThreeSparseQ : SparseRational.Poly ℕ :=
  normalizeQ [(1 / 6, [0, 0, 0]), (1 / 2, [0, 1]), (1 / 3, [2])]

def hPartZeroZeroZeroSparseQ : SparseRational.Poly ℕ :=
  scaleQ (1 / 6) (aWordActSparseQ [0, 0, 0] 4 3 sThreeSparseQ)

def hPartZeroOneSparseQ : SparseRational.Poly ℕ :=
  scaleQ (1 / 2) (aWordActSparseQ [0, 1] 4 3 sThreeSparseQ)

def hPartTwoSparseQ : SparseRational.Poly ℕ :=
  scaleQ (1 / 3) (aWordActSparseQ [2] 4 3 sThreeSparseQ)

def hProductSparseQ : SparseRational.Poly ℕ :=
  addQ hPartZeroZeroZeroSparseQ (addQ hPartZeroOneSparseQ hPartTwoSparseQ)

def hPartTwoExpectedQ : SparseRational.Poly ℕ :=
  normalizeQ [(5 / 6, [0, 0, 0, 6]), (5 / 2, [0, 1, 6]), (5 / 3, [2, 6])]

def hPartZeroOneExpectedQ : SparseRational.Poly ℕ := normalizeQ
  [(5 / 12, [0, 0, 0, 0, 5]), (5 / 12, [0, 0, 0, 1, 4]),
   (5 / 12, [0, 0, 0, 2, 3]), (5 / 4, [0, 0, 1, 5]),
   (5, [0, 0, 7]), (5 / 4, [0, 1, 1, 4]), (5 / 4, [0, 1, 2, 3]),
   (5 / 6, [0, 2, 5]), (10, [0, 8]), (5 / 6, [1, 2, 4]),
   (5, [1, 7]), (5 / 6, [2, 2, 3]), (10, [9])]

def hPartZeroZeroZeroExpectedQ : SparseRational.Poly ℕ := normalizeQ
  [(1 / 12, [0, 0, 0, 0, 0, 4]), (1 / 6, [0, 0, 0, 0, 1, 3]),
   (1 / 12, [0, 0, 0, 0, 2, 2]), (1 / 12, [0, 0, 0, 1, 1, 2]),
   (1 / 4, [0, 0, 0, 1, 4]), (2, [0, 0, 0, 6]),
   (1 / 2, [0, 0, 1, 1, 3]), (1 / 4, [0, 0, 1, 2, 2]),
   (2, [0, 0, 1, 5]), (13 / 6, [0, 0, 2, 4]), (1, [0, 0, 3, 3]),
   (4, [0, 0, 7]), (1 / 4, [0, 1, 1, 1, 2]), (1 / 3, [0, 1, 2, 3]),
   (6, [0, 1, 6]), (1 / 6, [0, 2, 2, 2]), (4, [0, 2, 5]),
   (4, [0, 3, 4]), (12, [0, 8]), (1 / 6, [1, 1, 2, 2]),
   (2, [1, 1, 5]), (2, [1, 2, 4]), (1, [1, 3, 3]), (4, [1, 7]),
   (4, [2, 6]), (4, [3, 5]), (2, [4, 4]), (16, [9])]

private theorem intIccListQ_neg_four_nine :
    intIccListQ (-4) 9 = [-4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9] := by
  norm_num [intIccListQ, natRangeQ, Int.toNat]

private theorem intIccListQ_neg_six_seven :
    intIccListQ (-6) 7 = [-6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7] := by
  norm_num [intIccListQ, natRangeQ, Int.toNat]

theorem hPartTwoSparseQ_eq : hPartTwoSparseQ = hPartTwoExpectedQ := by
  rw [hPartTwoSparseQ, aWordActSparseQ]
  norm_num [aWordWeightQ]
  rw [sumSparseIcc, intIccListQ_neg_six_seven]
  simp only [List.map_cons, List.map_nil, sumQ]
  norm_num (config := { maxSteps := 1000000 })
    [hPartTwoExpectedQ, aWordActSparseQ, aWordWeightQ, sumSparseIcc,
    intIccListQ, natRangeQ, Int.toNat, Function.comp_apply, aFieldActSparseQ,
    aFieldActMonomialQ, aFieldModeQ, aFieldCoeffQ, annihilateRawQ,
    prependRawQ, scaleRawQ, sThreeSparseQ, bindQ, sumQ, addQ, scaleQ, toRaw,
    normalizeQ, insertQ, sortWord, insertVar, insertSorted, compareWord]

set_option maxHeartbeats 1000000 in
theorem hPartZeroOneSparseQ_eq : hPartZeroOneSparseQ = hPartZeroOneExpectedQ := by
  rw [hPartZeroOneSparseQ, aWordActSparseQ]
  norm_num [aWordWeightQ]
  rw [sumSparseIcc, intIccListQ_neg_four_nine]
  simp only [List.map_cons, List.map_nil, sumQ]
  norm_num (config := { maxSteps := 1000000 })
    [hPartZeroOneExpectedQ, aWordActSparseQ, aWordWeightQ, sumSparseIcc,
    intIccListQ, natRangeQ, Int.toNat, Function.comp_apply, aFieldActSparseQ,
    aFieldActMonomialQ, aFieldModeQ, aFieldCoeffQ, annihilateRawQ,
    prependRawQ, scaleRawQ, sThreeSparseQ, bindQ, sumQ, addQ, scaleQ, toRaw,
    normalizeQ, insertQ, sortWord, insertVar, insertSorted, compareWord]

end VOA.LatGen.WpTwoAMSparseCompute
