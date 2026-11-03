/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoZhuSparseHBase

/-! # Three-block split of the right `L(-3)H` coordinate

The cubic left `H` monomial is too large to normalize against all nine right monomials in
one kernel unit.  This file records a contiguous three-by-three split of the already audited
`l3hExpectedQ` coordinate.  Subsequent files certify each block independently.
-/

namespace VOA.LatGen.WpTwoZhuSparseCompute

open VOA.SparseRational
open VOA.LatGen.WpTwoAMSparseCompute

def l3hBlockSparseQ : ℕ → SparseRational.Poly ℕ
  | 0 => [([0, 0, 0, 0, 1], 1 / 24), ([0, 0, 0, 2], 1 / 12),
    ([0, 0, 1, 1], 1 / 8)]
  | 1 => [([0, 0, 3], 1 / 2), ([0, 1, 2], 1 / 3), ([0, 4], 1)]
  | 2 => [([1, 3], 1 / 2), ([2, 2], 1 / 6), ([5], 1)]
  | _ => []

def hEntryModePartBlockSparseQ (i j k : ℕ) : SparseRational.Poly ℕ :=
  scaleQ (-4725 / 2048)
    (scaleQ (Nat.choose 3 i)
      (voaModeActSparseQ (hLeftPartSparseQ j) ((i : ℤ) - 2) 6
        (l3hBlockSparseQ k)))

def hEntryMode2Part0Block0ExpectedQ : SparseRational.Poly ℕ :=
  [([0, 0, 0, 0, 0, 2], -4725 / 2048),
   ([0, 0, 0, 0, 1, 1], -23625 / 4096),
   ([0, 0, 0, 0, 3], -14175 / 2048),
   ([0, 0, 0, 1, 2], -14175 / 512),
   ([0, 0, 0, 4], -4725 / 128),
   ([0, 0, 1, 1, 1], -14175 / 1024),
   ([0, 0, 1, 3], -14175 / 512),
   ([0, 0, 5], -70875 / 512),
   ([0, 1, 4], -14175 / 128),
   ([0, 2, 3], -14175 / 512),
   ([1, 1, 3], -14175 / 1024)]

def hEntryMode2Part0Block1ExpectedQ : SparseRational.Poly ℕ :=
  [([0, 0, 0, 4], -14175 / 256),
   ([0, 0, 1, 3], -14175 / 128),
   ([0, 0, 2, 2], -23625 / 512),
   ([0, 0, 5], -70875 / 512),
   ([0, 1, 1, 2], -23625 / 512),
   ([0, 1, 4], -42525 / 256),
   ([0, 2, 3], -70875 / 512),
   ([0, 6], -42525 / 64),
   ([1, 5], -14175 / 128),
   ([2, 4], -4725 / 64),
   ([3, 3], -14175 / 256),
   ([7], -70875 / 128)]

def hEntryMode2Part0Block2ExpectedQ : SparseRational.Poly ℕ :=
  [([0, 1, 4], -14175 / 256),
   ([0, 2, 3], -14175 / 256),
   ([0, 6], -42525 / 256),
   ([1, 1, 3], -70875 / 1024),
   ([1, 2, 2], -14175 / 256),
   ([1, 5], -42525 / 256),
   ([2, 4], -42525 / 256),
   ([3, 3], -42525 / 512),
   ([7], -155925 / 256)]

end VOA.LatGen.WpTwoZhuSparseCompute
