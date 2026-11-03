/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoZhuSparseHMode2Part2

/-! # Outer-mode split of the cubic H branch at Zhu mode three -/

namespace VOA.LatGen.WpTwoZhuSparseCompute

open VOA.SparseRational
open VOA.LatGen.WpTwoAMSparseCompute

/-- One summand of the outermost `aWordActSparseQ [0,0,0]` mode expansion. -/
def hMode3Part0OuterSparseQ (m : ℤ) : SparseRational.Poly ℕ :=
  scaleQ (-4725 / 2048) (scaleQ 1 (scaleQ (1 / 6)
    (if 0 ≤ m then
      aFieldActSparseQ 0 m
        (aWordActSparseQ [0, 0] (-2 - m) 6 l3hExpectedQ)
    else
      aWordActSparseQ [0, 0] (-2 - m) (7 + m).toNat
        (aFieldActSparseQ 0 m l3hExpectedQ))))

def hMode3Part0OuterNeg7ExpectedQ : SparseRational.Poly ℕ :=
  [([0, 5], -4725 / 256), ([1, 4], -4725 / 256), ([2, 3], -4725 / 256)]
def hMode3Part0OuterNeg6ExpectedQ : SparseRational.Poly ℕ :=
  [([0, 0, 4], -7875 / 512), ([0, 1, 3], -7875 / 512),
   ([0, 2, 2], -7875 / 1024), ([6], -7875 / 128)]
def hMode3Part0OuterNeg5ExpectedQ : SparseRational.Poly ℕ :=
  [([0, 0, 0, 3], -1575 / 256), ([0, 0, 1, 2], -1575 / 256),
   ([0, 1, 3], -1575 / 256), ([0, 5], -1575 / 32),
   ([1, 1, 2], -1575 / 256), ([6], -1575 / 32)]
def hMode3Part0OuterNeg4ExpectedQ : SparseRational.Poly ℕ :=
  [([0, 0, 0, 0, 2], -1575 / 2048),
   ([0, 0, 0, 1, 1], -1575 / 4096), ([0, 0, 1, 2], -1575 / 512),
   ([0, 0, 4], -4725 / 512), ([0, 1, 1, 1], -1575 / 1024),
   ([0, 2, 2], -1575 / 512), ([0, 5], -1575 / 64),
   ([1, 1, 2], -1575 / 1024), ([1, 4], -1575 / 128),
   ([6], -4725 / 128)]
def hMode3Part0OuterNeg3ExpectedQ : SparseRational.Poly ℕ :=
  [([0, 0, 0, 0, 0, 1], -525 / 2048),
   ([0, 0, 0, 1, 1], -1575 / 1024), ([0, 0, 0, 3], -525 / 128),
   ([0, 0, 1, 2], -525 / 256), ([0, 0, 4], -1575 / 128),
   ([0, 1, 3], -7875 / 512), ([0, 5], -1575 / 64),
   ([2, 3], -525 / 64), ([6], -1575 / 32)]
def hMode3Part0OuterNeg2ExpectedQ : SparseRational.Poly ℕ :=
  [([0, 0, 0, 0, 0, 1], -525 / 2048),
   ([0, 0, 0, 0, 2], -1575 / 4096),
   ([0, 0, 0, 1, 1], -1575 / 4096),
   ([0, 0, 0, 3], -5775 / 1024), ([0, 0, 1, 2], -6825 / 1024),
   ([0, 0, 4], -11025 / 1024), ([0, 1, 3], -1575 / 128),
   ([0, 2, 2], -1575 / 256), ([0, 5], -1575 / 32),
   ([1, 1, 2], -1575 / 512), ([1, 4], -1575 / 128),
   ([2, 3], -2625 / 128), ([6], -7875 / 128)]
def hMode3Part0OuterNeg1ExpectedQ : SparseRational.Poly ℕ := []
def hMode3Part0Outer0ExpectedQ : SparseRational.Poly ℕ :=
  [([0, 0, 0, 0, 0, 1], -1575 / 2048),
   ([0, 0, 0, 0, 2], -1575 / 1024),
   ([0, 0, 0, 1, 1], -4725 / 2048), ([0, 0, 0, 3], -4725 / 512),
   ([0, 0, 1, 2], -1575 / 256), ([0, 0, 4], -4725 / 256),
   ([0, 1, 3], -4725 / 512), ([0, 2, 2], -1575 / 512),
   ([0, 5], -4725 / 256)]
def hMode3Part0Outer1ExpectedQ : SparseRational.Poly ℕ :=
  [([0, 0, 0, 0, 0, 1], -525 / 2048),
   ([0, 0, 0, 1, 1], -4725 / 2048), ([0, 0, 1, 2], -525 / 64),
   ([0, 1, 1, 1], -1575 / 512), ([0, 1, 3], -4725 / 256),
   ([1, 1, 2], -4725 / 512), ([1, 4], -4725 / 256)]
def hMode3Part0Outer2ExpectedQ : SparseRational.Poly ℕ :=
  [([0, 0, 0, 0, 2], -1575 / 2048), ([0, 0, 1, 2], -1575 / 128),
   ([0, 2, 2], -11025 / 512), ([1, 1, 2], -7875 / 1024),
   ([2, 3], -1575 / 64)]
def hMode3Part0Outer3ExpectedQ : SparseRational.Poly ℕ :=
  [([0, 0, 0, 3], -2625 / 256), ([0, 1, 3], -17325 / 512),
   ([2, 3], -6825 / 256)]
def hMode3Part0Outer4ExpectedQ : SparseRational.Poly ℕ :=
  [([0, 0, 4], -7875 / 256), ([1, 4], -7875 / 256)]
def hMode3Part0Outer5ExpectedQ : SparseRational.Poly ℕ :=
  [([0, 5], -23625 / 256)]
def hMode3Part0Outer6ExpectedQ : SparseRational.Poly ℕ :=
  [([6], -33075 / 256)]

end VOA.LatGen.WpTwoZhuSparseCompute
