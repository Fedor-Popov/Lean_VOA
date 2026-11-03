import VOA.Classification.COne.OrbOctaRCScreenCache03

/-! Exact shared exponential descendants for the weight-sixteen screening chain. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
namespace VOA.Classification.COne.OrbOctaRC
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational HeisenbergN
  PlusC2Eval PlusUnitary PlusC2 OrbC2e OrbC2g OrbC2h LatMod

def sc600 : RawPoly ℕ :=
  [(1, [0, 1, 1]),
   (-2, [2])]

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc600_check :
    reduceTwo (prependC 1 sc210 ++ scaleR (-1) (prependC 0 sc211)) = sc600 := by
  decide +kernel

theorem sc600_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc600 = evRc a c (expWordR [1, 1, 3] (-3)) := by
  rw [← sc600_check]
  exact expTwo_step _ _ hc 0 [1, 3] (-3)
    sc210 sc211 (sc210_sound a c hc) (sc211_sound a c hc)

def sc601 : RawPoly ℕ :=
  [(mkRat (2) 3, [1, 1, 1]),
   (mkRat (2) 3, [3])]

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc601_check :
    reduceTwo (prependC 1 sc211 ++ scaleR (-1) (prependC 0 sc212)) = sc601 := by
  decide +kernel

theorem sc601_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc601 = evRc a c (expWordR [1, 1, 3] (-2)) := by
  rw [← sc601_check]
  exact expTwo_step _ _ hc 0 [1, 3] (-2)
    sc211 sc212 (sc211_sound a c hc) (sc212_sound a c hc)

def sc602 : RawPoly ℕ :=
  [(mkRat (-1) 2, [0, 2, 2]),
   (1, [1, 1, 2]),
   (-1, [4])]

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc602_check :
    reduceTwo (prependC 1 sc212 ++ scaleR (-1) (prependC 0 sc213)) = sc602 := by
  decide +kernel

theorem sc602_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc602 = evRc a c (expWordR [1, 1, 3] (-1)) := by
  rw [← sc602_check]
  exact expTwo_step _ _ hc 0 [1, 3] (-1)
    sc212 sc213 (sc212_sound a c hc) (sc213_sound a c hc)

def sc603 : RawPoly ℕ :=
  [(mkRat (1) 3, [0, 1, 1, 1, 2]),
   (mkRat (1) 3, [0, 2, 3]),
   (mkRat (-2) 15, [1, 1, 1, 1, 1]),
   (mkRat (-1) 3, [1, 1, 3]),
   (mkRat (-4) 5, [5])]

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc603_check :
    reduceTwo (prependC 1 sc213 ++ scaleR (-1) (prependC 0 sc214)) = sc603 := by
  decide +kernel

theorem sc603_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc603 = evRc a c (expWordR [1, 1, 3] (0)) := by
  rw [← sc603_check]
  exact expTwo_step _ _ hc 0 [1, 3] (0)
    sc213 sc214 (sc213_sound a c hc) (sc214_sound a c hc)

def sc604 : RawPoly ℕ :=
  [(mkRat (-1) 18, [0, 1, 1, 1, 1, 1, 1]),
   (mkRat (-1) 9, [0, 1, 1, 1, 3]),
   (mkRat (1) 4, [0, 1, 1, 2, 2]),
   (mkRat (-1) 2, [0, 2, 4]),
   (mkRat (4) 9, [0, 3, 3]),
   (mkRat (1) 2, [1, 1, 4]),
   (mkRat (-1) 6, [2, 2, 2]),
   (mkRat (-2) 3, [6])]

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc604_check :
    reduceTwo (prependC 1 sc214 ++ scaleR (-1) (prependC 0 sc215)) = sc604 := by
  decide +kernel

theorem sc604_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc604 = evRc a c (expWordR [1, 1, 3] (1)) := by
  rw [← sc604_check]
  exact expTwo_step _ _ hc 0 [1, 3] (1)
    sc214 sc215 (sc214_sound a c hc) (sc215_sound a c hc)

def sc605 : RawPoly ℕ :=
  [(mkRat (-1) 15, [0, 1, 1, 1, 1, 1, 2]),
   (mkRat (1) 6, [0, 1, 1, 1, 4]),
   (mkRat (-1) 6, [0, 1, 1, 2, 3]),
   (mkRat (-2) 5, [0, 2, 5]),
   (mkRat (1) 6, [0, 3, 4]),
   (mkRat (-1) 35, [1, 1, 1, 1, 1, 1, 1]),
   (mkRat (1) 6, [1, 1, 1, 2, 2]),
   (mkRat (2) 5, [1, 1, 5]),
   (mkRat (1) 6, [2, 2, 3]),
   (mkRat (-4) 7, [7])]

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc605_check :
    reduceTwo (prependC 1 sc215 ++ scaleR (-1) (prependC 0 sc216)) = sc605 := by
  decide +kernel

theorem sc605_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc605 = evRc a c (expWordR [1, 1, 3] (2)) := by
  rw [← sc605_check]
  exact expTwo_step _ _ hc 0 [1, 3] (2)
    sc215 sc216 (sc215_sound a c hc) (sc216_sound a c hc)

def sc606 : RawPoly ℕ :=
  [(mkRat (-1) 180, [0, 1, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (1) 45, [0, 1, 1, 1, 1, 1, 3]),
   (mkRat (2) 15, [0, 1, 1, 1, 5]),
   (mkRat (1) 4, [0, 1, 1, 2, 4]),
   (mkRat (-2) 9, [0, 1, 1, 3, 3]),
   (mkRat (-1) 48, [0, 2, 2, 2, 2]),
   (mkRat (-1) 3, [0, 2, 6]),
   (mkRat (2) 15, [0, 3, 5]),
   (mkRat (-1) 8, [0, 4, 4]),
   (mkRat (-1) 18, [1, 1, 1, 1, 1, 1, 2]),
   (mkRat (-1) 9, [1, 1, 1, 2, 3]),
   (mkRat (1) 12, [1, 1, 2, 2, 2]),
   (mkRat (1) 3, [1, 1, 6]),
   (mkRat (-1) 4, [2, 2, 4]),
   (mkRat (4) 9, [2, 3, 3]),
   (mkRat (-1) 2, [8])]

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc606_check :
    reduceTwo (prependC 1 sc216 ++ scaleR (-1) (prependC 0 sc217)) = sc606 := by
  decide +kernel

theorem sc606_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc606 = evRc a c (expWordR [1, 1, 3] (3)) := by
  rw [← sc606_check]
  exact expTwo_step _ _ hc 0 [1, 3] (3)
    sc216 sc217 (sc216_sound a c hc) (sc217_sound a c hc)

def sc607 : RawPoly ℕ :=
  [(mkRat (-1) 70, [0, 1, 1, 1, 1, 1, 1, 1, 2]),
   (mkRat (-1) 30, [0, 1, 1, 1, 1, 1, 4]),
   (mkRat (1) 36, [0, 1, 1, 1, 2, 2, 2]),
   (mkRat (1) 9, [0, 1, 1, 1, 6]),
   (mkRat (1) 5, [0, 1, 1, 2, 5]),
   (mkRat (-1) 12, [0, 1, 1, 3, 4]),
   (mkRat (1) 36, [0, 2, 2, 2, 3]),
   (mkRat (-2) 7, [0, 2, 7]),
   (mkRat (1) 9, [0, 3, 6]),
   (mkRat (-1) 5, [0, 4, 5]),
   (mkRat (-1) 567, [1, 1, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (1) 54, [1, 1, 1, 1, 1, 1, 3]),
   (mkRat (-1) 30, [1, 1, 1, 1, 1, 2, 2]),
   (mkRat (1) 6, [1, 1, 1, 2, 4]),
   (mkRat (-4) 27, [1, 1, 1, 3, 3]),
   (mkRat (-1) 12, [1, 1, 2, 2, 3]),
   (mkRat (2) 7, [1, 1, 7]),
   (mkRat (-1) 5, [2, 2, 5]),
   (mkRat (1) 6, [2, 3, 4]),
   (mkRat (14) 81, [3, 3, 3]),
   (mkRat (-4) 9, [9])]

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc607_check :
    reduceTwo (prependC 1 sc217 ++ scaleR (-1) (prependC 0 sc218)) = sc607 := by
  decide +kernel

theorem sc607_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc607 = evRc a c (expWordR [1, 1, 3] (4)) := by
  rw [← sc607_check]
  exact expTwo_step _ _ hc 0 [1, 3] (4)
    sc217 sc218 (sc217_sound a c hc) (sc218_sound a c hc)

def sc608Part0 : RawPoly ℕ :=
  [(mkRat (-1) 4200, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (1) 210, [0, 1, 1, 1, 1, 1, 1, 1, 3]),
   (mkRat (-1) 72, [0, 1, 1, 1, 1, 1, 1, 2, 2]),
   (mkRat (-2) 75, [0, 1, 1, 1, 1, 1, 5]),
   (mkRat (-1) 36, [0, 1, 1, 1, 2, 2, 3]),
   (mkRat (2) 21, [0, 1, 1, 1, 7]),
   (mkRat (1) 96, [0, 1, 1, 2, 2, 2, 2]),
   (mkRat (1) 6, [0, 1, 1, 2, 6]),
   (mkRat (-1) 15, [0, 1, 1, 3, 5]),
   (mkRat (1) 16, [0, 1, 1, 4, 4]),
   (mkRat (-1) 24, [0, 2, 2, 2, 4]),
   (mkRat (1) 9, [0, 2, 2, 3, 3]),
   (mkRat (-1) 4, [0, 2, 8]),
   (mkRat (2) 21, [0, 3, 7]),
   (mkRat (-1) 6, [0, 4, 6]),
   (mkRat (-2) 25, [0, 5, 5]),
   (mkRat (-1) 180, [1, 1, 1, 1, 1, 1, 1, 1, 2]),
   (mkRat (-1) 36, [1, 1, 1, 1, 1, 1, 4]),
   (mkRat (1) 45, [1, 1, 1, 1, 1, 2, 3]),
   (mkRat (2) 15, [1, 1, 1, 2, 5]),
   (mkRat (-1) 18, [1, 1, 1, 3, 4]),
   (mkRat (1) 8, [1, 1, 2, 2, 4]),
   (mkRat (-2) 9, [1, 1, 2, 3, 3]),
   (mkRat (1) 4, [1, 1, 8])]

def sc608Part1 : RawPoly ℕ :=
  [(mkRat (-1) 240, [2, 2, 2, 2, 2]),
   (mkRat (-1) 6, [2, 2, 6]),
   (mkRat (2) 15, [2, 3, 5]),
   (mkRat (-1) 8, [2, 4, 4]),
   (mkRat (2) 9, [3, 3, 4]),
   (mkRat (-2) 5, [10])]

def sc608 : RawPoly ℕ :=
  [sc608Part0,
   sc608Part1].flatten

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc608_check :
    reduceTwo (prependC 1 sc218 ++ scaleR (-1) (prependC 0 sc219)) = sc608 := by
  decide +kernel

theorem sc608_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc608 = evRc a c (expWordR [1, 1, 3] (5)) := by
  rw [← sc608_check]
  exact expTwo_step _ _ hc 0 [1, 3] (5)
    sc218 sc219 (sc218_sound a c hc) (sc219_sound a c hc)

def sc609Part0 : RawPoly ℕ :=
  [(mkRat (-1) 1134, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2]),
   (mkRat (-1) 140, [0, 1, 1, 1, 1, 1, 1, 1, 4]),
   (mkRat (1) 108, [0, 1, 1, 1, 1, 1, 1, 2, 3]),
   (mkRat (-1) 180, [0, 1, 1, 1, 1, 1, 2, 2, 2]),
   (mkRat (-1) 45, [0, 1, 1, 1, 1, 1, 6]),
   (mkRat (1) 24, [0, 1, 1, 1, 2, 2, 4]),
   (mkRat (-2) 27, [0, 1, 1, 1, 2, 3, 3]),
   (mkRat (1) 12, [0, 1, 1, 1, 8]),
   (mkRat (-1) 72, [0, 1, 1, 2, 2, 2, 3]),
   (mkRat (1) 7, [0, 1, 1, 2, 7]),
   (mkRat (-1) 18, [0, 1, 1, 3, 6]),
   (mkRat (1) 10, [0, 1, 1, 4, 5]),
   (mkRat (-1) 30, [0, 2, 2, 2, 5]),
   (mkRat (1) 24, [0, 2, 2, 3, 4]),
   (mkRat (7) 81, [0, 2, 3, 3, 3]),
   (mkRat (-2) 9, [0, 2, 9]),
   (mkRat (1) 12, [0, 3, 8]),
   (mkRat (-1) 7, [0, 4, 7]),
   (mkRat (-2) 15, [0, 5, 6]),
   (mkRat (-1) 17820, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (1) 540, [1, 1, 1, 1, 1, 1, 1, 1, 3]),
   (mkRat (-1) 140, [1, 1, 1, 1, 1, 1, 1, 2, 2]),
   (mkRat (-1) 45, [1, 1, 1, 1, 1, 1, 5]),
   (mkRat (-1) 30, [1, 1, 1, 1, 1, 2, 4])]

def sc609Part1 : RawPoly ℕ :=
  [(mkRat (4) 135, [1, 1, 1, 1, 1, 3, 3]),
   (mkRat (1) 144, [1, 1, 1, 2, 2, 2, 2]),
   (mkRat (1) 9, [1, 1, 1, 2, 6]),
   (mkRat (-2) 45, [1, 1, 1, 3, 5]),
   (mkRat (1) 24, [1, 1, 1, 4, 4]),
   (mkRat (1) 10, [1, 1, 2, 2, 5]),
   (mkRat (-1) 12, [1, 1, 2, 3, 4]),
   (mkRat (-7) 81, [1, 1, 3, 3, 3]),
   (mkRat (2) 9, [1, 1, 9]),
   (mkRat (1) 144, [2, 2, 2, 2, 3]),
   (mkRat (-1) 7, [2, 2, 7]),
   (mkRat (1) 9, [2, 3, 6]),
   (mkRat (-1) 5, [2, 4, 5]),
   (mkRat (8) 45, [3, 3, 5]),
   (mkRat (1) 24, [3, 4, 4]),
   (mkRat (-4) 11, [11])]

def sc609 : RawPoly ℕ :=
  [sc609Part0,
   sc609Part1].flatten

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc609_check :
    reduceTwo (prependC 1 sc219 ++ scaleR (-1) (prependC 0 sc220)) = sc609 := by
  decide +kernel

theorem sc609_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc609 = evRc a c (expWordR [1, 1, 3] (6)) := by
  rw [← sc609_check]
  exact expTwo_step _ _ hc 0 [1, 3] (6)
    sc219 sc220 (sc219_sound a c hc) (sc220_sound a c hc)

def sc610Part0 : RawPoly ℕ :=
  [(mkRat (-1) 170100, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (1) 3402, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3]),
   (mkRat (-1) 720, [0, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2]),
   (mkRat (-1) 175, [0, 1, 1, 1, 1, 1, 1, 1, 5]),
   (mkRat (-1) 72, [0, 1, 1, 1, 1, 1, 1, 2, 4]),
   (mkRat (1) 81, [0, 1, 1, 1, 1, 1, 1, 3, 3]),
   (mkRat (1) 180, [0, 1, 1, 1, 1, 1, 2, 2, 3]),
   (mkRat (-2) 105, [0, 1, 1, 1, 1, 1, 7]),
   (mkRat (1) 30, [0, 1, 1, 1, 2, 2, 5]),
   (mkRat (-1) 36, [0, 1, 1, 1, 2, 3, 4]),
   (mkRat (-7) 243, [0, 1, 1, 1, 3, 3, 3]),
   (mkRat (2) 27, [0, 1, 1, 1, 9]),
   (mkRat (1) 48, [0, 1, 1, 2, 2, 2, 4]),
   (mkRat (-1) 18, [0, 1, 1, 2, 2, 3, 3]),
   (mkRat (1) 8, [0, 1, 1, 2, 8]),
   (mkRat (-1) 21, [0, 1, 1, 3, 7]),
   (mkRat (1) 12, [0, 1, 1, 4, 6]),
   (mkRat (1) 25, [0, 1, 1, 5, 5]),
   (mkRat (-1) 2880, [0, 2, 2, 2, 2, 2, 2]),
   (mkRat (-1) 36, [0, 2, 2, 2, 6]),
   (mkRat (1) 30, [0, 2, 2, 3, 5]),
   (mkRat (-1) 32, [0, 2, 2, 4, 4]),
   (mkRat (1) 9, [0, 2, 3, 3, 4]),
   (mkRat (-1) 5, [0, 2, 10])]

def sc610Part1 : RawPoly ℕ :=
  [(mkRat (5) 243, [0, 3, 3, 3, 3]),
   (mkRat (2) 27, [0, 3, 9]),
   (mkRat (-1) 8, [0, 4, 8]),
   (mkRat (-4) 35, [0, 5, 7]),
   (mkRat (-1) 18, [0, 6, 6]),
   (mkRat (-1) 4200, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2]),
   (mkRat (-1) 360, [1, 1, 1, 1, 1, 1, 1, 1, 4]),
   (mkRat (1) 210, [1, 1, 1, 1, 1, 1, 1, 2, 3]),
   (mkRat (-1) 216, [1, 1, 1, 1, 1, 1, 2, 2, 2]),
   (mkRat (-1) 54, [1, 1, 1, 1, 1, 1, 6]),
   (mkRat (-2) 75, [1, 1, 1, 1, 1, 2, 5]),
   (mkRat (1) 90, [1, 1, 1, 1, 1, 3, 4]),
   (mkRat (-1) 108, [1, 1, 1, 2, 2, 2, 3]),
   (mkRat (2) 21, [1, 1, 1, 2, 7]),
   (mkRat (-1) 27, [1, 1, 1, 3, 6]),
   (mkRat (1) 15, [1, 1, 1, 4, 5]),
   (mkRat (1) 480, [1, 1, 2, 2, 2, 2, 2]),
   (mkRat (1) 12, [1, 1, 2, 2, 6]),
   (mkRat (-1) 15, [1, 1, 2, 3, 5]),
   (mkRat (1) 16, [1, 1, 2, 4, 4]),
   (mkRat (-1) 9, [1, 1, 3, 3, 4]),
   (mkRat (1) 5, [1, 1, 10]),
   (mkRat (-1) 96, [2, 2, 2, 2, 4]),
   (mkRat (1) 27, [2, 2, 2, 3, 3])]

def sc610Part2 : RawPoly ℕ :=
  [(mkRat (-1) 8, [2, 2, 8]),
   (mkRat (2) 21, [2, 3, 7]),
   (mkRat (-1) 6, [2, 4, 6]),
   (mkRat (-2) 25, [2, 5, 5]),
   (mkRat (4) 27, [3, 3, 6]),
   (mkRat (1) 15, [3, 4, 5]),
   (mkRat (-1) 48, [4, 4, 4]),
   (mkRat (-1) 3, [12])]

def sc610 : RawPoly ℕ :=
  [sc610Part0,
   sc610Part1,
   sc610Part2].flatten

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc610_check :
    reduceTwo (prependC 1 sc220 ++ scaleR (-1) (prependC 0 sc221)) = sc610 := by
  decide +kernel

theorem sc610_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc610 = evRc a c (expWordR [1, 1, 3] (7)) := by
  rw [← sc610_check]
  exact expTwo_step _ _ hc 0 [1, 3] (7)
    sc220 sc221 (sc220_sound a c hc) (sc221_sound a c hc)

def sc611Part0 : RawPoly ℕ :=
  [(mkRat (-1) 35640, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2]),
   (mkRat (-1) 2268, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4]),
   (mkRat (1) 1080, [0, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3]),
   (mkRat (-1) 840, [0, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2]),
   (mkRat (-1) 210, [0, 1, 1, 1, 1, 1, 1, 1, 6]),
   (mkRat (-1) 90, [0, 1, 1, 1, 1, 1, 1, 2, 5]),
   (mkRat (1) 216, [0, 1, 1, 1, 1, 1, 1, 3, 4]),
   (mkRat (-1) 120, [0, 1, 1, 1, 1, 1, 2, 2, 4]),
   (mkRat (2) 135, [0, 1, 1, 1, 1, 1, 2, 3, 3]),
   (mkRat (-1) 60, [0, 1, 1, 1, 1, 1, 8]),
   (mkRat (1) 1440, [0, 1, 1, 1, 2, 2, 2, 2, 2]),
   (mkRat (1) 36, [0, 1, 1, 1, 2, 2, 6]),
   (mkRat (-1) 45, [0, 1, 1, 1, 2, 3, 5]),
   (mkRat (1) 48, [0, 1, 1, 1, 2, 4, 4]),
   (mkRat (-1) 27, [0, 1, 1, 1, 3, 3, 4]),
   (mkRat (1) 15, [0, 1, 1, 1, 10]),
   (mkRat (1) 60, [0, 1, 1, 2, 2, 2, 5]),
   (mkRat (-1) 48, [0, 1, 1, 2, 2, 3, 4]),
   (mkRat (-7) 162, [0, 1, 1, 2, 3, 3, 3]),
   (mkRat (1) 9, [0, 1, 1, 2, 9]),
   (mkRat (-1) 24, [0, 1, 1, 3, 8]),
   (mkRat (1) 14, [0, 1, 1, 4, 7]),
   (mkRat (1) 15, [0, 1, 1, 5, 6]),
   (mkRat (1) 1440, [0, 2, 2, 2, 2, 2, 3])]

def sc611Part1 : RawPoly ℕ :=
  [(mkRat (-1) 42, [0, 2, 2, 2, 7]),
   (mkRat (1) 36, [0, 2, 2, 3, 6]),
   (mkRat (-1) 20, [0, 2, 2, 4, 5]),
   (mkRat (4) 45, [0, 2, 3, 3, 5]),
   (mkRat (1) 48, [0, 2, 3, 4, 4]),
   (mkRat (-2) 11, [0, 2, 11]),
   (mkRat (7) 162, [0, 3, 3, 3, 4]),
   (mkRat (1) 15, [0, 3, 10]),
   (mkRat (-1) 9, [0, 4, 9]),
   (mkRat (-1) 10, [0, 5, 8]),
   (mkRat (-2) 21, [0, 6, 7]),
   (mkRat (-1) 900900, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (1) 12600, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3]),
   (mkRat (-1) 2268, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2]),
   (mkRat (-1) 450, [1, 1, 1, 1, 1, 1, 1, 1, 5]),
   (mkRat (-1) 140, [1, 1, 1, 1, 1, 1, 1, 2, 4]),
   (mkRat (2) 315, [1, 1, 1, 1, 1, 1, 1, 3, 3]),
   (mkRat (1) 216, [1, 1, 1, 1, 1, 1, 2, 2, 3]),
   (mkRat (-1) 63, [1, 1, 1, 1, 1, 1, 7]),
   (mkRat (-1) 720, [1, 1, 1, 1, 1, 2, 2, 2, 2]),
   (mkRat (-1) 45, [1, 1, 1, 1, 1, 2, 6]),
   (mkRat (2) 225, [1, 1, 1, 1, 1, 3, 5]),
   (mkRat (-1) 120, [1, 1, 1, 1, 1, 4, 4]),
   (mkRat (1) 72, [1, 1, 1, 2, 2, 2, 4])]

def sc611Part2 : RawPoly ℕ :=
  [(mkRat (-1) 27, [1, 1, 1, 2, 2, 3, 3]),
   (mkRat (1) 12, [1, 1, 1, 2, 8]),
   (mkRat (-2) 63, [1, 1, 1, 3, 7]),
   (mkRat (1) 18, [1, 1, 1, 4, 6]),
   (mkRat (2) 75, [1, 1, 1, 5, 5]),
   (mkRat (-1) 288, [1, 1, 2, 2, 2, 2, 3]),
   (mkRat (1) 14, [1, 1, 2, 2, 7]),
   (mkRat (-1) 18, [1, 1, 2, 3, 6]),
   (mkRat (1) 10, [1, 1, 2, 4, 5]),
   (mkRat (-4) 45, [1, 1, 3, 3, 5]),
   (mkRat (-1) 48, [1, 1, 3, 4, 4]),
   (mkRat (2) 11, [1, 1, 11]),
   (mkRat (-1) 120, [2, 2, 2, 2, 5]),
   (mkRat (1) 72, [2, 2, 2, 3, 4]),
   (mkRat (7) 162, [2, 2, 3, 3, 3]),
   (mkRat (-1) 9, [2, 2, 9]),
   (mkRat (1) 12, [2, 3, 8]),
   (mkRat (-1) 7, [2, 4, 7]),
   (mkRat (-2) 15, [2, 5, 6]),
   (mkRat (8) 63, [3, 3, 7]),
   (mkRat (1) 18, [3, 4, 6]),
   (mkRat (2) 75, [3, 5, 5]),
   (mkRat (-1) 20, [4, 4, 5]),
   (mkRat (-4) 13, [13])]

def sc611 : RawPoly ℕ :=
  [sc611Part0,
   sc611Part1,
   sc611Part2].flatten

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc611_check :
    reduceTwo (prependC 1 sc221 ++ scaleR (-1) (prependC 0 sc222)) = sc611 := by
  decide +kernel

theorem sc611_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc611 = evRc a c (expWordR [1, 1, 3] (8)) := by
  rw [← sc611_check]
  exact expTwo_step _ _ hc 0 [1, 3] (8)
    sc221 sc222 (sc221_sound a c hc) (sc222_sound a c hc)

def sc612Part0 : RawPoly ℕ :=
  [(mkRat (-1) 10478160, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (1) 106920, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3]),
   (mkRat (-1) 16800, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2]),
   (mkRat (-1) 2835, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5]),
   (mkRat (-1) 720, [0, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4]),
   (mkRat (1) 810, [0, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3]),
   (mkRat (1) 840, [0, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3]),
   (mkRat (-1) 245, [0, 1, 1, 1, 1, 1, 1, 1, 7]),
   (mkRat (-1) 1728, [0, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2]),
   (mkRat (-1) 108, [0, 1, 1, 1, 1, 1, 1, 2, 6]),
   (mkRat (1) 270, [0, 1, 1, 1, 1, 1, 1, 3, 5]),
   (mkRat (-1) 288, [0, 1, 1, 1, 1, 1, 1, 4, 4]),
   (mkRat (-1) 150, [0, 1, 1, 1, 1, 1, 2, 2, 5]),
   (mkRat (1) 180, [0, 1, 1, 1, 1, 1, 2, 3, 4]),
   (mkRat (7) 1215, [0, 1, 1, 1, 1, 1, 3, 3, 3]),
   (mkRat (-2) 135, [0, 1, 1, 1, 1, 1, 9]),
   (mkRat (-1) 864, [0, 1, 1, 1, 2, 2, 2, 2, 3]),
   (mkRat (1) 42, [0, 1, 1, 1, 2, 2, 7]),
   (mkRat (-1) 54, [0, 1, 1, 1, 2, 3, 6]),
   (mkRat (1) 30, [0, 1, 1, 1, 2, 4, 5]),
   (mkRat (-4) 135, [0, 1, 1, 1, 3, 3, 5]),
   (mkRat (-1) 144, [0, 1, 1, 1, 3, 4, 4]),
   (mkRat (2) 33, [0, 1, 1, 1, 11]),
   (mkRat (1) 5760, [0, 1, 1, 2, 2, 2, 2, 2, 2])]

def sc612Part1 : RawPoly ℕ :=
  [(mkRat (1) 72, [0, 1, 1, 2, 2, 2, 6]),
   (mkRat (-1) 60, [0, 1, 1, 2, 2, 3, 5]),
   (mkRat (1) 64, [0, 1, 1, 2, 2, 4, 4]),
   (mkRat (-1) 18, [0, 1, 1, 2, 3, 3, 4]),
   (mkRat (1) 10, [0, 1, 1, 2, 10]),
   (mkRat (-5) 486, [0, 1, 1, 3, 3, 3, 3]),
   (mkRat (-1) 27, [0, 1, 1, 3, 9]),
   (mkRat (1) 16, [0, 1, 1, 4, 8]),
   (mkRat (2) 35, [0, 1, 1, 5, 7]),
   (mkRat (1) 36, [0, 1, 1, 6, 6]),
   (mkRat (-1) 960, [0, 2, 2, 2, 2, 2, 4]),
   (mkRat (1) 216, [0, 2, 2, 2, 2, 3, 3]),
   (mkRat (-1) 48, [0, 2, 2, 2, 8]),
   (mkRat (1) 42, [0, 2, 2, 3, 7]),
   (mkRat (-1) 24, [0, 2, 2, 4, 6]),
   (mkRat (-1) 50, [0, 2, 2, 5, 5]),
   (mkRat (2) 27, [0, 2, 3, 3, 6]),
   (mkRat (1) 30, [0, 2, 3, 4, 5]),
   (mkRat (-1) 96, [0, 2, 4, 4, 4]),
   (mkRat (-1) 6, [0, 2, 12]),
   (mkRat (14) 405, [0, 3, 3, 3, 5]),
   (mkRat (1) 36, [0, 3, 3, 4, 4]),
   (mkRat (2) 33, [0, 3, 11]),
   (mkRat (-1) 10, [0, 4, 10])]

def sc612Part2 : RawPoly ℕ :=
  [(mkRat (-4) 45, [0, 5, 9]),
   (mkRat (-1) 12, [0, 6, 8]),
   (mkRat (-2) 49, [0, 7, 7]),
   (mkRat (-1) 170100, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2]),
   (mkRat (-1) 8400, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4]),
   (mkRat (1) 3402, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3]),
   (mkRat (-1) 2160, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2]),
   (mkRat (-1) 540, [1, 1, 1, 1, 1, 1, 1, 1, 6]),
   (mkRat (-1) 175, [1, 1, 1, 1, 1, 1, 1, 2, 5]),
   (mkRat (1) 420, [1, 1, 1, 1, 1, 1, 1, 3, 4]),
   (mkRat (-1) 144, [1, 1, 1, 1, 1, 1, 2, 2, 4]),
   (mkRat (1) 81, [1, 1, 1, 1, 1, 1, 2, 3, 3]),
   (mkRat (-1) 72, [1, 1, 1, 1, 1, 1, 8]),
   (mkRat (1) 540, [1, 1, 1, 1, 1, 2, 2, 2, 3]),
   (mkRat (-2) 105, [1, 1, 1, 1, 1, 2, 7]),
   (mkRat (1) 135, [1, 1, 1, 1, 1, 3, 6]),
   (mkRat (-1) 75, [1, 1, 1, 1, 1, 4, 5]),
   (mkRat (1) 90, [1, 1, 1, 2, 2, 2, 5]),
   (mkRat (-1) 72, [1, 1, 1, 2, 2, 3, 4]),
   (mkRat (-7) 243, [1, 1, 1, 2, 3, 3, 3]),
   (mkRat (2) 27, [1, 1, 1, 2, 9]),
   (mkRat (-1) 36, [1, 1, 1, 3, 8]),
   (mkRat (1) 21, [1, 1, 1, 4, 7]),
   (mkRat (2) 45, [1, 1, 1, 5, 6])]

def sc612Part3 : RawPoly ℕ :=
  [(mkRat (1) 192, [1, 1, 2, 2, 2, 2, 4]),
   (mkRat (-1) 54, [1, 1, 2, 2, 2, 3, 3]),
   (mkRat (1) 16, [1, 1, 2, 2, 8]),
   (mkRat (-1) 21, [1, 1, 2, 3, 7]),
   (mkRat (1) 12, [1, 1, 2, 4, 6]),
   (mkRat (1) 25, [1, 1, 2, 5, 5]),
   (mkRat (-2) 27, [1, 1, 3, 3, 6]),
   (mkRat (-1) 30, [1, 1, 3, 4, 5]),
   (mkRat (1) 96, [1, 1, 4, 4, 4]),
   (mkRat (1) 6, [1, 1, 12]),
   (mkRat (-1) 20160, [2, 2, 2, 2, 2, 2, 2]),
   (mkRat (-1) 144, [2, 2, 2, 2, 6]),
   (mkRat (1) 90, [2, 2, 2, 3, 5]),
   (mkRat (-1) 96, [2, 2, 2, 4, 4]),
   (mkRat (1) 18, [2, 2, 3, 3, 4]),
   (mkRat (-1) 10, [2, 2, 10]),
   (mkRat (5) 243, [2, 3, 3, 3, 3]),
   (mkRat (2) 27, [2, 3, 9]),
   (mkRat (-1) 8, [2, 4, 8]),
   (mkRat (-4) 35, [2, 5, 7]),
   (mkRat (-1) 18, [2, 6, 6]),
   (mkRat (1) 9, [3, 3, 8]),
   (mkRat (1) 21, [3, 4, 7]),
   (mkRat (2) 45, [3, 5, 6])]

def sc612Part4 : RawPoly ℕ :=
  [(mkRat (-1) 24, [4, 4, 6]),
   (mkRat (-1) 25, [4, 5, 5]),
   (mkRat (-2) 7, [14])]

def sc612 : RawPoly ℕ :=
  [sc612Part0,
   sc612Part1,
   sc612Part2,
   sc612Part3,
   sc612Part4].flatten

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc612_check :
    reduceTwo (prependC 1 sc222 ++ scaleR (-1) (prependC 0 sc223)) = sc612 := by
  decide +kernel

theorem sc612_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc612 = evRc a c (expWordR [1, 1, 3] (9)) := by
  rw [← sc612_check]
  exact expTwo_step _ _ hc 0 [1, 3] (9)
    sc222 sc223 (sc222_sound a c hc) (sc223_sound a c hc)

def sc613Part0 : RawPoly ℕ :=
  [(mkRat (-1) 1801800, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2]),
   (mkRat (-1) 71280, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4]),
   (mkRat (1) 25200, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3]),
   (mkRat (-1) 13608, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2]),
   (mkRat (-1) 3402, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6]),
   (mkRat (-1) 900, [0, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5]),
   (mkRat (1) 2160, [0, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4]),
   (mkRat (-1) 560, [0, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4]),
   (mkRat (1) 315, [0, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3]),
   (mkRat (-1) 280, [0, 1, 1, 1, 1, 1, 1, 1, 8]),
   (mkRat (1) 1296, [0, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3]),
   (mkRat (-1) 126, [0, 1, 1, 1, 1, 1, 1, 2, 7]),
   (mkRat (1) 324, [0, 1, 1, 1, 1, 1, 1, 3, 6]),
   (mkRat (-1) 180, [0, 1, 1, 1, 1, 1, 1, 4, 5]),
   (mkRat (-1) 7200, [0, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2]),
   (mkRat (-1) 180, [0, 1, 1, 1, 1, 1, 2, 2, 6]),
   (mkRat (1) 225, [0, 1, 1, 1, 1, 1, 2, 3, 5]),
   (mkRat (-1) 240, [0, 1, 1, 1, 1, 1, 2, 4, 4]),
   (mkRat (1) 135, [0, 1, 1, 1, 1, 1, 3, 3, 4]),
   (mkRat (-1) 75, [0, 1, 1, 1, 1, 1, 10]),
   (mkRat (1) 576, [0, 1, 1, 1, 2, 2, 2, 2, 4]),
   (mkRat (-1) 162, [0, 1, 1, 1, 2, 2, 2, 3, 3]),
   (mkRat (1) 48, [0, 1, 1, 1, 2, 2, 8]),
   (mkRat (-1) 63, [0, 1, 1, 1, 2, 3, 7])]

def sc613Part1 : RawPoly ℕ :=
  [(mkRat (1) 36, [0, 1, 1, 1, 2, 4, 6]),
   (mkRat (1) 75, [0, 1, 1, 1, 2, 5, 5]),
   (mkRat (-2) 81, [0, 1, 1, 1, 3, 3, 6]),
   (mkRat (-1) 90, [0, 1, 1, 1, 3, 4, 5]),
   (mkRat (1) 288, [0, 1, 1, 1, 4, 4, 4]),
   (mkRat (1) 18, [0, 1, 1, 1, 12]),
   (mkRat (-1) 2880, [0, 1, 1, 2, 2, 2, 2, 2, 3]),
   (mkRat (1) 84, [0, 1, 1, 2, 2, 2, 7]),
   (mkRat (-1) 72, [0, 1, 1, 2, 2, 3, 6]),
   (mkRat (1) 40, [0, 1, 1, 2, 2, 4, 5]),
   (mkRat (-2) 45, [0, 1, 1, 2, 3, 3, 5]),
   (mkRat (-1) 96, [0, 1, 1, 2, 3, 4, 4]),
   (mkRat (1) 11, [0, 1, 1, 2, 11]),
   (mkRat (-7) 324, [0, 1, 1, 3, 3, 3, 4]),
   (mkRat (-1) 30, [0, 1, 1, 3, 10]),
   (mkRat (1) 18, [0, 1, 1, 4, 9]),
   (mkRat (1) 20, [0, 1, 1, 5, 8]),
   (mkRat (1) 21, [0, 1, 1, 6, 7]),
   (mkRat (-1) 1200, [0, 2, 2, 2, 2, 2, 5]),
   (mkRat (1) 576, [0, 2, 2, 2, 2, 3, 4]),
   (mkRat (7) 972, [0, 2, 2, 2, 3, 3, 3]),
   (mkRat (-1) 54, [0, 2, 2, 2, 9]),
   (mkRat (1) 48, [0, 2, 2, 3, 8]),
   (mkRat (-1) 28, [0, 2, 2, 4, 7])]

def sc613Part2 : RawPoly ℕ :=
  [(mkRat (-1) 30, [0, 2, 2, 5, 6]),
   (mkRat (4) 63, [0, 2, 3, 3, 7]),
   (mkRat (1) 36, [0, 2, 3, 4, 6]),
   (mkRat (1) 75, [0, 2, 3, 5, 5]),
   (mkRat (-1) 40, [0, 2, 4, 4, 5]),
   (mkRat (-2) 13, [0, 2, 13]),
   (mkRat (7) 243, [0, 3, 3, 3, 6]),
   (mkRat (2) 45, [0, 3, 3, 4, 5]),
   (mkRat (1) 288, [0, 3, 4, 4, 4]),
   (mkRat (1) 18, [0, 3, 12]),
   (mkRat (-1) 11, [0, 4, 11]),
   (mkRat (-2) 25, [0, 5, 10]),
   (mkRat (-2) 27, [0, 6, 9]),
   (mkRat (-1) 14, [0, 7, 8]),
   (mkRat (-1) 66339000, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (1) 510300, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3]),
   (mkRat (-1) 71280, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2]),
   (mkRat (-1) 10500, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5]),
   (mkRat (-1) 2268, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4]),
   (mkRat (2) 5103, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3]),
   (mkRat (1) 2160, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3]),
   (mkRat (-1) 630, [1, 1, 1, 1, 1, 1, 1, 1, 7]),
   (mkRat (-1) 3360, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2]),
   (mkRat (-1) 210, [1, 1, 1, 1, 1, 1, 1, 2, 6])]

def sc613Part3 : RawPoly ℕ :=
  [(mkRat (1) 525, [1, 1, 1, 1, 1, 1, 1, 3, 5]),
   (mkRat (-1) 560, [1, 1, 1, 1, 1, 1, 1, 4, 4]),
   (mkRat (-1) 180, [1, 1, 1, 1, 1, 1, 2, 2, 5]),
   (mkRat (1) 216, [1, 1, 1, 1, 1, 1, 2, 3, 4]),
   (mkRat (7) 1458, [1, 1, 1, 1, 1, 1, 3, 3, 3]),
   (mkRat (-1) 81, [1, 1, 1, 1, 1, 1, 9]),
   (mkRat (-1) 360, [1, 1, 1, 1, 1, 2, 2, 2, 4]),
   (mkRat (1) 135, [1, 1, 1, 1, 1, 2, 2, 3, 3]),
   (mkRat (-1) 60, [1, 1, 1, 1, 1, 2, 8]),
   (mkRat (2) 315, [1, 1, 1, 1, 1, 3, 7]),
   (mkRat (-1) 90, [1, 1, 1, 1, 1, 4, 6]),
   (mkRat (-2) 375, [1, 1, 1, 1, 1, 5, 5]),
   (mkRat (1) 8640, [1, 1, 1, 2, 2, 2, 2, 2, 2]),
   (mkRat (1) 108, [1, 1, 1, 2, 2, 2, 6]),
   (mkRat (-1) 90, [1, 1, 1, 2, 2, 3, 5]),
   (mkRat (1) 96, [1, 1, 1, 2, 2, 4, 4]),
   (mkRat (-1) 27, [1, 1, 1, 2, 3, 3, 4]),
   (mkRat (1) 15, [1, 1, 1, 2, 10]),
   (mkRat (-5) 729, [1, 1, 1, 3, 3, 3, 3]),
   (mkRat (-2) 81, [1, 1, 1, 3, 9]),
   (mkRat (1) 24, [1, 1, 1, 4, 8]),
   (mkRat (4) 105, [1, 1, 1, 5, 7]),
   (mkRat (1) 54, [1, 1, 1, 6, 6]),
   (mkRat (1) 240, [1, 1, 2, 2, 2, 2, 5])]

def sc613Part4 : RawPoly ℕ :=
  [(mkRat (-1) 144, [1, 1, 2, 2, 2, 3, 4]),
   (mkRat (-7) 324, [1, 1, 2, 2, 3, 3, 3]),
   (mkRat (1) 18, [1, 1, 2, 2, 9]),
   (mkRat (-1) 24, [1, 1, 2, 3, 8]),
   (mkRat (1) 14, [1, 1, 2, 4, 7]),
   (mkRat (1) 15, [1, 1, 2, 5, 6]),
   (mkRat (-4) 63, [1, 1, 3, 3, 7]),
   (mkRat (-1) 36, [1, 1, 3, 4, 6]),
   (mkRat (-1) 75, [1, 1, 3, 5, 5]),
   (mkRat (1) 40, [1, 1, 4, 4, 5]),
   (mkRat (2) 13, [1, 1, 13]),
   (mkRat (1) 8640, [2, 2, 2, 2, 2, 2, 3]),
   (mkRat (-1) 168, [2, 2, 2, 2, 7]),
   (mkRat (1) 108, [2, 2, 2, 3, 6]),
   (mkRat (-1) 60, [2, 2, 2, 4, 5]),
   (mkRat (2) 45, [2, 2, 3, 3, 5]),
   (mkRat (1) 96, [2, 2, 3, 4, 4]),
   (mkRat (-1) 11, [2, 2, 11]),
   (mkRat (7) 162, [2, 3, 3, 3, 4]),
   (mkRat (1) 15, [2, 3, 10]),
   (mkRat (-1) 9, [2, 4, 9]),
   (mkRat (-1) 10, [2, 5, 8]),
   (mkRat (-2) 21, [2, 6, 7]),
   (mkRat (13) 3645, [3, 3, 3, 3, 3])]

def sc613Part5 : RawPoly ℕ :=
  [(mkRat (8) 81, [3, 3, 9]),
   (mkRat (1) 24, [3, 4, 8]),
   (mkRat (4) 105, [3, 5, 7]),
   (mkRat (1) 54, [3, 6, 6]),
   (mkRat (-1) 28, [4, 4, 7]),
   (mkRat (-1) 15, [4, 5, 6]),
   (mkRat (-4) 375, [5, 5, 5]),
   (mkRat (-4) 15, [15])]

def sc613 : RawPoly ℕ :=
  [sc613Part0,
   sc613Part1,
   sc613Part2,
   sc613Part3,
   sc613Part4,
   sc613Part5].flatten

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc613_check :
    reduceTwo (prependC 1 sc223 ++ scaleR (-1) (prependC 0 sc224)) = sc613 := by
  decide +kernel

theorem sc613_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc613 = evRc a c (expWordR [1, 1, 3] (10)) := by
  rw [← sc613_check]
  exact expTwo_step _ _ hc 0 [1, 3] (10)
    sc223 sc224 (sc223_sound a c hc) (sc224_sound a c hc)

def sc614Part0 : RawPoly ℕ :=
  [(mkRat (-1) 908107200, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (1) 5405400, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3]),
   (mkRat (-1) 680400, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2]),
   (mkRat (-1) 89100, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5]),
   (mkRat (-1) 16800, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4]),
   (mkRat (1) 18900, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3]),
   (mkRat (1) 13608, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3]),
   (mkRat (-1) 3969, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7]),
   (mkRat (-1) 17280, [0, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2]),
   (mkRat (-1) 1080, [0, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6]),
   (mkRat (1) 2700, [0, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5]),
   (mkRat (-1) 2880, [0, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4]),
   (mkRat (-1) 700, [0, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5]),
   (mkRat (1) 840, [0, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4]),
   (mkRat (1) 810, [0, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3]),
   (mkRat (-1) 315, [0, 1, 1, 1, 1, 1, 1, 1, 9]),
   (mkRat (-1) 864, [0, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4]),
   (mkRat (1) 324, [0, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3]),
   (mkRat (-1) 144, [0, 1, 1, 1, 1, 1, 1, 2, 8]),
   (mkRat (1) 378, [0, 1, 1, 1, 1, 1, 1, 3, 7]),
   (mkRat (-1) 216, [0, 1, 1, 1, 1, 1, 1, 4, 6]),
   (mkRat (-1) 450, [0, 1, 1, 1, 1, 1, 1, 5, 5]),
   (mkRat (1) 4320, [0, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3]),
   (mkRat (-1) 210, [0, 1, 1, 1, 1, 1, 2, 2, 7])]

def sc614Part1 : RawPoly ℕ :=
  [(mkRat (1) 270, [0, 1, 1, 1, 1, 1, 2, 3, 6]),
   (mkRat (-1) 150, [0, 1, 1, 1, 1, 1, 2, 4, 5]),
   (mkRat (4) 675, [0, 1, 1, 1, 1, 1, 3, 3, 5]),
   (mkRat (1) 720, [0, 1, 1, 1, 1, 1, 3, 4, 4]),
   (mkRat (-2) 165, [0, 1, 1, 1, 1, 1, 11]),
   (mkRat (1) 720, [0, 1, 1, 1, 2, 2, 2, 2, 5]),
   (mkRat (-1) 432, [0, 1, 1, 1, 2, 2, 2, 3, 4]),
   (mkRat (-7) 972, [0, 1, 1, 1, 2, 2, 3, 3, 3]),
   (mkRat (1) 54, [0, 1, 1, 1, 2, 2, 9]),
   (mkRat (-1) 72, [0, 1, 1, 1, 2, 3, 8]),
   (mkRat (1) 42, [0, 1, 1, 1, 2, 4, 7]),
   (mkRat (1) 45, [0, 1, 1, 1, 2, 5, 6]),
   (mkRat (-4) 189, [0, 1, 1, 1, 3, 3, 7]),
   (mkRat (-1) 108, [0, 1, 1, 1, 3, 4, 6]),
   (mkRat (-1) 225, [0, 1, 1, 1, 3, 5, 5]),
   (mkRat (1) 120, [0, 1, 1, 1, 4, 4, 5]),
   (mkRat (2) 39, [0, 1, 1, 1, 13]),
   (mkRat (1) 1920, [0, 1, 1, 2, 2, 2, 2, 2, 4]),
   (mkRat (-1) 432, [0, 1, 1, 2, 2, 2, 2, 3, 3]),
   (mkRat (1) 96, [0, 1, 1, 2, 2, 2, 8]),
   (mkRat (-1) 84, [0, 1, 1, 2, 2, 3, 7]),
   (mkRat (1) 48, [0, 1, 1, 2, 2, 4, 6]),
   (mkRat (1) 100, [0, 1, 1, 2, 2, 5, 5]),
   (mkRat (-1) 27, [0, 1, 1, 2, 3, 3, 6])]

def sc614Part2 : RawPoly ℕ :=
  [(mkRat (-1) 60, [0, 1, 1, 2, 3, 4, 5]),
   (mkRat (1) 192, [0, 1, 1, 2, 4, 4, 4]),
   (mkRat (1) 12, [0, 1, 1, 2, 12]),
   (mkRat (-7) 405, [0, 1, 1, 3, 3, 3, 5]),
   (mkRat (-1) 72, [0, 1, 1, 3, 3, 4, 4]),
   (mkRat (-1) 33, [0, 1, 1, 3, 11]),
   (mkRat (1) 20, [0, 1, 1, 4, 10]),
   (mkRat (2) 45, [0, 1, 1, 5, 9]),
   (mkRat (1) 24, [0, 1, 1, 6, 8]),
   (mkRat (1) 49, [0, 1, 1, 7, 7]),
   (mkRat (-1) 322560, [0, 2, 2, 2, 2, 2, 2, 2, 2]),
   (mkRat (-1) 1440, [0, 2, 2, 2, 2, 2, 6]),
   (mkRat (1) 720, [0, 2, 2, 2, 2, 3, 5]),
   (mkRat (-1) 768, [0, 2, 2, 2, 2, 4, 4]),
   (mkRat (1) 108, [0, 2, 2, 2, 3, 3, 4]),
   (mkRat (-1) 60, [0, 2, 2, 2, 10]),
   (mkRat (5) 972, [0, 2, 2, 3, 3, 3, 3]),
   (mkRat (1) 54, [0, 2, 2, 3, 9]),
   (mkRat (-1) 32, [0, 2, 2, 4, 8]),
   (mkRat (-1) 35, [0, 2, 2, 5, 7]),
   (mkRat (-1) 72, [0, 2, 2, 6, 6]),
   (mkRat (1) 18, [0, 2, 3, 3, 8]),
   (mkRat (1) 42, [0, 2, 3, 4, 7]),
   (mkRat (1) 45, [0, 2, 3, 5, 6])]

def sc614Part3 : RawPoly ℕ :=
  [(mkRat (-1) 48, [0, 2, 4, 4, 6]),
   (mkRat (-1) 50, [0, 2, 4, 5, 5]),
   (mkRat (-1) 7, [0, 2, 14]),
   (mkRat (2) 81, [0, 3, 3, 3, 7]),
   (mkRat (1) 27, [0, 3, 3, 4, 6]),
   (mkRat (4) 225, [0, 3, 3, 5, 5]),
   (mkRat (1) 120, [0, 3, 4, 4, 5]),
   (mkRat (2) 39, [0, 3, 13]),
   (mkRat (-1) 768, [0, 4, 4, 4, 4]),
   (mkRat (-1) 12, [0, 4, 12]),
   (mkRat (-4) 55, [0, 5, 11]),
   (mkRat (-1) 15, [0, 6, 10]),
   (mkRat (-4) 63, [0, 7, 9]),
   (mkRat (-1) 32, [0, 8, 8]),
   (mkRat (-1) 10478160, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2]),
   (mkRat (-1) 340200, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4]),
   (mkRat (1) 106920, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3]),
   (mkRat (-1) 50400, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2]),
   (mkRat (-1) 12600, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6]),
   (mkRat (-1) 2835, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5]),
   (mkRat (1) 6804, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4]),
   (mkRat (-1) 1440, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4]),
   (mkRat (1) 810, [1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3]),
   (mkRat (-1) 720, [1, 1, 1, 1, 1, 1, 1, 1, 8])]

def sc614Part4 : RawPoly ℕ :=
  [(mkRat (1) 2520, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3]),
   (mkRat (-1) 245, [1, 1, 1, 1, 1, 1, 1, 2, 7]),
   (mkRat (1) 630, [1, 1, 1, 1, 1, 1, 1, 3, 6]),
   (mkRat (-1) 350, [1, 1, 1, 1, 1, 1, 1, 4, 5]),
   (mkRat (-1) 8640, [1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2]),
   (mkRat (-1) 216, [1, 1, 1, 1, 1, 1, 2, 2, 6]),
   (mkRat (1) 270, [1, 1, 1, 1, 1, 1, 2, 3, 5]),
   (mkRat (-1) 288, [1, 1, 1, 1, 1, 1, 2, 4, 4]),
   (mkRat (1) 162, [1, 1, 1, 1, 1, 1, 3, 3, 4]),
   (mkRat (-1) 90, [1, 1, 1, 1, 1, 1, 10]),
   (mkRat (-1) 450, [1, 1, 1, 1, 1, 2, 2, 2, 5]),
   (mkRat (1) 360, [1, 1, 1, 1, 1, 2, 2, 3, 4]),
   (mkRat (7) 1215, [1, 1, 1, 1, 1, 2, 3, 3, 3]),
   (mkRat (-2) 135, [1, 1, 1, 1, 1, 2, 9]),
   (mkRat (1) 180, [1, 1, 1, 1, 1, 3, 8]),
   (mkRat (-1) 105, [1, 1, 1, 1, 1, 4, 7]),
   (mkRat (-2) 225, [1, 1, 1, 1, 1, 5, 6]),
   (mkRat (-1) 4320, [1, 1, 1, 2, 2, 2, 2, 2, 3]),
   (mkRat (1) 126, [1, 1, 1, 2, 2, 2, 7]),
   (mkRat (-1) 108, [1, 1, 1, 2, 2, 3, 6]),
   (mkRat (1) 60, [1, 1, 1, 2, 2, 4, 5]),
   (mkRat (-4) 135, [1, 1, 1, 2, 3, 3, 5]),
   (mkRat (-1) 144, [1, 1, 1, 2, 3, 4, 4]),
   (mkRat (2) 33, [1, 1, 1, 2, 11])]

def sc614Part5 : RawPoly ℕ :=
  [(mkRat (-7) 486, [1, 1, 1, 3, 3, 3, 4]),
   (mkRat (-1) 45, [1, 1, 1, 3, 10]),
   (mkRat (1) 27, [1, 1, 1, 4, 9]),
   (mkRat (1) 30, [1, 1, 1, 5, 8]),
   (mkRat (2) 63, [1, 1, 1, 6, 7]),
   (mkRat (1) 40320, [1, 1, 2, 2, 2, 2, 2, 2, 2]),
   (mkRat (1) 288, [1, 1, 2, 2, 2, 2, 6]),
   (mkRat (-1) 180, [1, 1, 2, 2, 2, 3, 5]),
   (mkRat (1) 192, [1, 1, 2, 2, 2, 4, 4]),
   (mkRat (-1) 36, [1, 1, 2, 2, 3, 3, 4]),
   (mkRat (1) 20, [1, 1, 2, 2, 10]),
   (mkRat (-5) 486, [1, 1, 2, 3, 3, 3, 3]),
   (mkRat (-1) 27, [1, 1, 2, 3, 9]),
   (mkRat (1) 16, [1, 1, 2, 4, 8]),
   (mkRat (2) 35, [1, 1, 2, 5, 7]),
   (mkRat (1) 36, [1, 1, 2, 6, 6]),
   (mkRat (-1) 18, [1, 1, 3, 3, 8]),
   (mkRat (-1) 42, [1, 1, 3, 4, 7]),
   (mkRat (-1) 45, [1, 1, 3, 5, 6]),
   (mkRat (1) 48, [1, 1, 4, 4, 6]),
   (mkRat (1) 50, [1, 1, 4, 5, 5]),
   (mkRat (1) 7, [1, 1, 14]),
   (mkRat (-1) 5760, [2, 2, 2, 2, 2, 2, 4]),
   (mkRat (1) 1080, [2, 2, 2, 2, 2, 3, 3])]

def sc614Part6 : RawPoly ℕ :=
  [(mkRat (-1) 192, [2, 2, 2, 2, 8]),
   (mkRat (1) 126, [2, 2, 2, 3, 7]),
   (mkRat (-1) 72, [2, 2, 2, 4, 6]),
   (mkRat (-1) 150, [2, 2, 2, 5, 5]),
   (mkRat (1) 27, [2, 2, 3, 3, 6]),
   (mkRat (1) 60, [2, 2, 3, 4, 5]),
   (mkRat (-1) 192, [2, 2, 4, 4, 4]),
   (mkRat (-1) 12, [2, 2, 12]),
   (mkRat (14) 405, [2, 3, 3, 3, 5]),
   (mkRat (1) 36, [2, 3, 3, 4, 4]),
   (mkRat (2) 33, [2, 3, 11]),
   (mkRat (-1) 10, [2, 4, 10]),
   (mkRat (-4) 45, [2, 5, 9]),
   (mkRat (-1) 12, [2, 6, 8]),
   (mkRat (-2) 49, [2, 7, 7]),
   (mkRat (5) 486, [3, 3, 3, 3, 4]),
   (mkRat (4) 45, [3, 3, 10]),
   (mkRat (1) 27, [3, 4, 9]),
   (mkRat (1) 30, [3, 5, 8]),
   (mkRat (2) 63, [3, 6, 7]),
   (mkRat (-1) 32, [4, 4, 8]),
   (mkRat (-2) 35, [4, 5, 7]),
   (mkRat (-1) 36, [4, 6, 6]),
   (mkRat (-2) 75, [5, 5, 6])]

def sc614Part7 : RawPoly ℕ :=
  [(mkRat (-1) 4, [16])]

def sc614 : RawPoly ℕ :=
  [sc614Part0,
   sc614Part1,
   sc614Part2,
   sc614Part3,
   sc614Part4,
   sc614Part5,
   sc614Part6,
   sc614Part7].flatten

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc614_check :
    reduceTwo (prependC 1 sc224 ++ scaleR (-1) (prependC 0 sc225)) = sc614 := by
  decide +kernel

theorem sc614_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc614 = evRc a c (expWordR [1, 1, 3] (11)) := by
  rw [← sc614_check]
  exact expTwo_step _ _ hc 0 [1, 3] (11)
    sc224 sc225 (sc224_sound a c hc) (sc225_sound a c hc)

def sc615 : RawPoly ℕ :=
  []

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc615_check :
    reduceTwo (prependC 1 sc226 ++ scaleR (-1) (prependC 0 sc227)) = sc615 := by
  decide +kernel

theorem sc615_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc615 = evRc a c (expWordR [1, 1, 4] (-7)) := by
  rw [← sc615_check]
  exact expTwo_step _ _ hc 0 [1, 4] (-7)
    sc226 sc227 (sc226_sound a c hc) (sc227_sound a c hc)

def sc616 : RawPoly ℕ :=
  [(-2, [0])]

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc616_check :
    reduceTwo (prependC 1 sc227 ++ scaleR (-1) (prependC 0 sc228)) = sc616 := by
  decide +kernel

theorem sc616_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc616 = evRc a c (expWordR [1, 1, 4] (-6)) := by
  rw [← sc616_check]
  exact expTwo_step _ _ hc 0 [1, 4] (-6)
    sc227 sc228 (sc227_sound a c hc) (sc228_sound a c hc)

def sc617 : RawPoly ℕ :=
  []

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc617_check :
    reduceTwo (prependC 1 sc228 ++ scaleR (-1) (prependC 0 sc229)) = sc617 := by
  decide +kernel

theorem sc617_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc617 = evRc a c (expWordR [1, 1, 4] (-5)) := by
  rw [← sc617_check]
  exact expTwo_step _ _ hc 0 [1, 4] (-5)
    sc228 sc229 (sc228_sound a c hc) (sc229_sound a c hc)

def sc618 : RawPoly ℕ :=
  [(1, [0, 1, 1]),
   (-2, [2])]

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc618_check :
    reduceTwo (prependC 1 sc229 ++ scaleR (-1) (prependC 0 sc230)) = sc618 := by
  decide +kernel

theorem sc618_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc618 = evRc a c (expWordR [1, 1, 4] (-4)) := by
  rw [← sc618_check]
  exact expTwo_step _ _ hc 0 [1, 4] (-4)
    sc229 sc230 (sc229_sound a c hc) (sc230_sound a c hc)

def sc619 : RawPoly ℕ :=
  [(mkRat (2) 3, [1, 1, 1]),
   (mkRat (-4) 3, [3])]

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc619_check :
    reduceTwo (prependC 1 sc230 ++ scaleR (-1) (prependC 0 sc231)) = sc619 := by
  decide +kernel

theorem sc619_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc619 = evRc a c (expWordR [1, 1, 4] (-3)) := by
  rw [← sc619_check]
  exact expTwo_step _ _ hc 0 [1, 4] (-3)
    sc230 sc231 (sc230_sound a c hc) (sc231_sound a c hc)

def sc620 : RawPoly ℕ :=
  [(mkRat (-1) 2, [0, 2, 2]),
   (1, [1, 1, 2]),
   (1, [4])]

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc620_check :
    reduceTwo (prependC 1 sc231 ++ scaleR (-1) (prependC 0 sc232)) = sc620 := by
  decide +kernel

theorem sc620_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc620 = evRc a c (expWordR [1, 1, 4] (-2)) := by
  rw [← sc620_check]
  exact expTwo_step _ _ hc 0 [1, 4] (-2)
    sc231 sc232 (sc231_sound a c hc) (sc232_sound a c hc)

def sc621 : RawPoly ℕ :=
  [(mkRat (1) 3, [0, 1, 1, 1, 2]),
   (mkRat (-2) 3, [0, 2, 3]),
   (mkRat (-2) 15, [1, 1, 1, 1, 1]),
   (mkRat (2) 3, [1, 1, 3]),
   (mkRat (-4) 5, [5])]

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc621_check :
    reduceTwo (prependC 1 sc232 ++ scaleR (-1) (prependC 0 sc233)) = sc621 := by
  decide +kernel

theorem sc621_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc621 = evRc a c (expWordR [1, 1, 4] (-1)) := by
  rw [← sc621_check]
  exact expTwo_step _ _ hc 0 [1, 4] (-1)
    sc232 sc233 (sc232_sound a c hc) (sc233_sound a c hc)

def sc622 : RawPoly ℕ :=
  [(mkRat (-1) 18, [0, 1, 1, 1, 1, 1, 1]),
   (mkRat (2) 9, [0, 1, 1, 1, 3]),
   (mkRat (1) 4, [0, 1, 1, 2, 2]),
   (mkRat (1) 2, [0, 2, 4]),
   (mkRat (-2) 9, [0, 3, 3]),
   (mkRat (-1) 2, [1, 1, 4]),
   (mkRat (-1) 6, [2, 2, 2]),
   (mkRat (-2) 3, [6])]

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc622_check :
    reduceTwo (prependC 1 sc233 ++ scaleR (-1) (prependC 0 sc234)) = sc622 := by
  decide +kernel

theorem sc622_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc622 = evRc a c (expWordR [1, 1, 4] (0)) := by
  rw [← sc622_check]
  exact expTwo_step _ _ hc 0 [1, 4] (0)
    sc233 sc234 (sc233_sound a c hc) (sc234_sound a c hc)

def sc623 : RawPoly ℕ :=
  [(mkRat (-1) 15, [0, 1, 1, 1, 1, 1, 2]),
   (mkRat (-1) 6, [0, 1, 1, 1, 4]),
   (mkRat (1) 3, [0, 1, 1, 2, 3]),
   (mkRat (-2) 5, [0, 2, 5]),
   (mkRat (1) 3, [0, 3, 4]),
   (mkRat (-1) 35, [1, 1, 1, 1, 1, 1, 1]),
   (mkRat (1) 6, [1, 1, 1, 2, 2]),
   (mkRat (2) 5, [1, 1, 5]),
   (mkRat (-1) 3, [2, 2, 3]),
   (mkRat (-4) 7, [7])]

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc623_check :
    reduceTwo (prependC 1 sc234 ++ scaleR (-1) (prependC 0 sc235)) = sc623 := by
  decide +kernel

theorem sc623_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc623 = evRc a c (expWordR [1, 1, 4] (1)) := by
  rw [← sc623_check]
  exact expTwo_step _ _ hc 0 [1, 4] (1)
    sc234 sc235 (sc234_sound a c hc) (sc235_sound a c hc)

def sc624 : RawPoly ℕ :=
  [(mkRat (-1) 180, [0, 1, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (-2) 45, [0, 1, 1, 1, 1, 1, 3]),
   (mkRat (2) 15, [0, 1, 1, 1, 5]),
   (mkRat (-1) 4, [0, 1, 1, 2, 4]),
   (mkRat (1) 9, [0, 1, 1, 3, 3]),
   (mkRat (-1) 48, [0, 2, 2, 2, 2]),
   (mkRat (-1) 3, [0, 2, 6]),
   (mkRat (-4) 15, [0, 3, 5]),
   (mkRat (3) 8, [0, 4, 4]),
   (mkRat (-1) 18, [1, 1, 1, 1, 1, 1, 2]),
   (mkRat (2) 9, [1, 1, 1, 2, 3]),
   (mkRat (1) 12, [1, 1, 2, 2, 2]),
   (mkRat (1) 3, [1, 1, 6]),
   (mkRat (1) 4, [2, 2, 4]),
   (mkRat (-2) 9, [2, 3, 3]),
   (mkRat (-1) 2, [8])]

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc624_check :
    reduceTwo (prependC 1 sc235 ++ scaleR (-1) (prependC 0 sc236)) = sc624 := by
  decide +kernel

theorem sc624_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc624 = evRc a c (expWordR [1, 1, 4] (2)) := by
  rw [← sc624_check]
  exact expTwo_step _ _ hc 0 [1, 4] (2)
    sc235 sc236 (sc235_sound a c hc) (sc236_sound a c hc)

def sc625 : RawPoly ℕ :=
  [(mkRat (-1) 70, [0, 1, 1, 1, 1, 1, 1, 1, 2]),
   (mkRat (1) 30, [0, 1, 1, 1, 1, 1, 4]),
   (mkRat (1) 36, [0, 1, 1, 1, 2, 2, 2]),
   (mkRat (1) 9, [0, 1, 1, 1, 6]),
   (mkRat (1) 5, [0, 1, 1, 2, 5]),
   (mkRat (-1) 6, [0, 1, 1, 3, 4]),
   (mkRat (-1) 18, [0, 2, 2, 2, 3]),
   (mkRat (-2) 7, [0, 2, 7]),
   (mkRat (-2) 9, [0, 3, 6]),
   (mkRat (1) 5, [0, 4, 5]),
   (mkRat (-1) 567, [1, 1, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (-1) 27, [1, 1, 1, 1, 1, 1, 3]),
   (mkRat (-1) 30, [1, 1, 1, 1, 1, 2, 2]),
   (mkRat (-1) 6, [1, 1, 1, 2, 4]),
   (mkRat (2) 27, [1, 1, 1, 3, 3]),
   (mkRat (1) 6, [1, 1, 2, 2, 3]),
   (mkRat (2) 7, [1, 1, 7]),
   (mkRat (-1) 5, [2, 2, 5]),
   (mkRat (1) 3, [2, 3, 4]),
   (mkRat (-4) 81, [3, 3, 3]),
   (mkRat (-4) 9, [9])]

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc625_check :
    reduceTwo (prependC 1 sc236 ++ scaleR (-1) (prependC 0 sc237)) = sc625 := by
  decide +kernel

theorem sc625_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc625 = evRc a c (expWordR [1, 1, 4] (3)) := by
  rw [← sc625_check]
  exact expTwo_step _ _ hc 0 [1, 4] (3)
    sc236 sc237 (sc236_sound a c hc) (sc237_sound a c hc)

def sc626Part0 : RawPoly ℕ :=
  [(mkRat (-1) 4200, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (-1) 105, [0, 1, 1, 1, 1, 1, 1, 1, 3]),
   (mkRat (-1) 72, [0, 1, 1, 1, 1, 1, 1, 2, 2]),
   (mkRat (-2) 75, [0, 1, 1, 1, 1, 1, 5]),
   (mkRat (1) 18, [0, 1, 1, 1, 2, 2, 3]),
   (mkRat (2) 21, [0, 1, 1, 1, 7]),
   (mkRat (1) 96, [0, 1, 1, 2, 2, 2, 2]),
   (mkRat (1) 6, [0, 1, 1, 2, 6]),
   (mkRat (2) 15, [0, 1, 1, 3, 5]),
   (mkRat (-3) 16, [0, 1, 1, 4, 4]),
   (mkRat (1) 24, [0, 2, 2, 2, 4]),
   (mkRat (-1) 18, [0, 2, 2, 3, 3]),
   (mkRat (-1) 4, [0, 2, 8]),
   (mkRat (-4) 21, [0, 3, 7]),
   (mkRat (1) 6, [0, 4, 6]),
   (mkRat (-2) 25, [0, 5, 5]),
   (mkRat (-1) 180, [1, 1, 1, 1, 1, 1, 1, 1, 2]),
   (mkRat (1) 36, [1, 1, 1, 1, 1, 1, 4]),
   (mkRat (-2) 45, [1, 1, 1, 1, 1, 2, 3]),
   (mkRat (2) 15, [1, 1, 1, 2, 5]),
   (mkRat (-1) 9, [1, 1, 1, 3, 4]),
   (mkRat (-1) 8, [1, 1, 2, 2, 4]),
   (mkRat (1) 9, [1, 1, 2, 3, 3]),
   (mkRat (1) 4, [1, 1, 8])]

def sc626Part1 : RawPoly ℕ :=
  [(mkRat (-1) 240, [2, 2, 2, 2, 2]),
   (mkRat (-1) 6, [2, 2, 6]),
   (mkRat (-4) 15, [2, 3, 5]),
   (mkRat (3) 8, [2, 4, 4]),
   (mkRat (1) 9, [3, 3, 4]),
   (mkRat (-2) 5, [10])]

def sc626 : RawPoly ℕ :=
  [sc626Part0,
   sc626Part1].flatten

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc626_check :
    reduceTwo (prependC 1 sc237 ++ scaleR (-1) (prependC 0 sc238)) = sc626 := by
  decide +kernel

theorem sc626_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc626 = evRc a c (expWordR [1, 1, 4] (4)) := by
  rw [← sc626_check]
  exact expTwo_step _ _ hc 0 [1, 4] (4)
    sc237 sc238 (sc237_sound a c hc) (sc238_sound a c hc)

def sc627Part0 : RawPoly ℕ :=
  [(mkRat (-1) 1134, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2]),
   (mkRat (1) 140, [0, 1, 1, 1, 1, 1, 1, 1, 4]),
   (mkRat (-1) 54, [0, 1, 1, 1, 1, 1, 1, 2, 3]),
   (mkRat (-1) 180, [0, 1, 1, 1, 1, 1, 2, 2, 2]),
   (mkRat (-1) 45, [0, 1, 1, 1, 1, 1, 6]),
   (mkRat (-1) 24, [0, 1, 1, 1, 2, 2, 4]),
   (mkRat (1) 27, [0, 1, 1, 1, 2, 3, 3]),
   (mkRat (1) 12, [0, 1, 1, 1, 8]),
   (mkRat (1) 36, [0, 1, 1, 2, 2, 2, 3]),
   (mkRat (1) 7, [0, 1, 1, 2, 7]),
   (mkRat (1) 9, [0, 1, 1, 3, 6]),
   (mkRat (-1) 10, [0, 1, 1, 4, 5]),
   (mkRat (-1) 30, [0, 2, 2, 2, 5]),
   (mkRat (1) 12, [0, 2, 2, 3, 4]),
   (mkRat (-2) 81, [0, 2, 3, 3, 3]),
   (mkRat (-2) 9, [0, 2, 9]),
   (mkRat (-1) 6, [0, 3, 8]),
   (mkRat (1) 7, [0, 4, 7]),
   (mkRat (-2) 15, [0, 5, 6]),
   (mkRat (-1) 17820, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (-1) 270, [1, 1, 1, 1, 1, 1, 1, 1, 3]),
   (mkRat (-1) 140, [1, 1, 1, 1, 1, 1, 1, 2, 2]),
   (mkRat (-1) 45, [1, 1, 1, 1, 1, 1, 5]),
   (mkRat (1) 30, [1, 1, 1, 1, 1, 2, 4])]

def sc627Part1 : RawPoly ℕ :=
  [(mkRat (-2) 135, [1, 1, 1, 1, 1, 3, 3]),
   (mkRat (1) 144, [1, 1, 1, 2, 2, 2, 2]),
   (mkRat (1) 9, [1, 1, 1, 2, 6]),
   (mkRat (4) 45, [1, 1, 1, 3, 5]),
   (mkRat (-1) 8, [1, 1, 1, 4, 4]),
   (mkRat (1) 10, [1, 1, 2, 2, 5]),
   (mkRat (-1) 6, [1, 1, 2, 3, 4]),
   (mkRat (2) 81, [1, 1, 3, 3, 3]),
   (mkRat (2) 9, [1, 1, 9]),
   (mkRat (-1) 72, [2, 2, 2, 2, 3]),
   (mkRat (-1) 7, [2, 2, 7]),
   (mkRat (-2) 9, [2, 3, 6]),
   (mkRat (1) 5, [2, 4, 5]),
   (mkRat (-4) 45, [3, 3, 5]),
   (mkRat (1) 4, [3, 4, 4]),
   (mkRat (-4) 11, [11])]

def sc627 : RawPoly ℕ :=
  [sc627Part0,
   sc627Part1].flatten

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc627_check :
    reduceTwo (prependC 1 sc238 ++ scaleR (-1) (prependC 0 sc239)) = sc627 := by
  decide +kernel

theorem sc627_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc627 = evRc a c (expWordR [1, 1, 4] (5)) := by
  rw [← sc627_check]
  exact expTwo_step _ _ hc 0 [1, 4] (5)
    sc238 sc239 (sc238_sound a c hc) (sc239_sound a c hc)

def sc628Part0 : RawPoly ℕ :=
  [(mkRat (-1) 170100, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (-1) 1701, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3]),
   (mkRat (-1) 720, [0, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2]),
   (mkRat (-1) 175, [0, 1, 1, 1, 1, 1, 1, 1, 5]),
   (mkRat (1) 72, [0, 1, 1, 1, 1, 1, 1, 2, 4]),
   (mkRat (-1) 162, [0, 1, 1, 1, 1, 1, 1, 3, 3]),
   (mkRat (-1) 90, [0, 1, 1, 1, 1, 1, 2, 2, 3]),
   (mkRat (-2) 105, [0, 1, 1, 1, 1, 1, 7]),
   (mkRat (1) 30, [0, 1, 1, 1, 2, 2, 5]),
   (mkRat (-1) 18, [0, 1, 1, 1, 2, 3, 4]),
   (mkRat (2) 243, [0, 1, 1, 1, 3, 3, 3]),
   (mkRat (2) 27, [0, 1, 1, 1, 9]),
   (mkRat (-1) 48, [0, 1, 1, 2, 2, 2, 4]),
   (mkRat (1) 36, [0, 1, 1, 2, 2, 3, 3]),
   (mkRat (1) 8, [0, 1, 1, 2, 8]),
   (mkRat (2) 21, [0, 1, 1, 3, 7]),
   (mkRat (-1) 12, [0, 1, 1, 4, 6]),
   (mkRat (1) 25, [0, 1, 1, 5, 5]),
   (mkRat (-1) 2880, [0, 2, 2, 2, 2, 2, 2]),
   (mkRat (-1) 36, [0, 2, 2, 2, 6]),
   (mkRat (-1) 15, [0, 2, 2, 3, 5]),
   (mkRat (3) 32, [0, 2, 2, 4, 4]),
   (mkRat (1) 18, [0, 2, 3, 3, 4]),
   (mkRat (-1) 5, [0, 2, 10])]

def sc628Part1 : RawPoly ℕ :=
  [(mkRat (-1) 243, [0, 3, 3, 3, 3]),
   (mkRat (-4) 27, [0, 3, 9]),
   (mkRat (1) 8, [0, 4, 8]),
   (mkRat (-4) 35, [0, 5, 7]),
   (mkRat (-1) 18, [0, 6, 6]),
   (mkRat (-1) 4200, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2]),
   (mkRat (1) 360, [1, 1, 1, 1, 1, 1, 1, 1, 4]),
   (mkRat (-1) 105, [1, 1, 1, 1, 1, 1, 1, 2, 3]),
   (mkRat (-1) 216, [1, 1, 1, 1, 1, 1, 2, 2, 2]),
   (mkRat (-1) 54, [1, 1, 1, 1, 1, 1, 6]),
   (mkRat (-2) 75, [1, 1, 1, 1, 1, 2, 5]),
   (mkRat (1) 45, [1, 1, 1, 1, 1, 3, 4]),
   (mkRat (1) 54, [1, 1, 1, 2, 2, 2, 3]),
   (mkRat (2) 21, [1, 1, 1, 2, 7]),
   (mkRat (2) 27, [1, 1, 1, 3, 6]),
   (mkRat (-1) 15, [1, 1, 1, 4, 5]),
   (mkRat (1) 480, [1, 1, 2, 2, 2, 2, 2]),
   (mkRat (1) 12, [1, 1, 2, 2, 6]),
   (mkRat (2) 15, [1, 1, 2, 3, 5]),
   (mkRat (-3) 16, [1, 1, 2, 4, 4]),
   (mkRat (-1) 18, [1, 1, 3, 3, 4]),
   (mkRat (1) 5, [1, 1, 10]),
   (mkRat (1) 96, [2, 2, 2, 2, 4]),
   (mkRat (-1) 54, [2, 2, 2, 3, 3])]

def sc628Part2 : RawPoly ℕ :=
  [(mkRat (-1) 8, [2, 2, 8]),
   (mkRat (-4) 21, [2, 3, 7]),
   (mkRat (1) 6, [2, 4, 6]),
   (mkRat (-2) 25, [2, 5, 5]),
   (mkRat (-2) 27, [3, 3, 6]),
   (mkRat (2) 15, [3, 4, 5]),
   (mkRat (5) 48, [4, 4, 4]),
   (mkRat (-1) 3, [12])]

def sc628 : RawPoly ℕ :=
  [sc628Part0,
   sc628Part1,
   sc628Part2].flatten

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc628_check :
    reduceTwo (prependC 1 sc239 ++ scaleR (-1) (prependC 0 sc240)) = sc628 := by
  decide +kernel

theorem sc628_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc628 = evRc a c (expWordR [1, 1, 4] (6)) := by
  rw [← sc628_check]
  exact expTwo_step _ _ hc 0 [1, 4] (6)
    sc239 sc240 (sc239_sound a c hc) (sc240_sound a c hc)

def sc629Part0 : RawPoly ℕ :=
  [(mkRat (-1) 35640, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2]),
   (mkRat (1) 2268, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4]),
   (mkRat (-1) 540, [0, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3]),
   (mkRat (-1) 840, [0, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2]),
   (mkRat (-1) 210, [0, 1, 1, 1, 1, 1, 1, 1, 6]),
   (mkRat (-1) 90, [0, 1, 1, 1, 1, 1, 1, 2, 5]),
   (mkRat (1) 108, [0, 1, 1, 1, 1, 1, 1, 3, 4]),
   (mkRat (1) 120, [0, 1, 1, 1, 1, 1, 2, 2, 4]),
   (mkRat (-1) 135, [0, 1, 1, 1, 1, 1, 2, 3, 3]),
   (mkRat (-1) 60, [0, 1, 1, 1, 1, 1, 8]),
   (mkRat (1) 1440, [0, 1, 1, 1, 2, 2, 2, 2, 2]),
   (mkRat (1) 36, [0, 1, 1, 1, 2, 2, 6]),
   (mkRat (2) 45, [0, 1, 1, 1, 2, 3, 5]),
   (mkRat (-1) 16, [0, 1, 1, 1, 2, 4, 4]),
   (mkRat (-1) 54, [0, 1, 1, 1, 3, 3, 4]),
   (mkRat (1) 15, [0, 1, 1, 1, 10]),
   (mkRat (1) 60, [0, 1, 1, 2, 2, 2, 5]),
   (mkRat (-1) 24, [0, 1, 1, 2, 2, 3, 4]),
   (mkRat (1) 81, [0, 1, 1, 2, 3, 3, 3]),
   (mkRat (1) 9, [0, 1, 1, 2, 9]),
   (mkRat (1) 12, [0, 1, 1, 3, 8]),
   (mkRat (-1) 14, [0, 1, 1, 4, 7]),
   (mkRat (1) 15, [0, 1, 1, 5, 6]),
   (mkRat (-1) 720, [0, 2, 2, 2, 2, 2, 3])]

def sc629Part1 : RawPoly ℕ :=
  [(mkRat (-1) 42, [0, 2, 2, 2, 7]),
   (mkRat (-1) 18, [0, 2, 2, 3, 6]),
   (mkRat (1) 20, [0, 2, 2, 4, 5]),
   (mkRat (-2) 45, [0, 2, 3, 3, 5]),
   (mkRat (1) 8, [0, 2, 3, 4, 4]),
   (mkRat (-2) 11, [0, 2, 11]),
   (mkRat (1) 81, [0, 3, 3, 3, 4]),
   (mkRat (-2) 15, [0, 3, 10]),
   (mkRat (1) 9, [0, 4, 9]),
   (mkRat (-1) 10, [0, 5, 8]),
   (mkRat (-2) 21, [0, 6, 7]),
   (mkRat (-1) 900900, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (-1) 6300, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3]),
   (mkRat (-1) 2268, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2]),
   (mkRat (-1) 450, [1, 1, 1, 1, 1, 1, 1, 1, 5]),
   (mkRat (1) 140, [1, 1, 1, 1, 1, 1, 1, 2, 4]),
   (mkRat (-1) 315, [1, 1, 1, 1, 1, 1, 1, 3, 3]),
   (mkRat (-1) 108, [1, 1, 1, 1, 1, 1, 2, 2, 3]),
   (mkRat (-1) 63, [1, 1, 1, 1, 1, 1, 7]),
   (mkRat (-1) 720, [1, 1, 1, 1, 1, 2, 2, 2, 2]),
   (mkRat (-1) 45, [1, 1, 1, 1, 1, 2, 6]),
   (mkRat (-4) 225, [1, 1, 1, 1, 1, 3, 5]),
   (mkRat (1) 40, [1, 1, 1, 1, 1, 4, 4]),
   (mkRat (-1) 72, [1, 1, 1, 2, 2, 2, 4])]

def sc629Part2 : RawPoly ℕ :=
  [(mkRat (1) 54, [1, 1, 1, 2, 2, 3, 3]),
   (mkRat (1) 12, [1, 1, 1, 2, 8]),
   (mkRat (4) 63, [1, 1, 1, 3, 7]),
   (mkRat (-1) 18, [1, 1, 1, 4, 6]),
   (mkRat (2) 75, [1, 1, 1, 5, 5]),
   (mkRat (1) 144, [1, 1, 2, 2, 2, 2, 3]),
   (mkRat (1) 14, [1, 1, 2, 2, 7]),
   (mkRat (1) 9, [1, 1, 2, 3, 6]),
   (mkRat (-1) 10, [1, 1, 2, 4, 5]),
   (mkRat (2) 45, [1, 1, 3, 3, 5]),
   (mkRat (-1) 8, [1, 1, 3, 4, 4]),
   (mkRat (2) 11, [1, 1, 11]),
   (mkRat (-1) 120, [2, 2, 2, 2, 5]),
   (mkRat (1) 36, [2, 2, 2, 3, 4]),
   (mkRat (-1) 81, [2, 2, 3, 3, 3]),
   (mkRat (-1) 9, [2, 2, 9]),
   (mkRat (-1) 6, [2, 3, 8]),
   (mkRat (1) 7, [2, 4, 7]),
   (mkRat (-2) 15, [2, 5, 6]),
   (mkRat (-4) 63, [3, 3, 7]),
   (mkRat (1) 9, [3, 4, 6]),
   (mkRat (-4) 75, [3, 5, 5]),
   (mkRat (3) 20, [4, 4, 5]),
   (mkRat (-4) 13, [13])]

def sc629 : RawPoly ℕ :=
  [sc629Part0,
   sc629Part1,
   sc629Part2].flatten

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc629_check :
    reduceTwo (prependC 1 sc240 ++ scaleR (-1) (prependC 0 sc241)) = sc629 := by
  decide +kernel

theorem sc629_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc629 = evRc a c (expWordR [1, 1, 4] (7)) := by
  rw [← sc629_check]
  exact expTwo_step _ _ hc 0 [1, 4] (7)
    sc240 sc241 (sc240_sound a c hc) (sc241_sound a c hc)

def sc630Part0 : RawPoly ℕ :=
  [(mkRat (-1) 10478160, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (-1) 53460, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3]),
   (mkRat (-1) 16800, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2]),
   (mkRat (-1) 2835, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5]),
   (mkRat (1) 720, [0, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4]),
   (mkRat (-1) 1620, [0, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3]),
   (mkRat (-1) 420, [0, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3]),
   (mkRat (-1) 245, [0, 1, 1, 1, 1, 1, 1, 1, 7]),
   (mkRat (-1) 1728, [0, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2]),
   (mkRat (-1) 108, [0, 1, 1, 1, 1, 1, 1, 2, 6]),
   (mkRat (-1) 135, [0, 1, 1, 1, 1, 1, 1, 3, 5]),
   (mkRat (1) 96, [0, 1, 1, 1, 1, 1, 1, 4, 4]),
   (mkRat (-1) 150, [0, 1, 1, 1, 1, 1, 2, 2, 5]),
   (mkRat (1) 90, [0, 1, 1, 1, 1, 1, 2, 3, 4]),
   (mkRat (-2) 1215, [0, 1, 1, 1, 1, 1, 3, 3, 3]),
   (mkRat (-2) 135, [0, 1, 1, 1, 1, 1, 9]),
   (mkRat (1) 432, [0, 1, 1, 1, 2, 2, 2, 2, 3]),
   (mkRat (1) 42, [0, 1, 1, 1, 2, 2, 7]),
   (mkRat (1) 27, [0, 1, 1, 1, 2, 3, 6]),
   (mkRat (-1) 30, [0, 1, 1, 1, 2, 4, 5]),
   (mkRat (2) 135, [0, 1, 1, 1, 3, 3, 5]),
   (mkRat (-1) 24, [0, 1, 1, 1, 3, 4, 4]),
   (mkRat (2) 33, [0, 1, 1, 1, 11]),
   (mkRat (1) 5760, [0, 1, 1, 2, 2, 2, 2, 2, 2])]

def sc630Part1 : RawPoly ℕ :=
  [(mkRat (1) 72, [0, 1, 1, 2, 2, 2, 6]),
   (mkRat (1) 30, [0, 1, 1, 2, 2, 3, 5]),
   (mkRat (-3) 64, [0, 1, 1, 2, 2, 4, 4]),
   (mkRat (-1) 36, [0, 1, 1, 2, 3, 3, 4]),
   (mkRat (1) 10, [0, 1, 1, 2, 10]),
   (mkRat (1) 486, [0, 1, 1, 3, 3, 3, 3]),
   (mkRat (2) 27, [0, 1, 1, 3, 9]),
   (mkRat (-1) 16, [0, 1, 1, 4, 8]),
   (mkRat (2) 35, [0, 1, 1, 5, 7]),
   (mkRat (1) 36, [0, 1, 1, 6, 6]),
   (mkRat (1) 960, [0, 2, 2, 2, 2, 2, 4]),
   (mkRat (-1) 432, [0, 2, 2, 2, 2, 3, 3]),
   (mkRat (-1) 48, [0, 2, 2, 2, 8]),
   (mkRat (-1) 21, [0, 2, 2, 3, 7]),
   (mkRat (1) 24, [0, 2, 2, 4, 6]),
   (mkRat (-1) 50, [0, 2, 2, 5, 5]),
   (mkRat (-1) 27, [0, 2, 3, 3, 6]),
   (mkRat (1) 15, [0, 2, 3, 4, 5]),
   (mkRat (5) 96, [0, 2, 4, 4, 4]),
   (mkRat (-1) 6, [0, 2, 12]),
   (mkRat (-4) 405, [0, 3, 3, 3, 5]),
   (mkRat (1) 24, [0, 3, 3, 4, 4]),
   (mkRat (-4) 33, [0, 3, 11]),
   (mkRat (1) 10, [0, 4, 10])]

def sc630Part2 : RawPoly ℕ :=
  [(mkRat (-4) 45, [0, 5, 9]),
   (mkRat (-1) 12, [0, 6, 8]),
   (mkRat (-2) 49, [0, 7, 7]),
   (mkRat (-1) 170100, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2]),
   (mkRat (1) 8400, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4]),
   (mkRat (-1) 1701, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3]),
   (mkRat (-1) 2160, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2]),
   (mkRat (-1) 540, [1, 1, 1, 1, 1, 1, 1, 1, 6]),
   (mkRat (-1) 175, [1, 1, 1, 1, 1, 1, 1, 2, 5]),
   (mkRat (1) 210, [1, 1, 1, 1, 1, 1, 1, 3, 4]),
   (mkRat (1) 144, [1, 1, 1, 1, 1, 1, 2, 2, 4]),
   (mkRat (-1) 162, [1, 1, 1, 1, 1, 1, 2, 3, 3]),
   (mkRat (-1) 72, [1, 1, 1, 1, 1, 1, 8]),
   (mkRat (-1) 270, [1, 1, 1, 1, 1, 2, 2, 2, 3]),
   (mkRat (-2) 105, [1, 1, 1, 1, 1, 2, 7]),
   (mkRat (-2) 135, [1, 1, 1, 1, 1, 3, 6]),
   (mkRat (1) 75, [1, 1, 1, 1, 1, 4, 5]),
   (mkRat (1) 90, [1, 1, 1, 2, 2, 2, 5]),
   (mkRat (-1) 36, [1, 1, 1, 2, 2, 3, 4]),
   (mkRat (2) 243, [1, 1, 1, 2, 3, 3, 3]),
   (mkRat (2) 27, [1, 1, 1, 2, 9]),
   (mkRat (1) 18, [1, 1, 1, 3, 8]),
   (mkRat (-1) 21, [1, 1, 1, 4, 7]),
   (mkRat (2) 45, [1, 1, 1, 5, 6])]

def sc630Part3 : RawPoly ℕ :=
  [(mkRat (-1) 192, [1, 1, 2, 2, 2, 2, 4]),
   (mkRat (1) 108, [1, 1, 2, 2, 2, 3, 3]),
   (mkRat (1) 16, [1, 1, 2, 2, 8]),
   (mkRat (2) 21, [1, 1, 2, 3, 7]),
   (mkRat (-1) 12, [1, 1, 2, 4, 6]),
   (mkRat (1) 25, [1, 1, 2, 5, 5]),
   (mkRat (1) 27, [1, 1, 3, 3, 6]),
   (mkRat (-1) 15, [1, 1, 3, 4, 5]),
   (mkRat (-5) 96, [1, 1, 4, 4, 4]),
   (mkRat (1) 6, [1, 1, 12]),
   (mkRat (-1) 20160, [2, 2, 2, 2, 2, 2, 2]),
   (mkRat (-1) 144, [2, 2, 2, 2, 6]),
   (mkRat (-1) 45, [2, 2, 2, 3, 5]),
   (mkRat (1) 32, [2, 2, 2, 4, 4]),
   (mkRat (1) 36, [2, 2, 3, 3, 4]),
   (mkRat (-1) 10, [2, 2, 10]),
   (mkRat (-1) 243, [2, 3, 3, 3, 3]),
   (mkRat (-4) 27, [2, 3, 9]),
   (mkRat (1) 8, [2, 4, 8]),
   (mkRat (-4) 35, [2, 5, 7]),
   (mkRat (-1) 18, [2, 6, 6]),
   (mkRat (-1) 18, [3, 3, 8]),
   (mkRat (2) 21, [3, 4, 7]),
   (mkRat (-4) 45, [3, 5, 6])]

def sc630Part4 : RawPoly ℕ :=
  [(mkRat (1) 8, [4, 4, 6]),
   (mkRat (1) 25, [4, 5, 5]),
   (mkRat (-2) 7, [14])]

def sc630 : RawPoly ℕ :=
  [sc630Part0,
   sc630Part1,
   sc630Part2,
   sc630Part3,
   sc630Part4].flatten

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc630_check :
    reduceTwo (prependC 1 sc241 ++ scaleR (-1) (prependC 0 sc242)) = sc630 := by
  decide +kernel

theorem sc630_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc630 = evRc a c (expWordR [1, 1, 4] (8)) := by
  rw [← sc630_check]
  exact expTwo_step _ _ hc 0 [1, 4] (8)
    sc241 sc242 (sc241_sound a c hc) (sc242_sound a c hc)

def sc631Part0 : RawPoly ℕ :=
  [(mkRat (-1) 1801800, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2]),
   (mkRat (1) 71280, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4]),
   (mkRat (-1) 12600, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3]),
   (mkRat (-1) 13608, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2]),
   (mkRat (-1) 3402, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6]),
   (mkRat (-1) 900, [0, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5]),
   (mkRat (1) 1080, [0, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4]),
   (mkRat (1) 560, [0, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4]),
   (mkRat (-1) 630, [0, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3]),
   (mkRat (-1) 280, [0, 1, 1, 1, 1, 1, 1, 1, 8]),
   (mkRat (-1) 648, [0, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3]),
   (mkRat (-1) 126, [0, 1, 1, 1, 1, 1, 1, 2, 7]),
   (mkRat (-1) 162, [0, 1, 1, 1, 1, 1, 1, 3, 6]),
   (mkRat (1) 180, [0, 1, 1, 1, 1, 1, 1, 4, 5]),
   (mkRat (-1) 7200, [0, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2]),
   (mkRat (-1) 180, [0, 1, 1, 1, 1, 1, 2, 2, 6]),
   (mkRat (-2) 225, [0, 1, 1, 1, 1, 1, 2, 3, 5]),
   (mkRat (1) 80, [0, 1, 1, 1, 1, 1, 2, 4, 4]),
   (mkRat (1) 270, [0, 1, 1, 1, 1, 1, 3, 3, 4]),
   (mkRat (-1) 75, [0, 1, 1, 1, 1, 1, 10]),
   (mkRat (-1) 576, [0, 1, 1, 1, 2, 2, 2, 2, 4]),
   (mkRat (1) 324, [0, 1, 1, 1, 2, 2, 2, 3, 3]),
   (mkRat (1) 48, [0, 1, 1, 1, 2, 2, 8]),
   (mkRat (2) 63, [0, 1, 1, 1, 2, 3, 7])]

def sc631Part1 : RawPoly ℕ :=
  [(mkRat (-1) 36, [0, 1, 1, 1, 2, 4, 6]),
   (mkRat (1) 75, [0, 1, 1, 1, 2, 5, 5]),
   (mkRat (1) 81, [0, 1, 1, 1, 3, 3, 6]),
   (mkRat (-1) 45, [0, 1, 1, 1, 3, 4, 5]),
   (mkRat (-5) 288, [0, 1, 1, 1, 4, 4, 4]),
   (mkRat (1) 18, [0, 1, 1, 1, 12]),
   (mkRat (1) 1440, [0, 1, 1, 2, 2, 2, 2, 2, 3]),
   (mkRat (1) 84, [0, 1, 1, 2, 2, 2, 7]),
   (mkRat (1) 36, [0, 1, 1, 2, 2, 3, 6]),
   (mkRat (-1) 40, [0, 1, 1, 2, 2, 4, 5]),
   (mkRat (1) 45, [0, 1, 1, 2, 3, 3, 5]),
   (mkRat (-1) 16, [0, 1, 1, 2, 3, 4, 4]),
   (mkRat (1) 11, [0, 1, 1, 2, 11]),
   (mkRat (-1) 162, [0, 1, 1, 3, 3, 3, 4]),
   (mkRat (1) 15, [0, 1, 1, 3, 10]),
   (mkRat (-1) 18, [0, 1, 1, 4, 9]),
   (mkRat (1) 20, [0, 1, 1, 5, 8]),
   (mkRat (1) 21, [0, 1, 1, 6, 7]),
   (mkRat (-1) 1200, [0, 2, 2, 2, 2, 2, 5]),
   (mkRat (1) 288, [0, 2, 2, 2, 2, 3, 4]),
   (mkRat (-1) 486, [0, 2, 2, 2, 3, 3, 3]),
   (mkRat (-1) 54, [0, 2, 2, 2, 9]),
   (mkRat (-1) 24, [0, 2, 2, 3, 8]),
   (mkRat (1) 28, [0, 2, 2, 4, 7])]

def sc631Part2 : RawPoly ℕ :=
  [(mkRat (-1) 30, [0, 2, 2, 5, 6]),
   (mkRat (-2) 63, [0, 2, 3, 3, 7]),
   (mkRat (1) 18, [0, 2, 3, 4, 6]),
   (mkRat (-2) 75, [0, 2, 3, 5, 5]),
   (mkRat (3) 40, [0, 2, 4, 4, 5]),
   (mkRat (-2) 13, [0, 2, 13]),
   (mkRat (-2) 243, [0, 3, 3, 3, 6]),
   (mkRat (1) 45, [0, 3, 3, 4, 5]),
   (mkRat (5) 144, [0, 3, 4, 4, 4]),
   (mkRat (-1) 9, [0, 3, 12]),
   (mkRat (1) 11, [0, 4, 11]),
   (mkRat (-2) 25, [0, 5, 10]),
   (mkRat (-2) 27, [0, 6, 9]),
   (mkRat (-1) 14, [0, 7, 8]),
   (mkRat (-1) 66339000, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (-1) 255150, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3]),
   (mkRat (-1) 71280, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2]),
   (mkRat (-1) 10500, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5]),
   (mkRat (1) 2268, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4]),
   (mkRat (-1) 5103, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3]),
   (mkRat (-1) 1080, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3]),
   (mkRat (-1) 630, [1, 1, 1, 1, 1, 1, 1, 1, 7]),
   (mkRat (-1) 3360, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2]),
   (mkRat (-1) 210, [1, 1, 1, 1, 1, 1, 1, 2, 6])]

def sc631Part3 : RawPoly ℕ :=
  [(mkRat (-2) 525, [1, 1, 1, 1, 1, 1, 1, 3, 5]),
   (mkRat (3) 560, [1, 1, 1, 1, 1, 1, 1, 4, 4]),
   (mkRat (-1) 180, [1, 1, 1, 1, 1, 1, 2, 2, 5]),
   (mkRat (1) 108, [1, 1, 1, 1, 1, 1, 2, 3, 4]),
   (mkRat (-1) 729, [1, 1, 1, 1, 1, 1, 3, 3, 3]),
   (mkRat (-1) 81, [1, 1, 1, 1, 1, 1, 9]),
   (mkRat (1) 360, [1, 1, 1, 1, 1, 2, 2, 2, 4]),
   (mkRat (-1) 270, [1, 1, 1, 1, 1, 2, 2, 3, 3]),
   (mkRat (-1) 60, [1, 1, 1, 1, 1, 2, 8]),
   (mkRat (-4) 315, [1, 1, 1, 1, 1, 3, 7]),
   (mkRat (1) 90, [1, 1, 1, 1, 1, 4, 6]),
   (mkRat (-2) 375, [1, 1, 1, 1, 1, 5, 5]),
   (mkRat (1) 8640, [1, 1, 1, 2, 2, 2, 2, 2, 2]),
   (mkRat (1) 108, [1, 1, 1, 2, 2, 2, 6]),
   (mkRat (1) 45, [1, 1, 1, 2, 2, 3, 5]),
   (mkRat (-1) 32, [1, 1, 1, 2, 2, 4, 4]),
   (mkRat (-1) 54, [1, 1, 1, 2, 3, 3, 4]),
   (mkRat (1) 15, [1, 1, 1, 2, 10]),
   (mkRat (1) 729, [1, 1, 1, 3, 3, 3, 3]),
   (mkRat (4) 81, [1, 1, 1, 3, 9]),
   (mkRat (-1) 24, [1, 1, 1, 4, 8]),
   (mkRat (4) 105, [1, 1, 1, 5, 7]),
   (mkRat (1) 54, [1, 1, 1, 6, 6]),
   (mkRat (1) 240, [1, 1, 2, 2, 2, 2, 5])]

def sc631Part4 : RawPoly ℕ :=
  [(mkRat (-1) 72, [1, 1, 2, 2, 2, 3, 4]),
   (mkRat (1) 162, [1, 1, 2, 2, 3, 3, 3]),
   (mkRat (1) 18, [1, 1, 2, 2, 9]),
   (mkRat (1) 12, [1, 1, 2, 3, 8]),
   (mkRat (-1) 14, [1, 1, 2, 4, 7]),
   (mkRat (1) 15, [1, 1, 2, 5, 6]),
   (mkRat (2) 63, [1, 1, 3, 3, 7]),
   (mkRat (-1) 18, [1, 1, 3, 4, 6]),
   (mkRat (2) 75, [1, 1, 3, 5, 5]),
   (mkRat (-3) 40, [1, 1, 4, 4, 5]),
   (mkRat (2) 13, [1, 1, 13]),
   (mkRat (-1) 4320, [2, 2, 2, 2, 2, 2, 3]),
   (mkRat (-1) 168, [2, 2, 2, 2, 7]),
   (mkRat (-1) 54, [2, 2, 2, 3, 6]),
   (mkRat (1) 60, [2, 2, 2, 4, 5]),
   (mkRat (-1) 45, [2, 2, 3, 3, 5]),
   (mkRat (1) 16, [2, 2, 3, 4, 4]),
   (mkRat (-1) 11, [2, 2, 11]),
   (mkRat (1) 81, [2, 3, 3, 3, 4]),
   (mkRat (-2) 15, [2, 3, 10]),
   (mkRat (1) 9, [2, 4, 9]),
   (mkRat (-1) 10, [2, 5, 8]),
   (mkRat (-2) 21, [2, 6, 7]),
   (mkRat (-2) 3645, [3, 3, 3, 3, 3])]

def sc631Part5 : RawPoly ℕ :=
  [(mkRat (-4) 81, [3, 3, 9]),
   (mkRat (1) 12, [3, 4, 8]),
   (mkRat (-8) 105, [3, 5, 7]),
   (mkRat (-1) 27, [3, 6, 6]),
   (mkRat (3) 28, [4, 4, 7]),
   (mkRat (1) 15, [4, 5, 6]),
   (mkRat (-4) 375, [5, 5, 5]),
   (mkRat (-4) 15, [15])]

def sc631 : RawPoly ℕ :=
  [sc631Part0,
   sc631Part1,
   sc631Part2,
   sc631Part3,
   sc631Part4,
   sc631Part5].flatten

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc631_check :
    reduceTwo (prependC 1 sc242 ++ scaleR (-1) (prependC 0 sc243)) = sc631 := by
  decide +kernel

theorem sc631_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc631 = evRc a c (expWordR [1, 1, 4] (9)) := by
  rw [← sc631_check]
  exact expTwo_step _ _ hc 0 [1, 4] (9)
    sc242 sc243 (sc242_sound a c hc) (sc243_sound a c hc)

def sc632Part0 : RawPoly ℕ :=
  [(mkRat (-1) 908107200, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (-1) 2702700, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3]),
   (mkRat (-1) 680400, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2]),
   (mkRat (-1) 89100, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5]),
   (mkRat (1) 16800, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4]),
   (mkRat (-1) 37800, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3]),
   (mkRat (-1) 6804, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3]),
   (mkRat (-1) 3969, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7]),
   (mkRat (-1) 17280, [0, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2]),
   (mkRat (-1) 1080, [0, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6]),
   (mkRat (-1) 1350, [0, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5]),
   (mkRat (1) 960, [0, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4]),
   (mkRat (-1) 700, [0, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5]),
   (mkRat (1) 420, [0, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4]),
   (mkRat (-1) 2835, [0, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3]),
   (mkRat (-1) 315, [0, 1, 1, 1, 1, 1, 1, 1, 9]),
   (mkRat (1) 864, [0, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4]),
   (mkRat (-1) 648, [0, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3]),
   (mkRat (-1) 144, [0, 1, 1, 1, 1, 1, 1, 2, 8]),
   (mkRat (-1) 189, [0, 1, 1, 1, 1, 1, 1, 3, 7]),
   (mkRat (1) 216, [0, 1, 1, 1, 1, 1, 1, 4, 6]),
   (mkRat (-1) 450, [0, 1, 1, 1, 1, 1, 1, 5, 5]),
   (mkRat (-1) 2160, [0, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3]),
   (mkRat (-1) 210, [0, 1, 1, 1, 1, 1, 2, 2, 7])]

def sc632Part1 : RawPoly ℕ :=
  [(mkRat (-1) 135, [0, 1, 1, 1, 1, 1, 2, 3, 6]),
   (mkRat (1) 150, [0, 1, 1, 1, 1, 1, 2, 4, 5]),
   (mkRat (-2) 675, [0, 1, 1, 1, 1, 1, 3, 3, 5]),
   (mkRat (1) 120, [0, 1, 1, 1, 1, 1, 3, 4, 4]),
   (mkRat (-2) 165, [0, 1, 1, 1, 1, 1, 11]),
   (mkRat (1) 720, [0, 1, 1, 1, 2, 2, 2, 2, 5]),
   (mkRat (-1) 216, [0, 1, 1, 1, 2, 2, 2, 3, 4]),
   (mkRat (1) 486, [0, 1, 1, 1, 2, 2, 3, 3, 3]),
   (mkRat (1) 54, [0, 1, 1, 1, 2, 2, 9]),
   (mkRat (1) 36, [0, 1, 1, 1, 2, 3, 8]),
   (mkRat (-1) 42, [0, 1, 1, 1, 2, 4, 7]),
   (mkRat (1) 45, [0, 1, 1, 1, 2, 5, 6]),
   (mkRat (2) 189, [0, 1, 1, 1, 3, 3, 7]),
   (mkRat (-1) 54, [0, 1, 1, 1, 3, 4, 6]),
   (mkRat (2) 225, [0, 1, 1, 1, 3, 5, 5]),
   (mkRat (-1) 40, [0, 1, 1, 1, 4, 4, 5]),
   (mkRat (2) 39, [0, 1, 1, 1, 13]),
   (mkRat (-1) 1920, [0, 1, 1, 2, 2, 2, 2, 2, 4]),
   (mkRat (1) 864, [0, 1, 1, 2, 2, 2, 2, 3, 3]),
   (mkRat (1) 96, [0, 1, 1, 2, 2, 2, 8]),
   (mkRat (1) 42, [0, 1, 1, 2, 2, 3, 7]),
   (mkRat (-1) 48, [0, 1, 1, 2, 2, 4, 6]),
   (mkRat (1) 100, [0, 1, 1, 2, 2, 5, 5]),
   (mkRat (1) 54, [0, 1, 1, 2, 3, 3, 6])]

def sc632Part2 : RawPoly ℕ :=
  [(mkRat (-1) 30, [0, 1, 1, 2, 3, 4, 5]),
   (mkRat (-5) 192, [0, 1, 1, 2, 4, 4, 4]),
   (mkRat (1) 12, [0, 1, 1, 2, 12]),
   (mkRat (2) 405, [0, 1, 1, 3, 3, 3, 5]),
   (mkRat (-1) 48, [0, 1, 1, 3, 3, 4, 4]),
   (mkRat (2) 33, [0, 1, 1, 3, 11]),
   (mkRat (-1) 20, [0, 1, 1, 4, 10]),
   (mkRat (2) 45, [0, 1, 1, 5, 9]),
   (mkRat (1) 24, [0, 1, 1, 6, 8]),
   (mkRat (1) 49, [0, 1, 1, 7, 7]),
   (mkRat (-1) 322560, [0, 2, 2, 2, 2, 2, 2, 2, 2]),
   (mkRat (-1) 1440, [0, 2, 2, 2, 2, 2, 6]),
   (mkRat (-1) 360, [0, 2, 2, 2, 2, 3, 5]),
   (mkRat (1) 256, [0, 2, 2, 2, 2, 4, 4]),
   (mkRat (1) 216, [0, 2, 2, 2, 3, 3, 4]),
   (mkRat (-1) 60, [0, 2, 2, 2, 10]),
   (mkRat (-1) 972, [0, 2, 2, 3, 3, 3, 3]),
   (mkRat (-1) 27, [0, 2, 2, 3, 9]),
   (mkRat (1) 32, [0, 2, 2, 4, 8]),
   (mkRat (-1) 35, [0, 2, 2, 5, 7]),
   (mkRat (-1) 72, [0, 2, 2, 6, 6]),
   (mkRat (-1) 36, [0, 2, 3, 3, 8]),
   (mkRat (1) 21, [0, 2, 3, 4, 7]),
   (mkRat (-2) 45, [0, 2, 3, 5, 6])]

def sc632Part3 : RawPoly ℕ :=
  [(mkRat (1) 16, [0, 2, 4, 4, 6]),
   (mkRat (1) 50, [0, 2, 4, 5, 5]),
   (mkRat (-1) 7, [0, 2, 14]),
   (mkRat (-4) 567, [0, 3, 3, 3, 7]),
   (mkRat (1) 54, [0, 3, 3, 4, 6]),
   (mkRat (-2) 225, [0, 3, 3, 5, 5]),
   (mkRat (1) 20, [0, 3, 4, 4, 5]),
   (mkRat (-4) 39, [0, 3, 13]),
   (mkRat (7) 768, [0, 4, 4, 4, 4]),
   (mkRat (1) 12, [0, 4, 12]),
   (mkRat (-4) 55, [0, 5, 11]),
   (mkRat (-1) 15, [0, 6, 10]),
   (mkRat (-4) 63, [0, 7, 9]),
   (mkRat (-1) 32, [0, 8, 8]),
   (mkRat (-1) 10478160, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2]),
   (mkRat (1) 340200, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4]),
   (mkRat (-1) 53460, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3]),
   (mkRat (-1) 50400, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2]),
   (mkRat (-1) 12600, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6]),
   (mkRat (-1) 2835, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5]),
   (mkRat (1) 3402, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4]),
   (mkRat (1) 1440, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4]),
   (mkRat (-1) 1620, [1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3]),
   (mkRat (-1) 720, [1, 1, 1, 1, 1, 1, 1, 1, 8])]

def sc632Part4 : RawPoly ℕ :=
  [(mkRat (-1) 1260, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3]),
   (mkRat (-1) 245, [1, 1, 1, 1, 1, 1, 1, 2, 7]),
   (mkRat (-1) 315, [1, 1, 1, 1, 1, 1, 1, 3, 6]),
   (mkRat (1) 350, [1, 1, 1, 1, 1, 1, 1, 4, 5]),
   (mkRat (-1) 8640, [1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2]),
   (mkRat (-1) 216, [1, 1, 1, 1, 1, 1, 2, 2, 6]),
   (mkRat (-1) 135, [1, 1, 1, 1, 1, 1, 2, 3, 5]),
   (mkRat (1) 96, [1, 1, 1, 1, 1, 1, 2, 4, 4]),
   (mkRat (1) 324, [1, 1, 1, 1, 1, 1, 3, 3, 4]),
   (mkRat (-1) 90, [1, 1, 1, 1, 1, 1, 10]),
   (mkRat (-1) 450, [1, 1, 1, 1, 1, 2, 2, 2, 5]),
   (mkRat (1) 180, [1, 1, 1, 1, 1, 2, 2, 3, 4]),
   (mkRat (-2) 1215, [1, 1, 1, 1, 1, 2, 3, 3, 3]),
   (mkRat (-2) 135, [1, 1, 1, 1, 1, 2, 9]),
   (mkRat (-1) 90, [1, 1, 1, 1, 1, 3, 8]),
   (mkRat (1) 105, [1, 1, 1, 1, 1, 4, 7]),
   (mkRat (-2) 225, [1, 1, 1, 1, 1, 5, 6]),
   (mkRat (1) 2160, [1, 1, 1, 2, 2, 2, 2, 2, 3]),
   (mkRat (1) 126, [1, 1, 1, 2, 2, 2, 7]),
   (mkRat (1) 54, [1, 1, 1, 2, 2, 3, 6]),
   (mkRat (-1) 60, [1, 1, 1, 2, 2, 4, 5]),
   (mkRat (2) 135, [1, 1, 1, 2, 3, 3, 5]),
   (mkRat (-1) 24, [1, 1, 1, 2, 3, 4, 4]),
   (mkRat (2) 33, [1, 1, 1, 2, 11])]

def sc632Part5 : RawPoly ℕ :=
  [(mkRat (-1) 243, [1, 1, 1, 3, 3, 3, 4]),
   (mkRat (2) 45, [1, 1, 1, 3, 10]),
   (mkRat (-1) 27, [1, 1, 1, 4, 9]),
   (mkRat (1) 30, [1, 1, 1, 5, 8]),
   (mkRat (2) 63, [1, 1, 1, 6, 7]),
   (mkRat (1) 40320, [1, 1, 2, 2, 2, 2, 2, 2, 2]),
   (mkRat (1) 288, [1, 1, 2, 2, 2, 2, 6]),
   (mkRat (1) 90, [1, 1, 2, 2, 2, 3, 5]),
   (mkRat (-1) 64, [1, 1, 2, 2, 2, 4, 4]),
   (mkRat (-1) 72, [1, 1, 2, 2, 3, 3, 4]),
   (mkRat (1) 20, [1, 1, 2, 2, 10]),
   (mkRat (1) 486, [1, 1, 2, 3, 3, 3, 3]),
   (mkRat (2) 27, [1, 1, 2, 3, 9]),
   (mkRat (-1) 16, [1, 1, 2, 4, 8]),
   (mkRat (2) 35, [1, 1, 2, 5, 7]),
   (mkRat (1) 36, [1, 1, 2, 6, 6]),
   (mkRat (1) 36, [1, 1, 3, 3, 8]),
   (mkRat (-1) 21, [1, 1, 3, 4, 7]),
   (mkRat (2) 45, [1, 1, 3, 5, 6]),
   (mkRat (-1) 16, [1, 1, 4, 4, 6]),
   (mkRat (-1) 50, [1, 1, 4, 5, 5]),
   (mkRat (1) 7, [1, 1, 14]),
   (mkRat (1) 5760, [2, 2, 2, 2, 2, 2, 4]),
   (mkRat (-1) 2160, [2, 2, 2, 2, 2, 3, 3])]

def sc632Part6 : RawPoly ℕ :=
  [(mkRat (-1) 192, [2, 2, 2, 2, 8]),
   (mkRat (-1) 63, [2, 2, 2, 3, 7]),
   (mkRat (1) 72, [2, 2, 2, 4, 6]),
   (mkRat (-1) 150, [2, 2, 2, 5, 5]),
   (mkRat (-1) 54, [2, 2, 3, 3, 6]),
   (mkRat (1) 30, [2, 2, 3, 4, 5]),
   (mkRat (5) 192, [2, 2, 4, 4, 4]),
   (mkRat (-1) 12, [2, 2, 12]),
   (mkRat (-4) 405, [2, 3, 3, 3, 5]),
   (mkRat (1) 24, [2, 3, 3, 4, 4]),
   (mkRat (-4) 33, [2, 3, 11]),
   (mkRat (1) 10, [2, 4, 10]),
   (mkRat (-4) 45, [2, 5, 9]),
   (mkRat (-1) 12, [2, 6, 8]),
   (mkRat (-2) 49, [2, 7, 7]),
   (mkRat (1) 486, [3, 3, 3, 3, 4]),
   (mkRat (-2) 45, [3, 3, 10]),
   (mkRat (2) 27, [3, 4, 9]),
   (mkRat (-1) 15, [3, 5, 8]),
   (mkRat (-4) 63, [3, 6, 7]),
   (mkRat (3) 32, [4, 4, 8]),
   (mkRat (2) 35, [4, 5, 7]),
   (mkRat (1) 36, [4, 6, 6]),
   (mkRat (-2) 75, [5, 5, 6])]

def sc632Part7 : RawPoly ℕ :=
  [(mkRat (-1) 4, [16])]

def sc632 : RawPoly ℕ :=
  [sc632Part0,
   sc632Part1,
   sc632Part2,
   sc632Part3,
   sc632Part4,
   sc632Part5,
   sc632Part6,
   sc632Part7].flatten

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc632_check :
    reduceTwo (prependC 1 sc243 ++ scaleR (-1) (prependC 0 sc244)) = sc632 := by
  decide +kernel

theorem sc632_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc632 = evRc a c (expWordR [1, 1, 4] (10)) := by
  rw [← sc632_check]
  exact expTwo_step _ _ hc 0 [1, 4] (10)
    sc243 sc244 (sc243_sound a c hc) (sc244_sound a c hc)

def sc633 : RawPoly ℕ :=
  [(-2, [0])]

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc633_check :
    reduceTwo (prependC 1 sc245 ++ scaleR (-1) (prependC 0 sc246)) = sc633 := by
  decide +kernel

theorem sc633_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc633 = evRc a c (expWordR [1, 1, 5] (-7)) := by
  rw [← sc633_check]
  exact expTwo_step _ _ hc 0 [1, 5] (-7)
    sc245 sc246 (sc245_sound a c hc) (sc246_sound a c hc)

def sc634 : RawPoly ℕ :=
  [(1, [0, 1, 1]),
   (-2, [2])]

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc634_check :
    reduceTwo (prependC 1 sc247 ++ scaleR (-1) (prependC 0 sc248)) = sc634 := by
  decide +kernel

theorem sc634_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc634 = evRc a c (expWordR [1, 1, 5] (-5)) := by
  rw [← sc634_check]
  exact expTwo_step _ _ hc 0 [1, 5] (-5)
    sc247 sc248 (sc247_sound a c hc) (sc248_sound a c hc)

def sc635 : RawPoly ℕ :=
  [(mkRat (2) 3, [1, 1, 1]),
   (mkRat (-4) 3, [3])]

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc635_check :
    reduceTwo (prependC 1 sc248 ++ scaleR (-1) (prependC 0 sc249)) = sc635 := by
  decide +kernel

theorem sc635_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc635 = evRc a c (expWordR [1, 1, 5] (-4)) := by
  rw [← sc635_check]
  exact expTwo_step _ _ hc 0 [1, 5] (-4)
    sc248 sc249 (sc248_sound a c hc) (sc249_sound a c hc)

def sc636 : RawPoly ℕ :=
  [(mkRat (-1) 2, [0, 2, 2]),
   (1, [1, 1, 2]),
   (-1, [4])]

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc636_check :
    reduceTwo (prependC 1 sc249 ++ scaleR (-1) (prependC 0 sc250)) = sc636 := by
  decide +kernel

theorem sc636_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc636 = evRc a c (expWordR [1, 1, 5] (-3)) := by
  rw [← sc636_check]
  exact expTwo_step _ _ hc 0 [1, 5] (-3)
    sc249 sc250 (sc249_sound a c hc) (sc250_sound a c hc)

def sc637 : RawPoly ℕ :=
  [(mkRat (1) 3, [0, 1, 1, 1, 2]),
   (mkRat (-2) 3, [0, 2, 3]),
   (mkRat (-2) 15, [1, 1, 1, 1, 1]),
   (mkRat (2) 3, [1, 1, 3]),
   (mkRat (6) 5, [5])]

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc637_check :
    reduceTwo (prependC 1 sc250 ++ scaleR (-1) (prependC 0 sc251)) = sc637 := by
  decide +kernel

theorem sc637_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc637 = evRc a c (expWordR [1, 1, 5] (-2)) := by
  rw [← sc637_check]
  exact expTwo_step _ _ hc 0 [1, 5] (-2)
    sc250 sc251 (sc250_sound a c hc) (sc251_sound a c hc)

def sc638 : RawPoly ℕ :=
  [(mkRat (-1) 18, [0, 1, 1, 1, 1, 1, 1]),
   (mkRat (2) 9, [0, 1, 1, 1, 3]),
   (mkRat (1) 4, [0, 1, 1, 2, 2]),
   (mkRat (-1) 2, [0, 2, 4]),
   (mkRat (-2) 9, [0, 3, 3]),
   (mkRat (1) 2, [1, 1, 4]),
   (mkRat (-1) 6, [2, 2, 2]),
   (mkRat (-2) 3, [6])]

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc638_check :
    reduceTwo (prependC 1 sc251 ++ scaleR (-1) (prependC 0 sc252)) = sc638 := by
  decide +kernel

theorem sc638_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc638 = evRc a c (expWordR [1, 1, 5] (-1)) := by
  rw [← sc638_check]
  exact expTwo_step _ _ hc 0 [1, 5] (-1)
    sc251 sc252 (sc251_sound a c hc) (sc252_sound a c hc)

def sc639 : RawPoly ℕ :=
  [(mkRat (-1) 15, [0, 1, 1, 1, 1, 1, 2]),
   (mkRat (1) 6, [0, 1, 1, 1, 4]),
   (mkRat (1) 3, [0, 1, 1, 2, 3]),
   (mkRat (3) 5, [0, 2, 5]),
   (mkRat (-1) 3, [0, 3, 4]),
   (mkRat (-1) 35, [1, 1, 1, 1, 1, 1, 1]),
   (mkRat (1) 6, [1, 1, 1, 2, 2]),
   (mkRat (-3) 5, [1, 1, 5]),
   (mkRat (-1) 3, [2, 2, 3]),
   (mkRat (-4) 7, [7])]

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc639_check :
    reduceTwo (prependC 1 sc252 ++ scaleR (-1) (prependC 0 sc253)) = sc639 := by
  decide +kernel

theorem sc639_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc639 = evRc a c (expWordR [1, 1, 5] (0)) := by
  rw [← sc639_check]
  exact expTwo_step _ _ hc 0 [1, 5] (0)
    sc252 sc253 (sc252_sound a c hc) (sc253_sound a c hc)

def sc640 : RawPoly ℕ :=
  [(mkRat (-1) 180, [0, 1, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (-2) 45, [0, 1, 1, 1, 1, 1, 3]),
   (mkRat (-1) 5, [0, 1, 1, 1, 5]),
   (mkRat (1) 4, [0, 1, 1, 2, 4]),
   (mkRat (1) 9, [0, 1, 1, 3, 3]),
   (mkRat (-1) 48, [0, 2, 2, 2, 2]),
   (mkRat (-1) 3, [0, 2, 6]),
   (mkRat (2) 5, [0, 3, 5]),
   (mkRat (-1) 8, [0, 4, 4]),
   (mkRat (-1) 18, [1, 1, 1, 1, 1, 1, 2]),
   (mkRat (2) 9, [1, 1, 1, 2, 3]),
   (mkRat (1) 12, [1, 1, 2, 2, 2]),
   (mkRat (1) 3, [1, 1, 6]),
   (mkRat (-1) 4, [2, 2, 4]),
   (mkRat (-2) 9, [2, 3, 3]),
   (mkRat (-1) 2, [8])]

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc640_check :
    reduceTwo (prependC 1 sc253 ++ scaleR (-1) (prependC 0 sc254)) = sc640 := by
  decide +kernel

theorem sc640_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc640 = evRc a c (expWordR [1, 1, 5] (1)) := by
  rw [← sc640_check]
  exact expTwo_step _ _ hc 0 [1, 5] (1)
    sc253 sc254 (sc253_sound a c hc) (sc254_sound a c hc)

def sc641 : RawPoly ℕ :=
  [(mkRat (-1) 70, [0, 1, 1, 1, 1, 1, 1, 1, 2]),
   (mkRat (-1) 30, [0, 1, 1, 1, 1, 1, 4]),
   (mkRat (1) 36, [0, 1, 1, 1, 2, 2, 2]),
   (mkRat (1) 9, [0, 1, 1, 1, 6]),
   (mkRat (-3) 10, [0, 1, 1, 2, 5]),
   (mkRat (1) 6, [0, 1, 1, 3, 4]),
   (mkRat (-1) 18, [0, 2, 2, 2, 3]),
   (mkRat (-2) 7, [0, 2, 7]),
   (mkRat (-2) 9, [0, 3, 6]),
   (mkRat (3) 10, [0, 4, 5]),
   (mkRat (-1) 567, [1, 1, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (-1) 27, [1, 1, 1, 1, 1, 1, 3]),
   (mkRat (-1) 30, [1, 1, 1, 1, 1, 2, 2]),
   (mkRat (1) 6, [1, 1, 1, 2, 4]),
   (mkRat (2) 27, [1, 1, 1, 3, 3]),
   (mkRat (1) 6, [1, 1, 2, 2, 3]),
   (mkRat (2) 7, [1, 1, 7]),
   (mkRat (3) 10, [2, 2, 5]),
   (mkRat (-1) 3, [2, 3, 4]),
   (mkRat (-4) 81, [3, 3, 3]),
   (mkRat (-4) 9, [9])]

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc641_check :
    reduceTwo (prependC 1 sc254 ++ scaleR (-1) (prependC 0 sc255)) = sc641 := by
  decide +kernel

theorem sc641_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc641 = evRc a c (expWordR [1, 1, 5] (2)) := by
  rw [← sc641_check]
  exact expTwo_step _ _ hc 0 [1, 5] (2)
    sc254 sc255 (sc254_sound a c hc) (sc255_sound a c hc)

def sc642Part0 : RawPoly ℕ :=
  [(mkRat (-1) 4200, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (-1) 105, [0, 1, 1, 1, 1, 1, 1, 1, 3]),
   (mkRat (-1) 72, [0, 1, 1, 1, 1, 1, 1, 2, 2]),
   (mkRat (1) 25, [0, 1, 1, 1, 1, 1, 5]),
   (mkRat (1) 18, [0, 1, 1, 1, 2, 2, 3]),
   (mkRat (2) 21, [0, 1, 1, 1, 7]),
   (mkRat (1) 96, [0, 1, 1, 2, 2, 2, 2]),
   (mkRat (1) 6, [0, 1, 1, 2, 6]),
   (mkRat (-1) 5, [0, 1, 1, 3, 5]),
   (mkRat (1) 16, [0, 1, 1, 4, 4]),
   (mkRat (-1) 24, [0, 2, 2, 2, 4]),
   (mkRat (-1) 18, [0, 2, 2, 3, 3]),
   (mkRat (-1) 4, [0, 2, 8]),
   (mkRat (-4) 21, [0, 3, 7]),
   (mkRat (-1) 6, [0, 4, 6]),
   (mkRat (8) 25, [0, 5, 5]),
   (mkRat (-1) 180, [1, 1, 1, 1, 1, 1, 1, 1, 2]),
   (mkRat (-1) 36, [1, 1, 1, 1, 1, 1, 4]),
   (mkRat (-2) 45, [1, 1, 1, 1, 1, 2, 3]),
   (mkRat (-1) 5, [1, 1, 1, 2, 5]),
   (mkRat (1) 9, [1, 1, 1, 3, 4]),
   (mkRat (1) 8, [1, 1, 2, 2, 4]),
   (mkRat (1) 9, [1, 1, 2, 3, 3]),
   (mkRat (1) 4, [1, 1, 8])]

def sc642Part1 : RawPoly ℕ :=
  [(mkRat (-1) 240, [2, 2, 2, 2, 2]),
   (mkRat (-1) 6, [2, 2, 6]),
   (mkRat (2) 5, [2, 3, 5]),
   (mkRat (-1) 8, [2, 4, 4]),
   (mkRat (-1) 9, [3, 3, 4]),
   (mkRat (-2) 5, [10])]

def sc642 : RawPoly ℕ :=
  [sc642Part0,
   sc642Part1].flatten

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc642_check :
    reduceTwo (prependC 1 sc255 ++ scaleR (-1) (prependC 0 sc256)) = sc642 := by
  decide +kernel

theorem sc642_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc642 = evRc a c (expWordR [1, 1, 5] (3)) := by
  rw [← sc642_check]
  exact expTwo_step _ _ hc 0 [1, 5] (3)
    sc255 sc256 (sc255_sound a c hc) (sc256_sound a c hc)

def sc643Part0 : RawPoly ℕ :=
  [(mkRat (-1) 1134, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2]),
   (mkRat (-1) 140, [0, 1, 1, 1, 1, 1, 1, 1, 4]),
   (mkRat (-1) 54, [0, 1, 1, 1, 1, 1, 1, 2, 3]),
   (mkRat (-1) 180, [0, 1, 1, 1, 1, 1, 2, 2, 2]),
   (mkRat (-1) 45, [0, 1, 1, 1, 1, 1, 6]),
   (mkRat (1) 24, [0, 1, 1, 1, 2, 2, 4]),
   (mkRat (1) 27, [0, 1, 1, 1, 2, 3, 3]),
   (mkRat (1) 12, [0, 1, 1, 1, 8]),
   (mkRat (1) 36, [0, 1, 1, 2, 2, 2, 3]),
   (mkRat (1) 7, [0, 1, 1, 2, 7]),
   (mkRat (1) 9, [0, 1, 1, 3, 6]),
   (mkRat (-3) 20, [0, 1, 1, 4, 5]),
   (mkRat (1) 20, [0, 2, 2, 2, 5]),
   (mkRat (-1) 12, [0, 2, 2, 3, 4]),
   (mkRat (-2) 81, [0, 2, 3, 3, 3]),
   (mkRat (-2) 9, [0, 2, 9]),
   (mkRat (-1) 6, [0, 3, 8]),
   (mkRat (-1) 7, [0, 4, 7]),
   (mkRat (1) 5, [0, 5, 6]),
   (mkRat (-1) 17820, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (-1) 270, [1, 1, 1, 1, 1, 1, 1, 1, 3]),
   (mkRat (-1) 140, [1, 1, 1, 1, 1, 1, 1, 2, 2]),
   (mkRat (1) 30, [1, 1, 1, 1, 1, 1, 5]),
   (mkRat (-1) 30, [1, 1, 1, 1, 1, 2, 4])]

def sc643Part1 : RawPoly ℕ :=
  [(mkRat (-2) 135, [1, 1, 1, 1, 1, 3, 3]),
   (mkRat (1) 144, [1, 1, 1, 2, 2, 2, 2]),
   (mkRat (1) 9, [1, 1, 1, 2, 6]),
   (mkRat (-2) 15, [1, 1, 1, 3, 5]),
   (mkRat (1) 24, [1, 1, 1, 4, 4]),
   (mkRat (-3) 20, [1, 1, 2, 2, 5]),
   (mkRat (1) 6, [1, 1, 2, 3, 4]),
   (mkRat (2) 81, [1, 1, 3, 3, 3]),
   (mkRat (2) 9, [1, 1, 9]),
   (mkRat (-1) 72, [2, 2, 2, 2, 3]),
   (mkRat (-1) 7, [2, 2, 7]),
   (mkRat (-2) 9, [2, 3, 6]),
   (mkRat (3) 10, [2, 4, 5]),
   (mkRat (2) 15, [3, 3, 5]),
   (mkRat (-1) 12, [3, 4, 4]),
   (mkRat (-4) 11, [11])]

def sc643 : RawPoly ℕ :=
  [sc643Part0,
   sc643Part1].flatten

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc643_check :
    reduceTwo (prependC 1 sc256 ++ scaleR (-1) (prependC 0 sc257)) = sc643 := by
  decide +kernel

theorem sc643_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc643 = evRc a c (expWordR [1, 1, 5] (4)) := by
  rw [← sc643_check]
  exact expTwo_step _ _ hc 0 [1, 5] (4)
    sc256 sc257 (sc256_sound a c hc) (sc257_sound a c hc)

def sc644Part0 : RawPoly ℕ :=
  [(mkRat (-1) 170100, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (-1) 1701, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3]),
   (mkRat (-1) 720, [0, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2]),
   (mkRat (3) 350, [0, 1, 1, 1, 1, 1, 1, 1, 5]),
   (mkRat (-1) 72, [0, 1, 1, 1, 1, 1, 1, 2, 4]),
   (mkRat (-1) 162, [0, 1, 1, 1, 1, 1, 1, 3, 3]),
   (mkRat (-1) 90, [0, 1, 1, 1, 1, 1, 2, 2, 3]),
   (mkRat (-2) 105, [0, 1, 1, 1, 1, 1, 7]),
   (mkRat (-1) 20, [0, 1, 1, 1, 2, 2, 5]),
   (mkRat (1) 18, [0, 1, 1, 1, 2, 3, 4]),
   (mkRat (2) 243, [0, 1, 1, 1, 3, 3, 3]),
   (mkRat (2) 27, [0, 1, 1, 1, 9]),
   (mkRat (1) 48, [0, 1, 1, 2, 2, 2, 4]),
   (mkRat (1) 36, [0, 1, 1, 2, 2, 3, 3]),
   (mkRat (1) 8, [0, 1, 1, 2, 8]),
   (mkRat (2) 21, [0, 1, 1, 3, 7]),
   (mkRat (1) 12, [0, 1, 1, 4, 6]),
   (mkRat (-4) 25, [0, 1, 1, 5, 5]),
   (mkRat (-1) 2880, [0, 2, 2, 2, 2, 2, 2]),
   (mkRat (-1) 36, [0, 2, 2, 2, 6]),
   (mkRat (1) 10, [0, 2, 2, 3, 5]),
   (mkRat (-1) 32, [0, 2, 2, 4, 4]),
   (mkRat (-1) 18, [0, 2, 3, 3, 4]),
   (mkRat (-1) 5, [0, 2, 10])]

def sc644Part1 : RawPoly ℕ :=
  [(mkRat (-1) 243, [0, 3, 3, 3, 3]),
   (mkRat (-4) 27, [0, 3, 9]),
   (mkRat (-1) 8, [0, 4, 8]),
   (mkRat (6) 35, [0, 5, 7]),
   (mkRat (-1) 18, [0, 6, 6]),
   (mkRat (-1) 4200, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2]),
   (mkRat (-1) 360, [1, 1, 1, 1, 1, 1, 1, 1, 4]),
   (mkRat (-1) 105, [1, 1, 1, 1, 1, 1, 1, 2, 3]),
   (mkRat (-1) 216, [1, 1, 1, 1, 1, 1, 2, 2, 2]),
   (mkRat (-1) 54, [1, 1, 1, 1, 1, 1, 6]),
   (mkRat (1) 25, [1, 1, 1, 1, 1, 2, 5]),
   (mkRat (-1) 45, [1, 1, 1, 1, 1, 3, 4]),
   (mkRat (1) 54, [1, 1, 1, 2, 2, 2, 3]),
   (mkRat (2) 21, [1, 1, 1, 2, 7]),
   (mkRat (2) 27, [1, 1, 1, 3, 6]),
   (mkRat (-1) 10, [1, 1, 1, 4, 5]),
   (mkRat (1) 480, [1, 1, 2, 2, 2, 2, 2]),
   (mkRat (1) 12, [1, 1, 2, 2, 6]),
   (mkRat (-1) 5, [1, 1, 2, 3, 5]),
   (mkRat (1) 16, [1, 1, 2, 4, 4]),
   (mkRat (1) 18, [1, 1, 3, 3, 4]),
   (mkRat (1) 5, [1, 1, 10]),
   (mkRat (-1) 96, [2, 2, 2, 2, 4]),
   (mkRat (-1) 54, [2, 2, 2, 3, 3])]

def sc644Part2 : RawPoly ℕ :=
  [(mkRat (-1) 8, [2, 2, 8]),
   (mkRat (-4) 21, [2, 3, 7]),
   (mkRat (-1) 6, [2, 4, 6]),
   (mkRat (8) 25, [2, 5, 5]),
   (mkRat (-2) 27, [3, 3, 6]),
   (mkRat (1) 5, [3, 4, 5]),
   (mkRat (-1) 48, [4, 4, 4]),
   (mkRat (-1) 3, [12])]

def sc644 : RawPoly ℕ :=
  [sc644Part0,
   sc644Part1,
   sc644Part2].flatten

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc644_check :
    reduceTwo (prependC 1 sc257 ++ scaleR (-1) (prependC 0 sc258)) = sc644 := by
  decide +kernel

theorem sc644_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc644 = evRc a c (expWordR [1, 1, 5] (5)) := by
  rw [← sc644_check]
  exact expTwo_step _ _ hc 0 [1, 5] (5)
    sc257 sc258 (sc257_sound a c hc) (sc258_sound a c hc)

def sc645Part0 : RawPoly ℕ :=
  [(mkRat (-1) 35640, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2]),
   (mkRat (-1) 2268, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4]),
   (mkRat (-1) 540, [0, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3]),
   (mkRat (-1) 840, [0, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2]),
   (mkRat (-1) 210, [0, 1, 1, 1, 1, 1, 1, 1, 6]),
   (mkRat (1) 60, [0, 1, 1, 1, 1, 1, 1, 2, 5]),
   (mkRat (-1) 108, [0, 1, 1, 1, 1, 1, 1, 3, 4]),
   (mkRat (-1) 120, [0, 1, 1, 1, 1, 1, 2, 2, 4]),
   (mkRat (-1) 135, [0, 1, 1, 1, 1, 1, 2, 3, 3]),
   (mkRat (-1) 60, [0, 1, 1, 1, 1, 1, 8]),
   (mkRat (1) 1440, [0, 1, 1, 1, 2, 2, 2, 2, 2]),
   (mkRat (1) 36, [0, 1, 1, 1, 2, 2, 6]),
   (mkRat (-1) 15, [0, 1, 1, 1, 2, 3, 5]),
   (mkRat (1) 48, [0, 1, 1, 1, 2, 4, 4]),
   (mkRat (1) 54, [0, 1, 1, 1, 3, 3, 4]),
   (mkRat (1) 15, [0, 1, 1, 1, 10]),
   (mkRat (-1) 40, [0, 1, 1, 2, 2, 2, 5]),
   (mkRat (1) 24, [0, 1, 1, 2, 2, 3, 4]),
   (mkRat (1) 81, [0, 1, 1, 2, 3, 3, 3]),
   (mkRat (1) 9, [0, 1, 1, 2, 9]),
   (mkRat (1) 12, [0, 1, 1, 3, 8]),
   (mkRat (1) 14, [0, 1, 1, 4, 7]),
   (mkRat (-1) 10, [0, 1, 1, 5, 6]),
   (mkRat (-1) 720, [0, 2, 2, 2, 2, 2, 3])]

def sc645Part1 : RawPoly ℕ :=
  [(mkRat (-1) 42, [0, 2, 2, 2, 7]),
   (mkRat (-1) 18, [0, 2, 2, 3, 6]),
   (mkRat (3) 40, [0, 2, 2, 4, 5]),
   (mkRat (1) 15, [0, 2, 3, 3, 5]),
   (mkRat (-1) 24, [0, 2, 3, 4, 4]),
   (mkRat (-2) 11, [0, 2, 11]),
   (mkRat (-1) 81, [0, 3, 3, 3, 4]),
   (mkRat (-2) 15, [0, 3, 10]),
   (mkRat (-1) 9, [0, 4, 9]),
   (mkRat (3) 20, [0, 5, 8]),
   (mkRat (-2) 21, [0, 6, 7]),
   (mkRat (-1) 900900, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (-1) 6300, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3]),
   (mkRat (-1) 2268, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2]),
   (mkRat (1) 300, [1, 1, 1, 1, 1, 1, 1, 1, 5]),
   (mkRat (-1) 140, [1, 1, 1, 1, 1, 1, 1, 2, 4]),
   (mkRat (-1) 315, [1, 1, 1, 1, 1, 1, 1, 3, 3]),
   (mkRat (-1) 108, [1, 1, 1, 1, 1, 1, 2, 2, 3]),
   (mkRat (-1) 63, [1, 1, 1, 1, 1, 1, 7]),
   (mkRat (-1) 720, [1, 1, 1, 1, 1, 2, 2, 2, 2]),
   (mkRat (-1) 45, [1, 1, 1, 1, 1, 2, 6]),
   (mkRat (2) 75, [1, 1, 1, 1, 1, 3, 5]),
   (mkRat (-1) 120, [1, 1, 1, 1, 1, 4, 4]),
   (mkRat (1) 72, [1, 1, 1, 2, 2, 2, 4])]

def sc645Part2 : RawPoly ℕ :=
  [(mkRat (1) 54, [1, 1, 1, 2, 2, 3, 3]),
   (mkRat (1) 12, [1, 1, 1, 2, 8]),
   (mkRat (4) 63, [1, 1, 1, 3, 7]),
   (mkRat (1) 18, [1, 1, 1, 4, 6]),
   (mkRat (-8) 75, [1, 1, 1, 5, 5]),
   (mkRat (1) 144, [1, 1, 2, 2, 2, 2, 3]),
   (mkRat (1) 14, [1, 1, 2, 2, 7]),
   (mkRat (1) 9, [1, 1, 2, 3, 6]),
   (mkRat (-3) 20, [1, 1, 2, 4, 5]),
   (mkRat (-1) 15, [1, 1, 3, 3, 5]),
   (mkRat (1) 24, [1, 1, 3, 4, 4]),
   (mkRat (2) 11, [1, 1, 11]),
   (mkRat (1) 80, [2, 2, 2, 2, 5]),
   (mkRat (-1) 36, [2, 2, 2, 3, 4]),
   (mkRat (-1) 81, [2, 2, 3, 3, 3]),
   (mkRat (-1) 9, [2, 2, 9]),
   (mkRat (-1) 6, [2, 3, 8]),
   (mkRat (-1) 7, [2, 4, 7]),
   (mkRat (1) 5, [2, 5, 6]),
   (mkRat (-4) 63, [3, 3, 7]),
   (mkRat (-1) 9, [3, 4, 6]),
   (mkRat (16) 75, [3, 5, 5]),
   (mkRat (3) 40, [4, 4, 5]),
   (mkRat (-4) 13, [13])]

def sc645 : RawPoly ℕ :=
  [sc645Part0,
   sc645Part1,
   sc645Part2].flatten

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc645_check :
    reduceTwo (prependC 1 sc258 ++ scaleR (-1) (prependC 0 sc259)) = sc645 := by
  decide +kernel

theorem sc645_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc645 = evRc a c (expWordR [1, 1, 5] (6)) := by
  rw [← sc645_check]
  exact expTwo_step _ _ hc 0 [1, 5] (6)
    sc258 sc259 (sc258_sound a c hc) (sc259_sound a c hc)

def sc646Part0 : RawPoly ℕ :=
  [(mkRat (-1) 10478160, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (-1) 53460, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3]),
   (mkRat (-1) 16800, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2]),
   (mkRat (1) 1890, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5]),
   (mkRat (-1) 720, [0, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4]),
   (mkRat (-1) 1620, [0, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3]),
   (mkRat (-1) 420, [0, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3]),
   (mkRat (-1) 245, [0, 1, 1, 1, 1, 1, 1, 1, 7]),
   (mkRat (-1) 1728, [0, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2]),
   (mkRat (-1) 108, [0, 1, 1, 1, 1, 1, 1, 2, 6]),
   (mkRat (1) 90, [0, 1, 1, 1, 1, 1, 1, 3, 5]),
   (mkRat (-1) 288, [0, 1, 1, 1, 1, 1, 1, 4, 4]),
   (mkRat (1) 100, [0, 1, 1, 1, 1, 1, 2, 2, 5]),
   (mkRat (-1) 90, [0, 1, 1, 1, 1, 1, 2, 3, 4]),
   (mkRat (-2) 1215, [0, 1, 1, 1, 1, 1, 3, 3, 3]),
   (mkRat (-2) 135, [0, 1, 1, 1, 1, 1, 9]),
   (mkRat (1) 432, [0, 1, 1, 1, 2, 2, 2, 2, 3]),
   (mkRat (1) 42, [0, 1, 1, 1, 2, 2, 7]),
   (mkRat (1) 27, [0, 1, 1, 1, 2, 3, 6]),
   (mkRat (-1) 20, [0, 1, 1, 1, 2, 4, 5]),
   (mkRat (-1) 45, [0, 1, 1, 1, 3, 3, 5]),
   (mkRat (1) 72, [0, 1, 1, 1, 3, 4, 4]),
   (mkRat (2) 33, [0, 1, 1, 1, 11]),
   (mkRat (1) 5760, [0, 1, 1, 2, 2, 2, 2, 2, 2])]

def sc646Part1 : RawPoly ℕ :=
  [(mkRat (1) 72, [0, 1, 1, 2, 2, 2, 6]),
   (mkRat (-1) 20, [0, 1, 1, 2, 2, 3, 5]),
   (mkRat (1) 64, [0, 1, 1, 2, 2, 4, 4]),
   (mkRat (1) 36, [0, 1, 1, 2, 3, 3, 4]),
   (mkRat (1) 10, [0, 1, 1, 2, 10]),
   (mkRat (1) 486, [0, 1, 1, 3, 3, 3, 3]),
   (mkRat (2) 27, [0, 1, 1, 3, 9]),
   (mkRat (1) 16, [0, 1, 1, 4, 8]),
   (mkRat (-3) 35, [0, 1, 1, 5, 7]),
   (mkRat (1) 36, [0, 1, 1, 6, 6]),
   (mkRat (-1) 960, [0, 2, 2, 2, 2, 2, 4]),
   (mkRat (-1) 432, [0, 2, 2, 2, 2, 3, 3]),
   (mkRat (-1) 48, [0, 2, 2, 2, 8]),
   (mkRat (-1) 21, [0, 2, 2, 3, 7]),
   (mkRat (-1) 24, [0, 2, 2, 4, 6]),
   (mkRat (2) 25, [0, 2, 2, 5, 5]),
   (mkRat (-1) 27, [0, 2, 3, 3, 6]),
   (mkRat (1) 10, [0, 2, 3, 4, 5]),
   (mkRat (-1) 96, [0, 2, 4, 4, 4]),
   (mkRat (-1) 6, [0, 2, 12]),
   (mkRat (2) 135, [0, 3, 3, 3, 5]),
   (mkRat (-1) 72, [0, 3, 3, 4, 4]),
   (mkRat (-4) 33, [0, 3, 11]),
   (mkRat (-1) 10, [0, 4, 10])]

def sc646Part2 : RawPoly ℕ :=
  [(mkRat (2) 15, [0, 5, 9]),
   (mkRat (-1) 12, [0, 6, 8]),
   (mkRat (-2) 49, [0, 7, 7]),
   (mkRat (-1) 170100, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2]),
   (mkRat (-1) 8400, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4]),
   (mkRat (-1) 1701, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3]),
   (mkRat (-1) 2160, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2]),
   (mkRat (-1) 540, [1, 1, 1, 1, 1, 1, 1, 1, 6]),
   (mkRat (3) 350, [1, 1, 1, 1, 1, 1, 1, 2, 5]),
   (mkRat (-1) 210, [1, 1, 1, 1, 1, 1, 1, 3, 4]),
   (mkRat (-1) 144, [1, 1, 1, 1, 1, 1, 2, 2, 4]),
   (mkRat (-1) 162, [1, 1, 1, 1, 1, 1, 2, 3, 3]),
   (mkRat (-1) 72, [1, 1, 1, 1, 1, 1, 8]),
   (mkRat (-1) 270, [1, 1, 1, 1, 1, 2, 2, 2, 3]),
   (mkRat (-2) 105, [1, 1, 1, 1, 1, 2, 7]),
   (mkRat (-2) 135, [1, 1, 1, 1, 1, 3, 6]),
   (mkRat (1) 50, [1, 1, 1, 1, 1, 4, 5]),
   (mkRat (-1) 60, [1, 1, 1, 2, 2, 2, 5]),
   (mkRat (1) 36, [1, 1, 1, 2, 2, 3, 4]),
   (mkRat (2) 243, [1, 1, 1, 2, 3, 3, 3]),
   (mkRat (2) 27, [1, 1, 1, 2, 9]),
   (mkRat (1) 18, [1, 1, 1, 3, 8]),
   (mkRat (1) 21, [1, 1, 1, 4, 7]),
   (mkRat (-1) 15, [1, 1, 1, 5, 6])]

def sc646Part3 : RawPoly ℕ :=
  [(mkRat (1) 192, [1, 1, 2, 2, 2, 2, 4]),
   (mkRat (1) 108, [1, 1, 2, 2, 2, 3, 3]),
   (mkRat (1) 16, [1, 1, 2, 2, 8]),
   (mkRat (2) 21, [1, 1, 2, 3, 7]),
   (mkRat (1) 12, [1, 1, 2, 4, 6]),
   (mkRat (-4) 25, [1, 1, 2, 5, 5]),
   (mkRat (1) 27, [1, 1, 3, 3, 6]),
   (mkRat (-1) 10, [1, 1, 3, 4, 5]),
   (mkRat (1) 96, [1, 1, 4, 4, 4]),
   (mkRat (1) 6, [1, 1, 12]),
   (mkRat (-1) 20160, [2, 2, 2, 2, 2, 2, 2]),
   (mkRat (-1) 144, [2, 2, 2, 2, 6]),
   (mkRat (1) 30, [2, 2, 2, 3, 5]),
   (mkRat (-1) 96, [2, 2, 2, 4, 4]),
   (mkRat (-1) 36, [2, 2, 3, 3, 4]),
   (mkRat (-1) 10, [2, 2, 10]),
   (mkRat (-1) 243, [2, 3, 3, 3, 3]),
   (mkRat (-4) 27, [2, 3, 9]),
   (mkRat (-1) 8, [2, 4, 8]),
   (mkRat (6) 35, [2, 5, 7]),
   (mkRat (-1) 18, [2, 6, 6]),
   (mkRat (-1) 18, [3, 3, 8]),
   (mkRat (-2) 21, [3, 4, 7]),
   (mkRat (2) 15, [3, 5, 6])]

def sc646Part4 : RawPoly ℕ :=
  [(mkRat (-1) 24, [4, 4, 6]),
   (mkRat (4) 25, [4, 5, 5]),
   (mkRat (-2) 7, [14])]

def sc646 : RawPoly ℕ :=
  [sc646Part0,
   sc646Part1,
   sc646Part2,
   sc646Part3,
   sc646Part4].flatten

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc646_check :
    reduceTwo (prependC 1 sc259 ++ scaleR (-1) (prependC 0 sc260)) = sc646 := by
  decide +kernel

theorem sc646_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc646 = evRc a c (expWordR [1, 1, 5] (7)) := by
  rw [← sc646_check]
  exact expTwo_step _ _ hc 0 [1, 5] (7)
    sc259 sc260 (sc259_sound a c hc) (sc260_sound a c hc)

def sc647Part0 : RawPoly ℕ :=
  [(mkRat (-1) 1801800, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2]),
   (mkRat (-1) 71280, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4]),
   (mkRat (-1) 12600, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3]),
   (mkRat (-1) 13608, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2]),
   (mkRat (-1) 3402, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6]),
   (mkRat (1) 600, [0, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5]),
   (mkRat (-1) 1080, [0, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4]),
   (mkRat (-1) 560, [0, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4]),
   (mkRat (-1) 630, [0, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3]),
   (mkRat (-1) 280, [0, 1, 1, 1, 1, 1, 1, 1, 8]),
   (mkRat (-1) 648, [0, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3]),
   (mkRat (-1) 126, [0, 1, 1, 1, 1, 1, 1, 2, 7]),
   (mkRat (-1) 162, [0, 1, 1, 1, 1, 1, 1, 3, 6]),
   (mkRat (1) 120, [0, 1, 1, 1, 1, 1, 1, 4, 5]),
   (mkRat (-1) 7200, [0, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2]),
   (mkRat (-1) 180, [0, 1, 1, 1, 1, 1, 2, 2, 6]),
   (mkRat (1) 75, [0, 1, 1, 1, 1, 1, 2, 3, 5]),
   (mkRat (-1) 240, [0, 1, 1, 1, 1, 1, 2, 4, 4]),
   (mkRat (-1) 270, [0, 1, 1, 1, 1, 1, 3, 3, 4]),
   (mkRat (-1) 75, [0, 1, 1, 1, 1, 1, 10]),
   (mkRat (1) 576, [0, 1, 1, 1, 2, 2, 2, 2, 4]),
   (mkRat (1) 324, [0, 1, 1, 1, 2, 2, 2, 3, 3]),
   (mkRat (1) 48, [0, 1, 1, 1, 2, 2, 8]),
   (mkRat (2) 63, [0, 1, 1, 1, 2, 3, 7])]

def sc647Part1 : RawPoly ℕ :=
  [(mkRat (1) 36, [0, 1, 1, 1, 2, 4, 6]),
   (mkRat (-4) 75, [0, 1, 1, 1, 2, 5, 5]),
   (mkRat (1) 81, [0, 1, 1, 1, 3, 3, 6]),
   (mkRat (-1) 30, [0, 1, 1, 1, 3, 4, 5]),
   (mkRat (1) 288, [0, 1, 1, 1, 4, 4, 4]),
   (mkRat (1) 18, [0, 1, 1, 1, 12]),
   (mkRat (1) 1440, [0, 1, 1, 2, 2, 2, 2, 2, 3]),
   (mkRat (1) 84, [0, 1, 1, 2, 2, 2, 7]),
   (mkRat (1) 36, [0, 1, 1, 2, 2, 3, 6]),
   (mkRat (-3) 80, [0, 1, 1, 2, 2, 4, 5]),
   (mkRat (-1) 30, [0, 1, 1, 2, 3, 3, 5]),
   (mkRat (1) 48, [0, 1, 1, 2, 3, 4, 4]),
   (mkRat (1) 11, [0, 1, 1, 2, 11]),
   (mkRat (1) 162, [0, 1, 1, 3, 3, 3, 4]),
   (mkRat (1) 15, [0, 1, 1, 3, 10]),
   (mkRat (1) 18, [0, 1, 1, 4, 9]),
   (mkRat (-3) 40, [0, 1, 1, 5, 8]),
   (mkRat (1) 21, [0, 1, 1, 6, 7]),
   (mkRat (1) 800, [0, 2, 2, 2, 2, 2, 5]),
   (mkRat (-1) 288, [0, 2, 2, 2, 2, 3, 4]),
   (mkRat (-1) 486, [0, 2, 2, 2, 3, 3, 3]),
   (mkRat (-1) 54, [0, 2, 2, 2, 9]),
   (mkRat (-1) 24, [0, 2, 2, 3, 8]),
   (mkRat (-1) 28, [0, 2, 2, 4, 7])]

def sc647Part2 : RawPoly ℕ :=
  [(mkRat (1) 20, [0, 2, 2, 5, 6]),
   (mkRat (-2) 63, [0, 2, 3, 3, 7]),
   (mkRat (-1) 18, [0, 2, 3, 4, 6]),
   (mkRat (8) 75, [0, 2, 3, 5, 5]),
   (mkRat (3) 80, [0, 2, 4, 4, 5]),
   (mkRat (-2) 13, [0, 2, 13]),
   (mkRat (-2) 243, [0, 3, 3, 3, 6]),
   (mkRat (1) 30, [0, 3, 3, 4, 5]),
   (mkRat (-1) 144, [0, 3, 4, 4, 4]),
   (mkRat (-1) 9, [0, 3, 12]),
   (mkRat (-1) 11, [0, 4, 11]),
   (mkRat (3) 25, [0, 5, 10]),
   (mkRat (-2) 27, [0, 6, 9]),
   (mkRat (-1) 14, [0, 7, 8]),
   (mkRat (-1) 66339000, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (-1) 255150, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3]),
   (mkRat (-1) 71280, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2]),
   (mkRat (1) 7000, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5]),
   (mkRat (-1) 2268, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4]),
   (mkRat (-1) 5103, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3]),
   (mkRat (-1) 1080, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3]),
   (mkRat (-1) 630, [1, 1, 1, 1, 1, 1, 1, 1, 7]),
   (mkRat (-1) 3360, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2]),
   (mkRat (-1) 210, [1, 1, 1, 1, 1, 1, 1, 2, 6])]

def sc647Part3 : RawPoly ℕ :=
  [(mkRat (1) 175, [1, 1, 1, 1, 1, 1, 1, 3, 5]),
   (mkRat (-1) 560, [1, 1, 1, 1, 1, 1, 1, 4, 4]),
   (mkRat (1) 120, [1, 1, 1, 1, 1, 1, 2, 2, 5]),
   (mkRat (-1) 108, [1, 1, 1, 1, 1, 1, 2, 3, 4]),
   (mkRat (-1) 729, [1, 1, 1, 1, 1, 1, 3, 3, 3]),
   (mkRat (-1) 81, [1, 1, 1, 1, 1, 1, 9]),
   (mkRat (-1) 360, [1, 1, 1, 1, 1, 2, 2, 2, 4]),
   (mkRat (-1) 270, [1, 1, 1, 1, 1, 2, 2, 3, 3]),
   (mkRat (-1) 60, [1, 1, 1, 1, 1, 2, 8]),
   (mkRat (-4) 315, [1, 1, 1, 1, 1, 3, 7]),
   (mkRat (-1) 90, [1, 1, 1, 1, 1, 4, 6]),
   (mkRat (8) 375, [1, 1, 1, 1, 1, 5, 5]),
   (mkRat (1) 8640, [1, 1, 1, 2, 2, 2, 2, 2, 2]),
   (mkRat (1) 108, [1, 1, 1, 2, 2, 2, 6]),
   (mkRat (-1) 30, [1, 1, 1, 2, 2, 3, 5]),
   (mkRat (1) 96, [1, 1, 1, 2, 2, 4, 4]),
   (mkRat (1) 54, [1, 1, 1, 2, 3, 3, 4]),
   (mkRat (1) 15, [1, 1, 1, 2, 10]),
   (mkRat (1) 729, [1, 1, 1, 3, 3, 3, 3]),
   (mkRat (4) 81, [1, 1, 1, 3, 9]),
   (mkRat (1) 24, [1, 1, 1, 4, 8]),
   (mkRat (-2) 35, [1, 1, 1, 5, 7]),
   (mkRat (1) 54, [1, 1, 1, 6, 6]),
   (mkRat (-1) 160, [1, 1, 2, 2, 2, 2, 5])]

def sc647Part4 : RawPoly ℕ :=
  [(mkRat (1) 72, [1, 1, 2, 2, 2, 3, 4]),
   (mkRat (1) 162, [1, 1, 2, 2, 3, 3, 3]),
   (mkRat (1) 18, [1, 1, 2, 2, 9]),
   (mkRat (1) 12, [1, 1, 2, 3, 8]),
   (mkRat (1) 14, [1, 1, 2, 4, 7]),
   (mkRat (-1) 10, [1, 1, 2, 5, 6]),
   (mkRat (2) 63, [1, 1, 3, 3, 7]),
   (mkRat (1) 18, [1, 1, 3, 4, 6]),
   (mkRat (-8) 75, [1, 1, 3, 5, 5]),
   (mkRat (-3) 80, [1, 1, 4, 4, 5]),
   (mkRat (2) 13, [1, 1, 13]),
   (mkRat (-1) 4320, [2, 2, 2, 2, 2, 2, 3]),
   (mkRat (-1) 168, [2, 2, 2, 2, 7]),
   (mkRat (-1) 54, [2, 2, 2, 3, 6]),
   (mkRat (1) 40, [2, 2, 2, 4, 5]),
   (mkRat (1) 30, [2, 2, 3, 3, 5]),
   (mkRat (-1) 48, [2, 2, 3, 4, 4]),
   (mkRat (-1) 11, [2, 2, 11]),
   (mkRat (-1) 81, [2, 3, 3, 3, 4]),
   (mkRat (-2) 15, [2, 3, 10]),
   (mkRat (-1) 9, [2, 4, 9]),
   (mkRat (3) 20, [2, 5, 8]),
   (mkRat (-2) 21, [2, 6, 7]),
   (mkRat (-2) 3645, [3, 3, 3, 3, 3])]

def sc647Part5 : RawPoly ℕ :=
  [(mkRat (-4) 81, [3, 3, 9]),
   (mkRat (-1) 12, [3, 4, 8]),
   (mkRat (4) 35, [3, 5, 7]),
   (mkRat (-1) 27, [3, 6, 6]),
   (mkRat (-1) 28, [4, 4, 7]),
   (mkRat (1) 10, [4, 5, 6]),
   (mkRat (26) 375, [5, 5, 5]),
   (mkRat (-4) 15, [15])]

def sc647 : RawPoly ℕ :=
  [sc647Part0,
   sc647Part1,
   sc647Part2,
   sc647Part3,
   sc647Part4,
   sc647Part5].flatten

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc647_check :
    reduceTwo (prependC 1 sc260 ++ scaleR (-1) (prependC 0 sc261)) = sc647 := by
  decide +kernel

theorem sc647_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc647 = evRc a c (expWordR [1, 1, 5] (8)) := by
  rw [← sc647_check]
  exact expTwo_step _ _ hc 0 [1, 5] (8)
    sc260 sc261 (sc260_sound a c hc) (sc261_sound a c hc)

def sc648Part0 : RawPoly ℕ :=
  [(mkRat (-1) 908107200, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (-1) 2702700, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3]),
   (mkRat (-1) 680400, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2]),
   (mkRat (1) 59400, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5]),
   (mkRat (-1) 16800, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4]),
   (mkRat (-1) 37800, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3]),
   (mkRat (-1) 6804, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3]),
   (mkRat (-1) 3969, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7]),
   (mkRat (-1) 17280, [0, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2]),
   (mkRat (-1) 1080, [0, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6]),
   (mkRat (1) 900, [0, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5]),
   (mkRat (-1) 2880, [0, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4]),
   (mkRat (3) 1400, [0, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5]),
   (mkRat (-1) 420, [0, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4]),
   (mkRat (-1) 2835, [0, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3]),
   (mkRat (-1) 315, [0, 1, 1, 1, 1, 1, 1, 1, 9]),
   (mkRat (-1) 864, [0, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4]),
   (mkRat (-1) 648, [0, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3]),
   (mkRat (-1) 144, [0, 1, 1, 1, 1, 1, 1, 2, 8]),
   (mkRat (-1) 189, [0, 1, 1, 1, 1, 1, 1, 3, 7]),
   (mkRat (-1) 216, [0, 1, 1, 1, 1, 1, 1, 4, 6]),
   (mkRat (2) 225, [0, 1, 1, 1, 1, 1, 1, 5, 5]),
   (mkRat (-1) 2160, [0, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3]),
   (mkRat (-1) 210, [0, 1, 1, 1, 1, 1, 2, 2, 7])]

def sc648Part1 : RawPoly ℕ :=
  [(mkRat (-1) 135, [0, 1, 1, 1, 1, 1, 2, 3, 6]),
   (mkRat (1) 100, [0, 1, 1, 1, 1, 1, 2, 4, 5]),
   (mkRat (1) 225, [0, 1, 1, 1, 1, 1, 3, 3, 5]),
   (mkRat (-1) 360, [0, 1, 1, 1, 1, 1, 3, 4, 4]),
   (mkRat (-2) 165, [0, 1, 1, 1, 1, 1, 11]),
   (mkRat (-1) 480, [0, 1, 1, 1, 2, 2, 2, 2, 5]),
   (mkRat (1) 216, [0, 1, 1, 1, 2, 2, 2, 3, 4]),
   (mkRat (1) 486, [0, 1, 1, 1, 2, 2, 3, 3, 3]),
   (mkRat (1) 54, [0, 1, 1, 1, 2, 2, 9]),
   (mkRat (1) 36, [0, 1, 1, 1, 2, 3, 8]),
   (mkRat (1) 42, [0, 1, 1, 1, 2, 4, 7]),
   (mkRat (-1) 30, [0, 1, 1, 1, 2, 5, 6]),
   (mkRat (2) 189, [0, 1, 1, 1, 3, 3, 7]),
   (mkRat (1) 54, [0, 1, 1, 1, 3, 4, 6]),
   (mkRat (-8) 225, [0, 1, 1, 1, 3, 5, 5]),
   (mkRat (-1) 80, [0, 1, 1, 1, 4, 4, 5]),
   (mkRat (2) 39, [0, 1, 1, 1, 13]),
   (mkRat (1) 1920, [0, 1, 1, 2, 2, 2, 2, 2, 4]),
   (mkRat (1) 864, [0, 1, 1, 2, 2, 2, 2, 3, 3]),
   (mkRat (1) 96, [0, 1, 1, 2, 2, 2, 8]),
   (mkRat (1) 42, [0, 1, 1, 2, 2, 3, 7]),
   (mkRat (1) 48, [0, 1, 1, 2, 2, 4, 6]),
   (mkRat (-1) 25, [0, 1, 1, 2, 2, 5, 5]),
   (mkRat (1) 54, [0, 1, 1, 2, 3, 3, 6])]

def sc648Part2 : RawPoly ℕ :=
  [(mkRat (-1) 20, [0, 1, 1, 2, 3, 4, 5]),
   (mkRat (1) 192, [0, 1, 1, 2, 4, 4, 4]),
   (mkRat (1) 12, [0, 1, 1, 2, 12]),
   (mkRat (-1) 135, [0, 1, 1, 3, 3, 3, 5]),
   (mkRat (1) 144, [0, 1, 1, 3, 3, 4, 4]),
   (mkRat (2) 33, [0, 1, 1, 3, 11]),
   (mkRat (1) 20, [0, 1, 1, 4, 10]),
   (mkRat (-1) 15, [0, 1, 1, 5, 9]),
   (mkRat (1) 24, [0, 1, 1, 6, 8]),
   (mkRat (1) 49, [0, 1, 1, 7, 7]),
   (mkRat (-1) 322560, [0, 2, 2, 2, 2, 2, 2, 2, 2]),
   (mkRat (-1) 1440, [0, 2, 2, 2, 2, 2, 6]),
   (mkRat (1) 240, [0, 2, 2, 2, 2, 3, 5]),
   (mkRat (-1) 768, [0, 2, 2, 2, 2, 4, 4]),
   (mkRat (-1) 216, [0, 2, 2, 2, 3, 3, 4]),
   (mkRat (-1) 60, [0, 2, 2, 2, 10]),
   (mkRat (-1) 972, [0, 2, 2, 3, 3, 3, 3]),
   (mkRat (-1) 27, [0, 2, 2, 3, 9]),
   (mkRat (-1) 32, [0, 2, 2, 4, 8]),
   (mkRat (3) 70, [0, 2, 2, 5, 7]),
   (mkRat (-1) 72, [0, 2, 2, 6, 6]),
   (mkRat (-1) 36, [0, 2, 3, 3, 8]),
   (mkRat (-1) 21, [0, 2, 3, 4, 7]),
   (mkRat (1) 15, [0, 2, 3, 5, 6])]

def sc648Part3 : RawPoly ℕ :=
  [(mkRat (-1) 48, [0, 2, 4, 4, 6]),
   (mkRat (2) 25, [0, 2, 4, 5, 5]),
   (mkRat (-1) 7, [0, 2, 14]),
   (mkRat (-4) 567, [0, 3, 3, 3, 7]),
   (mkRat (-1) 54, [0, 3, 3, 4, 6]),
   (mkRat (8) 225, [0, 3, 3, 5, 5]),
   (mkRat (1) 40, [0, 3, 4, 4, 5]),
   (mkRat (-4) 39, [0, 3, 13]),
   (mkRat (-1) 768, [0, 4, 4, 4, 4]),
   (mkRat (-1) 12, [0, 4, 12]),
   (mkRat (6) 55, [0, 5, 11]),
   (mkRat (-1) 15, [0, 6, 10]),
   (mkRat (-4) 63, [0, 7, 9]),
   (mkRat (-1) 32, [0, 8, 8]),
   (mkRat (-1) 10478160, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2]),
   (mkRat (-1) 340200, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4]),
   (mkRat (-1) 53460, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3]),
   (mkRat (-1) 50400, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2]),
   (mkRat (-1) 12600, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6]),
   (mkRat (1) 1890, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5]),
   (mkRat (-1) 3402, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4]),
   (mkRat (-1) 1440, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4]),
   (mkRat (-1) 1620, [1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3]),
   (mkRat (-1) 720, [1, 1, 1, 1, 1, 1, 1, 1, 8])]

def sc648Part4 : RawPoly ℕ :=
  [(mkRat (-1) 1260, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3]),
   (mkRat (-1) 245, [1, 1, 1, 1, 1, 1, 1, 2, 7]),
   (mkRat (-1) 315, [1, 1, 1, 1, 1, 1, 1, 3, 6]),
   (mkRat (3) 700, [1, 1, 1, 1, 1, 1, 1, 4, 5]),
   (mkRat (-1) 8640, [1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2]),
   (mkRat (-1) 216, [1, 1, 1, 1, 1, 1, 2, 2, 6]),
   (mkRat (1) 90, [1, 1, 1, 1, 1, 1, 2, 3, 5]),
   (mkRat (-1) 288, [1, 1, 1, 1, 1, 1, 2, 4, 4]),
   (mkRat (-1) 324, [1, 1, 1, 1, 1, 1, 3, 3, 4]),
   (mkRat (-1) 90, [1, 1, 1, 1, 1, 1, 10]),
   (mkRat (1) 300, [1, 1, 1, 1, 1, 2, 2, 2, 5]),
   (mkRat (-1) 180, [1, 1, 1, 1, 1, 2, 2, 3, 4]),
   (mkRat (-2) 1215, [1, 1, 1, 1, 1, 2, 3, 3, 3]),
   (mkRat (-2) 135, [1, 1, 1, 1, 1, 2, 9]),
   (mkRat (-1) 90, [1, 1, 1, 1, 1, 3, 8]),
   (mkRat (-1) 105, [1, 1, 1, 1, 1, 4, 7]),
   (mkRat (1) 75, [1, 1, 1, 1, 1, 5, 6]),
   (mkRat (1) 2160, [1, 1, 1, 2, 2, 2, 2, 2, 3]),
   (mkRat (1) 126, [1, 1, 1, 2, 2, 2, 7]),
   (mkRat (1) 54, [1, 1, 1, 2, 2, 3, 6]),
   (mkRat (-1) 40, [1, 1, 1, 2, 2, 4, 5]),
   (mkRat (-1) 45, [1, 1, 1, 2, 3, 3, 5]),
   (mkRat (1) 72, [1, 1, 1, 2, 3, 4, 4]),
   (mkRat (2) 33, [1, 1, 1, 2, 11])]

def sc648Part5 : RawPoly ℕ :=
  [(mkRat (1) 243, [1, 1, 1, 3, 3, 3, 4]),
   (mkRat (2) 45, [1, 1, 1, 3, 10]),
   (mkRat (1) 27, [1, 1, 1, 4, 9]),
   (mkRat (-1) 20, [1, 1, 1, 5, 8]),
   (mkRat (2) 63, [1, 1, 1, 6, 7]),
   (mkRat (1) 40320, [1, 1, 2, 2, 2, 2, 2, 2, 2]),
   (mkRat (1) 288, [1, 1, 2, 2, 2, 2, 6]),
   (mkRat (-1) 60, [1, 1, 2, 2, 2, 3, 5]),
   (mkRat (1) 192, [1, 1, 2, 2, 2, 4, 4]),
   (mkRat (1) 72, [1, 1, 2, 2, 3, 3, 4]),
   (mkRat (1) 20, [1, 1, 2, 2, 10]),
   (mkRat (1) 486, [1, 1, 2, 3, 3, 3, 3]),
   (mkRat (2) 27, [1, 1, 2, 3, 9]),
   (mkRat (1) 16, [1, 1, 2, 4, 8]),
   (mkRat (-3) 35, [1, 1, 2, 5, 7]),
   (mkRat (1) 36, [1, 1, 2, 6, 6]),
   (mkRat (1) 36, [1, 1, 3, 3, 8]),
   (mkRat (1) 21, [1, 1, 3, 4, 7]),
   (mkRat (-1) 15, [1, 1, 3, 5, 6]),
   (mkRat (1) 48, [1, 1, 4, 4, 6]),
   (mkRat (-2) 25, [1, 1, 4, 5, 5]),
   (mkRat (1) 7, [1, 1, 14]),
   (mkRat (-1) 5760, [2, 2, 2, 2, 2, 2, 4]),
   (mkRat (-1) 2160, [2, 2, 2, 2, 2, 3, 3])]

def sc648Part6 : RawPoly ℕ :=
  [(mkRat (-1) 192, [2, 2, 2, 2, 8]),
   (mkRat (-1) 63, [2, 2, 2, 3, 7]),
   (mkRat (-1) 72, [2, 2, 2, 4, 6]),
   (mkRat (2) 75, [2, 2, 2, 5, 5]),
   (mkRat (-1) 54, [2, 2, 3, 3, 6]),
   (mkRat (1) 20, [2, 2, 3, 4, 5]),
   (mkRat (-1) 192, [2, 2, 4, 4, 4]),
   (mkRat (-1) 12, [2, 2, 12]),
   (mkRat (2) 135, [2, 3, 3, 3, 5]),
   (mkRat (-1) 72, [2, 3, 3, 4, 4]),
   (mkRat (-4) 33, [2, 3, 11]),
   (mkRat (-1) 10, [2, 4, 10]),
   (mkRat (2) 15, [2, 5, 9]),
   (mkRat (-1) 12, [2, 6, 8]),
   (mkRat (-2) 49, [2, 7, 7]),
   (mkRat (-1) 486, [3, 3, 3, 3, 4]),
   (mkRat (-2) 45, [3, 3, 10]),
   (mkRat (-2) 27, [3, 4, 9]),
   (mkRat (1) 10, [3, 5, 8]),
   (mkRat (-4) 63, [3, 6, 7]),
   (mkRat (-1) 32, [4, 4, 8]),
   (mkRat (3) 35, [4, 5, 7]),
   (mkRat (-1) 36, [4, 6, 6]),
   (mkRat (8) 75, [5, 5, 6])]

def sc648Part7 : RawPoly ℕ :=
  [(mkRat (-1) 4, [16])]

def sc648 : RawPoly ℕ :=
  [sc648Part0,
   sc648Part1,
   sc648Part2,
   sc648Part3,
   sc648Part4,
   sc648Part5,
   sc648Part6,
   sc648Part7].flatten

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc648_check :
    reduceTwo (prependC 1 sc261 ++ scaleR (-1) (prependC 0 sc262)) = sc648 := by
  decide +kernel

theorem sc648_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc648 = evRc a c (expWordR [1, 1, 5] (9)) := by
  rw [← sc648_check]
  exact expTwo_step _ _ hc 0 [1, 5] (9)
    sc261 sc262 (sc261_sound a c hc) (sc262_sound a c hc)

def sc649 : RawPoly ℕ :=
  [(mkRat (2) 3, [1, 1, 1]),
   (mkRat (-4) 3, [3])]

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc649_check :
    reduceTwo (prependC 1 sc264 ++ scaleR (-1) (prependC 0 sc265)) = sc649 := by
  decide +kernel

theorem sc649_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc649 = evRc a c (expWordR [1, 1, 6] (-5)) := by
  rw [← sc649_check]
  exact expTwo_step _ _ hc 0 [1, 6] (-5)
    sc264 sc265 (sc264_sound a c hc) (sc265_sound a c hc)

def sc650 : RawPoly ℕ :=
  [(mkRat (-1) 2, [0, 2, 2]),
   (1, [1, 1, 2]),
   (-1, [4])]

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc650_check :
    reduceTwo (prependC 1 sc265 ++ scaleR (-1) (prependC 0 sc266)) = sc650 := by
  decide +kernel

theorem sc650_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc650 = evRc a c (expWordR [1, 1, 6] (-4)) := by
  rw [← sc650_check]
  exact expTwo_step _ _ hc 0 [1, 6] (-4)
    sc265 sc266 (sc265_sound a c hc) (sc266_sound a c hc)

def sc651 : RawPoly ℕ :=
  [(mkRat (1) 3, [0, 1, 1, 1, 2]),
   (mkRat (-2) 3, [0, 2, 3]),
   (mkRat (-2) 15, [1, 1, 1, 1, 1]),
   (mkRat (2) 3, [1, 1, 3]),
   (mkRat (-4) 5, [5])]

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc651_check :
    reduceTwo (prependC 1 sc266 ++ scaleR (-1) (prependC 0 sc267)) = sc651 := by
  decide +kernel

theorem sc651_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc651 = evRc a c (expWordR [1, 1, 6] (-3)) := by
  rw [← sc651_check]
  exact expTwo_step _ _ hc 0 [1, 6] (-3)
    sc266 sc267 (sc266_sound a c hc) (sc267_sound a c hc)

def sc652 : RawPoly ℕ :=
  [(mkRat (-1) 18, [0, 1, 1, 1, 1, 1, 1]),
   (mkRat (2) 9, [0, 1, 1, 1, 3]),
   (mkRat (1) 4, [0, 1, 1, 2, 2]),
   (mkRat (-1) 2, [0, 2, 4]),
   (mkRat (-2) 9, [0, 3, 3]),
   (mkRat (1) 2, [1, 1, 4]),
   (mkRat (-1) 6, [2, 2, 2]),
   (mkRat (4) 3, [6])]

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc652_check :
    reduceTwo (prependC 1 sc267 ++ scaleR (-1) (prependC 0 sc268)) = sc652 := by
  decide +kernel

theorem sc652_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc652 = evRc a c (expWordR [1, 1, 6] (-2)) := by
  rw [← sc652_check]
  exact expTwo_step _ _ hc 0 [1, 6] (-2)
    sc267 sc268 (sc267_sound a c hc) (sc268_sound a c hc)

def sc653 : RawPoly ℕ :=
  [(mkRat (-1) 15, [0, 1, 1, 1, 1, 1, 2]),
   (mkRat (1) 6, [0, 1, 1, 1, 4]),
   (mkRat (1) 3, [0, 1, 1, 2, 3]),
   (mkRat (-2) 5, [0, 2, 5]),
   (mkRat (-1) 3, [0, 3, 4]),
   (mkRat (-1) 35, [1, 1, 1, 1, 1, 1, 1]),
   (mkRat (1) 6, [1, 1, 1, 2, 2]),
   (mkRat (2) 5, [1, 1, 5]),
   (mkRat (-1) 3, [2, 2, 3]),
   (mkRat (-4) 7, [7])]

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc653_check :
    reduceTwo (prependC 1 sc268 ++ scaleR (-1) (prependC 0 sc269)) = sc653 := by
  decide +kernel

theorem sc653_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc653 = evRc a c (expWordR [1, 1, 6] (-1)) := by
  rw [← sc653_check]
  exact expTwo_step _ _ hc 0 [1, 6] (-1)
    sc268 sc269 (sc268_sound a c hc) (sc269_sound a c hc)

def sc654 : RawPoly ℕ :=
  [(mkRat (-1) 180, [0, 1, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (-2) 45, [0, 1, 1, 1, 1, 1, 3]),
   (mkRat (2) 15, [0, 1, 1, 1, 5]),
   (mkRat (1) 4, [0, 1, 1, 2, 4]),
   (mkRat (1) 9, [0, 1, 1, 3, 3]),
   (mkRat (-1) 48, [0, 2, 2, 2, 2]),
   (mkRat (2) 3, [0, 2, 6]),
   (mkRat (-4) 15, [0, 3, 5]),
   (mkRat (-1) 8, [0, 4, 4]),
   (mkRat (-1) 18, [1, 1, 1, 1, 1, 1, 2]),
   (mkRat (2) 9, [1, 1, 1, 2, 3]),
   (mkRat (1) 12, [1, 1, 2, 2, 2]),
   (mkRat (-2) 3, [1, 1, 6]),
   (mkRat (-1) 4, [2, 2, 4]),
   (mkRat (-2) 9, [2, 3, 3]),
   (mkRat (-1) 2, [8])]

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc654_check :
    reduceTwo (prependC 1 sc269 ++ scaleR (-1) (prependC 0 sc270)) = sc654 := by
  decide +kernel

theorem sc654_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc654 = evRc a c (expWordR [1, 1, 6] (0)) := by
  rw [← sc654_check]
  exact expTwo_step _ _ hc 0 [1, 6] (0)
    sc269 sc270 (sc269_sound a c hc) (sc270_sound a c hc)

def sc655 : RawPoly ℕ :=
  [(mkRat (-1) 70, [0, 1, 1, 1, 1, 1, 1, 1, 2]),
   (mkRat (-1) 30, [0, 1, 1, 1, 1, 1, 4]),
   (mkRat (1) 36, [0, 1, 1, 1, 2, 2, 2]),
   (mkRat (-2) 9, [0, 1, 1, 1, 6]),
   (mkRat (1) 5, [0, 1, 1, 2, 5]),
   (mkRat (1) 6, [0, 1, 1, 3, 4]),
   (mkRat (-1) 18, [0, 2, 2, 2, 3]),
   (mkRat (-2) 7, [0, 2, 7]),
   (mkRat (4) 9, [0, 3, 6]),
   (mkRat (-1) 5, [0, 4, 5]),
   (mkRat (-1) 567, [1, 1, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (-1) 27, [1, 1, 1, 1, 1, 1, 3]),
   (mkRat (-1) 30, [1, 1, 1, 1, 1, 2, 2]),
   (mkRat (1) 6, [1, 1, 1, 2, 4]),
   (mkRat (2) 27, [1, 1, 1, 3, 3]),
   (mkRat (1) 6, [1, 1, 2, 2, 3]),
   (mkRat (2) 7, [1, 1, 7]),
   (mkRat (-1) 5, [2, 2, 5]),
   (mkRat (-1) 3, [2, 3, 4]),
   (mkRat (-4) 81, [3, 3, 3]),
   (mkRat (-4) 9, [9])]

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc655_check :
    reduceTwo (prependC 1 sc270 ++ scaleR (-1) (prependC 0 sc271)) = sc655 := by
  decide +kernel

theorem sc655_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc655 = evRc a c (expWordR [1, 1, 6] (1)) := by
  rw [← sc655_check]
  exact expTwo_step _ _ hc 0 [1, 6] (1)
    sc270 sc271 (sc270_sound a c hc) (sc271_sound a c hc)

def sc656Part0 : RawPoly ℕ :=
  [(mkRat (-1) 4200, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (-1) 105, [0, 1, 1, 1, 1, 1, 1, 1, 3]),
   (mkRat (-1) 72, [0, 1, 1, 1, 1, 1, 1, 2, 2]),
   (mkRat (-2) 75, [0, 1, 1, 1, 1, 1, 5]),
   (mkRat (1) 18, [0, 1, 1, 1, 2, 2, 3]),
   (mkRat (2) 21, [0, 1, 1, 1, 7]),
   (mkRat (1) 96, [0, 1, 1, 2, 2, 2, 2]),
   (mkRat (-1) 3, [0, 1, 1, 2, 6]),
   (mkRat (2) 15, [0, 1, 1, 3, 5]),
   (mkRat (1) 16, [0, 1, 1, 4, 4]),
   (mkRat (-1) 24, [0, 2, 2, 2, 4]),
   (mkRat (-1) 18, [0, 2, 2, 3, 3]),
   (mkRat (-1) 4, [0, 2, 8]),
   (mkRat (-4) 21, [0, 3, 7]),
   (mkRat (1) 3, [0, 4, 6]),
   (mkRat (-2) 25, [0, 5, 5]),
   (mkRat (-1) 180, [1, 1, 1, 1, 1, 1, 1, 1, 2]),
   (mkRat (-1) 36, [1, 1, 1, 1, 1, 1, 4]),
   (mkRat (-2) 45, [1, 1, 1, 1, 1, 2, 3]),
   (mkRat (2) 15, [1, 1, 1, 2, 5]),
   (mkRat (1) 9, [1, 1, 1, 3, 4]),
   (mkRat (1) 8, [1, 1, 2, 2, 4]),
   (mkRat (1) 9, [1, 1, 2, 3, 3]),
   (mkRat (1) 4, [1, 1, 8])]

def sc656Part1 : RawPoly ℕ :=
  [(mkRat (-1) 240, [2, 2, 2, 2, 2]),
   (mkRat (1) 3, [2, 2, 6]),
   (mkRat (-4) 15, [2, 3, 5]),
   (mkRat (-1) 8, [2, 4, 4]),
   (mkRat (-1) 9, [3, 3, 4]),
   (mkRat (-2) 5, [10])]

def sc656 : RawPoly ℕ :=
  [sc656Part0,
   sc656Part1].flatten

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc656_check :
    reduceTwo (prependC 1 sc271 ++ scaleR (-1) (prependC 0 sc272)) = sc656 := by
  decide +kernel

theorem sc656_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc656 = evRc a c (expWordR [1, 1, 6] (2)) := by
  rw [← sc656_check]
  exact expTwo_step _ _ hc 0 [1, 6] (2)
    sc271 sc272 (sc271_sound a c hc) (sc272_sound a c hc)

def sc657Part0 : RawPoly ℕ :=
  [(mkRat (-1) 1134, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2]),
   (mkRat (-1) 140, [0, 1, 1, 1, 1, 1, 1, 1, 4]),
   (mkRat (-1) 54, [0, 1, 1, 1, 1, 1, 1, 2, 3]),
   (mkRat (-1) 180, [0, 1, 1, 1, 1, 1, 2, 2, 2]),
   (mkRat (2) 45, [0, 1, 1, 1, 1, 1, 6]),
   (mkRat (1) 24, [0, 1, 1, 1, 2, 2, 4]),
   (mkRat (1) 27, [0, 1, 1, 1, 2, 3, 3]),
   (mkRat (1) 12, [0, 1, 1, 1, 8]),
   (mkRat (1) 36, [0, 1, 1, 2, 2, 2, 3]),
   (mkRat (1) 7, [0, 1, 1, 2, 7]),
   (mkRat (-2) 9, [0, 1, 1, 3, 6]),
   (mkRat (1) 10, [0, 1, 1, 4, 5]),
   (mkRat (-1) 30, [0, 2, 2, 2, 5]),
   (mkRat (-1) 12, [0, 2, 2, 3, 4]),
   (mkRat (-2) 81, [0, 2, 3, 3, 3]),
   (mkRat (-2) 9, [0, 2, 9]),
   (mkRat (-1) 6, [0, 3, 8]),
   (mkRat (-1) 7, [0, 4, 7]),
   (mkRat (4) 15, [0, 5, 6]),
   (mkRat (-1) 17820, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (-1) 270, [1, 1, 1, 1, 1, 1, 1, 1, 3]),
   (mkRat (-1) 140, [1, 1, 1, 1, 1, 1, 1, 2, 2]),
   (mkRat (-1) 45, [1, 1, 1, 1, 1, 1, 5]),
   (mkRat (-1) 30, [1, 1, 1, 1, 1, 2, 4])]

def sc657Part1 : RawPoly ℕ :=
  [(mkRat (-2) 135, [1, 1, 1, 1, 1, 3, 3]),
   (mkRat (1) 144, [1, 1, 1, 2, 2, 2, 2]),
   (mkRat (-2) 9, [1, 1, 1, 2, 6]),
   (mkRat (4) 45, [1, 1, 1, 3, 5]),
   (mkRat (1) 24, [1, 1, 1, 4, 4]),
   (mkRat (1) 10, [1, 1, 2, 2, 5]),
   (mkRat (1) 6, [1, 1, 2, 3, 4]),
   (mkRat (2) 81, [1, 1, 3, 3, 3]),
   (mkRat (2) 9, [1, 1, 9]),
   (mkRat (-1) 72, [2, 2, 2, 2, 3]),
   (mkRat (-1) 7, [2, 2, 7]),
   (mkRat (4) 9, [2, 3, 6]),
   (mkRat (-1) 5, [2, 4, 5]),
   (mkRat (-4) 45, [3, 3, 5]),
   (mkRat (-1) 12, [3, 4, 4]),
   (mkRat (-4) 11, [11])]

def sc657 : RawPoly ℕ :=
  [sc657Part0,
   sc657Part1].flatten

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc657_check :
    reduceTwo (prependC 1 sc272 ++ scaleR (-1) (prependC 0 sc273)) = sc657 := by
  decide +kernel

theorem sc657_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc657 = evRc a c (expWordR [1, 1, 6] (3)) := by
  rw [← sc657_check]
  exact expTwo_step _ _ hc 0 [1, 6] (3)
    sc272 sc273 (sc272_sound a c hc) (sc273_sound a c hc)

def sc658Part0 : RawPoly ℕ :=
  [(mkRat (-1) 170100, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (-1) 1701, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3]),
   (mkRat (-1) 720, [0, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2]),
   (mkRat (-1) 175, [0, 1, 1, 1, 1, 1, 1, 1, 5]),
   (mkRat (-1) 72, [0, 1, 1, 1, 1, 1, 1, 2, 4]),
   (mkRat (-1) 162, [0, 1, 1, 1, 1, 1, 1, 3, 3]),
   (mkRat (-1) 90, [0, 1, 1, 1, 1, 1, 2, 2, 3]),
   (mkRat (-2) 105, [0, 1, 1, 1, 1, 1, 7]),
   (mkRat (1) 30, [0, 1, 1, 1, 2, 2, 5]),
   (mkRat (1) 18, [0, 1, 1, 1, 2, 3, 4]),
   (mkRat (2) 243, [0, 1, 1, 1, 3, 3, 3]),
   (mkRat (2) 27, [0, 1, 1, 1, 9]),
   (mkRat (1) 48, [0, 1, 1, 2, 2, 2, 4]),
   (mkRat (1) 36, [0, 1, 1, 2, 2, 3, 3]),
   (mkRat (1) 8, [0, 1, 1, 2, 8]),
   (mkRat (2) 21, [0, 1, 1, 3, 7]),
   (mkRat (-1) 6, [0, 1, 1, 4, 6]),
   (mkRat (1) 25, [0, 1, 1, 5, 5]),
   (mkRat (-1) 2880, [0, 2, 2, 2, 2, 2, 2]),
   (mkRat (1) 18, [0, 2, 2, 2, 6]),
   (mkRat (-1) 15, [0, 2, 2, 3, 5]),
   (mkRat (-1) 32, [0, 2, 2, 4, 4]),
   (mkRat (-1) 18, [0, 2, 3, 3, 4]),
   (mkRat (-1) 5, [0, 2, 10])]

def sc658Part1 : RawPoly ℕ :=
  [(mkRat (-1) 243, [0, 3, 3, 3, 3]),
   (mkRat (-4) 27, [0, 3, 9]),
   (mkRat (-1) 8, [0, 4, 8]),
   (mkRat (-4) 35, [0, 5, 7]),
   (mkRat (5) 18, [0, 6, 6]),
   (mkRat (-1) 4200, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2]),
   (mkRat (-1) 360, [1, 1, 1, 1, 1, 1, 1, 1, 4]),
   (mkRat (-1) 105, [1, 1, 1, 1, 1, 1, 1, 2, 3]),
   (mkRat (-1) 216, [1, 1, 1, 1, 1, 1, 2, 2, 2]),
   (mkRat (1) 27, [1, 1, 1, 1, 1, 1, 6]),
   (mkRat (-2) 75, [1, 1, 1, 1, 1, 2, 5]),
   (mkRat (-1) 45, [1, 1, 1, 1, 1, 3, 4]),
   (mkRat (1) 54, [1, 1, 1, 2, 2, 2, 3]),
   (mkRat (2) 21, [1, 1, 1, 2, 7]),
   (mkRat (-4) 27, [1, 1, 1, 3, 6]),
   (mkRat (1) 15, [1, 1, 1, 4, 5]),
   (mkRat (1) 480, [1, 1, 2, 2, 2, 2, 2]),
   (mkRat (-1) 6, [1, 1, 2, 2, 6]),
   (mkRat (2) 15, [1, 1, 2, 3, 5]),
   (mkRat (1) 16, [1, 1, 2, 4, 4]),
   (mkRat (1) 18, [1, 1, 3, 3, 4]),
   (mkRat (1) 5, [1, 1, 10]),
   (mkRat (-1) 96, [2, 2, 2, 2, 4]),
   (mkRat (-1) 54, [2, 2, 2, 3, 3])]

def sc658Part2 : RawPoly ℕ :=
  [(mkRat (-1) 8, [2, 2, 8]),
   (mkRat (-4) 21, [2, 3, 7]),
   (mkRat (1) 3, [2, 4, 6]),
   (mkRat (-2) 25, [2, 5, 5]),
   (mkRat (4) 27, [3, 3, 6]),
   (mkRat (-2) 15, [3, 4, 5]),
   (mkRat (-1) 48, [4, 4, 4]),
   (mkRat (-1) 3, [12])]

def sc658 : RawPoly ℕ :=
  [sc658Part0,
   sc658Part1,
   sc658Part2].flatten

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc658_check :
    reduceTwo (prependC 1 sc273 ++ scaleR (-1) (prependC 0 sc274)) = sc658 := by
  decide +kernel

theorem sc658_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc658 = evRc a c (expWordR [1, 1, 6] (4)) := by
  rw [← sc658_check]
  exact expTwo_step _ _ hc 0 [1, 6] (4)
    sc273 sc274 (sc273_sound a c hc) (sc274_sound a c hc)

def sc659Part0 : RawPoly ℕ :=
  [(mkRat (-1) 35640, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2]),
   (mkRat (-1) 2268, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4]),
   (mkRat (-1) 540, [0, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3]),
   (mkRat (-1) 840, [0, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2]),
   (mkRat (1) 105, [0, 1, 1, 1, 1, 1, 1, 1, 6]),
   (mkRat (-1) 90, [0, 1, 1, 1, 1, 1, 1, 2, 5]),
   (mkRat (-1) 108, [0, 1, 1, 1, 1, 1, 1, 3, 4]),
   (mkRat (-1) 120, [0, 1, 1, 1, 1, 1, 2, 2, 4]),
   (mkRat (-1) 135, [0, 1, 1, 1, 1, 1, 2, 3, 3]),
   (mkRat (-1) 60, [0, 1, 1, 1, 1, 1, 8]),
   (mkRat (1) 1440, [0, 1, 1, 1, 2, 2, 2, 2, 2]),
   (mkRat (-1) 18, [0, 1, 1, 1, 2, 2, 6]),
   (mkRat (2) 45, [0, 1, 1, 1, 2, 3, 5]),
   (mkRat (1) 48, [0, 1, 1, 1, 2, 4, 4]),
   (mkRat (1) 54, [0, 1, 1, 1, 3, 3, 4]),
   (mkRat (1) 15, [0, 1, 1, 1, 10]),
   (mkRat (1) 60, [0, 1, 1, 2, 2, 2, 5]),
   (mkRat (1) 24, [0, 1, 1, 2, 2, 3, 4]),
   (mkRat (1) 81, [0, 1, 1, 2, 3, 3, 3]),
   (mkRat (1) 9, [0, 1, 1, 2, 9]),
   (mkRat (1) 12, [0, 1, 1, 3, 8]),
   (mkRat (1) 14, [0, 1, 1, 4, 7]),
   (mkRat (-2) 15, [0, 1, 1, 5, 6]),
   (mkRat (-1) 720, [0, 2, 2, 2, 2, 2, 3])]

def sc659Part1 : RawPoly ℕ :=
  [(mkRat (-1) 42, [0, 2, 2, 2, 7]),
   (mkRat (1) 9, [0, 2, 2, 3, 6]),
   (mkRat (-1) 20, [0, 2, 2, 4, 5]),
   (mkRat (-2) 45, [0, 2, 3, 3, 5]),
   (mkRat (-1) 24, [0, 2, 3, 4, 4]),
   (mkRat (-2) 11, [0, 2, 11]),
   (mkRat (-1) 81, [0, 3, 3, 3, 4]),
   (mkRat (-2) 15, [0, 3, 10]),
   (mkRat (-1) 9, [0, 4, 9]),
   (mkRat (-1) 10, [0, 5, 8]),
   (mkRat (4) 21, [0, 6, 7]),
   (mkRat (-1) 900900, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (-1) 6300, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3]),
   (mkRat (-1) 2268, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2]),
   (mkRat (-1) 450, [1, 1, 1, 1, 1, 1, 1, 1, 5]),
   (mkRat (-1) 140, [1, 1, 1, 1, 1, 1, 1, 2, 4]),
   (mkRat (-1) 315, [1, 1, 1, 1, 1, 1, 1, 3, 3]),
   (mkRat (-1) 108, [1, 1, 1, 1, 1, 1, 2, 2, 3]),
   (mkRat (-1) 63, [1, 1, 1, 1, 1, 1, 7]),
   (mkRat (-1) 720, [1, 1, 1, 1, 1, 2, 2, 2, 2]),
   (mkRat (2) 45, [1, 1, 1, 1, 1, 2, 6]),
   (mkRat (-4) 225, [1, 1, 1, 1, 1, 3, 5]),
   (mkRat (-1) 120, [1, 1, 1, 1, 1, 4, 4]),
   (mkRat (1) 72, [1, 1, 1, 2, 2, 2, 4])]

def sc659Part2 : RawPoly ℕ :=
  [(mkRat (1) 54, [1, 1, 1, 2, 2, 3, 3]),
   (mkRat (1) 12, [1, 1, 1, 2, 8]),
   (mkRat (4) 63, [1, 1, 1, 3, 7]),
   (mkRat (-1) 9, [1, 1, 1, 4, 6]),
   (mkRat (2) 75, [1, 1, 1, 5, 5]),
   (mkRat (1) 144, [1, 1, 2, 2, 2, 2, 3]),
   (mkRat (1) 14, [1, 1, 2, 2, 7]),
   (mkRat (-2) 9, [1, 1, 2, 3, 6]),
   (mkRat (1) 10, [1, 1, 2, 4, 5]),
   (mkRat (2) 45, [1, 1, 3, 3, 5]),
   (mkRat (1) 24, [1, 1, 3, 4, 4]),
   (mkRat (2) 11, [1, 1, 11]),
   (mkRat (-1) 120, [2, 2, 2, 2, 5]),
   (mkRat (-1) 36, [2, 2, 2, 3, 4]),
   (mkRat (-1) 81, [2, 2, 3, 3, 3]),
   (mkRat (-1) 9, [2, 2, 9]),
   (mkRat (-1) 6, [2, 3, 8]),
   (mkRat (-1) 7, [2, 4, 7]),
   (mkRat (4) 15, [2, 5, 6]),
   (mkRat (-4) 63, [3, 3, 7]),
   (mkRat (2) 9, [3, 4, 6]),
   (mkRat (-4) 75, [3, 5, 5]),
   (mkRat (-1) 20, [4, 4, 5]),
   (mkRat (-4) 13, [13])]

def sc659 : RawPoly ℕ :=
  [sc659Part0,
   sc659Part1,
   sc659Part2].flatten

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc659_check :
    reduceTwo (prependC 1 sc274 ++ scaleR (-1) (prependC 0 sc275)) = sc659 := by
  decide +kernel

theorem sc659_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc659 = evRc a c (expWordR [1, 1, 6] (5)) := by
  rw [← sc659_check]
  exact expTwo_step _ _ hc 0 [1, 6] (5)
    sc274 sc275 (sc274_sound a c hc) (sc275_sound a c hc)

def sc660Part0 : RawPoly ℕ :=
  [(mkRat (-1) 10478160, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (-1) 53460, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3]),
   (mkRat (-1) 16800, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2]),
   (mkRat (-1) 2835, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5]),
   (mkRat (-1) 720, [0, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4]),
   (mkRat (-1) 1620, [0, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3]),
   (mkRat (-1) 420, [0, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3]),
   (mkRat (-1) 245, [0, 1, 1, 1, 1, 1, 1, 1, 7]),
   (mkRat (-1) 1728, [0, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2]),
   (mkRat (1) 54, [0, 1, 1, 1, 1, 1, 1, 2, 6]),
   (mkRat (-1) 135, [0, 1, 1, 1, 1, 1, 1, 3, 5]),
   (mkRat (-1) 288, [0, 1, 1, 1, 1, 1, 1, 4, 4]),
   (mkRat (-1) 150, [0, 1, 1, 1, 1, 1, 2, 2, 5]),
   (mkRat (-1) 90, [0, 1, 1, 1, 1, 1, 2, 3, 4]),
   (mkRat (-2) 1215, [0, 1, 1, 1, 1, 1, 3, 3, 3]),
   (mkRat (-2) 135, [0, 1, 1, 1, 1, 1, 9]),
   (mkRat (1) 432, [0, 1, 1, 1, 2, 2, 2, 2, 3]),
   (mkRat (1) 42, [0, 1, 1, 1, 2, 2, 7]),
   (mkRat (-2) 27, [0, 1, 1, 1, 2, 3, 6]),
   (mkRat (1) 30, [0, 1, 1, 1, 2, 4, 5]),
   (mkRat (2) 135, [0, 1, 1, 1, 3, 3, 5]),
   (mkRat (1) 72, [0, 1, 1, 1, 3, 4, 4]),
   (mkRat (2) 33, [0, 1, 1, 1, 11]),
   (mkRat (1) 5760, [0, 1, 1, 2, 2, 2, 2, 2, 2])]

def sc660Part1 : RawPoly ℕ :=
  [(mkRat (-1) 36, [0, 1, 1, 2, 2, 2, 6]),
   (mkRat (1) 30, [0, 1, 1, 2, 2, 3, 5]),
   (mkRat (1) 64, [0, 1, 1, 2, 2, 4, 4]),
   (mkRat (1) 36, [0, 1, 1, 2, 3, 3, 4]),
   (mkRat (1) 10, [0, 1, 1, 2, 10]),
   (mkRat (1) 486, [0, 1, 1, 3, 3, 3, 3]),
   (mkRat (2) 27, [0, 1, 1, 3, 9]),
   (mkRat (1) 16, [0, 1, 1, 4, 8]),
   (mkRat (2) 35, [0, 1, 1, 5, 7]),
   (mkRat (-5) 36, [0, 1, 1, 6, 6]),
   (mkRat (-1) 960, [0, 2, 2, 2, 2, 2, 4]),
   (mkRat (-1) 432, [0, 2, 2, 2, 2, 3, 3]),
   (mkRat (-1) 48, [0, 2, 2, 2, 8]),
   (mkRat (-1) 21, [0, 2, 2, 3, 7]),
   (mkRat (1) 12, [0, 2, 2, 4, 6]),
   (mkRat (-1) 50, [0, 2, 2, 5, 5]),
   (mkRat (2) 27, [0, 2, 3, 3, 6]),
   (mkRat (-1) 15, [0, 2, 3, 4, 5]),
   (mkRat (-1) 96, [0, 2, 4, 4, 4]),
   (mkRat (-1) 6, [0, 2, 12]),
   (mkRat (-4) 405, [0, 3, 3, 3, 5]),
   (mkRat (-1) 72, [0, 3, 3, 4, 4]),
   (mkRat (-4) 33, [0, 3, 11]),
   (mkRat (-1) 10, [0, 4, 10])]

def sc660Part2 : RawPoly ℕ :=
  [(mkRat (-4) 45, [0, 5, 9]),
   (mkRat (1) 6, [0, 6, 8]),
   (mkRat (-2) 49, [0, 7, 7]),
   (mkRat (-1) 170100, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2]),
   (mkRat (-1) 8400, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4]),
   (mkRat (-1) 1701, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3]),
   (mkRat (-1) 2160, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2]),
   (mkRat (1) 270, [1, 1, 1, 1, 1, 1, 1, 1, 6]),
   (mkRat (-1) 175, [1, 1, 1, 1, 1, 1, 1, 2, 5]),
   (mkRat (-1) 210, [1, 1, 1, 1, 1, 1, 1, 3, 4]),
   (mkRat (-1) 144, [1, 1, 1, 1, 1, 1, 2, 2, 4]),
   (mkRat (-1) 162, [1, 1, 1, 1, 1, 1, 2, 3, 3]),
   (mkRat (-1) 72, [1, 1, 1, 1, 1, 1, 8]),
   (mkRat (-1) 270, [1, 1, 1, 1, 1, 2, 2, 2, 3]),
   (mkRat (-2) 105, [1, 1, 1, 1, 1, 2, 7]),
   (mkRat (4) 135, [1, 1, 1, 1, 1, 3, 6]),
   (mkRat (-1) 75, [1, 1, 1, 1, 1, 4, 5]),
   (mkRat (1) 90, [1, 1, 1, 2, 2, 2, 5]),
   (mkRat (1) 36, [1, 1, 1, 2, 2, 3, 4]),
   (mkRat (2) 243, [1, 1, 1, 2, 3, 3, 3]),
   (mkRat (2) 27, [1, 1, 1, 2, 9]),
   (mkRat (1) 18, [1, 1, 1, 3, 8]),
   (mkRat (1) 21, [1, 1, 1, 4, 7]),
   (mkRat (-4) 45, [1, 1, 1, 5, 6])]

def sc660Part3 : RawPoly ℕ :=
  [(mkRat (1) 192, [1, 1, 2, 2, 2, 2, 4]),
   (mkRat (1) 108, [1, 1, 2, 2, 2, 3, 3]),
   (mkRat (1) 16, [1, 1, 2, 2, 8]),
   (mkRat (2) 21, [1, 1, 2, 3, 7]),
   (mkRat (-1) 6, [1, 1, 2, 4, 6]),
   (mkRat (1) 25, [1, 1, 2, 5, 5]),
   (mkRat (-2) 27, [1, 1, 3, 3, 6]),
   (mkRat (1) 15, [1, 1, 3, 4, 5]),
   (mkRat (1) 96, [1, 1, 4, 4, 4]),
   (mkRat (1) 6, [1, 1, 12]),
   (mkRat (-1) 20160, [2, 2, 2, 2, 2, 2, 2]),
   (mkRat (1) 72, [2, 2, 2, 2, 6]),
   (mkRat (-1) 45, [2, 2, 2, 3, 5]),
   (mkRat (-1) 96, [2, 2, 2, 4, 4]),
   (mkRat (-1) 36, [2, 2, 3, 3, 4]),
   (mkRat (-1) 10, [2, 2, 10]),
   (mkRat (-1) 243, [2, 3, 3, 3, 3]),
   (mkRat (-4) 27, [2, 3, 9]),
   (mkRat (-1) 8, [2, 4, 8]),
   (mkRat (-4) 35, [2, 5, 7]),
   (mkRat (5) 18, [2, 6, 6]),
   (mkRat (-1) 18, [3, 3, 8]),
   (mkRat (-2) 21, [3, 4, 7]),
   (mkRat (8) 45, [3, 5, 6])]

def sc660Part4 : RawPoly ℕ :=
  [(mkRat (1) 12, [4, 4, 6]),
   (mkRat (-1) 25, [4, 5, 5]),
   (mkRat (-2) 7, [14])]

def sc660 : RawPoly ℕ :=
  [sc660Part0,
   sc660Part1,
   sc660Part2,
   sc660Part3,
   sc660Part4].flatten

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc660_check :
    reduceTwo (prependC 1 sc275 ++ scaleR (-1) (prependC 0 sc276)) = sc660 := by
  decide +kernel

theorem sc660_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc660 = evRc a c (expWordR [1, 1, 6] (6)) := by
  rw [← sc660_check]
  exact expTwo_step _ _ hc 0 [1, 6] (6)
    sc275 sc276 (sc275_sound a c hc) (sc276_sound a c hc)

def sc661Part0 : RawPoly ℕ :=
  [(mkRat (-1) 1801800, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2]),
   (mkRat (-1) 71280, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4]),
   (mkRat (-1) 12600, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3]),
   (mkRat (-1) 13608, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2]),
   (mkRat (1) 1701, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6]),
   (mkRat (-1) 900, [0, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5]),
   (mkRat (-1) 1080, [0, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4]),
   (mkRat (-1) 560, [0, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4]),
   (mkRat (-1) 630, [0, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3]),
   (mkRat (-1) 280, [0, 1, 1, 1, 1, 1, 1, 1, 8]),
   (mkRat (-1) 648, [0, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3]),
   (mkRat (-1) 126, [0, 1, 1, 1, 1, 1, 1, 2, 7]),
   (mkRat (1) 81, [0, 1, 1, 1, 1, 1, 1, 3, 6]),
   (mkRat (-1) 180, [0, 1, 1, 1, 1, 1, 1, 4, 5]),
   (mkRat (-1) 7200, [0, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2]),
   (mkRat (1) 90, [0, 1, 1, 1, 1, 1, 2, 2, 6]),
   (mkRat (-2) 225, [0, 1, 1, 1, 1, 1, 2, 3, 5]),
   (mkRat (-1) 240, [0, 1, 1, 1, 1, 1, 2, 4, 4]),
   (mkRat (-1) 270, [0, 1, 1, 1, 1, 1, 3, 3, 4]),
   (mkRat (-1) 75, [0, 1, 1, 1, 1, 1, 10]),
   (mkRat (1) 576, [0, 1, 1, 1, 2, 2, 2, 2, 4]),
   (mkRat (1) 324, [0, 1, 1, 1, 2, 2, 2, 3, 3]),
   (mkRat (1) 48, [0, 1, 1, 1, 2, 2, 8]),
   (mkRat (2) 63, [0, 1, 1, 1, 2, 3, 7])]

def sc661Part1 : RawPoly ℕ :=
  [(mkRat (-1) 18, [0, 1, 1, 1, 2, 4, 6]),
   (mkRat (1) 75, [0, 1, 1, 1, 2, 5, 5]),
   (mkRat (-2) 81, [0, 1, 1, 1, 3, 3, 6]),
   (mkRat (1) 45, [0, 1, 1, 1, 3, 4, 5]),
   (mkRat (1) 288, [0, 1, 1, 1, 4, 4, 4]),
   (mkRat (1) 18, [0, 1, 1, 1, 12]),
   (mkRat (1) 1440, [0, 1, 1, 2, 2, 2, 2, 2, 3]),
   (mkRat (1) 84, [0, 1, 1, 2, 2, 2, 7]),
   (mkRat (-1) 18, [0, 1, 1, 2, 2, 3, 6]),
   (mkRat (1) 40, [0, 1, 1, 2, 2, 4, 5]),
   (mkRat (1) 45, [0, 1, 1, 2, 3, 3, 5]),
   (mkRat (1) 48, [0, 1, 1, 2, 3, 4, 4]),
   (mkRat (1) 11, [0, 1, 1, 2, 11]),
   (mkRat (1) 162, [0, 1, 1, 3, 3, 3, 4]),
   (mkRat (1) 15, [0, 1, 1, 3, 10]),
   (mkRat (1) 18, [0, 1, 1, 4, 9]),
   (mkRat (1) 20, [0, 1, 1, 5, 8]),
   (mkRat (-2) 21, [0, 1, 1, 6, 7]),
   (mkRat (-1) 1200, [0, 2, 2, 2, 2, 2, 5]),
   (mkRat (-1) 288, [0, 2, 2, 2, 2, 3, 4]),
   (mkRat (-1) 486, [0, 2, 2, 2, 3, 3, 3]),
   (mkRat (-1) 54, [0, 2, 2, 2, 9]),
   (mkRat (-1) 24, [0, 2, 2, 3, 8]),
   (mkRat (-1) 28, [0, 2, 2, 4, 7])]

def sc661Part2 : RawPoly ℕ :=
  [(mkRat (1) 15, [0, 2, 2, 5, 6]),
   (mkRat (-2) 63, [0, 2, 3, 3, 7]),
   (mkRat (1) 9, [0, 2, 3, 4, 6]),
   (mkRat (-2) 75, [0, 2, 3, 5, 5]),
   (mkRat (-1) 40, [0, 2, 4, 4, 5]),
   (mkRat (-2) 13, [0, 2, 13]),
   (mkRat (4) 243, [0, 3, 3, 3, 6]),
   (mkRat (-1) 45, [0, 3, 3, 4, 5]),
   (mkRat (-1) 144, [0, 3, 4, 4, 4]),
   (mkRat (-1) 9, [0, 3, 12]),
   (mkRat (-1) 11, [0, 4, 11]),
   (mkRat (-2) 25, [0, 5, 10]),
   (mkRat (4) 27, [0, 6, 9]),
   (mkRat (-1) 14, [0, 7, 8]),
   (mkRat (-1) 66339000, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (-1) 255150, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3]),
   (mkRat (-1) 71280, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2]),
   (mkRat (-1) 10500, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5]),
   (mkRat (-1) 2268, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4]),
   (mkRat (-1) 5103, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3]),
   (mkRat (-1) 1080, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3]),
   (mkRat (-1) 630, [1, 1, 1, 1, 1, 1, 1, 1, 7]),
   (mkRat (-1) 3360, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2]),
   (mkRat (1) 105, [1, 1, 1, 1, 1, 1, 1, 2, 6])]

def sc661Part3 : RawPoly ℕ :=
  [(mkRat (-2) 525, [1, 1, 1, 1, 1, 1, 1, 3, 5]),
   (mkRat (-1) 560, [1, 1, 1, 1, 1, 1, 1, 4, 4]),
   (mkRat (-1) 180, [1, 1, 1, 1, 1, 1, 2, 2, 5]),
   (mkRat (-1) 108, [1, 1, 1, 1, 1, 1, 2, 3, 4]),
   (mkRat (-1) 729, [1, 1, 1, 1, 1, 1, 3, 3, 3]),
   (mkRat (-1) 81, [1, 1, 1, 1, 1, 1, 9]),
   (mkRat (-1) 360, [1, 1, 1, 1, 1, 2, 2, 2, 4]),
   (mkRat (-1) 270, [1, 1, 1, 1, 1, 2, 2, 3, 3]),
   (mkRat (-1) 60, [1, 1, 1, 1, 1, 2, 8]),
   (mkRat (-4) 315, [1, 1, 1, 1, 1, 3, 7]),
   (mkRat (1) 45, [1, 1, 1, 1, 1, 4, 6]),
   (mkRat (-2) 375, [1, 1, 1, 1, 1, 5, 5]),
   (mkRat (1) 8640, [1, 1, 1, 2, 2, 2, 2, 2, 2]),
   (mkRat (-1) 54, [1, 1, 1, 2, 2, 2, 6]),
   (mkRat (1) 45, [1, 1, 1, 2, 2, 3, 5]),
   (mkRat (1) 96, [1, 1, 1, 2, 2, 4, 4]),
   (mkRat (1) 54, [1, 1, 1, 2, 3, 3, 4]),
   (mkRat (1) 15, [1, 1, 1, 2, 10]),
   (mkRat (1) 729, [1, 1, 1, 3, 3, 3, 3]),
   (mkRat (4) 81, [1, 1, 1, 3, 9]),
   (mkRat (1) 24, [1, 1, 1, 4, 8]),
   (mkRat (4) 105, [1, 1, 1, 5, 7]),
   (mkRat (-5) 54, [1, 1, 1, 6, 6]),
   (mkRat (1) 240, [1, 1, 2, 2, 2, 2, 5])]

def sc661Part4 : RawPoly ℕ :=
  [(mkRat (1) 72, [1, 1, 2, 2, 2, 3, 4]),
   (mkRat (1) 162, [1, 1, 2, 2, 3, 3, 3]),
   (mkRat (1) 18, [1, 1, 2, 2, 9]),
   (mkRat (1) 12, [1, 1, 2, 3, 8]),
   (mkRat (1) 14, [1, 1, 2, 4, 7]),
   (mkRat (-2) 15, [1, 1, 2, 5, 6]),
   (mkRat (2) 63, [1, 1, 3, 3, 7]),
   (mkRat (-1) 9, [1, 1, 3, 4, 6]),
   (mkRat (2) 75, [1, 1, 3, 5, 5]),
   (mkRat (1) 40, [1, 1, 4, 4, 5]),
   (mkRat (2) 13, [1, 1, 13]),
   (mkRat (-1) 4320, [2, 2, 2, 2, 2, 2, 3]),
   (mkRat (-1) 168, [2, 2, 2, 2, 7]),
   (mkRat (1) 27, [2, 2, 2, 3, 6]),
   (mkRat (-1) 60, [2, 2, 2, 4, 5]),
   (mkRat (-1) 45, [2, 2, 3, 3, 5]),
   (mkRat (-1) 48, [2, 2, 3, 4, 4]),
   (mkRat (-1) 11, [2, 2, 11]),
   (mkRat (-1) 81, [2, 3, 3, 3, 4]),
   (mkRat (-2) 15, [2, 3, 10]),
   (mkRat (-1) 9, [2, 4, 9]),
   (mkRat (-1) 10, [2, 5, 8]),
   (mkRat (4) 21, [2, 6, 7]),
   (mkRat (-2) 3645, [3, 3, 3, 3, 3])]

def sc661Part5 : RawPoly ℕ :=
  [(mkRat (-4) 81, [3, 3, 9]),
   (mkRat (-1) 12, [3, 4, 8]),
   (mkRat (-8) 105, [3, 5, 7]),
   (mkRat (5) 27, [3, 6, 6]),
   (mkRat (-1) 28, [4, 4, 7]),
   (mkRat (2) 15, [4, 5, 6]),
   (mkRat (-4) 375, [5, 5, 5]),
   (mkRat (-4) 15, [15])]

def sc661 : RawPoly ℕ :=
  [sc661Part0,
   sc661Part1,
   sc661Part2,
   sc661Part3,
   sc661Part4,
   sc661Part5].flatten

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc661_check :
    reduceTwo (prependC 1 sc276 ++ scaleR (-1) (prependC 0 sc277)) = sc661 := by
  decide +kernel

theorem sc661_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc661 = evRc a c (expWordR [1, 1, 6] (7)) := by
  rw [← sc661_check]
  exact expTwo_step _ _ hc 0 [1, 6] (7)
    sc276 sc277 (sc276_sound a c hc) (sc277_sound a c hc)

def sc662Part0 : RawPoly ℕ :=
  [(mkRat (-1) 908107200, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (-1) 2702700, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3]),
   (mkRat (-1) 680400, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2]),
   (mkRat (-1) 89100, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5]),
   (mkRat (-1) 16800, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4]),
   (mkRat (-1) 37800, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3]),
   (mkRat (-1) 6804, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3]),
   (mkRat (-1) 3969, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7]),
   (mkRat (-1) 17280, [0, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2]),
   (mkRat (1) 540, [0, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6]),
   (mkRat (-1) 1350, [0, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5]),
   (mkRat (-1) 2880, [0, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4]),
   (mkRat (-1) 700, [0, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5]),
   (mkRat (-1) 420, [0, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4]),
   (mkRat (-1) 2835, [0, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3]),
   (mkRat (-1) 315, [0, 1, 1, 1, 1, 1, 1, 1, 9]),
   (mkRat (-1) 864, [0, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4]),
   (mkRat (-1) 648, [0, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3]),
   (mkRat (-1) 144, [0, 1, 1, 1, 1, 1, 1, 2, 8]),
   (mkRat (-1) 189, [0, 1, 1, 1, 1, 1, 1, 3, 7]),
   (mkRat (1) 108, [0, 1, 1, 1, 1, 1, 1, 4, 6]),
   (mkRat (-1) 450, [0, 1, 1, 1, 1, 1, 1, 5, 5]),
   (mkRat (-1) 2160, [0, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3]),
   (mkRat (-1) 210, [0, 1, 1, 1, 1, 1, 2, 2, 7])]

def sc662Part1 : RawPoly ℕ :=
  [(mkRat (2) 135, [0, 1, 1, 1, 1, 1, 2, 3, 6]),
   (mkRat (-1) 150, [0, 1, 1, 1, 1, 1, 2, 4, 5]),
   (mkRat (-2) 675, [0, 1, 1, 1, 1, 1, 3, 3, 5]),
   (mkRat (-1) 360, [0, 1, 1, 1, 1, 1, 3, 4, 4]),
   (mkRat (-2) 165, [0, 1, 1, 1, 1, 1, 11]),
   (mkRat (1) 720, [0, 1, 1, 1, 2, 2, 2, 2, 5]),
   (mkRat (1) 216, [0, 1, 1, 1, 2, 2, 2, 3, 4]),
   (mkRat (1) 486, [0, 1, 1, 1, 2, 2, 3, 3, 3]),
   (mkRat (1) 54, [0, 1, 1, 1, 2, 2, 9]),
   (mkRat (1) 36, [0, 1, 1, 1, 2, 3, 8]),
   (mkRat (1) 42, [0, 1, 1, 1, 2, 4, 7]),
   (mkRat (-2) 45, [0, 1, 1, 1, 2, 5, 6]),
   (mkRat (2) 189, [0, 1, 1, 1, 3, 3, 7]),
   (mkRat (-1) 27, [0, 1, 1, 1, 3, 4, 6]),
   (mkRat (2) 225, [0, 1, 1, 1, 3, 5, 5]),
   (mkRat (1) 120, [0, 1, 1, 1, 4, 4, 5]),
   (mkRat (2) 39, [0, 1, 1, 1, 13]),
   (mkRat (1) 1920, [0, 1, 1, 2, 2, 2, 2, 2, 4]),
   (mkRat (1) 864, [0, 1, 1, 2, 2, 2, 2, 3, 3]),
   (mkRat (1) 96, [0, 1, 1, 2, 2, 2, 8]),
   (mkRat (1) 42, [0, 1, 1, 2, 2, 3, 7]),
   (mkRat (-1) 24, [0, 1, 1, 2, 2, 4, 6]),
   (mkRat (1) 100, [0, 1, 1, 2, 2, 5, 5]),
   (mkRat (-1) 27, [0, 1, 1, 2, 3, 3, 6])]

def sc662Part2 : RawPoly ℕ :=
  [(mkRat (1) 30, [0, 1, 1, 2, 3, 4, 5]),
   (mkRat (1) 192, [0, 1, 1, 2, 4, 4, 4]),
   (mkRat (1) 12, [0, 1, 1, 2, 12]),
   (mkRat (2) 405, [0, 1, 1, 3, 3, 3, 5]),
   (mkRat (1) 144, [0, 1, 1, 3, 3, 4, 4]),
   (mkRat (2) 33, [0, 1, 1, 3, 11]),
   (mkRat (1) 20, [0, 1, 1, 4, 10]),
   (mkRat (2) 45, [0, 1, 1, 5, 9]),
   (mkRat (-1) 12, [0, 1, 1, 6, 8]),
   (mkRat (1) 49, [0, 1, 1, 7, 7]),
   (mkRat (-1) 322560, [0, 2, 2, 2, 2, 2, 2, 2, 2]),
   (mkRat (1) 720, [0, 2, 2, 2, 2, 2, 6]),
   (mkRat (-1) 360, [0, 2, 2, 2, 2, 3, 5]),
   (mkRat (-1) 768, [0, 2, 2, 2, 2, 4, 4]),
   (mkRat (-1) 216, [0, 2, 2, 2, 3, 3, 4]),
   (mkRat (-1) 60, [0, 2, 2, 2, 10]),
   (mkRat (-1) 972, [0, 2, 2, 3, 3, 3, 3]),
   (mkRat (-1) 27, [0, 2, 2, 3, 9]),
   (mkRat (-1) 32, [0, 2, 2, 4, 8]),
   (mkRat (-1) 35, [0, 2, 2, 5, 7]),
   (mkRat (5) 72, [0, 2, 2, 6, 6]),
   (mkRat (-1) 36, [0, 2, 3, 3, 8]),
   (mkRat (-1) 21, [0, 2, 3, 4, 7]),
   (mkRat (4) 45, [0, 2, 3, 5, 6])]

def sc662Part3 : RawPoly ℕ :=
  [(mkRat (1) 24, [0, 2, 4, 4, 6]),
   (mkRat (-1) 50, [0, 2, 4, 5, 5]),
   (mkRat (-1) 7, [0, 2, 14]),
   (mkRat (-4) 567, [0, 3, 3, 3, 7]),
   (mkRat (1) 27, [0, 3, 3, 4, 6]),
   (mkRat (-2) 225, [0, 3, 3, 5, 5]),
   (mkRat (-1) 60, [0, 3, 4, 4, 5]),
   (mkRat (-4) 39, [0, 3, 13]),
   (mkRat (-1) 768, [0, 4, 4, 4, 4]),
   (mkRat (-1) 12, [0, 4, 12]),
   (mkRat (-4) 55, [0, 5, 11]),
   (mkRat (2) 15, [0, 6, 10]),
   (mkRat (-4) 63, [0, 7, 9]),
   (mkRat (-1) 32, [0, 8, 8]),
   (mkRat (-1) 10478160, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2]),
   (mkRat (-1) 340200, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4]),
   (mkRat (-1) 53460, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3]),
   (mkRat (-1) 50400, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2]),
   (mkRat (1) 6300, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6]),
   (mkRat (-1) 2835, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5]),
   (mkRat (-1) 3402, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4]),
   (mkRat (-1) 1440, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4]),
   (mkRat (-1) 1620, [1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3]),
   (mkRat (-1) 720, [1, 1, 1, 1, 1, 1, 1, 1, 8])]

def sc662Part4 : RawPoly ℕ :=
  [(mkRat (-1) 1260, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3]),
   (mkRat (-1) 245, [1, 1, 1, 1, 1, 1, 1, 2, 7]),
   (mkRat (2) 315, [1, 1, 1, 1, 1, 1, 1, 3, 6]),
   (mkRat (-1) 350, [1, 1, 1, 1, 1, 1, 1, 4, 5]),
   (mkRat (-1) 8640, [1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2]),
   (mkRat (1) 108, [1, 1, 1, 1, 1, 1, 2, 2, 6]),
   (mkRat (-1) 135, [1, 1, 1, 1, 1, 1, 2, 3, 5]),
   (mkRat (-1) 288, [1, 1, 1, 1, 1, 1, 2, 4, 4]),
   (mkRat (-1) 324, [1, 1, 1, 1, 1, 1, 3, 3, 4]),
   (mkRat (-1) 90, [1, 1, 1, 1, 1, 1, 10]),
   (mkRat (-1) 450, [1, 1, 1, 1, 1, 2, 2, 2, 5]),
   (mkRat (-1) 180, [1, 1, 1, 1, 1, 2, 2, 3, 4]),
   (mkRat (-2) 1215, [1, 1, 1, 1, 1, 2, 3, 3, 3]),
   (mkRat (-2) 135, [1, 1, 1, 1, 1, 2, 9]),
   (mkRat (-1) 90, [1, 1, 1, 1, 1, 3, 8]),
   (mkRat (-1) 105, [1, 1, 1, 1, 1, 4, 7]),
   (mkRat (4) 225, [1, 1, 1, 1, 1, 5, 6]),
   (mkRat (1) 2160, [1, 1, 1, 2, 2, 2, 2, 2, 3]),
   (mkRat (1) 126, [1, 1, 1, 2, 2, 2, 7]),
   (mkRat (-1) 27, [1, 1, 1, 2, 2, 3, 6]),
   (mkRat (1) 60, [1, 1, 1, 2, 2, 4, 5]),
   (mkRat (2) 135, [1, 1, 1, 2, 3, 3, 5]),
   (mkRat (1) 72, [1, 1, 1, 2, 3, 4, 4]),
   (mkRat (2) 33, [1, 1, 1, 2, 11])]

def sc662Part5 : RawPoly ℕ :=
  [(mkRat (1) 243, [1, 1, 1, 3, 3, 3, 4]),
   (mkRat (2) 45, [1, 1, 1, 3, 10]),
   (mkRat (1) 27, [1, 1, 1, 4, 9]),
   (mkRat (1) 30, [1, 1, 1, 5, 8]),
   (mkRat (-4) 63, [1, 1, 1, 6, 7]),
   (mkRat (1) 40320, [1, 1, 2, 2, 2, 2, 2, 2, 2]),
   (mkRat (-1) 144, [1, 1, 2, 2, 2, 2, 6]),
   (mkRat (1) 90, [1, 1, 2, 2, 2, 3, 5]),
   (mkRat (1) 192, [1, 1, 2, 2, 2, 4, 4]),
   (mkRat (1) 72, [1, 1, 2, 2, 3, 3, 4]),
   (mkRat (1) 20, [1, 1, 2, 2, 10]),
   (mkRat (1) 486, [1, 1, 2, 3, 3, 3, 3]),
   (mkRat (2) 27, [1, 1, 2, 3, 9]),
   (mkRat (1) 16, [1, 1, 2, 4, 8]),
   (mkRat (2) 35, [1, 1, 2, 5, 7]),
   (mkRat (-5) 36, [1, 1, 2, 6, 6]),
   (mkRat (1) 36, [1, 1, 3, 3, 8]),
   (mkRat (1) 21, [1, 1, 3, 4, 7]),
   (mkRat (-4) 45, [1, 1, 3, 5, 6]),
   (mkRat (-1) 24, [1, 1, 4, 4, 6]),
   (mkRat (1) 50, [1, 1, 4, 5, 5]),
   (mkRat (1) 7, [1, 1, 14]),
   (mkRat (-1) 5760, [2, 2, 2, 2, 2, 2, 4]),
   (mkRat (-1) 2160, [2, 2, 2, 2, 2, 3, 3])]

def sc662Part6 : RawPoly ℕ :=
  [(mkRat (-1) 192, [2, 2, 2, 2, 8]),
   (mkRat (-1) 63, [2, 2, 2, 3, 7]),
   (mkRat (1) 36, [2, 2, 2, 4, 6]),
   (mkRat (-1) 150, [2, 2, 2, 5, 5]),
   (mkRat (1) 27, [2, 2, 3, 3, 6]),
   (mkRat (-1) 30, [2, 2, 3, 4, 5]),
   (mkRat (-1) 192, [2, 2, 4, 4, 4]),
   (mkRat (-1) 12, [2, 2, 12]),
   (mkRat (-4) 405, [2, 3, 3, 3, 5]),
   (mkRat (-1) 72, [2, 3, 3, 4, 4]),
   (mkRat (-4) 33, [2, 3, 11]),
   (mkRat (-1) 10, [2, 4, 10]),
   (mkRat (-4) 45, [2, 5, 9]),
   (mkRat (1) 6, [2, 6, 8]),
   (mkRat (-2) 49, [2, 7, 7]),
   (mkRat (-1) 486, [3, 3, 3, 3, 4]),
   (mkRat (-2) 45, [3, 3, 10]),
   (mkRat (-2) 27, [3, 4, 9]),
   (mkRat (-1) 15, [3, 5, 8]),
   (mkRat (8) 63, [3, 6, 7]),
   (mkRat (-1) 32, [4, 4, 8]),
   (mkRat (-2) 35, [4, 5, 7]),
   (mkRat (5) 36, [4, 6, 6]),
   (mkRat (4) 75, [5, 5, 6])]

def sc662Part7 : RawPoly ℕ :=
  [(mkRat (-1) 4, [16])]

def sc662 : RawPoly ℕ :=
  [sc662Part0,
   sc662Part1,
   sc662Part2,
   sc662Part3,
   sc662Part4,
   sc662Part5,
   sc662Part6,
   sc662Part7].flatten

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc662_check :
    reduceTwo (prependC 1 sc277 ++ scaleR (-1) (prependC 0 sc278)) = sc662 := by
  decide +kernel

theorem sc662_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc662 = evRc a c (expWordR [1, 1, 6] (8)) := by
  rw [← sc662_check]
  exact expTwo_step _ _ hc 0 [1, 6] (8)
    sc277 sc278 (sc277_sound a c hc) (sc278_sound a c hc)

def sc663 : RawPoly ℕ :=
  [(mkRat (-1) 2, [0, 2, 2]),
   (1, [1, 1, 2]),
   (-1, [4])]

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc663_check :
    reduceTwo (prependC 1 sc279 ++ scaleR (-1) (prependC 0 sc280)) = sc663 := by
  decide +kernel

theorem sc663_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc663 = evRc a c (expWordR [1, 1, 7] (-5)) := by
  rw [← sc663_check]
  exact expTwo_step _ _ hc 0 [1, 7] (-5)
    sc279 sc280 (sc279_sound a c hc) (sc280_sound a c hc)

def sc664 : RawPoly ℕ :=
  [(mkRat (1) 3, [0, 1, 1, 1, 2]),
   (mkRat (-2) 3, [0, 2, 3]),
   (mkRat (-2) 15, [1, 1, 1, 1, 1]),
   (mkRat (2) 3, [1, 1, 3]),
   (mkRat (-4) 5, [5])]

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc664_check :
    reduceTwo (prependC 1 sc280 ++ scaleR (-1) (prependC 0 sc281)) = sc664 := by
  decide +kernel

theorem sc664_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc664 = evRc a c (expWordR [1, 1, 7] (-4)) := by
  rw [← sc664_check]
  exact expTwo_step _ _ hc 0 [1, 7] (-4)
    sc280 sc281 (sc280_sound a c hc) (sc281_sound a c hc)

def sc665 : RawPoly ℕ :=
  [(mkRat (-1) 18, [0, 1, 1, 1, 1, 1, 1]),
   (mkRat (2) 9, [0, 1, 1, 1, 3]),
   (mkRat (1) 4, [0, 1, 1, 2, 2]),
   (mkRat (-1) 2, [0, 2, 4]),
   (mkRat (-2) 9, [0, 3, 3]),
   (mkRat (1) 2, [1, 1, 4]),
   (mkRat (-1) 6, [2, 2, 2]),
   (mkRat (-2) 3, [6])]

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc665_check :
    reduceTwo (prependC 1 sc281 ++ scaleR (-1) (prependC 0 sc282)) = sc665 := by
  decide +kernel

theorem sc665_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc665 = evRc a c (expWordR [1, 1, 7] (-3)) := by
  rw [← sc665_check]
  exact expTwo_step _ _ hc 0 [1, 7] (-3)
    sc281 sc282 (sc281_sound a c hc) (sc282_sound a c hc)

def sc666 : RawPoly ℕ :=
  [(mkRat (-1) 15, [0, 1, 1, 1, 1, 1, 2]),
   (mkRat (1) 6, [0, 1, 1, 1, 4]),
   (mkRat (1) 3, [0, 1, 1, 2, 3]),
   (mkRat (-2) 5, [0, 2, 5]),
   (mkRat (-1) 3, [0, 3, 4]),
   (mkRat (-1) 35, [1, 1, 1, 1, 1, 1, 1]),
   (mkRat (1) 6, [1, 1, 1, 2, 2]),
   (mkRat (2) 5, [1, 1, 5]),
   (mkRat (-1) 3, [2, 2, 3]),
   (mkRat (10) 7, [7])]

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc666_check :
    reduceTwo (prependC 1 sc282 ++ scaleR (-1) (prependC 0 sc283)) = sc666 := by
  decide +kernel

theorem sc666_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc666 = evRc a c (expWordR [1, 1, 7] (-2)) := by
  rw [← sc666_check]
  exact expTwo_step _ _ hc 0 [1, 7] (-2)
    sc282 sc283 (sc282_sound a c hc) (sc283_sound a c hc)

def sc667 : RawPoly ℕ :=
  [(mkRat (-1) 180, [0, 1, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (-2) 45, [0, 1, 1, 1, 1, 1, 3]),
   (mkRat (2) 15, [0, 1, 1, 1, 5]),
   (mkRat (1) 4, [0, 1, 1, 2, 4]),
   (mkRat (1) 9, [0, 1, 1, 3, 3]),
   (mkRat (-1) 48, [0, 2, 2, 2, 2]),
   (mkRat (-1) 3, [0, 2, 6]),
   (mkRat (-4) 15, [0, 3, 5]),
   (mkRat (-1) 8, [0, 4, 4]),
   (mkRat (-1) 18, [1, 1, 1, 1, 1, 1, 2]),
   (mkRat (2) 9, [1, 1, 1, 2, 3]),
   (mkRat (1) 12, [1, 1, 2, 2, 2]),
   (mkRat (1) 3, [1, 1, 6]),
   (mkRat (-1) 4, [2, 2, 4]),
   (mkRat (-2) 9, [2, 3, 3]),
   (mkRat (-1) 2, [8])]

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc667_check :
    reduceTwo (prependC 1 sc283 ++ scaleR (-1) (prependC 0 sc284)) = sc667 := by
  decide +kernel

theorem sc667_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc667 = evRc a c (expWordR [1, 1, 7] (-1)) := by
  rw [← sc667_check]
  exact expTwo_step _ _ hc 0 [1, 7] (-1)
    sc283 sc284 (sc283_sound a c hc) (sc284_sound a c hc)

def sc668 : RawPoly ℕ :=
  [(mkRat (-1) 70, [0, 1, 1, 1, 1, 1, 1, 1, 2]),
   (mkRat (-1) 30, [0, 1, 1, 1, 1, 1, 4]),
   (mkRat (1) 36, [0, 1, 1, 1, 2, 2, 2]),
   (mkRat (1) 9, [0, 1, 1, 1, 6]),
   (mkRat (1) 5, [0, 1, 1, 2, 5]),
   (mkRat (1) 6, [0, 1, 1, 3, 4]),
   (mkRat (-1) 18, [0, 2, 2, 2, 3]),
   (mkRat (5) 7, [0, 2, 7]),
   (mkRat (-2) 9, [0, 3, 6]),
   (mkRat (-1) 5, [0, 4, 5]),
   (mkRat (-1) 567, [1, 1, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (-1) 27, [1, 1, 1, 1, 1, 1, 3]),
   (mkRat (-1) 30, [1, 1, 1, 1, 1, 2, 2]),
   (mkRat (1) 6, [1, 1, 1, 2, 4]),
   (mkRat (2) 27, [1, 1, 1, 3, 3]),
   (mkRat (1) 6, [1, 1, 2, 2, 3]),
   (mkRat (-5) 7, [1, 1, 7]),
   (mkRat (-1) 5, [2, 2, 5]),
   (mkRat (-1) 3, [2, 3, 4]),
   (mkRat (-4) 81, [3, 3, 3]),
   (mkRat (-4) 9, [9])]

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc668_check :
    reduceTwo (prependC 1 sc284 ++ scaleR (-1) (prependC 0 sc285)) = sc668 := by
  decide +kernel

theorem sc668_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc668 = evRc a c (expWordR [1, 1, 7] (0)) := by
  rw [← sc668_check]
  exact expTwo_step _ _ hc 0 [1, 7] (0)
    sc284 sc285 (sc284_sound a c hc) (sc285_sound a c hc)

def sc669Part0 : RawPoly ℕ :=
  [(mkRat (-1) 4200, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (-1) 105, [0, 1, 1, 1, 1, 1, 1, 1, 3]),
   (mkRat (-1) 72, [0, 1, 1, 1, 1, 1, 1, 2, 2]),
   (mkRat (-2) 75, [0, 1, 1, 1, 1, 1, 5]),
   (mkRat (1) 18, [0, 1, 1, 1, 2, 2, 3]),
   (mkRat (-5) 21, [0, 1, 1, 1, 7]),
   (mkRat (1) 96, [0, 1, 1, 2, 2, 2, 2]),
   (mkRat (1) 6, [0, 1, 1, 2, 6]),
   (mkRat (2) 15, [0, 1, 1, 3, 5]),
   (mkRat (1) 16, [0, 1, 1, 4, 4]),
   (mkRat (-1) 24, [0, 2, 2, 2, 4]),
   (mkRat (-1) 18, [0, 2, 2, 3, 3]),
   (mkRat (-1) 4, [0, 2, 8]),
   (mkRat (10) 21, [0, 3, 7]),
   (mkRat (-1) 6, [0, 4, 6]),
   (mkRat (-2) 25, [0, 5, 5]),
   (mkRat (-1) 180, [1, 1, 1, 1, 1, 1, 1, 1, 2]),
   (mkRat (-1) 36, [1, 1, 1, 1, 1, 1, 4]),
   (mkRat (-2) 45, [1, 1, 1, 1, 1, 2, 3]),
   (mkRat (2) 15, [1, 1, 1, 2, 5]),
   (mkRat (1) 9, [1, 1, 1, 3, 4]),
   (mkRat (1) 8, [1, 1, 2, 2, 4]),
   (mkRat (1) 9, [1, 1, 2, 3, 3]),
   (mkRat (1) 4, [1, 1, 8])]

def sc669Part1 : RawPoly ℕ :=
  [(mkRat (-1) 240, [2, 2, 2, 2, 2]),
   (mkRat (-1) 6, [2, 2, 6]),
   (mkRat (-4) 15, [2, 3, 5]),
   (mkRat (-1) 8, [2, 4, 4]),
   (mkRat (-1) 9, [3, 3, 4]),
   (mkRat (-2) 5, [10])]

def sc669 : RawPoly ℕ :=
  [sc669Part0,
   sc669Part1].flatten

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc669_check :
    reduceTwo (prependC 1 sc285 ++ scaleR (-1) (prependC 0 sc286)) = sc669 := by
  decide +kernel

theorem sc669_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc669 = evRc a c (expWordR [1, 1, 7] (1)) := by
  rw [← sc669_check]
  exact expTwo_step _ _ hc 0 [1, 7] (1)
    sc285 sc286 (sc285_sound a c hc) (sc286_sound a c hc)

def sc670Part0 : RawPoly ℕ :=
  [(mkRat (-1) 1134, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2]),
   (mkRat (-1) 140, [0, 1, 1, 1, 1, 1, 1, 1, 4]),
   (mkRat (-1) 54, [0, 1, 1, 1, 1, 1, 1, 2, 3]),
   (mkRat (-1) 180, [0, 1, 1, 1, 1, 1, 2, 2, 2]),
   (mkRat (-1) 45, [0, 1, 1, 1, 1, 1, 6]),
   (mkRat (1) 24, [0, 1, 1, 1, 2, 2, 4]),
   (mkRat (1) 27, [0, 1, 1, 1, 2, 3, 3]),
   (mkRat (1) 12, [0, 1, 1, 1, 8]),
   (mkRat (1) 36, [0, 1, 1, 2, 2, 2, 3]),
   (mkRat (-5) 14, [0, 1, 1, 2, 7]),
   (mkRat (1) 9, [0, 1, 1, 3, 6]),
   (mkRat (1) 10, [0, 1, 1, 4, 5]),
   (mkRat (-1) 30, [0, 2, 2, 2, 5]),
   (mkRat (-1) 12, [0, 2, 2, 3, 4]),
   (mkRat (-2) 81, [0, 2, 3, 3, 3]),
   (mkRat (-2) 9, [0, 2, 9]),
   (mkRat (-1) 6, [0, 3, 8]),
   (mkRat (5) 14, [0, 4, 7]),
   (mkRat (-2) 15, [0, 5, 6]),
   (mkRat (-1) 17820, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (-1) 270, [1, 1, 1, 1, 1, 1, 1, 1, 3]),
   (mkRat (-1) 140, [1, 1, 1, 1, 1, 1, 1, 2, 2]),
   (mkRat (-1) 45, [1, 1, 1, 1, 1, 1, 5]),
   (mkRat (-1) 30, [1, 1, 1, 1, 1, 2, 4])]

def sc670Part1 : RawPoly ℕ :=
  [(mkRat (-2) 135, [1, 1, 1, 1, 1, 3, 3]),
   (mkRat (1) 144, [1, 1, 1, 2, 2, 2, 2]),
   (mkRat (1) 9, [1, 1, 1, 2, 6]),
   (mkRat (4) 45, [1, 1, 1, 3, 5]),
   (mkRat (1) 24, [1, 1, 1, 4, 4]),
   (mkRat (1) 10, [1, 1, 2, 2, 5]),
   (mkRat (1) 6, [1, 1, 2, 3, 4]),
   (mkRat (2) 81, [1, 1, 3, 3, 3]),
   (mkRat (2) 9, [1, 1, 9]),
   (mkRat (-1) 72, [2, 2, 2, 2, 3]),
   (mkRat (5) 14, [2, 2, 7]),
   (mkRat (-2) 9, [2, 3, 6]),
   (mkRat (-1) 5, [2, 4, 5]),
   (mkRat (-4) 45, [3, 3, 5]),
   (mkRat (-1) 12, [3, 4, 4]),
   (mkRat (-4) 11, [11])]

def sc670 : RawPoly ℕ :=
  [sc670Part0,
   sc670Part1].flatten

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc670_check :
    reduceTwo (prependC 1 sc286 ++ scaleR (-1) (prependC 0 sc287)) = sc670 := by
  decide +kernel

theorem sc670_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc670 = evRc a c (expWordR [1, 1, 7] (2)) := by
  rw [← sc670_check]
  exact expTwo_step _ _ hc 0 [1, 7] (2)
    sc286 sc287 (sc286_sound a c hc) (sc287_sound a c hc)

def sc671Part0 : RawPoly ℕ :=
  [(mkRat (-1) 170100, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (-1) 1701, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3]),
   (mkRat (-1) 720, [0, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2]),
   (mkRat (-1) 175, [0, 1, 1, 1, 1, 1, 1, 1, 5]),
   (mkRat (-1) 72, [0, 1, 1, 1, 1, 1, 1, 2, 4]),
   (mkRat (-1) 162, [0, 1, 1, 1, 1, 1, 1, 3, 3]),
   (mkRat (-1) 90, [0, 1, 1, 1, 1, 1, 2, 2, 3]),
   (mkRat (1) 21, [0, 1, 1, 1, 1, 1, 7]),
   (mkRat (1) 30, [0, 1, 1, 1, 2, 2, 5]),
   (mkRat (1) 18, [0, 1, 1, 1, 2, 3, 4]),
   (mkRat (2) 243, [0, 1, 1, 1, 3, 3, 3]),
   (mkRat (2) 27, [0, 1, 1, 1, 9]),
   (mkRat (1) 48, [0, 1, 1, 2, 2, 2, 4]),
   (mkRat (1) 36, [0, 1, 1, 2, 2, 3, 3]),
   (mkRat (1) 8, [0, 1, 1, 2, 8]),
   (mkRat (-5) 21, [0, 1, 1, 3, 7]),
   (mkRat (1) 12, [0, 1, 1, 4, 6]),
   (mkRat (1) 25, [0, 1, 1, 5, 5]),
   (mkRat (-1) 2880, [0, 2, 2, 2, 2, 2, 2]),
   (mkRat (-1) 36, [0, 2, 2, 2, 6]),
   (mkRat (-1) 15, [0, 2, 2, 3, 5]),
   (mkRat (-1) 32, [0, 2, 2, 4, 4]),
   (mkRat (-1) 18, [0, 2, 3, 3, 4]),
   (mkRat (-1) 5, [0, 2, 10])]

def sc671Part1 : RawPoly ℕ :=
  [(mkRat (-1) 243, [0, 3, 3, 3, 3]),
   (mkRat (-4) 27, [0, 3, 9]),
   (mkRat (-1) 8, [0, 4, 8]),
   (mkRat (2) 7, [0, 5, 7]),
   (mkRat (-1) 18, [0, 6, 6]),
   (mkRat (-1) 4200, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2]),
   (mkRat (-1) 360, [1, 1, 1, 1, 1, 1, 1, 1, 4]),
   (mkRat (-1) 105, [1, 1, 1, 1, 1, 1, 1, 2, 3]),
   (mkRat (-1) 216, [1, 1, 1, 1, 1, 1, 2, 2, 2]),
   (mkRat (-1) 54, [1, 1, 1, 1, 1, 1, 6]),
   (mkRat (-2) 75, [1, 1, 1, 1, 1, 2, 5]),
   (mkRat (-1) 45, [1, 1, 1, 1, 1, 3, 4]),
   (mkRat (1) 54, [1, 1, 1, 2, 2, 2, 3]),
   (mkRat (-5) 21, [1, 1, 1, 2, 7]),
   (mkRat (2) 27, [1, 1, 1, 3, 6]),
   (mkRat (1) 15, [1, 1, 1, 4, 5]),
   (mkRat (1) 480, [1, 1, 2, 2, 2, 2, 2]),
   (mkRat (1) 12, [1, 1, 2, 2, 6]),
   (mkRat (2) 15, [1, 1, 2, 3, 5]),
   (mkRat (1) 16, [1, 1, 2, 4, 4]),
   (mkRat (1) 18, [1, 1, 3, 3, 4]),
   (mkRat (1) 5, [1, 1, 10]),
   (mkRat (-1) 96, [2, 2, 2, 2, 4]),
   (mkRat (-1) 54, [2, 2, 2, 3, 3])]

def sc671Part2 : RawPoly ℕ :=
  [(mkRat (-1) 8, [2, 2, 8]),
   (mkRat (10) 21, [2, 3, 7]),
   (mkRat (-1) 6, [2, 4, 6]),
   (mkRat (-2) 25, [2, 5, 5]),
   (mkRat (-2) 27, [3, 3, 6]),
   (mkRat (-2) 15, [3, 4, 5]),
   (mkRat (-1) 48, [4, 4, 4]),
   (mkRat (-1) 3, [12])]

def sc671 : RawPoly ℕ :=
  [sc671Part0,
   sc671Part1,
   sc671Part2].flatten

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc671_check :
    reduceTwo (prependC 1 sc287 ++ scaleR (-1) (prependC 0 sc288)) = sc671 := by
  decide +kernel

theorem sc671_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc671 = evRc a c (expWordR [1, 1, 7] (3)) := by
  rw [← sc671_check]
  exact expTwo_step _ _ hc 0 [1, 7] (3)
    sc287 sc288 (sc287_sound a c hc) (sc288_sound a c hc)

def sc672Part0 : RawPoly ℕ :=
  [(mkRat (-1) 35640, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2]),
   (mkRat (-1) 2268, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4]),
   (mkRat (-1) 540, [0, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3]),
   (mkRat (-1) 840, [0, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2]),
   (mkRat (-1) 210, [0, 1, 1, 1, 1, 1, 1, 1, 6]),
   (mkRat (-1) 90, [0, 1, 1, 1, 1, 1, 1, 2, 5]),
   (mkRat (-1) 108, [0, 1, 1, 1, 1, 1, 1, 3, 4]),
   (mkRat (-1) 120, [0, 1, 1, 1, 1, 1, 2, 2, 4]),
   (mkRat (-1) 135, [0, 1, 1, 1, 1, 1, 2, 3, 3]),
   (mkRat (-1) 60, [0, 1, 1, 1, 1, 1, 8]),
   (mkRat (1) 1440, [0, 1, 1, 1, 2, 2, 2, 2, 2]),
   (mkRat (1) 36, [0, 1, 1, 1, 2, 2, 6]),
   (mkRat (2) 45, [0, 1, 1, 1, 2, 3, 5]),
   (mkRat (1) 48, [0, 1, 1, 1, 2, 4, 4]),
   (mkRat (1) 54, [0, 1, 1, 1, 3, 3, 4]),
   (mkRat (1) 15, [0, 1, 1, 1, 10]),
   (mkRat (1) 60, [0, 1, 1, 2, 2, 2, 5]),
   (mkRat (1) 24, [0, 1, 1, 2, 2, 3, 4]),
   (mkRat (1) 81, [0, 1, 1, 2, 3, 3, 3]),
   (mkRat (1) 9, [0, 1, 1, 2, 9]),
   (mkRat (1) 12, [0, 1, 1, 3, 8]),
   (mkRat (-5) 28, [0, 1, 1, 4, 7]),
   (mkRat (1) 15, [0, 1, 1, 5, 6]),
   (mkRat (-1) 720, [0, 2, 2, 2, 2, 2, 3])]

def sc672Part1 : RawPoly ℕ :=
  [(mkRat (5) 84, [0, 2, 2, 2, 7]),
   (mkRat (-1) 18, [0, 2, 2, 3, 6]),
   (mkRat (-1) 20, [0, 2, 2, 4, 5]),
   (mkRat (-2) 45, [0, 2, 3, 3, 5]),
   (mkRat (-1) 24, [0, 2, 3, 4, 4]),
   (mkRat (-2) 11, [0, 2, 11]),
   (mkRat (-1) 81, [0, 3, 3, 3, 4]),
   (mkRat (-2) 15, [0, 3, 10]),
   (mkRat (-1) 9, [0, 4, 9]),
   (mkRat (-1) 10, [0, 5, 8]),
   (mkRat (5) 21, [0, 6, 7]),
   (mkRat (-1) 900900, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (-1) 6300, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3]),
   (mkRat (-1) 2268, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2]),
   (mkRat (-1) 450, [1, 1, 1, 1, 1, 1, 1, 1, 5]),
   (mkRat (-1) 140, [1, 1, 1, 1, 1, 1, 1, 2, 4]),
   (mkRat (-1) 315, [1, 1, 1, 1, 1, 1, 1, 3, 3]),
   (mkRat (-1) 108, [1, 1, 1, 1, 1, 1, 2, 2, 3]),
   (mkRat (5) 126, [1, 1, 1, 1, 1, 1, 7]),
   (mkRat (-1) 720, [1, 1, 1, 1, 1, 2, 2, 2, 2]),
   (mkRat (-1) 45, [1, 1, 1, 1, 1, 2, 6]),
   (mkRat (-4) 225, [1, 1, 1, 1, 1, 3, 5]),
   (mkRat (-1) 120, [1, 1, 1, 1, 1, 4, 4]),
   (mkRat (1) 72, [1, 1, 1, 2, 2, 2, 4])]

def sc672Part2 : RawPoly ℕ :=
  [(mkRat (1) 54, [1, 1, 1, 2, 2, 3, 3]),
   (mkRat (1) 12, [1, 1, 1, 2, 8]),
   (mkRat (-10) 63, [1, 1, 1, 3, 7]),
   (mkRat (1) 18, [1, 1, 1, 4, 6]),
   (mkRat (2) 75, [1, 1, 1, 5, 5]),
   (mkRat (1) 144, [1, 1, 2, 2, 2, 2, 3]),
   (mkRat (-5) 28, [1, 1, 2, 2, 7]),
   (mkRat (1) 9, [1, 1, 2, 3, 6]),
   (mkRat (1) 10, [1, 1, 2, 4, 5]),
   (mkRat (2) 45, [1, 1, 3, 3, 5]),
   (mkRat (1) 24, [1, 1, 3, 4, 4]),
   (mkRat (2) 11, [1, 1, 11]),
   (mkRat (-1) 120, [2, 2, 2, 2, 5]),
   (mkRat (-1) 36, [2, 2, 2, 3, 4]),
   (mkRat (-1) 81, [2, 2, 3, 3, 3]),
   (mkRat (-1) 9, [2, 2, 9]),
   (mkRat (-1) 6, [2, 3, 8]),
   (mkRat (5) 14, [2, 4, 7]),
   (mkRat (-2) 15, [2, 5, 6]),
   (mkRat (10) 63, [3, 3, 7]),
   (mkRat (-1) 9, [3, 4, 6]),
   (mkRat (-4) 75, [3, 5, 5]),
   (mkRat (-1) 20, [4, 4, 5]),
   (mkRat (-4) 13, [13])]

def sc672 : RawPoly ℕ :=
  [sc672Part0,
   sc672Part1,
   sc672Part2].flatten

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc672_check :
    reduceTwo (prependC 1 sc288 ++ scaleR (-1) (prependC 0 sc289)) = sc672 := by
  decide +kernel

theorem sc672_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc672 = evRc a c (expWordR [1, 1, 7] (4)) := by
  rw [← sc672_check]
  exact expTwo_step _ _ hc 0 [1, 7] (4)
    sc288 sc289 (sc288_sound a c hc) (sc289_sound a c hc)

def sc673Part0 : RawPoly ℕ :=
  [(mkRat (-1) 10478160, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (-1) 53460, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3]),
   (mkRat (-1) 16800, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2]),
   (mkRat (-1) 2835, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5]),
   (mkRat (-1) 720, [0, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4]),
   (mkRat (-1) 1620, [0, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3]),
   (mkRat (-1) 420, [0, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3]),
   (mkRat (1) 98, [0, 1, 1, 1, 1, 1, 1, 1, 7]),
   (mkRat (-1) 1728, [0, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2]),
   (mkRat (-1) 108, [0, 1, 1, 1, 1, 1, 1, 2, 6]),
   (mkRat (-1) 135, [0, 1, 1, 1, 1, 1, 1, 3, 5]),
   (mkRat (-1) 288, [0, 1, 1, 1, 1, 1, 1, 4, 4]),
   (mkRat (-1) 150, [0, 1, 1, 1, 1, 1, 2, 2, 5]),
   (mkRat (-1) 90, [0, 1, 1, 1, 1, 1, 2, 3, 4]),
   (mkRat (-2) 1215, [0, 1, 1, 1, 1, 1, 3, 3, 3]),
   (mkRat (-2) 135, [0, 1, 1, 1, 1, 1, 9]),
   (mkRat (1) 432, [0, 1, 1, 1, 2, 2, 2, 2, 3]),
   (mkRat (-5) 84, [0, 1, 1, 1, 2, 2, 7]),
   (mkRat (1) 27, [0, 1, 1, 1, 2, 3, 6]),
   (mkRat (1) 30, [0, 1, 1, 1, 2, 4, 5]),
   (mkRat (2) 135, [0, 1, 1, 1, 3, 3, 5]),
   (mkRat (1) 72, [0, 1, 1, 1, 3, 4, 4]),
   (mkRat (2) 33, [0, 1, 1, 1, 11]),
   (mkRat (1) 5760, [0, 1, 1, 2, 2, 2, 2, 2, 2])]

def sc673Part1 : RawPoly ℕ :=
  [(mkRat (1) 72, [0, 1, 1, 2, 2, 2, 6]),
   (mkRat (1) 30, [0, 1, 1, 2, 2, 3, 5]),
   (mkRat (1) 64, [0, 1, 1, 2, 2, 4, 4]),
   (mkRat (1) 36, [0, 1, 1, 2, 3, 3, 4]),
   (mkRat (1) 10, [0, 1, 1, 2, 10]),
   (mkRat (1) 486, [0, 1, 1, 3, 3, 3, 3]),
   (mkRat (2) 27, [0, 1, 1, 3, 9]),
   (mkRat (1) 16, [0, 1, 1, 4, 8]),
   (mkRat (-1) 7, [0, 1, 1, 5, 7]),
   (mkRat (1) 36, [0, 1, 1, 6, 6]),
   (mkRat (-1) 960, [0, 2, 2, 2, 2, 2, 4]),
   (mkRat (-1) 432, [0, 2, 2, 2, 2, 3, 3]),
   (mkRat (-1) 48, [0, 2, 2, 2, 8]),
   (mkRat (5) 42, [0, 2, 2, 3, 7]),
   (mkRat (-1) 24, [0, 2, 2, 4, 6]),
   (mkRat (-1) 50, [0, 2, 2, 5, 5]),
   (mkRat (-1) 27, [0, 2, 3, 3, 6]),
   (mkRat (-1) 15, [0, 2, 3, 4, 5]),
   (mkRat (-1) 96, [0, 2, 4, 4, 4]),
   (mkRat (-1) 6, [0, 2, 12]),
   (mkRat (-4) 405, [0, 3, 3, 3, 5]),
   (mkRat (-1) 72, [0, 3, 3, 4, 4]),
   (mkRat (-4) 33, [0, 3, 11]),
   (mkRat (-1) 10, [0, 4, 10])]

def sc673Part2 : RawPoly ℕ :=
  [(mkRat (-4) 45, [0, 5, 9]),
   (mkRat (-1) 12, [0, 6, 8]),
   (mkRat (12) 49, [0, 7, 7]),
   (mkRat (-1) 170100, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2]),
   (mkRat (-1) 8400, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4]),
   (mkRat (-1) 1701, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3]),
   (mkRat (-1) 2160, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2]),
   (mkRat (-1) 540, [1, 1, 1, 1, 1, 1, 1, 1, 6]),
   (mkRat (-1) 175, [1, 1, 1, 1, 1, 1, 1, 2, 5]),
   (mkRat (-1) 210, [1, 1, 1, 1, 1, 1, 1, 3, 4]),
   (mkRat (-1) 144, [1, 1, 1, 1, 1, 1, 2, 2, 4]),
   (mkRat (-1) 162, [1, 1, 1, 1, 1, 1, 2, 3, 3]),
   (mkRat (-1) 72, [1, 1, 1, 1, 1, 1, 8]),
   (mkRat (-1) 270, [1, 1, 1, 1, 1, 2, 2, 2, 3]),
   (mkRat (1) 21, [1, 1, 1, 1, 1, 2, 7]),
   (mkRat (-2) 135, [1, 1, 1, 1, 1, 3, 6]),
   (mkRat (-1) 75, [1, 1, 1, 1, 1, 4, 5]),
   (mkRat (1) 90, [1, 1, 1, 2, 2, 2, 5]),
   (mkRat (1) 36, [1, 1, 1, 2, 2, 3, 4]),
   (mkRat (2) 243, [1, 1, 1, 2, 3, 3, 3]),
   (mkRat (2) 27, [1, 1, 1, 2, 9]),
   (mkRat (1) 18, [1, 1, 1, 3, 8]),
   (mkRat (-5) 42, [1, 1, 1, 4, 7]),
   (mkRat (2) 45, [1, 1, 1, 5, 6])]

def sc673Part3 : RawPoly ℕ :=
  [(mkRat (1) 192, [1, 1, 2, 2, 2, 2, 4]),
   (mkRat (1) 108, [1, 1, 2, 2, 2, 3, 3]),
   (mkRat (1) 16, [1, 1, 2, 2, 8]),
   (mkRat (-5) 21, [1, 1, 2, 3, 7]),
   (mkRat (1) 12, [1, 1, 2, 4, 6]),
   (mkRat (1) 25, [1, 1, 2, 5, 5]),
   (mkRat (1) 27, [1, 1, 3, 3, 6]),
   (mkRat (1) 15, [1, 1, 3, 4, 5]),
   (mkRat (1) 96, [1, 1, 4, 4, 4]),
   (mkRat (1) 6, [1, 1, 12]),
   (mkRat (-1) 20160, [2, 2, 2, 2, 2, 2, 2]),
   (mkRat (-1) 144, [2, 2, 2, 2, 6]),
   (mkRat (-1) 45, [2, 2, 2, 3, 5]),
   (mkRat (-1) 96, [2, 2, 2, 4, 4]),
   (mkRat (-1) 36, [2, 2, 3, 3, 4]),
   (mkRat (-1) 10, [2, 2, 10]),
   (mkRat (-1) 243, [2, 3, 3, 3, 3]),
   (mkRat (-4) 27, [2, 3, 9]),
   (mkRat (-1) 8, [2, 4, 8]),
   (mkRat (2) 7, [2, 5, 7]),
   (mkRat (-1) 18, [2, 6, 6]),
   (mkRat (-1) 18, [3, 3, 8]),
   (mkRat (5) 21, [3, 4, 7]),
   (mkRat (-4) 45, [3, 5, 6])]

def sc673Part4 : RawPoly ℕ :=
  [(mkRat (-1) 24, [4, 4, 6]),
   (mkRat (-1) 25, [4, 5, 5]),
   (mkRat (-2) 7, [14])]

def sc673 : RawPoly ℕ :=
  [sc673Part0,
   sc673Part1,
   sc673Part2,
   sc673Part3,
   sc673Part4].flatten

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc673_check :
    reduceTwo (prependC 1 sc289 ++ scaleR (-1) (prependC 0 sc290)) = sc673 := by
  decide +kernel

theorem sc673_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc673 = evRc a c (expWordR [1, 1, 7] (5)) := by
  rw [← sc673_check]
  exact expTwo_step _ _ hc 0 [1, 7] (5)
    sc289 sc290 (sc289_sound a c hc) (sc290_sound a c hc)

def sc674Part0 : RawPoly ℕ :=
  [(mkRat (-1) 1801800, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2]),
   (mkRat (-1) 71280, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4]),
   (mkRat (-1) 12600, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3]),
   (mkRat (-1) 13608, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2]),
   (mkRat (-1) 3402, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6]),
   (mkRat (-1) 900, [0, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5]),
   (mkRat (-1) 1080, [0, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4]),
   (mkRat (-1) 560, [0, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4]),
   (mkRat (-1) 630, [0, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3]),
   (mkRat (-1) 280, [0, 1, 1, 1, 1, 1, 1, 1, 8]),
   (mkRat (-1) 648, [0, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3]),
   (mkRat (5) 252, [0, 1, 1, 1, 1, 1, 1, 2, 7]),
   (mkRat (-1) 162, [0, 1, 1, 1, 1, 1, 1, 3, 6]),
   (mkRat (-1) 180, [0, 1, 1, 1, 1, 1, 1, 4, 5]),
   (mkRat (-1) 7200, [0, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2]),
   (mkRat (-1) 180, [0, 1, 1, 1, 1, 1, 2, 2, 6]),
   (mkRat (-2) 225, [0, 1, 1, 1, 1, 1, 2, 3, 5]),
   (mkRat (-1) 240, [0, 1, 1, 1, 1, 1, 2, 4, 4]),
   (mkRat (-1) 270, [0, 1, 1, 1, 1, 1, 3, 3, 4]),
   (mkRat (-1) 75, [0, 1, 1, 1, 1, 1, 10]),
   (mkRat (1) 576, [0, 1, 1, 1, 2, 2, 2, 2, 4]),
   (mkRat (1) 324, [0, 1, 1, 1, 2, 2, 2, 3, 3]),
   (mkRat (1) 48, [0, 1, 1, 1, 2, 2, 8]),
   (mkRat (-5) 63, [0, 1, 1, 1, 2, 3, 7])]

def sc674Part1 : RawPoly ℕ :=
  [(mkRat (1) 36, [0, 1, 1, 1, 2, 4, 6]),
   (mkRat (1) 75, [0, 1, 1, 1, 2, 5, 5]),
   (mkRat (1) 81, [0, 1, 1, 1, 3, 3, 6]),
   (mkRat (1) 45, [0, 1, 1, 1, 3, 4, 5]),
   (mkRat (1) 288, [0, 1, 1, 1, 4, 4, 4]),
   (mkRat (1) 18, [0, 1, 1, 1, 12]),
   (mkRat (1) 1440, [0, 1, 1, 2, 2, 2, 2, 2, 3]),
   (mkRat (-5) 168, [0, 1, 1, 2, 2, 2, 7]),
   (mkRat (1) 36, [0, 1, 1, 2, 2, 3, 6]),
   (mkRat (1) 40, [0, 1, 1, 2, 2, 4, 5]),
   (mkRat (1) 45, [0, 1, 1, 2, 3, 3, 5]),
   (mkRat (1) 48, [0, 1, 1, 2, 3, 4, 4]),
   (mkRat (1) 11, [0, 1, 1, 2, 11]),
   (mkRat (1) 162, [0, 1, 1, 3, 3, 3, 4]),
   (mkRat (1) 15, [0, 1, 1, 3, 10]),
   (mkRat (1) 18, [0, 1, 1, 4, 9]),
   (mkRat (1) 20, [0, 1, 1, 5, 8]),
   (mkRat (-5) 42, [0, 1, 1, 6, 7]),
   (mkRat (-1) 1200, [0, 2, 2, 2, 2, 2, 5]),
   (mkRat (-1) 288, [0, 2, 2, 2, 2, 3, 4]),
   (mkRat (-1) 486, [0, 2, 2, 2, 3, 3, 3]),
   (mkRat (-1) 54, [0, 2, 2, 2, 9]),
   (mkRat (-1) 24, [0, 2, 2, 3, 8]),
   (mkRat (5) 56, [0, 2, 2, 4, 7])]

def sc674Part2 : RawPoly ℕ :=
  [(mkRat (-1) 30, [0, 2, 2, 5, 6]),
   (mkRat (5) 63, [0, 2, 3, 3, 7]),
   (mkRat (-1) 18, [0, 2, 3, 4, 6]),
   (mkRat (-2) 75, [0, 2, 3, 5, 5]),
   (mkRat (-1) 40, [0, 2, 4, 4, 5]),
   (mkRat (-2) 13, [0, 2, 13]),
   (mkRat (-2) 243, [0, 3, 3, 3, 6]),
   (mkRat (-1) 45, [0, 3, 3, 4, 5]),
   (mkRat (-1) 144, [0, 3, 4, 4, 4]),
   (mkRat (-1) 9, [0, 3, 12]),
   (mkRat (-1) 11, [0, 4, 11]),
   (mkRat (-2) 25, [0, 5, 10]),
   (mkRat (-2) 27, [0, 6, 9]),
   (mkRat (5) 28, [0, 7, 8]),
   (mkRat (-1) 66339000, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (-1) 255150, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3]),
   (mkRat (-1) 71280, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2]),
   (mkRat (-1) 10500, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5]),
   (mkRat (-1) 2268, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4]),
   (mkRat (-1) 5103, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3]),
   (mkRat (-1) 1080, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3]),
   (mkRat (1) 252, [1, 1, 1, 1, 1, 1, 1, 1, 7]),
   (mkRat (-1) 3360, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2]),
   (mkRat (-1) 210, [1, 1, 1, 1, 1, 1, 1, 2, 6])]

def sc674Part3 : RawPoly ℕ :=
  [(mkRat (-2) 525, [1, 1, 1, 1, 1, 1, 1, 3, 5]),
   (mkRat (-1) 560, [1, 1, 1, 1, 1, 1, 1, 4, 4]),
   (mkRat (-1) 180, [1, 1, 1, 1, 1, 1, 2, 2, 5]),
   (mkRat (-1) 108, [1, 1, 1, 1, 1, 1, 2, 3, 4]),
   (mkRat (-1) 729, [1, 1, 1, 1, 1, 1, 3, 3, 3]),
   (mkRat (-1) 81, [1, 1, 1, 1, 1, 1, 9]),
   (mkRat (-1) 360, [1, 1, 1, 1, 1, 2, 2, 2, 4]),
   (mkRat (-1) 270, [1, 1, 1, 1, 1, 2, 2, 3, 3]),
   (mkRat (-1) 60, [1, 1, 1, 1, 1, 2, 8]),
   (mkRat (2) 63, [1, 1, 1, 1, 1, 3, 7]),
   (mkRat (-1) 90, [1, 1, 1, 1, 1, 4, 6]),
   (mkRat (-2) 375, [1, 1, 1, 1, 1, 5, 5]),
   (mkRat (1) 8640, [1, 1, 1, 2, 2, 2, 2, 2, 2]),
   (mkRat (1) 108, [1, 1, 1, 2, 2, 2, 6]),
   (mkRat (1) 45, [1, 1, 1, 2, 2, 3, 5]),
   (mkRat (1) 96, [1, 1, 1, 2, 2, 4, 4]),
   (mkRat (1) 54, [1, 1, 1, 2, 3, 3, 4]),
   (mkRat (1) 15, [1, 1, 1, 2, 10]),
   (mkRat (1) 729, [1, 1, 1, 3, 3, 3, 3]),
   (mkRat (4) 81, [1, 1, 1, 3, 9]),
   (mkRat (1) 24, [1, 1, 1, 4, 8]),
   (mkRat (-2) 21, [1, 1, 1, 5, 7]),
   (mkRat (1) 54, [1, 1, 1, 6, 6]),
   (mkRat (1) 240, [1, 1, 2, 2, 2, 2, 5])]

def sc674Part4 : RawPoly ℕ :=
  [(mkRat (1) 72, [1, 1, 2, 2, 2, 3, 4]),
   (mkRat (1) 162, [1, 1, 2, 2, 3, 3, 3]),
   (mkRat (1) 18, [1, 1, 2, 2, 9]),
   (mkRat (1) 12, [1, 1, 2, 3, 8]),
   (mkRat (-5) 28, [1, 1, 2, 4, 7]),
   (mkRat (1) 15, [1, 1, 2, 5, 6]),
   (mkRat (-5) 63, [1, 1, 3, 3, 7]),
   (mkRat (1) 18, [1, 1, 3, 4, 6]),
   (mkRat (2) 75, [1, 1, 3, 5, 5]),
   (mkRat (1) 40, [1, 1, 4, 4, 5]),
   (mkRat (2) 13, [1, 1, 13]),
   (mkRat (-1) 4320, [2, 2, 2, 2, 2, 2, 3]),
   (mkRat (5) 336, [2, 2, 2, 2, 7]),
   (mkRat (-1) 54, [2, 2, 2, 3, 6]),
   (mkRat (-1) 60, [2, 2, 2, 4, 5]),
   (mkRat (-1) 45, [2, 2, 3, 3, 5]),
   (mkRat (-1) 48, [2, 2, 3, 4, 4]),
   (mkRat (-1) 11, [2, 2, 11]),
   (mkRat (-1) 81, [2, 3, 3, 3, 4]),
   (mkRat (-2) 15, [2, 3, 10]),
   (mkRat (-1) 9, [2, 4, 9]),
   (mkRat (-1) 10, [2, 5, 8]),
   (mkRat (5) 21, [2, 6, 7]),
   (mkRat (-2) 3645, [3, 3, 3, 3, 3])]

def sc674Part5 : RawPoly ℕ :=
  [(mkRat (-4) 81, [3, 3, 9]),
   (mkRat (-1) 12, [3, 4, 8]),
   (mkRat (4) 21, [3, 5, 7]),
   (mkRat (-1) 27, [3, 6, 6]),
   (mkRat (5) 56, [4, 4, 7]),
   (mkRat (-1) 15, [4, 5, 6]),
   (mkRat (-4) 375, [5, 5, 5]),
   (mkRat (-4) 15, [15])]

def sc674 : RawPoly ℕ :=
  [sc674Part0,
   sc674Part1,
   sc674Part2,
   sc674Part3,
   sc674Part4,
   sc674Part5].flatten

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc674_check :
    reduceTwo (prependC 1 sc290 ++ scaleR (-1) (prependC 0 sc291)) = sc674 := by
  decide +kernel

theorem sc674_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc674 = evRc a c (expWordR [1, 1, 7] (6)) := by
  rw [← sc674_check]
  exact expTwo_step _ _ hc 0 [1, 7] (6)
    sc290 sc291 (sc290_sound a c hc) (sc291_sound a c hc)

def sc675Part0 : RawPoly ℕ :=
  [(mkRat (-1) 908107200, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (-1) 2702700, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3]),
   (mkRat (-1) 680400, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2]),
   (mkRat (-1) 89100, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5]),
   (mkRat (-1) 16800, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4]),
   (mkRat (-1) 37800, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3]),
   (mkRat (-1) 6804, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3]),
   (mkRat (5) 7938, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7]),
   (mkRat (-1) 17280, [0, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2]),
   (mkRat (-1) 1080, [0, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6]),
   (mkRat (-1) 1350, [0, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5]),
   (mkRat (-1) 2880, [0, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4]),
   (mkRat (-1) 700, [0, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5]),
   (mkRat (-1) 420, [0, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4]),
   (mkRat (-1) 2835, [0, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3]),
   (mkRat (-1) 315, [0, 1, 1, 1, 1, 1, 1, 1, 9]),
   (mkRat (-1) 864, [0, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4]),
   (mkRat (-1) 648, [0, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3]),
   (mkRat (-1) 144, [0, 1, 1, 1, 1, 1, 1, 2, 8]),
   (mkRat (5) 378, [0, 1, 1, 1, 1, 1, 1, 3, 7]),
   (mkRat (-1) 216, [0, 1, 1, 1, 1, 1, 1, 4, 6]),
   (mkRat (-1) 450, [0, 1, 1, 1, 1, 1, 1, 5, 5]),
   (mkRat (-1) 2160, [0, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3]),
   (mkRat (1) 84, [0, 1, 1, 1, 1, 1, 2, 2, 7])]

def sc675Part1 : RawPoly ℕ :=
  [(mkRat (-1) 135, [0, 1, 1, 1, 1, 1, 2, 3, 6]),
   (mkRat (-1) 150, [0, 1, 1, 1, 1, 1, 2, 4, 5]),
   (mkRat (-2) 675, [0, 1, 1, 1, 1, 1, 3, 3, 5]),
   (mkRat (-1) 360, [0, 1, 1, 1, 1, 1, 3, 4, 4]),
   (mkRat (-2) 165, [0, 1, 1, 1, 1, 1, 11]),
   (mkRat (1) 720, [0, 1, 1, 1, 2, 2, 2, 2, 5]),
   (mkRat (1) 216, [0, 1, 1, 1, 2, 2, 2, 3, 4]),
   (mkRat (1) 486, [0, 1, 1, 1, 2, 2, 3, 3, 3]),
   (mkRat (1) 54, [0, 1, 1, 1, 2, 2, 9]),
   (mkRat (1) 36, [0, 1, 1, 1, 2, 3, 8]),
   (mkRat (-5) 84, [0, 1, 1, 1, 2, 4, 7]),
   (mkRat (1) 45, [0, 1, 1, 1, 2, 5, 6]),
   (mkRat (-5) 189, [0, 1, 1, 1, 3, 3, 7]),
   (mkRat (1) 54, [0, 1, 1, 1, 3, 4, 6]),
   (mkRat (2) 225, [0, 1, 1, 1, 3, 5, 5]),
   (mkRat (1) 120, [0, 1, 1, 1, 4, 4, 5]),
   (mkRat (2) 39, [0, 1, 1, 1, 13]),
   (mkRat (1) 1920, [0, 1, 1, 2, 2, 2, 2, 2, 4]),
   (mkRat (1) 864, [0, 1, 1, 2, 2, 2, 2, 3, 3]),
   (mkRat (1) 96, [0, 1, 1, 2, 2, 2, 8]),
   (mkRat (-5) 84, [0, 1, 1, 2, 2, 3, 7]),
   (mkRat (1) 48, [0, 1, 1, 2, 2, 4, 6]),
   (mkRat (1) 100, [0, 1, 1, 2, 2, 5, 5]),
   (mkRat (1) 54, [0, 1, 1, 2, 3, 3, 6])]

def sc675Part2 : RawPoly ℕ :=
  [(mkRat (1) 30, [0, 1, 1, 2, 3, 4, 5]),
   (mkRat (1) 192, [0, 1, 1, 2, 4, 4, 4]),
   (mkRat (1) 12, [0, 1, 1, 2, 12]),
   (mkRat (2) 405, [0, 1, 1, 3, 3, 3, 5]),
   (mkRat (1) 144, [0, 1, 1, 3, 3, 4, 4]),
   (mkRat (2) 33, [0, 1, 1, 3, 11]),
   (mkRat (1) 20, [0, 1, 1, 4, 10]),
   (mkRat (2) 45, [0, 1, 1, 5, 9]),
   (mkRat (1) 24, [0, 1, 1, 6, 8]),
   (mkRat (-6) 49, [0, 1, 1, 7, 7]),
   (mkRat (-1) 322560, [0, 2, 2, 2, 2, 2, 2, 2, 2]),
   (mkRat (-1) 1440, [0, 2, 2, 2, 2, 2, 6]),
   (mkRat (-1) 360, [0, 2, 2, 2, 2, 3, 5]),
   (mkRat (-1) 768, [0, 2, 2, 2, 2, 4, 4]),
   (mkRat (-1) 216, [0, 2, 2, 2, 3, 3, 4]),
   (mkRat (-1) 60, [0, 2, 2, 2, 10]),
   (mkRat (-1) 972, [0, 2, 2, 3, 3, 3, 3]),
   (mkRat (-1) 27, [0, 2, 2, 3, 9]),
   (mkRat (-1) 32, [0, 2, 2, 4, 8]),
   (mkRat (1) 14, [0, 2, 2, 5, 7]),
   (mkRat (-1) 72, [0, 2, 2, 6, 6]),
   (mkRat (-1) 36, [0, 2, 3, 3, 8]),
   (mkRat (5) 42, [0, 2, 3, 4, 7]),
   (mkRat (-2) 45, [0, 2, 3, 5, 6])]

def sc675Part3 : RawPoly ℕ :=
  [(mkRat (-1) 48, [0, 2, 4, 4, 6]),
   (mkRat (-1) 50, [0, 2, 4, 5, 5]),
   (mkRat (-1) 7, [0, 2, 14]),
   (mkRat (10) 567, [0, 3, 3, 3, 7]),
   (mkRat (-1) 54, [0, 3, 3, 4, 6]),
   (mkRat (-2) 225, [0, 3, 3, 5, 5]),
   (mkRat (-1) 60, [0, 3, 4, 4, 5]),
   (mkRat (-4) 39, [0, 3, 13]),
   (mkRat (-1) 768, [0, 4, 4, 4, 4]),
   (mkRat (-1) 12, [0, 4, 12]),
   (mkRat (-4) 55, [0, 5, 11]),
   (mkRat (-1) 15, [0, 6, 10]),
   (mkRat (10) 63, [0, 7, 9]),
   (mkRat (-1) 32, [0, 8, 8]),
   (mkRat (-1) 10478160, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2]),
   (mkRat (-1) 340200, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4]),
   (mkRat (-1) 53460, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3]),
   (mkRat (-1) 50400, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2]),
   (mkRat (-1) 12600, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6]),
   (mkRat (-1) 2835, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5]),
   (mkRat (-1) 3402, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4]),
   (mkRat (-1) 1440, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4]),
   (mkRat (-1) 1620, [1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3]),
   (mkRat (-1) 720, [1, 1, 1, 1, 1, 1, 1, 1, 8])]

def sc675Part4 : RawPoly ℕ :=
  [(mkRat (-1) 1260, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3]),
   (mkRat (1) 98, [1, 1, 1, 1, 1, 1, 1, 2, 7]),
   (mkRat (-1) 315, [1, 1, 1, 1, 1, 1, 1, 3, 6]),
   (mkRat (-1) 350, [1, 1, 1, 1, 1, 1, 1, 4, 5]),
   (mkRat (-1) 8640, [1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2]),
   (mkRat (-1) 216, [1, 1, 1, 1, 1, 1, 2, 2, 6]),
   (mkRat (-1) 135, [1, 1, 1, 1, 1, 1, 2, 3, 5]),
   (mkRat (-1) 288, [1, 1, 1, 1, 1, 1, 2, 4, 4]),
   (mkRat (-1) 324, [1, 1, 1, 1, 1, 1, 3, 3, 4]),
   (mkRat (-1) 90, [1, 1, 1, 1, 1, 1, 10]),
   (mkRat (-1) 450, [1, 1, 1, 1, 1, 2, 2, 2, 5]),
   (mkRat (-1) 180, [1, 1, 1, 1, 1, 2, 2, 3, 4]),
   (mkRat (-2) 1215, [1, 1, 1, 1, 1, 2, 3, 3, 3]),
   (mkRat (-2) 135, [1, 1, 1, 1, 1, 2, 9]),
   (mkRat (-1) 90, [1, 1, 1, 1, 1, 3, 8]),
   (mkRat (1) 42, [1, 1, 1, 1, 1, 4, 7]),
   (mkRat (-2) 225, [1, 1, 1, 1, 1, 5, 6]),
   (mkRat (1) 2160, [1, 1, 1, 2, 2, 2, 2, 2, 3]),
   (mkRat (-5) 252, [1, 1, 1, 2, 2, 2, 7]),
   (mkRat (1) 54, [1, 1, 1, 2, 2, 3, 6]),
   (mkRat (1) 60, [1, 1, 1, 2, 2, 4, 5]),
   (mkRat (2) 135, [1, 1, 1, 2, 3, 3, 5]),
   (mkRat (1) 72, [1, 1, 1, 2, 3, 4, 4]),
   (mkRat (2) 33, [1, 1, 1, 2, 11])]

def sc675Part5 : RawPoly ℕ :=
  [(mkRat (1) 243, [1, 1, 1, 3, 3, 3, 4]),
   (mkRat (2) 45, [1, 1, 1, 3, 10]),
   (mkRat (1) 27, [1, 1, 1, 4, 9]),
   (mkRat (1) 30, [1, 1, 1, 5, 8]),
   (mkRat (-5) 63, [1, 1, 1, 6, 7]),
   (mkRat (1) 40320, [1, 1, 2, 2, 2, 2, 2, 2, 2]),
   (mkRat (1) 288, [1, 1, 2, 2, 2, 2, 6]),
   (mkRat (1) 90, [1, 1, 2, 2, 2, 3, 5]),
   (mkRat (1) 192, [1, 1, 2, 2, 2, 4, 4]),
   (mkRat (1) 72, [1, 1, 2, 2, 3, 3, 4]),
   (mkRat (1) 20, [1, 1, 2, 2, 10]),
   (mkRat (1) 486, [1, 1, 2, 3, 3, 3, 3]),
   (mkRat (2) 27, [1, 1, 2, 3, 9]),
   (mkRat (1) 16, [1, 1, 2, 4, 8]),
   (mkRat (-1) 7, [1, 1, 2, 5, 7]),
   (mkRat (1) 36, [1, 1, 2, 6, 6]),
   (mkRat (1) 36, [1, 1, 3, 3, 8]),
   (mkRat (-5) 42, [1, 1, 3, 4, 7]),
   (mkRat (2) 45, [1, 1, 3, 5, 6]),
   (mkRat (1) 48, [1, 1, 4, 4, 6]),
   (mkRat (1) 50, [1, 1, 4, 5, 5]),
   (mkRat (1) 7, [1, 1, 14]),
   (mkRat (-1) 5760, [2, 2, 2, 2, 2, 2, 4]),
   (mkRat (-1) 2160, [2, 2, 2, 2, 2, 3, 3])]

def sc675Part6 : RawPoly ℕ :=
  [(mkRat (-1) 192, [2, 2, 2, 2, 8]),
   (mkRat (5) 126, [2, 2, 2, 3, 7]),
   (mkRat (-1) 72, [2, 2, 2, 4, 6]),
   (mkRat (-1) 150, [2, 2, 2, 5, 5]),
   (mkRat (-1) 54, [2, 2, 3, 3, 6]),
   (mkRat (-1) 30, [2, 2, 3, 4, 5]),
   (mkRat (-1) 192, [2, 2, 4, 4, 4]),
   (mkRat (-1) 12, [2, 2, 12]),
   (mkRat (-4) 405, [2, 3, 3, 3, 5]),
   (mkRat (-1) 72, [2, 3, 3, 4, 4]),
   (mkRat (-4) 33, [2, 3, 11]),
   (mkRat (-1) 10, [2, 4, 10]),
   (mkRat (-4) 45, [2, 5, 9]),
   (mkRat (-1) 12, [2, 6, 8]),
   (mkRat (12) 49, [2, 7, 7]),
   (mkRat (-1) 486, [3, 3, 3, 3, 4]),
   (mkRat (-2) 45, [3, 3, 10]),
   (mkRat (-2) 27, [3, 4, 9]),
   (mkRat (-1) 15, [3, 5, 8]),
   (mkRat (10) 63, [3, 6, 7]),
   (mkRat (-1) 32, [4, 4, 8]),
   (mkRat (1) 7, [4, 5, 7]),
   (mkRat (-1) 36, [4, 6, 6]),
   (mkRat (-2) 75, [5, 5, 6])]

def sc675Part7 : RawPoly ℕ :=
  [(mkRat (-1) 4, [16])]

def sc675 : RawPoly ℕ :=
  [sc675Part0,
   sc675Part1,
   sc675Part2,
   sc675Part3,
   sc675Part4,
   sc675Part5,
   sc675Part6,
   sc675Part7].flatten

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc675_check :
    reduceTwo (prependC 1 sc291 ++ scaleR (-1) (prependC 0 sc292)) = sc675 := by
  decide +kernel

theorem sc675_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc675 = evRc a c (expWordR [1, 1, 7] (7)) := by
  rw [← sc675_check]
  exact expTwo_step _ _ hc 0 [1, 7] (7)
    sc291 sc292 (sc291_sound a c hc) (sc292_sound a c hc)

def sc676 : RawPoly ℕ :=
  []

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc676_check :
    reduceTwo (prependC 1 sc293 ++ scaleR (-1) (prependC 0 sc294)) = sc676 := by
  decide +kernel

theorem sc676_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc676 = evRc a c (expWordR [1, 2, 2] (-7)) := by
  rw [← sc676_check]
  exact expTwo_step _ _ hc 0 [2, 2] (-7)
    sc293 sc294 (sc293_sound a c hc) (sc294_sound a c hc)

def sc677 : RawPoly ℕ :=
  []

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc677_check :
    reduceTwo (prependC 1 sc294 ++ scaleR (-1) (prependC 0 sc295)) = sc677 := by
  decide +kernel

theorem sc677_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc677 = evRc a c (expWordR [1, 2, 2] (-6)) := by
  rw [← sc677_check]
  exact expTwo_step _ _ hc 0 [2, 2] (-6)
    sc294 sc295 (sc294_sound a c hc) (sc295_sound a c hc)

def sc678 : RawPoly ℕ :=
  [(-2, [0])]

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc678_check :
    reduceTwo (prependC 1 sc295 ++ scaleR (-1) (prependC 0 sc296)) = sc678 := by
  decide +kernel

theorem sc678_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc678 = evRc a c (expWordR [1, 2, 2] (-5)) := by
  rw [← sc678_check]
  exact expTwo_step _ _ hc 0 [2, 2] (-5)
    sc295 sc296 (sc295_sound a c hc) (sc296_sound a c hc)

def sc679 : RawPoly ℕ :=
  [(-2, [1])]

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc679_check :
    reduceTwo (prependC 1 sc296 ++ scaleR (-1) (prependC 0 sc297)) = sc679 := by
  decide +kernel

theorem sc679_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc679 = evRc a c (expWordR [1, 2, 2] (-4)) := by
  rw [← sc679_check]
  exact expTwo_step _ _ hc 0 [2, 2] (-4)
    sc296 sc297 (sc296_sound a c hc) (sc297_sound a c hc)

def sc680 : RawPoly ℕ :=
  [(2, [2])]

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc680_check :
    reduceTwo (prependC 1 sc297 ++ scaleR (-1) (prependC 0 sc298)) = sc680 := by
  decide +kernel

theorem sc680_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc680 = evRc a c (expWordR [1, 2, 2] (-3)) := by
  rw [← sc680_check]
  exact expTwo_step _ _ hc 0 [2, 2] (-3)
    sc297 sc298 (sc297_sound a c hc) (sc298_sound a c hc)

def sc681 : RawPoly ℕ :=
  [(1, [0, 1, 2]),
   (mkRat (2) 3, [1, 1, 1]),
   (mkRat (-4) 3, [3])]

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc681_check :
    reduceTwo (prependC 1 sc298 ++ scaleR (-1) (prependC 0 sc299)) = sc681 := by
  decide +kernel

theorem sc681_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc681 = evRc a c (expWordR [1, 2, 2] (-2)) := by
  rw [← sc681_check]
  exact expTwo_step _ _ hc 0 [2, 2] (-2)
    sc298 sc299 (sc298_sound a c hc) (sc299_sound a c hc)

def sc682 : RawPoly ℕ :=
  [(mkRat (1) 3, [0, 1, 1, 1, 1]),
   (mkRat (-2) 3, [0, 1, 3]),
   (mkRat (1) 2, [0, 2, 2]),
   (-1, [4])]

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc682_check :
    reduceTwo (prependC 1 sc299 ++ scaleR (-1) (prependC 0 sc300)) = sc682 := by
  decide +kernel

theorem sc682_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc682 = evRc a c (expWordR [1, 2, 2] (-1)) := by
  rw [← sc682_check]
  exact expTwo_step _ _ hc 0 [2, 2] (-1)
    sc299 sc300 (sc299_sound a c hc) (sc300_sound a c hc)

def sc683 : RawPoly ℕ :=
  [(mkRat (-1) 3, [0, 1, 1, 1, 2]),
   (mkRat (-1) 2, [0, 1, 4]),
   (mkRat (2) 3, [0, 2, 3]),
   (mkRat (1) 5, [1, 1, 1, 1, 1]),
   (mkRat (1) 2, [1, 2, 2]),
   (mkRat (-4) 5, [5])]

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc683_check :
    reduceTwo (prependC 1 sc300 ++ scaleR (-1) (prependC 0 sc301)) = sc683 := by
  decide +kernel

theorem sc683_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc683 = evRc a c (expWordR [1, 2, 2] (0)) := by
  rw [← sc683_check]
  exact expTwo_step _ _ hc 0 [2, 2] (0)
    sc300 sc301 (sc300_sound a c hc) (sc301_sound a c hc)

def sc684 : RawPoly ℕ :=
  [(mkRat (2) 45, [0, 1, 1, 1, 1, 1, 1]),
   (mkRat (2) 9, [0, 1, 1, 1, 3]),
   (mkRat (-2) 5, [0, 1, 5]),
   (mkRat (1) 2, [0, 2, 4]),
   (mkRat (-2) 9, [0, 3, 3]),
   (mkRat (-1) 3, [1, 1, 1, 1, 2]),
   (mkRat (2) 3, [1, 2, 3]),
   (mkRat (-1) 6, [2, 2, 2]),
   (mkRat (-2) 3, [6])]

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc684_check :
    reduceTwo (prependC 1 sc301 ++ scaleR (-1) (prependC 0 sc302)) = sc684 := by
  decide +kernel

theorem sc684_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc684 = evRc a c (expWordR [1, 2, 2] (1)) := by
  rw [← sc684_check]
  exact expTwo_step _ _ hc 0 [2, 2] (1)
    sc301 sc302 (sc301_sound a c hc) (sc302_sound a c hc)

def sc685 : RawPoly ℕ :=
  [(mkRat (-1) 10, [0, 1, 1, 1, 1, 1, 2]),
   (mkRat (1) 6, [0, 1, 1, 1, 4]),
   (mkRat (-1) 12, [0, 1, 2, 2, 2]),
   (mkRat (-1) 3, [0, 1, 6]),
   (mkRat (2) 5, [0, 2, 5]),
   (mkRat (-1) 3, [0, 3, 4]),
   (mkRat (1) 63, [1, 1, 1, 1, 1, 1, 1]),
   (mkRat (2) 9, [1, 1, 1, 1, 3]),
   (mkRat (-1) 6, [1, 1, 1, 2, 2]),
   (mkRat (1) 2, [1, 2, 4]),
   (mkRat (-2) 9, [1, 3, 3]),
   (mkRat (1) 3, [2, 2, 3]),
   (mkRat (-4) 7, [7])]

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc685_check :
    reduceTwo (prependC 1 sc302 ++ scaleR (-1) (prependC 0 sc303)) = sc685 := by
  decide +kernel

theorem sc685_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc685 = evRc a c (expWordR [1, 2, 2] (2)) := by
  rw [← sc685_check]
  exact expTwo_step _ _ hc 0 [2, 2] (2)
    sc302 sc303 (sc302_sound a c hc) (sc303_sound a c hc)

def sc686 : RawPoly ℕ :=
  [(mkRat (1) 420, [0, 1, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (1) 15, [0, 1, 1, 1, 1, 1, 3]),
   (mkRat (-1) 12, [0, 1, 1, 1, 1, 2, 2]),
   (mkRat (2) 15, [0, 1, 1, 1, 5]),
   (mkRat (1) 6, [0, 1, 2, 2, 3]),
   (mkRat (-2) 7, [0, 1, 7]),
   (mkRat (-5) 48, [0, 2, 2, 2, 2]),
   (mkRat (1) 3, [0, 2, 6]),
   (mkRat (-4) 15, [0, 3, 5]),
   (mkRat (-1) 8, [0, 4, 4]),
   (mkRat (-2) 45, [1, 1, 1, 1, 1, 1, 2]),
   (mkRat (1) 6, [1, 1, 1, 1, 4]),
   (mkRat (-2) 9, [1, 1, 1, 2, 3]),
   (mkRat (2) 5, [1, 2, 5]),
   (mkRat (-1) 3, [1, 3, 4]),
   (mkRat (1) 4, [2, 2, 4]),
   (mkRat (2) 9, [2, 3, 3]),
   (mkRat (-1) 2, [8])]

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc686_check :
    reduceTwo (prependC 1 sc303 ++ scaleR (-1) (prependC 0 sc304)) = sc686 := by
  decide +kernel

theorem sc686_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc686 = evRc a c (expWordR [1, 2, 2] (3)) := by
  rw [← sc686_check]
  exact expTwo_step _ _ hc 0 [2, 2] (3)
    sc303 sc304 (sc303_sound a c hc) (sc304_sound a c hc)

def sc687Part0 : RawPoly ℕ :=
  [(mkRat (-1) 126, [0, 1, 1, 1, 1, 1, 1, 1, 2]),
   (mkRat (1) 20, [0, 1, 1, 1, 1, 1, 4]),
   (mkRat (-1) 9, [0, 1, 1, 1, 1, 2, 3]),
   (mkRat (1) 36, [0, 1, 1, 1, 2, 2, 2]),
   (mkRat (1) 9, [0, 1, 1, 1, 6]),
   (mkRat (1) 8, [0, 1, 2, 2, 4]),
   (mkRat (1) 9, [0, 1, 2, 3, 3]),
   (mkRat (-1) 4, [0, 1, 8]),
   (mkRat (-1) 18, [0, 2, 2, 2, 3]),
   (mkRat (2) 7, [0, 2, 7]),
   (mkRat (-2) 9, [0, 3, 6]),
   (mkRat (-1) 5, [0, 4, 5]),
   (mkRat (1) 1620, [1, 1, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (4) 135, [1, 1, 1, 1, 1, 1, 3]),
   (mkRat (-1) 20, [1, 1, 1, 1, 1, 2, 2]),
   (mkRat (2) 15, [1, 1, 1, 1, 5]),
   (mkRat (-1) 6, [1, 1, 1, 2, 4]),
   (mkRat (2) 27, [1, 1, 1, 3, 3]),
   (mkRat (-5) 48, [1, 2, 2, 2, 2]),
   (mkRat (1) 3, [1, 2, 6]),
   (mkRat (-4) 15, [1, 3, 5]),
   (mkRat (-1) 8, [1, 4, 4]),
   (mkRat (1) 5, [2, 2, 5]),
   (mkRat (1) 3, [2, 3, 4])]

def sc687Part1 : RawPoly ℕ :=
  [(mkRat (-4) 81, [3, 3, 3]),
   (mkRat (-4) 9, [9])]

def sc687 : RawPoly ℕ :=
  [sc687Part0,
   sc687Part1].flatten

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc687_check :
    reduceTwo (prependC 1 sc304 ++ scaleR (-1) (prependC 0 sc305)) = sc687 := by
  decide +kernel

theorem sc687_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc687 = evRc a c (expWordR [1, 2, 2] (4)) := by
  rw [← sc687_check]
  exact expTwo_step _ _ hc 0 [2, 2] (4)
    sc304 sc305 (sc304_sound a c hc) (sc305_sound a c hc)

def sc688Part0 : RawPoly ℕ :=
  [(mkRat (1) 14175, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (1) 189, [0, 1, 1, 1, 1, 1, 1, 1, 3]),
   (mkRat (-1) 90, [0, 1, 1, 1, 1, 1, 1, 2, 2]),
   (mkRat (1) 25, [0, 1, 1, 1, 1, 1, 5]),
   (mkRat (-1) 12, [0, 1, 1, 1, 1, 2, 4]),
   (mkRat (1) 27, [0, 1, 1, 1, 1, 3, 3]),
   (mkRat (-1) 18, [0, 1, 1, 1, 2, 2, 3]),
   (mkRat (2) 21, [0, 1, 1, 1, 7]),
   (mkRat (1) 10, [0, 1, 2, 2, 5]),
   (mkRat (1) 6, [0, 1, 2, 3, 4]),
   (mkRat (-2) 81, [0, 1, 3, 3, 3]),
   (mkRat (-2) 9, [0, 1, 9]),
   (mkRat (-1) 24, [0, 2, 2, 2, 4]),
   (mkRat (1) 18, [0, 2, 2, 3, 3]),
   (mkRat (1) 4, [0, 2, 8]),
   (mkRat (-4) 21, [0, 3, 7]),
   (mkRat (-1) 6, [0, 4, 6]),
   (mkRat (-2) 25, [0, 5, 5]),
   (mkRat (-1) 420, [1, 1, 1, 1, 1, 1, 1, 1, 2]),
   (mkRat (1) 45, [1, 1, 1, 1, 1, 1, 4]),
   (mkRat (-1) 15, [1, 1, 1, 1, 1, 2, 3]),
   (mkRat (1) 36, [1, 1, 1, 1, 2, 2, 2]),
   (mkRat (1) 9, [1, 1, 1, 1, 6]),
   (mkRat (-2) 15, [1, 1, 1, 2, 5])]

def sc688Part1 : RawPoly ℕ :=
  [(mkRat (1) 9, [1, 1, 1, 3, 4]),
   (mkRat (-1) 18, [1, 2, 2, 2, 3]),
   (mkRat (2) 7, [1, 2, 7]),
   (mkRat (-2) 9, [1, 3, 6]),
   (mkRat (-1) 5, [1, 4, 5]),
   (mkRat (-11) 240, [2, 2, 2, 2, 2]),
   (mkRat (1) 6, [2, 2, 6]),
   (mkRat (4) 15, [2, 3, 5]),
   (mkRat (1) 8, [2, 4, 4]),
   (mkRat (-1) 9, [3, 3, 4]),
   (mkRat (-2) 5, [10])]

def sc688 : RawPoly ℕ :=
  [sc688Part0,
   sc688Part1].flatten

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc688_check :
    reduceTwo (prependC 1 sc305 ++ scaleR (-1) (prependC 0 sc306)) = sc688 := by
  decide +kernel

theorem sc688_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc688 = evRc a c (expWordR [1, 2, 2] (5)) := by
  rw [← sc688_check]
  exact expTwo_step _ _ hc 0 [2, 2] (5)
    sc305 sc306 (sc305_sound a c hc) (sc306_sound a c hc)

def sc689Part0 : RawPoly ℕ :=
  [(mkRat (-1) 3240, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2]),
   (mkRat (1) 252, [0, 1, 1, 1, 1, 1, 1, 1, 4]),
   (mkRat (-2) 135, [0, 1, 1, 1, 1, 1, 1, 2, 3]),
   (mkRat (1) 120, [0, 1, 1, 1, 1, 1, 2, 2, 2]),
   (mkRat (1) 30, [0, 1, 1, 1, 1, 1, 6]),
   (mkRat (-1) 15, [0, 1, 1, 1, 1, 2, 5]),
   (mkRat (1) 18, [0, 1, 1, 1, 1, 3, 4]),
   (mkRat (-1) 24, [0, 1, 1, 1, 2, 2, 4]),
   (mkRat (-1) 27, [0, 1, 1, 1, 2, 3, 3]),
   (mkRat (1) 12, [0, 1, 1, 1, 8]),
   (mkRat (-11) 480, [0, 1, 2, 2, 2, 2, 2]),
   (mkRat (1) 12, [0, 1, 2, 2, 6]),
   (mkRat (2) 15, [0, 1, 2, 3, 5]),
   (mkRat (1) 16, [0, 1, 2, 4, 4]),
   (mkRat (-1) 18, [0, 1, 3, 3, 4]),
   (mkRat (-1) 5, [0, 1, 10]),
   (mkRat (-1) 30, [0, 2, 2, 2, 5]),
   (mkRat (1) 12, [0, 2, 2, 3, 4]),
   (mkRat (2) 81, [0, 2, 3, 3, 3]),
   (mkRat (2) 9, [0, 2, 9]),
   (mkRat (-1) 6, [0, 3, 8]),
   (mkRat (-1) 7, [0, 4, 7]),
   (mkRat (-2) 15, [0, 5, 6]),
   (mkRat (1) 69300, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])]

def sc689Part1 : RawPoly ℕ :=
  [(mkRat (1) 630, [1, 1, 1, 1, 1, 1, 1, 1, 3]),
   (mkRat (-1) 252, [1, 1, 1, 1, 1, 1, 1, 2, 2]),
   (mkRat (4) 225, [1, 1, 1, 1, 1, 1, 5]),
   (mkRat (-1) 20, [1, 1, 1, 1, 1, 2, 4]),
   (mkRat (1) 45, [1, 1, 1, 1, 1, 3, 3]),
   (mkRat (-1) 18, [1, 1, 1, 1, 2, 2, 3]),
   (mkRat (2) 21, [1, 1, 1, 1, 7]),
   (mkRat (5) 144, [1, 1, 1, 2, 2, 2, 2]),
   (mkRat (-1) 9, [1, 1, 1, 2, 6]),
   (mkRat (4) 45, [1, 1, 1, 3, 5]),
   (mkRat (1) 24, [1, 1, 1, 4, 4]),
   (mkRat (-1) 24, [1, 2, 2, 2, 4]),
   (mkRat (1) 18, [1, 2, 2, 3, 3]),
   (mkRat (1) 4, [1, 2, 8]),
   (mkRat (-4) 21, [1, 3, 7]),
   (mkRat (-1) 6, [1, 4, 6]),
   (mkRat (-2) 25, [1, 5, 5]),
   (mkRat (-5) 72, [2, 2, 2, 2, 3]),
   (mkRat (1) 7, [2, 2, 7]),
   (mkRat (2) 9, [2, 3, 6]),
   (mkRat (1) 5, [2, 4, 5]),
   (mkRat (-4) 45, [3, 3, 5]),
   (mkRat (-1) 12, [3, 4, 4]),
   (mkRat (-4) 11, [11])]

def sc689 : RawPoly ℕ :=
  [sc689Part0,
   sc689Part1].flatten

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc689_check :
    reduceTwo (prependC 1 sc306 ++ scaleR (-1) (prependC 0 sc307)) = sc689 := by
  decide +kernel

theorem sc689_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc689 = evRc a c (expWordR [1, 2, 2] (6)) := by
  rw [← sc689_check]
  exact expTwo_step _ _ hc 0 [2, 2] (6)
    sc306 sc307 (sc306_sound a c hc) (sc307_sound a c hc)

def sc690Part0 : RawPoly ℕ :=
  [(mkRat (1) 748440, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (1) 4860, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3]),
   (mkRat (-1) 1680, [0, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2]),
   (mkRat (1) 315, [0, 1, 1, 1, 1, 1, 1, 1, 5]),
   (mkRat (-1) 90, [0, 1, 1, 1, 1, 1, 1, 2, 4]),
   (mkRat (2) 405, [0, 1, 1, 1, 1, 1, 1, 3, 3]),
   (mkRat (-1) 60, [0, 1, 1, 1, 1, 1, 2, 2, 3]),
   (mkRat (1) 35, [0, 1, 1, 1, 1, 1, 7]),
   (mkRat (5) 288, [0, 1, 1, 1, 1, 2, 2, 2, 2]),
   (mkRat (-1) 18, [0, 1, 1, 1, 1, 2, 6]),
   (mkRat (2) 45, [0, 1, 1, 1, 1, 3, 5]),
   (mkRat (1) 48, [0, 1, 1, 1, 1, 4, 4]),
   (mkRat (-1) 30, [0, 1, 1, 1, 2, 2, 5]),
   (mkRat (-1) 18, [0, 1, 1, 1, 2, 3, 4]),
   (mkRat (2) 243, [0, 1, 1, 1, 3, 3, 3]),
   (mkRat (2) 27, [0, 1, 1, 1, 9]),
   (mkRat (-5) 144, [0, 1, 2, 2, 2, 2, 3]),
   (mkRat (1) 14, [0, 1, 2, 2, 7]),
   (mkRat (1) 9, [0, 1, 2, 3, 6]),
   (mkRat (1) 10, [0, 1, 2, 4, 5]),
   (mkRat (-2) 45, [0, 1, 3, 3, 5]),
   (mkRat (-1) 24, [0, 1, 3, 4, 4]),
   (mkRat (-2) 11, [0, 1, 11]),
   (mkRat (-19) 2880, [0, 2, 2, 2, 2, 2, 2])]

def sc690Part1 : RawPoly ℕ :=
  [(mkRat (-1) 36, [0, 2, 2, 2, 6]),
   (mkRat (1) 15, [0, 2, 2, 3, 5]),
   (mkRat (1) 32, [0, 2, 2, 4, 4]),
   (mkRat (1) 18, [0, 2, 3, 3, 4]),
   (mkRat (1) 5, [0, 2, 10]),
   (mkRat (-1) 243, [0, 3, 3, 3, 3]),
   (mkRat (-4) 27, [0, 3, 9]),
   (mkRat (-1) 8, [0, 4, 8]),
   (mkRat (-4) 35, [0, 5, 7]),
   (mkRat (-1) 18, [0, 6, 6]),
   (mkRat (-1) 14175, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2]),
   (mkRat (1) 840, [1, 1, 1, 1, 1, 1, 1, 1, 4]),
   (mkRat (-1) 189, [1, 1, 1, 1, 1, 1, 1, 2, 3]),
   (mkRat (1) 270, [1, 1, 1, 1, 1, 1, 2, 2, 2]),
   (mkRat (2) 135, [1, 1, 1, 1, 1, 1, 6]),
   (mkRat (-1) 25, [1, 1, 1, 1, 1, 2, 5]),
   (mkRat (1) 30, [1, 1, 1, 1, 1, 3, 4]),
   (mkRat (-1) 24, [1, 1, 1, 1, 2, 2, 4]),
   (mkRat (-1) 27, [1, 1, 1, 1, 2, 3, 3]),
   (mkRat (1) 12, [1, 1, 1, 1, 8]),
   (mkRat (1) 54, [1, 1, 1, 2, 2, 2, 3]),
   (mkRat (-2) 21, [1, 1, 1, 2, 7]),
   (mkRat (2) 27, [1, 1, 1, 3, 6]),
   (mkRat (1) 15, [1, 1, 1, 4, 5])]

def sc690Part2 : RawPoly ℕ :=
  [(mkRat (-1) 30, [1, 2, 2, 2, 5]),
   (mkRat (1) 12, [1, 2, 2, 3, 4]),
   (mkRat (2) 81, [1, 2, 3, 3, 3]),
   (mkRat (2) 9, [1, 2, 9]),
   (mkRat (-1) 6, [1, 3, 8]),
   (mkRat (-1) 7, [1, 4, 7]),
   (mkRat (-2) 15, [1, 5, 6]),
   (mkRat (-5) 96, [2, 2, 2, 2, 4]),
   (mkRat (-1) 54, [2, 2, 2, 3, 3]),
   (mkRat (1) 8, [2, 2, 8]),
   (mkRat (4) 21, [2, 3, 7]),
   (mkRat (1) 6, [2, 4, 6]),
   (mkRat (2) 25, [2, 5, 5]),
   (mkRat (-2) 27, [3, 3, 6]),
   (mkRat (-2) 15, [3, 4, 5]),
   (mkRat (-1) 48, [4, 4, 4]),
   (mkRat (-1) 3, [12])]

def sc690 : RawPoly ℕ :=
  [sc690Part0,
   sc690Part1,
   sc690Part2].flatten

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc690_check :
    reduceTwo (prependC 1 sc307 ++ scaleR (-1) (prependC 0 sc308)) = sc690 := by
  decide +kernel

theorem sc690_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc690 = evRc a c (expWordR [1, 2, 2] (7)) := by
  rw [← sc690_check]
  exact expTwo_step _ _ hc 0 [2, 2] (7)
    sc307 sc308 (sc307_sound a c hc) (sc308_sound a c hc)

def sc691Part0 : RawPoly ℕ :=
  [(mkRat (-1) 138600, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2]),
   (mkRat (1) 6480, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4]),
   (mkRat (-1) 1260, [0, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3]),
   (mkRat (1) 1512, [0, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2]),
   (mkRat (1) 378, [0, 1, 1, 1, 1, 1, 1, 1, 6]),
   (mkRat (-2) 225, [0, 1, 1, 1, 1, 1, 1, 2, 5]),
   (mkRat (1) 135, [0, 1, 1, 1, 1, 1, 1, 3, 4]),
   (mkRat (-1) 80, [0, 1, 1, 1, 1, 1, 2, 2, 4]),
   (mkRat (-1) 90, [0, 1, 1, 1, 1, 1, 2, 3, 3]),
   (mkRat (1) 40, [0, 1, 1, 1, 1, 1, 8]),
   (mkRat (1) 108, [0, 1, 1, 1, 1, 2, 2, 2, 3]),
   (mkRat (-1) 21, [0, 1, 1, 1, 1, 2, 7]),
   (mkRat (1) 27, [0, 1, 1, 1, 1, 3, 6]),
   (mkRat (1) 30, [0, 1, 1, 1, 1, 4, 5]),
   (mkRat (11) 1440, [0, 1, 1, 1, 2, 2, 2, 2, 2]),
   (mkRat (-1) 36, [0, 1, 1, 1, 2, 2, 6]),
   (mkRat (-2) 45, [0, 1, 1, 1, 2, 3, 5]),
   (mkRat (-1) 48, [0, 1, 1, 1, 2, 4, 4]),
   (mkRat (1) 54, [0, 1, 1, 1, 3, 3, 4]),
   (mkRat (1) 15, [0, 1, 1, 1, 10]),
   (mkRat (-5) 192, [0, 1, 2, 2, 2, 2, 4]),
   (mkRat (-1) 108, [0, 1, 2, 2, 2, 3, 3]),
   (mkRat (1) 16, [0, 1, 2, 2, 8]),
   (mkRat (2) 21, [0, 1, 2, 3, 7])]

def sc691Part1 : RawPoly ℕ :=
  [(mkRat (1) 12, [0, 1, 2, 4, 6]),
   (mkRat (1) 25, [0, 1, 2, 5, 5]),
   (mkRat (-1) 27, [0, 1, 3, 3, 6]),
   (mkRat (-1) 15, [0, 1, 3, 4, 5]),
   (mkRat (-1) 96, [0, 1, 4, 4, 4]),
   (mkRat (-1) 6, [0, 1, 12]),
   (mkRat (-11) 720, [0, 2, 2, 2, 2, 2, 3]),
   (mkRat (-1) 42, [0, 2, 2, 2, 7]),
   (mkRat (1) 18, [0, 2, 2, 3, 6]),
   (mkRat (1) 20, [0, 2, 2, 4, 5]),
   (mkRat (2) 45, [0, 2, 3, 3, 5]),
   (mkRat (1) 24, [0, 2, 3, 4, 4]),
   (mkRat (2) 11, [0, 2, 11]),
   (mkRat (-1) 81, [0, 3, 3, 3, 4]),
   (mkRat (-2) 15, [0, 3, 10]),
   (mkRat (-1) 9, [0, 4, 9]),
   (mkRat (-1) 10, [0, 5, 8]),
   (mkRat (-2) 21, [0, 6, 7]),
   (mkRat (1) 4422600, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (2) 42525, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3]),
   (mkRat (-1) 6480, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2]),
   (mkRat (1) 1050, [1, 1, 1, 1, 1, 1, 1, 1, 5]),
   (mkRat (-1) 252, [1, 1, 1, 1, 1, 1, 1, 2, 4]),
   (mkRat (1) 567, [1, 1, 1, 1, 1, 1, 1, 3, 3])]

def sc691Part2 : RawPoly ℕ :=
  [(mkRat (-1) 135, [1, 1, 1, 1, 1, 1, 2, 2, 3]),
   (mkRat (4) 315, [1, 1, 1, 1, 1, 1, 7]),
   (mkRat (1) 96, [1, 1, 1, 1, 1, 2, 2, 2, 2]),
   (mkRat (-1) 30, [1, 1, 1, 1, 1, 2, 6]),
   (mkRat (2) 75, [1, 1, 1, 1, 1, 3, 5]),
   (mkRat (1) 80, [1, 1, 1, 1, 1, 4, 4]),
   (mkRat (-1) 30, [1, 1, 1, 1, 2, 2, 5]),
   (mkRat (-1) 18, [1, 1, 1, 1, 2, 3, 4]),
   (mkRat (2) 243, [1, 1, 1, 1, 3, 3, 3]),
   (mkRat (2) 27, [1, 1, 1, 1, 9]),
   (mkRat (1) 72, [1, 1, 1, 2, 2, 2, 4]),
   (mkRat (-1) 54, [1, 1, 1, 2, 2, 3, 3]),
   (mkRat (-1) 12, [1, 1, 1, 2, 8]),
   (mkRat (4) 63, [1, 1, 1, 3, 7]),
   (mkRat (1) 18, [1, 1, 1, 4, 6]),
   (mkRat (2) 75, [1, 1, 1, 5, 5]),
   (mkRat (-19) 2880, [1, 2, 2, 2, 2, 2, 2]),
   (mkRat (-1) 36, [1, 2, 2, 2, 6]),
   (mkRat (1) 15, [1, 2, 2, 3, 5]),
   (mkRat (1) 32, [1, 2, 2, 4, 4]),
   (mkRat (1) 18, [1, 2, 3, 3, 4]),
   (mkRat (1) 5, [1, 2, 10]),
   (mkRat (-1) 243, [1, 3, 3, 3, 3]),
   (mkRat (-4) 27, [1, 3, 9])]

def sc691Part3 : RawPoly ℕ :=
  [(mkRat (-1) 8, [1, 4, 8]),
   (mkRat (-4) 35, [1, 5, 7]),
   (mkRat (-1) 18, [1, 6, 6]),
   (mkRat (-1) 24, [2, 2, 2, 2, 5]),
   (mkRat (-1) 36, [2, 2, 2, 3, 4]),
   (mkRat (1) 81, [2, 2, 3, 3, 3]),
   (mkRat (1) 9, [2, 2, 9]),
   (mkRat (1) 6, [2, 3, 8]),
   (mkRat (1) 7, [2, 4, 7]),
   (mkRat (2) 15, [2, 5, 6]),
   (mkRat (-4) 63, [3, 3, 7]),
   (mkRat (-1) 9, [3, 4, 6]),
   (mkRat (-4) 75, [3, 5, 5]),
   (mkRat (-1) 20, [4, 4, 5]),
   (mkRat (-4) 13, [13])]

def sc691 : RawPoly ℕ :=
  [sc691Part0,
   sc691Part1,
   sc691Part2,
   sc691Part3].flatten

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc691_check :
    reduceTwo (prependC 1 sc308 ++ scaleR (-1) (prependC 0 sc309)) = sc691 := by
  decide +kernel

theorem sc691_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc691 = evRc a c (expWordR [1, 2, 2] (8)) := by
  rw [← sc691_check]
  exact expTwo_step _ _ hc 0 [2, 2] (8)
    sc308 sc309 (sc308_sound a c hc) (sc309_sound a c hc)

def sc692Part0 : RawPoly ℕ :=
  [(mkRat (1) 56756700, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (1) 207900, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3]),
   (mkRat (-1) 56700, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2]),
   (mkRat (1) 8100, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5]),
   (mkRat (-1) 1680, [0, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4]),
   (mkRat (1) 3780, [0, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3]),
   (mkRat (-1) 756, [0, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3]),
   (mkRat (1) 441, [0, 1, 1, 1, 1, 1, 1, 1, 7]),
   (mkRat (1) 432, [0, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2]),
   (mkRat (-1) 135, [0, 1, 1, 1, 1, 1, 1, 2, 6]),
   (mkRat (4) 675, [0, 1, 1, 1, 1, 1, 1, 3, 5]),
   (mkRat (1) 360, [0, 1, 1, 1, 1, 1, 1, 4, 4]),
   (mkRat (-1) 100, [0, 1, 1, 1, 1, 1, 2, 2, 5]),
   (mkRat (-1) 60, [0, 1, 1, 1, 1, 1, 2, 3, 4]),
   (mkRat (1) 405, [0, 1, 1, 1, 1, 1, 3, 3, 3]),
   (mkRat (1) 45, [0, 1, 1, 1, 1, 1, 9]),
   (mkRat (1) 144, [0, 1, 1, 1, 1, 2, 2, 2, 4]),
   (mkRat (-1) 108, [0, 1, 1, 1, 1, 2, 2, 3, 3]),
   (mkRat (-1) 24, [0, 1, 1, 1, 1, 2, 8]),
   (mkRat (2) 63, [0, 1, 1, 1, 1, 3, 7]),
   (mkRat (1) 36, [0, 1, 1, 1, 1, 4, 6]),
   (mkRat (1) 75, [0, 1, 1, 1, 1, 5, 5]),
   (mkRat (5) 432, [0, 1, 1, 1, 2, 2, 2, 2, 3]),
   (mkRat (-1) 42, [0, 1, 1, 1, 2, 2, 7])]

def sc692Part1 : RawPoly ℕ :=
  [(mkRat (-1) 27, [0, 1, 1, 1, 2, 3, 6]),
   (mkRat (-1) 30, [0, 1, 1, 1, 2, 4, 5]),
   (mkRat (2) 135, [0, 1, 1, 1, 3, 3, 5]),
   (mkRat (1) 72, [0, 1, 1, 1, 3, 4, 4]),
   (mkRat (2) 33, [0, 1, 1, 1, 11]),
   (mkRat (-1) 48, [0, 1, 2, 2, 2, 2, 5]),
   (mkRat (-1) 72, [0, 1, 2, 2, 2, 3, 4]),
   (mkRat (1) 162, [0, 1, 2, 2, 3, 3, 3]),
   (mkRat (1) 18, [0, 1, 2, 2, 9]),
   (mkRat (1) 12, [0, 1, 2, 3, 8]),
   (mkRat (1) 14, [0, 1, 2, 4, 7]),
   (mkRat (1) 15, [0, 1, 2, 5, 6]),
   (mkRat (-2) 63, [0, 1, 3, 3, 7]),
   (mkRat (-1) 18, [0, 1, 3, 4, 6]),
   (mkRat (-2) 75, [0, 1, 3, 5, 5]),
   (mkRat (-1) 40, [0, 1, 4, 4, 5]),
   (mkRat (-2) 13, [0, 1, 13]),
   (mkRat (-11) 960, [0, 2, 2, 2, 2, 2, 4]),
   (mkRat (-5) 432, [0, 2, 2, 2, 2, 3, 3]),
   (mkRat (-1) 48, [0, 2, 2, 2, 8]),
   (mkRat (1) 21, [0, 2, 2, 3, 7]),
   (mkRat (1) 24, [0, 2, 2, 4, 6]),
   (mkRat (1) 50, [0, 2, 2, 5, 5]),
   (mkRat (1) 27, [0, 2, 3, 3, 6])]

def sc692Part2 : RawPoly ℕ :=
  [(mkRat (1) 15, [0, 2, 3, 4, 5]),
   (mkRat (1) 96, [0, 2, 4, 4, 4]),
   (mkRat (1) 6, [0, 2, 12]),
   (mkRat (-4) 405, [0, 3, 3, 3, 5]),
   (mkRat (-1) 72, [0, 3, 3, 4, 4]),
   (mkRat (-4) 33, [0, 3, 11]),
   (mkRat (-1) 10, [0, 4, 10]),
   (mkRat (-4) 45, [0, 5, 9]),
   (mkRat (-1) 12, [0, 6, 8]),
   (mkRat (-2) 49, [0, 7, 7]),
   (mkRat (-1) 748440, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2]),
   (mkRat (1) 28350, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4]),
   (mkRat (-1) 4860, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3]),
   (mkRat (1) 5040, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2]),
   (mkRat (1) 1260, [1, 1, 1, 1, 1, 1, 1, 1, 6]),
   (mkRat (-1) 315, [1, 1, 1, 1, 1, 1, 1, 2, 5]),
   (mkRat (1) 378, [1, 1, 1, 1, 1, 1, 1, 3, 4]),
   (mkRat (-1) 180, [1, 1, 1, 1, 1, 1, 2, 2, 4]),
   (mkRat (-2) 405, [1, 1, 1, 1, 1, 1, 2, 3, 3]),
   (mkRat (1) 90, [1, 1, 1, 1, 1, 1, 8]),
   (mkRat (1) 180, [1, 1, 1, 1, 1, 2, 2, 2, 3]),
   (mkRat (-1) 35, [1, 1, 1, 1, 1, 2, 7]),
   (mkRat (1) 45, [1, 1, 1, 1, 1, 3, 6]),
   (mkRat (1) 50, [1, 1, 1, 1, 1, 4, 5])]

def sc692Part3 : RawPoly ℕ :=
  [(mkRat (11) 1440, [1, 1, 1, 1, 2, 2, 2, 2, 2]),
   (mkRat (-1) 36, [1, 1, 1, 1, 2, 2, 6]),
   (mkRat (-2) 45, [1, 1, 1, 1, 2, 3, 5]),
   (mkRat (-1) 48, [1, 1, 1, 1, 2, 4, 4]),
   (mkRat (1) 54, [1, 1, 1, 1, 3, 3, 4]),
   (mkRat (1) 15, [1, 1, 1, 1, 10]),
   (mkRat (1) 90, [1, 1, 1, 2, 2, 2, 5]),
   (mkRat (-1) 36, [1, 1, 1, 2, 2, 3, 4]),
   (mkRat (-2) 243, [1, 1, 1, 2, 3, 3, 3]),
   (mkRat (-2) 27, [1, 1, 1, 2, 9]),
   (mkRat (1) 18, [1, 1, 1, 3, 8]),
   (mkRat (1) 21, [1, 1, 1, 4, 7]),
   (mkRat (2) 45, [1, 1, 1, 5, 6]),
   (mkRat (-11) 720, [1, 2, 2, 2, 2, 2, 3]),
   (mkRat (-1) 42, [1, 2, 2, 2, 7]),
   (mkRat (1) 18, [1, 2, 2, 3, 6]),
   (mkRat (1) 20, [1, 2, 2, 4, 5]),
   (mkRat (2) 45, [1, 2, 3, 3, 5]),
   (mkRat (1) 24, [1, 2, 3, 4, 4]),
   (mkRat (2) 11, [1, 2, 11]),
   (mkRat (-1) 81, [1, 3, 3, 3, 4]),
   (mkRat (-2) 15, [1, 3, 10]),
   (mkRat (-1) 9, [1, 4, 9]),
   (mkRat (-1) 10, [1, 5, 8])]

def sc692Part4 : RawPoly ℕ :=
  [(mkRat (-2) 21, [1, 6, 7]),
   (mkRat (-29) 20160, [2, 2, 2, 2, 2, 2, 2]),
   (mkRat (-5) 144, [2, 2, 2, 2, 6]),
   (mkRat (-1) 45, [2, 2, 2, 3, 5]),
   (mkRat (-1) 96, [2, 2, 2, 4, 4]),
   (mkRat (1) 36, [2, 2, 3, 3, 4]),
   (mkRat (1) 10, [2, 2, 10]),
   (mkRat (1) 243, [2, 3, 3, 3, 3]),
   (mkRat (4) 27, [2, 3, 9]),
   (mkRat (1) 8, [2, 4, 8]),
   (mkRat (4) 35, [2, 5, 7]),
   (mkRat (1) 18, [2, 6, 6]),
   (mkRat (-1) 18, [3, 3, 8]),
   (mkRat (-2) 21, [3, 4, 7]),
   (mkRat (-4) 45, [3, 5, 6]),
   (mkRat (-1) 24, [4, 4, 6]),
   (mkRat (-1) 25, [4, 5, 5]),
   (mkRat (-2) 7, [14])]

def sc692 : RawPoly ℕ :=
  [sc692Part0,
   sc692Part1,
   sc692Part2,
   sc692Part3,
   sc692Part4].flatten

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc692_check :
    reduceTwo (prependC 1 sc309 ++ scaleR (-1) (prependC 0 sc310)) = sc692 := by
  decide +kernel

theorem sc692_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc692 = evRc a c (expWordR [1, 2, 2] (9)) := by
  rw [← sc692_check]
  exact expTwo_step _ _ hc 0 [2, 2] (9)
    sc309 sc310 (sc309_sound a c hc) (sc310_sound a c hc)

def sc693Part0 : RawPoly ℕ :=
  [(mkRat (-1) 8845200, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2]),
   (mkRat (1) 277200, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4]),
   (mkRat (-1) 42525, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3]),
   (mkRat (1) 38880, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2]),
   (mkRat (1) 9720, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6]),
   (mkRat (-1) 2100, [0, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5]),
   (mkRat (1) 2520, [0, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4]),
   (mkRat (-1) 1008, [0, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4]),
   (mkRat (-1) 1134, [0, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3]),
   (mkRat (1) 504, [0, 1, 1, 1, 1, 1, 1, 1, 8]),
   (mkRat (1) 810, [0, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3]),
   (mkRat (-2) 315, [0, 1, 1, 1, 1, 1, 1, 2, 7]),
   (mkRat (2) 405, [0, 1, 1, 1, 1, 1, 1, 3, 6]),
   (mkRat (1) 225, [0, 1, 1, 1, 1, 1, 1, 4, 5]),
   (mkRat (11) 4800, [0, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2]),
   (mkRat (-1) 120, [0, 1, 1, 1, 1, 1, 2, 2, 6]),
   (mkRat (-1) 75, [0, 1, 1, 1, 1, 1, 2, 3, 5]),
   (mkRat (-1) 160, [0, 1, 1, 1, 1, 1, 2, 4, 4]),
   (mkRat (1) 180, [0, 1, 1, 1, 1, 1, 3, 3, 4]),
   (mkRat (1) 50, [0, 1, 1, 1, 1, 1, 10]),
   (mkRat (1) 180, [0, 1, 1, 1, 1, 2, 2, 2, 5]),
   (mkRat (-1) 72, [0, 1, 1, 1, 1, 2, 2, 3, 4]),
   (mkRat (-1) 243, [0, 1, 1, 1, 1, 2, 3, 3, 3]),
   (mkRat (-1) 27, [0, 1, 1, 1, 1, 2, 9])]

def sc693Part1 : RawPoly ℕ :=
  [(mkRat (1) 36, [0, 1, 1, 1, 1, 3, 8]),
   (mkRat (1) 42, [0, 1, 1, 1, 1, 4, 7]),
   (mkRat (1) 45, [0, 1, 1, 1, 1, 5, 6]),
   (mkRat (5) 576, [0, 1, 1, 1, 2, 2, 2, 2, 4]),
   (mkRat (1) 324, [0, 1, 1, 1, 2, 2, 2, 3, 3]),
   (mkRat (-1) 48, [0, 1, 1, 1, 2, 2, 8]),
   (mkRat (-2) 63, [0, 1, 1, 1, 2, 3, 7]),
   (mkRat (-1) 36, [0, 1, 1, 1, 2, 4, 6]),
   (mkRat (-1) 75, [0, 1, 1, 1, 2, 5, 5]),
   (mkRat (1) 81, [0, 1, 1, 1, 3, 3, 6]),
   (mkRat (1) 45, [0, 1, 1, 1, 3, 4, 5]),
   (mkRat (1) 288, [0, 1, 1, 1, 4, 4, 4]),
   (mkRat (1) 18, [0, 1, 1, 1, 12]),
   (mkRat (-29) 40320, [0, 1, 2, 2, 2, 2, 2, 2, 2]),
   (mkRat (-5) 288, [0, 1, 2, 2, 2, 2, 6]),
   (mkRat (-1) 90, [0, 1, 2, 2, 2, 3, 5]),
   (mkRat (-1) 192, [0, 1, 2, 2, 2, 4, 4]),
   (mkRat (1) 72, [0, 1, 2, 2, 3, 3, 4]),
   (mkRat (1) 20, [0, 1, 2, 2, 10]),
   (mkRat (1) 486, [0, 1, 2, 3, 3, 3, 3]),
   (mkRat (2) 27, [0, 1, 2, 3, 9]),
   (mkRat (1) 16, [0, 1, 2, 4, 8]),
   (mkRat (2) 35, [0, 1, 2, 5, 7]),
   (mkRat (1) 36, [0, 1, 2, 6, 6])]

def sc693Part2 : RawPoly ℕ :=
  [(mkRat (-1) 36, [0, 1, 3, 3, 8]),
   (mkRat (-1) 21, [0, 1, 3, 4, 7]),
   (mkRat (-2) 45, [0, 1, 3, 5, 6]),
   (mkRat (-1) 48, [0, 1, 4, 4, 6]),
   (mkRat (-1) 50, [0, 1, 4, 5, 5]),
   (mkRat (-1) 7, [0, 1, 14]),
   (mkRat (-11) 1200, [0, 2, 2, 2, 2, 2, 5]),
   (mkRat (-5) 288, [0, 2, 2, 2, 2, 3, 4]),
   (mkRat (-1) 486, [0, 2, 2, 2, 3, 3, 3]),
   (mkRat (-1) 54, [0, 2, 2, 2, 9]),
   (mkRat (1) 24, [0, 2, 2, 3, 8]),
   (mkRat (1) 28, [0, 2, 2, 4, 7]),
   (mkRat (1) 30, [0, 2, 2, 5, 6]),
   (mkRat (2) 63, [0, 2, 3, 3, 7]),
   (mkRat (1) 18, [0, 2, 3, 4, 6]),
   (mkRat (2) 75, [0, 2, 3, 5, 5]),
   (mkRat (1) 40, [0, 2, 4, 4, 5]),
   (mkRat (2) 13, [0, 2, 13]),
   (mkRat (-2) 243, [0, 3, 3, 3, 6]),
   (mkRat (-1) 45, [0, 3, 3, 4, 5]),
   (mkRat (-1) 144, [0, 3, 4, 4, 4]),
   (mkRat (-1) 9, [0, 3, 12]),
   (mkRat (-1) 11, [0, 4, 11]),
   (mkRat (-2) 25, [0, 5, 10])]

def sc693Part3 : RawPoly ℕ :=
  [(mkRat (-2) 27, [0, 6, 9]),
   (mkRat (-1) 14, [0, 7, 8]),
   (mkRat (1) 392931000, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (1) 1122660, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3]),
   (mkRat (-1) 277200, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2]),
   (mkRat (2) 70875, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5]),
   (mkRat (-1) 6480, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4]),
   (mkRat (1) 14580, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3]),
   (mkRat (-1) 2520, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3]),
   (mkRat (1) 1470, [1, 1, 1, 1, 1, 1, 1, 1, 7]),
   (mkRat (5) 6048, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2]),
   (mkRat (-1) 378, [1, 1, 1, 1, 1, 1, 1, 2, 6]),
   (mkRat (2) 945, [1, 1, 1, 1, 1, 1, 1, 3, 5]),
   (mkRat (1) 1008, [1, 1, 1, 1, 1, 1, 1, 4, 4]),
   (mkRat (-1) 225, [1, 1, 1, 1, 1, 1, 2, 2, 5]),
   (mkRat (-1) 135, [1, 1, 1, 1, 1, 1, 2, 3, 4]),
   (mkRat (4) 3645, [1, 1, 1, 1, 1, 1, 3, 3, 3]),
   (mkRat (4) 405, [1, 1, 1, 1, 1, 1, 9]),
   (mkRat (1) 240, [1, 1, 1, 1, 1, 2, 2, 2, 4]),
   (mkRat (-1) 180, [1, 1, 1, 1, 1, 2, 2, 3, 3]),
   (mkRat (-1) 40, [1, 1, 1, 1, 1, 2, 8]),
   (mkRat (2) 105, [1, 1, 1, 1, 1, 3, 7]),
   (mkRat (1) 60, [1, 1, 1, 1, 1, 4, 6]),
   (mkRat (1) 125, [1, 1, 1, 1, 1, 5, 5])]

def sc693Part4 : RawPoly ℕ :=
  [(mkRat (5) 432, [1, 1, 1, 1, 2, 2, 2, 2, 3]),
   (mkRat (-1) 42, [1, 1, 1, 1, 2, 2, 7]),
   (mkRat (-1) 27, [1, 1, 1, 1, 2, 3, 6]),
   (mkRat (-1) 30, [1, 1, 1, 1, 2, 4, 5]),
   (mkRat (2) 135, [1, 1, 1, 1, 3, 3, 5]),
   (mkRat (1) 72, [1, 1, 1, 1, 3, 4, 4]),
   (mkRat (2) 33, [1, 1, 1, 1, 11]),
   (mkRat (19) 8640, [1, 1, 1, 2, 2, 2, 2, 2, 2]),
   (mkRat (1) 108, [1, 1, 1, 2, 2, 2, 6]),
   (mkRat (-1) 45, [1, 1, 1, 2, 2, 3, 5]),
   (mkRat (-1) 96, [1, 1, 1, 2, 2, 4, 4]),
   (mkRat (-1) 54, [1, 1, 1, 2, 3, 3, 4]),
   (mkRat (-1) 15, [1, 1, 1, 2, 10]),
   (mkRat (1) 729, [1, 1, 1, 3, 3, 3, 3]),
   (mkRat (4) 81, [1, 1, 1, 3, 9]),
   (mkRat (1) 24, [1, 1, 1, 4, 8]),
   (mkRat (4) 105, [1, 1, 1, 5, 7]),
   (mkRat (1) 54, [1, 1, 1, 6, 6]),
   (mkRat (-11) 960, [1, 2, 2, 2, 2, 2, 4]),
   (mkRat (-5) 432, [1, 2, 2, 2, 2, 3, 3]),
   (mkRat (-1) 48, [1, 2, 2, 2, 8]),
   (mkRat (1) 21, [1, 2, 2, 3, 7]),
   (mkRat (1) 24, [1, 2, 2, 4, 6]),
   (mkRat (1) 50, [1, 2, 2, 5, 5])]

def sc693Part5 : RawPoly ℕ :=
  [(mkRat (1) 27, [1, 2, 3, 3, 6]),
   (mkRat (1) 15, [1, 2, 3, 4, 5]),
   (mkRat (1) 96, [1, 2, 4, 4, 4]),
   (mkRat (1) 6, [1, 2, 12]),
   (mkRat (-4) 405, [1, 3, 3, 3, 5]),
   (mkRat (-1) 72, [1, 3, 3, 4, 4]),
   (mkRat (-4) 33, [1, 3, 11]),
   (mkRat (-1) 10, [1, 4, 10]),
   (mkRat (-4) 45, [1, 5, 9]),
   (mkRat (-1) 12, [1, 6, 8]),
   (mkRat (-2) 49, [1, 7, 7]),
   (mkRat (-19) 4320, [2, 2, 2, 2, 2, 2, 3]),
   (mkRat (-5) 168, [2, 2, 2, 2, 7]),
   (mkRat (-1) 54, [2, 2, 2, 3, 6]),
   (mkRat (-1) 60, [2, 2, 2, 4, 5]),
   (mkRat (1) 45, [2, 2, 3, 3, 5]),
   (mkRat (1) 48, [2, 2, 3, 4, 4]),
   (mkRat (1) 11, [2, 2, 11]),
   (mkRat (1) 81, [2, 3, 3, 3, 4]),
   (mkRat (2) 15, [2, 3, 10]),
   (mkRat (1) 9, [2, 4, 9]),
   (mkRat (1) 10, [2, 5, 8]),
   (mkRat (2) 21, [2, 6, 7]),
   (mkRat (-2) 3645, [3, 3, 3, 3, 3])]

def sc693Part6 : RawPoly ℕ :=
  [(mkRat (-4) 81, [3, 3, 9]),
   (mkRat (-1) 12, [3, 4, 8]),
   (mkRat (-8) 105, [3, 5, 7]),
   (mkRat (-1) 27, [3, 6, 6]),
   (mkRat (-1) 28, [4, 4, 7]),
   (mkRat (-1) 15, [4, 5, 6]),
   (mkRat (-4) 375, [5, 5, 5]),
   (mkRat (-4) 15, [15])]

def sc693 : RawPoly ℕ :=
  [sc693Part0,
   sc693Part1,
   sc693Part2,
   sc693Part3,
   sc693Part4,
   sc693Part5,
   sc693Part6].flatten

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc693_check :
    reduceTwo (prependC 1 sc310 ++ scaleR (-1) (prependC 0 sc311)) = sc693 := by
  decide +kernel

theorem sc693_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc693 = evRc a c (expWordR [1, 2, 2] (10)) := by
  rw [← sc693_check]
  exact expTwo_step _ _ hc 0 [2, 2] (10)
    sc310 sc311 (sc310_sound a c hc) (sc311_sound a c hc)

def sc694Part0 : RawPoly ℕ :=
  [(mkRat (1) 5837832000, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (1) 13267800, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3]),
   (mkRat (-1) 2993760, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2]),
   (mkRat (1) 346500, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5]),
   (mkRat (-1) 56700, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4]),
   (mkRat (1) 127575, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3]),
   (mkRat (-1) 19440, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3]),
   (mkRat (1) 11340, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7]),
   (mkRat (1) 8064, [0, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2]),
   (mkRat (-1) 2520, [0, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6]),
   (mkRat (1) 3150, [0, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5]),
   (mkRat (1) 6720, [0, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4]),
   (mkRat (-1) 1260, [0, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5]),
   (mkRat (-1) 756, [0, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4]),
   (mkRat (1) 5103, [0, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3]),
   (mkRat (1) 567, [0, 1, 1, 1, 1, 1, 1, 1, 9]),
   (mkRat (1) 1080, [0, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4]),
   (mkRat (-1) 810, [0, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3]),
   (mkRat (-1) 180, [0, 1, 1, 1, 1, 1, 1, 2, 8]),
   (mkRat (4) 945, [0, 1, 1, 1, 1, 1, 1, 3, 7]),
   (mkRat (1) 270, [0, 1, 1, 1, 1, 1, 1, 4, 6]),
   (mkRat (2) 1125, [0, 1, 1, 1, 1, 1, 1, 5, 5]),
   (mkRat (1) 288, [0, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3]),
   (mkRat (-1) 140, [0, 1, 1, 1, 1, 1, 2, 2, 7])]

def sc694Part1 : RawPoly ℕ :=
  [(mkRat (-1) 90, [0, 1, 1, 1, 1, 1, 2, 3, 6]),
   (mkRat (-1) 100, [0, 1, 1, 1, 1, 1, 2, 4, 5]),
   (mkRat (1) 225, [0, 1, 1, 1, 1, 1, 3, 3, 5]),
   (mkRat (1) 240, [0, 1, 1, 1, 1, 1, 3, 4, 4]),
   (mkRat (1) 55, [0, 1, 1, 1, 1, 1, 11]),
   (mkRat (19) 17280, [0, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2]),
   (mkRat (1) 216, [0, 1, 1, 1, 1, 2, 2, 2, 6]),
   (mkRat (-1) 90, [0, 1, 1, 1, 1, 2, 2, 3, 5]),
   (mkRat (-1) 192, [0, 1, 1, 1, 1, 2, 2, 4, 4]),
   (mkRat (-1) 108, [0, 1, 1, 1, 1, 2, 3, 3, 4]),
   (mkRat (-1) 30, [0, 1, 1, 1, 1, 2, 10]),
   (mkRat (1) 1458, [0, 1, 1, 1, 1, 3, 3, 3, 3]),
   (mkRat (2) 81, [0, 1, 1, 1, 1, 3, 9]),
   (mkRat (1) 48, [0, 1, 1, 1, 1, 4, 8]),
   (mkRat (2) 105, [0, 1, 1, 1, 1, 5, 7]),
   (mkRat (1) 108, [0, 1, 1, 1, 1, 6, 6]),
   (mkRat (1) 144, [0, 1, 1, 1, 2, 2, 2, 2, 5]),
   (mkRat (1) 216, [0, 1, 1, 1, 2, 2, 2, 3, 4]),
   (mkRat (-1) 486, [0, 1, 1, 1, 2, 2, 3, 3, 3]),
   (mkRat (-1) 54, [0, 1, 1, 1, 2, 2, 9]),
   (mkRat (-1) 36, [0, 1, 1, 1, 2, 3, 8]),
   (mkRat (-1) 42, [0, 1, 1, 1, 2, 4, 7]),
   (mkRat (-1) 45, [0, 1, 1, 1, 2, 5, 6]),
   (mkRat (2) 189, [0, 1, 1, 1, 3, 3, 7])]

def sc694Part2 : RawPoly ℕ :=
  [(mkRat (1) 54, [0, 1, 1, 1, 3, 4, 6]),
   (mkRat (2) 225, [0, 1, 1, 1, 3, 5, 5]),
   (mkRat (1) 120, [0, 1, 1, 1, 4, 4, 5]),
   (mkRat (2) 39, [0, 1, 1, 1, 13]),
   (mkRat (-19) 8640, [0, 1, 2, 2, 2, 2, 2, 2, 3]),
   (mkRat (-5) 336, [0, 1, 2, 2, 2, 2, 7]),
   (mkRat (-1) 108, [0, 1, 2, 2, 2, 3, 6]),
   (mkRat (-1) 120, [0, 1, 2, 2, 2, 4, 5]),
   (mkRat (1) 90, [0, 1, 2, 2, 3, 3, 5]),
   (mkRat (1) 96, [0, 1, 2, 2, 3, 4, 4]),
   (mkRat (1) 22, [0, 1, 2, 2, 11]),
   (mkRat (1) 162, [0, 1, 2, 3, 3, 3, 4]),
   (mkRat (1) 15, [0, 1, 2, 3, 10]),
   (mkRat (1) 18, [0, 1, 2, 4, 9]),
   (mkRat (1) 20, [0, 1, 2, 5, 8]),
   (mkRat (1) 21, [0, 1, 2, 6, 7]),
   (mkRat (-1) 3645, [0, 1, 3, 3, 3, 3, 3]),
   (mkRat (-2) 81, [0, 1, 3, 3, 9]),
   (mkRat (-1) 24, [0, 1, 3, 4, 8]),
   (mkRat (-4) 105, [0, 1, 3, 5, 7]),
   (mkRat (-1) 54, [0, 1, 3, 6, 6]),
   (mkRat (-1) 56, [0, 1, 4, 4, 7]),
   (mkRat (-1) 30, [0, 1, 4, 5, 6]),
   (mkRat (-2) 375, [0, 1, 5, 5, 5])]

def sc694Part3 : RawPoly ℕ :=
  [(mkRat (-2) 15, [0, 1, 15]),
   (mkRat (-41) 322560, [0, 2, 2, 2, 2, 2, 2, 2, 2]),
   (mkRat (-11) 1440, [0, 2, 2, 2, 2, 2, 6]),
   (mkRat (-1) 72, [0, 2, 2, 2, 2, 3, 5]),
   (mkRat (-5) 768, [0, 2, 2, 2, 2, 4, 4]),
   (mkRat (-1) 216, [0, 2, 2, 2, 3, 3, 4]),
   (mkRat (-1) 60, [0, 2, 2, 2, 10]),
   (mkRat (1) 972, [0, 2, 2, 3, 3, 3, 3]),
   (mkRat (1) 27, [0, 2, 2, 3, 9]),
   (mkRat (1) 32, [0, 2, 2, 4, 8]),
   (mkRat (1) 35, [0, 2, 2, 5, 7]),
   (mkRat (1) 72, [0, 2, 2, 6, 6]),
   (mkRat (1) 36, [0, 2, 3, 3, 8]),
   (mkRat (1) 21, [0, 2, 3, 4, 7]),
   (mkRat (2) 45, [0, 2, 3, 5, 6]),
   (mkRat (1) 48, [0, 2, 4, 4, 6]),
   (mkRat (1) 50, [0, 2, 4, 5, 5]),
   (mkRat (1) 7, [0, 2, 14]),
   (mkRat (-4) 567, [0, 3, 3, 3, 7]),
   (mkRat (-1) 54, [0, 3, 3, 4, 6]),
   (mkRat (-2) 225, [0, 3, 3, 5, 5]),
   (mkRat (-1) 60, [0, 3, 4, 4, 5]),
   (mkRat (-4) 39, [0, 3, 13]),
   (mkRat (-1) 768, [0, 4, 4, 4, 4])]

def sc694Part4 : RawPoly ℕ :=
  [(mkRat (-1) 12, [0, 4, 12]),
   (mkRat (-4) 55, [0, 5, 11]),
   (mkRat (-1) 15, [0, 6, 10]),
   (mkRat (-4) 63, [0, 7, 9]),
   (mkRat (-1) 32, [0, 8, 8]),
   (mkRat (-1) 56756700, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2]),
   (mkRat (1) 1496880, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4]),
   (mkRat (-1) 207900, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3]),
   (mkRat (1) 170100, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2]),
   (mkRat (1) 42525, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6]),
   (mkRat (-1) 8100, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5]),
   (mkRat (1) 9720, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4]),
   (mkRat (-1) 3360, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4]),
   (mkRat (-1) 3780, [1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3]),
   (mkRat (1) 1680, [1, 1, 1, 1, 1, 1, 1, 1, 8]),
   (mkRat (1) 2268, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3]),
   (mkRat (-1) 441, [1, 1, 1, 1, 1, 1, 1, 2, 7]),
   (mkRat (1) 567, [1, 1, 1, 1, 1, 1, 1, 3, 6]),
   (mkRat (1) 630, [1, 1, 1, 1, 1, 1, 1, 4, 5]),
   (mkRat (11) 10800, [1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2]),
   (mkRat (-1) 270, [1, 1, 1, 1, 1, 1, 2, 2, 6]),
   (mkRat (-4) 675, [1, 1, 1, 1, 1, 1, 2, 3, 5]),
   (mkRat (-1) 360, [1, 1, 1, 1, 1, 1, 2, 4, 4]),
   (mkRat (1) 405, [1, 1, 1, 1, 1, 1, 3, 3, 4])]

def sc694Part5 : RawPoly ℕ :=
  [(mkRat (2) 225, [1, 1, 1, 1, 1, 1, 10]),
   (mkRat (1) 300, [1, 1, 1, 1, 1, 2, 2, 2, 5]),
   (mkRat (-1) 120, [1, 1, 1, 1, 1, 2, 2, 3, 4]),
   (mkRat (-1) 405, [1, 1, 1, 1, 1, 2, 3, 3, 3]),
   (mkRat (-1) 45, [1, 1, 1, 1, 1, 2, 9]),
   (mkRat (1) 60, [1, 1, 1, 1, 1, 3, 8]),
   (mkRat (1) 70, [1, 1, 1, 1, 1, 4, 7]),
   (mkRat (1) 75, [1, 1, 1, 1, 1, 5, 6]),
   (mkRat (5) 576, [1, 1, 1, 1, 2, 2, 2, 2, 4]),
   (mkRat (1) 324, [1, 1, 1, 1, 2, 2, 2, 3, 3]),
   (mkRat (-1) 48, [1, 1, 1, 1, 2, 2, 8]),
   (mkRat (-2) 63, [1, 1, 1, 1, 2, 3, 7]),
   (mkRat (-1) 36, [1, 1, 1, 1, 2, 4, 6]),
   (mkRat (-1) 75, [1, 1, 1, 1, 2, 5, 5]),
   (mkRat (1) 81, [1, 1, 1, 1, 3, 3, 6]),
   (mkRat (1) 45, [1, 1, 1, 1, 3, 4, 5]),
   (mkRat (1) 288, [1, 1, 1, 1, 4, 4, 4]),
   (mkRat (1) 18, [1, 1, 1, 1, 12]),
   (mkRat (11) 2160, [1, 1, 1, 2, 2, 2, 2, 2, 3]),
   (mkRat (1) 126, [1, 1, 1, 2, 2, 2, 7]),
   (mkRat (-1) 54, [1, 1, 1, 2, 2, 3, 6]),
   (mkRat (-1) 60, [1, 1, 1, 2, 2, 4, 5]),
   (mkRat (-2) 135, [1, 1, 1, 2, 3, 3, 5]),
   (mkRat (-1) 72, [1, 1, 1, 2, 3, 4, 4])]

def sc694Part6 : RawPoly ℕ :=
  [(mkRat (-2) 33, [1, 1, 1, 2, 11]),
   (mkRat (1) 243, [1, 1, 1, 3, 3, 3, 4]),
   (mkRat (2) 45, [1, 1, 1, 3, 10]),
   (mkRat (1) 27, [1, 1, 1, 4, 9]),
   (mkRat (1) 30, [1, 1, 1, 5, 8]),
   (mkRat (2) 63, [1, 1, 1, 6, 7]),
   (mkRat (-11) 1200, [1, 2, 2, 2, 2, 2, 5]),
   (mkRat (-5) 288, [1, 2, 2, 2, 2, 3, 4]),
   (mkRat (-1) 486, [1, 2, 2, 2, 3, 3, 3]),
   (mkRat (-1) 54, [1, 2, 2, 2, 9]),
   (mkRat (1) 24, [1, 2, 2, 3, 8]),
   (mkRat (1) 28, [1, 2, 2, 4, 7]),
   (mkRat (1) 30, [1, 2, 2, 5, 6]),
   (mkRat (2) 63, [1, 2, 3, 3, 7]),
   (mkRat (1) 18, [1, 2, 3, 4, 6]),
   (mkRat (2) 75, [1, 2, 3, 5, 5]),
   (mkRat (1) 40, [1, 2, 4, 4, 5]),
   (mkRat (2) 13, [1, 2, 13]),
   (mkRat (-2) 243, [1, 3, 3, 3, 6]),
   (mkRat (-1) 45, [1, 3, 3, 4, 5]),
   (mkRat (-1) 144, [1, 3, 4, 4, 4]),
   (mkRat (-1) 9, [1, 3, 12]),
   (mkRat (-1) 11, [1, 4, 11]),
   (mkRat (-2) 25, [1, 5, 10])]

def sc694Part7 : RawPoly ℕ :=
  [(mkRat (-2) 27, [1, 6, 9]),
   (mkRat (-1) 14, [1, 7, 8]),
   (mkRat (-19) 5760, [2, 2, 2, 2, 2, 2, 4]),
   (mkRat (-11) 2160, [2, 2, 2, 2, 2, 3, 3]),
   (mkRat (-5) 192, [2, 2, 2, 2, 8]),
   (mkRat (-1) 63, [2, 2, 2, 3, 7]),
   (mkRat (-1) 72, [2, 2, 2, 4, 6]),
   (mkRat (-1) 150, [2, 2, 2, 5, 5]),
   (mkRat (1) 54, [2, 2, 3, 3, 6]),
   (mkRat (1) 30, [2, 2, 3, 4, 5]),
   (mkRat (1) 192, [2, 2, 4, 4, 4]),
   (mkRat (1) 12, [2, 2, 12]),
   (mkRat (4) 405, [2, 3, 3, 3, 5]),
   (mkRat (1) 72, [2, 3, 3, 4, 4]),
   (mkRat (4) 33, [2, 3, 11]),
   (mkRat (1) 10, [2, 4, 10]),
   (mkRat (4) 45, [2, 5, 9]),
   (mkRat (1) 12, [2, 6, 8]),
   (mkRat (2) 49, [2, 7, 7]),
   (mkRat (-1) 486, [3, 3, 3, 3, 4]),
   (mkRat (-2) 45, [3, 3, 10]),
   (mkRat (-2) 27, [3, 4, 9]),
   (mkRat (-1) 15, [3, 5, 8]),
   (mkRat (-4) 63, [3, 6, 7])]

def sc694Part8 : RawPoly ℕ :=
  [(mkRat (-1) 32, [4, 4, 8]),
   (mkRat (-2) 35, [4, 5, 7]),
   (mkRat (-1) 36, [4, 6, 6]),
   (mkRat (-2) 75, [5, 5, 6]),
   (mkRat (-1) 4, [16])]

def sc694 : RawPoly ℕ :=
  [sc694Part0,
   sc694Part1,
   sc694Part2,
   sc694Part3,
   sc694Part4,
   sc694Part5,
   sc694Part6,
   sc694Part7,
   sc694Part8].flatten

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc694_check :
    reduceTwo (prependC 1 sc311 ++ scaleR (-1) (prependC 0 sc312)) = sc694 := by
  decide +kernel

theorem sc694_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc694 = evRc a c (expWordR [1, 2, 2] (11)) := by
  rw [← sc694_check]
  exact expTwo_step _ _ hc 0 [2, 2] (11)
    sc311 sc312 (sc311_sound a c hc) (sc312_sound a c hc)

def sc695 : RawPoly ℕ :=
  []

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc695_check :
    reduceTwo (prependC 1 sc313 ++ scaleR (-1) (prependC 0 sc314)) = sc695 := by
  decide +kernel

theorem sc695_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc695 = evRc a c (expWordR [1, 2, 3] (-7)) := by
  rw [← sc695_check]
  exact expTwo_step _ _ hc 0 [2, 3] (-7)
    sc313 sc314 (sc313_sound a c hc) (sc314_sound a c hc)

def sc696 : RawPoly ℕ :=
  [(-2, [0])]

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc696_check :
    reduceTwo (prependC 1 sc314 ++ scaleR (-1) (prependC 0 sc315)) = sc696 := by
  decide +kernel

theorem sc696_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc696 = evRc a c (expWordR [1, 2, 3] (-6)) := by
  rw [← sc696_check]
  exact expTwo_step _ _ hc 0 [2, 3] (-6)
    sc314 sc315 (sc314_sound a c hc) (sc315_sound a c hc)

def sc697 : RawPoly ℕ :=
  [(-2, [1])]

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc697_check :
    reduceTwo (prependC 1 sc315 ++ scaleR (-1) (prependC 0 sc316)) = sc697 := by
  decide +kernel

theorem sc697_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc697 = evRc a c (expWordR [1, 2, 3] (-5)) := by
  rw [← sc697_check]
  exact expTwo_step _ _ hc 0 [2, 3] (-5)
    sc315 sc316 (sc315_sound a c hc) (sc316_sound a c hc)

def sc698 : RawPoly ℕ :=
  []

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc698_check :
    reduceTwo (prependC 1 sc316 ++ scaleR (-1) (prependC 0 sc317)) = sc698 := by
  decide +kernel

theorem sc698_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc698 = evRc a c (expWordR [1, 2, 3] (-4)) := by
  rw [← sc698_check]
  exact expTwo_step _ _ hc 0 [2, 3] (-4)
    sc316 sc317 (sc316_sound a c hc) (sc317_sound a c hc)

def sc699 : RawPoly ℕ :=
  [(mkRat (2) 3, [1, 1, 1]),
   (mkRat (2) 3, [3])]

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc699_check :
    reduceTwo (prependC 1 sc317 ++ scaleR (-1) (prependC 0 sc318)) = sc699 := by
  decide +kernel

theorem sc699_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc699 = evRc a c (expWordR [1, 2, 3] (-3)) := by
  rw [← sc699_check]
  exact expTwo_step _ _ hc 0 [2, 3] (-3)
    sc317 sc318 (sc317_sound a c hc) (sc318_sound a c hc)

def sc700 : RawPoly ℕ :=
  [(mkRat (1) 3, [0, 1, 1, 1, 1]),
   (mkRat (1) 3, [0, 1, 3]),
   (mkRat (1) 2, [0, 2, 2]),
   (-1, [4])]

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc700_check :
    reduceTwo (prependC 1 sc318 ++ scaleR (-1) (prependC 0 sc319)) = sc700 := by
  decide +kernel

theorem sc700_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc700 = evRc a c (expWordR [1, 2, 3] (-2)) := by
  rw [← sc700_check]
  exact expTwo_step _ _ hc 0 [2, 3] (-2)
    sc318 sc319 (sc318_sound a c hc) (sc319_sound a c hc)

def sc701 : RawPoly ℕ :=
  [(mkRat (-1) 2, [0, 1, 4]),
   (mkRat (1) 5, [1, 1, 1, 1, 1]),
   (mkRat (1) 2, [1, 2, 2]),
   (mkRat (-4) 5, [5])]

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc701_check :
    reduceTwo (prependC 1 sc319 ++ scaleR (-1) (prependC 0 sc320)) = sc701 := by
  decide +kernel

theorem sc701_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc701 = evRc a c (expWordR [1, 2, 3] (-1)) := by
  rw [← sc701_check]
  exact expTwo_step _ _ hc 0 [2, 3] (-1)
    sc319 sc320 (sc319_sound a c hc) (sc320_sound a c hc)

def sc702 : RawPoly ℕ :=
  [(mkRat (2) 45, [0, 1, 1, 1, 1, 1, 1]),
   (mkRat (-1) 9, [0, 1, 1, 1, 3]),
   (mkRat (-2) 5, [0, 1, 5]),
   (mkRat (4) 9, [0, 3, 3]),
   (mkRat (1) 3, [2, 2, 2]),
   (mkRat (-2) 3, [6])]

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc702_check :
    reduceTwo (prependC 1 sc320 ++ scaleR (-1) (prependC 0 sc321)) = sc702 := by
  decide +kernel

theorem sc702_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc702 = evRc a c (expWordR [1, 2, 3] (0)) := by
  rw [← sc702_check]
  exact expTwo_step _ _ hc 0 [2, 3] (0)
    sc320 sc321 (sc320_sound a c hc) (sc321_sound a c hc)

def sc703 : RawPoly ℕ :=
  [(mkRat (1) 6, [0, 1, 1, 1, 4]),
   (mkRat (1) 6, [0, 1, 2, 2, 2]),
   (mkRat (-1) 3, [0, 1, 6]),
   (mkRat (1) 6, [0, 3, 4]),
   (mkRat (1) 63, [1, 1, 1, 1, 1, 1, 1]),
   (mkRat (-1) 9, [1, 1, 1, 1, 3]),
   (mkRat (-1) 6, [1, 1, 1, 2, 2]),
   (mkRat (4) 9, [1, 3, 3]),
   (mkRat (-1) 6, [2, 2, 3]),
   (mkRat (-4) 7, [7])]

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc703_check :
    reduceTwo (prependC 1 sc321 ++ scaleR (-1) (prependC 0 sc322)) = sc703 := by
  decide +kernel

theorem sc703_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc703 = evRc a c (expWordR [1, 2, 3] (1)) := by
  rw [← sc703_check]
  exact expTwo_step _ _ hc 0 [2, 3] (1)
    sc321 sc322 (sc321_sound a c hc) (sc322_sound a c hc)

def sc704 : RawPoly ℕ :=
  [(mkRat (1) 420, [0, 1, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (-1) 30, [0, 1, 1, 1, 1, 1, 3]),
   (mkRat (-1) 12, [0, 1, 1, 1, 1, 2, 2]),
   (mkRat (2) 15, [0, 1, 1, 1, 5]),
   (mkRat (-1) 12, [0, 1, 2, 2, 3]),
   (mkRat (-2) 7, [0, 1, 7]),
   (mkRat (1) 16, [0, 2, 2, 2, 2]),
   (mkRat (2) 15, [0, 3, 5]),
   (mkRat (-1) 8, [0, 4, 4]),
   (mkRat (1) 6, [1, 1, 1, 1, 4]),
   (mkRat (1) 6, [1, 3, 4]),
   (mkRat (1) 4, [2, 2, 4]),
   (mkRat (-1) 2, [8])]

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc704_check :
    reduceTwo (prependC 1 sc322 ++ scaleR (-1) (prependC 0 sc323)) = sc704 := by
  decide +kernel

theorem sc704_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc704 = evRc a c (expWordR [1, 2, 3] (2)) := by
  rw [← sc704_check]
  exact expTwo_step _ _ hc 0 [2, 3] (2)
    sc322 sc323 (sc322_sound a c hc) (sc323_sound a c hc)

def sc705 : RawPoly ℕ :=
  [(mkRat (1) 20, [0, 1, 1, 1, 1, 1, 4]),
   (mkRat (-1) 18, [0, 1, 1, 1, 2, 2, 2]),
   (mkRat (1) 9, [0, 1, 1, 1, 6]),
   (mkRat (1) 8, [0, 1, 2, 2, 4]),
   (mkRat (-1) 4, [0, 1, 8]),
   (mkRat (-1) 18, [0, 2, 2, 2, 3]),
   (mkRat (1) 9, [0, 3, 6]),
   (mkRat (-1) 5, [0, 4, 5]),
   (mkRat (1) 1620, [1, 1, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (-2) 135, [1, 1, 1, 1, 1, 1, 3]),
   (mkRat (-1) 20, [1, 1, 1, 1, 1, 2, 2]),
   (mkRat (2) 15, [1, 1, 1, 1, 5]),
   (mkRat (-4) 27, [1, 1, 1, 3, 3]),
   (mkRat (1) 16, [1, 2, 2, 2, 2]),
   (mkRat (2) 15, [1, 3, 5]),
   (mkRat (-1) 8, [1, 4, 4]),
   (mkRat (1) 5, [2, 2, 5]),
   (mkRat (14) 81, [3, 3, 3]),
   (mkRat (-4) 9, [9])]

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc705_check :
    reduceTwo (prependC 1 sc323 ++ scaleR (-1) (prependC 0 sc324)) = sc705 := by
  decide +kernel

theorem sc705_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc705 = evRc a c (expWordR [1, 2, 3] (3)) := by
  rw [← sc705_check]
  exact expTwo_step _ _ hc 0 [2, 3] (3)
    sc323 sc324 (sc323_sound a c hc) (sc324_sound a c hc)

def sc706Part0 : RawPoly ℕ :=
  [(mkRat (1) 14175, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (-1) 378, [0, 1, 1, 1, 1, 1, 1, 1, 3]),
   (mkRat (-1) 90, [0, 1, 1, 1, 1, 1, 1, 2, 2]),
   (mkRat (1) 25, [0, 1, 1, 1, 1, 1, 5]),
   (mkRat (-2) 27, [0, 1, 1, 1, 1, 3, 3]),
   (mkRat (1) 36, [0, 1, 1, 1, 2, 2, 3]),
   (mkRat (2) 21, [0, 1, 1, 1, 7]),
   (mkRat (1) 10, [0, 1, 2, 2, 5]),
   (mkRat (7) 81, [0, 1, 3, 3, 3]),
   (mkRat (-2) 9, [0, 1, 9]),
   (mkRat (1) 12, [0, 2, 2, 2, 4]),
   (mkRat (-1) 9, [0, 2, 2, 3, 3]),
   (mkRat (2) 21, [0, 3, 7]),
   (mkRat (-1) 6, [0, 4, 6]),
   (mkRat (-2) 25, [0, 5, 5]),
   (mkRat (1) 45, [1, 1, 1, 1, 1, 1, 4]),
   (mkRat (-1) 18, [1, 1, 1, 1, 2, 2, 2]),
   (mkRat (1) 9, [1, 1, 1, 1, 6]),
   (mkRat (-1) 18, [1, 1, 1, 3, 4]),
   (mkRat (-1) 18, [1, 2, 2, 2, 3]),
   (mkRat (1) 9, [1, 3, 6]),
   (mkRat (-1) 5, [1, 4, 5]),
   (mkRat (1) 60, [2, 2, 2, 2, 2]),
   (mkRat (1) 6, [2, 2, 6])]

def sc706Part1 : RawPoly ℕ :=
  [(mkRat (2) 9, [3, 3, 4]),
   (mkRat (-2) 5, [10])]

def sc706 : RawPoly ℕ :=
  [sc706Part0,
   sc706Part1].flatten

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc706_check :
    reduceTwo (prependC 1 sc324 ++ scaleR (-1) (prependC 0 sc325)) = sc706 := by
  decide +kernel

theorem sc706_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc706 = evRc a c (expWordR [1, 2, 3] (4)) := by
  rw [← sc706_check]
  exact expTwo_step _ _ hc 0 [2, 3] (4)
    sc324 sc325 (sc324_sound a c hc) (sc325_sound a c hc)

def sc707Part0 : RawPoly ℕ :=
  [(mkRat (1) 252, [0, 1, 1, 1, 1, 1, 1, 1, 4]),
   (mkRat (-1) 60, [0, 1, 1, 1, 1, 1, 2, 2, 2]),
   (mkRat (1) 30, [0, 1, 1, 1, 1, 1, 6]),
   (mkRat (-1) 36, [0, 1, 1, 1, 1, 3, 4]),
   (mkRat (-1) 24, [0, 1, 1, 1, 2, 2, 4]),
   (mkRat (1) 12, [0, 1, 1, 1, 8]),
   (mkRat (1) 120, [0, 1, 2, 2, 2, 2, 2]),
   (mkRat (1) 12, [0, 1, 2, 2, 6]),
   (mkRat (1) 9, [0, 1, 3, 3, 4]),
   (mkRat (-1) 5, [0, 1, 10]),
   (mkRat (1) 15, [0, 2, 2, 2, 5]),
   (mkRat (-1) 24, [0, 2, 2, 3, 4]),
   (mkRat (1) 12, [0, 3, 8]),
   (mkRat (-1) 7, [0, 4, 7]),
   (mkRat (-2) 15, [0, 5, 6]),
   (mkRat (1) 69300, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (-1) 1260, [1, 1, 1, 1, 1, 1, 1, 1, 3]),
   (mkRat (-1) 252, [1, 1, 1, 1, 1, 1, 1, 2, 2]),
   (mkRat (4) 225, [1, 1, 1, 1, 1, 1, 5]),
   (mkRat (-2) 45, [1, 1, 1, 1, 1, 3, 3]),
   (mkRat (1) 36, [1, 1, 1, 1, 2, 2, 3]),
   (mkRat (2) 21, [1, 1, 1, 1, 7]),
   (mkRat (-1) 48, [1, 1, 1, 2, 2, 2, 2]),
   (mkRat (-2) 45, [1, 1, 1, 3, 5])]

def sc707Part1 : RawPoly ℕ :=
  [(mkRat (1) 24, [1, 1, 1, 4, 4]),
   (mkRat (1) 12, [1, 2, 2, 2, 4]),
   (mkRat (-1) 9, [1, 2, 2, 3, 3]),
   (mkRat (2) 21, [1, 3, 7]),
   (mkRat (-1) 6, [1, 4, 6]),
   (mkRat (-2) 25, [1, 5, 5]),
   (mkRat (-1) 48, [2, 2, 2, 2, 3]),
   (mkRat (1) 7, [2, 2, 7]),
   (mkRat (8) 45, [3, 3, 5]),
   (mkRat (1) 24, [3, 4, 4]),
   (mkRat (-4) 11, [11])]

def sc707 : RawPoly ℕ :=
  [sc707Part0,
   sc707Part1].flatten

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc707_check :
    reduceTwo (prependC 1 sc325 ++ scaleR (-1) (prependC 0 sc326)) = sc707 := by
  decide +kernel

theorem sc707_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc707 = evRc a c (expWordR [1, 2, 3] (5)) := by
  rw [← sc707_check]
  exact expTwo_step _ _ hc 0 [2, 3] (5)
    sc325 sc326 (sc325_sound a c hc) (sc326_sound a c hc)

def sc708Part0 : RawPoly ℕ :=
  [(mkRat (1) 748440, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (-1) 9720, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3]),
   (mkRat (-1) 1680, [0, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2]),
   (mkRat (1) 315, [0, 1, 1, 1, 1, 1, 1, 1, 5]),
   (mkRat (-4) 405, [0, 1, 1, 1, 1, 1, 1, 3, 3]),
   (mkRat (1) 120, [0, 1, 1, 1, 1, 1, 2, 2, 3]),
   (mkRat (1) 35, [0, 1, 1, 1, 1, 1, 7]),
   (mkRat (-1) 96, [0, 1, 1, 1, 1, 2, 2, 2, 2]),
   (mkRat (-1) 45, [0, 1, 1, 1, 1, 3, 5]),
   (mkRat (1) 48, [0, 1, 1, 1, 1, 4, 4]),
   (mkRat (-1) 30, [0, 1, 1, 1, 2, 2, 5]),
   (mkRat (-7) 243, [0, 1, 1, 1, 3, 3, 3]),
   (mkRat (2) 27, [0, 1, 1, 1, 9]),
   (mkRat (-1) 96, [0, 1, 2, 2, 2, 2, 3]),
   (mkRat (1) 14, [0, 1, 2, 2, 7]),
   (mkRat (4) 45, [0, 1, 3, 3, 5]),
   (mkRat (1) 48, [0, 1, 3, 4, 4]),
   (mkRat (-2) 11, [0, 1, 11]),
   (mkRat (1) 576, [0, 2, 2, 2, 2, 2, 2]),
   (mkRat (1) 18, [0, 2, 2, 2, 6]),
   (mkRat (-1) 30, [0, 2, 2, 3, 5]),
   (mkRat (1) 32, [0, 2, 2, 4, 4]),
   (mkRat (5) 243, [0, 3, 3, 3, 3]),
   (mkRat (2) 27, [0, 3, 9])]

def sc708Part1 : RawPoly ℕ :=
  [(mkRat (-1) 8, [0, 4, 8]),
   (mkRat (-4) 35, [0, 5, 7]),
   (mkRat (-1) 18, [0, 6, 6]),
   (mkRat (1) 840, [1, 1, 1, 1, 1, 1, 1, 1, 4]),
   (mkRat (-1) 135, [1, 1, 1, 1, 1, 1, 2, 2, 2]),
   (mkRat (2) 135, [1, 1, 1, 1, 1, 1, 6]),
   (mkRat (-1) 60, [1, 1, 1, 1, 1, 3, 4]),
   (mkRat (-1) 24, [1, 1, 1, 1, 2, 2, 4]),
   (mkRat (1) 12, [1, 1, 1, 1, 8]),
   (mkRat (1) 54, [1, 1, 1, 2, 2, 2, 3]),
   (mkRat (-1) 27, [1, 1, 1, 3, 6]),
   (mkRat (1) 15, [1, 1, 1, 4, 5]),
   (mkRat (1) 15, [1, 2, 2, 2, 5]),
   (mkRat (-1) 24, [1, 2, 2, 3, 4]),
   (mkRat (1) 12, [1, 3, 8]),
   (mkRat (-1) 7, [1, 4, 7]),
   (mkRat (-2) 15, [1, 5, 6]),
   (mkRat (1) 32, [2, 2, 2, 2, 4]),
   (mkRat (-2) 27, [2, 2, 2, 3, 3]),
   (mkRat (1) 8, [2, 2, 8]),
   (mkRat (4) 27, [3, 3, 6]),
   (mkRat (1) 15, [3, 4, 5]),
   (mkRat (-1) 48, [4, 4, 4]),
   (mkRat (-1) 3, [12])]

def sc708 : RawPoly ℕ :=
  [sc708Part0,
   sc708Part1].flatten

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc708_check :
    reduceTwo (prependC 1 sc326 ++ scaleR (-1) (prependC 0 sc327)) = sc708 := by
  decide +kernel

theorem sc708_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc708 = evRc a c (expWordR [1, 2, 3] (6)) := by
  rw [← sc708_check]
  exact expTwo_step _ _ hc 0 [2, 3] (6)
    sc326 sc327 (sc326_sound a c hc) (sc327_sound a c hc)

def sc709Part0 : RawPoly ℕ :=
  [(mkRat (1) 6480, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4]),
   (mkRat (-1) 756, [0, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2]),
   (mkRat (1) 378, [0, 1, 1, 1, 1, 1, 1, 1, 6]),
   (mkRat (-1) 270, [0, 1, 1, 1, 1, 1, 1, 3, 4]),
   (mkRat (-1) 80, [0, 1, 1, 1, 1, 1, 2, 2, 4]),
   (mkRat (1) 40, [0, 1, 1, 1, 1, 1, 8]),
   (mkRat (1) 108, [0, 1, 1, 1, 1, 2, 2, 2, 3]),
   (mkRat (-1) 54, [0, 1, 1, 1, 1, 3, 6]),
   (mkRat (1) 30, [0, 1, 1, 1, 1, 4, 5]),
   (mkRat (-1) 360, [0, 1, 1, 1, 2, 2, 2, 2, 2]),
   (mkRat (-1) 36, [0, 1, 1, 1, 2, 2, 6]),
   (mkRat (-1) 27, [0, 1, 1, 1, 3, 3, 4]),
   (mkRat (1) 15, [0, 1, 1, 1, 10]),
   (mkRat (1) 64, [0, 1, 2, 2, 2, 2, 4]),
   (mkRat (-1) 27, [0, 1, 2, 2, 2, 3, 3]),
   (mkRat (1) 16, [0, 1, 2, 2, 8]),
   (mkRat (2) 27, [0, 1, 3, 3, 6]),
   (mkRat (1) 30, [0, 1, 3, 4, 5]),
   (mkRat (-1) 96, [0, 1, 4, 4, 4]),
   (mkRat (-1) 6, [0, 1, 12]),
   (mkRat (-1) 360, [0, 2, 2, 2, 2, 2, 3]),
   (mkRat (1) 21, [0, 2, 2, 2, 7]),
   (mkRat (-1) 36, [0, 2, 2, 3, 6]),
   (mkRat (1) 20, [0, 2, 2, 4, 5])]

def sc709Part1 : RawPoly ℕ :=
  [(mkRat (7) 162, [0, 3, 3, 3, 4]),
   (mkRat (1) 15, [0, 3, 10]),
   (mkRat (-1) 9, [0, 4, 9]),
   (mkRat (-1) 10, [0, 5, 8]),
   (mkRat (-2) 21, [0, 6, 7]),
   (mkRat (1) 4422600, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (-1) 42525, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3]),
   (mkRat (-1) 6480, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2]),
   (mkRat (1) 1050, [1, 1, 1, 1, 1, 1, 1, 1, 5]),
   (mkRat (-2) 567, [1, 1, 1, 1, 1, 1, 1, 3, 3]),
   (mkRat (1) 270, [1, 1, 1, 1, 1, 1, 2, 2, 3]),
   (mkRat (4) 315, [1, 1, 1, 1, 1, 1, 7]),
   (mkRat (-1) 160, [1, 1, 1, 1, 1, 2, 2, 2, 2]),
   (mkRat (-1) 75, [1, 1, 1, 1, 1, 3, 5]),
   (mkRat (1) 80, [1, 1, 1, 1, 1, 4, 4]),
   (mkRat (-1) 30, [1, 1, 1, 1, 2, 2, 5]),
   (mkRat (-7) 243, [1, 1, 1, 1, 3, 3, 3]),
   (mkRat (2) 27, [1, 1, 1, 1, 9]),
   (mkRat (-1) 36, [1, 1, 1, 2, 2, 2, 4]),
   (mkRat (1) 27, [1, 1, 1, 2, 2, 3, 3]),
   (mkRat (-2) 63, [1, 1, 1, 3, 7]),
   (mkRat (1) 18, [1, 1, 1, 4, 6]),
   (mkRat (2) 75, [1, 1, 1, 5, 5]),
   (mkRat (1) 576, [1, 2, 2, 2, 2, 2, 2])]

def sc709Part2 : RawPoly ℕ :=
  [(mkRat (1) 18, [1, 2, 2, 2, 6]),
   (mkRat (-1) 30, [1, 2, 2, 3, 5]),
   (mkRat (1) 32, [1, 2, 2, 4, 4]),
   (mkRat (5) 243, [1, 3, 3, 3, 3]),
   (mkRat (2) 27, [1, 3, 9]),
   (mkRat (-1) 8, [1, 4, 8]),
   (mkRat (-4) 35, [1, 5, 7]),
   (mkRat (-1) 18, [1, 6, 6]),
   (mkRat (1) 40, [2, 2, 2, 2, 5]),
   (mkRat (-1) 36, [2, 2, 2, 3, 4]),
   (mkRat (-7) 162, [2, 2, 3, 3, 3]),
   (mkRat (1) 9, [2, 2, 9]),
   (mkRat (8) 63, [3, 3, 7]),
   (mkRat (1) 18, [3, 4, 6]),
   (mkRat (2) 75, [3, 5, 5]),
   (mkRat (-1) 20, [4, 4, 5]),
   (mkRat (-4) 13, [13])]

def sc709 : RawPoly ℕ :=
  [sc709Part0,
   sc709Part1,
   sc709Part2].flatten

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc709_check :
    reduceTwo (prependC 1 sc327 ++ scaleR (-1) (prependC 0 sc328)) = sc709 := by
  decide +kernel

theorem sc709_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc709 = evRc a c (expWordR [1, 2, 3] (7)) := by
  rw [← sc709_check]
  exact expTwo_step _ _ hc 0 [2, 3] (7)
    sc327 sc328 (sc327_sound a c hc) (sc328_sound a c hc)

def sc710Part0 : RawPoly ℕ :=
  [(mkRat (1) 56756700, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (-1) 415800, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3]),
   (mkRat (-1) 56700, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2]),
   (mkRat (1) 8100, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5]),
   (mkRat (-1) 1890, [0, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3]),
   (mkRat (1) 1512, [0, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3]),
   (mkRat (1) 441, [0, 1, 1, 1, 1, 1, 1, 1, 7]),
   (mkRat (-1) 720, [0, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2]),
   (mkRat (-2) 675, [0, 1, 1, 1, 1, 1, 1, 3, 5]),
   (mkRat (1) 360, [0, 1, 1, 1, 1, 1, 1, 4, 4]),
   (mkRat (-1) 100, [0, 1, 1, 1, 1, 1, 2, 2, 5]),
   (mkRat (-7) 810, [0, 1, 1, 1, 1, 1, 3, 3, 3]),
   (mkRat (1) 45, [0, 1, 1, 1, 1, 1, 9]),
   (mkRat (-1) 72, [0, 1, 1, 1, 1, 2, 2, 2, 4]),
   (mkRat (1) 54, [0, 1, 1, 1, 1, 2, 2, 3, 3]),
   (mkRat (-1) 63, [0, 1, 1, 1, 1, 3, 7]),
   (mkRat (1) 36, [0, 1, 1, 1, 1, 4, 6]),
   (mkRat (1) 75, [0, 1, 1, 1, 1, 5, 5]),
   (mkRat (1) 288, [0, 1, 1, 1, 2, 2, 2, 2, 3]),
   (mkRat (-1) 42, [0, 1, 1, 1, 2, 2, 7]),
   (mkRat (-4) 135, [0, 1, 1, 1, 3, 3, 5]),
   (mkRat (-1) 144, [0, 1, 1, 1, 3, 4, 4]),
   (mkRat (2) 33, [0, 1, 1, 1, 11]),
   (mkRat (1) 80, [0, 1, 2, 2, 2, 2, 5])]

def sc710Part1 : RawPoly ℕ :=
  [(mkRat (-1) 72, [0, 1, 2, 2, 2, 3, 4]),
   (mkRat (-7) 324, [0, 1, 2, 2, 3, 3, 3]),
   (mkRat (1) 18, [0, 1, 2, 2, 9]),
   (mkRat (4) 63, [0, 1, 3, 3, 7]),
   (mkRat (1) 36, [0, 1, 3, 4, 6]),
   (mkRat (1) 75, [0, 1, 3, 5, 5]),
   (mkRat (-1) 40, [0, 1, 4, 4, 5]),
   (mkRat (-2) 13, [0, 1, 13]),
   (mkRat (1) 240, [0, 2, 2, 2, 2, 2, 4]),
   (mkRat (-1) 72, [0, 2, 2, 2, 2, 3, 3]),
   (mkRat (1) 24, [0, 2, 2, 2, 8]),
   (mkRat (-1) 42, [0, 2, 2, 3, 7]),
   (mkRat (1) 24, [0, 2, 2, 4, 6]),
   (mkRat (1) 50, [0, 2, 2, 5, 5]),
   (mkRat (14) 405, [0, 3, 3, 3, 5]),
   (mkRat (1) 36, [0, 3, 3, 4, 4]),
   (mkRat (2) 33, [0, 3, 11]),
   (mkRat (-1) 10, [0, 4, 10]),
   (mkRat (-4) 45, [0, 5, 9]),
   (mkRat (-1) 12, [0, 6, 8]),
   (mkRat (-2) 49, [0, 7, 7]),
   (mkRat (1) 28350, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4]),
   (mkRat (-1) 2520, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2]),
   (mkRat (1) 1260, [1, 1, 1, 1, 1, 1, 1, 1, 6])]

def sc710Part2 : RawPoly ℕ :=
  [(mkRat (-1) 756, [1, 1, 1, 1, 1, 1, 1, 3, 4]),
   (mkRat (-1) 180, [1, 1, 1, 1, 1, 1, 2, 2, 4]),
   (mkRat (1) 90, [1, 1, 1, 1, 1, 1, 8]),
   (mkRat (1) 180, [1, 1, 1, 1, 1, 2, 2, 2, 3]),
   (mkRat (-1) 90, [1, 1, 1, 1, 1, 3, 6]),
   (mkRat (1) 50, [1, 1, 1, 1, 1, 4, 5]),
   (mkRat (-1) 360, [1, 1, 1, 1, 2, 2, 2, 2, 2]),
   (mkRat (-1) 36, [1, 1, 1, 1, 2, 2, 6]),
   (mkRat (-1) 27, [1, 1, 1, 1, 3, 3, 4]),
   (mkRat (1) 15, [1, 1, 1, 1, 10]),
   (mkRat (-1) 45, [1, 1, 1, 2, 2, 2, 5]),
   (mkRat (1) 72, [1, 1, 1, 2, 2, 3, 4]),
   (mkRat (-1) 36, [1, 1, 1, 3, 8]),
   (mkRat (1) 21, [1, 1, 1, 4, 7]),
   (mkRat (2) 45, [1, 1, 1, 5, 6]),
   (mkRat (-1) 360, [1, 2, 2, 2, 2, 2, 3]),
   (mkRat (1) 21, [1, 2, 2, 2, 7]),
   (mkRat (-1) 36, [1, 2, 2, 3, 6]),
   (mkRat (1) 20, [1, 2, 2, 4, 5]),
   (mkRat (7) 162, [1, 3, 3, 3, 4]),
   (mkRat (1) 15, [1, 3, 10]),
   (mkRat (-1) 9, [1, 4, 9]),
   (mkRat (-1) 10, [1, 5, 8]),
   (mkRat (-2) 21, [1, 6, 7])]

def sc710Part3 : RawPoly ℕ :=
  [(mkRat (1) 3360, [2, 2, 2, 2, 2, 2, 2]),
   (mkRat (1) 48, [2, 2, 2, 2, 6]),
   (mkRat (-1) 45, [2, 2, 2, 3, 5]),
   (mkRat (1) 48, [2, 2, 2, 4, 4]),
   (mkRat (-1) 18, [2, 2, 3, 3, 4]),
   (mkRat (1) 10, [2, 2, 10]),
   (mkRat (1) 9, [3, 3, 8]),
   (mkRat (1) 21, [3, 4, 7]),
   (mkRat (2) 45, [3, 5, 6]),
   (mkRat (-1) 24, [4, 4, 6]),
   (mkRat (-1) 25, [4, 5, 5]),
   (mkRat (-2) 7, [14])]

def sc710 : RawPoly ℕ :=
  [sc710Part0,
   sc710Part1,
   sc710Part2,
   sc710Part3].flatten

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc710_check :
    reduceTwo (prependC 1 sc328 ++ scaleR (-1) (prependC 0 sc329)) = sc710 := by
  decide +kernel

theorem sc710_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc710 = evRc a c (expWordR [1, 2, 3] (8)) := by
  rw [← sc710_check]
  exact expTwo_step _ _ hc 0 [2, 3] (8)
    sc328 sc329 (sc328_sound a c hc) (sc329_sound a c hc)

def sc711Part0 : RawPoly ℕ :=
  [(mkRat (1) 277200, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4]),
   (mkRat (-1) 19440, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2]),
   (mkRat (1) 9720, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6]),
   (mkRat (-1) 5040, [0, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4]),
   (mkRat (-1) 1008, [0, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4]),
   (mkRat (1) 504, [0, 1, 1, 1, 1, 1, 1, 1, 8]),
   (mkRat (1) 810, [0, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3]),
   (mkRat (-1) 405, [0, 1, 1, 1, 1, 1, 1, 3, 6]),
   (mkRat (1) 225, [0, 1, 1, 1, 1, 1, 1, 4, 5]),
   (mkRat (-1) 1200, [0, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2]),
   (mkRat (-1) 120, [0, 1, 1, 1, 1, 1, 2, 2, 6]),
   (mkRat (-1) 90, [0, 1, 1, 1, 1, 1, 3, 3, 4]),
   (mkRat (1) 50, [0, 1, 1, 1, 1, 1, 10]),
   (mkRat (-1) 90, [0, 1, 1, 1, 1, 2, 2, 2, 5]),
   (mkRat (1) 144, [0, 1, 1, 1, 1, 2, 2, 3, 4]),
   (mkRat (-1) 72, [0, 1, 1, 1, 1, 3, 8]),
   (mkRat (1) 42, [0, 1, 1, 1, 1, 4, 7]),
   (mkRat (1) 45, [0, 1, 1, 1, 1, 5, 6]),
   (mkRat (-1) 192, [0, 1, 1, 1, 2, 2, 2, 2, 4]),
   (mkRat (1) 81, [0, 1, 1, 1, 2, 2, 2, 3, 3]),
   (mkRat (-1) 48, [0, 1, 1, 1, 2, 2, 8]),
   (mkRat (-2) 81, [0, 1, 1, 1, 3, 3, 6]),
   (mkRat (-1) 90, [0, 1, 1, 1, 3, 4, 5]),
   (mkRat (1) 288, [0, 1, 1, 1, 4, 4, 4])]

def sc711Part1 : RawPoly ℕ :=
  [(mkRat (1) 18, [0, 1, 1, 1, 12]),
   (mkRat (1) 6720, [0, 1, 2, 2, 2, 2, 2, 2, 2]),
   (mkRat (1) 96, [0, 1, 2, 2, 2, 2, 6]),
   (mkRat (-1) 90, [0, 1, 2, 2, 2, 3, 5]),
   (mkRat (1) 96, [0, 1, 2, 2, 2, 4, 4]),
   (mkRat (-1) 36, [0, 1, 2, 2, 3, 3, 4]),
   (mkRat (1) 20, [0, 1, 2, 2, 10]),
   (mkRat (1) 18, [0, 1, 3, 3, 8]),
   (mkRat (1) 42, [0, 1, 3, 4, 7]),
   (mkRat (1) 45, [0, 1, 3, 5, 6]),
   (mkRat (-1) 48, [0, 1, 4, 4, 6]),
   (mkRat (-1) 50, [0, 1, 4, 5, 5]),
   (mkRat (-1) 7, [0, 1, 14]),
   (mkRat (1) 300, [0, 2, 2, 2, 2, 2, 5]),
   (mkRat (-1) 192, [0, 2, 2, 2, 2, 3, 4]),
   (mkRat (-7) 486, [0, 2, 2, 2, 3, 3, 3]),
   (mkRat (1) 27, [0, 2, 2, 2, 9]),
   (mkRat (-1) 48, [0, 2, 2, 3, 8]),
   (mkRat (1) 28, [0, 2, 2, 4, 7]),
   (mkRat (1) 30, [0, 2, 2, 5, 6]),
   (mkRat (7) 243, [0, 3, 3, 3, 6]),
   (mkRat (2) 45, [0, 3, 3, 4, 5]),
   (mkRat (1) 288, [0, 3, 4, 4, 4]),
   (mkRat (1) 18, [0, 3, 12])]

def sc711Part2 : RawPoly ℕ :=
  [(mkRat (-1) 11, [0, 4, 11]),
   (mkRat (-2) 25, [0, 5, 10]),
   (mkRat (-2) 27, [0, 6, 9]),
   (mkRat (-1) 14, [0, 7, 8]),
   (mkRat (1) 392931000, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (-1) 2245320, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3]),
   (mkRat (-1) 277200, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2]),
   (mkRat (2) 70875, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5]),
   (mkRat (-1) 7290, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3]),
   (mkRat (1) 5040, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3]),
   (mkRat (1) 1470, [1, 1, 1, 1, 1, 1, 1, 1, 7]),
   (mkRat (-1) 2016, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2]),
   (mkRat (-1) 945, [1, 1, 1, 1, 1, 1, 1, 3, 5]),
   (mkRat (1) 1008, [1, 1, 1, 1, 1, 1, 1, 4, 4]),
   (mkRat (-1) 225, [1, 1, 1, 1, 1, 1, 2, 2, 5]),
   (mkRat (-14) 3645, [1, 1, 1, 1, 1, 1, 3, 3, 3]),
   (mkRat (4) 405, [1, 1, 1, 1, 1, 1, 9]),
   (mkRat (-1) 120, [1, 1, 1, 1, 1, 2, 2, 2, 4]),
   (mkRat (1) 90, [1, 1, 1, 1, 1, 2, 2, 3, 3]),
   (mkRat (-1) 105, [1, 1, 1, 1, 1, 3, 7]),
   (mkRat (1) 60, [1, 1, 1, 1, 1, 4, 6]),
   (mkRat (1) 125, [1, 1, 1, 1, 1, 5, 5]),
   (mkRat (1) 288, [1, 1, 1, 1, 2, 2, 2, 2, 3]),
   (mkRat (-1) 42, [1, 1, 1, 1, 2, 2, 7])]

def sc711Part3 : RawPoly ℕ :=
  [(mkRat (-4) 135, [1, 1, 1, 1, 3, 3, 5]),
   (mkRat (-1) 144, [1, 1, 1, 1, 3, 4, 4]),
   (mkRat (2) 33, [1, 1, 1, 1, 11]),
   (mkRat (-1) 1728, [1, 1, 1, 2, 2, 2, 2, 2, 2]),
   (mkRat (-1) 54, [1, 1, 1, 2, 2, 2, 6]),
   (mkRat (1) 90, [1, 1, 1, 2, 2, 3, 5]),
   (mkRat (-1) 96, [1, 1, 1, 2, 2, 4, 4]),
   (mkRat (-5) 729, [1, 1, 1, 3, 3, 3, 3]),
   (mkRat (-2) 81, [1, 1, 1, 3, 9]),
   (mkRat (1) 24, [1, 1, 1, 4, 8]),
   (mkRat (4) 105, [1, 1, 1, 5, 7]),
   (mkRat (1) 54, [1, 1, 1, 6, 6]),
   (mkRat (1) 240, [1, 2, 2, 2, 2, 2, 4]),
   (mkRat (-1) 72, [1, 2, 2, 2, 2, 3, 3]),
   (mkRat (1) 24, [1, 2, 2, 2, 8]),
   (mkRat (-1) 42, [1, 2, 2, 3, 7]),
   (mkRat (1) 24, [1, 2, 2, 4, 6]),
   (mkRat (1) 50, [1, 2, 2, 5, 5]),
   (mkRat (14) 405, [1, 3, 3, 3, 5]),
   (mkRat (1) 36, [1, 3, 3, 4, 4]),
   (mkRat (2) 33, [1, 3, 11]),
   (mkRat (-1) 10, [1, 4, 10]),
   (mkRat (-4) 45, [1, 5, 9]),
   (mkRat (-1) 12, [1, 6, 8])]

def sc711Part4 : RawPoly ℕ :=
  [(mkRat (-2) 49, [1, 7, 7]),
   (mkRat (-1) 1728, [2, 2, 2, 2, 2, 2, 3]),
   (mkRat (1) 56, [2, 2, 2, 2, 7]),
   (mkRat (-1) 54, [2, 2, 2, 3, 6]),
   (mkRat (1) 30, [2, 2, 2, 4, 5]),
   (mkRat (-2) 45, [2, 2, 3, 3, 5]),
   (mkRat (-1) 96, [2, 2, 3, 4, 4]),
   (mkRat (1) 11, [2, 2, 11]),
   (mkRat (13) 3645, [3, 3, 3, 3, 3]),
   (mkRat (8) 81, [3, 3, 9]),
   (mkRat (1) 24, [3, 4, 8]),
   (mkRat (4) 105, [3, 5, 7]),
   (mkRat (1) 54, [3, 6, 6]),
   (mkRat (-1) 28, [4, 4, 7]),
   (mkRat (-1) 15, [4, 5, 6]),
   (mkRat (-4) 375, [5, 5, 5]),
   (mkRat (-4) 15, [15])]

def sc711 : RawPoly ℕ :=
  [sc711Part0,
   sc711Part1,
   sc711Part2,
   sc711Part3,
   sc711Part4].flatten

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc711_check :
    reduceTwo (prependC 1 sc329 ++ scaleR (-1) (prependC 0 sc330)) = sc711 := by
  decide +kernel

theorem sc711_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc711 = evRc a c (expWordR [1, 2, 3] (9)) := by
  rw [← sc711_check]
  exact expTwo_step _ _ hc 0 [2, 3] (9)
    sc329 sc330 (sc329_sound a c hc) (sc330_sound a c hc)

def sc712Part0 : RawPoly ℕ :=
  [(mkRat (1) 5837832000, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (-1) 26535600, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3]),
   (mkRat (-1) 2993760, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2]),
   (mkRat (1) 346500, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5]),
   (mkRat (-2) 127575, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3]),
   (mkRat (1) 38880, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3]),
   (mkRat (1) 11340, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7]),
   (mkRat (-1) 13440, [0, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2]),
   (mkRat (-1) 6300, [0, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5]),
   (mkRat (1) 6720, [0, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4]),
   (mkRat (-1) 1260, [0, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5]),
   (mkRat (-1) 1458, [0, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3]),
   (mkRat (1) 567, [0, 1, 1, 1, 1, 1, 1, 1, 9]),
   (mkRat (-1) 540, [0, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4]),
   (mkRat (1) 405, [0, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3]),
   (mkRat (-2) 945, [0, 1, 1, 1, 1, 1, 1, 3, 7]),
   (mkRat (1) 270, [0, 1, 1, 1, 1, 1, 1, 4, 6]),
   (mkRat (2) 1125, [0, 1, 1, 1, 1, 1, 1, 5, 5]),
   (mkRat (1) 960, [0, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3]),
   (mkRat (-1) 140, [0, 1, 1, 1, 1, 1, 2, 2, 7]),
   (mkRat (-2) 225, [0, 1, 1, 1, 1, 1, 3, 3, 5]),
   (mkRat (-1) 480, [0, 1, 1, 1, 1, 1, 3, 4, 4]),
   (mkRat (1) 55, [0, 1, 1, 1, 1, 1, 11]),
   (mkRat (-1) 3456, [0, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2])]

def sc712Part1 : RawPoly ℕ :=
  [(mkRat (-1) 108, [0, 1, 1, 1, 1, 2, 2, 2, 6]),
   (mkRat (1) 180, [0, 1, 1, 1, 1, 2, 2, 3, 5]),
   (mkRat (-1) 192, [0, 1, 1, 1, 1, 2, 2, 4, 4]),
   (mkRat (-5) 1458, [0, 1, 1, 1, 1, 3, 3, 3, 3]),
   (mkRat (-1) 81, [0, 1, 1, 1, 1, 3, 9]),
   (mkRat (1) 48, [0, 1, 1, 1, 1, 4, 8]),
   (mkRat (2) 105, [0, 1, 1, 1, 1, 5, 7]),
   (mkRat (1) 108, [0, 1, 1, 1, 1, 6, 6]),
   (mkRat (-1) 240, [0, 1, 1, 1, 2, 2, 2, 2, 5]),
   (mkRat (1) 216, [0, 1, 1, 1, 2, 2, 2, 3, 4]),
   (mkRat (7) 972, [0, 1, 1, 1, 2, 2, 3, 3, 3]),
   (mkRat (-1) 54, [0, 1, 1, 1, 2, 2, 9]),
   (mkRat (-4) 189, [0, 1, 1, 1, 3, 3, 7]),
   (mkRat (-1) 108, [0, 1, 1, 1, 3, 4, 6]),
   (mkRat (-1) 225, [0, 1, 1, 1, 3, 5, 5]),
   (mkRat (1) 120, [0, 1, 1, 1, 4, 4, 5]),
   (mkRat (2) 39, [0, 1, 1, 1, 13]),
   (mkRat (-1) 3456, [0, 1, 2, 2, 2, 2, 2, 2, 3]),
   (mkRat (1) 112, [0, 1, 2, 2, 2, 2, 7]),
   (mkRat (-1) 108, [0, 1, 2, 2, 2, 3, 6]),
   (mkRat (1) 60, [0, 1, 2, 2, 2, 4, 5]),
   (mkRat (-1) 45, [0, 1, 2, 2, 3, 3, 5]),
   (mkRat (-1) 192, [0, 1, 2, 2, 3, 4, 4]),
   (mkRat (1) 22, [0, 1, 2, 2, 11])]

def sc712Part2 : RawPoly ℕ :=
  [(mkRat (13) 7290, [0, 1, 3, 3, 3, 3, 3]),
   (mkRat (4) 81, [0, 1, 3, 3, 9]),
   (mkRat (1) 48, [0, 1, 3, 4, 8]),
   (mkRat (2) 105, [0, 1, 3, 5, 7]),
   (mkRat (1) 108, [0, 1, 3, 6, 6]),
   (mkRat (-1) 56, [0, 1, 4, 4, 7]),
   (mkRat (-1) 30, [0, 1, 4, 5, 6]),
   (mkRat (-2) 375, [0, 1, 5, 5, 5]),
   (mkRat (-2) 15, [0, 1, 15]),
   (mkRat (1) 46080, [0, 2, 2, 2, 2, 2, 2, 2, 2]),
   (mkRat (1) 360, [0, 2, 2, 2, 2, 2, 6]),
   (mkRat (-1) 240, [0, 2, 2, 2, 2, 3, 5]),
   (mkRat (1) 256, [0, 2, 2, 2, 2, 4, 4]),
   (mkRat (-1) 54, [0, 2, 2, 2, 3, 3, 4]),
   (mkRat (1) 30, [0, 2, 2, 2, 10]),
   (mkRat (-5) 972, [0, 2, 2, 3, 3, 3, 3]),
   (mkRat (-1) 54, [0, 2, 2, 3, 9]),
   (mkRat (1) 32, [0, 2, 2, 4, 8]),
   (mkRat (1) 35, [0, 2, 2, 5, 7]),
   (mkRat (1) 72, [0, 2, 2, 6, 6]),
   (mkRat (2) 81, [0, 3, 3, 3, 7]),
   (mkRat (1) 27, [0, 3, 3, 4, 6]),
   (mkRat (4) 225, [0, 3, 3, 5, 5]),
   (mkRat (1) 120, [0, 3, 4, 4, 5])]

def sc712Part3 : RawPoly ℕ :=
  [(mkRat (2) 39, [0, 3, 13]),
   (mkRat (-1) 768, [0, 4, 4, 4, 4]),
   (mkRat (-1) 12, [0, 4, 12]),
   (mkRat (-4) 55, [0, 5, 11]),
   (mkRat (-1) 15, [0, 6, 10]),
   (mkRat (-4) 63, [0, 7, 9]),
   (mkRat (-1) 32, [0, 8, 8]),
   (mkRat (1) 1496880, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4]),
   (mkRat (-1) 85050, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2]),
   (mkRat (1) 42525, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6]),
   (mkRat (-1) 19440, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4]),
   (mkRat (-1) 3360, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4]),
   (mkRat (1) 1680, [1, 1, 1, 1, 1, 1, 1, 1, 8]),
   (mkRat (1) 2268, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3]),
   (mkRat (-1) 1134, [1, 1, 1, 1, 1, 1, 1, 3, 6]),
   (mkRat (1) 630, [1, 1, 1, 1, 1, 1, 1, 4, 5]),
   (mkRat (-1) 2700, [1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2]),
   (mkRat (-1) 270, [1, 1, 1, 1, 1, 1, 2, 2, 6]),
   (mkRat (-2) 405, [1, 1, 1, 1, 1, 1, 3, 3, 4]),
   (mkRat (2) 225, [1, 1, 1, 1, 1, 1, 10]),
   (mkRat (-1) 150, [1, 1, 1, 1, 1, 2, 2, 2, 5]),
   (mkRat (1) 240, [1, 1, 1, 1, 1, 2, 2, 3, 4]),
   (mkRat (-1) 120, [1, 1, 1, 1, 1, 3, 8]),
   (mkRat (1) 70, [1, 1, 1, 1, 1, 4, 7])]

def sc712Part4 : RawPoly ℕ :=
  [(mkRat (1) 75, [1, 1, 1, 1, 1, 5, 6]),
   (mkRat (-1) 192, [1, 1, 1, 1, 2, 2, 2, 2, 4]),
   (mkRat (1) 81, [1, 1, 1, 1, 2, 2, 2, 3, 3]),
   (mkRat (-1) 48, [1, 1, 1, 1, 2, 2, 8]),
   (mkRat (-2) 81, [1, 1, 1, 1, 3, 3, 6]),
   (mkRat (-1) 90, [1, 1, 1, 1, 3, 4, 5]),
   (mkRat (1) 288, [1, 1, 1, 1, 4, 4, 4]),
   (mkRat (1) 18, [1, 1, 1, 1, 12]),
   (mkRat (1) 1080, [1, 1, 1, 2, 2, 2, 2, 2, 3]),
   (mkRat (-1) 63, [1, 1, 1, 2, 2, 2, 7]),
   (mkRat (1) 108, [1, 1, 1, 2, 2, 3, 6]),
   (mkRat (-1) 60, [1, 1, 1, 2, 2, 4, 5]),
   (mkRat (-7) 486, [1, 1, 1, 3, 3, 3, 4]),
   (mkRat (-1) 45, [1, 1, 1, 3, 10]),
   (mkRat (1) 27, [1, 1, 1, 4, 9]),
   (mkRat (1) 30, [1, 1, 1, 5, 8]),
   (mkRat (2) 63, [1, 1, 1, 6, 7]),
   (mkRat (1) 300, [1, 2, 2, 2, 2, 2, 5]),
   (mkRat (-1) 192, [1, 2, 2, 2, 2, 3, 4]),
   (mkRat (-7) 486, [1, 2, 2, 2, 3, 3, 3]),
   (mkRat (1) 27, [1, 2, 2, 2, 9]),
   (mkRat (-1) 48, [1, 2, 2, 3, 8]),
   (mkRat (1) 28, [1, 2, 2, 4, 7]),
   (mkRat (1) 30, [1, 2, 2, 5, 6])]

def sc712Part5 : RawPoly ℕ :=
  [(mkRat (7) 243, [1, 3, 3, 3, 6]),
   (mkRat (2) 45, [1, 3, 3, 4, 5]),
   (mkRat (1) 288, [1, 3, 4, 4, 4]),
   (mkRat (1) 18, [1, 3, 12]),
   (mkRat (-1) 11, [1, 4, 11]),
   (mkRat (-2) 25, [1, 5, 10]),
   (mkRat (-2) 27, [1, 6, 9]),
   (mkRat (-1) 14, [1, 7, 8]),
   (mkRat (1) 1152, [2, 2, 2, 2, 2, 2, 4]),
   (mkRat (-1) 270, [2, 2, 2, 2, 2, 3, 3]),
   (mkRat (1) 64, [2, 2, 2, 2, 8]),
   (mkRat (-1) 63, [2, 2, 2, 3, 7]),
   (mkRat (1) 36, [2, 2, 2, 4, 6]),
   (mkRat (1) 75, [2, 2, 2, 5, 5]),
   (mkRat (-1) 27, [2, 2, 3, 3, 6]),
   (mkRat (-1) 60, [2, 2, 3, 4, 5]),
   (mkRat (1) 192, [2, 2, 4, 4, 4]),
   (mkRat (1) 12, [2, 2, 12]),
   (mkRat (5) 486, [3, 3, 3, 3, 4]),
   (mkRat (4) 45, [3, 3, 10]),
   (mkRat (1) 27, [3, 4, 9]),
   (mkRat (1) 30, [3, 5, 8]),
   (mkRat (2) 63, [3, 6, 7]),
   (mkRat (-1) 32, [4, 4, 8])]

def sc712Part6 : RawPoly ℕ :=
  [(mkRat (-2) 35, [4, 5, 7]),
   (mkRat (-1) 36, [4, 6, 6]),
   (mkRat (-2) 75, [5, 5, 6]),
   (mkRat (-1) 4, [16])]

def sc712 : RawPoly ℕ :=
  [sc712Part0,
   sc712Part1,
   sc712Part2,
   sc712Part3,
   sc712Part4,
   sc712Part5,
   sc712Part6].flatten

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc712_check :
    reduceTwo (prependC 1 sc330 ++ scaleR (-1) (prependC 0 sc331)) = sc712 := by
  decide +kernel

theorem sc712_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc712 = evRc a c (expWordR [1, 2, 3] (10)) := by
  rw [← sc712_check]
  exact expTwo_step _ _ hc 0 [2, 3] (10)
    sc330 sc331 (sc330_sound a c hc) (sc331_sound a c hc)

def sc713 : RawPoly ℕ :=
  [(-2, [0])]

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc713_check :
    reduceTwo (prependC 1 sc332 ++ scaleR (-1) (prependC 0 sc333)) = sc713 := by
  decide +kernel

theorem sc713_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc713 = evRc a c (expWordR [1, 2, 4] (-7)) := by
  rw [← sc713_check]
  exact expTwo_step _ _ hc 0 [2, 4] (-7)
    sc332 sc333 (sc332_sound a c hc) (sc333_sound a c hc)

def sc714 : RawPoly ℕ :=
  [(mkRat (1) 3, [0, 1, 1, 1, 1]),
   (mkRat (-2) 3, [0, 1, 3]),
   (mkRat (1) 2, [0, 2, 2]),
   (1, [4])]

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc714_check :
    reduceTwo (prependC 1 sc335 ++ scaleR (-1) (prependC 0 sc336)) = sc714 := by
  decide +kernel

theorem sc714_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc714 = evRc a c (expWordR [1, 2, 4] (-3)) := by
  rw [← sc714_check]
  exact expTwo_step _ _ hc 0 [2, 4] (-3)
    sc335 sc336 (sc335_sound a c hc) (sc336_sound a c hc)

def sc715 : RawPoly ℕ :=
  [(mkRat (1) 2, [0, 1, 4]),
   (mkRat (1) 5, [1, 1, 1, 1, 1]),
   (mkRat (1) 2, [1, 2, 2]),
   (mkRat (-4) 5, [5])]

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc715_check :
    reduceTwo (prependC 1 sc336 ++ scaleR (-1) (prependC 0 sc337)) = sc715 := by
  decide +kernel

theorem sc715_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc715 = evRc a c (expWordR [1, 2, 4] (-2)) := by
  rw [← sc715_check]
  exact expTwo_step _ _ hc 0 [2, 4] (-2)
    sc336 sc337 (sc336_sound a c hc) (sc337_sound a c hc)

def sc716 : RawPoly ℕ :=
  [(mkRat (2) 45, [0, 1, 1, 1, 1, 1, 1]),
   (mkRat (2) 9, [0, 1, 1, 1, 3]),
   (mkRat (-2) 5, [0, 1, 5]),
   (mkRat (-2) 9, [0, 3, 3]),
   (mkRat (1) 3, [2, 2, 2]),
   (mkRat (-2) 3, [6])]

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc716_check :
    reduceTwo (prependC 1 sc337 ++ scaleR (-1) (prependC 0 sc338)) = sc716 := by
  decide +kernel

theorem sc716_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc716 = evRc a c (expWordR [1, 2, 4] (-1)) := by
  rw [← sc716_check]
  exact expTwo_step _ _ hc 0 [2, 4] (-1)
    sc337 sc338 (sc337_sound a c hc) (sc338_sound a c hc)

def sc717 : RawPoly ℕ :=
  [(mkRat (-1) 6, [0, 1, 1, 1, 4]),
   (mkRat (1) 6, [0, 1, 2, 2, 2]),
   (mkRat (-1) 3, [0, 1, 6]),
   (mkRat (1) 3, [0, 3, 4]),
   (mkRat (1) 63, [1, 1, 1, 1, 1, 1, 1]),
   (mkRat (2) 9, [1, 1, 1, 1, 3]),
   (mkRat (-1) 6, [1, 1, 1, 2, 2]),
   (mkRat (-2) 9, [1, 3, 3]),
   (mkRat (1) 3, [2, 2, 3]),
   (mkRat (-4) 7, [7])]

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc717_check :
    reduceTwo (prependC 1 sc338 ++ scaleR (-1) (prependC 0 sc339)) = sc717 := by
  decide +kernel

theorem sc717_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc717 = evRc a c (expWordR [1, 2, 4] (0)) := by
  rw [← sc717_check]
  exact expTwo_step _ _ hc 0 [2, 4] (0)
    sc338 sc339 (sc338_sound a c hc) (sc339_sound a c hc)

def sc718 : RawPoly ℕ :=
  [(mkRat (1) 420, [0, 1, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (1) 15, [0, 1, 1, 1, 1, 1, 3]),
   (mkRat (-1) 12, [0, 1, 1, 1, 1, 2, 2]),
   (mkRat (2) 15, [0, 1, 1, 1, 5]),
   (mkRat (1) 6, [0, 1, 2, 2, 3]),
   (mkRat (-2) 7, [0, 1, 7]),
   (mkRat (1) 16, [0, 2, 2, 2, 2]),
   (mkRat (-4) 15, [0, 3, 5]),
   (mkRat (3) 8, [0, 4, 4]),
   (mkRat (-1) 6, [1, 1, 1, 1, 4]),
   (mkRat (1) 3, [1, 3, 4]),
   (mkRat (-1) 4, [2, 2, 4]),
   (mkRat (-1) 2, [8])]

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc718_check :
    reduceTwo (prependC 1 sc339 ++ scaleR (-1) (prependC 0 sc340)) = sc718 := by
  decide +kernel

theorem sc718_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc718 = evRc a c (expWordR [1, 2, 4] (1)) := by
  rw [← sc718_check]
  exact expTwo_step _ _ hc 0 [2, 4] (1)
    sc339 sc340 (sc339_sound a c hc) (sc340_sound a c hc)

def sc719 : RawPoly ℕ :=
  [(mkRat (-1) 20, [0, 1, 1, 1, 1, 1, 4]),
   (mkRat (-1) 18, [0, 1, 1, 1, 2, 2, 2]),
   (mkRat (1) 9, [0, 1, 1, 1, 6]),
   (mkRat (-1) 8, [0, 1, 2, 2, 4]),
   (mkRat (-1) 4, [0, 1, 8]),
   (mkRat (1) 9, [0, 2, 2, 2, 3]),
   (mkRat (-2) 9, [0, 3, 6]),
   (mkRat (1) 5, [0, 4, 5]),
   (mkRat (1) 1620, [1, 1, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (4) 135, [1, 1, 1, 1, 1, 1, 3]),
   (mkRat (-1) 20, [1, 1, 1, 1, 1, 2, 2]),
   (mkRat (2) 15, [1, 1, 1, 1, 5]),
   (mkRat (2) 27, [1, 1, 1, 3, 3]),
   (mkRat (1) 16, [1, 2, 2, 2, 2]),
   (mkRat (-4) 15, [1, 3, 5]),
   (mkRat (3) 8, [1, 4, 4]),
   (mkRat (1) 5, [2, 2, 5]),
   (mkRat (-4) 81, [3, 3, 3]),
   (mkRat (-4) 9, [9])]

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc719_check :
    reduceTwo (prependC 1 sc340 ++ scaleR (-1) (prependC 0 sc341)) = sc719 := by
  decide +kernel

theorem sc719_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc719 = evRc a c (expWordR [1, 2, 4] (2)) := by
  rw [← sc719_check]
  exact expTwo_step _ _ hc 0 [2, 4] (2)
    sc340 sc341 (sc340_sound a c hc) (sc341_sound a c hc)

def sc720Part0 : RawPoly ℕ :=
  [(mkRat (1) 14175, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (1) 189, [0, 1, 1, 1, 1, 1, 1, 1, 3]),
   (mkRat (-1) 90, [0, 1, 1, 1, 1, 1, 1, 2, 2]),
   (mkRat (1) 25, [0, 1, 1, 1, 1, 1, 5]),
   (mkRat (1) 27, [0, 1, 1, 1, 1, 3, 3]),
   (mkRat (-1) 18, [0, 1, 1, 1, 2, 2, 3]),
   (mkRat (2) 21, [0, 1, 1, 1, 7]),
   (mkRat (1) 10, [0, 1, 2, 2, 5]),
   (mkRat (-2) 81, [0, 1, 3, 3, 3]),
   (mkRat (-2) 9, [0, 1, 9]),
   (mkRat (-1) 12, [0, 2, 2, 2, 4]),
   (mkRat (1) 18, [0, 2, 2, 3, 3]),
   (mkRat (-4) 21, [0, 3, 7]),
   (mkRat (1) 6, [0, 4, 6]),
   (mkRat (-2) 25, [0, 5, 5]),
   (mkRat (-1) 45, [1, 1, 1, 1, 1, 1, 4]),
   (mkRat (-1) 18, [1, 1, 1, 1, 2, 2, 2]),
   (mkRat (1) 9, [1, 1, 1, 1, 6]),
   (mkRat (-1) 9, [1, 1, 1, 3, 4]),
   (mkRat (1) 9, [1, 2, 2, 2, 3]),
   (mkRat (-2) 9, [1, 3, 6]),
   (mkRat (1) 5, [1, 4, 5]),
   (mkRat (1) 60, [2, 2, 2, 2, 2]),
   (mkRat (1) 6, [2, 2, 6])]

def sc720Part1 : RawPoly ℕ :=
  [(mkRat (1) 9, [3, 3, 4]),
   (mkRat (-2) 5, [10])]

def sc720 : RawPoly ℕ :=
  [sc720Part0,
   sc720Part1].flatten

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc720_check :
    reduceTwo (prependC 1 sc341 ++ scaleR (-1) (prependC 0 sc342)) = sc720 := by
  decide +kernel

theorem sc720_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc720 = evRc a c (expWordR [1, 2, 4] (3)) := by
  rw [← sc720_check]
  exact expTwo_step _ _ hc 0 [2, 4] (3)
    sc341 sc342 (sc341_sound a c hc) (sc342_sound a c hc)

def sc721Part0 : RawPoly ℕ :=
  [(mkRat (-1) 252, [0, 1, 1, 1, 1, 1, 1, 1, 4]),
   (mkRat (-1) 60, [0, 1, 1, 1, 1, 1, 2, 2, 2]),
   (mkRat (1) 30, [0, 1, 1, 1, 1, 1, 6]),
   (mkRat (-1) 18, [0, 1, 1, 1, 1, 3, 4]),
   (mkRat (1) 24, [0, 1, 1, 1, 2, 2, 4]),
   (mkRat (1) 12, [0, 1, 1, 1, 8]),
   (mkRat (1) 120, [0, 1, 2, 2, 2, 2, 2]),
   (mkRat (1) 12, [0, 1, 2, 2, 6]),
   (mkRat (1) 18, [0, 1, 3, 3, 4]),
   (mkRat (-1) 5, [0, 1, 10]),
   (mkRat (1) 15, [0, 2, 2, 2, 5]),
   (mkRat (-1) 12, [0, 2, 2, 3, 4]),
   (mkRat (-1) 6, [0, 3, 8]),
   (mkRat (1) 7, [0, 4, 7]),
   (mkRat (-2) 15, [0, 5, 6]),
   (mkRat (1) 69300, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (1) 630, [1, 1, 1, 1, 1, 1, 1, 1, 3]),
   (mkRat (-1) 252, [1, 1, 1, 1, 1, 1, 1, 2, 2]),
   (mkRat (4) 225, [1, 1, 1, 1, 1, 1, 5]),
   (mkRat (1) 45, [1, 1, 1, 1, 1, 3, 3]),
   (mkRat (-1) 18, [1, 1, 1, 1, 2, 2, 3]),
   (mkRat (2) 21, [1, 1, 1, 1, 7]),
   (mkRat (-1) 48, [1, 1, 1, 2, 2, 2, 2]),
   (mkRat (4) 45, [1, 1, 1, 3, 5])]

def sc721Part1 : RawPoly ℕ :=
  [(mkRat (-1) 8, [1, 1, 1, 4, 4]),
   (mkRat (-1) 12, [1, 2, 2, 2, 4]),
   (mkRat (1) 18, [1, 2, 2, 3, 3]),
   (mkRat (-4) 21, [1, 3, 7]),
   (mkRat (1) 6, [1, 4, 6]),
   (mkRat (-2) 25, [1, 5, 5]),
   (mkRat (1) 24, [2, 2, 2, 2, 3]),
   (mkRat (1) 7, [2, 2, 7]),
   (mkRat (-4) 45, [3, 3, 5]),
   (mkRat (1) 4, [3, 4, 4]),
   (mkRat (-4) 11, [11])]

def sc721 : RawPoly ℕ :=
  [sc721Part0,
   sc721Part1].flatten

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc721_check :
    reduceTwo (prependC 1 sc342 ++ scaleR (-1) (prependC 0 sc343)) = sc721 := by
  decide +kernel

theorem sc721_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc721 = evRc a c (expWordR [1, 2, 4] (4)) := by
  rw [← sc721_check]
  exact expTwo_step _ _ hc 0 [2, 4] (4)
    sc342 sc343 (sc342_sound a c hc) (sc343_sound a c hc)

def sc722Part0 : RawPoly ℕ :=
  [(mkRat (1) 748440, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (1) 4860, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3]),
   (mkRat (-1) 1680, [0, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2]),
   (mkRat (1) 315, [0, 1, 1, 1, 1, 1, 1, 1, 5]),
   (mkRat (2) 405, [0, 1, 1, 1, 1, 1, 1, 3, 3]),
   (mkRat (-1) 60, [0, 1, 1, 1, 1, 1, 2, 2, 3]),
   (mkRat (1) 35, [0, 1, 1, 1, 1, 1, 7]),
   (mkRat (-1) 96, [0, 1, 1, 1, 1, 2, 2, 2, 2]),
   (mkRat (2) 45, [0, 1, 1, 1, 1, 3, 5]),
   (mkRat (-1) 16, [0, 1, 1, 1, 1, 4, 4]),
   (mkRat (-1) 30, [0, 1, 1, 1, 2, 2, 5]),
   (mkRat (2) 243, [0, 1, 1, 1, 3, 3, 3]),
   (mkRat (2) 27, [0, 1, 1, 1, 9]),
   (mkRat (1) 48, [0, 1, 2, 2, 2, 2, 3]),
   (mkRat (1) 14, [0, 1, 2, 2, 7]),
   (mkRat (-2) 45, [0, 1, 3, 3, 5]),
   (mkRat (1) 8, [0, 1, 3, 4, 4]),
   (mkRat (-2) 11, [0, 1, 11]),
   (mkRat (1) 576, [0, 2, 2, 2, 2, 2, 2]),
   (mkRat (1) 18, [0, 2, 2, 2, 6]),
   (mkRat (1) 15, [0, 2, 2, 3, 5]),
   (mkRat (-3) 32, [0, 2, 2, 4, 4]),
   (mkRat (-1) 243, [0, 3, 3, 3, 3]),
   (mkRat (-4) 27, [0, 3, 9])]

def sc722Part1 : RawPoly ℕ :=
  [(mkRat (1) 8, [0, 4, 8]),
   (mkRat (-4) 35, [0, 5, 7]),
   (mkRat (-1) 18, [0, 6, 6]),
   (mkRat (-1) 840, [1, 1, 1, 1, 1, 1, 1, 1, 4]),
   (mkRat (-1) 135, [1, 1, 1, 1, 1, 1, 2, 2, 2]),
   (mkRat (2) 135, [1, 1, 1, 1, 1, 1, 6]),
   (mkRat (-1) 30, [1, 1, 1, 1, 1, 3, 4]),
   (mkRat (1) 24, [1, 1, 1, 1, 2, 2, 4]),
   (mkRat (1) 12, [1, 1, 1, 1, 8]),
   (mkRat (-1) 27, [1, 1, 1, 2, 2, 2, 3]),
   (mkRat (2) 27, [1, 1, 1, 3, 6]),
   (mkRat (-1) 15, [1, 1, 1, 4, 5]),
   (mkRat (1) 15, [1, 2, 2, 2, 5]),
   (mkRat (-1) 12, [1, 2, 2, 3, 4]),
   (mkRat (-1) 6, [1, 3, 8]),
   (mkRat (1) 7, [1, 4, 7]),
   (mkRat (-2) 15, [1, 5, 6]),
   (mkRat (-1) 32, [2, 2, 2, 2, 4]),
   (mkRat (1) 27, [2, 2, 2, 3, 3]),
   (mkRat (1) 8, [2, 2, 8]),
   (mkRat (-2) 27, [3, 3, 6]),
   (mkRat (2) 15, [3, 4, 5]),
   (mkRat (5) 48, [4, 4, 4]),
   (mkRat (-1) 3, [12])]

def sc722 : RawPoly ℕ :=
  [sc722Part0,
   sc722Part1].flatten

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc722_check :
    reduceTwo (prependC 1 sc343 ++ scaleR (-1) (prependC 0 sc344)) = sc722 := by
  decide +kernel

theorem sc722_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc722 = evRc a c (expWordR [1, 2, 4] (5)) := by
  rw [← sc722_check]
  exact expTwo_step _ _ hc 0 [2, 4] (5)
    sc343 sc344 (sc343_sound a c hc) (sc344_sound a c hc)

def sc723Part0 : RawPoly ℕ :=
  [(mkRat (-1) 6480, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4]),
   (mkRat (-1) 756, [0, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2]),
   (mkRat (1) 378, [0, 1, 1, 1, 1, 1, 1, 1, 6]),
   (mkRat (-1) 135, [0, 1, 1, 1, 1, 1, 1, 3, 4]),
   (mkRat (1) 80, [0, 1, 1, 1, 1, 1, 2, 2, 4]),
   (mkRat (1) 40, [0, 1, 1, 1, 1, 1, 8]),
   (mkRat (-1) 54, [0, 1, 1, 1, 1, 2, 2, 2, 3]),
   (mkRat (1) 27, [0, 1, 1, 1, 1, 3, 6]),
   (mkRat (-1) 30, [0, 1, 1, 1, 1, 4, 5]),
   (mkRat (-1) 360, [0, 1, 1, 1, 2, 2, 2, 2, 2]),
   (mkRat (-1) 36, [0, 1, 1, 1, 2, 2, 6]),
   (mkRat (-1) 54, [0, 1, 1, 1, 3, 3, 4]),
   (mkRat (1) 15, [0, 1, 1, 1, 10]),
   (mkRat (-1) 64, [0, 1, 2, 2, 2, 2, 4]),
   (mkRat (1) 54, [0, 1, 2, 2, 2, 3, 3]),
   (mkRat (1) 16, [0, 1, 2, 2, 8]),
   (mkRat (-1) 27, [0, 1, 3, 3, 6]),
   (mkRat (1) 15, [0, 1, 3, 4, 5]),
   (mkRat (5) 96, [0, 1, 4, 4, 4]),
   (mkRat (-1) 6, [0, 1, 12]),
   (mkRat (1) 180, [0, 2, 2, 2, 2, 2, 3]),
   (mkRat (1) 21, [0, 2, 2, 2, 7]),
   (mkRat (1) 18, [0, 2, 2, 3, 6]),
   (mkRat (-1) 20, [0, 2, 2, 4, 5])]

def sc723Part1 : RawPoly ℕ :=
  [(mkRat (1) 81, [0, 3, 3, 3, 4]),
   (mkRat (-2) 15, [0, 3, 10]),
   (mkRat (1) 9, [0, 4, 9]),
   (mkRat (-1) 10, [0, 5, 8]),
   (mkRat (-2) 21, [0, 6, 7]),
   (mkRat (1) 4422600, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (2) 42525, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3]),
   (mkRat (-1) 6480, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2]),
   (mkRat (1) 1050, [1, 1, 1, 1, 1, 1, 1, 1, 5]),
   (mkRat (1) 567, [1, 1, 1, 1, 1, 1, 1, 3, 3]),
   (mkRat (-1) 135, [1, 1, 1, 1, 1, 1, 2, 2, 3]),
   (mkRat (4) 315, [1, 1, 1, 1, 1, 1, 7]),
   (mkRat (-1) 160, [1, 1, 1, 1, 1, 2, 2, 2, 2]),
   (mkRat (2) 75, [1, 1, 1, 1, 1, 3, 5]),
   (mkRat (-3) 80, [1, 1, 1, 1, 1, 4, 4]),
   (mkRat (-1) 30, [1, 1, 1, 1, 2, 2, 5]),
   (mkRat (2) 243, [1, 1, 1, 1, 3, 3, 3]),
   (mkRat (2) 27, [1, 1, 1, 1, 9]),
   (mkRat (1) 36, [1, 1, 1, 2, 2, 2, 4]),
   (mkRat (-1) 54, [1, 1, 1, 2, 2, 3, 3]),
   (mkRat (4) 63, [1, 1, 1, 3, 7]),
   (mkRat (-1) 18, [1, 1, 1, 4, 6]),
   (mkRat (2) 75, [1, 1, 1, 5, 5]),
   (mkRat (1) 576, [1, 2, 2, 2, 2, 2, 2])]

def sc723Part2 : RawPoly ℕ :=
  [(mkRat (1) 18, [1, 2, 2, 2, 6]),
   (mkRat (1) 15, [1, 2, 2, 3, 5]),
   (mkRat (-3) 32, [1, 2, 2, 4, 4]),
   (mkRat (-1) 243, [1, 3, 3, 3, 3]),
   (mkRat (-4) 27, [1, 3, 9]),
   (mkRat (1) 8, [1, 4, 8]),
   (mkRat (-4) 35, [1, 5, 7]),
   (mkRat (-1) 18, [1, 6, 6]),
   (mkRat (1) 40, [2, 2, 2, 2, 5]),
   (mkRat (-1) 18, [2, 2, 2, 3, 4]),
   (mkRat (1) 81, [2, 2, 3, 3, 3]),
   (mkRat (1) 9, [2, 2, 9]),
   (mkRat (-4) 63, [3, 3, 7]),
   (mkRat (1) 9, [3, 4, 6]),
   (mkRat (-4) 75, [3, 5, 5]),
   (mkRat (3) 20, [4, 4, 5]),
   (mkRat (-4) 13, [13])]

def sc723 : RawPoly ℕ :=
  [sc723Part0,
   sc723Part1,
   sc723Part2].flatten

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc723_check :
    reduceTwo (prependC 1 sc344 ++ scaleR (-1) (prependC 0 sc345)) = sc723 := by
  decide +kernel

theorem sc723_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc723 = evRc a c (expWordR [1, 2, 4] (6)) := by
  rw [← sc723_check]
  exact expTwo_step _ _ hc 0 [2, 4] (6)
    sc344 sc345 (sc344_sound a c hc) (sc345_sound a c hc)

def sc724Part0 : RawPoly ℕ :=
  [(mkRat (1) 56756700, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (1) 207900, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3]),
   (mkRat (-1) 56700, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2]),
   (mkRat (1) 8100, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5]),
   (mkRat (1) 3780, [0, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3]),
   (mkRat (-1) 756, [0, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3]),
   (mkRat (1) 441, [0, 1, 1, 1, 1, 1, 1, 1, 7]),
   (mkRat (-1) 720, [0, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2]),
   (mkRat (4) 675, [0, 1, 1, 1, 1, 1, 1, 3, 5]),
   (mkRat (-1) 120, [0, 1, 1, 1, 1, 1, 1, 4, 4]),
   (mkRat (-1) 100, [0, 1, 1, 1, 1, 1, 2, 2, 5]),
   (mkRat (1) 405, [0, 1, 1, 1, 1, 1, 3, 3, 3]),
   (mkRat (1) 45, [0, 1, 1, 1, 1, 1, 9]),
   (mkRat (1) 72, [0, 1, 1, 1, 1, 2, 2, 2, 4]),
   (mkRat (-1) 108, [0, 1, 1, 1, 1, 2, 2, 3, 3]),
   (mkRat (2) 63, [0, 1, 1, 1, 1, 3, 7]),
   (mkRat (-1) 36, [0, 1, 1, 1, 1, 4, 6]),
   (mkRat (1) 75, [0, 1, 1, 1, 1, 5, 5]),
   (mkRat (-1) 144, [0, 1, 1, 1, 2, 2, 2, 2, 3]),
   (mkRat (-1) 42, [0, 1, 1, 1, 2, 2, 7]),
   (mkRat (2) 135, [0, 1, 1, 1, 3, 3, 5]),
   (mkRat (-1) 24, [0, 1, 1, 1, 3, 4, 4]),
   (mkRat (2) 33, [0, 1, 1, 1, 11]),
   (mkRat (1) 80, [0, 1, 2, 2, 2, 2, 5])]

def sc724Part1 : RawPoly ℕ :=
  [(mkRat (-1) 36, [0, 1, 2, 2, 2, 3, 4]),
   (mkRat (1) 162, [0, 1, 2, 2, 3, 3, 3]),
   (mkRat (1) 18, [0, 1, 2, 2, 9]),
   (mkRat (-2) 63, [0, 1, 3, 3, 7]),
   (mkRat (1) 18, [0, 1, 3, 4, 6]),
   (mkRat (-2) 75, [0, 1, 3, 5, 5]),
   (mkRat (3) 40, [0, 1, 4, 4, 5]),
   (mkRat (-2) 13, [0, 1, 13]),
   (mkRat (-1) 240, [0, 2, 2, 2, 2, 2, 4]),
   (mkRat (1) 144, [0, 2, 2, 2, 2, 3, 3]),
   (mkRat (1) 24, [0, 2, 2, 2, 8]),
   (mkRat (1) 21, [0, 2, 2, 3, 7]),
   (mkRat (-1) 24, [0, 2, 2, 4, 6]),
   (mkRat (1) 50, [0, 2, 2, 5, 5]),
   (mkRat (-4) 405, [0, 3, 3, 3, 5]),
   (mkRat (1) 24, [0, 3, 3, 4, 4]),
   (mkRat (-4) 33, [0, 3, 11]),
   (mkRat (1) 10, [0, 4, 10]),
   (mkRat (-4) 45, [0, 5, 9]),
   (mkRat (-1) 12, [0, 6, 8]),
   (mkRat (-2) 49, [0, 7, 7]),
   (mkRat (-1) 28350, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4]),
   (mkRat (-1) 2520, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2]),
   (mkRat (1) 1260, [1, 1, 1, 1, 1, 1, 1, 1, 6])]

def sc724Part2 : RawPoly ℕ :=
  [(mkRat (-1) 378, [1, 1, 1, 1, 1, 1, 1, 3, 4]),
   (mkRat (1) 180, [1, 1, 1, 1, 1, 1, 2, 2, 4]),
   (mkRat (1) 90, [1, 1, 1, 1, 1, 1, 8]),
   (mkRat (-1) 90, [1, 1, 1, 1, 1, 2, 2, 2, 3]),
   (mkRat (1) 45, [1, 1, 1, 1, 1, 3, 6]),
   (mkRat (-1) 50, [1, 1, 1, 1, 1, 4, 5]),
   (mkRat (-1) 360, [1, 1, 1, 1, 2, 2, 2, 2, 2]),
   (mkRat (-1) 36, [1, 1, 1, 1, 2, 2, 6]),
   (mkRat (-1) 54, [1, 1, 1, 1, 3, 3, 4]),
   (mkRat (1) 15, [1, 1, 1, 1, 10]),
   (mkRat (-1) 45, [1, 1, 1, 2, 2, 2, 5]),
   (mkRat (1) 36, [1, 1, 1, 2, 2, 3, 4]),
   (mkRat (1) 18, [1, 1, 1, 3, 8]),
   (mkRat (-1) 21, [1, 1, 1, 4, 7]),
   (mkRat (2) 45, [1, 1, 1, 5, 6]),
   (mkRat (1) 180, [1, 2, 2, 2, 2, 2, 3]),
   (mkRat (1) 21, [1, 2, 2, 2, 7]),
   (mkRat (1) 18, [1, 2, 2, 3, 6]),
   (mkRat (-1) 20, [1, 2, 2, 4, 5]),
   (mkRat (1) 81, [1, 3, 3, 3, 4]),
   (mkRat (-2) 15, [1, 3, 10]),
   (mkRat (1) 9, [1, 4, 9]),
   (mkRat (-1) 10, [1, 5, 8]),
   (mkRat (-2) 21, [1, 6, 7])]

def sc724Part3 : RawPoly ℕ :=
  [(mkRat (1) 3360, [2, 2, 2, 2, 2, 2, 2]),
   (mkRat (1) 48, [2, 2, 2, 2, 6]),
   (mkRat (2) 45, [2, 2, 2, 3, 5]),
   (mkRat (-1) 16, [2, 2, 2, 4, 4]),
   (mkRat (-1) 36, [2, 2, 3, 3, 4]),
   (mkRat (1) 10, [2, 2, 10]),
   (mkRat (-1) 18, [3, 3, 8]),
   (mkRat (2) 21, [3, 4, 7]),
   (mkRat (-4) 45, [3, 5, 6]),
   (mkRat (1) 8, [4, 4, 6]),
   (mkRat (1) 25, [4, 5, 5]),
   (mkRat (-2) 7, [14])]

def sc724 : RawPoly ℕ :=
  [sc724Part0,
   sc724Part1,
   sc724Part2,
   sc724Part3].flatten

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc724_check :
    reduceTwo (prependC 1 sc345 ++ scaleR (-1) (prependC 0 sc346)) = sc724 := by
  decide +kernel

theorem sc724_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc724 = evRc a c (expWordR [1, 2, 4] (7)) := by
  rw [← sc724_check]
  exact expTwo_step _ _ hc 0 [2, 4] (7)
    sc345 sc346 (sc345_sound a c hc) (sc346_sound a c hc)

def sc725Part0 : RawPoly ℕ :=
  [(mkRat (-1) 277200, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4]),
   (mkRat (-1) 19440, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2]),
   (mkRat (1) 9720, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6]),
   (mkRat (-1) 2520, [0, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4]),
   (mkRat (1) 1008, [0, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4]),
   (mkRat (1) 504, [0, 1, 1, 1, 1, 1, 1, 1, 8]),
   (mkRat (-1) 405, [0, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3]),
   (mkRat (2) 405, [0, 1, 1, 1, 1, 1, 1, 3, 6]),
   (mkRat (-1) 225, [0, 1, 1, 1, 1, 1, 1, 4, 5]),
   (mkRat (-1) 1200, [0, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2]),
   (mkRat (-1) 120, [0, 1, 1, 1, 1, 1, 2, 2, 6]),
   (mkRat (-1) 180, [0, 1, 1, 1, 1, 1, 3, 3, 4]),
   (mkRat (1) 50, [0, 1, 1, 1, 1, 1, 10]),
   (mkRat (-1) 90, [0, 1, 1, 1, 1, 2, 2, 2, 5]),
   (mkRat (1) 72, [0, 1, 1, 1, 1, 2, 2, 3, 4]),
   (mkRat (1) 36, [0, 1, 1, 1, 1, 3, 8]),
   (mkRat (-1) 42, [0, 1, 1, 1, 1, 4, 7]),
   (mkRat (1) 45, [0, 1, 1, 1, 1, 5, 6]),
   (mkRat (1) 192, [0, 1, 1, 1, 2, 2, 2, 2, 4]),
   (mkRat (-1) 162, [0, 1, 1, 1, 2, 2, 2, 3, 3]),
   (mkRat (-1) 48, [0, 1, 1, 1, 2, 2, 8]),
   (mkRat (1) 81, [0, 1, 1, 1, 3, 3, 6]),
   (mkRat (-1) 45, [0, 1, 1, 1, 3, 4, 5]),
   (mkRat (-5) 288, [0, 1, 1, 1, 4, 4, 4])]

def sc725Part1 : RawPoly ℕ :=
  [(mkRat (1) 18, [0, 1, 1, 1, 12]),
   (mkRat (1) 6720, [0, 1, 2, 2, 2, 2, 2, 2, 2]),
   (mkRat (1) 96, [0, 1, 2, 2, 2, 2, 6]),
   (mkRat (1) 45, [0, 1, 2, 2, 2, 3, 5]),
   (mkRat (-1) 32, [0, 1, 2, 2, 2, 4, 4]),
   (mkRat (-1) 72, [0, 1, 2, 2, 3, 3, 4]),
   (mkRat (1) 20, [0, 1, 2, 2, 10]),
   (mkRat (-1) 36, [0, 1, 3, 3, 8]),
   (mkRat (1) 21, [0, 1, 3, 4, 7]),
   (mkRat (-2) 45, [0, 1, 3, 5, 6]),
   (mkRat (1) 16, [0, 1, 4, 4, 6]),
   (mkRat (1) 50, [0, 1, 4, 5, 5]),
   (mkRat (-1) 7, [0, 1, 14]),
   (mkRat (1) 300, [0, 2, 2, 2, 2, 2, 5]),
   (mkRat (-1) 96, [0, 2, 2, 2, 2, 3, 4]),
   (mkRat (1) 243, [0, 2, 2, 2, 3, 3, 3]),
   (mkRat (1) 27, [0, 2, 2, 2, 9]),
   (mkRat (1) 24, [0, 2, 2, 3, 8]),
   (mkRat (-1) 28, [0, 2, 2, 4, 7]),
   (mkRat (1) 30, [0, 2, 2, 5, 6]),
   (mkRat (-2) 243, [0, 3, 3, 3, 6]),
   (mkRat (1) 45, [0, 3, 3, 4, 5]),
   (mkRat (5) 144, [0, 3, 4, 4, 4]),
   (mkRat (-1) 9, [0, 3, 12])]

def sc725Part2 : RawPoly ℕ :=
  [(mkRat (1) 11, [0, 4, 11]),
   (mkRat (-2) 25, [0, 5, 10]),
   (mkRat (-2) 27, [0, 6, 9]),
   (mkRat (-1) 14, [0, 7, 8]),
   (mkRat (1) 392931000, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (1) 1122660, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3]),
   (mkRat (-1) 277200, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2]),
   (mkRat (2) 70875, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5]),
   (mkRat (1) 14580, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3]),
   (mkRat (-1) 2520, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3]),
   (mkRat (1) 1470, [1, 1, 1, 1, 1, 1, 1, 1, 7]),
   (mkRat (-1) 2016, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2]),
   (mkRat (2) 945, [1, 1, 1, 1, 1, 1, 1, 3, 5]),
   (mkRat (-1) 336, [1, 1, 1, 1, 1, 1, 1, 4, 4]),
   (mkRat (-1) 225, [1, 1, 1, 1, 1, 1, 2, 2, 5]),
   (mkRat (4) 3645, [1, 1, 1, 1, 1, 1, 3, 3, 3]),
   (mkRat (4) 405, [1, 1, 1, 1, 1, 1, 9]),
   (mkRat (1) 120, [1, 1, 1, 1, 1, 2, 2, 2, 4]),
   (mkRat (-1) 180, [1, 1, 1, 1, 1, 2, 2, 3, 3]),
   (mkRat (2) 105, [1, 1, 1, 1, 1, 3, 7]),
   (mkRat (-1) 60, [1, 1, 1, 1, 1, 4, 6]),
   (mkRat (1) 125, [1, 1, 1, 1, 1, 5, 5]),
   (mkRat (-1) 144, [1, 1, 1, 1, 2, 2, 2, 2, 3]),
   (mkRat (-1) 42, [1, 1, 1, 1, 2, 2, 7])]

def sc725Part3 : RawPoly ℕ :=
  [(mkRat (2) 135, [1, 1, 1, 1, 3, 3, 5]),
   (mkRat (-1) 24, [1, 1, 1, 1, 3, 4, 4]),
   (mkRat (2) 33, [1, 1, 1, 1, 11]),
   (mkRat (-1) 1728, [1, 1, 1, 2, 2, 2, 2, 2, 2]),
   (mkRat (-1) 54, [1, 1, 1, 2, 2, 2, 6]),
   (mkRat (-1) 45, [1, 1, 1, 2, 2, 3, 5]),
   (mkRat (1) 32, [1, 1, 1, 2, 2, 4, 4]),
   (mkRat (1) 729, [1, 1, 1, 3, 3, 3, 3]),
   (mkRat (4) 81, [1, 1, 1, 3, 9]),
   (mkRat (-1) 24, [1, 1, 1, 4, 8]),
   (mkRat (4) 105, [1, 1, 1, 5, 7]),
   (mkRat (1) 54, [1, 1, 1, 6, 6]),
   (mkRat (-1) 240, [1, 2, 2, 2, 2, 2, 4]),
   (mkRat (1) 144, [1, 2, 2, 2, 2, 3, 3]),
   (mkRat (1) 24, [1, 2, 2, 2, 8]),
   (mkRat (1) 21, [1, 2, 2, 3, 7]),
   (mkRat (-1) 24, [1, 2, 2, 4, 6]),
   (mkRat (1) 50, [1, 2, 2, 5, 5]),
   (mkRat (-4) 405, [1, 3, 3, 3, 5]),
   (mkRat (1) 24, [1, 3, 3, 4, 4]),
   (mkRat (-4) 33, [1, 3, 11]),
   (mkRat (1) 10, [1, 4, 10]),
   (mkRat (-4) 45, [1, 5, 9]),
   (mkRat (-1) 12, [1, 6, 8])]

def sc725Part4 : RawPoly ℕ :=
  [(mkRat (-2) 49, [1, 7, 7]),
   (mkRat (1) 864, [2, 2, 2, 2, 2, 2, 3]),
   (mkRat (1) 56, [2, 2, 2, 2, 7]),
   (mkRat (1) 27, [2, 2, 2, 3, 6]),
   (mkRat (-1) 30, [2, 2, 2, 4, 5]),
   (mkRat (1) 45, [2, 2, 3, 3, 5]),
   (mkRat (-1) 16, [2, 2, 3, 4, 4]),
   (mkRat (1) 11, [2, 2, 11]),
   (mkRat (-2) 3645, [3, 3, 3, 3, 3]),
   (mkRat (-4) 81, [3, 3, 9]),
   (mkRat (1) 12, [3, 4, 8]),
   (mkRat (-8) 105, [3, 5, 7]),
   (mkRat (-1) 27, [3, 6, 6]),
   (mkRat (3) 28, [4, 4, 7]),
   (mkRat (1) 15, [4, 5, 6]),
   (mkRat (-4) 375, [5, 5, 5]),
   (mkRat (-4) 15, [15])]

def sc725 : RawPoly ℕ :=
  [sc725Part0,
   sc725Part1,
   sc725Part2,
   sc725Part3,
   sc725Part4].flatten

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc725_check :
    reduceTwo (prependC 1 sc346 ++ scaleR (-1) (prependC 0 sc347)) = sc725 := by
  decide +kernel

theorem sc725_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc725 = evRc a c (expWordR [1, 2, 4] (8)) := by
  rw [← sc725_check]
  exact expTwo_step _ _ hc 0 [2, 4] (8)
    sc346 sc347 (sc346_sound a c hc) (sc347_sound a c hc)

def sc726Part0 : RawPoly ℕ :=
  [(mkRat (1) 5837832000, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (1) 13267800, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3]),
   (mkRat (-1) 2993760, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2]),
   (mkRat (1) 346500, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5]),
   (mkRat (1) 127575, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3]),
   (mkRat (-1) 19440, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3]),
   (mkRat (1) 11340, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7]),
   (mkRat (-1) 13440, [0, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2]),
   (mkRat (1) 3150, [0, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5]),
   (mkRat (-1) 2240, [0, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4]),
   (mkRat (-1) 1260, [0, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5]),
   (mkRat (1) 5103, [0, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3]),
   (mkRat (1) 567, [0, 1, 1, 1, 1, 1, 1, 1, 9]),
   (mkRat (1) 540, [0, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4]),
   (mkRat (-1) 810, [0, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3]),
   (mkRat (4) 945, [0, 1, 1, 1, 1, 1, 1, 3, 7]),
   (mkRat (-1) 270, [0, 1, 1, 1, 1, 1, 1, 4, 6]),
   (mkRat (2) 1125, [0, 1, 1, 1, 1, 1, 1, 5, 5]),
   (mkRat (-1) 480, [0, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3]),
   (mkRat (-1) 140, [0, 1, 1, 1, 1, 1, 2, 2, 7]),
   (mkRat (1) 225, [0, 1, 1, 1, 1, 1, 3, 3, 5]),
   (mkRat (-1) 80, [0, 1, 1, 1, 1, 1, 3, 4, 4]),
   (mkRat (1) 55, [0, 1, 1, 1, 1, 1, 11]),
   (mkRat (-1) 3456, [0, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2])]

def sc726Part1 : RawPoly ℕ :=
  [(mkRat (-1) 108, [0, 1, 1, 1, 1, 2, 2, 2, 6]),
   (mkRat (-1) 90, [0, 1, 1, 1, 1, 2, 2, 3, 5]),
   (mkRat (1) 64, [0, 1, 1, 1, 1, 2, 2, 4, 4]),
   (mkRat (1) 1458, [0, 1, 1, 1, 1, 3, 3, 3, 3]),
   (mkRat (2) 81, [0, 1, 1, 1, 1, 3, 9]),
   (mkRat (-1) 48, [0, 1, 1, 1, 1, 4, 8]),
   (mkRat (2) 105, [0, 1, 1, 1, 1, 5, 7]),
   (mkRat (1) 108, [0, 1, 1, 1, 1, 6, 6]),
   (mkRat (-1) 240, [0, 1, 1, 1, 2, 2, 2, 2, 5]),
   (mkRat (1) 108, [0, 1, 1, 1, 2, 2, 2, 3, 4]),
   (mkRat (-1) 486, [0, 1, 1, 1, 2, 2, 3, 3, 3]),
   (mkRat (-1) 54, [0, 1, 1, 1, 2, 2, 9]),
   (mkRat (2) 189, [0, 1, 1, 1, 3, 3, 7]),
   (mkRat (-1) 54, [0, 1, 1, 1, 3, 4, 6]),
   (mkRat (2) 225, [0, 1, 1, 1, 3, 5, 5]),
   (mkRat (-1) 40, [0, 1, 1, 1, 4, 4, 5]),
   (mkRat (2) 39, [0, 1, 1, 1, 13]),
   (mkRat (1) 1728, [0, 1, 2, 2, 2, 2, 2, 2, 3]),
   (mkRat (1) 112, [0, 1, 2, 2, 2, 2, 7]),
   (mkRat (1) 54, [0, 1, 2, 2, 2, 3, 6]),
   (mkRat (-1) 60, [0, 1, 2, 2, 2, 4, 5]),
   (mkRat (1) 90, [0, 1, 2, 2, 3, 3, 5]),
   (mkRat (-1) 32, [0, 1, 2, 2, 3, 4, 4]),
   (mkRat (1) 22, [0, 1, 2, 2, 11])]

def sc726Part2 : RawPoly ℕ :=
  [(mkRat (-1) 3645, [0, 1, 3, 3, 3, 3, 3]),
   (mkRat (-2) 81, [0, 1, 3, 3, 9]),
   (mkRat (1) 24, [0, 1, 3, 4, 8]),
   (mkRat (-4) 105, [0, 1, 3, 5, 7]),
   (mkRat (-1) 54, [0, 1, 3, 6, 6]),
   (mkRat (3) 56, [0, 1, 4, 4, 7]),
   (mkRat (1) 30, [0, 1, 4, 5, 6]),
   (mkRat (-2) 375, [0, 1, 5, 5, 5]),
   (mkRat (-2) 15, [0, 1, 15]),
   (mkRat (1) 46080, [0, 2, 2, 2, 2, 2, 2, 2, 2]),
   (mkRat (1) 360, [0, 2, 2, 2, 2, 2, 6]),
   (mkRat (1) 120, [0, 2, 2, 2, 2, 3, 5]),
   (mkRat (-3) 256, [0, 2, 2, 2, 2, 4, 4]),
   (mkRat (-1) 108, [0, 2, 2, 2, 3, 3, 4]),
   (mkRat (1) 30, [0, 2, 2, 2, 10]),
   (mkRat (1) 972, [0, 2, 2, 3, 3, 3, 3]),
   (mkRat (1) 27, [0, 2, 2, 3, 9]),
   (mkRat (-1) 32, [0, 2, 2, 4, 8]),
   (mkRat (1) 35, [0, 2, 2, 5, 7]),
   (mkRat (1) 72, [0, 2, 2, 6, 6]),
   (mkRat (-4) 567, [0, 3, 3, 3, 7]),
   (mkRat (1) 54, [0, 3, 3, 4, 6]),
   (mkRat (-2) 225, [0, 3, 3, 5, 5]),
   (mkRat (1) 20, [0, 3, 4, 4, 5])]

def sc726Part3 : RawPoly ℕ :=
  [(mkRat (-4) 39, [0, 3, 13]),
   (mkRat (7) 768, [0, 4, 4, 4, 4]),
   (mkRat (1) 12, [0, 4, 12]),
   (mkRat (-4) 55, [0, 5, 11]),
   (mkRat (-1) 15, [0, 6, 10]),
   (mkRat (-4) 63, [0, 7, 9]),
   (mkRat (-1) 32, [0, 8, 8]),
   (mkRat (-1) 1496880, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4]),
   (mkRat (-1) 85050, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2]),
   (mkRat (1) 42525, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6]),
   (mkRat (-1) 9720, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4]),
   (mkRat (1) 3360, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4]),
   (mkRat (1) 1680, [1, 1, 1, 1, 1, 1, 1, 1, 8]),
   (mkRat (-1) 1134, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3]),
   (mkRat (1) 567, [1, 1, 1, 1, 1, 1, 1, 3, 6]),
   (mkRat (-1) 630, [1, 1, 1, 1, 1, 1, 1, 4, 5]),
   (mkRat (-1) 2700, [1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2]),
   (mkRat (-1) 270, [1, 1, 1, 1, 1, 1, 2, 2, 6]),
   (mkRat (-1) 405, [1, 1, 1, 1, 1, 1, 3, 3, 4]),
   (mkRat (2) 225, [1, 1, 1, 1, 1, 1, 10]),
   (mkRat (-1) 150, [1, 1, 1, 1, 1, 2, 2, 2, 5]),
   (mkRat (1) 120, [1, 1, 1, 1, 1, 2, 2, 3, 4]),
   (mkRat (1) 60, [1, 1, 1, 1, 1, 3, 8]),
   (mkRat (-1) 70, [1, 1, 1, 1, 1, 4, 7])]

def sc726Part4 : RawPoly ℕ :=
  [(mkRat (1) 75, [1, 1, 1, 1, 1, 5, 6]),
   (mkRat (1) 192, [1, 1, 1, 1, 2, 2, 2, 2, 4]),
   (mkRat (-1) 162, [1, 1, 1, 1, 2, 2, 2, 3, 3]),
   (mkRat (-1) 48, [1, 1, 1, 1, 2, 2, 8]),
   (mkRat (1) 81, [1, 1, 1, 1, 3, 3, 6]),
   (mkRat (-1) 45, [1, 1, 1, 1, 3, 4, 5]),
   (mkRat (-5) 288, [1, 1, 1, 1, 4, 4, 4]),
   (mkRat (1) 18, [1, 1, 1, 1, 12]),
   (mkRat (-1) 540, [1, 1, 1, 2, 2, 2, 2, 2, 3]),
   (mkRat (-1) 63, [1, 1, 1, 2, 2, 2, 7]),
   (mkRat (-1) 54, [1, 1, 1, 2, 2, 3, 6]),
   (mkRat (1) 60, [1, 1, 1, 2, 2, 4, 5]),
   (mkRat (-1) 243, [1, 1, 1, 3, 3, 3, 4]),
   (mkRat (2) 45, [1, 1, 1, 3, 10]),
   (mkRat (-1) 27, [1, 1, 1, 4, 9]),
   (mkRat (1) 30, [1, 1, 1, 5, 8]),
   (mkRat (2) 63, [1, 1, 1, 6, 7]),
   (mkRat (1) 300, [1, 2, 2, 2, 2, 2, 5]),
   (mkRat (-1) 96, [1, 2, 2, 2, 2, 3, 4]),
   (mkRat (1) 243, [1, 2, 2, 2, 3, 3, 3]),
   (mkRat (1) 27, [1, 2, 2, 2, 9]),
   (mkRat (1) 24, [1, 2, 2, 3, 8]),
   (mkRat (-1) 28, [1, 2, 2, 4, 7]),
   (mkRat (1) 30, [1, 2, 2, 5, 6])]

def sc726Part5 : RawPoly ℕ :=
  [(mkRat (-2) 243, [1, 3, 3, 3, 6]),
   (mkRat (1) 45, [1, 3, 3, 4, 5]),
   (mkRat (5) 144, [1, 3, 4, 4, 4]),
   (mkRat (-1) 9, [1, 3, 12]),
   (mkRat (1) 11, [1, 4, 11]),
   (mkRat (-2) 25, [1, 5, 10]),
   (mkRat (-2) 27, [1, 6, 9]),
   (mkRat (-1) 14, [1, 7, 8]),
   (mkRat (-1) 1152, [2, 2, 2, 2, 2, 2, 4]),
   (mkRat (1) 540, [2, 2, 2, 2, 2, 3, 3]),
   (mkRat (1) 64, [2, 2, 2, 2, 8]),
   (mkRat (2) 63, [2, 2, 2, 3, 7]),
   (mkRat (-1) 36, [2, 2, 2, 4, 6]),
   (mkRat (1) 75, [2, 2, 2, 5, 5]),
   (mkRat (1) 54, [2, 2, 3, 3, 6]),
   (mkRat (-1) 30, [2, 2, 3, 4, 5]),
   (mkRat (-5) 192, [2, 2, 4, 4, 4]),
   (mkRat (1) 12, [2, 2, 12]),
   (mkRat (1) 486, [3, 3, 3, 3, 4]),
   (mkRat (-2) 45, [3, 3, 10]),
   (mkRat (2) 27, [3, 4, 9]),
   (mkRat (-1) 15, [3, 5, 8]),
   (mkRat (-4) 63, [3, 6, 7]),
   (mkRat (3) 32, [4, 4, 8])]

def sc726Part6 : RawPoly ℕ :=
  [(mkRat (2) 35, [4, 5, 7]),
   (mkRat (1) 36, [4, 6, 6]),
   (mkRat (-2) 75, [5, 5, 6]),
   (mkRat (-1) 4, [16])]

def sc726 : RawPoly ℕ :=
  [sc726Part0,
   sc726Part1,
   sc726Part2,
   sc726Part3,
   sc726Part4,
   sc726Part5,
   sc726Part6].flatten

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc726_check :
    reduceTwo (prependC 1 sc347 ++ scaleR (-1) (prependC 0 sc348)) = sc726 := by
  decide +kernel

theorem sc726_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc726 = evRc a c (expWordR [1, 2, 4] (9)) := by
  rw [← sc726_check]
  exact expTwo_step _ _ hc 0 [2, 4] (9)
    sc347 sc348 (sc347_sound a c hc) (sc348_sound a c hc)

def sc727 : RawPoly ℕ :=
  [(mkRat (2) 3, [1, 1, 1]),
   (mkRat (-4) 3, [3])]

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc727_check :
    reduceTwo (prependC 1 sc350 ++ scaleR (-1) (prependC 0 sc351)) = sc727 := by
  decide +kernel

theorem sc727_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc727 = evRc a c (expWordR [1, 2, 5] (-5)) := by
  rw [← sc727_check]
  exact expTwo_step _ _ hc 0 [2, 5] (-5)
    sc350 sc351 (sc350_sound a c hc) (sc351_sound a c hc)

def sc728 : RawPoly ℕ :=
  [(mkRat (1) 3, [0, 1, 1, 1, 1]),
   (mkRat (-2) 3, [0, 1, 3]),
   (mkRat (1) 2, [0, 2, 2]),
   (-1, [4])]

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc728_check :
    reduceTwo (prependC 1 sc351 ++ scaleR (-1) (prependC 0 sc352)) = sc728 := by
  decide +kernel

theorem sc728_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc728 = evRc a c (expWordR [1, 2, 5] (-4)) := by
  rw [← sc728_check]
  exact expTwo_step _ _ hc 0 [2, 5] (-4)
    sc351 sc352 (sc351_sound a c hc) (sc352_sound a c hc)

def sc729 : RawPoly ℕ :=
  [(mkRat (-1) 2, [0, 1, 4]),
   (mkRat (1) 5, [1, 1, 1, 1, 1]),
   (mkRat (1) 2, [1, 2, 2]),
   (mkRat (6) 5, [5])]

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc729_check :
    reduceTwo (prependC 1 sc352 ++ scaleR (-1) (prependC 0 sc353)) = sc729 := by
  decide +kernel

theorem sc729_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc729 = evRc a c (expWordR [1, 2, 5] (-3)) := by
  rw [← sc729_check]
  exact expTwo_step _ _ hc 0 [2, 5] (-3)
    sc352 sc353 (sc352_sound a c hc) (sc353_sound a c hc)

def sc730 : RawPoly ℕ :=
  [(mkRat (2) 45, [0, 1, 1, 1, 1, 1, 1]),
   (mkRat (2) 9, [0, 1, 1, 1, 3]),
   (mkRat (3) 5, [0, 1, 5]),
   (mkRat (-2) 9, [0, 3, 3]),
   (mkRat (1) 3, [2, 2, 2]),
   (mkRat (-2) 3, [6])]

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc730_check :
    reduceTwo (prependC 1 sc353 ++ scaleR (-1) (prependC 0 sc354)) = sc730 := by
  decide +kernel

theorem sc730_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc730 = evRc a c (expWordR [1, 2, 5] (-2)) := by
  rw [← sc730_check]
  exact expTwo_step _ _ hc 0 [2, 5] (-2)
    sc353 sc354 (sc353_sound a c hc) (sc354_sound a c hc)

def sc731 : RawPoly ℕ :=
  [(mkRat (1) 6, [0, 1, 1, 1, 4]),
   (mkRat (1) 6, [0, 1, 2, 2, 2]),
   (mkRat (-1) 3, [0, 1, 6]),
   (mkRat (-1) 3, [0, 3, 4]),
   (mkRat (1) 63, [1, 1, 1, 1, 1, 1, 1]),
   (mkRat (2) 9, [1, 1, 1, 1, 3]),
   (mkRat (-1) 6, [1, 1, 1, 2, 2]),
   (mkRat (-2) 9, [1, 3, 3]),
   (mkRat (1) 3, [2, 2, 3]),
   (mkRat (-4) 7, [7])]

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc731_check :
    reduceTwo (prependC 1 sc354 ++ scaleR (-1) (prependC 0 sc355)) = sc731 := by
  decide +kernel

theorem sc731_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc731 = evRc a c (expWordR [1, 2, 5] (-1)) := by
  rw [← sc731_check]
  exact expTwo_step _ _ hc 0 [2, 5] (-1)
    sc354 sc355 (sc354_sound a c hc) (sc355_sound a c hc)

def sc732 : RawPoly ℕ :=
  [(mkRat (1) 420, [0, 1, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (1) 15, [0, 1, 1, 1, 1, 1, 3]),
   (mkRat (-1) 12, [0, 1, 1, 1, 1, 2, 2]),
   (mkRat (-1) 5, [0, 1, 1, 1, 5]),
   (mkRat (1) 6, [0, 1, 2, 2, 3]),
   (mkRat (-2) 7, [0, 1, 7]),
   (mkRat (1) 16, [0, 2, 2, 2, 2]),
   (mkRat (2) 5, [0, 3, 5]),
   (mkRat (-1) 8, [0, 4, 4]),
   (mkRat (1) 6, [1, 1, 1, 1, 4]),
   (mkRat (-1) 3, [1, 3, 4]),
   (mkRat (1) 4, [2, 2, 4]),
   (mkRat (-1) 2, [8])]

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc732_check :
    reduceTwo (prependC 1 sc355 ++ scaleR (-1) (prependC 0 sc356)) = sc732 := by
  decide +kernel

theorem sc732_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc732 = evRc a c (expWordR [1, 2, 5] (0)) := by
  rw [← sc732_check]
  exact expTwo_step _ _ hc 0 [2, 5] (0)
    sc355 sc356 (sc355_sound a c hc) (sc356_sound a c hc)

def sc733 : RawPoly ℕ :=
  [(mkRat (1) 20, [0, 1, 1, 1, 1, 1, 4]),
   (mkRat (-1) 18, [0, 1, 1, 1, 2, 2, 2]),
   (mkRat (1) 9, [0, 1, 1, 1, 6]),
   (mkRat (1) 8, [0, 1, 2, 2, 4]),
   (mkRat (-1) 4, [0, 1, 8]),
   (mkRat (1) 9, [0, 2, 2, 2, 3]),
   (mkRat (-2) 9, [0, 3, 6]),
   (mkRat (3) 10, [0, 4, 5]),
   (mkRat (1) 1620, [1, 1, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (4) 135, [1, 1, 1, 1, 1, 1, 3]),
   (mkRat (-1) 20, [1, 1, 1, 1, 1, 2, 2]),
   (mkRat (-1) 5, [1, 1, 1, 1, 5]),
   (mkRat (2) 27, [1, 1, 1, 3, 3]),
   (mkRat (1) 16, [1, 2, 2, 2, 2]),
   (mkRat (2) 5, [1, 3, 5]),
   (mkRat (-1) 8, [1, 4, 4]),
   (mkRat (-3) 10, [2, 2, 5]),
   (mkRat (-4) 81, [3, 3, 3]),
   (mkRat (-4) 9, [9])]

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc733_check :
    reduceTwo (prependC 1 sc356 ++ scaleR (-1) (prependC 0 sc357)) = sc733 := by
  decide +kernel

theorem sc733_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc733 = evRc a c (expWordR [1, 2, 5] (1)) := by
  rw [← sc733_check]
  exact expTwo_step _ _ hc 0 [2, 5] (1)
    sc356 sc357 (sc356_sound a c hc) (sc357_sound a c hc)

def sc734Part0 : RawPoly ℕ :=
  [(mkRat (1) 14175, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (1) 189, [0, 1, 1, 1, 1, 1, 1, 1, 3]),
   (mkRat (-1) 90, [0, 1, 1, 1, 1, 1, 1, 2, 2]),
   (mkRat (-3) 50, [0, 1, 1, 1, 1, 1, 5]),
   (mkRat (1) 27, [0, 1, 1, 1, 1, 3, 3]),
   (mkRat (-1) 18, [0, 1, 1, 1, 2, 2, 3]),
   (mkRat (2) 21, [0, 1, 1, 1, 7]),
   (mkRat (-3) 20, [0, 1, 2, 2, 5]),
   (mkRat (-2) 81, [0, 1, 3, 3, 3]),
   (mkRat (-2) 9, [0, 1, 9]),
   (mkRat (1) 12, [0, 2, 2, 2, 4]),
   (mkRat (1) 18, [0, 2, 2, 3, 3]),
   (mkRat (-4) 21, [0, 3, 7]),
   (mkRat (-1) 6, [0, 4, 6]),
   (mkRat (8) 25, [0, 5, 5]),
   (mkRat (1) 45, [1, 1, 1, 1, 1, 1, 4]),
   (mkRat (-1) 18, [1, 1, 1, 1, 2, 2, 2]),
   (mkRat (1) 9, [1, 1, 1, 1, 6]),
   (mkRat (1) 9, [1, 1, 1, 3, 4]),
   (mkRat (1) 9, [1, 2, 2, 2, 3]),
   (mkRat (-2) 9, [1, 3, 6]),
   (mkRat (3) 10, [1, 4, 5]),
   (mkRat (1) 60, [2, 2, 2, 2, 2]),
   (mkRat (1) 6, [2, 2, 6])]

def sc734Part1 : RawPoly ℕ :=
  [(mkRat (-1) 9, [3, 3, 4]),
   (mkRat (-2) 5, [10])]

def sc734 : RawPoly ℕ :=
  [sc734Part0,
   sc734Part1].flatten

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc734_check :
    reduceTwo (prependC 1 sc357 ++ scaleR (-1) (prependC 0 sc358)) = sc734 := by
  decide +kernel

theorem sc734_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc734 = evRc a c (expWordR [1, 2, 5] (2)) := by
  rw [← sc734_check]
  exact expTwo_step _ _ hc 0 [2, 5] (2)
    sc357 sc358 (sc357_sound a c hc) (sc358_sound a c hc)

def sc735Part0 : RawPoly ℕ :=
  [(mkRat (1) 252, [0, 1, 1, 1, 1, 1, 1, 1, 4]),
   (mkRat (-1) 60, [0, 1, 1, 1, 1, 1, 2, 2, 2]),
   (mkRat (1) 30, [0, 1, 1, 1, 1, 1, 6]),
   (mkRat (1) 18, [0, 1, 1, 1, 1, 3, 4]),
   (mkRat (-1) 24, [0, 1, 1, 1, 2, 2, 4]),
   (mkRat (1) 12, [0, 1, 1, 1, 8]),
   (mkRat (1) 120, [0, 1, 2, 2, 2, 2, 2]),
   (mkRat (1) 12, [0, 1, 2, 2, 6]),
   (mkRat (-1) 18, [0, 1, 3, 3, 4]),
   (mkRat (-1) 5, [0, 1, 10]),
   (mkRat (-1) 10, [0, 2, 2, 2, 5]),
   (mkRat (1) 12, [0, 2, 2, 3, 4]),
   (mkRat (-1) 6, [0, 3, 8]),
   (mkRat (-1) 7, [0, 4, 7]),
   (mkRat (1) 5, [0, 5, 6]),
   (mkRat (1) 69300, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (1) 630, [1, 1, 1, 1, 1, 1, 1, 1, 3]),
   (mkRat (-1) 252, [1, 1, 1, 1, 1, 1, 1, 2, 2]),
   (mkRat (-2) 75, [1, 1, 1, 1, 1, 1, 5]),
   (mkRat (1) 45, [1, 1, 1, 1, 1, 3, 3]),
   (mkRat (-1) 18, [1, 1, 1, 1, 2, 2, 3]),
   (mkRat (2) 21, [1, 1, 1, 1, 7]),
   (mkRat (-1) 48, [1, 1, 1, 2, 2, 2, 2]),
   (mkRat (-2) 15, [1, 1, 1, 3, 5])]

def sc735Part1 : RawPoly ℕ :=
  [(mkRat (1) 24, [1, 1, 1, 4, 4]),
   (mkRat (1) 12, [1, 2, 2, 2, 4]),
   (mkRat (1) 18, [1, 2, 2, 3, 3]),
   (mkRat (-4) 21, [1, 3, 7]),
   (mkRat (-1) 6, [1, 4, 6]),
   (mkRat (8) 25, [1, 5, 5]),
   (mkRat (1) 24, [2, 2, 2, 2, 3]),
   (mkRat (1) 7, [2, 2, 7]),
   (mkRat (2) 15, [3, 3, 5]),
   (mkRat (-1) 12, [3, 4, 4]),
   (mkRat (-4) 11, [11])]

def sc735 : RawPoly ℕ :=
  [sc735Part0,
   sc735Part1].flatten

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc735_check :
    reduceTwo (prependC 1 sc358 ++ scaleR (-1) (prependC 0 sc359)) = sc735 := by
  decide +kernel

theorem sc735_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc735 = evRc a c (expWordR [1, 2, 5] (3)) := by
  rw [← sc735_check]
  exact expTwo_step _ _ hc 0 [2, 5] (3)
    sc358 sc359 (sc358_sound a c hc) (sc359_sound a c hc)

def sc736Part0 : RawPoly ℕ :=
  [(mkRat (1) 748440, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (1) 4860, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3]),
   (mkRat (-1) 1680, [0, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2]),
   (mkRat (-1) 210, [0, 1, 1, 1, 1, 1, 1, 1, 5]),
   (mkRat (2) 405, [0, 1, 1, 1, 1, 1, 1, 3, 3]),
   (mkRat (-1) 60, [0, 1, 1, 1, 1, 1, 2, 2, 3]),
   (mkRat (1) 35, [0, 1, 1, 1, 1, 1, 7]),
   (mkRat (-1) 96, [0, 1, 1, 1, 1, 2, 2, 2, 2]),
   (mkRat (-1) 15, [0, 1, 1, 1, 1, 3, 5]),
   (mkRat (1) 48, [0, 1, 1, 1, 1, 4, 4]),
   (mkRat (1) 20, [0, 1, 1, 1, 2, 2, 5]),
   (mkRat (2) 243, [0, 1, 1, 1, 3, 3, 3]),
   (mkRat (2) 27, [0, 1, 1, 1, 9]),
   (mkRat (1) 48, [0, 1, 2, 2, 2, 2, 3]),
   (mkRat (1) 14, [0, 1, 2, 2, 7]),
   (mkRat (1) 15, [0, 1, 3, 3, 5]),
   (mkRat (-1) 24, [0, 1, 3, 4, 4]),
   (mkRat (-2) 11, [0, 1, 11]),
   (mkRat (1) 576, [0, 2, 2, 2, 2, 2, 2]),
   (mkRat (1) 18, [0, 2, 2, 2, 6]),
   (mkRat (-1) 10, [0, 2, 2, 3, 5]),
   (mkRat (1) 32, [0, 2, 2, 4, 4]),
   (mkRat (-1) 243, [0, 3, 3, 3, 3]),
   (mkRat (-4) 27, [0, 3, 9])]

def sc736Part1 : RawPoly ℕ :=
  [(mkRat (-1) 8, [0, 4, 8]),
   (mkRat (6) 35, [0, 5, 7]),
   (mkRat (-1) 18, [0, 6, 6]),
   (mkRat (1) 840, [1, 1, 1, 1, 1, 1, 1, 1, 4]),
   (mkRat (-1) 135, [1, 1, 1, 1, 1, 1, 2, 2, 2]),
   (mkRat (2) 135, [1, 1, 1, 1, 1, 1, 6]),
   (mkRat (1) 30, [1, 1, 1, 1, 1, 3, 4]),
   (mkRat (-1) 24, [1, 1, 1, 1, 2, 2, 4]),
   (mkRat (1) 12, [1, 1, 1, 1, 8]),
   (mkRat (-1) 27, [1, 1, 1, 2, 2, 2, 3]),
   (mkRat (2) 27, [1, 1, 1, 3, 6]),
   (mkRat (-1) 10, [1, 1, 1, 4, 5]),
   (mkRat (-1) 10, [1, 2, 2, 2, 5]),
   (mkRat (1) 12, [1, 2, 2, 3, 4]),
   (mkRat (-1) 6, [1, 3, 8]),
   (mkRat (-1) 7, [1, 4, 7]),
   (mkRat (1) 5, [1, 5, 6]),
   (mkRat (1) 32, [2, 2, 2, 2, 4]),
   (mkRat (1) 27, [2, 2, 2, 3, 3]),
   (mkRat (1) 8, [2, 2, 8]),
   (mkRat (-2) 27, [3, 3, 6]),
   (mkRat (1) 5, [3, 4, 5]),
   (mkRat (-1) 48, [4, 4, 4]),
   (mkRat (-1) 3, [12])]

def sc736 : RawPoly ℕ :=
  [sc736Part0,
   sc736Part1].flatten

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc736_check :
    reduceTwo (prependC 1 sc359 ++ scaleR (-1) (prependC 0 sc360)) = sc736 := by
  decide +kernel

theorem sc736_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc736 = evRc a c (expWordR [1, 2, 5] (4)) := by
  rw [← sc736_check]
  exact expTwo_step _ _ hc 0 [2, 5] (4)
    sc359 sc360 (sc359_sound a c hc) (sc360_sound a c hc)

def sc737Part0 : RawPoly ℕ :=
  [(mkRat (1) 6480, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4]),
   (mkRat (-1) 756, [0, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2]),
   (mkRat (1) 378, [0, 1, 1, 1, 1, 1, 1, 1, 6]),
   (mkRat (1) 135, [0, 1, 1, 1, 1, 1, 1, 3, 4]),
   (mkRat (-1) 80, [0, 1, 1, 1, 1, 1, 2, 2, 4]),
   (mkRat (1) 40, [0, 1, 1, 1, 1, 1, 8]),
   (mkRat (-1) 54, [0, 1, 1, 1, 1, 2, 2, 2, 3]),
   (mkRat (1) 27, [0, 1, 1, 1, 1, 3, 6]),
   (mkRat (-1) 20, [0, 1, 1, 1, 1, 4, 5]),
   (mkRat (-1) 360, [0, 1, 1, 1, 2, 2, 2, 2, 2]),
   (mkRat (-1) 36, [0, 1, 1, 1, 2, 2, 6]),
   (mkRat (1) 54, [0, 1, 1, 1, 3, 3, 4]),
   (mkRat (1) 15, [0, 1, 1, 1, 10]),
   (mkRat (1) 64, [0, 1, 2, 2, 2, 2, 4]),
   (mkRat (1) 54, [0, 1, 2, 2, 2, 3, 3]),
   (mkRat (1) 16, [0, 1, 2, 2, 8]),
   (mkRat (-1) 27, [0, 1, 3, 3, 6]),
   (mkRat (1) 10, [0, 1, 3, 4, 5]),
   (mkRat (-1) 96, [0, 1, 4, 4, 4]),
   (mkRat (-1) 6, [0, 1, 12]),
   (mkRat (1) 180, [0, 2, 2, 2, 2, 2, 3]),
   (mkRat (1) 21, [0, 2, 2, 2, 7]),
   (mkRat (1) 18, [0, 2, 2, 3, 6]),
   (mkRat (-3) 40, [0, 2, 2, 4, 5])]

def sc737Part1 : RawPoly ℕ :=
  [(mkRat (-1) 81, [0, 3, 3, 3, 4]),
   (mkRat (-2) 15, [0, 3, 10]),
   (mkRat (-1) 9, [0, 4, 9]),
   (mkRat (3) 20, [0, 5, 8]),
   (mkRat (-2) 21, [0, 6, 7]),
   (mkRat (1) 4422600, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (2) 42525, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3]),
   (mkRat (-1) 6480, [1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2]),
   (mkRat (-1) 700, [1, 1, 1, 1, 1, 1, 1, 1, 5]),
   (mkRat (1) 567, [1, 1, 1, 1, 1, 1, 1, 3, 3]),
   (mkRat (-1) 135, [1, 1, 1, 1, 1, 1, 2, 2, 3]),
   (mkRat (4) 315, [1, 1, 1, 1, 1, 1, 7]),
   (mkRat (-1) 160, [1, 1, 1, 1, 1, 2, 2, 2, 2]),
   (mkRat (-1) 25, [1, 1, 1, 1, 1, 3, 5]),
   (mkRat (1) 80, [1, 1, 1, 1, 1, 4, 4]),
   (mkRat (1) 20, [1, 1, 1, 1, 2, 2, 5]),
   (mkRat (2) 243, [1, 1, 1, 1, 3, 3, 3]),
   (mkRat (2) 27, [1, 1, 1, 1, 9]),
   (mkRat (-1) 36, [1, 1, 1, 2, 2, 2, 4]),
   (mkRat (-1) 54, [1, 1, 1, 2, 2, 3, 3]),
   (mkRat (4) 63, [1, 1, 1, 3, 7]),
   (mkRat (1) 18, [1, 1, 1, 4, 6]),
   (mkRat (-8) 75, [1, 1, 1, 5, 5]),
   (mkRat (1) 576, [1, 2, 2, 2, 2, 2, 2])]

def sc737Part2 : RawPoly ℕ :=
  [(mkRat (1) 18, [1, 2, 2, 2, 6]),
   (mkRat (-1) 10, [1, 2, 2, 3, 5]),
   (mkRat (1) 32, [1, 2, 2, 4, 4]),
   (mkRat (-1) 243, [1, 3, 3, 3, 3]),
   (mkRat (-4) 27, [1, 3, 9]),
   (mkRat (-1) 8, [1, 4, 8]),
   (mkRat (6) 35, [1, 5, 7]),
   (mkRat (-1) 18, [1, 6, 6]),
   (mkRat (-3) 80, [2, 2, 2, 2, 5]),
   (mkRat (1) 18, [2, 2, 2, 3, 4]),
   (mkRat (1) 81, [2, 2, 3, 3, 3]),
   (mkRat (1) 9, [2, 2, 9]),
   (mkRat (-4) 63, [3, 3, 7]),
   (mkRat (-1) 9, [3, 4, 6]),
   (mkRat (16) 75, [3, 5, 5]),
   (mkRat (3) 40, [4, 4, 5]),
   (mkRat (-4) 13, [13])]

def sc737 : RawPoly ℕ :=
  [sc737Part0,
   sc737Part1,
   sc737Part2].flatten

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc737_check :
    reduceTwo (prependC 1 sc360 ++ scaleR (-1) (prependC 0 sc361)) = sc737 := by
  decide +kernel

theorem sc737_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc737 = evRc a c (expWordR [1, 2, 5] (5)) := by
  rw [← sc737_check]
  exact expTwo_step _ _ hc 0 [2, 5] (5)
    sc360 sc361 (sc360_sound a c hc) (sc361_sound a c hc)

def sc738Part0 : RawPoly ℕ :=
  [(mkRat (1) 56756700, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (1) 207900, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3]),
   (mkRat (-1) 56700, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2]),
   (mkRat (-1) 5400, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5]),
   (mkRat (1) 3780, [0, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3]),
   (mkRat (-1) 756, [0, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3]),
   (mkRat (1) 441, [0, 1, 1, 1, 1, 1, 1, 1, 7]),
   (mkRat (-1) 720, [0, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2]),
   (mkRat (-2) 225, [0, 1, 1, 1, 1, 1, 1, 3, 5]),
   (mkRat (1) 360, [0, 1, 1, 1, 1, 1, 1, 4, 4]),
   (mkRat (3) 200, [0, 1, 1, 1, 1, 1, 2, 2, 5]),
   (mkRat (1) 405, [0, 1, 1, 1, 1, 1, 3, 3, 3]),
   (mkRat (1) 45, [0, 1, 1, 1, 1, 1, 9]),
   (mkRat (-1) 72, [0, 1, 1, 1, 1, 2, 2, 2, 4]),
   (mkRat (-1) 108, [0, 1, 1, 1, 1, 2, 2, 3, 3]),
   (mkRat (2) 63, [0, 1, 1, 1, 1, 3, 7]),
   (mkRat (1) 36, [0, 1, 1, 1, 1, 4, 6]),
   (mkRat (-4) 75, [0, 1, 1, 1, 1, 5, 5]),
   (mkRat (-1) 144, [0, 1, 1, 1, 2, 2, 2, 2, 3]),
   (mkRat (-1) 42, [0, 1, 1, 1, 2, 2, 7]),
   (mkRat (-1) 45, [0, 1, 1, 1, 3, 3, 5]),
   (mkRat (1) 72, [0, 1, 1, 1, 3, 4, 4]),
   (mkRat (2) 33, [0, 1, 1, 1, 11]),
   (mkRat (-3) 160, [0, 1, 2, 2, 2, 2, 5])]

def sc738Part1 : RawPoly ℕ :=
  [(mkRat (1) 36, [0, 1, 2, 2, 2, 3, 4]),
   (mkRat (1) 162, [0, 1, 2, 2, 3, 3, 3]),
   (mkRat (1) 18, [0, 1, 2, 2, 9]),
   (mkRat (-2) 63, [0, 1, 3, 3, 7]),
   (mkRat (-1) 18, [0, 1, 3, 4, 6]),
   (mkRat (8) 75, [0, 1, 3, 5, 5]),
   (mkRat (3) 80, [0, 1, 4, 4, 5]),
   (mkRat (-2) 13, [0, 1, 13]),
   (mkRat (1) 240, [0, 2, 2, 2, 2, 2, 4]),
   (mkRat (1) 144, [0, 2, 2, 2, 2, 3, 3]),
   (mkRat (1) 24, [0, 2, 2, 2, 8]),
   (mkRat (1) 21, [0, 2, 2, 3, 7]),
   (mkRat (1) 24, [0, 2, 2, 4, 6]),
   (mkRat (-2) 25, [0, 2, 2, 5, 5]),
   (mkRat (2) 135, [0, 3, 3, 3, 5]),
   (mkRat (-1) 72, [0, 3, 3, 4, 4]),
   (mkRat (-4) 33, [0, 3, 11]),
   (mkRat (-1) 10, [0, 4, 10]),
   (mkRat (2) 15, [0, 5, 9]),
   (mkRat (-1) 12, [0, 6, 8]),
   (mkRat (-2) 49, [0, 7, 7]),
   (mkRat (1) 28350, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4]),
   (mkRat (-1) 2520, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2]),
   (mkRat (1) 1260, [1, 1, 1, 1, 1, 1, 1, 1, 6])]

def sc738Part2 : RawPoly ℕ :=
  [(mkRat (1) 378, [1, 1, 1, 1, 1, 1, 1, 3, 4]),
   (mkRat (-1) 180, [1, 1, 1, 1, 1, 1, 2, 2, 4]),
   (mkRat (1) 90, [1, 1, 1, 1, 1, 1, 8]),
   (mkRat (-1) 90, [1, 1, 1, 1, 1, 2, 2, 2, 3]),
   (mkRat (1) 45, [1, 1, 1, 1, 1, 3, 6]),
   (mkRat (-3) 100, [1, 1, 1, 1, 1, 4, 5]),
   (mkRat (-1) 360, [1, 1, 1, 1, 2, 2, 2, 2, 2]),
   (mkRat (-1) 36, [1, 1, 1, 1, 2, 2, 6]),
   (mkRat (1) 54, [1, 1, 1, 1, 3, 3, 4]),
   (mkRat (1) 15, [1, 1, 1, 1, 10]),
   (mkRat (1) 30, [1, 1, 1, 2, 2, 2, 5]),
   (mkRat (-1) 36, [1, 1, 1, 2, 2, 3, 4]),
   (mkRat (1) 18, [1, 1, 1, 3, 8]),
   (mkRat (1) 21, [1, 1, 1, 4, 7]),
   (mkRat (-1) 15, [1, 1, 1, 5, 6]),
   (mkRat (1) 180, [1, 2, 2, 2, 2, 2, 3]),
   (mkRat (1) 21, [1, 2, 2, 2, 7]),
   (mkRat (1) 18, [1, 2, 2, 3, 6]),
   (mkRat (-3) 40, [1, 2, 2, 4, 5]),
   (mkRat (-1) 81, [1, 3, 3, 3, 4]),
   (mkRat (-2) 15, [1, 3, 10]),
   (mkRat (-1) 9, [1, 4, 9]),
   (mkRat (3) 20, [1, 5, 8]),
   (mkRat (-2) 21, [1, 6, 7])]

def sc738Part3 : RawPoly ℕ :=
  [(mkRat (1) 3360, [2, 2, 2, 2, 2, 2, 2]),
   (mkRat (1) 48, [2, 2, 2, 2, 6]),
   (mkRat (-1) 15, [2, 2, 2, 3, 5]),
   (mkRat (1) 48, [2, 2, 2, 4, 4]),
   (mkRat (1) 36, [2, 2, 3, 3, 4]),
   (mkRat (1) 10, [2, 2, 10]),
   (mkRat (-1) 18, [3, 3, 8]),
   (mkRat (-2) 21, [3, 4, 7]),
   (mkRat (2) 15, [3, 5, 6]),
   (mkRat (-1) 24, [4, 4, 6]),
   (mkRat (4) 25, [4, 5, 5]),
   (mkRat (-2) 7, [14])]

def sc738 : RawPoly ℕ :=
  [sc738Part0,
   sc738Part1,
   sc738Part2,
   sc738Part3].flatten

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc738_check :
    reduceTwo (prependC 1 sc361 ++ scaleR (-1) (prependC 0 sc362)) = sc738 := by
  decide +kernel

theorem sc738_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc738 = evRc a c (expWordR [1, 2, 5] (6)) := by
  rw [← sc738_check]
  exact expTwo_step _ _ hc 0 [2, 5] (6)
    sc361 sc362 (sc361_sound a c hc) (sc362_sound a c hc)

def sc739Part0 : RawPoly ℕ :=
  [(mkRat (1) 277200, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4]),
   (mkRat (-1) 19440, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2]),
   (mkRat (1) 9720, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6]),
   (mkRat (1) 2520, [0, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4]),
   (mkRat (-1) 1008, [0, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4]),
   (mkRat (1) 504, [0, 1, 1, 1, 1, 1, 1, 1, 8]),
   (mkRat (-1) 405, [0, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3]),
   (mkRat (2) 405, [0, 1, 1, 1, 1, 1, 1, 3, 6]),
   (mkRat (-1) 150, [0, 1, 1, 1, 1, 1, 1, 4, 5]),
   (mkRat (-1) 1200, [0, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2]),
   (mkRat (-1) 120, [0, 1, 1, 1, 1, 1, 2, 2, 6]),
   (mkRat (1) 180, [0, 1, 1, 1, 1, 1, 3, 3, 4]),
   (mkRat (1) 50, [0, 1, 1, 1, 1, 1, 10]),
   (mkRat (1) 60, [0, 1, 1, 1, 1, 2, 2, 2, 5]),
   (mkRat (-1) 72, [0, 1, 1, 1, 1, 2, 2, 3, 4]),
   (mkRat (1) 36, [0, 1, 1, 1, 1, 3, 8]),
   (mkRat (1) 42, [0, 1, 1, 1, 1, 4, 7]),
   (mkRat (-1) 30, [0, 1, 1, 1, 1, 5, 6]),
   (mkRat (-1) 192, [0, 1, 1, 1, 2, 2, 2, 2, 4]),
   (mkRat (-1) 162, [0, 1, 1, 1, 2, 2, 2, 3, 3]),
   (mkRat (-1) 48, [0, 1, 1, 1, 2, 2, 8]),
   (mkRat (1) 81, [0, 1, 1, 1, 3, 3, 6]),
   (mkRat (-1) 30, [0, 1, 1, 1, 3, 4, 5]),
   (mkRat (1) 288, [0, 1, 1, 1, 4, 4, 4])]

def sc739Part1 : RawPoly ℕ :=
  [(mkRat (1) 18, [0, 1, 1, 1, 12]),
   (mkRat (1) 6720, [0, 1, 2, 2, 2, 2, 2, 2, 2]),
   (mkRat (1) 96, [0, 1, 2, 2, 2, 2, 6]),
   (mkRat (-1) 30, [0, 1, 2, 2, 2, 3, 5]),
   (mkRat (1) 96, [0, 1, 2, 2, 2, 4, 4]),
   (mkRat (1) 72, [0, 1, 2, 2, 3, 3, 4]),
   (mkRat (1) 20, [0, 1, 2, 2, 10]),
   (mkRat (-1) 36, [0, 1, 3, 3, 8]),
   (mkRat (-1) 21, [0, 1, 3, 4, 7]),
   (mkRat (1) 15, [0, 1, 3, 5, 6]),
   (mkRat (-1) 48, [0, 1, 4, 4, 6]),
   (mkRat (2) 25, [0, 1, 4, 5, 5]),
   (mkRat (-1) 7, [0, 1, 14]),
   (mkRat (-1) 200, [0, 2, 2, 2, 2, 2, 5]),
   (mkRat (1) 96, [0, 2, 2, 2, 2, 3, 4]),
   (mkRat (1) 243, [0, 2, 2, 2, 3, 3, 3]),
   (mkRat (1) 27, [0, 2, 2, 2, 9]),
   (mkRat (1) 24, [0, 2, 2, 3, 8]),
   (mkRat (1) 28, [0, 2, 2, 4, 7]),
   (mkRat (-1) 20, [0, 2, 2, 5, 6]),
   (mkRat (-2) 243, [0, 3, 3, 3, 6]),
   (mkRat (1) 30, [0, 3, 3, 4, 5]),
   (mkRat (-1) 144, [0, 3, 4, 4, 4]),
   (mkRat (-1) 9, [0, 3, 12])]

def sc739Part2 : RawPoly ℕ :=
  [(mkRat (-1) 11, [0, 4, 11]),
   (mkRat (3) 25, [0, 5, 10]),
   (mkRat (-2) 27, [0, 6, 9]),
   (mkRat (-1) 14, [0, 7, 8]),
   (mkRat (1) 392931000, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (1) 1122660, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3]),
   (mkRat (-1) 277200, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2]),
   (mkRat (-1) 23625, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5]),
   (mkRat (1) 14580, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3]),
   (mkRat (-1) 2520, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3]),
   (mkRat (1) 1470, [1, 1, 1, 1, 1, 1, 1, 1, 7]),
   (mkRat (-1) 2016, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2]),
   (mkRat (-1) 315, [1, 1, 1, 1, 1, 1, 1, 3, 5]),
   (mkRat (1) 1008, [1, 1, 1, 1, 1, 1, 1, 4, 4]),
   (mkRat (1) 150, [1, 1, 1, 1, 1, 1, 2, 2, 5]),
   (mkRat (4) 3645, [1, 1, 1, 1, 1, 1, 3, 3, 3]),
   (mkRat (4) 405, [1, 1, 1, 1, 1, 1, 9]),
   (mkRat (-1) 120, [1, 1, 1, 1, 1, 2, 2, 2, 4]),
   (mkRat (-1) 180, [1, 1, 1, 1, 1, 2, 2, 3, 3]),
   (mkRat (2) 105, [1, 1, 1, 1, 1, 3, 7]),
   (mkRat (1) 60, [1, 1, 1, 1, 1, 4, 6]),
   (mkRat (-4) 125, [1, 1, 1, 1, 1, 5, 5]),
   (mkRat (-1) 144, [1, 1, 1, 1, 2, 2, 2, 2, 3]),
   (mkRat (-1) 42, [1, 1, 1, 1, 2, 2, 7])]

def sc739Part3 : RawPoly ℕ :=
  [(mkRat (-1) 45, [1, 1, 1, 1, 3, 3, 5]),
   (mkRat (1) 72, [1, 1, 1, 1, 3, 4, 4]),
   (mkRat (2) 33, [1, 1, 1, 1, 11]),
   (mkRat (-1) 1728, [1, 1, 1, 2, 2, 2, 2, 2, 2]),
   (mkRat (-1) 54, [1, 1, 1, 2, 2, 2, 6]),
   (mkRat (1) 30, [1, 1, 1, 2, 2, 3, 5]),
   (mkRat (-1) 96, [1, 1, 1, 2, 2, 4, 4]),
   (mkRat (1) 729, [1, 1, 1, 3, 3, 3, 3]),
   (mkRat (4) 81, [1, 1, 1, 3, 9]),
   (mkRat (1) 24, [1, 1, 1, 4, 8]),
   (mkRat (-2) 35, [1, 1, 1, 5, 7]),
   (mkRat (1) 54, [1, 1, 1, 6, 6]),
   (mkRat (1) 240, [1, 2, 2, 2, 2, 2, 4]),
   (mkRat (1) 144, [1, 2, 2, 2, 2, 3, 3]),
   (mkRat (1) 24, [1, 2, 2, 2, 8]),
   (mkRat (1) 21, [1, 2, 2, 3, 7]),
   (mkRat (1) 24, [1, 2, 2, 4, 6]),
   (mkRat (-2) 25, [1, 2, 2, 5, 5]),
   (mkRat (2) 135, [1, 3, 3, 3, 5]),
   (mkRat (-1) 72, [1, 3, 3, 4, 4]),
   (mkRat (-4) 33, [1, 3, 11]),
   (mkRat (-1) 10, [1, 4, 10]),
   (mkRat (2) 15, [1, 5, 9]),
   (mkRat (-1) 12, [1, 6, 8])]

def sc739Part4 : RawPoly ℕ :=
  [(mkRat (-2) 49, [1, 7, 7]),
   (mkRat (1) 864, [2, 2, 2, 2, 2, 2, 3]),
   (mkRat (1) 56, [2, 2, 2, 2, 7]),
   (mkRat (1) 27, [2, 2, 2, 3, 6]),
   (mkRat (-1) 20, [2, 2, 2, 4, 5]),
   (mkRat (-1) 30, [2, 2, 3, 3, 5]),
   (mkRat (1) 48, [2, 2, 3, 4, 4]),
   (mkRat (1) 11, [2, 2, 11]),
   (mkRat (-2) 3645, [3, 3, 3, 3, 3]),
   (mkRat (-4) 81, [3, 3, 9]),
   (mkRat (-1) 12, [3, 4, 8]),
   (mkRat (4) 35, [3, 5, 7]),
   (mkRat (-1) 27, [3, 6, 6]),
   (mkRat (-1) 28, [4, 4, 7]),
   (mkRat (1) 10, [4, 5, 6]),
   (mkRat (26) 375, [5, 5, 5]),
   (mkRat (-4) 15, [15])]

def sc739 : RawPoly ℕ :=
  [sc739Part0,
   sc739Part1,
   sc739Part2,
   sc739Part3,
   sc739Part4].flatten

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc739_check :
    reduceTwo (prependC 1 sc362 ++ scaleR (-1) (prependC 0 sc363)) = sc739 := by
  decide +kernel

theorem sc739_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc739 = evRc a c (expWordR [1, 2, 5] (7)) := by
  rw [← sc739_check]
  exact expTwo_step _ _ hc 0 [2, 5] (7)
    sc362 sc363 (sc362_sound a c hc) (sc363_sound a c hc)

def sc740Part0 : RawPoly ℕ :=
  [(mkRat (1) 5837832000, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (1) 13267800, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3]),
   (mkRat (-1) 2993760, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2]),
   (mkRat (-1) 231000, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5]),
   (mkRat (1) 127575, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3]),
   (mkRat (-1) 19440, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3]),
   (mkRat (1) 11340, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7]),
   (mkRat (-1) 13440, [0, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2]),
   (mkRat (-1) 2100, [0, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5]),
   (mkRat (1) 6720, [0, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4]),
   (mkRat (1) 840, [0, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5]),
   (mkRat (1) 5103, [0, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3]),
   (mkRat (1) 567, [0, 1, 1, 1, 1, 1, 1, 1, 9]),
   (mkRat (-1) 540, [0, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4]),
   (mkRat (-1) 810, [0, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3]),
   (mkRat (4) 945, [0, 1, 1, 1, 1, 1, 1, 3, 7]),
   (mkRat (1) 270, [0, 1, 1, 1, 1, 1, 1, 4, 6]),
   (mkRat (-8) 1125, [0, 1, 1, 1, 1, 1, 1, 5, 5]),
   (mkRat (-1) 480, [0, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3]),
   (mkRat (-1) 140, [0, 1, 1, 1, 1, 1, 2, 2, 7]),
   (mkRat (-1) 150, [0, 1, 1, 1, 1, 1, 3, 3, 5]),
   (mkRat (1) 240, [0, 1, 1, 1, 1, 1, 3, 4, 4]),
   (mkRat (1) 55, [0, 1, 1, 1, 1, 1, 11]),
   (mkRat (-1) 3456, [0, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2])]

def sc740Part1 : RawPoly ℕ :=
  [(mkRat (-1) 108, [0, 1, 1, 1, 1, 2, 2, 2, 6]),
   (mkRat (1) 60, [0, 1, 1, 1, 1, 2, 2, 3, 5]),
   (mkRat (-1) 192, [0, 1, 1, 1, 1, 2, 2, 4, 4]),
   (mkRat (1) 1458, [0, 1, 1, 1, 1, 3, 3, 3, 3]),
   (mkRat (2) 81, [0, 1, 1, 1, 1, 3, 9]),
   (mkRat (1) 48, [0, 1, 1, 1, 1, 4, 8]),
   (mkRat (-1) 35, [0, 1, 1, 1, 1, 5, 7]),
   (mkRat (1) 108, [0, 1, 1, 1, 1, 6, 6]),
   (mkRat (1) 160, [0, 1, 1, 1, 2, 2, 2, 2, 5]),
   (mkRat (-1) 108, [0, 1, 1, 1, 2, 2, 2, 3, 4]),
   (mkRat (-1) 486, [0, 1, 1, 1, 2, 2, 3, 3, 3]),
   (mkRat (-1) 54, [0, 1, 1, 1, 2, 2, 9]),
   (mkRat (2) 189, [0, 1, 1, 1, 3, 3, 7]),
   (mkRat (1) 54, [0, 1, 1, 1, 3, 4, 6]),
   (mkRat (-8) 225, [0, 1, 1, 1, 3, 5, 5]),
   (mkRat (-1) 80, [0, 1, 1, 1, 4, 4, 5]),
   (mkRat (2) 39, [0, 1, 1, 1, 13]),
   (mkRat (1) 1728, [0, 1, 2, 2, 2, 2, 2, 2, 3]),
   (mkRat (1) 112, [0, 1, 2, 2, 2, 2, 7]),
   (mkRat (1) 54, [0, 1, 2, 2, 2, 3, 6]),
   (mkRat (-1) 40, [0, 1, 2, 2, 2, 4, 5]),
   (mkRat (-1) 60, [0, 1, 2, 2, 3, 3, 5]),
   (mkRat (1) 96, [0, 1, 2, 2, 3, 4, 4]),
   (mkRat (1) 22, [0, 1, 2, 2, 11])]

def sc740Part2 : RawPoly ℕ :=
  [(mkRat (-1) 3645, [0, 1, 3, 3, 3, 3, 3]),
   (mkRat (-2) 81, [0, 1, 3, 3, 9]),
   (mkRat (-1) 24, [0, 1, 3, 4, 8]),
   (mkRat (2) 35, [0, 1, 3, 5, 7]),
   (mkRat (-1) 54, [0, 1, 3, 6, 6]),
   (mkRat (-1) 56, [0, 1, 4, 4, 7]),
   (mkRat (1) 20, [0, 1, 4, 5, 6]),
   (mkRat (13) 375, [0, 1, 5, 5, 5]),
   (mkRat (-2) 15, [0, 1, 15]),
   (mkRat (1) 46080, [0, 2, 2, 2, 2, 2, 2, 2, 2]),
   (mkRat (1) 360, [0, 2, 2, 2, 2, 2, 6]),
   (mkRat (-1) 80, [0, 2, 2, 2, 2, 3, 5]),
   (mkRat (1) 256, [0, 2, 2, 2, 2, 4, 4]),
   (mkRat (1) 108, [0, 2, 2, 2, 3, 3, 4]),
   (mkRat (1) 30, [0, 2, 2, 2, 10]),
   (mkRat (1) 972, [0, 2, 2, 3, 3, 3, 3]),
   (mkRat (1) 27, [0, 2, 2, 3, 9]),
   (mkRat (1) 32, [0, 2, 2, 4, 8]),
   (mkRat (-3) 70, [0, 2, 2, 5, 7]),
   (mkRat (1) 72, [0, 2, 2, 6, 6]),
   (mkRat (-4) 567, [0, 3, 3, 3, 7]),
   (mkRat (-1) 54, [0, 3, 3, 4, 6]),
   (mkRat (8) 225, [0, 3, 3, 5, 5]),
   (mkRat (1) 40, [0, 3, 4, 4, 5])]

def sc740Part3 : RawPoly ℕ :=
  [(mkRat (-4) 39, [0, 3, 13]),
   (mkRat (-1) 768, [0, 4, 4, 4, 4]),
   (mkRat (-1) 12, [0, 4, 12]),
   (mkRat (6) 55, [0, 5, 11]),
   (mkRat (-1) 15, [0, 6, 10]),
   (mkRat (-4) 63, [0, 7, 9]),
   (mkRat (-1) 32, [0, 8, 8]),
   (mkRat (1) 1496880, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4]),
   (mkRat (-1) 85050, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2]),
   (mkRat (1) 42525, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6]),
   (mkRat (1) 9720, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4]),
   (mkRat (-1) 3360, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4]),
   (mkRat (1) 1680, [1, 1, 1, 1, 1, 1, 1, 1, 8]),
   (mkRat (-1) 1134, [1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3]),
   (mkRat (1) 567, [1, 1, 1, 1, 1, 1, 1, 3, 6]),
   (mkRat (-1) 420, [1, 1, 1, 1, 1, 1, 1, 4, 5]),
   (mkRat (-1) 2700, [1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2]),
   (mkRat (-1) 270, [1, 1, 1, 1, 1, 1, 2, 2, 6]),
   (mkRat (1) 405, [1, 1, 1, 1, 1, 1, 3, 3, 4]),
   (mkRat (2) 225, [1, 1, 1, 1, 1, 1, 10]),
   (mkRat (1) 100, [1, 1, 1, 1, 1, 2, 2, 2, 5]),
   (mkRat (-1) 120, [1, 1, 1, 1, 1, 2, 2, 3, 4]),
   (mkRat (1) 60, [1, 1, 1, 1, 1, 3, 8]),
   (mkRat (1) 70, [1, 1, 1, 1, 1, 4, 7])]

def sc740Part4 : RawPoly ℕ :=
  [(mkRat (-1) 50, [1, 1, 1, 1, 1, 5, 6]),
   (mkRat (-1) 192, [1, 1, 1, 1, 2, 2, 2, 2, 4]),
   (mkRat (-1) 162, [1, 1, 1, 1, 2, 2, 2, 3, 3]),
   (mkRat (-1) 48, [1, 1, 1, 1, 2, 2, 8]),
   (mkRat (1) 81, [1, 1, 1, 1, 3, 3, 6]),
   (mkRat (-1) 30, [1, 1, 1, 1, 3, 4, 5]),
   (mkRat (1) 288, [1, 1, 1, 1, 4, 4, 4]),
   (mkRat (1) 18, [1, 1, 1, 1, 12]),
   (mkRat (-1) 540, [1, 1, 1, 2, 2, 2, 2, 2, 3]),
   (mkRat (-1) 63, [1, 1, 1, 2, 2, 2, 7]),
   (mkRat (-1) 54, [1, 1, 1, 2, 2, 3, 6]),
   (mkRat (1) 40, [1, 1, 1, 2, 2, 4, 5]),
   (mkRat (1) 243, [1, 1, 1, 3, 3, 3, 4]),
   (mkRat (2) 45, [1, 1, 1, 3, 10]),
   (mkRat (1) 27, [1, 1, 1, 4, 9]),
   (mkRat (-1) 20, [1, 1, 1, 5, 8]),
   (mkRat (2) 63, [1, 1, 1, 6, 7]),
   (mkRat (-1) 200, [1, 2, 2, 2, 2, 2, 5]),
   (mkRat (1) 96, [1, 2, 2, 2, 2, 3, 4]),
   (mkRat (1) 243, [1, 2, 2, 2, 3, 3, 3]),
   (mkRat (1) 27, [1, 2, 2, 2, 9]),
   (mkRat (1) 24, [1, 2, 2, 3, 8]),
   (mkRat (1) 28, [1, 2, 2, 4, 7]),
   (mkRat (-1) 20, [1, 2, 2, 5, 6])]

def sc740Part5 : RawPoly ℕ :=
  [(mkRat (-2) 243, [1, 3, 3, 3, 6]),
   (mkRat (1) 30, [1, 3, 3, 4, 5]),
   (mkRat (-1) 144, [1, 3, 4, 4, 4]),
   (mkRat (-1) 9, [1, 3, 12]),
   (mkRat (-1) 11, [1, 4, 11]),
   (mkRat (3) 25, [1, 5, 10]),
   (mkRat (-2) 27, [1, 6, 9]),
   (mkRat (-1) 14, [1, 7, 8]),
   (mkRat (1) 1152, [2, 2, 2, 2, 2, 2, 4]),
   (mkRat (1) 540, [2, 2, 2, 2, 2, 3, 3]),
   (mkRat (1) 64, [2, 2, 2, 2, 8]),
   (mkRat (2) 63, [2, 2, 2, 3, 7]),
   (mkRat (1) 36, [2, 2, 2, 4, 6]),
   (mkRat (-4) 75, [2, 2, 2, 5, 5]),
   (mkRat (1) 54, [2, 2, 3, 3, 6]),
   (mkRat (-1) 20, [2, 2, 3, 4, 5]),
   (mkRat (1) 192, [2, 2, 4, 4, 4]),
   (mkRat (1) 12, [2, 2, 12]),
   (mkRat (-1) 486, [3, 3, 3, 3, 4]),
   (mkRat (-2) 45, [3, 3, 10]),
   (mkRat (-2) 27, [3, 4, 9]),
   (mkRat (1) 10, [3, 5, 8]),
   (mkRat (-4) 63, [3, 6, 7]),
   (mkRat (-1) 32, [4, 4, 8])]

def sc740Part6 : RawPoly ℕ :=
  [(mkRat (3) 35, [4, 5, 7]),
   (mkRat (-1) 36, [4, 6, 6]),
   (mkRat (8) 75, [5, 5, 6]),
   (mkRat (-1) 4, [16])]

def sc740 : RawPoly ℕ :=
  [sc740Part0,
   sc740Part1,
   sc740Part2,
   sc740Part3,
   sc740Part4,
   sc740Part5,
   sc740Part6].flatten

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc740_check :
    reduceTwo (prependC 1 sc363 ++ scaleR (-1) (prependC 0 sc364)) = sc740 := by
  decide +kernel

theorem sc740_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc740 = evRc a c (expWordR [1, 2, 5] (8)) := by
  rw [← sc740_check]
  exact expTwo_step _ _ hc 0 [2, 5] (8)
    sc363 sc364 (sc363_sound a c hc) (sc364_sound a c hc)

def sc741 : RawPoly ℕ :=
  [(mkRat (1) 3, [0, 1, 1, 1, 1]),
   (mkRat (-2) 3, [0, 1, 3]),
   (mkRat (1) 2, [0, 2, 2]),
   (-1, [4])]

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc741_check :
    reduceTwo (prependC 1 sc365 ++ scaleR (-1) (prependC 0 sc366)) = sc741 := by
  decide +kernel

theorem sc741_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc741 = evRc a c (expWordR [1, 2, 6] (-5)) := by
  rw [← sc741_check]
  exact expTwo_step _ _ hc 0 [2, 6] (-5)
    sc365 sc366 (sc365_sound a c hc) (sc366_sound a c hc)

def sc742 : RawPoly ℕ :=
  [(mkRat (-1) 2, [0, 1, 4]),
   (mkRat (1) 5, [1, 1, 1, 1, 1]),
   (mkRat (1) 2, [1, 2, 2]),
   (mkRat (-4) 5, [5])]

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc742_check :
    reduceTwo (prependC 1 sc366 ++ scaleR (-1) (prependC 0 sc367)) = sc742 := by
  decide +kernel

theorem sc742_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc742 = evRc a c (expWordR [1, 2, 6] (-4)) := by
  rw [← sc742_check]
  exact expTwo_step _ _ hc 0 [2, 6] (-4)
    sc366 sc367 (sc366_sound a c hc) (sc367_sound a c hc)

def sc743 : RawPoly ℕ :=
  [(mkRat (2) 45, [0, 1, 1, 1, 1, 1, 1]),
   (mkRat (2) 9, [0, 1, 1, 1, 3]),
   (mkRat (-2) 5, [0, 1, 5]),
   (mkRat (-2) 9, [0, 3, 3]),
   (mkRat (1) 3, [2, 2, 2]),
   (mkRat (4) 3, [6])]

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc743_check :
    reduceTwo (prependC 1 sc367 ++ scaleR (-1) (prependC 0 sc368)) = sc743 := by
  decide +kernel

theorem sc743_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc743 = evRc a c (expWordR [1, 2, 6] (-3)) := by
  rw [← sc743_check]
  exact expTwo_step _ _ hc 0 [2, 6] (-3)
    sc367 sc368 (sc367_sound a c hc) (sc368_sound a c hc)

def sc744 : RawPoly ℕ :=
  [(mkRat (1) 6, [0, 1, 1, 1, 4]),
   (mkRat (1) 6, [0, 1, 2, 2, 2]),
   (mkRat (2) 3, [0, 1, 6]),
   (mkRat (-1) 3, [0, 3, 4]),
   (mkRat (1) 63, [1, 1, 1, 1, 1, 1, 1]),
   (mkRat (2) 9, [1, 1, 1, 1, 3]),
   (mkRat (-1) 6, [1, 1, 1, 2, 2]),
   (mkRat (-2) 9, [1, 3, 3]),
   (mkRat (1) 3, [2, 2, 3]),
   (mkRat (-4) 7, [7])]

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc744_check :
    reduceTwo (prependC 1 sc368 ++ scaleR (-1) (prependC 0 sc369)) = sc744 := by
  decide +kernel

theorem sc744_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc744 = evRc a c (expWordR [1, 2, 6] (-2)) := by
  rw [← sc744_check]
  exact expTwo_step _ _ hc 0 [2, 6] (-2)
    sc368 sc369 (sc368_sound a c hc) (sc369_sound a c hc)

def sc745 : RawPoly ℕ :=
  [(mkRat (1) 420, [0, 1, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (1) 15, [0, 1, 1, 1, 1, 1, 3]),
   (mkRat (-1) 12, [0, 1, 1, 1, 1, 2, 2]),
   (mkRat (2) 15, [0, 1, 1, 1, 5]),
   (mkRat (1) 6, [0, 1, 2, 2, 3]),
   (mkRat (-2) 7, [0, 1, 7]),
   (mkRat (1) 16, [0, 2, 2, 2, 2]),
   (mkRat (-4) 15, [0, 3, 5]),
   (mkRat (-1) 8, [0, 4, 4]),
   (mkRat (1) 6, [1, 1, 1, 1, 4]),
   (mkRat (-1) 3, [1, 3, 4]),
   (mkRat (1) 4, [2, 2, 4]),
   (mkRat (-1) 2, [8])]

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc745_check :
    reduceTwo (prependC 1 sc369 ++ scaleR (-1) (prependC 0 sc370)) = sc745 := by
  decide +kernel

theorem sc745_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc745 = evRc a c (expWordR [1, 2, 6] (-1)) := by
  rw [← sc745_check]
  exact expTwo_step _ _ hc 0 [2, 6] (-1)
    sc369 sc370 (sc369_sound a c hc) (sc370_sound a c hc)

def sc746 : RawPoly ℕ :=
  [(mkRat (1) 20, [0, 1, 1, 1, 1, 1, 4]),
   (mkRat (-1) 18, [0, 1, 1, 1, 2, 2, 2]),
   (mkRat (-2) 9, [0, 1, 1, 1, 6]),
   (mkRat (1) 8, [0, 1, 2, 2, 4]),
   (mkRat (-1) 4, [0, 1, 8]),
   (mkRat (1) 9, [0, 2, 2, 2, 3]),
   (mkRat (4) 9, [0, 3, 6]),
   (mkRat (-1) 5, [0, 4, 5]),
   (mkRat (1) 1620, [1, 1, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (4) 135, [1, 1, 1, 1, 1, 1, 3]),
   (mkRat (-1) 20, [1, 1, 1, 1, 1, 2, 2]),
   (mkRat (2) 15, [1, 1, 1, 1, 5]),
   (mkRat (2) 27, [1, 1, 1, 3, 3]),
   (mkRat (1) 16, [1, 2, 2, 2, 2]),
   (mkRat (-4) 15, [1, 3, 5]),
   (mkRat (-1) 8, [1, 4, 4]),
   (mkRat (1) 5, [2, 2, 5]),
   (mkRat (-4) 81, [3, 3, 3]),
   (mkRat (-4) 9, [9])]

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc746_check :
    reduceTwo (prependC 1 sc370 ++ scaleR (-1) (prependC 0 sc371)) = sc746 := by
  decide +kernel

theorem sc746_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc746 = evRc a c (expWordR [1, 2, 6] (0)) := by
  rw [← sc746_check]
  exact expTwo_step _ _ hc 0 [2, 6] (0)
    sc370 sc371 (sc370_sound a c hc) (sc371_sound a c hc)

def sc747Part0 : RawPoly ℕ :=
  [(mkRat (1) 14175, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (1) 189, [0, 1, 1, 1, 1, 1, 1, 1, 3]),
   (mkRat (-1) 90, [0, 1, 1, 1, 1, 1, 1, 2, 2]),
   (mkRat (1) 25, [0, 1, 1, 1, 1, 1, 5]),
   (mkRat (1) 27, [0, 1, 1, 1, 1, 3, 3]),
   (mkRat (-1) 18, [0, 1, 1, 1, 2, 2, 3]),
   (mkRat (2) 21, [0, 1, 1, 1, 7]),
   (mkRat (1) 10, [0, 1, 2, 2, 5]),
   (mkRat (-2) 81, [0, 1, 3, 3, 3]),
   (mkRat (-2) 9, [0, 1, 9]),
   (mkRat (1) 12, [0, 2, 2, 2, 4]),
   (mkRat (1) 18, [0, 2, 2, 3, 3]),
   (mkRat (-4) 21, [0, 3, 7]),
   (mkRat (1) 3, [0, 4, 6]),
   (mkRat (-2) 25, [0, 5, 5]),
   (mkRat (1) 45, [1, 1, 1, 1, 1, 1, 4]),
   (mkRat (-1) 18, [1, 1, 1, 1, 2, 2, 2]),
   (mkRat (-2) 9, [1, 1, 1, 1, 6]),
   (mkRat (1) 9, [1, 1, 1, 3, 4]),
   (mkRat (1) 9, [1, 2, 2, 2, 3]),
   (mkRat (4) 9, [1, 3, 6]),
   (mkRat (-1) 5, [1, 4, 5]),
   (mkRat (1) 60, [2, 2, 2, 2, 2]),
   (mkRat (-1) 3, [2, 2, 6])]

def sc747Part1 : RawPoly ℕ :=
  [(mkRat (-1) 9, [3, 3, 4]),
   (mkRat (-2) 5, [10])]

def sc747 : RawPoly ℕ :=
  [sc747Part0,
   sc747Part1].flatten

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc747_check :
    reduceTwo (prependC 1 sc371 ++ scaleR (-1) (prependC 0 sc372)) = sc747 := by
  decide +kernel

theorem sc747_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc747 = evRc a c (expWordR [1, 2, 6] (1)) := by
  rw [← sc747_check]
  exact expTwo_step _ _ hc 0 [2, 6] (1)
    sc371 sc372 (sc371_sound a c hc) (sc372_sound a c hc)

def sc748Part0 : RawPoly ℕ :=
  [(mkRat (1) 252, [0, 1, 1, 1, 1, 1, 1, 1, 4]),
   (mkRat (-1) 60, [0, 1, 1, 1, 1, 1, 2, 2, 2]),
   (mkRat (-1) 15, [0, 1, 1, 1, 1, 1, 6]),
   (mkRat (1) 18, [0, 1, 1, 1, 1, 3, 4]),
   (mkRat (-1) 24, [0, 1, 1, 1, 2, 2, 4]),
   (mkRat (1) 12, [0, 1, 1, 1, 8]),
   (mkRat (1) 120, [0, 1, 2, 2, 2, 2, 2]),
   (mkRat (-1) 6, [0, 1, 2, 2, 6]),
   (mkRat (-1) 18, [0, 1, 3, 3, 4]),
   (mkRat (-1) 5, [0, 1, 10]),
   (mkRat (1) 15, [0, 2, 2, 2, 5]),
   (mkRat (1) 12, [0, 2, 2, 3, 4]),
   (mkRat (-1) 6, [0, 3, 8]),
   (mkRat (-1) 7, [0, 4, 7]),
   (mkRat (4) 15, [0, 5, 6]),
   (mkRat (1) 69300, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (1) 630, [1, 1, 1, 1, 1, 1, 1, 1, 3]),
   (mkRat (-1) 252, [1, 1, 1, 1, 1, 1, 1, 2, 2]),
   (mkRat (4) 225, [1, 1, 1, 1, 1, 1, 5]),
   (mkRat (1) 45, [1, 1, 1, 1, 1, 3, 3]),
   (mkRat (-1) 18, [1, 1, 1, 1, 2, 2, 3]),
   (mkRat (2) 21, [1, 1, 1, 1, 7]),
   (mkRat (-1) 48, [1, 1, 1, 2, 2, 2, 2]),
   (mkRat (4) 45, [1, 1, 1, 3, 5])]

def sc748Part1 : RawPoly ℕ :=
  [(mkRat (1) 24, [1, 1, 1, 4, 4]),
   (mkRat (1) 12, [1, 2, 2, 2, 4]),
   (mkRat (1) 18, [1, 2, 2, 3, 3]),
   (mkRat (-4) 21, [1, 3, 7]),
   (mkRat (1) 3, [1, 4, 6]),
   (mkRat (-2) 25, [1, 5, 5]),
   (mkRat (1) 24, [2, 2, 2, 2, 3]),
   (mkRat (1) 7, [2, 2, 7]),
   (mkRat (-4) 45, [3, 3, 5]),
   (mkRat (-1) 12, [3, 4, 4]),
   (mkRat (-4) 11, [11])]

def sc748 : RawPoly ℕ :=
  [sc748Part0,
   sc748Part1].flatten

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc748_check :
    reduceTwo (prependC 1 sc372 ++ scaleR (-1) (prependC 0 sc373)) = sc748 := by
  decide +kernel

theorem sc748_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc748 = evRc a c (expWordR [1, 2, 6] (2)) := by
  rw [← sc748_check]
  exact expTwo_step _ _ hc 0 [2, 6] (2)
    sc372 sc373 (sc372_sound a c hc) (sc373_sound a c hc)

def sc749Part0 : RawPoly ℕ :=
  [(mkRat (1) 748440, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (1) 4860, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3]),
   (mkRat (-1) 1680, [0, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2]),
   (mkRat (1) 315, [0, 1, 1, 1, 1, 1, 1, 1, 5]),
   (mkRat (2) 405, [0, 1, 1, 1, 1, 1, 1, 3, 3]),
   (mkRat (-1) 60, [0, 1, 1, 1, 1, 1, 2, 2, 3]),
   (mkRat (1) 35, [0, 1, 1, 1, 1, 1, 7]),
   (mkRat (-1) 96, [0, 1, 1, 1, 1, 2, 2, 2, 2]),
   (mkRat (2) 45, [0, 1, 1, 1, 1, 3, 5]),
   (mkRat (1) 48, [0, 1, 1, 1, 1, 4, 4]),
   (mkRat (-1) 30, [0, 1, 1, 1, 2, 2, 5]),
   (mkRat (2) 243, [0, 1, 1, 1, 3, 3, 3]),
   (mkRat (2) 27, [0, 1, 1, 1, 9]),
   (mkRat (1) 48, [0, 1, 2, 2, 2, 2, 3]),
   (mkRat (1) 14, [0, 1, 2, 2, 7]),
   (mkRat (-2) 45, [0, 1, 3, 3, 5]),
   (mkRat (-1) 24, [0, 1, 3, 4, 4]),
   (mkRat (-2) 11, [0, 1, 11]),
   (mkRat (1) 576, [0, 2, 2, 2, 2, 2, 2]),
   (mkRat (-1) 9, [0, 2, 2, 2, 6]),
   (mkRat (1) 15, [0, 2, 2, 3, 5]),
   (mkRat (1) 32, [0, 2, 2, 4, 4]),
   (mkRat (-1) 243, [0, 3, 3, 3, 3]),
   (mkRat (-4) 27, [0, 3, 9])]

def sc749Part1 : RawPoly ℕ :=
  [(mkRat (-1) 8, [0, 4, 8]),
   (mkRat (-4) 35, [0, 5, 7]),
   (mkRat (5) 18, [0, 6, 6]),
   (mkRat (1) 840, [1, 1, 1, 1, 1, 1, 1, 1, 4]),
   (mkRat (-1) 135, [1, 1, 1, 1, 1, 1, 2, 2, 2]),
   (mkRat (-4) 135, [1, 1, 1, 1, 1, 1, 6]),
   (mkRat (1) 30, [1, 1, 1, 1, 1, 3, 4]),
   (mkRat (-1) 24, [1, 1, 1, 1, 2, 2, 4]),
   (mkRat (1) 12, [1, 1, 1, 1, 8]),
   (mkRat (-1) 27, [1, 1, 1, 2, 2, 2, 3]),
   (mkRat (-4) 27, [1, 1, 1, 3, 6]),
   (mkRat (1) 15, [1, 1, 1, 4, 5]),
   (mkRat (1) 15, [1, 2, 2, 2, 5]),
   (mkRat (1) 12, [1, 2, 2, 3, 4]),
   (mkRat (-1) 6, [1, 3, 8]),
   (mkRat (-1) 7, [1, 4, 7]),
   (mkRat (4) 15, [1, 5, 6]),
   (mkRat (1) 32, [2, 2, 2, 2, 4]),
   (mkRat (1) 27, [2, 2, 2, 3, 3]),
   (mkRat (1) 8, [2, 2, 8]),
   (mkRat (4) 27, [3, 3, 6]),
   (mkRat (-2) 15, [3, 4, 5]),
   (mkRat (-1) 48, [4, 4, 4]),
   (mkRat (-1) 3, [12])]

def sc749 : RawPoly ℕ :=
  [sc749Part0,
   sc749Part1].flatten

set_option maxHeartbeats 2000000 in
-- Exact normalization of at most 231 oscillator monomials.
set_option maxRecDepth 4096 in
theorem sc749_check :
    reduceTwo (prependC 1 sc373 ++ scaleR (-1) (prependC 0 sc374)) = sc749 := by
  decide +kernel

theorem sc749_sound {r : ℕ} (a : Fin r) (c : ℂ)
    (hc : c * c = ((2 : ℚ) : ℂ)) :
    evRc a c sc749 = evRc a c (expWordR [1, 2, 6] (3)) := by
  rw [← sc749_check]
  exact expTwo_step _ _ hc 0 [2, 6] (3)
    sc373 sc374 (sc373_sound a c hc) (sc374_sound a c hc)

end VOA.Classification.COne.OrbOctaRC
