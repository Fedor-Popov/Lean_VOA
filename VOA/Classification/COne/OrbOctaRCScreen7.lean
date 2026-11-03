import VOA.Classification.COne.OrbOctaRCScreenBlocks
import VOA.Classification.COne.OrbOctaRCScreenCache28
import VOA.Classification.COne.OrbOctaRCScreen6

/-! One exact screening step, checked in blocks of eight source monomials. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
namespace VOA.Classification.COne.OrbOctaRC
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational HeisenbergN
  PlusC2Eval PlusUnitary PlusC2 OrbC2e OrbC2g OrbC2h LatMod OrbRat6 OrbPrim

def screenState7 : RawPoly ℕ :=
  [(8, [0, 1, 1, 1, 1, 1, 1, 1]),
   (280, [0, 1, 1, 1, 1, 3]),
   (420, [0, 1, 1, 1, 2, 2]),
   (1008, [0, 1, 1, 5]),
   (1260, [0, 1, 2, 4]),
   (560, [0, 1, 3, 3]),
   (420, [0, 2, 2, 3]),
   (720, [0, 7]),
   (168, [1, 1, 1, 1, 1, 2]),
   (840, [1, 1, 1, 4]),
   (1680, [1, 1, 2, 3]),
   (420, [1, 2, 2, 2]),
   (1680, [1, 6]),
   (1008, [2, 5]),
   (840, [3, 4])]

def screen7Input0 : RawPoly ℕ :=
  [(mkRat (-16) 105, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2]),
   (mkRat (4) 7, [0, 1, 1, 1, 1, 1, 1, 1, 1, 4]),
   (mkRat (-16) 7, [0, 1, 1, 1, 1, 1, 1, 1, 2, 3]),
   (mkRat (-8) 3, [0, 1, 1, 1, 1, 1, 1, 2, 2, 2]),
   (mkRat (16) 3, [0, 1, 1, 1, 1, 1, 1, 6]),
   (mkRat (48) 5, [0, 1, 1, 1, 1, 1, 2, 5]),
   (-16, [0, 1, 1, 1, 1, 1, 3, 4]),
   (mkRat (-40) 3, [0, 1, 1, 1, 2, 2, 2, 3])]

def screen7Row0 : RawPoly ℕ :=
  [(mkRat (143872) 33075, [0, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (36352) 945, [0, 1, 1, 1, 1, 3]),
   (mkRat (9344) 315, [0, 1, 1, 1, 2, 2]),
   (mkRat (4608) 175, [0, 1, 1, 5]),
   (mkRat (-4096) 945, [0, 1, 3, 3]),
   (mkRat (-256) 315, [0, 2, 2, 3]),
   (mkRat (1024) 735, [0, 7]),
   (mkRat (18688) 315, [1, 1, 1, 4]),
   (mkRat (-2048) 315, [1, 2, 2, 2]),
   (mkRat (4096) 315, [1, 6]),
   (mkRat (-512) 315, [3, 4])]

set_option maxHeartbeats 3000000 in
-- Exact scalar substitution in one cached exponential descendant.
set_option maxRecDepth 8192 in
theorem screen7Row0_check :
    screenTerm (mkRat (-16) 105, [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2]) sc4240 = screen7Row0 := by
  decide +kernel

theorem screen7Row0_sound :
    fo (sector (-2) (evRc (a0 1) (cα 1) [(mkRat (-16) 105,
      [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2])])) =
      sector (-2 - 1) (evRc (a0 1) (cα 1) screen7Row0) := by
  rw [← screen7Row0_check]
  exact screenTerm_sound _ _ _ (fun c hc => sc4240_sound (a0 1) c hc)

def screen7Row1 : RawPoly ℕ :=
  [(mkRat (1024) 735, [0, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (-128) 21, [0, 1, 1, 1, 1, 3]),
   (mkRat (352) 21, [0, 1, 1, 1, 2, 2]),
   (mkRat (-128) 5, [0, 1, 1, 5]),
   (mkRat (-96) 7, [0, 1, 2, 4]),
   (mkRat (128) 21, [0, 1, 3, 3]),
   (mkRat (-32) 21, [0, 2, 2, 3]),
   (mkRat (-128) 49, [0, 7]),
   (mkRat (1024) 105, [1, 1, 1, 1, 1, 2]),
   (mkRat (704) 21, [1, 1, 1, 4]),
   (mkRat (128) 3, [1, 1, 2, 3]),
   (mkRat (-32) 7, [1, 2, 2, 2]),
   (mkRat (-128) 7, [1, 6]),
   (mkRat (128) 35, [2, 5]),
   (mkRat (-64) 21, [3, 4])]

set_option maxHeartbeats 3000000 in
-- Exact scalar substitution in one cached exponential descendant.
set_option maxRecDepth 8192 in
theorem screen7Row1_check :
    screenTerm (mkRat (4) 7, [0, 1, 1, 1, 1, 1, 1, 1, 1, 4]) sc3972 = screen7Row1 := by
  decide +kernel

theorem screen7Row1_sound :
    fo (sector (-2) (evRc (a0 1) (cα 1) [(mkRat (4) 7, [0, 1, 1, 1, 1, 1, 1, 1, 1, 4])])) =
      sector (-2 - 1) (evRc (a0 1) (cα 1) screen7Row1) := by
  rw [← screen7Row1_check]
  exact screenTerm_sound _ _ _ (fun c hc => sc3972_sound (a0 1) c hc)

def screen7Row2 : RawPoly ℕ :=
  [(mkRat (-6688) 2205, [0, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (320) 63, [0, 1, 1, 1, 1, 3]),
   (mkRat (544) 21, [0, 1, 1, 1, 2, 2]),
   (mkRat (2304) 35, [0, 1, 1, 5]),
   (mkRat (2560) 63, [0, 1, 3, 3]),
   (mkRat (64) 21, [0, 2, 2, 3]),
   (mkRat (512) 49, [0, 7]),
   (mkRat (1088) 21, [1, 1, 1, 4]),
   (mkRat (-640) 21, [1, 2, 2, 2]),
   (mkRat (1280) 21, [1, 6]),
   (mkRat (128) 21, [3, 4])]

set_option maxHeartbeats 3000000 in
-- Exact scalar substitution in one cached exponential descendant.
set_option maxRecDepth 8192 in
theorem screen7Row2_check :
    screenTerm (mkRat (-16) 7, [0, 1, 1, 1, 1, 1, 1, 1, 2, 3]) sc4007 = screen7Row2 := by
  decide +kernel

theorem screen7Row2_sound :
    fo (sector (-2) (evRc (a0 1) (cα 1) [(mkRat (-16) 7, [0, 1, 1, 1, 1, 1, 1, 1, 2, 3])])) =
      sector (-2 - 1) (evRc (a0 1) (cα 1) screen7Row2) := by
  rw [← screen7Row2_check]
  exact screenTerm_sound _ _ _ (fun c hc => sc4007_sound (a0 1) c hc)

def screen7Row3 : RawPoly ℕ :=
  [(mkRat (160) 189, [0, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (-448) 27, [0, 1, 1, 1, 1, 3]),
   (mkRat (-32) 9, [0, 1, 1, 1, 2, 2]),
   (mkRat (128) 3, [0, 1, 1, 5]),
   (mkRat (256) 3, [0, 1, 2, 4]),
   (mkRat (-512) 27, [0, 1, 3, 3]),
   (mkRat (64) 9, [0, 2, 2, 3]),
   (mkRat (256) 21, [0, 7]),
   (mkRat (256) 45, [1, 1, 1, 1, 1, 2]),
   (mkRat (64) 9, [1, 1, 1, 4]),
   (mkRat (1280) 9, [1, 1, 2, 3]),
   (mkRat (512) 9, [1, 2, 2, 2]),
   (mkRat (512) 9, [1, 6]),
   (mkRat (512) 15, [2, 5]),
   (mkRat (-128) 9, [3, 4])]

set_option maxHeartbeats 3000000 in
-- Exact scalar substitution in one cached exponential descendant.
set_option maxRecDepth 8192 in
theorem screen7Row3_check :
    screenTerm (mkRat (-8) 3, [0, 1, 1, 1, 1, 1, 1, 2, 2, 2]) sc4048 = screen7Row3 := by
  decide +kernel

theorem screen7Row3_sound :
    fo (sector (-2) (evRc (a0 1) (cα 1) [(mkRat (-8) 3, [0, 1, 1, 1, 1, 1, 1, 2, 2, 2])])) =
      sector (-2 - 1) (evRc (a0 1) (cα 1) screen7Row3) := by
  rw [← screen7Row3_check]
  exact screenTerm_sound _ _ _ (fun c hc => sc4048_sound (a0 1) c hc)

def screen7Row4 : RawPoly ℕ :=
  [(mkRat (-160) 189, [0, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (448) 27, [0, 1, 1, 1, 1, 3]),
   (mkRat (32) 9, [0, 1, 1, 1, 2, 2]),
   (mkRat (-128) 3, [0, 1, 1, 5]),
   (mkRat (128) 3, [0, 1, 2, 4]),
   (mkRat (512) 27, [0, 1, 3, 3]),
   (mkRat (-64) 9, [0, 2, 2, 3]),
   (mkRat (-256) 21, [0, 7]),
   (mkRat (128) 45, [1, 1, 1, 1, 1, 2]),
   (mkRat (-64) 9, [1, 1, 1, 4]),
   (mkRat (640) 9, [1, 1, 2, 3]),
   (mkRat (-128) 9, [1, 2, 2, 2]),
   (mkRat (1024) 9, [1, 6]),
   (mkRat (256) 15, [2, 5]),
   (mkRat (128) 9, [3, 4])]

set_option maxHeartbeats 3000000 in
-- Exact scalar substitution in one cached exponential descendant.
set_option maxRecDepth 8192 in
theorem screen7Row4_check :
    screenTerm (mkRat (16) 3, [0, 1, 1, 1, 1, 1, 1, 6]) sc3329 = screen7Row4 := by
  decide +kernel

theorem screen7Row4_sound :
    fo (sector (-2) (evRc (a0 1) (cα 1) [(mkRat (16) 3, [0, 1, 1, 1, 1, 1, 1, 6])])) =
      sector (-2 - 1) (evRc (a0 1) (cα 1) screen7Row4) := by
  rw [← screen7Row4_check]
  exact screenTerm_sound _ _ _ (fun c hc => sc3329_sound (a0 1) c hc)

def screen7Row5 : RawPoly ℕ :=
  [(mkRat (-416) 175, [0, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (64) 5, [0, 1, 1, 1, 1, 3]),
   (mkRat (64) 5, [0, 1, 1, 1, 2, 2]),
   (mkRat (1152) 25, [0, 1, 1, 5]),
   (mkRat (128) 5, [0, 1, 3, 3]),
   (mkRat (64) 5, [0, 2, 2, 3]),
   (mkRat (-768) 35, [0, 7]),
   (mkRat (128) 5, [1, 1, 1, 4]),
   (mkRat (192) 5, [1, 2, 2, 2]),
   (mkRat (-384) 5, [1, 6]),
   (mkRat (128) 5, [3, 4])]

set_option maxHeartbeats 3000000 in
-- Exact scalar substitution in one cached exponential descendant.
set_option maxRecDepth 8192 in
theorem screen7Row5_check :
    screenTerm (mkRat (48) 5, [0, 1, 1, 1, 1, 1, 2, 5]) sc3379 = screen7Row5 := by
  decide +kernel

theorem screen7Row5_sound :
    fo (sector (-2) (evRc (a0 1) (cα 1) [(mkRat (48) 5, [0, 1, 1, 1, 1, 1, 2, 5])])) =
      sector (-2 - 1) (evRc (a0 1) (cα 1) screen7Row5) := by
  rw [← screen7Row5_check]
  exact screenTerm_sound _ _ _ (fun c hc => sc3379_sound (a0 1) c hc)

def screen7Row6 : RawPoly ℕ :=
  [(mkRat (416) 105, [0, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (32) 3, [0, 1, 1, 1, 1, 3]),
   (mkRat (64) 3, [0, 1, 1, 1, 2, 2]),
   (mkRat (256) 5, [0, 1, 1, 5]),
   (96, [0, 1, 2, 4]),
   (mkRat (256) 3, [0, 1, 3, 3]),
   (mkRat (-32) 3, [0, 2, 2, 3]),
   (mkRat (256) 7, [0, 7]),
   (mkRat (352) 15, [1, 1, 1, 1, 1, 2]),
   (mkRat (128) 3, [1, 1, 1, 4]),
   (mkRat (128) 3, [1, 1, 2, 3]),
   (32, [1, 2, 2, 2]),
   (128, [1, 6]),
   (mkRat (-256) 5, [2, 5]),
   (mkRat (-64) 3, [3, 4])]

set_option maxHeartbeats 3000000 in
-- Exact scalar substitution in one cached exponential descendant.
set_option maxRecDepth 8192 in
theorem screen7Row6_check :
    screenTerm (-16, [0, 1, 1, 1, 1, 1, 3, 4]) sc3407 = screen7Row6 := by
  decide +kernel

theorem screen7Row6_sound :
    fo (sector (-2) (evRc (a0 1) (cα 1) [(-16, [0, 1, 1, 1, 1, 1, 3, 4])])) =
      sector (-2 - 1) (evRc (a0 1) (cα 1) screen7Row6) := by
  rw [← screen7Row6_check]
  exact screenTerm_sound _ _ _ (fun c hc => sc3407_sound (a0 1) c hc)

def screen7Row7 : RawPoly ℕ :=
  [(mkRat (-272) 189, [0, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (-160) 27, [0, 1, 1, 1, 1, 3]),
   (mkRat (40) 9, [0, 1, 1, 1, 2, 2]),
   (mkRat (-64) 3, [0, 1, 1, 5]),
   (mkRat (160) 3, [0, 1, 2, 4]),
   (mkRat (640) 27, [0, 1, 3, 3]),
   (mkRat (-80) 9, [0, 2, 2, 3]),
   (mkRat (640) 21, [0, 7]),
   (mkRat (128) 9, [1, 1, 1, 1, 1, 2]),
   (mkRat (-80) 9, [1, 1, 1, 4]),
   (mkRat (320) 9, [1, 1, 2, 3]),
   (mkRat (320) 9, [1, 2, 2, 2]),
   (mkRat (320) 9, [1, 6]),
   (mkRat (256) 3, [2, 5]),
   (mkRat (160) 9, [3, 4])]

set_option maxHeartbeats 3000000 in
-- Exact scalar substitution in one cached exponential descendant.
set_option maxRecDepth 8192 in
theorem screen7Row7_check :
    screenTerm (mkRat (-40) 3, [0, 1, 1, 1, 2, 2, 2, 3]) sc3553 = screen7Row7 := by
  decide +kernel

theorem screen7Row7_sound :
    fo (sector (-2) (evRc (a0 1) (cα 1) [(mkRat (-40) 3, [0, 1, 1, 1, 2, 2, 2, 3])])) =
      sector (-2 - 1) (evRc (a0 1) (cα 1) screen7Row7) := by
  rw [← screen7Row7_check]
  exact screenTerm_sound _ _ _ (fun c hc => sc3553_sound (a0 1) c hc)

def screen7Rows0 : List (RawPoly ℕ) :=
  [screen7Row0,
   screen7Row1,
   screen7Row2,
   screen7Row3,
   screen7Row4,
   screen7Row5,
   screen7Row6,
   screen7Row7]

def screen7Result0 : RawPoly ℕ :=
  [(mkRat (94448) 33075, [0, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (7424) 135, [0, 1, 1, 1, 1, 3]),
   (mkRat (34936) 315, [0, 1, 1, 1, 2, 2]),
   (mkRat (10688) 75, [0, 1, 1, 5]),
   (mkRat (5536) 21, [0, 1, 2, 4]),
   (mkRat (167296) 945, [0, 1, 3, 3]),
   (mkRat (-272) 45, [0, 2, 2, 3]),
   (mkRat (13312) 245, [0, 7]),
   (mkRat (17632) 315, [1, 1, 1, 1, 1, 2]),
   (mkRat (21424) 105, [1, 1, 1, 4]),
   (mkRat (3008) 9, [1, 1, 2, 3]),
   (mkRat (33728) 315, [1, 2, 2, 2]),
   (mkRat (98624) 315, [1, 6]),
   (mkRat (9344) 105, [2, 5]),
   (mkRat (352) 15, [3, 4])]

set_option maxHeartbeats 3000000 in
-- Merge eight certified screening rows.
set_option maxRecDepth 8192 in
theorem screen7Result0_check : reduceTwo screen7Rows0.flatten = screen7Result0 := by
  decide +kernel

theorem screen7Result0_sound :
    fo (sector (-2) (evRc (a0 1) (cα 1) screen7Input0)) =
      sector (-2 - 1) (evRc (a0 1) (cα 1) screen7Result0) := by
  apply screenRows_reduce _ _ screen7Rows0 _ _ screen7Result0_check
  exact .cons screen7Row0_sound <|
      .cons screen7Row1_sound <|
      .cons screen7Row2_sound <|
      .cons screen7Row3_sound <|
      .cons screen7Row4_sound <|
      .cons screen7Row5_sound <|
      .cons screen7Row6_sound <|
      .cons screen7Row7_sound .nil

def screen7Input1 : RawPoly ℕ :=
  [(mkRat (240) 7, [0, 1, 1, 1, 2, 7]),
   (mkRat (80) 3, [0, 1, 1, 1, 3, 6]),
   (-48, [0, 1, 1, 1, 4, 5]),
   (-48, [0, 1, 1, 2, 3, 5]),
   (40, [0, 1, 1, 3, 3, 4]),
   (24, [0, 1, 2, 2, 2, 5]),
   (mkRat (-80) 3, [0, 1, 2, 3, 3, 3]),
   (mkRat (360) 7, [0, 1, 4, 7])]

def screen7Row8 : RawPoly ℕ :=
  [(mkRat (272) 147, [0, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (-320) 21, [0, 1, 1, 1, 1, 3]),
   (mkRat (40) 7, [0, 1, 1, 1, 2, 2]),
   (mkRat (192) 7, [0, 1, 1, 5]),
   (mkRat (320) 21, [0, 1, 3, 3]),
   (mkRat (160) 7, [0, 2, 2, 3]),
   (mkRat (4800) 49, [0, 7]),
   (mkRat (80) 7, [1, 1, 1, 4]),
   (mkRat (160) 7, [1, 2, 2, 2]),
   (mkRat (-320) 7, [1, 6]),
   (mkRat (320) 7, [3, 4])]

set_option maxHeartbeats 3000000 in
-- Exact scalar substitution in one cached exponential descendant.
set_option maxRecDepth 8192 in
theorem screen7Row8_check :
    screenTerm (mkRat (240) 7, [0, 1, 1, 1, 2, 7]) sc2182 = screen7Row8 := by
  decide +kernel

theorem screen7Row8_sound :
    fo (sector (-2) (evRc (a0 1) (cα 1) [(mkRat (240) 7, [0, 1, 1, 1, 2, 7])])) =
      sector (-2 - 1) (evRc (a0 1) (cα 1) screen7Row8) := by
  rw [← screen7Row8_check]
  exact screenTerm_sound _ _ _ (fun c hc => sc2182_sound (a0 1) c hc)

def screen7Row9 : RawPoly ℕ :=
  [(mkRat (272) 189, [0, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (160) 27, [0, 1, 1, 1, 1, 3]),
   (mkRat (-40) 9, [0, 1, 1, 1, 2, 2]),
   (mkRat (64) 3, [0, 1, 1, 5]),
   (mkRat (80) 3, [0, 1, 2, 4]),
   (mkRat (-640) 27, [0, 1, 3, 3]),
   (mkRat (80) 9, [0, 2, 2, 3]),
   (mkRat (-640) 21, [0, 7]),
   (mkRat (64) 9, [1, 1, 1, 1, 1, 2]),
   (mkRat (80) 9, [1, 1, 1, 4]),
   (mkRat (160) 9, [1, 1, 2, 3]),
   (mkRat (-80) 9, [1, 2, 2, 2]),
   (mkRat (640) 9, [1, 6]),
   (mkRat (128) 3, [2, 5]),
   (mkRat (-160) 9, [3, 4])]

set_option maxHeartbeats 3000000 in
-- Exact scalar substitution in one cached exponential descendant.
set_option maxRecDepth 8192 in
theorem screen7Row9_check :
    screenTerm (mkRat (80) 3, [0, 1, 1, 1, 3, 6]) sc2227 = screen7Row9 := by
  decide +kernel

theorem screen7Row9_sound :
    fo (sector (-2) (evRc (a0 1) (cα 1) [(mkRat (80) 3, [0, 1, 1, 1, 3, 6])])) =
      sector (-2 - 1) (evRc (a0 1) (cα 1) screen7Row9) := by
  rw [← screen7Row9_check]
  exact screenTerm_sound _ _ _ (fun c hc => sc2227_sound (a0 1) c hc)

def screen7Row10 : RawPoly ℕ :=
  [(mkRat (-272) 105, [0, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (64) 3, [0, 1, 1, 1, 1, 3]),
   (8, [0, 1, 1, 1, 2, 2]),
   (mkRat (288) 5, [0, 1, 1, 5]),
   (48, [0, 1, 2, 4]),
   (mkRat (-64) 3, [0, 1, 3, 3]),
   (32, [0, 2, 2, 3]),
   (mkRat (384) 7, [0, 7]),
   (mkRat (-64) 5, [1, 1, 1, 1, 1, 2]),
   (16, [1, 1, 1, 4]),
   (64, [1, 1, 2, 3]),
   (16, [1, 2, 2, 2]),
   (64, [1, 6]),
   (mkRat (576) 5, [2, 5]),
   (64, [3, 4])]

set_option maxHeartbeats 3000000 in
-- Exact scalar substitution in one cached exponential descendant.
set_option maxRecDepth 8192 in
theorem screen7Row10_check :
    screenTerm (-48, [0, 1, 1, 1, 4, 5]) sc2254 = screen7Row10 := by
  decide +kernel

theorem screen7Row10_sound :
    fo (sector (-2) (evRc (a0 1) (cα 1) [(-48, [0, 1, 1, 1, 4, 5])])) =
      sector (-2 - 1) (evRc (a0 1) (cα 1) screen7Row10) := by
  rw [← screen7Row10_check]
  exact screenTerm_sound _ _ _ (fun c hc => sc2254_sound (a0 1) c hc)

def screen7Row11 : RawPoly ℕ :=
  [(mkRat (96) 35, [0, 1, 1, 1, 1, 1, 1, 1]),
   (16, [0, 1, 1, 1, 2, 2]),
   (mkRat (288) 5, [0, 1, 1, 5]),
   (16, [0, 2, 2, 3]),
   (mkRat (384) 7, [0, 7]),
   (32, [1, 1, 1, 4]),
   (32, [3, 4])]

set_option maxHeartbeats 3000000 in
-- Exact scalar substitution in one cached exponential descendant.
set_option maxRecDepth 8192 in
theorem screen7Row11_check :
    screenTerm (-48, [0, 1, 1, 2, 3, 5]) sc2373 = screen7Row11 := by
  decide +kernel

theorem screen7Row11_sound :
    fo (sector (-2) (evRc (a0 1) (cα 1) [(-48, [0, 1, 1, 2, 3, 5])])) =
      sector (-2 - 1) (evRc (a0 1) (cα 1) screen7Row11) := by
  rw [← screen7Row11_check]
  exact screenTerm_sound _ _ _ (fun c hc => sc2373_sound (a0 1) c hc)

def screen7Row12 : RawPoly ℕ :=
  [(mkRat (-16) 7, [0, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (40) 3, [0, 1, 1, 1, 2, 2]),
   (32, [0, 1, 1, 5]),
   (mkRat (160) 3, [0, 2, 2, 3]),
   (mkRat (-320) 7, [0, 7]),
   (mkRat (32) 3, [1, 1, 1, 1, 1, 2]),
   (mkRat (80) 3, [1, 1, 1, 4]),
   (mkRat (320) 3, [1, 1, 2, 3]),
   (64, [2, 5]),
   (mkRat (320) 3, [3, 4])]

set_option maxHeartbeats 3000000 in
-- Exact scalar substitution in one cached exponential descendant.
set_option maxRecDepth 8192 in
theorem screen7Row12_check :
    screenTerm (40, [0, 1, 1, 3, 3, 4]) sc2424 = screen7Row12 := by
  decide +kernel

theorem screen7Row12_sound :
    fo (sector (-2) (evRc (a0 1) (cα 1) [(40, [0, 1, 1, 3, 3, 4])])) =
      sector (-2 - 1) (evRc (a0 1) (cα 1) screen7Row12) := by
  rw [← screen7Row12_check]
  exact screenTerm_sound _ _ _ (fun c hc => sc2424_sound (a0 1) c hc)

def screen7Row13 : RawPoly ℕ :=
  [(mkRat (16) 21, [0, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (32) 3, [0, 1, 1, 1, 1, 3]),
   (8, [0, 1, 1, 1, 2, 2]),
   (48, [0, 1, 2, 4]),
   (mkRat (-32) 3, [0, 1, 3, 3]),
   (-16, [0, 2, 2, 3]),
   (mkRat (-192) 7, [0, 7]),
   (mkRat (96) 5, [1, 1, 1, 1, 1, 2]),
   (-16, [1, 1, 1, 4]),
   (32, [1, 2, 2, 2]),
   (32, [1, 6]),
   (mkRat (576) 5, [2, 5]),
   (32, [3, 4])]

set_option maxHeartbeats 3000000 in
-- Exact scalar substitution in one cached exponential descendant.
set_option maxRecDepth 8192 in
theorem screen7Row13_check :
    screenTerm (24, [0, 1, 2, 2, 2, 5]) sc2496 = screen7Row13 := by
  decide +kernel

theorem screen7Row13_sound :
    fo (sector (-2) (evRc (a0 1) (cα 1) [(24, [0, 1, 2, 2, 2, 5])])) =
      sector (-2 - 1) (evRc (a0 1) (cα 1) screen7Row13) := by
  rw [← screen7Row13_check]
  exact screenTerm_sound _ _ _ (fun c hc => sc2496_sound (a0 1) c hc)

def screen7Row14 : RawPoly ℕ :=
  [(mkRat (-160) 189, [0, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (1120) 27, [0, 1, 1, 1, 1, 3]),
   (mkRat (80) 9, [0, 1, 1, 1, 2, 2]),
   (mkRat (1760) 27, [0, 1, 3, 3]),
   (mkRat (560) 9, [0, 2, 2, 3]),
   (mkRat (640) 21, [0, 7]),
   (mkRat (160) 9, [1, 1, 1, 4]),
   (mkRat (160) 9, [1, 2, 2, 2]),
   (mkRat (-320) 9, [1, 6]),
   (mkRat (1120) 9, [3, 4])]

set_option maxHeartbeats 3000000 in
-- Exact scalar substitution in one cached exponential descendant.
set_option maxRecDepth 8192 in
theorem screen7Row14_check :
    screenTerm (mkRat (-80) 3, [0, 1, 2, 3, 3, 3]) sc2563 = screen7Row14 := by
  decide +kernel

theorem screen7Row14_sound :
    fo (sector (-2) (evRc (a0 1) (cα 1) [(mkRat (-80) 3, [0, 1, 2, 3, 3, 3])])) =
      sector (-2 - 1) (evRc (a0 1) (cα 1) screen7Row14) := by
  rw [← screen7Row14_check]
  exact screenTerm_sound _ _ _ (fun c hc => sc2563_sound (a0 1) c hc)

def screen7Row15 : RawPoly ℕ :=
  [(mkRat (40) 49, [0, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (80) 7, [0, 1, 1, 1, 1, 3]),
   (mkRat (60) 7, [0, 1, 1, 1, 2, 2]),
   (mkRat (180) 7, [0, 1, 2, 4]),
   (mkRat (-80) 7, [0, 1, 3, 3]),
   (mkRat (-120) 7, [0, 2, 2, 3]),
   (mkRat (3600) 49, [0, 7]),
   (mkRat (-72) 7, [1, 1, 1, 1, 1, 2]),
   (mkRat (120) 7, [1, 1, 1, 4]),
   (mkRat (60) 7, [1, 2, 2, 2]),
   (mkRat (240) 7, [1, 6]),
   (mkRat (288) 7, [2, 5]),
   (mkRat (-240) 7, [3, 4])]

set_option maxHeartbeats 3000000 in
-- Exact scalar substitution in one cached exponential descendant.
set_option maxRecDepth 8192 in
theorem screen7Row15_check :
    screenTerm (mkRat (360) 7, [0, 1, 4, 7]) sc865 = screen7Row15 := by
  decide +kernel

theorem screen7Row15_sound :
    fo (sector (-2) (evRc (a0 1) (cα 1) [(mkRat (360) 7, [0, 1, 4, 7])])) =
      sector (-2 - 1) (evRc (a0 1) (cα 1) screen7Row15) := by
  rw [← screen7Row15_check]
  exact screenTerm_sound _ _ _ (fun c hc => sc865_sound (a0 1) c hc)

def screen7Rows1 : List (RawPoly ℕ) :=
  [screen7Row8,
   screen7Row9,
   screen7Row10,
   screen7Row11,
   screen7Row12,
   screen7Row13,
   screen7Row14,
   screen7Row15]

def screen7Result1 : RawPoly ℕ :=
  [(mkRat (1784) 945, [0, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (14288) 189, [0, 1, 1, 1, 1, 3]),
   (mkRat (4036) 63, [0, 1, 1, 1, 2, 2]),
   (mkRat (20576) 105, [0, 1, 1, 5]),
   (mkRat (3116) 21, [0, 1, 2, 4]),
   (mkRat (2512) 189, [0, 1, 3, 3]),
   (mkRat (10216) 63, [0, 2, 2, 3]),
   (208, [0, 7]),
   (mkRat (4376) 315, [1, 1, 1, 1, 1, 2]),
   (mkRat (2392) 21, [1, 1, 1, 4]),
   (mkRat (1696) 9, [1, 1, 2, 3]),
   (mkRat (5564) 63, [1, 2, 2, 2]),
   (mkRat (7568) 63, [1, 6]),
   (mkRat (39712) 105, [2, 5]),
   (mkRat (7408) 21, [3, 4])]

set_option maxHeartbeats 3000000 in
-- Merge eight certified screening rows.
set_option maxRecDepth 8192 in
theorem screen7Result1_check : reduceTwo screen7Rows1.flatten = screen7Result1 := by
  decide +kernel

theorem screen7Result1_sound :
    fo (sector (-2) (evRc (a0 1) (cα 1) screen7Input1)) =
      sector (-2 - 1) (evRc (a0 1) (cα 1) screen7Result1) := by
  apply screenRows_reduce _ _ screen7Rows1 _ _ screen7Result1_check
  exact .cons screen7Row8_sound <|
      .cons screen7Row9_sound <|
      .cons screen7Row10_sound <|
      .cons screen7Row11_sound <|
      .cons screen7Row12_sound <|
      .cons screen7Row13_sound <|
      .cons screen7Row14_sound <|
      .cons screen7Row15_sound .nil

def screen7Input2 : RawPoly ℕ :=
  [(-48, [0, 1, 5, 6]),
   (-15, [0, 2, 2, 2, 2, 4]),
   (mkRat (40) 3, [0, 2, 2, 2, 3, 3]),
   (mkRat (240) 7, [0, 2, 3, 7]),
   (-60, [0, 2, 4, 6]),
   (mkRat (144) 5, [0, 2, 5, 5]),
   (mkRat (-80) 3, [0, 3, 3, 6]),
   (24, [0, 3, 4, 5])]

def screen7Row16 : RawPoly ℕ :=
  [(mkRat (-16) 21, [0, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (-32) 3, [0, 1, 1, 1, 1, 3]),
   (-8, [0, 1, 1, 1, 2, 2]),
   (24, [0, 1, 2, 4]),
   (mkRat (32) 3, [0, 1, 3, 3]),
   (16, [0, 2, 2, 3]),
   (mkRat (192) 7, [0, 7]),
   (mkRat (48) 5, [1, 1, 1, 1, 1, 2]),
   (16, [1, 1, 1, 4]),
   (-8, [1, 2, 2, 2]),
   (64, [1, 6]),
   (mkRat (288) 5, [2, 5]),
   (-32, [3, 4])]

set_option maxHeartbeats 3000000 in
-- Exact scalar substitution in one cached exponential descendant.
set_option maxRecDepth 8192 in
theorem screen7Row16_check :
    screenTerm (-48, [0, 1, 5, 6]) sc885 = screen7Row16 := by
  decide +kernel

theorem screen7Row16_sound :
    fo (sector (-2) (evRc (a0 1) (cα 1) [(-48, [0, 1, 5, 6])])) =
      sector (-2 - 1) (evRc (a0 1) (cα 1) screen7Row16) := by
  rw [← screen7Row16_check]
  exact screenTerm_sound _ _ _ (fun c hc => sc885_sound (a0 1) c hc)

def screen7Row17 : RawPoly ℕ :=
  [(mkRat (4) 21, [0, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (20) 3, [0, 1, 1, 1, 1, 3]),
   (50, [0, 1, 1, 1, 2, 2]),
   (24, [0, 1, 1, 5]),
   (90, [0, 1, 2, 4]),
   (mkRat (40) 3, [0, 1, 3, 3]),
   (50, [0, 2, 2, 3]),
   (mkRat (120) 7, [0, 7]),
   (12, [1, 1, 1, 1, 1, 2]),
   (20, [1, 1, 1, 4]),
   (120, [1, 1, 2, 3]),
   (-10, [1, 2, 2, 2]),
   (-40, [1, 6]),
   (72, [2, 5]),
   (20, [3, 4])]

set_option maxHeartbeats 3000000 in
-- Exact scalar substitution in one cached exponential descendant.
set_option maxRecDepth 8192 in
theorem screen7Row17_check :
    screenTerm (-15, [0, 2, 2, 2, 2, 4]) sc2625 = screen7Row17 := by
  decide +kernel

theorem screen7Row17_sound :
    fo (sector (-2) (evRc (a0 1) (cα 1) [(-15, [0, 2, 2, 2, 2, 4])])) =
      sector (-2 - 1) (evRc (a0 1) (cα 1) screen7Row17) := by
  rw [← screen7Row17_check]
  exact screenTerm_sound _ _ _ (fun c hc => sc2625_sound (a0 1) c hc)

def screen7Row18 : RawPoly ℕ :=
  [(mkRat (-32) 189, [0, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (320) 27, [0, 1, 1, 1, 1, 3]),
   (mkRat (-80) 9, [0, 1, 1, 1, 2, 2]),
   (mkRat (-64) 3, [0, 1, 1, 5]),
   (mkRat (160) 3, [0, 1, 2, 4]),
   (mkRat (160) 27, [0, 1, 3, 3]),
   (mkRat (160) 9, [0, 2, 2, 3]),
   (mkRat (-320) 21, [0, 7]),
   (mkRat (-64) 9, [1, 1, 1, 1, 1, 2]),
   (mkRat (160) 9, [1, 1, 1, 4]),
   (mkRat (1280) 9, [1, 1, 2, 3]),
   (mkRat (320) 9, [1, 2, 2, 2]),
   (mkRat (320) 9, [1, 6]),
   (mkRat (-128) 3, [2, 5]),
   (mkRat (-320) 9, [3, 4])]

set_option maxHeartbeats 3000000 in
-- Exact scalar substitution in one cached exponential descendant.
set_option maxRecDepth 8192 in
theorem screen7Row18_check :
    screenTerm (mkRat (40) 3, [0, 2, 2, 2, 3, 3]) sc2650 = screen7Row18 := by
  decide +kernel

theorem screen7Row18_sound :
    fo (sector (-2) (evRc (a0 1) (cα 1) [(mkRat (40) 3, [0, 2, 2, 2, 3, 3])])) =
      sector (-2 - 1) (evRc (a0 1) (cα 1) screen7Row18) := by
  rw [← screen7Row18_check]
  exact screenTerm_sound _ _ _ (fun c hc => sc2650_sound (a0 1) c hc)

def screen7Row19 : RawPoly ℕ :=
  [(mkRat (-32) 147, [0, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (80) 21, [0, 1, 1, 1, 1, 3]),
   (mkRat (80) 7, [0, 1, 1, 1, 2, 2]),
   (mkRat (-192) 7, [0, 1, 1, 5]),
   (mkRat (640) 21, [0, 1, 3, 3]),
   (mkRat (-40) 7, [0, 2, 2, 3]),
   (mkRat (2400) 49, [0, 7]),
   (mkRat (160) 7, [1, 1, 1, 4]),
   (mkRat (-160) 7, [1, 2, 2, 2]),
   (mkRat (320) 7, [1, 6]),
   (mkRat (-80) 7, [3, 4])]

set_option maxHeartbeats 3000000 in
-- Exact scalar substitution in one cached exponential descendant.
set_option maxRecDepth 8192 in
theorem screen7Row19_check :
    screenTerm (mkRat (240) 7, [0, 2, 3, 7]) sc1038 = screen7Row19 := by
  decide +kernel

theorem screen7Row19_sound :
    fo (sector (-2) (evRc (a0 1) (cα 1) [(mkRat (240) 7, [0, 2, 3, 7])])) =
      sector (-2 - 1) (evRc (a0 1) (cα 1) screen7Row19) := by
  rw [← screen7Row19_check]
  exact screenTerm_sound _ _ _ (fun c hc => sc1038_sound (a0 1) c hc)

def screen7Row20 : RawPoly ℕ :=
  [(mkRat (8) 21, [0, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (40) 3, [0, 1, 1, 1, 1, 3]),
   (-20, [0, 1, 1, 1, 2, 2]),
   (48, [0, 1, 1, 5]),
   (mkRat (80) 3, [0, 1, 3, 3]),
   (-20, [0, 2, 2, 3]),
   (mkRat (240) 7, [0, 7]),
   (40, [1, 1, 1, 4]),
   (40, [1, 2, 2, 2]),
   (160, [1, 6]),
   (40, [3, 4])]

set_option maxHeartbeats 3000000 in
-- Exact scalar substitution in one cached exponential descendant.
set_option maxRecDepth 8192 in
theorem screen7Row20_check :
    screenTerm (-60, [0, 2, 4, 6]) sc1067 = screen7Row20 := by
  decide +kernel

theorem screen7Row20_sound :
    fo (sector (-2) (evRc (a0 1) (cα 1) [(-60, [0, 2, 4, 6])])) =
      sector (-2 - 1) (evRc (a0 1) (cα 1) screen7Row20) := by
  rw [← screen7Row20_check]
  exact screenTerm_sound _ _ _ (fun c hc => sc1067_sound (a0 1) c hc)

def screen7Row21 : RawPoly ℕ :=
  [(mkRat (-32) 175, [0, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (-32) 5, [0, 1, 1, 1, 1, 3]),
   (mkRat (48) 5, [0, 1, 1, 1, 2, 2]),
   (mkRat (2304) 25, [0, 1, 1, 5]),
   (mkRat (-64) 5, [0, 1, 3, 3]),
   (mkRat (48) 5, [0, 2, 2, 3]),
   (mkRat (-576) 35, [0, 7]),
   (mkRat (96) 5, [1, 1, 1, 4]),
   (mkRat (-96) 5, [1, 2, 2, 2]),
   (mkRat (192) 5, [1, 6]),
   (mkRat (96) 5, [3, 4])]

set_option maxHeartbeats 3000000 in
-- Exact scalar substitution in one cached exponential descendant.
set_option maxRecDepth 8192 in
theorem screen7Row21_check :
    screenTerm (mkRat (144) 5, [0, 2, 5, 5]) sc1082 = screen7Row21 := by
  decide +kernel

theorem screen7Row21_sound :
    fo (sector (-2) (evRc (a0 1) (cα 1) [(mkRat (144) 5, [0, 2, 5, 5])])) =
      sector (-2 - 1) (evRc (a0 1) (cα 1) screen7Row21) := by
  rw [← screen7Row21_check]
  exact screenTerm_sound _ _ _ (fun c hc => sc1082_sound (a0 1) c hc)

def screen7Row22 : RawPoly ℕ :=
  [(mkRat (32) 189, [0, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (-320) 27, [0, 1, 1, 1, 1, 3]),
   (mkRat (80) 9, [0, 1, 1, 1, 2, 2]),
   (mkRat (64) 3, [0, 1, 1, 5]),
   (mkRat (80) 3, [0, 1, 2, 4]),
   (mkRat (-160) 27, [0, 1, 3, 3]),
   (mkRat (-160) 9, [0, 2, 2, 3]),
   (mkRat (320) 21, [0, 7]),
   (mkRat (-32) 9, [1, 1, 1, 1, 1, 2]),
   (mkRat (-160) 9, [1, 1, 1, 4]),
   (mkRat (640) 9, [1, 1, 2, 3]),
   (mkRat (-80) 9, [1, 2, 2, 2]),
   (mkRat (640) 9, [1, 6]),
   (mkRat (-64) 3, [2, 5]),
   (mkRat (320) 9, [3, 4])]

set_option maxHeartbeats 3000000 in
-- Exact scalar substitution in one cached exponential descendant.
set_option maxRecDepth 8192 in
theorem screen7Row22_check :
    screenTerm (mkRat (-80) 3, [0, 3, 3, 6]) sc1143 = screen7Row22 := by
  decide +kernel

theorem screen7Row22_sound :
    fo (sector (-2) (evRc (a0 1) (cα 1) [(mkRat (-80) 3, [0, 3, 3, 6])])) =
      sector (-2 - 1) (evRc (a0 1) (cα 1) screen7Row22) := by
  rw [← screen7Row22_check]
  exact screenTerm_sound _ _ _ (fun c hc => sc1143_sound (a0 1) c hc)

def screen7Row23 : RawPoly ℕ :=
  [(mkRat (-16) 105, [0, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (8) 3, [0, 1, 1, 1, 1, 3]),
   (-8, [0, 1, 1, 1, 2, 2]),
   (mkRat (144) 5, [0, 1, 1, 5]),
   (24, [0, 1, 2, 4]),
   (mkRat (64) 3, [0, 1, 3, 3]),
   (4, [0, 2, 2, 3]),
   (mkRat (-96) 7, [0, 7]),
   (mkRat (16) 5, [1, 1, 1, 1, 1, 2]),
   (-16, [1, 1, 1, 4]),
   (-16, [1, 1, 2, 3]),
   (8, [1, 2, 2, 2]),
   (32, [1, 6]),
   (mkRat (-144) 5, [2, 5]),
   (8, [3, 4])]

set_option maxHeartbeats 3000000 in
-- Exact scalar substitution in one cached exponential descendant.
set_option maxRecDepth 8192 in
theorem screen7Row23_check :
    screenTerm (24, [0, 3, 4, 5]) sc1168 = screen7Row23 := by
  decide +kernel

theorem screen7Row23_sound :
    fo (sector (-2) (evRc (a0 1) (cα 1) [(24, [0, 3, 4, 5])])) =
      sector (-2 - 1) (evRc (a0 1) (cα 1) screen7Row23) := by
  rw [← screen7Row23_check]
  exact screenTerm_sound _ _ _ (fun c hc => sc1168_sound (a0 1) c hc)

def screen7Rows2 : List (RawPoly ℕ) :=
  [screen7Row16,
   screen7Row17,
   screen7Row18,
   screen7Row19,
   screen7Row20,
   screen7Row21,
   screen7Row22,
   screen7Row23]

def screen7Result2 : RawPoly ℕ :=
  [(mkRat (-2732) 3675, [0, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (988) 105, [0, 1, 1, 1, 1, 3]),
   (mkRat (1226) 35, [0, 1, 1, 1, 2, 2]),
   (mkRat (28968) 175, [0, 1, 1, 5]),
   (218, [0, 1, 2, 4]),
   (mkRat (9416) 105, [0, 1, 3, 3]),
   (mkRat (1886) 35, [0, 2, 2, 3]),
   (mkRat (23928) 245, [0, 7]),
   (mkRat (212) 15, [1, 1, 1, 1, 1, 2]),
   (mkRat (3572) 35, [1, 1, 1, 4]),
   (mkRat (952) 3, [1, 1, 2, 3]),
   (mkRat (1534) 105, [1, 2, 2, 2]),
   (mkRat (42712) 105, [1, 6]),
   (mkRat (184) 5, [2, 5]),
   (mkRat (1532) 35, [3, 4])]

set_option maxHeartbeats 3000000 in
-- Merge eight certified screening rows.
set_option maxRecDepth 8192 in
theorem screen7Result2_check : reduceTwo screen7Rows2.flatten = screen7Result2 := by
  decide +kernel

theorem screen7Result2_sound :
    fo (sector (-2) (evRc (a0 1) (cα 1) screen7Input2)) =
      sector (-2 - 1) (evRc (a0 1) (cα 1) screen7Result2) := by
  apply screenRows_reduce _ _ screen7Rows2 _ _ screen7Result2_check
  exact .cons screen7Row16_sound <|
      .cons screen7Row17_sound <|
      .cons screen7Row18_sound <|
      .cons screen7Row19_sound <|
      .cons screen7Row20_sound <|
      .cons screen7Row21_sound <|
      .cons screen7Row22_sound <|
      .cons screen7Row23_sound .nil

def screen7Input3 : RawPoly ℕ :=
  [(mkRat (-4) 315, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (-8) 63, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3]),
   (mkRat (-10) 7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2]),
   (mkRat (128) 35, [1, 1, 1, 1, 1, 1, 1, 5]),
   (mkRat (-16) 3, [1, 1, 1, 1, 1, 1, 3, 3]),
   (-8, [1, 1, 1, 1, 1, 2, 2, 3]),
   (mkRat (48) 7, [1, 1, 1, 1, 1, 7]),
   (-5, [1, 1, 1, 1, 2, 2, 2, 2])]

def screen7Row24 : RawPoly ℕ :=
  [(mkRat (9536) 99225, [0, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (6592) 567, [0, 1, 1, 1, 1, 3]),
   (mkRat (-5312) 945, [0, 1, 1, 1, 2, 2]),
   (mkRat (5632) 1575, [0, 1, 1, 5]),
   (mkRat (-64) 63, [0, 1, 2, 4]),
   (mkRat (-256) 567, [0, 1, 3, 3]),
   (mkRat (64) 945, [0, 2, 2, 3]),
   (mkRat (256) 2205, [0, 7]),
   (mkRat (77632) 4725, [1, 1, 1, 1, 1, 2]),
   (mkRat (10624) 945, [1, 1, 1, 4]),
   (mkRat (-5632) 945, [1, 1, 2, 3]),
   (mkRat (64) 189, [1, 2, 2, 2]),
   (mkRat (256) 189, [1, 6]),
   (mkRat (-256) 1575, [2, 5]),
   (mkRat (-128) 945, [3, 4])]

set_option maxHeartbeats 3000000 in
-- Exact scalar substitution in one cached exponential descendant.
set_option maxRecDepth 8192 in
theorem screen7Row24_check :
    screenTerm (mkRat (-4) 315, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) sc4295 = screen7Row24 := by
  decide +kernel

theorem screen7Row24_sound :
    fo (sector (-2) (evRc (a0 1) (cα 1) [(mkRat (-4) 315, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])])) =
      sector (-2 - 1) (evRc (a0 1) (cα 1) screen7Row24) := by
  rw [← screen7Row24_check]
  exact screenTerm_sound _ _ _ (fun c hc => sc4295_sound (a0 1) c hc)

def screen7Row25 : RawPoly ℕ :=
  [(mkRat (832) 3969, [0, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (-256) 81, [0, 1, 1, 1, 1, 3]),
   (mkRat (-1376) 189, [0, 1, 1, 1, 2, 2]),
   (mkRat (512) 63, [0, 1, 1, 5]),
   (mkRat (-32) 9, [0, 1, 2, 4]),
   (mkRat (256) 81, [0, 1, 3, 3]),
   (mkRat (-32) 189, [0, 2, 2, 3]),
   (mkRat (256) 441, [0, 7]),
   (mkRat (-128) 945, [1, 1, 1, 1, 1, 2]),
   (mkRat (2752) 189, [1, 1, 1, 4]),
   (mkRat (1280) 189, [1, 1, 2, 3]),
   (mkRat (32) 27, [1, 2, 2, 2]),
   (mkRat (128) 27, [1, 6]),
   (mkRat (-256) 315, [2, 5]),
   (mkRat (64) 189, [3, 4])]

set_option maxHeartbeats 3000000 in
-- Exact scalar substitution in one cached exponential descendant.
set_option maxRecDepth 8192 in
theorem screen7Row25_check :
    screenTerm (mkRat (-8) 63, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3]) sc4138 = screen7Row25 := by
  decide +kernel

theorem screen7Row25_sound :
    fo (sector (-2) (evRc (a0 1) (cα 1) [(mkRat (-8) 63, [1, 1, 1, 1, 1, 1, 1, 1, 1, 3])])) =
      sector (-2 - 1) (evRc (a0 1) (cα 1) screen7Row25) := by
  rw [← screen7Row25_check]
  exact screenTerm_sound _ _ _ (fun c hc => sc4138_sound (a0 1) c hc)

def screen7Row26 : RawPoly ℕ :=
  [(mkRat (-512) 147, [0, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (320) 21, [0, 1, 1, 1, 1, 3]),
   (mkRat (880) 21, [0, 1, 1, 1, 2, 2]),
   (64, [0, 1, 1, 5]),
   (mkRat (240) 7, [0, 1, 2, 4]),
   (mkRat (-320) 21, [0, 1, 3, 3]),
   (mkRat (-80) 21, [0, 2, 2, 3]),
   (mkRat (320) 49, [0, 7]),
   (mkRat (512) 21, [1, 1, 1, 1, 1, 2]),
   (mkRat (1760) 21, [1, 1, 1, 4]),
   (mkRat (320) 3, [1, 1, 2, 3]),
   (mkRat (80) 7, [1, 2, 2, 2]),
   (mkRat (320) 7, [1, 6]),
   (mkRat (64) 7, [2, 5]),
   (mkRat (-160) 21, [3, 4])]

set_option maxHeartbeats 3000000 in
-- Exact scalar substitution in one cached exponential descendant.
set_option maxRecDepth 8192 in
theorem screen7Row26_check :
    screenTerm (mkRat (-10) 7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2]) sc4162 = screen7Row26 := by
  decide +kernel

theorem screen7Row26_sound :
    fo (sector (-2) (evRc (a0 1) (cα 1) [(mkRat (-10) 7, [1, 1, 1, 1, 1, 1, 1, 1, 2, 2])])) =
      sector (-2 - 1) (evRc (a0 1) (cα 1) screen7Row26) := by
  rw [← screen7Row26_check]
  exact screenTerm_sound _ _ _ (fun c hc => sc4162_sound (a0 1) c hc)

def screen7Row27 : RawPoly ℕ :=
  [(mkRat (26752) 11025, [0, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (512) 63, [0, 1, 1, 1, 1, 3]),
   (mkRat (2176) 105, [0, 1, 1, 1, 2, 2]),
   (mkRat (13824) 175, [0, 1, 1, 5]),
   (mkRat (256) 7, [0, 1, 2, 4]),
   (mkRat (1024) 63, [0, 1, 3, 3]),
   (mkRat (-512) 105, [0, 2, 2, 3]),
   (mkRat (-2048) 245, [0, 7]),
   (mkRat (3328) 175, [1, 1, 1, 1, 1, 2]),
   (mkRat (-4352) 105, [1, 1, 1, 4]),
   (mkRat (3072) 35, [1, 1, 2, 3]),
   (mkRat (-256) 21, [1, 2, 2, 2]),
   (mkRat (-1024) 21, [1, 6]),
   (mkRat (-3072) 175, [2, 5]),
   (mkRat (1024) 105, [3, 4])]

set_option maxHeartbeats 3000000 in
-- Exact scalar substitution in one cached exponential descendant.
set_option maxRecDepth 8192 in
theorem screen7Row27_check :
    screenTerm (mkRat (128) 35, [1, 1, 1, 1, 1, 1, 1, 5]) sc3709 = screen7Row27 := by
  decide +kernel

theorem screen7Row27_sound :
    fo (sector (-2) (evRc (a0 1) (cα 1) [(mkRat (128) 35, [1, 1, 1, 1, 1, 1, 1, 5])])) =
      sector (-2 - 1) (evRc (a0 1) (cα 1) screen7Row27) := by
  rw [← screen7Row27_check]
  exact screenTerm_sound _ _ _ (fun c hc => sc3709_sound (a0 1) c hc)

def screen7Row28 : RawPoly ℕ :=
  [(mkRat (160) 189, [0, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (896) 27, [0, 1, 1, 1, 1, 3]),
   (mkRat (-32) 9, [0, 1, 1, 1, 2, 2]),
   (mkRat (128) 3, [0, 1, 1, 5]),
   (mkRat (-128) 3, [0, 1, 2, 4]),
   (mkRat (256) 27, [0, 1, 3, 3]),
   (mkRat (-128) 9, [0, 2, 2, 3]),
   (mkRat (256) 21, [0, 7]),
   (mkRat (-128) 45, [1, 1, 1, 1, 1, 2]),
   (mkRat (64) 9, [1, 1, 1, 4]),
   (mkRat (1280) 9, [1, 1, 2, 3]),
   (mkRat (128) 9, [1, 2, 2, 2]),
   (mkRat (512) 9, [1, 6]),
   (mkRat (-256) 15, [2, 5]),
   (mkRat (256) 9, [3, 4])]

set_option maxHeartbeats 3000000 in
-- Exact scalar substitution in one cached exponential descendant.
set_option maxRecDepth 8192 in
theorem screen7Row28_check :
    screenTerm (mkRat (-16) 3, [1, 1, 1, 1, 1, 1, 3, 3]) sc3772 = screen7Row28 := by
  decide +kernel

theorem screen7Row28_sound :
    fo (sector (-2) (evRc (a0 1) (cα 1) [(mkRat (-16) 3, [1, 1, 1, 1, 1, 1, 3, 3])])) =
      sector (-2 - 1) (evRc (a0 1) (cα 1) screen7Row28) := by
  rw [← screen7Row28_check]
  exact screenTerm_sound _ _ _ (fun c hc => sc3772_sound (a0 1) c hc)

def screen7Row29 : RawPoly ℕ :=
  [(mkRat (208) 105, [0, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (16) 3, [0, 1, 1, 1, 1, 3]),
   (mkRat (-32) 3, [0, 1, 1, 1, 2, 2]),
   (mkRat (128) 5, [0, 1, 1, 5]),
   (48, [0, 1, 2, 4]),
   (mkRat (128) 3, [0, 1, 3, 3]),
   (mkRat (16) 3, [0, 2, 2, 3]),
   (mkRat (128) 7, [0, 7]),
   (mkRat (-176) 15, [1, 1, 1, 1, 1, 2]),
   (mkRat (-64) 3, [1, 1, 1, 4]),
   (mkRat (-64) 3, [1, 1, 2, 3]),
   (16, [1, 2, 2, 2]),
   (64, [1, 6]),
   (mkRat (128) 5, [2, 5]),
   (mkRat (32) 3, [3, 4])]

set_option maxHeartbeats 3000000 in
-- Exact scalar substitution in one cached exponential descendant.
set_option maxRecDepth 8192 in
theorem screen7Row29_check :
    screenTerm (-8, [1, 1, 1, 1, 1, 2, 2, 3]) sc3817 = screen7Row29 := by
  decide +kernel

theorem screen7Row29_sound :
    fo (sector (-2) (evRc (a0 1) (cα 1) [(-8, [1, 1, 1, 1, 1, 2, 2, 3])])) =
      sector (-2 - 1) (evRc (a0 1) (cα 1) screen7Row29) := by
  rw [← screen7Row29_check]
  exact screenTerm_sound _ _ _ (fun c hc => sc3817_sound (a0 1) c hc)

def screen7Row30 : RawPoly ℕ :=
  [(mkRat (-208) 245, [0, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (32) 7, [0, 1, 1, 1, 1, 3]),
   (mkRat (-32) 7, [0, 1, 1, 1, 2, 2]),
   (mkRat (-384) 35, [0, 1, 1, 5]),
   (mkRat (144) 7, [0, 1, 2, 4]),
   (mkRat (64) 7, [0, 1, 3, 3]),
   (mkRat (-32) 7, [0, 2, 2, 3]),
   (mkRat (960) 49, [0, 7]),
   (mkRat (-176) 35, [1, 1, 1, 1, 1, 2]),
   (mkRat (64) 7, [1, 1, 1, 4]),
   (mkRat (128) 7, [1, 1, 2, 3]),
   (mkRat (-48) 7, [1, 2, 2, 2]),
   (mkRat (-192) 7, [1, 6]),
   (mkRat (384) 35, [2, 5]),
   (mkRat (64) 7, [3, 4])]

set_option maxHeartbeats 3000000 in
-- Exact scalar substitution in one cached exponential descendant.
set_option maxRecDepth 8192 in
theorem screen7Row30_check :
    screenTerm (mkRat (48) 7, [1, 1, 1, 1, 1, 7]) sc2800 = screen7Row30 := by
  decide +kernel

theorem screen7Row30_sound :
    fo (sector (-2) (evRc (a0 1) (cα 1) [(mkRat (48) 7, [1, 1, 1, 1, 1, 7])])) =
      sector (-2 - 1) (evRc (a0 1) (cα 1) screen7Row30) := by
  rw [← screen7Row30_check]
  exact screenTerm_sound _ _ _ (fun c hc => sc2800_sound (a0 1) c hc)

def screen7Row31 : RawPoly ℕ :=
  [(mkRat (-20) 63, [0, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (20) 9, [0, 1, 1, 1, 1, 3]),
   (mkRat (100) 3, [0, 1, 1, 1, 2, 2]),
   (60, [0, 1, 2, 4]),
   (mkRat (-80) 9, [0, 1, 3, 3]),
   (mkRat (100) 3, [0, 2, 2, 3]),
   (mkRat (80) 7, [0, 7]),
   (-12, [1, 1, 1, 1, 1, 2]),
   (mkRat (-40) 3, [1, 1, 1, 4]),
   (mkRat (20) 3, [1, 2, 2, 2]),
   (mkRat (80) 3, [1, 6]),
   (48, [2, 5]),
   (mkRat (-40) 3, [3, 4])]

set_option maxHeartbeats 3000000 in
-- Exact scalar substitution in one cached exponential descendant.
set_option maxRecDepth 8192 in
theorem screen7Row31_check :
    screenTerm (-5, [1, 1, 1, 1, 2, 2, 2, 2]) sc3869 = screen7Row31 := by
  decide +kernel

theorem screen7Row31_sound :
    fo (sector (-2) (evRc (a0 1) (cα 1) [(-5, [1, 1, 1, 1, 2, 2, 2, 2])])) =
      sector (-2 - 1) (evRc (a0 1) (cα 1) screen7Row31) := by
  rw [← screen7Row31_check]
  exact screenTerm_sound _ _ _ (fun c hc => sc3869_sound (a0 1) c hc)

def screen7Rows3 : List (RawPoly ℕ) :=
  [screen7Row24,
   screen7Row25,
   screen7Row26,
   screen7Row27,
   screen7Row28,
   screen7Row29,
   screen7Row30,
   screen7Row31]

def screen7Result3 : RawPoly ℕ :=
  [(mkRat (10036) 11025, [0, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (540) 7, [0, 1, 1, 1, 1, 3]),
   (mkRat (964) 15, [0, 1, 1, 1, 2, 2]),
   (mkRat (111296) 525, [0, 1, 1, 5]),
   (mkRat (3196) 21, [0, 1, 2, 4]),
   (mkRat (3536) 63, [0, 1, 3, 3]),
   (mkRat (388) 35, [0, 2, 2, 3]),
   (mkRat (44368) 735, [0, 7]),
   (mkRat (44236) 1575, [1, 1, 1, 1, 1, 2]),
   (mkRat (5224) 105, [1, 1, 1, 4]),
   (mkRat (105344) 315, [1, 1, 2, 3]),
   (mkRat (1940) 63, [1, 2, 2, 2]),
   (mkRat (7760) 63, [1, 6]),
   (mkRat (30512) 525, [2, 5]),
   (mkRat (1304) 35, [3, 4])]

set_option maxHeartbeats 3000000 in
-- Merge eight certified screening rows.
set_option maxRecDepth 8192 in
theorem screen7Result3_check : reduceTwo screen7Rows3.flatten = screen7Result3 := by
  decide +kernel

theorem screen7Result3_sound :
    fo (sector (-2) (evRc (a0 1) (cα 1) screen7Input3)) =
      sector (-2 - 1) (evRc (a0 1) (cα 1) screen7Result3) := by
  apply screenRows_reduce _ _ screen7Rows3 _ _ screen7Result3_check
  exact .cons screen7Row24_sound <|
      .cons screen7Row25_sound <|
      .cons screen7Row26_sound <|
      .cons screen7Row27_sound <|
      .cons screen7Row28_sound <|
      .cons screen7Row29_sound <|
      .cons screen7Row30_sound <|
      .cons screen7Row31_sound .nil

def screen7Input4 : RawPoly ℕ :=
  [(40, [1, 1, 1, 1, 2, 6]),
   (-16, [1, 1, 1, 1, 3, 5]),
   (-30, [1, 1, 1, 1, 4, 4]),
   (mkRat (160) 9, [1, 1, 1, 3, 3, 3]),
   (-40, [1, 1, 2, 2, 3, 3]),
   (mkRat (480) 7, [1, 1, 3, 7]),
   (mkRat (-288) 5, [1, 1, 5, 5]),
   (10, [1, 2, 2, 2, 2, 3])]

def screen7Row32 : RawPoly ℕ :=
  [(mkRat (80) 63, [0, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (-80) 9, [0, 1, 1, 1, 1, 3]),
   (mkRat (80) 3, [0, 1, 1, 1, 2, 2]),
   (mkRat (320) 9, [0, 1, 3, 3]),
   (mkRat (80) 3, [0, 2, 2, 3]),
   (mkRat (-320) 7, [0, 7]),
   (mkRat (160) 3, [1, 1, 1, 4]),
   (mkRat (160) 3, [1, 2, 2, 2]),
   (mkRat (640) 3, [1, 6]),
   (mkRat (160) 3, [3, 4])]

set_option maxHeartbeats 3000000 in
-- Exact scalar substitution in one cached exponential descendant.
set_option maxRecDepth 8192 in
theorem screen7Row32_check :
    screenTerm (40, [1, 1, 1, 1, 2, 6]) sc2857 = screen7Row32 := by
  decide +kernel

theorem screen7Row32_sound :
    fo (sector (-2) (evRc (a0 1) (cα 1) [(40, [1, 1, 1, 1, 2, 6])])) =
      sector (-2 - 1) (evRc (a0 1) (cα 1) screen7Row32) := by
  rw [← screen7Row32_check]
  exact screenTerm_sound _ _ _ (fun c hc => sc2857_sound (a0 1) c hc)

def screen7Row33 : RawPoly ℕ :=
  [(mkRat (-32) 63, [0, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (-16) 9, [0, 1, 1, 1, 1, 3]),
   (mkRat (32) 3, [0, 1, 1, 1, 2, 2]),
   (-32, [0, 1, 2, 4]),
   (mkRat (256) 9, [0, 1, 3, 3]),
   (mkRat (-16) 3, [0, 2, 2, 3]),
   (mkRat (128) 7, [0, 7]),
   (mkRat (32) 5, [1, 1, 1, 1, 1, 2]),
   (mkRat (-64) 3, [1, 1, 1, 4]),
   (mkRat (32) 3, [1, 2, 2, 2]),
   (mkRat (128) 3, [1, 6]),
   (mkRat (192) 5, [2, 5]),
   (mkRat (32) 3, [3, 4])]

set_option maxHeartbeats 3000000 in
-- Exact scalar substitution in one cached exponential descendant.
set_option maxRecDepth 8192 in
theorem screen7Row33_check :
    screenTerm (-16, [1, 1, 1, 1, 3, 5]) sc2892 = screen7Row33 := by
  decide +kernel

theorem screen7Row33_sound :
    fo (sector (-2) (evRc (a0 1) (cα 1) [(-16, [1, 1, 1, 1, 3, 5])])) =
      sector (-2 - 1) (evRc (a0 1) (cα 1) screen7Row33) := by
  rw [← screen7Row33_check]
  exact screenTerm_sound _ _ _ (fun c hc => sc2892_sound (a0 1) c hc)

def screen7Row34 : RawPoly ℕ :=
  [(mkRat (-20) 21, [0, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (20) 3, [0, 1, 1, 1, 1, 3]),
   (20, [0, 1, 1, 1, 2, 2]),
   (180, [0, 1, 2, 4]),
   (mkRat (-80) 3, [0, 1, 3, 3]),
   (20, [0, 2, 2, 3]),
   (mkRat (240) 7, [0, 7]),
   (12, [1, 1, 1, 1, 1, 2]),
   (120, [1, 1, 1, 4]),
   (20, [1, 2, 2, 2]),
   (80, [1, 6]),
   (-48, [2, 5]),
   (120, [3, 4])]

set_option maxHeartbeats 3000000 in
-- Exact scalar substitution in one cached exponential descendant.
set_option maxRecDepth 8192 in
theorem screen7Row34_check :
    screenTerm (-30, [1, 1, 1, 1, 4, 4]) sc2913 = screen7Row34 := by
  decide +kernel

theorem screen7Row34_sound :
    fo (sector (-2) (evRc (a0 1) (cα 1) [(-30, [1, 1, 1, 1, 4, 4])])) =
      sector (-2 - 1) (evRc (a0 1) (cα 1) screen7Row34) := by
  rw [← screen7Row34_check]
  exact screenTerm_sound _ _ _ (fun c hc => sc2913_sound (a0 1) c hc)

def screen7Row35 : RawPoly ℕ :=
  [(mkRat (544) 567, [0, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (2240) 81, [0, 1, 1, 1, 1, 3]),
   (mkRat (-80) 27, [0, 1, 1, 1, 2, 2]),
   (mkRat (128) 9, [0, 1, 1, 5]),
   (mkRat (160) 9, [0, 1, 2, 4]),
   (mkRat (3520) 81, [0, 1, 3, 3]),
   (mkRat (1120) 27, [0, 2, 2, 3]),
   (mkRat (-1280) 63, [0, 7]),
   (mkRat (128) 27, [1, 1, 1, 1, 1, 2]),
   (mkRat (160) 27, [1, 1, 1, 4]),
   (mkRat (2240) 27, [1, 1, 2, 3]),
   (mkRat (-160) 27, [1, 2, 2, 2]),
   (mkRat (-640) 27, [1, 6]),
   (mkRat (256) 9, [2, 5]),
   (mkRat (-2240) 27, [3, 4])]

set_option maxHeartbeats 3000000 in
-- Exact scalar substitution in one cached exponential descendant.
set_option maxRecDepth 8192 in
theorem screen7Row35_check :
    screenTerm (mkRat (160) 9, [1, 1, 1, 3, 3, 3]) sc3044 = screen7Row35 := by
  decide +kernel

theorem screen7Row35_sound :
    fo (sector (-2) (evRc (a0 1) (cα 1) [(mkRat (160) 9, [1, 1, 1, 3, 3, 3])])) =
      sector (-2 - 1) (evRc (a0 1) (cα 1) screen7Row35) := by
  rw [← screen7Row35_check]
  exact screenTerm_sound _ _ _ (fun c hc => sc3044_sound (a0 1) c hc)

def screen7Row36 : RawPoly ℕ :=
  [(mkRat (16) 7, [0, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (40) 3, [0, 1, 1, 1, 2, 2]),
   (-32, [0, 1, 1, 5]),
   (mkRat (160) 3, [0, 2, 2, 3]),
   (mkRat (320) 7, [0, 7]),
   (mkRat (32) 3, [1, 1, 1, 1, 1, 2]),
   (mkRat (80) 3, [1, 1, 1, 4]),
   (mkRat (320) 3, [1, 1, 2, 3]),
   (64, [2, 5]),
   (mkRat (320) 3, [3, 4])]

set_option maxHeartbeats 3000000 in
-- Exact scalar substitution in one cached exponential descendant.
set_option maxRecDepth 8192 in
theorem screen7Row36_check :
    screenTerm (-40, [1, 1, 2, 2, 3, 3]) sc3117 = screen7Row36 := by
  decide +kernel

theorem screen7Row36_sound :
    fo (sector (-2) (evRc (a0 1) (cα 1) [(-40, [1, 1, 2, 2, 3, 3])])) =
      sector (-2 - 1) (evRc (a0 1) (cα 1) screen7Row36) := by
  rw [← screen7Row36_check]
  exact screenTerm_sound _ _ _ (fun c hc => sc3117_sound (a0 1) c hc)

def screen7Row37 : RawPoly ℕ :=
  [(mkRat (-96) 49, [0, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (80) 7, [0, 1, 1, 1, 2, 2]),
   (mkRat (192) 7, [0, 1, 1, 5]),
   (mkRat (80) 7, [0, 2, 2, 3]),
   (mkRat (4800) 49, [0, 7]),
   (mkRat (64) 7, [1, 1, 1, 1, 1, 2]),
   (mkRat (-160) 7, [1, 1, 1, 4]),
   (mkRat (160) 7, [1, 1, 2, 3]),
   (mkRat (384) 7, [2, 5]),
   (mkRat (-160) 7, [3, 4])]

set_option maxHeartbeats 3000000 in
-- Exact scalar substitution in one cached exponential descendant.
set_option maxRecDepth 8192 in
theorem screen7Row37_check :
    screenTerm (mkRat (480) 7, [1, 1, 3, 7]) sc1486 = screen7Row37 := by
  decide +kernel

theorem screen7Row37_sound :
    fo (sector (-2) (evRc (a0 1) (cα 1) [(mkRat (480) 7, [1, 1, 3, 7])])) =
      sector (-2 - 1) (evRc (a0 1) (cα 1) screen7Row37) := by
  rw [← screen7Row37_check]
  exact screenTerm_sound _ _ _ (fun c hc => sc1486_sound (a0 1) c hc)

def screen7Row38 : RawPoly ℕ :=
  [(mkRat (288) 175, [0, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (-48) 5, [0, 1, 1, 1, 2, 2]),
   (mkRat (2304) 25, [0, 1, 1, 5]),
   (mkRat (96) 5, [0, 2, 2, 3]),
   (mkRat (1152) 35, [0, 7]),
   (mkRat (-192) 25, [1, 1, 1, 1, 1, 2]),
   (mkRat (96) 5, [1, 1, 1, 4]),
   (mkRat (192) 5, [1, 1, 2, 3]),
   (mkRat (4608) 25, [2, 5]),
   (mkRat (-192) 5, [3, 4])]

set_option maxHeartbeats 3000000 in
-- Exact scalar substitution in one cached exponential descendant.
set_option maxRecDepth 8192 in
theorem screen7Row38_check :
    screenTerm (mkRat (-288) 5, [1, 1, 5, 5]) sc1532 = screen7Row38 := by
  decide +kernel

theorem screen7Row38_sound :
    fo (sector (-2) (evRc (a0 1) (cα 1) [(mkRat (-288) 5, [1, 1, 5, 5])])) =
      sector (-2 - 1) (evRc (a0 1) (cα 1) screen7Row38) := by
  rw [← screen7Row38_check]
  exact screenTerm_sound _ _ _ (fun c hc => sc1532_sound (a0 1) c hc)

def screen7Row39 : RawPoly ℕ :=
  [(mkRat (20) 63, [0, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (-20) 9, [0, 1, 1, 1, 1, 3]),
   (mkRat (50) 3, [0, 1, 1, 1, 2, 2]),
   (30, [0, 1, 2, 4]),
   (mkRat (80) 9, [0, 1, 3, 3]),
   (mkRat (50) 3, [0, 2, 2, 3]),
   (mkRat (-80) 7, [0, 7]),
   (12, [1, 1, 1, 1, 1, 2]),
   (mkRat (-20) 3, [1, 1, 1, 4]),
   (mkRat (10) 3, [1, 2, 2, 2]),
   (mkRat (40) 3, [1, 6]),
   (-48, [2, 5]),
   (mkRat (-20) 3, [3, 4])]

set_option maxHeartbeats 3000000 in
-- Exact scalar substitution in one cached exponential descendant.
set_option maxRecDepth 8192 in
theorem screen7Row39_check :
    screenTerm (10, [1, 2, 2, 2, 2, 3]) sc3179 = screen7Row39 := by
  decide +kernel

theorem screen7Row39_sound :
    fo (sector (-2) (evRc (a0 1) (cα 1) [(10, [1, 2, 2, 2, 2, 3])])) =
      sector (-2 - 1) (evRc (a0 1) (cα 1) screen7Row39) := by
  rw [← screen7Row39_check]
  exact screenTerm_sound _ _ _ (fun c hc => sc3179_sound (a0 1) c hc)

def screen7Rows4 : List (RawPoly ℕ) :=
  [screen7Row32,
   screen7Row33,
   screen7Row34,
   screen7Row35,
   screen7Row36,
   screen7Row37,
   screen7Row38,
   screen7Row39]

def screen7Result4 : RawPoly ℕ :=
  [(mkRat (303496) 99225, [0, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (1736) 81, [0, 1, 1, 1, 1, 3]),
   (mkRat (81458) 945, [0, 1, 1, 1, 2, 2]),
   (mkRat (160352) 1575, [0, 1, 1, 5]),
   (mkRat (1762) 9, [0, 1, 2, 4]),
   (mkRat (7264) 81, [0, 1, 3, 3]),
   (mkRat (173354) 945, [0, 2, 2, 3]),
   (mkRat (334496) 2205, [0, 7]),
   (mkRat (223352) 4725, [1, 1, 1, 1, 1, 2]),
   (mkRat (164684) 945, [1, 1, 1, 4]),
   (mkRat (237088) 945, [1, 1, 2, 3]),
   (mkRat (2198) 27, [1, 2, 2, 2]),
   (mkRat (8792) 27, [1, 6]),
   (mkRat (431584) 1575, [2, 5]),
   (mkRat (132092) 945, [3, 4])]

set_option maxHeartbeats 3000000 in
-- Merge eight certified screening rows.
set_option maxRecDepth 8192 in
theorem screen7Result4_check : reduceTwo screen7Rows4.flatten = screen7Result4 := by
  decide +kernel

theorem screen7Result4_sound :
    fo (sector (-2) (evRc (a0 1) (cα 1) screen7Input4)) =
      sector (-2 - 1) (evRc (a0 1) (cα 1) screen7Result4) := by
  apply screenRows_reduce _ _ screen7Rows4 _ _ screen7Result4_check
  exact .cons screen7Row32_sound <|
      .cons screen7Row33_sound <|
      .cons screen7Row34_sound <|
      .cons screen7Row35_sound <|
      .cons screen7Row36_sound <|
      .cons screen7Row37_sound <|
      .cons screen7Row38_sound <|
      .cons screen7Row39_sound .nil

def screen7Input5 : RawPoly ℕ :=
  [(mkRat (360) 7, [1, 2, 2, 7]),
   (-80, [1, 2, 3, 6]),
   (-32, [1, 3, 3, 5]),
   (60, [1, 3, 4, 4]),
   (mkRat (-5) 2, [2, 2, 2, 2, 2, 2]),
   (-20, [2, 2, 2, 6]),
   (72, [2, 2, 3, 5]),
   (-45, [2, 2, 4, 4])]

def screen7Row40 : RawPoly ℕ :=
  [(mkRat (40) 49, [0, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (80) 7, [0, 1, 1, 1, 1, 3]),
   (mkRat (-60) 7, [0, 1, 1, 1, 2, 2]),
   (mkRat (180) 7, [0, 1, 2, 4]),
   (mkRat (-80) 7, [0, 1, 3, 3]),
   (mkRat (120) 7, [0, 2, 2, 3]),
   (mkRat (3600) 49, [0, 7]),
   (mkRat (72) 7, [1, 1, 1, 1, 1, 2]),
   (mkRat (-120) 7, [1, 1, 1, 4]),
   (mkRat (60) 7, [1, 2, 2, 2]),
   (mkRat (240) 7, [1, 6]),
   (mkRat (-288) 7, [2, 5]),
   (mkRat (240) 7, [3, 4])]

set_option maxHeartbeats 3000000 in
-- Exact scalar substitution in one cached exponential descendant.
set_option maxRecDepth 8192 in
theorem screen7Row40_check :
    screenTerm (mkRat (360) 7, [1, 2, 2, 7]) sc1619 = screen7Row40 := by
  decide +kernel

theorem screen7Row40_sound :
    fo (sector (-2) (evRc (a0 1) (cα 1) [(mkRat (360) 7, [1, 2, 2, 7])])) =
      sector (-2 - 1) (evRc (a0 1) (cα 1) screen7Row40) := by
  rw [← screen7Row40_check]
  exact screenTerm_sound _ _ _ (fun c hc => sc1619_sound (a0 1) c hc)

def screen7Row41 : RawPoly ℕ :=
  [(mkRat (-80) 63, [0, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (80) 9, [0, 1, 1, 1, 1, 3]),
   (mkRat (40) 3, [0, 1, 1, 1, 2, 2]),
   (mkRat (-320) 9, [0, 1, 3, 3]),
   (mkRat (40) 3, [0, 2, 2, 3]),
   (mkRat (320) 7, [0, 7]),
   (mkRat (80) 3, [1, 1, 1, 4]),
   (mkRat (80) 3, [1, 2, 2, 2]),
   (mkRat (320) 3, [1, 6]),
   (mkRat (80) 3, [3, 4])]

set_option maxHeartbeats 3000000 in
-- Exact scalar substitution in one cached exponential descendant.
set_option maxRecDepth 8192 in
theorem screen7Row41_check :
    screenTerm (-80, [1, 2, 3, 6]) sc1660 = screen7Row41 := by
  decide +kernel

theorem screen7Row41_sound :
    fo (sector (-2) (evRc (a0 1) (cα 1) [(-80, [1, 2, 3, 6])])) =
      sector (-2 - 1) (evRc (a0 1) (cα 1) screen7Row41) := by
  rw [← screen7Row41_check]
  exact screenTerm_sound _ _ _ (fun c hc => sc1660_sound (a0 1) c hc)

def screen7Row42 : RawPoly ℕ :=
  [(mkRat (-32) 63, [0, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (128) 9, [0, 1, 1, 1, 1, 3]),
   (mkRat (-16) 3, [0, 1, 1, 1, 2, 2]),
   (16, [0, 1, 2, 4]),
   (mkRat (-32) 9, [0, 1, 3, 3]),
   (mkRat (-64) 3, [0, 2, 2, 3]),
   (mkRat (128) 7, [0, 7]),
   (mkRat (32) 5, [1, 1, 1, 1, 1, 2]),
   (mkRat (32) 3, [1, 1, 1, 4]),
   (mkRat (-16) 3, [1, 2, 2, 2]),
   (mkRat (-64) 3, [1, 6]),
   (mkRat (192) 5, [2, 5]),
   (mkRat (128) 3, [3, 4])]

set_option maxHeartbeats 3000000 in
-- Exact scalar substitution in one cached exponential descendant.
set_option maxRecDepth 8192 in
theorem screen7Row42_check :
    screenTerm (-32, [1, 3, 3, 5]) sc1728 = screen7Row42 := by
  decide +kernel

theorem screen7Row42_sound :
    fo (sector (-2) (evRc (a0 1) (cα 1) [(-32, [1, 3, 3, 5])])) =
      sector (-2 - 1) (evRc (a0 1) (cα 1) screen7Row42) := by
  rw [← screen7Row42_check]
  exact screenTerm_sound _ _ _ (fun c hc => sc1728_sound (a0 1) c hc)

def screen7Row43 : RawPoly ℕ :=
  [(mkRat (20) 21, [0, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (-20) 3, [0, 1, 1, 1, 1, 3]),
   (10, [0, 1, 1, 1, 2, 2]),
   (90, [0, 1, 2, 4]),
   (mkRat (80) 3, [0, 1, 3, 3]),
   (10, [0, 2, 2, 3]),
   (mkRat (-240) 7, [0, 7]),
   (-12, [1, 1, 1, 1, 1, 2]),
   (60, [1, 1, 1, 4]),
   (10, [1, 2, 2, 2]),
   (40, [1, 6]),
   (48, [2, 5]),
   (60, [3, 4])]

set_option maxHeartbeats 3000000 in
-- Exact scalar substitution in one cached exponential descendant.
set_option maxRecDepth 8192 in
theorem screen7Row43_check :
    screenTerm (60, [1, 3, 4, 4]) sc1738 = screen7Row43 := by
  decide +kernel

theorem screen7Row43_sound :
    fo (sector (-2) (evRc (a0 1) (cα 1) [(60, [1, 3, 4, 4])])) =
      sector (-2 - 1) (evRc (a0 1) (cα 1) screen7Row43) := by
  rw [← screen7Row43_check]
  exact screenTerm_sound _ _ _ (fun c hc => sc1738_sound (a0 1) c hc)

def screen7Row44 : RawPoly ℕ :=
  [(mkRat (2) 63, [0, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (10) 9, [0, 1, 1, 1, 1, 3]),
   (mkRat (95) 3, [0, 1, 1, 1, 2, 2]),
   (4, [0, 1, 1, 5]),
   (-25, [0, 1, 2, 4]),
   (mkRat (20) 9, [0, 1, 3, 3]),
   (mkRat (95) 3, [0, 2, 2, 3]),
   (mkRat (20) 7, [0, 7]),
   (mkRat (10) 3, [1, 1, 1, 1, 1, 2]),
   (mkRat (-10) 3, [1, 1, 1, 4]),
   (mkRat (100) 3, [1, 1, 2, 3]),
   (mkRat (235) 3, [1, 2, 2, 2]),
   (mkRat (-20) 3, [1, 6]),
   (20, [2, 5]),
   (mkRat (-10) 3, [3, 4])]

set_option maxHeartbeats 3000000 in
-- Exact scalar substitution in one cached exponential descendant.
set_option maxRecDepth 8192 in
theorem screen7Row44_check :
    screenTerm (mkRat (-5) 2, [2, 2, 2, 2, 2, 2]) sc3226 = screen7Row44 := by
  decide +kernel

theorem screen7Row44_sound :
    fo (sector (-2) (evRc (a0 1) (cα 1) [(mkRat (-5) 2, [2, 2, 2, 2, 2, 2])])) =
      sector (-2 - 1) (evRc (a0 1) (cα 1) screen7Row44) := by
  rw [← screen7Row44_check]
  exact screenTerm_sound _ _ _ (fun c hc => sc3226_sound (a0 1) c hc)

def screen7Row45 : RawPoly ℕ :=
  [(mkRat (8) 63, [0, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (40) 9, [0, 1, 1, 1, 1, 3]),
   (mkRat (20) 3, [0, 1, 1, 1, 2, 2]),
   (16, [0, 1, 1, 5]),
   (-40, [0, 1, 2, 4]),
   (mkRat (80) 9, [0, 1, 3, 3]),
   (mkRat (20) 3, [0, 2, 2, 3]),
   (mkRat (80) 7, [0, 7]),
   (mkRat (16) 3, [1, 1, 1, 1, 1, 2]),
   (mkRat (-40) 3, [1, 1, 1, 4]),
   (mkRat (160) 3, [1, 1, 2, 3]),
   (mkRat (-80) 3, [1, 2, 2, 2]),
   (mkRat (160) 3, [1, 6]),
   (32, [2, 5]),
   (mkRat (-40) 3, [3, 4])]

set_option maxHeartbeats 3000000 in
-- Exact scalar substitution in one cached exponential descendant.
set_option maxRecDepth 8192 in
theorem screen7Row45_check :
    screenTerm (-20, [2, 2, 2, 6]) sc1834 = screen7Row45 := by
  decide +kernel

theorem screen7Row45_sound :
    fo (sector (-2) (evRc (a0 1) (cα 1) [(-20, [2, 2, 2, 6])])) =
      sector (-2 - 1) (evRc (a0 1) (cα 1) screen7Row45) := by
  rw [← screen7Row45_check]
  exact screenTerm_sound _ _ _ (fun c hc => sc1834_sound (a0 1) c hc)

def screen7Row46 : RawPoly ℕ :=
  [(mkRat (-16) 35, [0, 1, 1, 1, 1, 1, 1, 1]),
   (8, [0, 1, 1, 1, 1, 3]),
   (24, [0, 1, 1, 1, 2, 2]),
   (mkRat (432) 5, [0, 1, 1, 5]),
   (72, [0, 1, 2, 4]),
   (64, [0, 1, 3, 3]),
   (-12, [0, 2, 2, 3]),
   (mkRat (-288) 7, [0, 7]),
   (mkRat (-48) 5, [1, 1, 1, 1, 1, 2]),
   (48, [1, 1, 1, 4]),
   (48, [1, 1, 2, 3]),
   (24, [1, 2, 2, 2]),
   (96, [1, 6]),
   (mkRat (432) 5, [2, 5]),
   (-24, [3, 4])]

set_option maxHeartbeats 3000000 in
-- Exact scalar substitution in one cached exponential descendant.
set_option maxRecDepth 8192 in
theorem screen7Row46_check :
    screenTerm (72, [2, 2, 3, 5]) sc1870 = screen7Row46 := by
  decide +kernel

theorem screen7Row46_sound :
    fo (sector (-2) (evRc (a0 1) (cα 1) [(72, [2, 2, 3, 5])])) =
      sector (-2 - 1) (evRc (a0 1) (cα 1) screen7Row46) := by
  rw [← screen7Row46_check]
  exact screenTerm_sound _ _ _ (fun c hc => sc1870_sound (a0 1) c hc)

def screen7Row47 : RawPoly ℕ :=
  [(mkRat (2) 7, [0, 1, 1, 1, 1, 1, 1, 1]),
   (10, [0, 1, 1, 1, 1, 3]),
   (-15, [0, 1, 1, 1, 2, 2]),
   (36, [0, 1, 1, 5]),
   (135, [0, 1, 2, 4]),
   (20, [0, 1, 3, 3]),
   (-15, [0, 2, 2, 3]),
   (mkRat (180) 7, [0, 7]),
   (6, [1, 1, 1, 1, 1, 2]),
   (90, [1, 1, 1, 4]),
   (60, [1, 1, 2, 3]),
   (-15, [1, 2, 2, 2]),
   (-60, [1, 6]),
   (36, [2, 5]),
   (90, [3, 4])]

set_option maxHeartbeats 3000000 in
-- Exact scalar substitution in one cached exponential descendant.
set_option maxRecDepth 8192 in
theorem screen7Row47_check :
    screenTerm (-45, [2, 2, 4, 4]) sc1892 = screen7Row47 := by
  decide +kernel

theorem screen7Row47_sound :
    fo (sector (-2) (evRc (a0 1) (cα 1) [(-45, [2, 2, 4, 4])])) =
      sector (-2 - 1) (evRc (a0 1) (cα 1) screen7Row47) := by
  rw [← screen7Row47_check]
  exact screenTerm_sound _ _ _ (fun c hc => sc1892_sound (a0 1) c hc)

def screen7Rows5 : List (RawPoly ℕ) :=
  [screen7Row40,
   screen7Row41,
   screen7Row42,
   screen7Row43,
   screen7Row44,
   screen7Row45,
   screen7Row46,
   screen7Row47]

def screen7Result5 : RawPoly ℕ :=
  [(mkRat (-16) 735, [0, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (360) 7, [0, 1, 1, 1, 1, 3]),
   (mkRat (1192) 21, [0, 1, 1, 1, 2, 2]),
   (mkRat (712) 5, [0, 1, 1, 5]),
   (mkRat (1916) 7, [0, 1, 2, 4]),
   (mkRat (1496) 21, [0, 1, 3, 3]),
   (mkRat (640) 21, [0, 2, 2, 3]),
   (mkRat (5000) 49, [0, 7]),
   (mkRat (1024) 105, [1, 1, 1, 1, 1, 2]),
   (mkRat (4232) 21, [1, 1, 1, 4]),
   (mkRat (584) 3, [1, 1, 2, 3]),
   (mkRat (704) 7, [1, 2, 2, 2]),
   (mkRat (1696) 7, [1, 6]),
   (mkRat (7688) 35, [2, 5]),
   (mkRat (4472) 21, [3, 4])]

set_option maxHeartbeats 3000000 in
-- Merge eight certified screening rows.
set_option maxRecDepth 8192 in
theorem screen7Result5_check : reduceTwo screen7Rows5.flatten = screen7Result5 := by
  decide +kernel

theorem screen7Result5_sound :
    fo (sector (-2) (evRc (a0 1) (cα 1) screen7Input5)) =
      sector (-2 - 1) (evRc (a0 1) (cα 1) screen7Result5) := by
  apply screenRows_reduce _ _ screen7Rows5 _ _ screen7Result5_check
  exact .cons screen7Row40_sound <|
      .cons screen7Row41_sound <|
      .cons screen7Row42_sound <|
      .cons screen7Row43_sound <|
      .cons screen7Row44_sound <|
      .cons screen7Row45_sound <|
      .cons screen7Row46_sound <|
      .cons screen7Row47_sound .nil

def screen7Input6 : RawPoly ℕ :=
  [(mkRat (-80) 9, [3, 3, 3, 3]),
   (mkRat (288) 7, [5, 7]),
   (-40, [6, 6])]

def screen7Row48 : RawPoly ℕ :=
  [(mkRat (32) 567, [0, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (-800) 81, [0, 1, 1, 1, 1, 3]),
   (mkRat (80) 27, [0, 1, 1, 1, 2, 2]),
   (mkRat (64) 9, [0, 1, 1, 5]),
   (mkRat (80) 9, [0, 1, 2, 4]),
   (mkRat (5120) 81, [0, 1, 3, 3]),
   (mkRat (-400) 27, [0, 2, 2, 3]),
   (mkRat (320) 63, [0, 7]),
   (mkRat (-32) 27, [1, 1, 1, 1, 1, 2]),
   (mkRat (-160) 27, [1, 1, 1, 4]),
   (mkRat (1600) 27, [1, 1, 2, 3]),
   (mkRat (-80) 27, [1, 2, 2, 2]),
   (mkRat (-320) 27, [1, 6]),
   (mkRat (-64) 9, [2, 5]),
   (mkRat (800) 27, [3, 4])]

set_option maxHeartbeats 3000000 in
-- Exact scalar substitution in one cached exponential descendant.
set_option maxRecDepth 8192 in
theorem screen7Row48_check :
    screenTerm (mkRat (-80) 9, [3, 3, 3, 3]) sc1980 = screen7Row48 := by
  decide +kernel

theorem screen7Row48_sound :
    fo (sector (-2) (evRc (a0 1) (cα 1) [(mkRat (-80) 9, [3, 3, 3, 3])])) =
      sector (-2 - 1) (evRc (a0 1) (cα 1) screen7Row48) := by
  rw [← screen7Row48_check]
  exact screenTerm_sound _ _ _ (fun c hc => sc1980_sound (a0 1) c hc)

def screen7Row49 : RawPoly ℕ :=
  [(mkRat (-32) 245, [0, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (-32) 7, [0, 1, 1, 1, 1, 3]),
   (mkRat (-48) 7, [0, 1, 1, 1, 2, 2]),
   (mkRat (864) 35, [0, 1, 1, 5]),
   (mkRat (-144) 7, [0, 1, 2, 4]),
   (mkRat (-64) 7, [0, 1, 3, 3]),
   (mkRat (-48) 7, [0, 2, 2, 3]),
   (mkRat (1440) 49, [0, 7]),
   (mkRat (96) 35, [1, 1, 1, 1, 1, 2]),
   (mkRat (96) 7, [1, 1, 1, 4]),
   (mkRat (192) 7, [1, 1, 2, 3]),
   (mkRat (48) 7, [1, 2, 2, 2]),
   (mkRat (192) 7, [1, 6]),
   (mkRat (-864) 35, [2, 5]),
   (mkRat (96) 7, [3, 4])]

set_option maxHeartbeats 3000000 in
-- Exact scalar substitution in one cached exponential descendant.
set_option maxRecDepth 8192 in
theorem screen7Row49_check :
    screenTerm (mkRat (288) 7, [5, 7]) sc537 = screen7Row49 := by
  decide +kernel

theorem screen7Row49_sound :
    fo (sector (-2) (evRc (a0 1) (cα 1) [(mkRat (288) 7, [5, 7])])) =
      sector (-2 - 1) (evRc (a0 1) (cα 1) screen7Row49) := by
  rw [← screen7Row49_check]
  exact screenTerm_sound _ _ _ (fun c hc => sc537_sound (a0 1) c hc)

def screen7Row50 : RawPoly ℕ :=
  [(mkRat (8) 63, [0, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (40) 9, [0, 1, 1, 1, 1, 3]),
   (mkRat (20) 3, [0, 1, 1, 1, 2, 2]),
   (16, [0, 1, 1, 5]),
   (20, [0, 1, 2, 4]),
   (mkRat (80) 9, [0, 1, 3, 3]),
   (mkRat (20) 3, [0, 2, 2, 3]),
   (mkRat (80) 7, [0, 7]),
   (mkRat (-8) 3, [1, 1, 1, 1, 1, 2]),
   (mkRat (-40) 3, [1, 1, 1, 4]),
   (mkRat (-80) 3, [1, 1, 2, 3]),
   (mkRat (-20) 3, [1, 2, 2, 2]),
   (mkRat (400) 3, [1, 6]),
   (-16, [2, 5]),
   (mkRat (-40) 3, [3, 4])]

set_option maxHeartbeats 3000000 in
-- Exact scalar substitution in one cached exponential descendant.
set_option maxRecDepth 8192 in
theorem screen7Row50_check :
    screenTerm (-40, [6, 6]) sc546 = screen7Row50 := by
  decide +kernel

theorem screen7Row50_sound :
    fo (sector (-2) (evRc (a0 1) (cα 1) [(-40, [6, 6])])) =
      sector (-2 - 1) (evRc (a0 1) (cα 1) screen7Row50) := by
  rw [← screen7Row50_check]
  exact screenTerm_sound _ _ _ (fun c hc => sc546_sound (a0 1) c hc)

def screen7Rows6 : List (RawPoly ℕ) :=
  [screen7Row48,
   screen7Row49,
   screen7Row50]

def screen7Result6 : RawPoly ℕ :=
  [(mkRat (1048) 19845, [0, 1, 1, 1, 1, 1, 1, 1]),
   (mkRat (-5672) 567, [0, 1, 1, 1, 1, 3]),
   (mkRat (524) 189, [0, 1, 1, 1, 2, 2]),
   (mkRat (15056) 315, [0, 1, 1, 5]),
   (mkRat (524) 63, [0, 1, 2, 4]),
   (mkRat (35696) 567, [0, 1, 3, 3]),
   (mkRat (-2836) 189, [0, 2, 2, 3]),
   (mkRat (20240) 441, [0, 7]),
   (mkRat (-1048) 945, [1, 1, 1, 1, 1, 2]),
   (mkRat (-1048) 189, [1, 1, 1, 4]),
   (mkRat (11344) 189, [1, 1, 2, 3]),
   (mkRat (-524) 189, [1, 2, 2, 2]),
   (mkRat (28144) 189, [1, 6]),
   (mkRat (-15056) 315, [2, 5]),
   (mkRat (5672) 189, [3, 4])]

set_option maxHeartbeats 3000000 in
-- Merge eight certified screening rows.
set_option maxRecDepth 8192 in
theorem screen7Result6_check : reduceTwo screen7Rows6.flatten = screen7Result6 := by
  decide +kernel

theorem screen7Result6_sound :
    fo (sector (-2) (evRc (a0 1) (cα 1) screen7Input6)) =
      sector (-2 - 1) (evRc (a0 1) (cα 1) screen7Result6) := by
  apply screenRows_reduce _ _ screen7Rows6 _ _ screen7Result6_check
  exact .cons screen7Row48_sound <|
      .cons screen7Row49_sound <|
      .cons screen7Row50_sound .nil

def screen7Inputs : List (RawPoly ℕ) :=
  [screen7Input0,
   screen7Input1,
   screen7Input2,
   screen7Input3,
   screen7Input4,
   screen7Input5,
   screen7Input6]

def screen7Results : List (RawPoly ℕ) :=
  [screen7Result0,
   screen7Result1,
   screen7Result2,
   screen7Result3,
   screen7Result4,
   screen7Result5,
   screen7Result6]

set_option maxHeartbeats 3000000 in
-- Reassemble the finite input partition.
set_option maxRecDepth 8192 in
theorem screen7_inputs :
    screenState6 = screen7Inputs.flatten := by
  decide +kernel

set_option maxHeartbeats 3000000 in
-- Merge the independently certified screening blocks.
set_option maxRecDepth 8192 in
theorem screen7_results :
    reduceTwo screen7Results.flatten = screenState7 := by
  decide +kernel

theorem screen7_step :
    fo (sector (-2) (evRc (a0 1) (cα 1) screenState6)) =
      sector (-3) (evRc (a0 1) (cα 1) screenState7) := by
  rw [screen7_inputs]
  apply screenBlocks_reduce _ _ _ _ _ screen7_results
  exact .cons screen7Result0_sound <|
      .cons screen7Result1_sound <|
      .cons screen7Result2_sound <|
      .cons screen7Result3_sound <|
      .cons screen7Result4_sound <|
      .cons screen7Result5_sound <|
      .cons screen7Result6_sound .nil

theorem vn4_7_value :
    vn 4 7 = sector (-3) (evRc (a0 1) (cα 1) screenState7) := by
  have hv : vn 4 7 = fo (vn 4 6) := by
    simp only [vn, pow_succ', Module.End.mul_apply]
  rw [hv]
  rw [vn4_6_value]
  exact screen7_step

end VOA.Classification.COne.OrbOctaRC
