import VOA.Classification.COne.OrbOctaRCScreenBlocks
import VOA.Classification.COne.OrbOctaRCScreenCache21
import VOA.Classification.COne.OrbOctaRCScreen7

/-! One exact screening step, checked in blocks of eight source monomials. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
namespace VOA.Classification.COne.OrbOctaRC
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational HeisenbergN
  PlusC2Eval PlusUnitary PlusC2 OrbC2e OrbC2g OrbC2h LatMod OrbRat6 OrbPrim

def screenState8 : RawPoly ℕ :=
  [(40320, [])]

def screen8Input0 : RawPoly ℕ :=
  [(8, [0, 1, 1, 1, 1, 1, 1, 1]),
   (280, [0, 1, 1, 1, 1, 3]),
   (420, [0, 1, 1, 1, 2, 2]),
   (1008, [0, 1, 1, 5]),
   (1260, [0, 1, 2, 4]),
   (560, [0, 1, 3, 3]),
   (420, [0, 2, 2, 3]),
   (720, [0, 7])]

def screen8Row0 : RawPoly ℕ :=
  [(128, [])]

set_option maxHeartbeats 3000000 in
-- Exact scalar substitution in one cached exponential descendant.
set_option maxRecDepth 8192 in
theorem screen8Row0_check :
    screenTerm (8, [0, 1, 1, 1, 1, 1, 1, 1]) sc3263 = screen8Row0 := by
  decide +kernel

theorem screen8Row0_sound :
    fo (sector (-3) (evRc (a0 1) (cα 1) [(8, [0, 1, 1, 1, 1, 1, 1, 1])])) =
      sector (-3 - 1) (evRc (a0 1) (cα 1) screen8Row0) := by
  rw [← screen8Row0_check]
  exact screenTerm_sound _ _ _ (fun c hc => sc3263_sound (a0 1) c hc)

def screen8Row1 : RawPoly ℕ :=
  [(2240, [])]

set_option maxHeartbeats 3000000 in
-- Exact scalar substitution in one cached exponential descendant.
set_option maxRecDepth 8192 in
theorem screen8Row1_check :
    screenTerm (280, [0, 1, 1, 1, 1, 3]) sc2055 = screen8Row1 := by
  decide +kernel

theorem screen8Row1_sound :
    fo (sector (-3) (evRc (a0 1) (cα 1) [(280, [0, 1, 1, 1, 1, 3])])) =
      sector (-3 - 1) (evRc (a0 1) (cα 1) screen8Row1) := by
  rw [← screen8Row1_check]
  exact screenTerm_sound _ _ _ (fun c hc => sc2055_sound (a0 1) c hc)

def screen8Row2 : RawPoly ℕ :=
  [(3360, [])]

set_option maxHeartbeats 3000000 in
-- Exact scalar substitution in one cached exponential descendant.
set_option maxRecDepth 8192 in
theorem screen8Row2_check :
    screenTerm (420, [0, 1, 1, 1, 2, 2]) sc2121 = screen8Row2 := by
  decide +kernel

theorem screen8Row2_sound :
    fo (sector (-3) (evRc (a0 1) (cα 1) [(420, [0, 1, 1, 1, 2, 2])])) =
      sector (-3 - 1) (evRc (a0 1) (cα 1) screen8Row2) := by
  rw [← screen8Row2_check]
  exact screenTerm_sound _ _ _ (fun c hc => sc2121_sound (a0 1) c hc)

def screen8Row3 : RawPoly ℕ :=
  [(4032, [])]

set_option maxHeartbeats 3000000 in
-- Exact scalar substitution in one cached exponential descendant.
set_option maxRecDepth 8192 in
theorem screen8Row3_check :
    screenTerm (1008, [0, 1, 1, 5]) sc633 = screen8Row3 := by
  decide +kernel

theorem screen8Row3_sound :
    fo (sector (-3) (evRc (a0 1) (cα 1) [(1008, [0, 1, 1, 5])])) =
      sector (-3 - 1) (evRc (a0 1) (cα 1) screen8Row3) := by
  rw [← screen8Row3_check]
  exact screenTerm_sound _ _ _ (fun c hc => sc633_sound (a0 1) c hc)

def screen8Row4 : RawPoly ℕ :=
  [(5040, [])]

set_option maxHeartbeats 3000000 in
-- Exact scalar substitution in one cached exponential descendant.
set_option maxRecDepth 8192 in
theorem screen8Row4_check :
    screenTerm (1260, [0, 1, 2, 4]) sc713 = screen8Row4 := by
  decide +kernel

theorem screen8Row4_sound :
    fo (sector (-3) (evRc (a0 1) (cα 1) [(1260, [0, 1, 2, 4])])) =
      sector (-3 - 1) (evRc (a0 1) (cα 1) screen8Row4) := by
  rw [← screen8Row4_check]
  exact screenTerm_sound _ _ _ (fun c hc => sc713_sound (a0 1) c hc)

def screen8Row5 : RawPoly ℕ :=
  [(2240, [])]

set_option maxHeartbeats 3000000 in
-- Exact scalar substitution in one cached exponential descendant.
set_option maxRecDepth 8192 in
theorem screen8Row5_check :
    screenTerm (560, [0, 1, 3, 3]) sc765 = screen8Row5 := by
  decide +kernel

theorem screen8Row5_sound :
    fo (sector (-3) (evRc (a0 1) (cα 1) [(560, [0, 1, 3, 3])])) =
      sector (-3 - 1) (evRc (a0 1) (cα 1) screen8Row5) := by
  rw [← screen8Row5_check]
  exact screenTerm_sound _ _ _ (fun c hc => sc765_sound (a0 1) c hc)

def screen8Row6 : RawPoly ℕ :=
  [(1680, [])]

set_option maxHeartbeats 3000000 in
-- Exact scalar substitution in one cached exponential descendant.
set_option maxRecDepth 8192 in
theorem screen8Row6_check :
    screenTerm (420, [0, 2, 2, 3]) sc926 = screen8Row6 := by
  decide +kernel

theorem screen8Row6_sound :
    fo (sector (-3) (evRc (a0 1) (cα 1) [(420, [0, 2, 2, 3])])) =
      sector (-3 - 1) (evRc (a0 1) (cα 1) screen8Row6) := by
  rw [← screen8Row6_check]
  exact screenTerm_sound _ _ _ (fun c hc => sc926_sound (a0 1) c hc)

def screen8Row7 : RawPoly ℕ :=
  [(1440, [])]

set_option maxHeartbeats 3000000 in
-- Exact scalar substitution in one cached exponential descendant.
set_option maxRecDepth 8192 in
theorem screen8Row7_check :
    screenTerm (720, [0, 7]) sc147 = screen8Row7 := by
  decide +kernel

theorem screen8Row7_sound :
    fo (sector (-3) (evRc (a0 1) (cα 1) [(720, [0, 7])])) =
      sector (-3 - 1) (evRc (a0 1) (cα 1) screen8Row7) := by
  rw [← screen8Row7_check]
  exact screenTerm_sound _ _ _ (fun c hc => sc147_sound (a0 1) c hc)

def screen8Rows0 : List (RawPoly ℕ) :=
  [screen8Row0,
   screen8Row1,
   screen8Row2,
   screen8Row3,
   screen8Row4,
   screen8Row5,
   screen8Row6,
   screen8Row7]

def screen8Result0 : RawPoly ℕ :=
  [(20160, [])]

set_option maxHeartbeats 3000000 in
-- Merge eight certified screening rows.
set_option maxRecDepth 8192 in
theorem screen8Result0_check : reduceTwo screen8Rows0.flatten = screen8Result0 := by
  decide +kernel

theorem screen8Result0_sound :
    fo (sector (-3) (evRc (a0 1) (cα 1) screen8Input0)) =
      sector (-3 - 1) (evRc (a0 1) (cα 1) screen8Result0) := by
  apply screenRows_reduce _ _ screen8Rows0 _ _ screen8Result0_check
  exact .cons screen8Row0_sound <|
      .cons screen8Row1_sound <|
      .cons screen8Row2_sound <|
      .cons screen8Row3_sound <|
      .cons screen8Row4_sound <|
      .cons screen8Row5_sound <|
      .cons screen8Row6_sound <|
      .cons screen8Row7_sound .nil

def screen8Input1 : RawPoly ℕ :=
  [(168, [1, 1, 1, 1, 1, 2]),
   (840, [1, 1, 1, 4]),
   (1680, [1, 1, 2, 3]),
   (420, [1, 2, 2, 2]),
   (1680, [1, 6]),
   (1008, [2, 5]),
   (840, [3, 4])]

def screen8Row8 : RawPoly ℕ :=
  [(1344, [])]

set_option maxHeartbeats 3000000 in
-- Exact scalar substitution in one cached exponential descendant.
set_option maxRecDepth 8192 in
theorem screen8Row8_check :
    screenTerm (168, [1, 1, 1, 1, 1, 2]) sc2734 = screen8Row8 := by
  decide +kernel

theorem screen8Row8_sound :
    fo (sector (-3) (evRc (a0 1) (cα 1) [(168, [1, 1, 1, 1, 1, 2])])) =
      sector (-3 - 1) (evRc (a0 1) (cα 1) screen8Row8) := by
  rw [← screen8Row8_check]
  exact screenTerm_sound _ _ _ (fun c hc => sc2734_sound (a0 1) c hc)

def screen8Row9 : RawPoly ℕ :=
  [(3360, [])]

set_option maxHeartbeats 3000000 in
-- Exact scalar substitution in one cached exponential descendant.
set_option maxRecDepth 8192 in
theorem screen8Row9_check :
    screenTerm (840, [1, 1, 1, 4]) sc1301 = screen8Row9 := by
  decide +kernel

theorem screen8Row9_sound :
    fo (sector (-3) (evRc (a0 1) (cα 1) [(840, [1, 1, 1, 4])])) =
      sector (-3 - 1) (evRc (a0 1) (cα 1) screen8Row9) := by
  rw [← screen8Row9_check]
  exact screenTerm_sound _ _ _ (fun c hc => sc1301_sound (a0 1) c hc)

def screen8Row10 : RawPoly ℕ :=
  [(6720, [])]

set_option maxHeartbeats 3000000 in
-- Exact scalar substitution in one cached exponential descendant.
set_option maxRecDepth 8192 in
theorem screen8Row10_check :
    screenTerm (1680, [1, 1, 2, 3]) sc1374 = screen8Row10 := by
  decide +kernel

theorem screen8Row10_sound :
    fo (sector (-3) (evRc (a0 1) (cα 1) [(1680, [1, 1, 2, 3])])) =
      sector (-3 - 1) (evRc (a0 1) (cα 1) screen8Row10) := by
  rw [← screen8Row10_check]
  exact screenTerm_sound _ _ _ (fun c hc => sc1374_sound (a0 1) c hc)

def screen8Row11 : RawPoly ℕ :=
  [(1680, [])]

set_option maxHeartbeats 3000000 in
-- Exact scalar substitution in one cached exponential descendant.
set_option maxRecDepth 8192 in
theorem screen8Row11_check :
    screenTerm (420, [1, 2, 2, 2]) sc1559 = screen8Row11 := by
  decide +kernel

theorem screen8Row11_sound :
    fo (sector (-3) (evRc (a0 1) (cα 1) [(420, [1, 2, 2, 2])])) =
      sector (-3 - 1) (evRc (a0 1) (cα 1) screen8Row11) := by
  rw [← screen8Row11_check]
  exact screenTerm_sound _ _ _ (fun c hc => sc1559_sound (a0 1) c hc)

def screen8Row12 : RawPoly ℕ :=
  [(3360, [])]

set_option maxHeartbeats 3000000 in
-- Exact scalar substitution in one cached exponential descendant.
set_option maxRecDepth 8192 in
theorem screen8Row12_check :
    screenTerm (1680, [1, 6]) sc263 = screen8Row12 := by
  decide +kernel

theorem screen8Row12_sound :
    fo (sector (-3) (evRc (a0 1) (cα 1) [(1680, [1, 6])])) =
      sector (-3 - 1) (evRc (a0 1) (cα 1) screen8Row12) := by
  rw [← screen8Row12_check]
  exact screenTerm_sound _ _ _ (fun c hc => sc263_sound (a0 1) c hc)

def screen8Row13 : RawPoly ℕ :=
  [(2016, [])]

set_option maxHeartbeats 3000000 in
-- Exact scalar substitution in one cached exponential descendant.
set_option maxRecDepth 8192 in
theorem screen8Row13_check :
    screenTerm (1008, [2, 5]) sc349 = screen8Row13 := by
  decide +kernel

theorem screen8Row13_sound :
    fo (sector (-3) (evRc (a0 1) (cα 1) [(1008, [2, 5])])) =
      sector (-3 - 1) (evRc (a0 1) (cα 1) screen8Row13) := by
  rw [← screen8Row13_check]
  exact screenTerm_sound _ _ _ (fun c hc => sc349_sound (a0 1) c hc)

def screen8Row14 : RawPoly ℕ :=
  [(1680, [])]

set_option maxHeartbeats 3000000 in
-- Exact scalar substitution in one cached exponential descendant.
set_option maxRecDepth 8192 in
theorem screen8Row14_check :
    screenTerm (840, [3, 4]) sc410 = screen8Row14 := by
  decide +kernel

theorem screen8Row14_sound :
    fo (sector (-3) (evRc (a0 1) (cα 1) [(840, [3, 4])])) =
      sector (-3 - 1) (evRc (a0 1) (cα 1) screen8Row14) := by
  rw [← screen8Row14_check]
  exact screenTerm_sound _ _ _ (fun c hc => sc410_sound (a0 1) c hc)

def screen8Rows1 : List (RawPoly ℕ) :=
  [screen8Row8,
   screen8Row9,
   screen8Row10,
   screen8Row11,
   screen8Row12,
   screen8Row13,
   screen8Row14]

def screen8Result1 : RawPoly ℕ :=
  [(20160, [])]

set_option maxHeartbeats 3000000 in
-- Merge eight certified screening rows.
set_option maxRecDepth 8192 in
theorem screen8Result1_check : reduceTwo screen8Rows1.flatten = screen8Result1 := by
  decide +kernel

theorem screen8Result1_sound :
    fo (sector (-3) (evRc (a0 1) (cα 1) screen8Input1)) =
      sector (-3 - 1) (evRc (a0 1) (cα 1) screen8Result1) := by
  apply screenRows_reduce _ _ screen8Rows1 _ _ screen8Result1_check
  exact .cons screen8Row8_sound <|
      .cons screen8Row9_sound <|
      .cons screen8Row10_sound <|
      .cons screen8Row11_sound <|
      .cons screen8Row12_sound <|
      .cons screen8Row13_sound <|
      .cons screen8Row14_sound .nil

def screen8Inputs : List (RawPoly ℕ) :=
  [screen8Input0,
   screen8Input1]

def screen8Results : List (RawPoly ℕ) :=
  [screen8Result0,
   screen8Result1]

set_option maxHeartbeats 3000000 in
-- Reassemble the finite input partition.
set_option maxRecDepth 8192 in
theorem screen8_inputs :
    screenState7 = screen8Inputs.flatten := by
  decide +kernel

set_option maxHeartbeats 3000000 in
-- Merge the independently certified screening blocks.
set_option maxRecDepth 8192 in
theorem screen8_results :
    reduceTwo screen8Results.flatten = screenState8 := by
  decide +kernel

theorem screen8_step :
    fo (sector (-3) (evRc (a0 1) (cα 1) screenState7)) =
      sector (-4) (evRc (a0 1) (cα 1) screenState8) := by
  rw [screen8_inputs]
  apply screenBlocks_reduce _ _ _ _ _ screen8_results
  exact .cons screen8Result0_sound <|
      .cons screen8Result1_sound .nil

theorem vn4_8_value :
    vn 4 8 = sector (-4) (evRc (a0 1) (cα 1) screenState8) := by
  have hv : vn 4 8 = fo (vn 4 7) := by
    simp only [vn, pow_succ', Module.End.mul_apply]
  rw [hv]
  rw [vn4_7_value]
  exact screen8_step

end VOA.Classification.COne.OrbOctaRC
