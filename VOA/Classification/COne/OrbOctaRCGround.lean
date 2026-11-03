import VOA.Classification.COne.OrbOctaRCVirWords

set_option Elab.async false
set_option maxSynthPendingDepth 3
namespace VOA.Classification.COne.OrbOctaRC
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational HeisenbergN
  PlusC2Eval PlusUnitary PlusC2 OrbC2e OrbC2g OrbC2h LatMod

def groundL1 : RawPoly ℕ :=
  [(4,
    [0, 1])]

set_option maxHeartbeats 1000000 in
-- Evaluate one Virasoro mode on the charged ground state.
set_option maxRecDepth 4096 in
theorem groundL1_check :
    neutralQuickOne omR 0 4 [(1, [])] = groundL1 := by
  decide +kernel

def groundL2 : RawPoly ℕ :=
  [(4,
    [0, 2]),
   (mkRat (1) 2,
    [1, 1])]

set_option maxHeartbeats 1000000 in
-- Evaluate one Virasoro mode on the charged ground state.
set_option maxRecDepth 4096 in
theorem groundL2_check :
    neutralQuickOne omR (-1) 4 [(1, [])] = groundL2 := by
  decide +kernel

def groundL3 : RawPoly ℕ :=
  [(4,
    [0, 3]),
   (1,
    [1, 2])]

set_option maxHeartbeats 1000000 in
-- Evaluate one Virasoro mode on the charged ground state.
set_option maxRecDepth 4096 in
theorem groundL3_check :
    neutralQuickOne omR (-2) 4 [(1, [])] = groundL3 := by
  decide +kernel

def groundL4 : RawPoly ℕ :=
  [(4,
    [0, 4]),
   (1,
    [1, 3]),
   (mkRat (1) 2,
    [2, 2])]

set_option maxHeartbeats 1000000 in
-- Evaluate one Virasoro mode on the charged ground state.
set_option maxRecDepth 4096 in
theorem groundL4_check :
    neutralQuickOne omR (-3) 4 [(1, [])] = groundL4 := by
  decide +kernel

def groundL5 : RawPoly ℕ :=
  [(4,
    [0, 5]),
   (1,
    [1, 4]),
   (1,
    [2, 3])]

set_option maxHeartbeats 1000000 in
-- Evaluate one Virasoro mode on the charged ground state.
set_option maxRecDepth 4096 in
theorem groundL5_check :
    neutralQuickOne omR (-4) 4 [(1, [])] = groundL5 := by
  decide +kernel

def groundL6 : RawPoly ℕ :=
  [(4,
    [0, 6]),
   (1,
    [1, 5]),
   (1,
    [2, 4]),
   (mkRat (1) 2,
    [3, 3])]

set_option maxHeartbeats 1000000 in
-- Evaluate one Virasoro mode on the charged ground state.
set_option maxRecDepth 4096 in
theorem groundL6_check :
    neutralQuickOne omR (-5) 4 [(1, [])] = groundL6 := by
  decide +kernel

def groundL7 : RawPoly ℕ :=
  [(4,
    [0, 7]),
   (1,
    [1, 6]),
   (1,
    [2, 5]),
   (1,
    [3, 4])]

set_option maxHeartbeats 1000000 in
-- Evaluate one Virasoro mode on the charged ground state.
set_option maxRecDepth 4096 in
theorem groundL7_check :
    neutralQuickOne omR (-6) 4 [(1, [])] = groundL7 := by
  decide +kernel

def groundL8 : RawPoly ℕ :=
  [(4,
    [0, 8]),
   (1,
    [1, 7]),
   (1,
    [2, 6]),
   (1,
    [3, 5]),
   (mkRat (1) 2,
    [4, 4])]

set_option maxHeartbeats 1000000 in
-- Evaluate one Virasoro mode on the charged ground state.
set_option maxRecDepth 4096 in
theorem groundL8_check :
    neutralQuickOne omR (-7) 4 [(1, [])] = groundL8 := by
  decide +kernel

def groundL9 : RawPoly ℕ :=
  [(4,
    [0, 9]),
   (1,
    [1, 8]),
   (1,
    [2, 7]),
   (1,
    [3, 6]),
   (1,
    [4, 5])]

set_option maxHeartbeats 1000000 in
-- Evaluate one Virasoro mode on the charged ground state.
set_option maxRecDepth 4096 in
theorem groundL9_check :
    neutralQuickOne omR (-8) 4 [(1, [])] = groundL9 := by
  decide +kernel

def groundL10 : RawPoly ℕ :=
  [(4,
    [0, 10]),
   (1,
    [1, 9]),
   (1,
    [2, 8]),
   (1,
    [3, 7]),
   (1,
    [4, 6]),
   (mkRat (1) 2,
    [5, 5])]

set_option maxHeartbeats 1000000 in
-- Evaluate one Virasoro mode on the charged ground state.
set_option maxRecDepth 4096 in
theorem groundL10_check :
    neutralQuickOne omR (-9) 4 [(1, [])] = groundL10 := by
  decide +kernel

def groundL11 : RawPoly ℕ :=
  [(4,
    [0, 11]),
   (1,
    [1, 10]),
   (1,
    [2, 9]),
   (1,
    [3, 8]),
   (1,
    [4, 7]),
   (1,
    [5, 6])]

set_option maxHeartbeats 1000000 in
-- Evaluate one Virasoro mode on the charged ground state.
set_option maxRecDepth 4096 in
theorem groundL11_check :
    neutralQuickOne omR (-10) 4 [(1, [])] = groundL11 := by
  decide +kernel

def groundL12 : RawPoly ℕ :=
  [(4,
    [0, 12]),
   (1,
    [1, 11]),
   (1,
    [2, 10]),
   (1,
    [3, 9]),
   (1,
    [4, 8]),
   (1,
    [5, 7]),
   (mkRat (1) 2,
    [6, 6])]

set_option maxHeartbeats 1000000 in
-- Evaluate one Virasoro mode on the charged ground state.
set_option maxRecDepth 4096 in
theorem groundL12_check :
    neutralQuickOne omR (-11) 4 [(1, [])] = groundL12 := by
  decide +kernel

def groundL13 : RawPoly ℕ :=
  [(4,
    [0, 13]),
   (1,
    [1, 12]),
   (1,
    [2, 11]),
   (1,
    [3, 10]),
   (1,
    [4, 9]),
   (1,
    [5, 8]),
   (1,
    [6, 7])]

set_option maxHeartbeats 1000000 in
-- Evaluate one Virasoro mode on the charged ground state.
set_option maxRecDepth 4096 in
theorem groundL13_check :
    neutralQuickOne omR (-12) 4 [(1, [])] = groundL13 := by
  decide +kernel

def groundL14 : RawPoly ℕ :=
  [(4,
    [0, 14]),
   (1,
    [1, 13]),
   (1,
    [2, 12]),
   (1,
    [3, 11]),
   (1,
    [4, 10]),
   (1,
    [5, 9]),
   (1,
    [6, 8]),
   (mkRat (1) 2,
    [7, 7])]

set_option maxHeartbeats 1000000 in
-- Evaluate one Virasoro mode on the charged ground state.
set_option maxRecDepth 4096 in
theorem groundL14_check :
    neutralQuickOne omR (-13) 4 [(1, [])] = groundL14 := by
  decide +kernel

def groundL15 : RawPoly ℕ :=
  [(4,
    [0, 15]),
   (1,
    [1, 14]),
   (1,
    [2, 13]),
   (1,
    [3, 12]),
   (1,
    [4, 11]),
   (1,
    [5, 10]),
   (1,
    [6, 9]),
   (1,
    [7, 8])]

set_option maxHeartbeats 1000000 in
-- Evaluate one Virasoro mode on the charged ground state.
set_option maxRecDepth 4096 in
theorem groundL15_check :
    neutralQuickOne omR (-14) 4 [(1, [])] = groundL15 := by
  decide +kernel

def groundL16 : RawPoly ℕ :=
  [(4,
    [0, 16]),
   (1,
    [1, 15]),
   (1,
    [2, 14]),
   (1,
    [3, 13]),
   (1,
    [4, 12]),
   (1,
    [5, 11]),
   (1,
    [6, 10]),
   (1,
    [7, 9]),
   (mkRat (1) 2,
    [8, 8])]

set_option maxHeartbeats 1000000 in
-- Evaluate one Virasoro mode on the charged ground state.
set_option maxRecDepth 4096 in
theorem groundL16_check :
    neutralQuickOne omR (-15) 4 [(1, [])] = groundL16 := by
  decide +kernel

def groundL17 : RawPoly ℕ :=
  [(4,
    [0, 17]),
   (1,
    [1, 16]),
   (1,
    [2, 15]),
   (1,
    [3, 14]),
   (1,
    [4, 13]),
   (1,
    [5, 12]),
   (1,
    [6, 11]),
   (1,
    [7, 10]),
   (1,
    [8, 9])]

set_option maxHeartbeats 1000000 in
-- Evaluate one Virasoro mode on the charged ground state.
set_option maxRecDepth 4096 in
theorem groundL17_check :
    neutralQuickOne omR (-16) 4 [(1, [])] = groundL17 := by
  decide +kernel

def groundL18 : RawPoly ℕ :=
  [(4,
    [0, 18]),
   (1,
    [1, 17]),
   (1,
    [2, 16]),
   (1,
    [3, 15]),
   (1,
    [4, 14]),
   (1,
    [5, 13]),
   (1,
    [6, 12]),
   (1,
    [7, 11]),
   (1,
    [8, 10]),
   (mkRat (1) 2,
    [9, 9])]

set_option maxHeartbeats 1000000 in
-- Evaluate one Virasoro mode on the charged ground state.
set_option maxRecDepth 4096 in
theorem groundL18_check :
    neutralQuickOne omR (-17) 4 [(1, [])] = groundL18 := by
  decide +kernel

end VOA.Classification.COne.OrbOctaRC
