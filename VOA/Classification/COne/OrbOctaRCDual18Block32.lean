import VOA.Classification.COne.OrbOctaRCDual18Block28

/-! Exact positive-mode checks for charged dual-state blocks. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
namespace VOA.Classification.COne.OrbOctaRC
open VOA VOA.SparseRational HeisenbergN PlusC2Eval PlusUnitary PlusC2 OrbC2g OrbC2h

def dual18Block32 : RawPoly ℕ :=
  [(-8 / 94040957626875,
    [0, 18])]

def dual18Block32L1 : RawPoly ℕ :=
  [(-16 / 10448995291875,
    [0, 17])]

set_option maxHeartbeats 2000000 in
-- Exact rational evaluation of a twelve-monomial block.
set_option maxRecDepth 4096 in
theorem dual18Block32L1_check :
    neutralQuickOne omR 2 4 dual18Block32 = dual18Block32L1 := by
  decide +kernel

def dual18Block32L3 : RawPoly ℕ :=
  [(-16 / 10448995291875,
    [0, 15])]

set_option maxHeartbeats 2000000 in
-- Exact rational evaluation of a twelve-monomial block.
set_option maxRecDepth 4096 in
theorem dual18Block32L3_check :
    neutralQuickOne omR 4 4 dual18Block32 = dual18Block32L3 := by
  decide +kernel

end VOA.Classification.COne.OrbOctaRC
