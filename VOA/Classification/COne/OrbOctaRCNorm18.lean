import VOA.Classification.COne.OrbOctaRCDescCache13
import VOA.Classification.COne.OrbOctaRCCharged
import VOA.Classification.COne.OrbOctaRCPair

/-! Normalization of a charged dual vector, checked in oscillator blocks. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
namespace VOA.Classification.COne.OrbOctaRC
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational HeisenbergN
  PlusC2Eval PlusUnitary PlusC2 OrbC2e LatMod OrbSpan

set_option maxHeartbeats 3000000 in
-- Pair one block with the certified charged dual polynomial.
set_option maxRecDepth 8192 in
theorem norm18_block0 : pairRaw vd1284Part0 dual18Parts.flatten =
    (mkRat (-1344823363046336) 156692436797271375, 0) := by
  decide +kernel

set_option maxHeartbeats 3000000 in
-- Pair one block with the certified charged dual polynomial.
set_option maxRecDepth 8192 in
theorem norm18_block1 : pairRaw vd1284Part1 dual18Parts.flatten =
    (mkRat (-2180279166190592) 111923169140908125, 0) := by
  decide +kernel

set_option maxHeartbeats 3000000 in
-- Pair one block with the certified charged dual polynomial.
set_option maxRecDepth 8192 in
theorem norm18_block2 : pairRaw vd1284Part2 dual18Parts.flatten =
    (mkRat (-14967398030336) 115503786523125, 0) := by
  decide +kernel

set_option maxHeartbeats 3000000 in
-- Pair one block with the certified charged dual polynomial.
set_option maxRecDepth 8192 in
theorem norm18_block3 : pairRaw vd1284Part3 dual18Parts.flatten =
    (mkRat (-81410604719366144) 111923169140908125, 0) := by
  decide +kernel

set_option maxHeartbeats 3000000 in
-- Pair one block with the certified charged dual polynomial.
set_option maxRecDepth 8192 in
theorem norm18_block4 : pairRaw vd1284Part4 dual18Parts.flatten =
    (mkRat (-117796910408192) 482130574760835, 0) := by
  decide +kernel

set_option maxHeartbeats 3000000 in
-- Pair one block with the certified charged dual polynomial.
set_option maxRecDepth 8192 in
theorem norm18_block5 : pairRaw vd1284Part5 dual18Parts.flatten =
    (mkRat (-6228585135985792) 261154061328785625, 0) := by
  decide +kernel

set_option maxHeartbeats 3000000 in
-- Pair one block with the certified charged dual polynomial.
set_option maxRecDepth 8192 in
theorem norm18_block6 : pairRaw vd1284Part6 dual18Parts.flatten =
    (mkRat (52133591968419968) 37307723046969375, 0) := by
  decide +kernel

set_option maxHeartbeats 3000000 in
-- Pair one block with the certified charged dual polynomial.
set_option maxRecDepth 8192 in
theorem norm18_block7 : pairRaw vd1284Part7 dual18Parts.flatten =
    (mkRat (137075788117344697) 2350386551959070625, 0) := by
  decide +kernel

set_option maxHeartbeats 3000000 in
-- Pair one block with the certified charged dual polynomial.
set_option maxRecDepth 8192 in
theorem norm18_block8 : pairRaw vd1284Part8 dual18Parts.flatten =
    (mkRat (2306618313443432) 783462183986356875, 0) := by
  decide +kernel

set_option maxHeartbeats 3000000 in
-- Pair one block with the certified charged dual polynomial.
set_option maxRecDepth 8192 in
theorem norm18_block9 : pairRaw vd1284Part9 dual18Parts.flatten =
    (mkRat (19056404731808) 506439679370625, 0) := by
  decide +kernel

set_option maxHeartbeats 3000000 in
-- Pair one block with the certified charged dual polynomial.
set_option maxRecDepth 8192 in
theorem norm18_block10 : pairRaw vd1284Part10 dual18Parts.flatten =
    (mkRat (130196773388659184) 783462183986356875, 0) := by
  decide +kernel

set_option maxHeartbeats 3000000 in
-- Pair one block with the certified charged dual polynomial.
set_option maxRecDepth 8192 in
theorem norm18_block11 : pairRaw vd1284Part11 dual18Parts.flatten =
    (mkRat (210391065262187426) 783462183986356875, 0) := by
  decide +kernel

set_option maxHeartbeats 3000000 in
-- Pair one block with the certified charged dual polynomial.
set_option maxRecDepth 8192 in
theorem norm18_block12 : pairRaw vd1284Part12 dual18Parts.flatten =
    (mkRat (24493076588195206) 71223834907850625, 0) := by
  decide +kernel

set_option maxHeartbeats 3000000 in
-- Pair one block with the certified charged dual polynomial.
set_option maxRecDepth 8192 in
theorem norm18_block13 : pairRaw vd1284Part13 dual18Parts.flatten =
    (mkRat (44268981333328) 10446162453151425, 0) := by
  decide +kernel

set_option maxHeartbeats 3000000 in
-- Pair one block with the certified charged dual polynomial.
set_option maxRecDepth 8192 in
theorem norm18_block14 : pairRaw vd1284Part14 dual18Parts.flatten =
    (mkRat (-125470182054857524) 2350386551959070625, 0) := by
  decide +kernel

set_option maxHeartbeats 3000000 in
-- Pair one block with the certified charged dual polynomial.
set_option maxRecDepth 8192 in
theorem norm18_block15 : pairRaw vd1284Part15 dual18Parts.flatten =
    (mkRat (-18948664999634144) 261154061328785625, 0) := by
  decide +kernel

set_option maxHeartbeats 3000000 in
-- Pair one block with the certified charged dual polynomial.
set_option maxRecDepth 8192 in
theorem norm18_block16 : pairRaw vd1284Part16 dual18Parts.flatten =
    (mkRat (3803032) 553732438545, 0) := by
  decide +kernel

theorem norm18_raw : pairRaw vd1284 dual18Parts.flatten = (1, 0) := by
  simp only [vd1284, List.flatten_cons, List.flatten_nil, pairRaw_append, pairRaw_nil,
    norm18_block0,
    norm18_block1,
    norm18_block2,
    norm18_block3,
    norm18_block4,
    norm18_block5,
    norm18_block6,
    norm18_block7,
    norm18_block8,
    norm18_block9,
    norm18_block10,
    norm18_block11,
    norm18_block12,
    norm18_block13,
    norm18_block14,
    norm18_block15,
    norm18_block16]
  norm_num

theorem charged_norm18 :
    (v2mVirUnitary 1 le_rfl).form
      ((((V2m 1 le_rfl).L (-2)) ^ 9) (latChargeGen (latP 1) (4 : ℤ)))
      dualState18 = 1 := by
  have h : (((V2m 1 le_rfl).L (-2)) ^ 9) (latChargeGen (latP 1) (4 : ℤ)) =
      sector 4 (evRc (a0 1) (cα 1) vd1284) :=
    (vd1284_sound.trans (virDesc_replicate (V2m 1 le_rfl) 2 9 _)).symm
  rw [h, dualState18, sector_pairRaw, norm18_raw]
  norm_num [pairValue]

end VOA.Classification.COne.OrbOctaRC
