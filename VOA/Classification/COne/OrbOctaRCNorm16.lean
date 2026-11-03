import VOA.Classification.COne.OrbOctaRCDescCache04
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
theorem norm16_block0 : pairRaw vd695Part0 dual16Parts.flatten =
    (mkRat (319196617453568) 14244766981570125, 0) := by
  decide +kernel

set_option maxHeartbeats 3000000 in
-- Pair one block with the certified charged dual polynomial.
set_option maxRecDepth 8192 in
theorem norm16_block1 : pairRaw vd695Part1 dual16Parts.flatten =
    (mkRat (19371983015936) 135664447443525, 0) := by
  decide +kernel

set_option maxHeartbeats 3000000 in
-- Pair one block with the certified charged dual polynomial.
set_option maxRecDepth 8192 in
theorem norm16_block2 : pairRaw vd695Part2 dual16Parts.flatten =
    (mkRat (225004249081856) 678322237217625, 0) := by
  decide +kernel

set_option maxHeartbeats 3000000 in
-- Pair one block with the certified charged dual polynomial.
set_option maxRecDepth 8192 in
theorem norm16_block3 : pairRaw vd695Part3 dual16Parts.flatten =
    (mkRat (-14082912462848) 26428139112375, 0) := by
  decide +kernel

set_option maxHeartbeats 3000000 in
-- Pair one block with the certified charged dual polynomial.
set_option maxRecDepth 8192 in
theorem norm16_block4 : pairRaw vd695Part4 dual16Parts.flatten =
    (mkRat (13608547117699) 258995763301275, 0) := by
  decide +kernel

set_option maxHeartbeats 3000000 in
-- Pair one block with the certified charged dual polynomial.
set_option maxRecDepth 8192 in
theorem norm16_block5 : pairRaw vd695Part5 dual16Parts.flatten =
    (mkRat (-15257186328856) 135664447443525, 0) := by
  decide +kernel

set_option maxHeartbeats 3000000 in
-- Pair one block with the certified charged dual polynomial.
set_option maxRecDepth 8192 in
theorem norm16_block6 : pairRaw vd695Part6 dual16Parts.flatten =
    (mkRat (-167680499355088) 321310533418875, 0) := by
  decide +kernel

set_option maxHeartbeats 3000000 in
-- Pair one block with the certified charged dual polynomial.
set_option maxRecDepth 8192 in
theorem norm16_block7 : pairRaw vd695Part7 dual16Parts.flatten =
    (mkRat (-6358534672532984) 42734300944710375, 0) := by
  decide +kernel

set_option maxHeartbeats 3000000 in
-- Pair one block with the certified charged dual polynomial.
set_option maxRecDepth 8192 in
theorem norm16_block8 : pairRaw vd695Part8 dual16Parts.flatten =
    (mkRat (4654814151194014) 2513782408512375, 0) := by
  decide +kernel

set_option maxHeartbeats 3000000 in
-- Pair one block with the certified charged dual polynomial.
set_option maxRecDepth 8192 in
theorem norm16_block9 : pairRaw vd695Part9 dual16Parts.flatten =
    (mkRat (-3639857861771126) 42734300944710375, 0) := by
  decide +kernel

theorem norm16_raw : pairRaw vd695 dual16Parts.flatten = (1, 0) := by
  simp only [vd695, List.flatten_cons, List.flatten_nil, pairRaw_append, pairRaw_nil,
    norm16_block0,
    norm16_block1,
    norm16_block2,
    norm16_block3,
    norm16_block4,
    norm16_block5,
    norm16_block6,
    norm16_block7,
    norm16_block8,
    norm16_block9]
  norm_num

theorem charged_norm16 :
    (v2mVirUnitary 1 le_rfl).form
      ((((V2m 1 le_rfl).L (-2)) ^ 8) (latChargeGen (latP 1) (4 : ℤ)))
      dualState16 = 1 := by
  have h : (((V2m 1 le_rfl).L (-2)) ^ 8) (latChargeGen (latP 1) (4 : ℤ)) =
      sector 4 (evRc (a0 1) (cα 1) vd695) :=
    (vd695_sound.trans (virDesc_replicate (V2m 1 le_rfl) 2 8 _)).symm
  rw [h, dualState16, sector_pairRaw, norm16_raw]
  norm_num [pairValue]

end VOA.Classification.COne.OrbOctaRC
