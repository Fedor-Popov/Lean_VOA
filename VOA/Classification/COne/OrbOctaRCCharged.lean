import VOA.Classification.COne.OrbOctaRCDual18Block32

/-! The two charged functionals annihilate every discarded Virasoro word. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
namespace VOA.Classification.COne.OrbOctaRC
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational HeisenbergN
  PlusC2Eval PlusUnitary PlusC2 OrbC2c OrbC2e OrbC2g OrbC2h LatMod OrbOctaR

def dual16Parts : List (RawPoly ℕ) :=
  [dual16Block0,
   dual16Block1,
   dual16Block2,
   dual16Block3,
   dual16Block4,
   dual16Block5,
   dual16Block6,
   dual16Block7,
   dual16Block8,
   dual16Block9,
   dual16Block10,
   dual16Block11,
   dual16Block12,
   dual16Block13,
   dual16Block14,
   dual16Block15,
   dual16Block16,
   dual16Block17,
   dual16Block18,
   dual16Block19]

def dual16PartsL1 : List (RawPoly ℕ) :=
  [dual16Block0L1,
   dual16Block1L1,
   dual16Block2L1,
   dual16Block3L1,
   dual16Block4L1,
   dual16Block5L1,
   dual16Block6L1,
   dual16Block7L1,
   dual16Block8L1,
   dual16Block9L1,
   dual16Block10L1,
   dual16Block11L1,
   dual16Block12L1,
   dual16Block13L1,
   dual16Block14L1,
   dual16Block15L1,
   dual16Block16L1,
   dual16Block17L1,
   dual16Block18L1,
   dual16Block19L1]

def dual16PartsL3 : List (RawPoly ℕ) :=
  [dual16Block0L3,
   dual16Block1L3,
   dual16Block2L3,
   dual16Block3L3,
   dual16Block4L3,
   dual16Block5L3,
   dual16Block6L3,
   dual16Block7L3,
   dual16Block8L3,
   dual16Block9L3,
   dual16Block10L3,
   dual16Block11L3,
   dual16Block12L3,
   dual16Block13L3,
   dual16Block14L3,
   dual16Block15L3,
   dual16Block16L3,
   dual16Block17L3,
   dual16Block18L3,
   dual16Block19L3]

noncomputable def dualState16 : LatModuleGen (latP 1) :=
  sector 4 (evRc (a0 1) (cα 1) dual16Parts.flatten)

set_option maxHeartbeats 4000000 in
-- Exact cancellation of the certified output blocks.
set_option maxRecDepth 8192 in
theorem dual16_L1_cancel : reduceTwo dual16PartsL1.flatten = [] := by
  decide +kernel

theorem dualState16_L1 : (V2m 1 le_rfl).L 1 dualState16 = 0 := by
  have hh : List.Forall₂ (fun P Q => neutralQuickOne omR 2 4 P = Q)
      dual16Parts dual16PartsL1 := by
    exact .cons dual16Block0L1_check <|
      .cons dual16Block1L1_check <|
      .cons dual16Block2L1_check <|
      .cons dual16Block3L1_check <|
      .cons dual16Block4L1_check <|
      .cons dual16Block5L1_check <|
      .cons dual16Block6L1_check <|
      .cons dual16Block7L1_check <|
      .cons dual16Block8L1_check <|
      .cons dual16Block9L1_check <|
      .cons dual16Block10L1_check <|
      .cons dual16Block11L1_check <|
      .cons dual16Block12L1_check <|
      .cons dual16Block13L1_check <|
      .cons dual16Block14L1_check <|
      .cons dual16Block15L1_check <|
      .cons dual16Block16L1_check <|
      .cons dual16Block17L1_check <|
      .cons dual16Block18L1_check <|
      .cons dual16Block19L1_check .nil
  have h := virOne_blocks 1 4 _ _ hh
  have hz : evRc (a0 1) (cα 1) dual16PartsL1.flatten = 0 := by
    rw [← evRc_reduceTwo_of_sq _ _ charge_square_two, dual16_L1_cancel, evRc_nil]
  rw [hz, map_zero] at h
  exact h

set_option maxHeartbeats 4000000 in
-- Exact cancellation of the certified output blocks.
set_option maxRecDepth 8192 in
theorem dual16_L3_cancel : reduceTwo dual16PartsL3.flatten = [] := by
  decide +kernel

theorem dualState16_L3 : (V2m 1 le_rfl).L 3 dualState16 = 0 := by
  have hh : List.Forall₂ (fun P Q => neutralQuickOne omR 4 4 P = Q)
      dual16Parts dual16PartsL3 := by
    exact .cons dual16Block0L3_check <|
      .cons dual16Block1L3_check <|
      .cons dual16Block2L3_check <|
      .cons dual16Block3L3_check <|
      .cons dual16Block4L3_check <|
      .cons dual16Block5L3_check <|
      .cons dual16Block6L3_check <|
      .cons dual16Block7L3_check <|
      .cons dual16Block8L3_check <|
      .cons dual16Block9L3_check <|
      .cons dual16Block10L3_check <|
      .cons dual16Block11L3_check <|
      .cons dual16Block12L3_check <|
      .cons dual16Block13L3_check <|
      .cons dual16Block14L3_check <|
      .cons dual16Block15L3_check <|
      .cons dual16Block16L3_check <|
      .cons dual16Block17L3_check <|
      .cons dual16Block18L3_check <|
      .cons dual16Block19L3_check .nil
  have h := virOne_blocks 3 4 _ _ hh
  have hz : evRc (a0 1) (cα 1) dual16PartsL3.flatten = 0 := by
    rw [← evRc_reduceTwo_of_sq _ _ charge_square_two, dual16_L3_cancel, evRc_nil]
  rw [hz, map_zero] at h
  exact h

theorem chargedProbe16_errors :
    virError W W.vacuum ⊔ virError W X ≤ (chargedProbe dualState16).ker :=
  chargedProbe_errors _ dualState16_L1 dualState16_L3

def dual18Parts : List (RawPoly ℕ) :=
  [dual18Block0,
   dual18Block1,
   dual18Block2,
   dual18Block3,
   dual18Block4,
   dual18Block5,
   dual18Block6,
   dual18Block7,
   dual18Block8,
   dual18Block9,
   dual18Block10,
   dual18Block11,
   dual18Block12,
   dual18Block13,
   dual18Block14,
   dual18Block15,
   dual18Block16,
   dual18Block17,
   dual18Block18,
   dual18Block19,
   dual18Block20,
   dual18Block21,
   dual18Block22,
   dual18Block23,
   dual18Block24,
   dual18Block25,
   dual18Block26,
   dual18Block27,
   dual18Block28,
   dual18Block29,
   dual18Block30,
   dual18Block31,
   dual18Block32]

def dual18PartsL1 : List (RawPoly ℕ) :=
  [dual18Block0L1,
   dual18Block1L1,
   dual18Block2L1,
   dual18Block3L1,
   dual18Block4L1,
   dual18Block5L1,
   dual18Block6L1,
   dual18Block7L1,
   dual18Block8L1,
   dual18Block9L1,
   dual18Block10L1,
   dual18Block11L1,
   dual18Block12L1,
   dual18Block13L1,
   dual18Block14L1,
   dual18Block15L1,
   dual18Block16L1,
   dual18Block17L1,
   dual18Block18L1,
   dual18Block19L1,
   dual18Block20L1,
   dual18Block21L1,
   dual18Block22L1,
   dual18Block23L1,
   dual18Block24L1,
   dual18Block25L1,
   dual18Block26L1,
   dual18Block27L1,
   dual18Block28L1,
   dual18Block29L1,
   dual18Block30L1,
   dual18Block31L1,
   dual18Block32L1]

def dual18PartsL3 : List (RawPoly ℕ) :=
  [dual18Block0L3,
   dual18Block1L3,
   dual18Block2L3,
   dual18Block3L3,
   dual18Block4L3,
   dual18Block5L3,
   dual18Block6L3,
   dual18Block7L3,
   dual18Block8L3,
   dual18Block9L3,
   dual18Block10L3,
   dual18Block11L3,
   dual18Block12L3,
   dual18Block13L3,
   dual18Block14L3,
   dual18Block15L3,
   dual18Block16L3,
   dual18Block17L3,
   dual18Block18L3,
   dual18Block19L3,
   dual18Block20L3,
   dual18Block21L3,
   dual18Block22L3,
   dual18Block23L3,
   dual18Block24L3,
   dual18Block25L3,
   dual18Block26L3,
   dual18Block27L3,
   dual18Block28L3,
   dual18Block29L3,
   dual18Block30L3,
   dual18Block31L3,
   dual18Block32L3]

noncomputable def dualState18 : LatModuleGen (latP 1) :=
  sector 4 (evRc (a0 1) (cα 1) dual18Parts.flatten)

set_option maxHeartbeats 4000000 in
-- Exact cancellation of the certified output blocks.
set_option maxRecDepth 8192 in
theorem dual18_L1_cancel : reduceTwo dual18PartsL1.flatten = [] := by
  decide +kernel

theorem dualState18_L1 : (V2m 1 le_rfl).L 1 dualState18 = 0 := by
  have hh : List.Forall₂ (fun P Q => neutralQuickOne omR 2 4 P = Q)
      dual18Parts dual18PartsL1 := by
    exact .cons dual18Block0L1_check <|
      .cons dual18Block1L1_check <|
      .cons dual18Block2L1_check <|
      .cons dual18Block3L1_check <|
      .cons dual18Block4L1_check <|
      .cons dual18Block5L1_check <|
      .cons dual18Block6L1_check <|
      .cons dual18Block7L1_check <|
      .cons dual18Block8L1_check <|
      .cons dual18Block9L1_check <|
      .cons dual18Block10L1_check <|
      .cons dual18Block11L1_check <|
      .cons dual18Block12L1_check <|
      .cons dual18Block13L1_check <|
      .cons dual18Block14L1_check <|
      .cons dual18Block15L1_check <|
      .cons dual18Block16L1_check <|
      .cons dual18Block17L1_check <|
      .cons dual18Block18L1_check <|
      .cons dual18Block19L1_check <|
      .cons dual18Block20L1_check <|
      .cons dual18Block21L1_check <|
      .cons dual18Block22L1_check <|
      .cons dual18Block23L1_check <|
      .cons dual18Block24L1_check <|
      .cons dual18Block25L1_check <|
      .cons dual18Block26L1_check <|
      .cons dual18Block27L1_check <|
      .cons dual18Block28L1_check <|
      .cons dual18Block29L1_check <|
      .cons dual18Block30L1_check <|
      .cons dual18Block31L1_check <|
      .cons dual18Block32L1_check .nil
  have h := virOne_blocks 1 4 _ _ hh
  have hz : evRc (a0 1) (cα 1) dual18PartsL1.flatten = 0 := by
    rw [← evRc_reduceTwo_of_sq _ _ charge_square_two, dual18_L1_cancel, evRc_nil]
  rw [hz, map_zero] at h
  exact h

set_option maxHeartbeats 4000000 in
-- Exact cancellation of the certified output blocks.
set_option maxRecDepth 8192 in
theorem dual18_L3_cancel : reduceTwo dual18PartsL3.flatten = [] := by
  decide +kernel

theorem dualState18_L3 : (V2m 1 le_rfl).L 3 dualState18 = 0 := by
  have hh : List.Forall₂ (fun P Q => neutralQuickOne omR 4 4 P = Q)
      dual18Parts dual18PartsL3 := by
    exact .cons dual18Block0L3_check <|
      .cons dual18Block1L3_check <|
      .cons dual18Block2L3_check <|
      .cons dual18Block3L3_check <|
      .cons dual18Block4L3_check <|
      .cons dual18Block5L3_check <|
      .cons dual18Block6L3_check <|
      .cons dual18Block7L3_check <|
      .cons dual18Block8L3_check <|
      .cons dual18Block9L3_check <|
      .cons dual18Block10L3_check <|
      .cons dual18Block11L3_check <|
      .cons dual18Block12L3_check <|
      .cons dual18Block13L3_check <|
      .cons dual18Block14L3_check <|
      .cons dual18Block15L3_check <|
      .cons dual18Block16L3_check <|
      .cons dual18Block17L3_check <|
      .cons dual18Block18L3_check <|
      .cons dual18Block19L3_check <|
      .cons dual18Block20L3_check <|
      .cons dual18Block21L3_check <|
      .cons dual18Block22L3_check <|
      .cons dual18Block23L3_check <|
      .cons dual18Block24L3_check <|
      .cons dual18Block25L3_check <|
      .cons dual18Block26L3_check <|
      .cons dual18Block27L3_check <|
      .cons dual18Block28L3_check <|
      .cons dual18Block29L3_check <|
      .cons dual18Block30L3_check <|
      .cons dual18Block31L3_check <|
      .cons dual18Block32L3_check .nil
  have h := virOne_blocks 3 4 _ _ hh
  have hz : evRc (a0 1) (cα 1) dual18PartsL3.flatten = 0 := by
    rw [← evRc_reduceTwo_of_sq _ _ charge_square_two, dual18_L3_cancel, evRc_nil]
  rw [hz, map_zero] at h
  exact h

theorem chargedProbe18_errors :
    virError W W.vacuum ⊔ virError W X ≤ (chargedProbe dualState18).ker :=
  chargedProbe_errors _ dualState18_L1 dualState18_L3

end VOA.Classification.COne.OrbOctaRC
