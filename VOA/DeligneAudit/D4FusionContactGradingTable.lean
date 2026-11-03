import VOA.DeligneAudit.D4FusionContactTable

/-!
# Typed contact-grading support for the D₄ parabolic PBW filtration

The zero contact-grade subalgebra preserves the negative radical.
Positive contact roots send its center to the eight noncentral roots
and send those eight roots into the zero-grade subalgebra.
-/

namespace VOA.DeligneAudit.D4FusionContact

open VOA.DeligneAudit.DeligneSector.Sparse
open VOA.DeligneAudit.DeligneSector.D4 (br)

def zeroIndex : Fin 10 → Fin 28 := ![0, 1, 2, 3, 4, 5, 7, 16, 17, 19]

def zeroGrade (c : Fin 28) : Prop :=
  c.val < 4 ∨ c = 4 ∨ c = 5 ∨ c = 7 ∨ c = 16 ∨ c = 17 ∨ c = 19

instance : DecidablePred zeroGrade := fun c => by unfold zeroGrade; infer_instance

def positiveIndex : Fin 8 → Fin 28 := ![14, 13, 12, 11, 10, 9, 8, 6]

def positiveSign : Fin 8 → ℤ := ![1, 1, 1, 1, -1, -1, -1, 1]

theorem zeroGrade_iff_index : ∀ c : Fin 28,
    zeroGrade c ↔ ∃ i : Fin 10, zeroIndex i = c := by
  decide +kernel

theorem zeroGrade_nonactive : ∀ c : Fin 28, zeroGrade c → ¬ active c := by
  decide +kernel

theorem positiveIndex_range (i : Fin 8) :
    4 ≤ (positiveIndex i).val ∧ (positiveIndex i).val < 16 := by
  fin_cases i <;> decide

theorem positive_centerZ : ∀ i : Fin 8, ∀ c : Fin 28,
    positiveSign i * fZ br (positiveIndex i) 27 c =
      if c = radIndex i.castSucc then 1 else 0 := by
  decide +kernel

private theorem zero_rad_row0 : ∀ j : Fin 9, ∀ c : Fin 28,
    ¬ active c → fZ br (zeroIndex 0) (radIndex j) c = 0 := by
  decide +kernel
private theorem zero_rad_row1 : ∀ j : Fin 9, ∀ c : Fin 28,
    ¬ active c → fZ br (zeroIndex 1) (radIndex j) c = 0 := by
  decide +kernel
private theorem zero_rad_row2 : ∀ j : Fin 9, ∀ c : Fin 28,
    ¬ active c → fZ br (zeroIndex 2) (radIndex j) c = 0 := by
  decide +kernel
private theorem zero_rad_row3 : ∀ j : Fin 9, ∀ c : Fin 28,
    ¬ active c → fZ br (zeroIndex 3) (radIndex j) c = 0 := by
  decide +kernel
private theorem zero_rad_row4 : ∀ j : Fin 9, ∀ c : Fin 28,
    ¬ active c → fZ br (zeroIndex 4) (radIndex j) c = 0 := by
  decide +kernel
private theorem zero_rad_row5 : ∀ j : Fin 9, ∀ c : Fin 28,
    ¬ active c → fZ br (zeroIndex 5) (radIndex j) c = 0 := by
  decide +kernel
private theorem zero_rad_row6 : ∀ j : Fin 9, ∀ c : Fin 28,
    ¬ active c → fZ br (zeroIndex 6) (radIndex j) c = 0 := by
  decide +kernel
private theorem zero_rad_row7 : ∀ j : Fin 9, ∀ c : Fin 28,
    ¬ active c → fZ br (zeroIndex 7) (radIndex j) c = 0 := by
  decide +kernel
private theorem zero_rad_row8 : ∀ j : Fin 9, ∀ c : Fin 28,
    ¬ active c → fZ br (zeroIndex 8) (radIndex j) c = 0 := by
  decide +kernel
private theorem zero_rad_row9 : ∀ j : Fin 9, ∀ c : Fin 28,
    ¬ active c → fZ br (zeroIndex 9) (radIndex j) c = 0 := by
  decide +kernel

theorem zero_rad_tableZ (i : Fin 10) (j : Fin 9) (c : Fin 28) (hc : ¬ active c) :
    fZ br (zeroIndex i) (radIndex j) c = 0 := by
  fin_cases i
  · exact zero_rad_row0 j c hc
  · exact zero_rad_row1 j c hc
  · exact zero_rad_row2 j c hc
  · exact zero_rad_row3 j c hc
  · exact zero_rad_row4 j c hc
  · exact zero_rad_row5 j c hc
  · exact zero_rad_row6 j c hc
  · exact zero_rad_row7 j c hc
  · exact zero_rad_row8 j c hc
  · exact zero_rad_row9 j c hc

private theorem positive_rad_row0 : ∀ j : Fin 8, ∀ c : Fin 28,
    ¬ zeroGrade c → fZ br (positiveIndex 0) (radIndex j.castSucc) c = 0 := by
  decide +kernel
private theorem positive_rad_row1 : ∀ j : Fin 8, ∀ c : Fin 28,
    ¬ zeroGrade c → fZ br (positiveIndex 1) (radIndex j.castSucc) c = 0 := by
  decide +kernel
private theorem positive_rad_row2 : ∀ j : Fin 8, ∀ c : Fin 28,
    ¬ zeroGrade c → fZ br (positiveIndex 2) (radIndex j.castSucc) c = 0 := by
  decide +kernel
private theorem positive_rad_row3 : ∀ j : Fin 8, ∀ c : Fin 28,
    ¬ zeroGrade c → fZ br (positiveIndex 3) (radIndex j.castSucc) c = 0 := by
  decide +kernel
private theorem positive_rad_row4 : ∀ j : Fin 8, ∀ c : Fin 28,
    ¬ zeroGrade c → fZ br (positiveIndex 4) (radIndex j.castSucc) c = 0 := by
  decide +kernel
private theorem positive_rad_row5 : ∀ j : Fin 8, ∀ c : Fin 28,
    ¬ zeroGrade c → fZ br (positiveIndex 5) (radIndex j.castSucc) c = 0 := by
  decide +kernel
private theorem positive_rad_row6 : ∀ j : Fin 8, ∀ c : Fin 28,
    ¬ zeroGrade c → fZ br (positiveIndex 6) (radIndex j.castSucc) c = 0 := by
  decide +kernel
private theorem positive_rad_row7 : ∀ j : Fin 8, ∀ c : Fin 28,
    ¬ zeroGrade c → fZ br (positiveIndex 7) (radIndex j.castSucc) c = 0 := by
  decide +kernel

theorem positive_rad_tableZ (i j : Fin 8) (c : Fin 28) (hc : ¬ zeroGrade c) :
    fZ br (positiveIndex i) (radIndex j.castSucc) c = 0 := by
  fin_cases i
  · exact positive_rad_row0 j c hc
  · exact positive_rad_row1 j c hc
  · exact positive_rad_row2 j c hc
  · exact positive_rad_row3 j c hc
  · exact positive_rad_row4 j c hc
  · exact positive_rad_row5 j c hc
  · exact positive_rad_row6 j c hc
  · exact positive_rad_row7 j c hc

theorem zero_rad_table (i : Fin 10) (j : Fin 9) (c : Fin 28) (hc : ¬ active c) :
    contactF (zeroIndex i) (radIndex j) c = 0 := by
  change (fZ br (zeroIndex i) (radIndex j) c : ℂ) = 0
  rw [zero_rad_tableZ i j c hc, Int.cast_zero]

theorem positive_rad_table (i j : Fin 8) (c : Fin 28) (hc : ¬ zeroGrade c) :
    contactF (positiveIndex i) (radIndex j.castSucc) c = 0 := by
  change (fZ br (positiveIndex i) (radIndex j.castSucc) c : ℂ) = 0
  rw [positive_rad_tableZ i j c hc, Int.cast_zero]

theorem positive_center (i : Fin 8) (c : Fin 28) :
    (positiveSign i : ℂ) * contactF (positiveIndex i) 27 c =
      if c = radIndex i.castSucc then 1 else 0 := by
  change (positiveSign i : ℂ) * (fZ br (positiveIndex i) 27 c : ℂ) = _
  rw [← Int.cast_mul, positive_centerZ]
  split_ifs <;> norm_num

end VOA.DeligneAudit.D4FusionContact

#print axioms VOA.DeligneAudit.D4FusionContact.zero_rad_table
#print axioms VOA.DeligneAudit.D4FusionContact.positive_rad_table
#print axioms VOA.DeligneAudit.D4FusionContact.positive_center

