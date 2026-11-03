import VOA.DeligneAudit.DeligneSectorD4Table

/-!
# Small typed D₄ contact-parabolic table checks

The radical has eight degree-one roots and its central highest-root
direction. The three outer simple negative roots form the Levi part.
The checks below are split into nine small integer rows.
-/

namespace VOA.DeligneAudit.D4FusionContact

open VOA.DeligneAudit.DeligneSector.Sparse
open VOA.DeligneAudit.DeligneSector.D4 (br)

abbrev contactF : Fin 28 → Fin 28 → Fin 28 → ℂ := fC 28 br

def active (c : Fin 28) : Prop := c = 18 ∨ 20 ≤ c.val

instance : DecidablePred active := fun c => by unfold active; infer_instance

def radIndex : Fin 9 → Fin 28 := ![18, 20, 21, 22, 23, 24, 25, 26, 27]

def leviIndex : Fin 3 → Fin 28 := ![16, 17, 19]

def leviCartan : Fin 3 → Fin 28 := ![3, 2, 0]

def contactCoeff (i j : Fin 9) : ℤ :=
  if i.val < 4 ∧ j.val = 7 - i.val then 1
  else if j.val < 4 ∧ i.val = 7 - j.val then -1 else 0

private theorem contact_row0 : ∀ j : Fin 9, ∀ c : Fin 28,
    fZ br (radIndex 0) (radIndex j) c = if c = 27 then contactCoeff 0 j else 0 := by
  decide +kernel
private theorem contact_row1 : ∀ j : Fin 9, ∀ c : Fin 28,
    fZ br (radIndex 1) (radIndex j) c = if c = 27 then contactCoeff 1 j else 0 := by
  decide +kernel
private theorem contact_row2 : ∀ j : Fin 9, ∀ c : Fin 28,
    fZ br (radIndex 2) (radIndex j) c = if c = 27 then contactCoeff 2 j else 0 := by
  decide +kernel
private theorem contact_row3 : ∀ j : Fin 9, ∀ c : Fin 28,
    fZ br (radIndex 3) (radIndex j) c = if c = 27 then contactCoeff 3 j else 0 := by
  decide +kernel
private theorem contact_row4 : ∀ j : Fin 9, ∀ c : Fin 28,
    fZ br (radIndex 4) (radIndex j) c = if c = 27 then contactCoeff 4 j else 0 := by
  decide +kernel
private theorem contact_row5 : ∀ j : Fin 9, ∀ c : Fin 28,
    fZ br (radIndex 5) (radIndex j) c = if c = 27 then contactCoeff 5 j else 0 := by
  decide +kernel
private theorem contact_row6 : ∀ j : Fin 9, ∀ c : Fin 28,
    fZ br (radIndex 6) (radIndex j) c = if c = 27 then contactCoeff 6 j else 0 := by
  decide +kernel
private theorem contact_row7 : ∀ j : Fin 9, ∀ c : Fin 28,
    fZ br (radIndex 7) (radIndex j) c = if c = 27 then contactCoeff 7 j else 0 := by
  decide +kernel
private theorem contact_row8 : ∀ j : Fin 9, ∀ c : Fin 28,
    fZ br (radIndex 8) (radIndex j) c = if c = 27 then contactCoeff 8 j else 0 := by
  decide +kernel

theorem contact_tableZ (i j : Fin 9) (c : Fin 28) :
    fZ br (radIndex i) (radIndex j) c = if c = 27 then contactCoeff i j else 0 := by
  fin_cases i
  · exact contact_row0 j c
  · exact contact_row1 j c
  · exact contact_row2 j c
  · exact contact_row3 j c
  · exact contact_row4 j c
  · exact contact_row5 j c
  · exact contact_row6 j c
  · exact contact_row7 j c
  · exact contact_row8 j c

theorem contact_table (i j : Fin 9) (c : Fin 28) :
    contactF (radIndex i) (radIndex j) c =
      if c = 27 then (contactCoeff i j : ℂ) else 0 := by
  change (fZ br (radIndex i) (radIndex j) c : ℂ) = _
  rw [contact_tableZ]
  split_ifs <;> simp

theorem levi_cartan_tableZ : ∀ i : Fin 3, ∀ c : Fin 28,
    fZ br (leviCartan i) (leviIndex i) c = if c = leviIndex i then -2 else 0 := by
  decide +kernel

theorem levi_cartan_table (i : Fin 3) (c : Fin 28) :
    contactF (leviCartan i) (leviIndex i) c = if c = leviIndex i then -2 else 0 := by
  change (fZ br (leviCartan i) (leviIndex i) c : ℂ) = _
  rw [levi_cartan_tableZ]
  split_ifs <;> norm_num

theorem active_iff_index : ∀ c : Fin 28, active c ↔ ∃ i : Fin 9, radIndex i = c := by
  decide +kernel

theorem negative_nonactive_iff : ∀ c : Fin 28,
    (16 ≤ c.val ∧ ¬ active c) ↔ ∃ i : Fin 3, leviIndex i = c := by
  decide +kernel

theorem leviCartan_lt_four (i : Fin 3) : (leviCartan i).val < 4 := by
  fin_cases i <;> decide

end VOA.DeligneAudit.D4FusionContact

#print axioms VOA.DeligneAudit.D4FusionContact.contact_table
#print axioms VOA.DeligneAudit.D4FusionContact.levi_cartan_table
