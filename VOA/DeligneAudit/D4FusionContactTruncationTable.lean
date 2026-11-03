import VOA.DeligneAudit.D4FusionContactTable

/-! # Small Cartan witnesses for all negative D₄ roots -/

namespace VOA.DeligneAudit.D4FusionContact

open VOA.DeligneAudit.DeligneSector.Sparse
open VOA.DeligneAudit.DeligneSector.D4 (br)

def negativeIndex : Fin 12 → Fin 28 :=
  ![16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]

def negativeCartan : Fin 12 → Fin 28 := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]

def negativeWeight : Fin 12 → ℤ := ![1, 1, 1, -2, 1, 1, -1, 1, -1, -1, -1, -1]

private theorem negative_cartan_row0 : ∀ c : Fin 28,
    fZ br (negativeCartan 0) (negativeIndex 0) c =
      if c = negativeIndex 0 then negativeWeight 0 else 0 := by
  decide +kernel
private theorem negative_cartan_row1 : ∀ c : Fin 28,
    fZ br (negativeCartan 1) (negativeIndex 1) c =
      if c = negativeIndex 1 then negativeWeight 1 else 0 := by
  decide +kernel
private theorem negative_cartan_row2 : ∀ c : Fin 28,
    fZ br (negativeCartan 2) (negativeIndex 2) c =
      if c = negativeIndex 2 then negativeWeight 2 else 0 := by
  decide +kernel
private theorem negative_cartan_row3 : ∀ c : Fin 28,
    fZ br (negativeCartan 3) (negativeIndex 3) c =
      if c = negativeIndex 3 then negativeWeight 3 else 0 := by
  decide +kernel
private theorem negative_cartan_row4 : ∀ c : Fin 28,
    fZ br (negativeCartan 4) (negativeIndex 4) c =
      if c = negativeIndex 4 then negativeWeight 4 else 0 := by
  decide +kernel
private theorem negative_cartan_row5 : ∀ c : Fin 28,
    fZ br (negativeCartan 5) (negativeIndex 5) c =
      if c = negativeIndex 5 then negativeWeight 5 else 0 := by
  decide +kernel
private theorem negative_cartan_row6 : ∀ c : Fin 28,
    fZ br (negativeCartan 6) (negativeIndex 6) c =
      if c = negativeIndex 6 then negativeWeight 6 else 0 := by
  decide +kernel
private theorem negative_cartan_row7 : ∀ c : Fin 28,
    fZ br (negativeCartan 7) (negativeIndex 7) c =
      if c = negativeIndex 7 then negativeWeight 7 else 0 := by
  decide +kernel
private theorem negative_cartan_row8 : ∀ c : Fin 28,
    fZ br (negativeCartan 8) (negativeIndex 8) c =
      if c = negativeIndex 8 then negativeWeight 8 else 0 := by
  decide +kernel
private theorem negative_cartan_row9 : ∀ c : Fin 28,
    fZ br (negativeCartan 9) (negativeIndex 9) c =
      if c = negativeIndex 9 then negativeWeight 9 else 0 := by
  decide +kernel
private theorem negative_cartan_row10 : ∀ c : Fin 28,
    fZ br (negativeCartan 10) (negativeIndex 10) c =
      if c = negativeIndex 10 then negativeWeight 10 else 0 := by
  decide +kernel
private theorem negative_cartan_row11 : ∀ c : Fin 28,
    fZ br (negativeCartan 11) (negativeIndex 11) c =
      if c = negativeIndex 11 then negativeWeight 11 else 0 := by
  decide +kernel

theorem negative_cartan_tableZ (i : Fin 12) (c : Fin 28) :
    fZ br (negativeCartan i) (negativeIndex i) c =
      if c = negativeIndex i then negativeWeight i else 0 := by
  fin_cases i
  · exact negative_cartan_row0 c
  · exact negative_cartan_row1 c
  · exact negative_cartan_row2 c
  · exact negative_cartan_row3 c
  · exact negative_cartan_row4 c
  · exact negative_cartan_row5 c
  · exact negative_cartan_row6 c
  · exact negative_cartan_row7 c
  · exact negative_cartan_row8 c
  · exact negative_cartan_row9 c
  · exact negative_cartan_row10 c
  · exact negative_cartan_row11 c

theorem negative_cartan_table (i : Fin 12) (c : Fin 28) :
    contactF (negativeCartan i) (negativeIndex i) c =
      if c = negativeIndex i then (negativeWeight i : ℂ) else 0 := by
  change (fZ br (negativeCartan i) (negativeIndex i) c : ℂ) = _
  rw [negative_cartan_tableZ]
  split_ifs <;> simp

theorem negativeWeight_ne_zero (i : Fin 12) : (negativeWeight i : ℂ) ≠ 0 := by
  fin_cases i <;> norm_num [negativeWeight]

theorem negativeCartan_lt_four (i : Fin 12) : (negativeCartan i).val < 4 := by
  fin_cases i <;> decide

theorem negativeIndex_range (i : Fin 12) : 16 ≤ (negativeIndex i).val := by
  fin_cases i <;> decide

theorem negativeIndex_covers : ∀ c : Fin 28, 16 ≤ c.val → ∃ i, negativeIndex i = c := by
  decide +kernel

end VOA.DeligneAudit.D4FusionContact

#print axioms VOA.DeligneAudit.D4FusionContact.negative_cartan_table
