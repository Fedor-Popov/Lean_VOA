import VOA.DeligneAudit.D4LeviCurrent

/-! Finite support checks for the node-one parabolic decomposition of D4. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.DeligneSector.Sparse

/-- The six positive roots containing the vector node. -/
def positiveColour : Fin 6 → Fin 28
  | 0 => 7
  | 1 => 10
  | 2 => 12
  | 3 => 13
  | 4 => 14
  | 5 => 15

/-- The central gl4 Cartan direction, followed by the fifteen sl4 colours. -/
def leviIndex : Fin 16 → Fin 28
  | 0 => 0
  | 1 => 5
  | 2 => 9
  | 3 => 11
  | 4 => 6
  | 5 => 8
  | 6 => 4
  | 7 => 17
  | 8 => 21
  | 9 => 23
  | 10 => 18
  | 11 => 20
  | 12 => 16
  | 13 => 2
  | 14 => 1
  | _ => 3

theorem colour_cases (z : Fin 28) :
    (∃ i : Fin 6, positiveColour i = z) ∨
      (∃ i : Fin 16, leviIndex i = z) ∨
        (∃ i : Fin 6, radicalColour i = z) := by
  fin_cases z <;> decide

set_option maxHeartbeats 8000000 in
-- The finite check covers all Levi, radical, and output colours.
/-- Every Levi bracket with a negative radical letter remains in the radical. -/
theorem levi_radical_closed :
    ∀ i : Fin 16, ∀ j : Fin 6, ∀ z : Fin 28,
      (∀ k : Fin 6, radicalColour k ≠ z) →
      sget (VOA.DeligneAudit.DeligneSector.D4.br
        (leviIndex i) (radicalColour j)) z = 0 := by
  decide +kernel

set_option maxHeartbeats 8000000 in
-- The reverse-order check avoids relying on a separate global skew theorem.
/-- A negative radical bracket with a Levi colour remains in the radical. -/
theorem radical_levi_closed :
    ∀ i : Fin 6, ∀ j : Fin 16, ∀ z : Fin 28,
      (∀ k : Fin 6, radicalColour k ≠ z) →
      sget (VOA.DeligneAudit.DeligneSector.D4.br
        (radicalColour i) (leviIndex j)) z = 0 := by
  decide +kernel

set_option maxHeartbeats 8000000 in
-- This finite check covers all positive, radical, and output colours.
/-- A positive radical bracket with a negative radical letter lies in gl4. -/
theorem positive_radical_closed :
    ∀ i j : Fin 6, ∀ z : Fin 28,
      (∀ k : Fin 16, leviIndex k ≠ z) →
      sget (VOA.DeligneAudit.DeligneSector.D4.br
        (positiveColour i) (radicalColour j)) z = 0 := by
  decide +kernel

set_option maxHeartbeats 8000000 in
-- This finite check covers all positive, Levi, and output colours.
/-- A positive radical bracket with a Levi colour stays positive radical. -/
theorem positive_levi_closed :
    ∀ i : Fin 6, ∀ j : Fin 16, ∀ z : Fin 28,
      (∀ k : Fin 6, positiveColour k ≠ z) →
      sget (VOA.DeligneAudit.DeligneSector.D4.br
        (positiveColour i) (leviIndex j)) z = 0 := by
  decide +kernel

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.colour_cases
#print axioms VOA.DeligneAudit.D4Levi.levi_radical_closed
#print axioms VOA.DeligneAudit.D4Levi.radical_levi_closed
#print axioms VOA.DeligneAudit.D4Levi.positive_radical_closed
#print axioms VOA.DeligneAudit.D4Levi.positive_levi_closed
