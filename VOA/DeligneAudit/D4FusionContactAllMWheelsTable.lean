import VOA.DeligneAudit.D4FusionContactGradingTable

/-! Exact finite g0 action data needed for the static triangle wheels. -/
namespace VOA.DeligneAudit.D4FusionContact.Polynomial.AllMWheels

open VOA.DeligneAudit.DeligneSector.Sparse
open VOA.DeligneAudit.DeligneSector.D4 (br)

def direction (j : Fin 12) : Fin 10 :=
  ([7, 8, 9, 8, 7, 8, 9, 9, 4, 5, 6, 5]).getD j.val 0

def sourceColor (j : Fin 12) : Fin 9 :=
  ([0, 0, 0, 1, 1, 4, 4, 7, 7, 7, 7, 6]).getD j.val 0

def targetColor (j : Fin 12) : Fin 9 :=
  ([1, 2, 3, 4, 0, 0, 7, 0, 6, 5, 4, 3]).getD j.val 0

def actionCoeff (j : Fin 12) : ℤ :=
  ([1, 1, -1, -1, 0, 0, 1, 0, -1, -1, 1, -1]).getD j.val 0

theorem action_rows_Z : ∀ j : Fin 12, ∀ a : Fin 9,
    fZ br (zeroIndex (direction j)) (radIndex (sourceColor j)) (radIndex a) =
      if a = targetColor j then actionCoeff j else 0 := by
  decide +kernel

theorem action_rows (j : Fin 12) (a : Fin 9) :
    contactF (zeroIndex (direction j)) (radIndex (sourceColor j)) (radIndex a) =
      if a = targetColor j then (actionCoeff j : ℂ) else 0 := by
  change (fZ br (zeroIndex (direction j)) (radIndex (sourceColor j)) (radIndex a) : ℂ) = _
  rw [action_rows_Z]
  split_ifs <;> norm_num

end VOA.DeligneAudit.D4FusionContact.Polynomial.AllMWheels

#print axioms VOA.DeligneAudit.D4FusionContact.Polynomial.AllMWheels.action_rows
