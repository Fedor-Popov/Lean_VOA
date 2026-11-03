import VOA.DeligneAudit.D4LeviSupport

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.A3Sector
open VOA.DeligneAudit.DeligneSector.Sparse

/-- Simple sl4 raising brackets on E, X, U, U', Y, Z, including signs. -/
def raiseAction : Fin 3 → Fin 6 → Option (Fin 6 × ℤ)
  | 0, 3 => some (1, -1)
  | 0, 4 => some (2, -1)
  | 1, 1 => some (0, 1)
  | 1, 5 => some (4, 1)
  | 2, 2 => some (1, -1)
  | 2, 4 => some (3, -1)
  | _, _ => none

theorem raise_bracket (i : Fin 3) (j : Fin 6) :
    VOA.DeligneAudit.DeligneSector.D4.br
      (leviColour (simpleE i)) (radicalColour j) =
      match raiseAction i j with
      | none => []
      | some (k, n) => [(radicalColour k, n)] := by
  fin_cases i <;> fin_cases j <;> decide

theorem raise_coefficient (i : Fin 3) (j : Fin 6) (z : Fin 28) :
    VOA.DeligneAudit.DeligneSector.D4.fD4
      (leviColour (simpleE i)) (radicalColour j) z =
      match raiseAction i j with
      | none => 0
      | some (k, n) => if z = radicalColour k then (n : ℂ) else 0 := by
  rw [VOA.DeligneAudit.DeligneSector.D4.fD4]
  simp only [fC, fZ, raise_bracket]
  cases h : raiseAction i j with
  | none => simp [h, sget]
  | some p =>
      rcases p with ⟨k, n⟩
      by_cases hz : z = radicalColour k
      · subst z
        simp [sget]
      · simp [sget, hz]
        intro hval
        exact (hz (Fin.ext hval.symm)).elim

/-- Each nonzero simple raising replacement increases Levi height by two. -/
theorem raise_height (m : ℕ) (i : Fin 3) (j k : Fin 6) (n : ℤ)
    (h : raiseAction i j = some (k, n)) :
    keyHeight m (wordKey [(j, 0)]) + 2 =
      keyHeight m (wordKey [(k, 0)]) := by
  fin_cases i <;> fin_cases j <;> simp [raiseAction] at h
  all_goals
    rcases h with ⟨rfl, rfl⟩
    simp [keyHeight, wordKey] <;> omega

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.raise_bracket
#print axioms VOA.DeligneAudit.D4Levi.raise_coefficient
#print axioms VOA.DeligneAudit.D4Levi.raise_height
