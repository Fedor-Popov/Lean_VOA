import VOA.DeligneAudit.DeligneSectorD4

/-! The six node-one radical colours and the exact D4 lowering action. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.DeligneSector.Sparse

/-- E, X, U, U', Y, Z, in that order. -/
def radicalColour : Fin 6 → Fin 28
  | 0 => 19
  | 1 => 22
  | 2 => 24
  | 3 => 25
  | 4 => 26
  | 5 => 27

/-- f3, f4, f2, f23, f24, f234, in that order. -/
def lowerColour : Fin 6 → Fin 28
  | 0 => 17
  | 1 => 16
  | 2 => 18
  | 3 => 21
  | 4 => 20
  | 5 => 23

/-- Exact lowering brackets in the unrescaled D4 carrier basis. -/
def lowerAction : Fin 6 → Fin 6 → Option (Fin 6 × ℤ)
  | 0, 1 => some (3, -1)
  | 0, 2 => some (4, -1)
  | 1, 1 => some (2, -1)
  | 1, 3 => some (4, -1)
  | 2, 0 => some (1, 1)
  | 2, 4 => some (5, 1)
  | 3, 0 => some (3, -1)
  | 3, 2 => some (5, 1)
  | 4, 0 => some (2, -1)
  | 4, 3 => some (5, 1)
  | 5, 0 => some (4, -1)
  | 5, 1 => some (5, -1)
  | _, _ => none

/-- The negative radical is abelian, at the level of the sparse bracket table. -/
theorem radical_bracket (i j : Fin 6) :
    VOA.DeligneAudit.DeligneSector.D4.br (radicalColour i) (radicalColour j) = [] := by
  fin_cases i <;> fin_cases j <;> decide

/-- All 36 entries of the paper's lowering table, including zeros and signs. -/
theorem lower_bracket (i j : Fin 6) :
    VOA.DeligneAudit.DeligneSector.D4.br (lowerColour i) (radicalColour j) =
      match lowerAction i j with
      | none => []
      | some (k, n) => [(radicalColour k, n)] := by
  fin_cases i <;> fin_cases j <;> decide

/-- The radical is abelian in the complex structure constants. -/
theorem radical_abelian (i j : Fin 6) (z : Fin 28) :
    VOA.DeligneAudit.DeligneSector.D4.fD4
      (radicalColour i) (radicalColour j) z = 0 := by
  simp [VOA.DeligneAudit.DeligneSector.D4.fD4, fC, fZ, radical_bracket]

/-- Coefficients of all lowering brackets in the actual D4 colour convention. -/
theorem lower_coefficient (i j : Fin 6) (z : Fin 28) :
    VOA.DeligneAudit.DeligneSector.D4.fD4
      (lowerColour i) (radicalColour j) z =
        match lowerAction i j with
        | none => 0
        | some (k, n) => if z = radicalColour k then (n : ℂ) else 0 := by
  rw [VOA.DeligneAudit.DeligneSector.D4.fD4]
  simp only [fC, fZ, lower_bracket]
  cases h : lowerAction i j with
  | none => simp [h, sget]
  | some p =>
      rcases p with ⟨k, n⟩
      by_cases hz : z = radicalColour k
      · subst z
        simp [sget]
      · simp [sget, hz]
        intro hval
        exact (hz (Fin.ext hval.symm)).elim

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.radical_bracket
#print axioms VOA.DeligneAudit.D4Levi.lower_bracket
#print axioms VOA.DeligneAudit.D4Levi.radical_abelian
#print axioms VOA.DeligneAudit.D4Levi.lower_coefficient
