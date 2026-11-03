import VOA.DeligneAudit.A3SectorGoal

/-! Finite bracket checks for the node-one `sl₄` Levi decomposition. -/

namespace VOA.DeligneAudit.A3Sector

/-- Colours E₀₁, E₀₂, E₀₃. -/
def a3Positive (a : Fin 15) : Prop := a = 0 ∨ a = 1 ∨ a = 2

/-- The two Levi simple nodes, their compound roots, and all Cartan directions. -/
def a3Levi (a : Fin 15) : Prop :=
  a = 3 ∨ a = 4 ∨ a = 5 ∨ a = 9 ∨ a = 10 ∨ a = 11 ∨
    a = 12 ∨ a = 13 ∨ a = 14

/-- Colours E₁₀, E₂₀, E₃₀. -/
def a3Radical (a : Fin 15) : Prop := a = 6 ∨ a = 7 ∨ a = 8

theorem a3_colour_cases (a : Fin 15) :
    a3Positive a ∨ a3Levi a ∨ a3Radical a := by
  fin_cases a <;> simp [a3Positive, a3Levi, a3Radical]

theorem a3_positive_radical_bracket (a b c : Fin 15)
    (ha : a3Positive a) (hb : a3Radical b) (hc : ¬ a3Levi c) :
    bracketTable a b c = 0 := by
  have h : bracketInt a b c = 0 := by
    rcases ha with rfl | rfl | rfl <;>
      rcases hb with rfl | rfl | rfl <;>
      fin_cases c <;> simp_all [a3Levi] <;> decide
  simp [bracketTable, h]

theorem a3_levi_radical_bracket (a b c : Fin 15)
    (ha : a3Levi a) (hb : a3Radical b) (hc : ¬ a3Radical c) :
    bracketTable a b c = 0 := by
  have h : bracketInt a b c = 0 := by
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hb with rfl | rfl | rfl <;>
      fin_cases c <;> simp_all [a3Radical] <;> decide
  simp [bracketTable, h]

theorem a3_radical_levi_bracket (a b c : Fin 15)
    (ha : a3Radical a) (hb : a3Levi b) (hc : ¬ a3Radical c) :
    bracketTable a b c = 0 := by
  have h : bracketInt a b c = 0 := by
    rcases ha with rfl | rfl | rfl <;>
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      fin_cases c <;> simp_all [a3Radical] <;> decide
  simp [bracketTable, h]

theorem a3_positive_levi_bracket (a b c : Fin 15)
    (ha : a3Positive a) (hb : a3Levi b) (hc : ¬ a3Positive c) :
    bracketTable a b c = 0 := by
  have h : bracketInt a b c = 0 := by
    rcases ha with rfl | rfl | rfl <;>
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      fin_cases c <;> simp_all [a3Positive] <;> decide
  simp [bracketTable, h]

theorem a3_radical_radical_bracket (a b c : Fin 15)
    (ha : a3Radical a) (hb : a3Radical b) :
    bracketTable a b c = 0 := by
  have h : bracketInt a b c = 0 := by
    rcases ha with rfl | rfl | rfl <;>
      rcases hb with rfl | rfl | rfl <;>
      fin_cases c <;> decide
  simp [bracketTable, h]

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a3_colour_cases
#print axioms VOA.DeligneAudit.A3Sector.a3_positive_radical_bracket
#print axioms VOA.DeligneAudit.A3Sector.a3_levi_radical_bracket
#print axioms VOA.DeligneAudit.A3Sector.a3_radical_levi_bracket
#print axioms VOA.DeligneAudit.A3Sector.a3_positive_levi_bracket
#print axioms VOA.DeligneAudit.A3Sector.a3_radical_radical_bracket
