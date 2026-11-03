import VOA.DeligneAudit.LeviTypeA2Cutoff

/-! The finite bracket checks needed for the node-two Levi straightening argument. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.AffineSl3

/-- The two positive radical colours, `e₁` and `e₁₂`. -/
def a2Positive (a : Fin 8) : Prop := a = 0 ∨ a = 2

/-- The node-two Levi colours, including both Cartan directions. -/
def a2Levi (a : Fin 8) : Prop := a = 1 ∨ a = 4 ∨ a = 6 ∨ a = 7

/-- The two negative radical colours, `f₁` and `f₁₂`. -/
def a2Radical (a : Fin 8) : Prop := a = 3 ∨ a = 5

/-- Commuting a positive radical letter past a negative one produces only Levi letters. -/
theorem a2_positive_radical_bracket (a b c : Fin 8)
    (ha : a2Positive a) (hb : a2Radical b) (hc : ¬ a2Levi c) :
    VOA.AffineSl3.bracketTable a b c = 0 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    fin_cases c <;> simp_all [a2Levi, VOA.AffineSl3.bracketTable]

/-- Commuting a Levi letter past a negative radical letter stays in that radical. -/
theorem a2_levi_radical_bracket (a b c : Fin 8)
    (ha : a2Levi a) (hb : a2Radical b) (hc : ¬ a2Radical c) :
    VOA.AffineSl3.bracketTable a b c = 0 := by
  rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl <;>
    fin_cases c <;> simp_all [a2Radical, VOA.AffineSl3.bracketTable]

/-- The reverse bracket of a negative radical and a Levi letter stays radical. -/
theorem a2_radical_levi_bracket (a b c : Fin 8)
    (ha : a2Radical a) (hb : a2Levi b) (hc : ¬ a2Radical c) :
    VOA.AffineSl3.bracketTable a b c = 0 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
    fin_cases c <;> simp_all [a2Radical, VOA.AffineSl3.bracketTable]

/-- Commuting a positive radical letter past a Levi letter stays positive. -/
theorem a2_positive_levi_bracket (a b c : Fin 8)
    (ha : a2Positive a) (hb : a2Levi b) (hc : ¬ a2Positive c) :
    VOA.AffineSl3.bracketTable a b c = 0 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
    fin_cases c <;> simp_all [a2Positive, VOA.AffineSl3.bracketTable]

/-- The negative radical is abelian. -/
theorem a2_radical_radical_bracket (a b c : Fin 8)
    (ha : a2Radical a) (hb : a2Radical b) :
    VOA.AffineSl3.bracketTable a b c = 0 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    fin_cases c <;> simp [VOA.AffineSl3.bracketTable]

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a2_positive_radical_bracket
#print axioms VOA.DeligneAudit.A3Sector.a2_levi_radical_bracket
#print axioms VOA.DeligneAudit.A3Sector.a2_radical_levi_bracket
#print axioms VOA.DeligneAudit.A3Sector.a2_positive_levi_bracket
#print axioms VOA.DeligneAudit.A3Sector.a2_radical_radical_bracket
