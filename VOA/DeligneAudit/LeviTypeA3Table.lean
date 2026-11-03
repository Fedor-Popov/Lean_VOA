import VOA.DeligneAudit.LeviTypeA3Order

/-! Embed the standard eight-colour `sl₃` table in the `sl₄` Levi. -/

namespace VOA.DeligneAudit.A3Sector

/-- The `sl₃` colours on matrix indices 1, 2, 3. -/
def a3LeviColour : Fin 8 → Fin 15
  | 0 => 3
  | 1 => 5
  | 2 => 4
  | 3 => 9
  | 4 => 11
  | 5 => 10
  | 6 => 13
  | 7 => 14

theorem a3LeviColour_injective : Function.Injective a3LeviColour := by
  intro x y h
  fin_cases x <;> fin_cases y <;> simp_all [a3LeviColour]

theorem a3LeviColour_levi (x : Fin 8) : a3Levi (a3LeviColour x) := by
  fin_cases x <;> simp [a3Levi, a3LeviColour]

set_option maxHeartbeats 8000000 in
-- The finite comparison reduces 512 matrix brackets and needs a larger heartbeat budget.
/-- All `sl₃` structure constants agree inside the `sl₄` matrix table. -/
theorem a3Levi_bracket_compat (x y z : Fin 8) :
    bracketTable (a3LeviColour x) (a3LeviColour y) (a3LeviColour z) =
      VOA.AffineSl3.bracketTable x y z := by
  fin_cases x <;> fin_cases y <;> fin_cases z <;>
    norm_num [a3LeviColour, bracketTable,
      VOA.AffineSl3.bracketTable] <;> norm_cast

/-- Brackets of embedded `sl₃` colours have no component outside its image. -/
theorem a3Levi_bracket_outside (x y : Fin 8) (z : Fin 15)
    (hz : z ∉ Set.range a3LeviColour) :
    bracketTable (a3LeviColour x) (a3LeviColour y) z = 0 := by
  have h : bracketInt (a3LeviColour x) (a3LeviColour y) z = 0 := by
    fin_cases z
    all_goals
      first
      | exact False.elim (hz ⟨0, rfl⟩)
      | exact False.elim (hz ⟨1, rfl⟩)
      | exact False.elim (hz ⟨2, rfl⟩)
      | exact False.elim (hz ⟨3, rfl⟩)
      | exact False.elim (hz ⟨4, rfl⟩)
      | exact False.elim (hz ⟨5, rfl⟩)
      | exact False.elim (hz ⟨6, rfl⟩)
      | exact False.elim (hz ⟨7, rfl⟩)
      | fin_cases x <;> fin_cases y <;> decide
  simp [bracketTable, h]

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a3LeviColour_injective
#print axioms VOA.DeligneAudit.A3Sector.a3LeviColour_levi
#print axioms VOA.DeligneAudit.A3Sector.a3Levi_bracket_compat
#print axioms VOA.DeligneAudit.A3Sector.a3Levi_bracket_outside
