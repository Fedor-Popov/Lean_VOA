import VOA.DeligneAudit.A3SectorBasic

/-! The three simple-root `sl₂[t]` triples in the A₃ table. -/

namespace VOA.DeligneAudit.A3Sector

def simpleE : Fin 3 → Fin 15
  | 0 => 0
  | 1 => 3
  | 2 => 5

theorem simpleE_raising (i : Fin 3) : (simpleE i).val < 6 := by
  fin_cases i <;> decide

theorem simple_ef_table (i : Fin 3) (c : Fin 15) :
    bracketTable (simpleE i) (simpleF i) c =
      if c = simpleH i then 1 else 0 := by
  have h : bracketInt (simpleE i) (simpleF i) c =
      if c = simpleH i then 1 else 0 := by
    fin_cases i <;> fin_cases c <;> decide
  simp [bracketTable, h]

theorem simple_hf_table (i : Fin 3) (c : Fin 15) :
    bracketTable (simpleH i) (simpleF i) c =
      if c = simpleF i then -2 else 0 := by
  have h : bracketInt (simpleH i) (simpleF i) c =
      if c = simpleF i then -2 else 0 := by
    fin_cases i <;> fin_cases c <;> decide
  simp [bracketTable, h]

theorem simple_ff_table (i : Fin 3) (c : Fin 15) :
    bracketTable (simpleF i) (simpleF i) c = 0 := by
  have h : bracketInt (simpleF i) (simpleF i) c = 0 := by
    fin_cases i <;> fin_cases c <;> decide
  simp [bracketTable, h]

#print axioms simple_ef_table
#print axioms simple_hf_table
#print axioms simple_ff_table

end VOA.DeligneAudit.A3Sector
