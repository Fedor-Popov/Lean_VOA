import VOA.DeligneAudit.A3SectorBasic

/-! Weights of the node-1 radical under the `sl₃` Levi, nodes 2 and 3. -/

namespace VOA.DeligneAudit.A3Sector

def leviH : Fin 2 → Fin 15
  | 0 => 13
  | 1 => 14

/-- The three positive roots of the Levi `sl₃`. -/
def leviE : Fin 3 → Fin 15
  | 0 => 3
  | 1 => 4
  | 2 => 5

/-- The only nonzero positive-Levi actions on radical letters are
`E₁₂·E₂₀ = E₁₀`, `E₁₃·E₃₀ = E₁₀`, and `E₂₃·E₃₀ = E₂₀`. -/
def raiseCoeff : Fin 3 → Fin 3 → Fin 15 → ℤ
  | 0, 1, c => if c = F 0 then 1 else 0
  | 1, 2, c => if c = F 0 then 1 else 0
  | 2, 2, c => if c = F 1 then 1 else 0
  | _, _, _ => 0

theorem levi_raising_table (i j : Fin 3) (c : Fin 15) :
    bracketTable (leviE i) (F j) c = (raiseCoeff i j c : ℂ) := by
  have h : bracketInt (leviE i) (F j) c = raiseCoeff i j c := by
    fin_cases i <;> fin_cases j <;> fin_cases c <;> decide
  simp [bracketTable, h]

/-- In column order E₁₀, E₂₀, E₃₀, the Levi weights are
`(1,0)`, `(-1,1)`, `(0,-1)`. -/
def leviWeight : Fin 2 → Fin 3 → ℤ
  | 0, 0 => 1
  | 0, 1 => -1
  | 0, 2 => 0
  | 1, 0 => 0
  | 1, 1 => 1
  | 1, 2 => -1

theorem levi_cartan_table (i : Fin 2) (j : Fin 3) (c : Fin 15) :
    bracketTable (leviH i) (F j) c =
      if c = F j then (leviWeight i j : ℂ) else 0 := by
  have h : bracketInt (leviH i) (F j) c =
      if c = F j then leviWeight i j else 0 := by
    fin_cases i <;> fin_cases j <;> fin_cases c <;> decide
  simp [bracketTable, h]

theorem levi_cartan_comm {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : VOA.DeligneAudit.SectorWeyl.CurrentModule bracketTable V)
    (i : Fin 2) (j : Fin 3) (r s : ℕ) (v : V) :
    ρ.op (leviH i) r (ρ.op (F j) s v) -
      ρ.op (F j) s (ρ.op (leviH i) r v) =
        (leviWeight i j : ℂ) • ρ.op (F j) (r + s) v := by
  rw [ρ.comm]
  simp [levi_cartan_table]

/-- The Levi labels of a radical monomial with letter counts `d`. -/
def keyWeight (b c : ℤ) (d : Fin 3 → ℕ) : Fin 2 → ℤ
  | 0 => b + d 0 - d 1
  | 1 => c + d 1 - d 2

theorem keyWeight_add_letter (b c : ℤ) (d : Fin 3 → ℕ) (j : Fin 3) (i : Fin 2) :
    keyWeight b c (Function.update d j (d j + 1)) i =
      keyWeight b c d i + leviWeight i j := by
  fin_cases i <;> fin_cases j <;>
    simp [keyWeight, leviWeight, Function.update] <;> omega

#print axioms levi_raising_table
#print axioms levi_cartan_table
#print axioms levi_cartan_comm
#print axioms keyWeight_add_letter

end VOA.DeligneAudit.A3Sector
