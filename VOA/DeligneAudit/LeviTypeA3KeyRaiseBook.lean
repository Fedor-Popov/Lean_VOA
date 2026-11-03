import VOA.DeligneAudit.LeviTypeA3KeyRaiseZero

/-! Exact key bookkeeping for all three positive Levi root currents. -/

namespace VOA.DeligneAudit.A3Sector

def a3RaiseKey (i : Fin 3) (r : ℕ) (k : A3RadicalKey) : A3RadicalKey :=
  match i with
  | 0 => ⟨k.d₁ + 1, k.d₂ - 1, k.d₃, k.degree + r⟩
  | 1 => ⟨k.d₁ + 1, k.d₂, k.d₃ - 1, k.degree + r⟩
  | 2 => ⟨k.d₁, k.d₂ + 1, k.d₃ - 1, k.degree + r⟩

theorem a3RaiseKey_insert_other (i j : Fin 3) (r s : ℕ) (k : A3RadicalKey)
    (hj : j ≠ a3RaiseSource i) :
    a3RaiseKey i r (a3KeyInsert j s k) =
      a3KeyInsert j s (a3RaiseKey i r k) := by
  rcases k with ⟨d₁, d₂, d₃, degree⟩
  fin_cases i <;> fin_cases j <;>
    simp_all [a3RaiseKey, a3RaiseSource, a3KeyInsert,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

theorem a3RaiseKey_insert_source (i : Fin 3) (r s : ℕ) (k : A3RadicalKey)
    (hk : 0 < (if i = 0 then k.d₂ else k.d₃)) :
    a3RaiseKey i r (a3KeyInsert (a3RaiseSource i) s k) =
      a3KeyInsert (a3RaiseSource i) s (a3RaiseKey i r k) := by
  rcases k with ⟨d₁, d₂, d₃, degree⟩
  fin_cases i <;>
    simp_all [a3RaiseKey, a3RaiseSource, a3KeyInsert,
      Nat.add_comm, Nat.add_left_comm] <;> omega

theorem a3RaiseKey_replace (i : Fin 3) (r s : ℕ) (k : A3RadicalKey) :
    a3RaiseKey i r (a3KeyInsert (a3RaiseSource i) s k) =
      a3KeyInsert (a3RaiseDest i) (r + s) k := by
  rcases k with ⟨d₁, d₂, d₃, degree⟩
  fin_cases i <;>
    simp [a3RaiseKey, a3RaiseSource, a3RaiseDest, a3KeyInsert,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

theorem a3RaiseKey_less (b c : ℕ) (i : Fin 3) (r : ℕ) (k : A3RadicalKey)
    (hk : 0 < (if i = 0 then k.d₂ else k.d₃)) :
    a3KeyLess b c k (a3RaiseKey i r k) := by
  fin_cases i <;>
    dsimp [a3KeyLess, a3KeyHeight, a3RaiseKey] at * <;>
    (left; omega)

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a3RaiseKey_insert_other
#print axioms VOA.DeligneAudit.A3Sector.a3RaiseKey_insert_source
#print axioms VOA.DeligneAudit.A3Sector.a3RaiseKey_replace
#print axioms VOA.DeligneAudit.A3Sector.a3RaiseKey_less
