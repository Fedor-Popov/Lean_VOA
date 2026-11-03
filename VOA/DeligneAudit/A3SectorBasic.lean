import VOA.DeligneAudit.A3SectorTable

/-!
All-weight `sl₄[t]` local Weyl data, using the 15-colour Chevalley table.
The fundamental-weight coefficients are `(a,b,c)` in node order.
-/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.SectorWeyl

/-- The three simple lowering colours, E₁₀, E₂₁, E₃₂. -/
def simpleF : Fin 3 → Fin 15
  | 0 => 6
  | 1 => 9
  | 2 => 11

/-- The three simple Cartan colours. -/
def simpleH : Fin 3 → Fin 15
  | 0 => 12
  | 1 => 13
  | 2 => 14

/-- The local Weyl relations for any dominant integral `sl₄` weight. -/
structure LocalWeylRel {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : CurrentModule bracketTable V) (w : V) (weight : Fin 3 → ℕ) : Prop where
  raising : ∀ e : Fin 15, e.val < 6 → ∀ r, ρ.op e r w = 0
  cartan_pos : ∀ i : Fin 3, ∀ r, 0 < r → ρ.op (simpleH i) r w = 0
  cartan_zero : ∀ i : Fin 3, ρ.op (simpleH i) 0 w = (weight i : ℂ) • w
  lowering : ∀ i : Fin 3, (ρ.op (simpleF i) 0)^[weight i + 1] w = 0

theorem simpleF_zero : simpleF 0 = F 0 := rfl
theorem simpleF_levi_one : simpleF 1 = leviF 0 := rfl
theorem simpleF_levi_two : simpleF 2 = leviF 1 := rfl

/-- All loop modes of the radical commute as operators. -/
theorem radical_comm {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : CurrentModule bracketTable V) (i j : Fin 3) (r s : ℕ) (v : V) :
    ρ.op (F i) r (ρ.op (F j) s v) -
      ρ.op (F j) s (ρ.op (F i) r v) = 0 := by
  rw [ρ.comm]
  simp [radical_abelian]

/-- The first Levi lowering operator moves F₁ to F₂. -/
theorem levi_comm_one {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : CurrentModule bracketTable V) (r s : ℕ) (v : V) :
    ρ.op (leviF 0) r (ρ.op (F 0) s v) -
      ρ.op (F 0) s (ρ.op (leviF 0) r v) = ρ.op (F 1) (r + s) v := by
  rw [ρ.comm]
  simp [levi_step_one]

/-- The second Levi lowering operator moves F₂ to F₃. -/
theorem levi_comm_two {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : CurrentModule bracketTable V) (r s : ℕ) (v : V) :
    ρ.op (leviF 1) r (ρ.op (F 1) s v) -
      ρ.op (F 1) s (ρ.op (leviF 1) r v) = ρ.op (F 2) (r + s) v := by
  rw [ρ.comm]
  simp [levi_step_two]

/-- Other Levi lowering brackets with node-1 radical letters vanish. -/
theorem levi_comm_other {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : CurrentModule bracketTable V) (i : Fin 2) (j : Fin 3)
    (h : j.val ≠ i.val) (r s : ℕ) (v : V) :
    ρ.op (leviF i) r (ρ.op (F j) s v) -
      ρ.op (F j) s (ρ.op (leviF i) r v) = 0 := by
  rw [ρ.comm]
  simp [levi_other_zero i j h]

#print axioms radical_comm
#print axioms levi_comm_one
#print axioms levi_comm_two
#print axioms levi_comm_other

end VOA.DeligneAudit.A3Sector
