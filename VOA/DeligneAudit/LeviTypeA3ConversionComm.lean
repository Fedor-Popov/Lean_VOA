import VOA.DeligneAudit.LeviTypeA3ConversionKill

/-! The two root-string commutators and their commuting spectators. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.SectorWeyl

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V)

def a3ConvA : Fin 2 → Fin 3
  | 0 => 0
  | 1 => 1

def a3ConvB : Fin 2 → Fin 3
  | 0 => 1
  | 1 => 2

def a3ConvSpectator : Fin 2 → Fin 3
  | 0 => 2
  | 1 => 0

/-- The first conversion is F₁ to F₂; the second is F₂ to F₃. -/
theorem a3_conversion_step (j : Fin 2) (r s : ℕ) :
    ρ.op (leviF j) r * ρ.op (F (a3ConvA j)) s -
      ρ.op (F (a3ConvA j)) s * ρ.op (leviF j) r =
        ρ.op (F (a3ConvB j)) (r + s) := by
  apply LinearMap.ext
  intro v
  fin_cases j
  · exact levi_comm_one ρ r s v
  · exact levi_comm_two ρ r s v

/-- The converted root and the spectator commute with the same Levi current. -/
theorem a3_conversion_other (j : Fin 2) (t : Fin 3)
    (ht : t = a3ConvB j ∨ t = a3ConvSpectator j) (r s : ℕ) :
    ρ.op (leviF j) r * ρ.op (F t) s =
      ρ.op (F t) s * ρ.op (leviF j) r := by
  apply sub_eq_zero.mp
  apply LinearMap.ext
  intro v
  have hne : t.val ≠ j.val := by
    rcases ht with rfl | rfl <;> fin_cases j <;> decide
  exact levi_comm_other ρ j t hne r s v

/-- Every pair of radical currents commutes, including converted roots. -/
theorem a3_conversion_radical_comm (i j : Fin 3) (r s : ℕ) :
    ρ.op (F i) r * ρ.op (F j) s =
      ρ.op (F j) s * ρ.op (F i) r := by
  simpa [radicalOp] using radicalOp_comm ρ i r j s

/-- A word in the remaining radical colour commutes with the conversion current. -/
theorem a3_conversion_spectator_comm (j : Fin 2) (zs : List ℕ) (r : ℕ) :
    (zs.map fun s => ρ.op (F (a3ConvSpectator j)) s).prod *
      ρ.op (leviF j) r =
      ρ.op (leviF j) r *
        (zs.map fun s => ρ.op (F (a3ConvSpectator j)) s).prod := by
  induction zs with
  | nil => simp
  | cons s zs ih =>
      simp only [List.map_cons, List.prod_cons]
      rw [mul_assoc, ih, ← mul_assoc,
        ← a3_conversion_other ρ j (a3ConvSpectator j) (Or.inr rfl) r s,
        mul_assoc]

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a3_conversion_step
#print axioms VOA.DeligneAudit.A3Sector.a3_conversion_other
#print axioms VOA.DeligneAudit.A3Sector.a3_conversion_radical_comm
#print axioms VOA.DeligneAudit.A3Sector.a3_conversion_spectator_comm
