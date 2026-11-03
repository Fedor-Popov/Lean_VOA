import VOA.DeligneAudit.LeviTypeA3KeyCartanQuot

/-! The positive Levi currents act on the three radical letters by replacement. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.SectorWeyl

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule bracketTable V)

/-- The only replacements are `F₂ ↦ F₁` and `F₃ ↦ F₁,F₂`. -/
def a3RaiseTarget : Fin 3 → Fin 3 → Option (Fin 3)
  | 0, 1 => some 0
  | 1, 2 => some 0
  | 2, 2 => some 1
  | _, _ => none

theorem a3_raising_comm (i j : Fin 3) (r s : ℕ) (v : V) :
    ρ.op (leviE i) r (radicalOp ρ j s v) -
      radicalOp ρ j s (ρ.op (leviE i) r v) =
        match a3RaiseTarget i j with
        | none => 0
        | some t => radicalOp ρ t (r + s) v := by
  change ρ.op (leviE i) r (ρ.op (F j) s v) -
    ρ.op (F j) s (ρ.op (leviE i) r v) = _
  rw [ρ.comm]
  fin_cases i <;> fin_cases j <;>
    simp [a3RaiseTarget, radicalOp,
      levi_raising_table, raiseCoeff]

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a3_raising_comm
