import VOA.DeligneAudit.A3SectorCount
import VOA.DeligneAudit.A3SectorSl2
import VOA.DeligneAudit.DeligneFusionUnivGGrade

/-! Exact residual statements for the all-weight `sl₄` local Weyl bound. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.SectorLoop

/-- Fundamental-weight coefficients at nodes 1, 2, 3. -/
def weightABC (a b c : ℕ) : Fin 3 → ℕ
  | 0 => a
  | 1 => b
  | 2 => c

/-- The exact remaining all-weight theorem TA for `sl₄`. -/
def TypeABound : Prop :=
  ∀ (a b c : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (ρ : CurrentModule bracketTable V) (w : V),
    LocalWeylRel ρ w (weightABC a b c) →
      FiniteDimensional ℂ (VOA.DeligneAudit.UnivG.cycSubG ρ w) ∧
        Module.finrank ℂ (VOA.DeligneAudit.UnivG.cycSubG ρ w) ≤
          4 ^ a * 6 ^ b * 4 ^ c

/-- The all-weight `sl₃` warm-up needed by the Levi induction. -/
structure A2LocalWeylRel {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : CurrentModule VOA.AffineSl3.bracketTable V) (w : V) (p q : ℕ) : Prop where
  raising : ∀ e : Fin 8, e.val < 3 → ∀ r, ρ.op e r w = 0
  cartan_pos : ∀ h : Fin 8, 6 ≤ h.val → ∀ r, 0 < r → ρ.op h r w = 0
  cartan_first : ρ.op 6 0 w = (p : ℂ) • w
  cartan_second : ρ.op 7 0 w = (q : ℂ) • w
  lowering_first : (ρ.op 3 0)^[p + 1] w = 0
  lowering_second : (ρ.op 4 0)^[q + 1] w = 0

def TypeA2Bound : Prop :=
  ∀ (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (ρ : CurrentModule VOA.AffineSl3.bracketTable V) (w : V),
    A2LocalWeylRel ρ w p q →
      FiniteDimensional ℂ (VOA.DeligneAudit.UnivG.cycSubG ρ w) ∧
        Module.finrank ℂ (VOA.DeligneAudit.UnivG.cycSubG ρ w) ≤ 3 ^ p * 3 ^ q

/-- Jacobi for the 15-colour structure constants, still to be certified. -/
def JacobiGoal : Prop := JacobiCoord bracketTable

end VOA.DeligneAudit.A3Sector
