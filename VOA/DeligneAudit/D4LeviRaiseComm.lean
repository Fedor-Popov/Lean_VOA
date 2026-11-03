import VOA.DeligneAudit.D4LeviLowerQuot

/-! The simple Levi raising current commutators with radical currents. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.DeligneSector.D4

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V)

theorem simple_raise_comm (i : Fin 3) (j : Fin 6)
    (r s : ℕ) (v : V) :
    ρ.op (leviColour (VOA.DeligneAudit.A3Sector.simpleE i)) r
      (ρ.op (radicalColour j) s v) -
    ρ.op (radicalColour j) s
      (ρ.op (leviColour (VOA.DeligneAudit.A3Sector.simpleE i)) r v) =
      match raiseAction i j with
      | none => 0
      | some (k, n) => (n : ℂ) • ρ.op (radicalColour k) (r + s) v := by
  rw [ρ.comm]
  change (∑ c : Fin 28,
      fD4 (leviColour (VOA.DeligneAudit.A3Sector.simpleE i))
        (radicalColour j) c • ρ.op c (r + s) v) = _
  cases h : raiseAction i j with
  | none => simp [raise_coefficient, h]
  | some p =>
      rcases p with ⟨k, n⟩
      simp [raise_coefficient, h, Finset.sum_ite_eq']

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.simple_raise_comm
