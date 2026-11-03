import VOA.DeligneAudit.D4LeviData
import VOA.DeligneAudit.A3SectorTable

/-! The node-one Levi is a signed copy of the standard matrix-unit sl4 table. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.DeligneSector.Sparse

/-- A3 matrix units, then three simple coroots, in the D4 carrier. -/
def leviColour : Fin 15 → Fin 28
  | 0 => 5
  | 1 => 9
  | 2 => 11
  | 3 => 6
  | 4 => 8
  | 5 => 4
  | 6 => 17
  | 7 => 21
  | 8 => 23
  | 9 => 18
  | 10 => 20
  | 11 => 16
  | 12 => 2
  | 13 => 1
  | 14 => 3

/-- The matrix-unit normalization relative to the D4 carrier basis. -/
def leviSign : Fin 15 → ℤ
  | 5 | 7 | 8 | 10 | 11 => -1
  | _ => 1

theorem leviColour_injective : Function.Injective leviColour := by
  intro x y h
  fin_cases x <;> fin_cases y <;> simp_all [leviColour]

set_option maxHeartbeats 8000000 in
-- The comparison checks the full finite matrix-unit table against the sparse D4 table.
/-- Every one of the 3375 matrix-unit structure constants agrees after signs. -/
theorem levi_bracket_int (x y z : Fin 15) :
    leviSign x * leviSign y *
      sget (VOA.DeligneAudit.DeligneSector.D4.br (leviColour x) (leviColour y))
        (leviColour z) =
      leviSign z * VOA.DeligneAudit.A3Sector.bracketInt x y z := by
  fin_cases x <;> fin_cases y <;> fin_cases z <;> decide

/-- All brackets of Levi colours are supported on Levi colours. -/
theorem levi_support_check (x y : Fin 15) :
    (VOA.DeligneAudit.DeligneSector.D4.br (leviColour x) (leviColour y)).all
      (fun p => decide (∃ z : Fin 15, (leviColour z : ℕ) = p.1)) = true := by
  fin_cases x <;> fin_cases y <;> decide

theorem levi_bracket_compat (x y z : Fin 15) :
    (leviSign x : ℂ) * (leviSign y : ℂ) *
      VOA.DeligneAudit.DeligneSector.D4.fD4 (leviColour x) (leviColour y)
        (leviColour z) =
      (leviSign z : ℂ) * VOA.DeligneAudit.A3Sector.bracketTable x y z := by
  simpa only [VOA.DeligneAudit.DeligneSector.D4.fD4, fC, fZ,
    VOA.DeligneAudit.A3Sector.bracketTable, Int.cast_mul] using
      congrArg (fun n : ℤ => (n : ℂ)) (levi_bracket_int x y z)

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.leviColour_injective
#print axioms VOA.DeligneAudit.D4Levi.levi_bracket_int
#print axioms VOA.DeligneAudit.D4Levi.levi_support_check
#print axioms VOA.DeligneAudit.D4Levi.levi_bracket_compat
