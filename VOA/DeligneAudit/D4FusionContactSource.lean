import VOA.DeligneAudit.D4FusionContactNilpotence
import VOA.DeligneAudit.D4FusionContactLengthTwo
import VOA.DeligneAudit.D4FusionContactSector
import VOA.DeligneAudit.D4FusionContactKnown

/-! # Actual multiplicity-one source nilpotence and contact-word reduction -/

namespace VOA.DeligneAudit.D4FusionContact

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.DeligneSector
open VOA.DeligneAudit.DeligneSector.D4

noncomputable section

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable {R : CurrentModule D4sector.f V} {w : V}

theorem localWeyl_center_known (h : LocalWeylRelG D4sector R w 1) :
    ∃ N, (center R ^ N) w = 0 := localWeyl_center_local_nil h

/-- The actual multiplicity-one source has center cube zero, derived
from highest-root sl₂ and the proved finite-table local nilpotence. -/
theorem localWeyl_center_cube (h : LocalWeylRelG D4sector R w 1) :
    (center R ^ 3) w = 0 :=
  center_cube_of_known (highestRel_of_localWeyl h) (localWeyl_center_known h)

theorem localWeyl_simple_square (h : LocalWeylRelG D4sector R w 1) :
    (root R 0 ^ 2) w = 0 := by
  have hi : D4sector.lowering (18 : Fin 28) := by
    change 16 ≤ (18 : Fin 28).val ∧ (18 : Fin 28).val < 20
    decide
  have he : D4sector.lowExp (18 : Fin 28) = 1 := rfl
  simpa only [he, Nat.mul_one, Module.End.pow_apply] using h.lowering (18 : Fin 28) hi

/-- Every actual multiplicity-one zero-mode radical word reduces to
length at most two, with no additional source relation or FD premise. -/
theorem localWeyl_radicalWord_two (h : LocalWeylRelG D4sector R w 1) (l : List (Fin 9)) :
    radicalWord R l w ∈ piece R w 2 :=
  radicalWord_mem_two (highestRel_of_localWeyl h) (localWeyl_center_cube h) l

end
end VOA.DeligneAudit.D4FusionContact

#print axioms VOA.DeligneAudit.D4FusionContact.localWeyl_center_cube
#print axioms VOA.DeligneAudit.D4FusionContact.localWeyl_simple_square
#print axioms VOA.DeligneAudit.D4FusionContact.localWeyl_radicalWord_two
