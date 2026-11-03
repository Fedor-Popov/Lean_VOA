import VOA.DeligneAudit.D4FusionContactSector
import VOA.DeligneAudit.DeligneFusionFiniteGNil

/-!
# Light D₄ center local nilpotence certificate

This reuses the existing eight-step finite-table certificate with the
generic proved nilpotence engine. It deliberately imports no universal
character, squeeze or Demazure-count module.
-/

namespace VOA.DeligneAudit.D4FusionContact

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.DeligneSector
open VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.DeligneSector.Sparse
open VOA.DeligneAudit.FiniteG

noncomputable section

def centerNilKnown (c : Fin 28) : Bool :=
  decide (4 ≤ c.val ∧ c.val < 16) || decide (16 ≤ c.val ∧ c.val < 20)

def centerNilNonzero (a b c : Fin 28) : Bool := fZ br a b c != 0

def centerNilCert : List (Step 28) :=
  [(16, 18, [20]), (17, 18, [21]), (17, 20, [23]), (18, 19, [22]),
    (19, 20, [24]), (19, 21, [25]), (19, 23, [26]), (18, 26, [27])]

theorem centerNilCert_valid :
    certValid D4sector.wt centerNilNonzero centerNilKnown centerNilCert = true := by
  decide +kernel

theorem centerNilCert_contains : certKnown centerNilKnown centerNilCert (27 : Fin 28) = true := by
  decide +kernel

theorem centerNilNonzero_sound (a b c : Fin 28) (h : centerNilNonzero a b c = true) :
    D4sector.f a b c ≠ 0 := by
  have hi : fZ br a b c ≠ 0 := by
    intro hz
    simp [centerNilNonzero, hz] at h
  change (fZ br a b c : ℂ) ≠ 0
  exact_mod_cast hi

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable {R : CurrentModule D4sector.f V} {w : V} {m : ℕ}

theorem localWeyl_known_initial (h : LocalWeylRelG D4sector R w m) (c : Fin 28)
    (hc : centerNilKnown c = true) : Known R w c := by
  have hs : D4sector.raising c ∨ D4sector.lowering c := by
    simpa only [centerNilKnown, Bool.or_eq_true, decide_eq_true_eq] using hc
  rcases hs with hr | hl
  · exact ⟨1, by simpa only [pow_one] using h.raising c hr 0⟩
  · exact ⟨m * D4sector.lowExp c + 1,
      by simpa only [Module.End.pow_apply] using h.lowering c hl⟩

/-- Actual center local nilpotence, without importing any character
or dimension theorem. The eight-step certificate is kernel checked. -/
theorem localWeyl_center_local_nil (h : LocalWeylRelG D4sector R w m) :
    ∃ N, (R.op (27 : Fin 28) 0 ^ N) w = 0 :=
  known_of_certValid R centerNilNonzero_sound centerNilCert centerNilKnown
    (localWeyl_known_initial h) centerNilCert_valid (27 : Fin 28) centerNilCert_contains

end
end VOA.DeligneAudit.D4FusionContact

#print axioms VOA.DeligneAudit.D4FusionContact.centerNilCert_valid
#print axioms VOA.DeligneAudit.D4FusionContact.localWeyl_center_local_nil
