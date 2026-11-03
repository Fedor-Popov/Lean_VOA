import VOA.DeligneAudit.D4FusionToroidalD4Shift

/-! The D4 Ravinder module has the toroidal associated-graded action. -/

namespace VOA.DeligneAudit.Toroidal

open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4

noncomputable section

/-- The toroidal action on the high-mode associated graded of `M_{m,0}`. -/
def grToroidal_D4 (m : ℕ) (hm : 1 ≤ m) :
    ToroidalModule D4sector.f m
      (Gr D4sector.f (ravFam D4sector m 0) m) :=
  grToroidal D4sector.f (ravFam D4sector m 0) m
    (highModeShift_D4 (ravFam D4sector m 0) m hm)

/-- Every Ravinder tail relation kills the graded generator. -/
theorem gr_tail_D4 (m : ℕ) (hm : 1 ≤ m)
    (t : List (Ltr 28)) (ht : t ∈ (ravFam D4sector m 0).tails) :
    wordOpT (grToroidal_D4 m hm) (symbolLetters m t)
      (grGenerator D4sector.f (ravFam D4sector m 0) m) = 0 :=
  gr_tail D4sector.f (ravFam D4sector m 0) m
    (highModeShift_D4 (ravFam D4sector m 0) m hm) hm t ht

end

end VOA.DeligneAudit.Toroidal

#print axioms VOA.DeligneAudit.Toroidal.grToroidal_D4
#print axioms VOA.DeligneAudit.Toroidal.gr_tail_D4
