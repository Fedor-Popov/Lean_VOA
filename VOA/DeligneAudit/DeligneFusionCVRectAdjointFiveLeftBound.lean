import VOA.DeligneAudit.DeligneFusionCVRectAdjointFiveLeftCount
import VOA.DeligneAudit.DeligneFusionCVRectAdjointFiveBound

/-!
# Unconditional five-family product bound with arbitrary ordinary left sites

The actual left primitive/shift quotient maps and zero-site elimination are
combined with the proved five-tail base. No base count, recurrence, ideal
inclusion, or original finite-dimensionality is assumed by the final theorem.
-/

namespace VOA.DeligneAudit.A2.CVRectAdjointFiveLeft

open VOA.DeligneAudit.A2.CVRectAdjointFamily
open VOA.DeligneAudit.A2.CVRectStarCount

noncomputable section

/-- The actual FiveFamily quotient is finite-dimensional with its sharp
five-times-rectangular product upper bound, without mathematical premises. -/
theorem five_family_bound (left right center : List ℕ) :
    FiniteDimensional ℂ (FiveFamily left right center) ∧
      Module.finrank ℂ (FiveFamily left right center) ≤ 5 * starWeight left right center :=
  five_family_bound_of_base
    (fun right center => CVRectAdjointFiveBound.five_base_bound right center)
    left right center

end

end VOA.DeligneAudit.A2.CVRectAdjointFiveLeft

#print axioms VOA.DeligneAudit.A2.CVRectAdjointFiveLeft.five_family_bound
