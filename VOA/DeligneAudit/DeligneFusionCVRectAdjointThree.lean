import VOA.DeligneAudit.DeligneFusionCVRectAdjointBase
import VOA.DeligneAudit.DeligneFusionCVRectStarBound

/-!
# The actual three-dimensional adjoint polynomial branch

The extra first-color variable is eliminated by the proved phantom-variable
quotient map. Its source is an existing STAR family with one extra capacity
one on the opposite orientation. Consequently the factor three is a proved
polynomial dimension bound, with no recurrence or CV presentation premise.
-/

namespace VOA.DeligneAudit.A2.CVRectAdjointThree

open VOA.DeligneAudit.A2.CVRectStarBase VOA.DeligneAudit.A2.CVRectStarIdeal
open VOA.DeligneAudit.A2.CVRectAdjointFamily VOA.DeligneAudit.A2.CVRectAdjointOrder
open VOA.DeligneAudit.A2.CVRectAdjointBase VOA.DeligneAudit.A2.CVRectStarCount
open VOA.DeligneAudit.A2.CVRectCount

noncomputable section

/-- The primitive adjoint branch is exactly one phantom first variable over
an ordinary STAR family with one opposite capacity-one site. -/
theorem three_order (left right center : List ℕ) :
    threeSiteOrder left right center =
      fun p q r => p + starOrder left (1 :: right) center p q r := by
  funext p q r
  simp only [threeSiteOrder, threeOrder, background, starOrder,
    CVRectIntegrationOrder.excess, List.map_cons, List.sum_cons]
  omega

set_option maxHeartbeats 20000 in
-- Keep quotient-coordinate transport within a small elaboration budget.
/-- The actual primitive adjoint quotient has the unconditional factor-three
product upper bound. The quotient types are normalized before transporting
finiteness, avoiding an opaque equivalence between polynomial quotients. -/
theorem three_family_bound (left right center : List ℕ) :
    FiniteDimensional ℂ (ThreeFamily left right center) ∧
      Module.finrank ℂ (ThreeFamily left right center) ≤ 3 * starWeight left right center := by
  let μ := starOrder left (1 :: right) center
  let N := left.length + right.length + center.length + 1
  let P : ℕ → Prop := fun n =>
    FiniteDimensional ℂ (Model left.length n (right.length + 1) μ) ∧
      Module.finrank ℂ (Model left.length n (right.length + 1) μ) ≤
        starWeight left (1 :: right) center
  have hb0 : P (left.length + (right.length + 1) + center.length) :=
    CVRectStarBound.family_bound left (1 :: right) center
  have hN : left.length + (right.length + 1) + center.length = N := by dsimp [N]; omega
  have hb : P N := (congrArg P hN).mp hb0
  haveI : FiniteDimensional ℂ (Model left.length N (right.length + 1) μ) := hb.1
  let Q : (ℕ → ℕ → ℕ → ℕ) → Prop := fun τ =>
    FiniteDimensional ℂ (Model (left.length + 1) N (right.length + 1) τ) ∧
      Module.finrank ℂ (Model (left.length + 1) N (right.length + 1) τ) ≤
        Module.finrank ℂ (Model left.length N (right.length + 1) μ)
  have hp : Q (fun p q r => p + μ p q r) :=
    phantom_model_bound left.length N (right.length + 1) μ
  have hp' : Q (threeSiteOrder left right center) :=
    (congrArg Q (three_order left right center)).mpr hp
  have hw : starWeight left (1 :: right) center = 3 * starWeight left right center := by
    simp only [starWeight, List.map_cons, List.prod_cons, rectangleWeight_one]
    ring
  exact ⟨hp'.1, hp'.2.trans (hb.2.trans_eq hw)⟩

end
end VOA.DeligneAudit.A2.CVRectAdjointThree

#print axioms VOA.DeligneAudit.A2.CVRectAdjointThree.three_family_bound
