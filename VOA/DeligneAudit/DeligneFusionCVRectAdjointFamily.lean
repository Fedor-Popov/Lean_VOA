import VOA.DeligneAudit.DeligneFusionCVRectAdjointOrder
import VOA.DeligneAudit.DeligneFusionCVRectStarBase

/-! # Concrete finite polynomial families with an adjoint FFLV site -/

namespace VOA.DeligneAudit.A2.CVRectAdjointFamily

open VOA.DeligneAudit.A2.CVRectStarBase
open VOA.DeligneAudit.A2.CVRectStarIdeal
open VOA.DeligneAudit.A2.CVRectAdjointOrder

noncomputable section

def ideal (L N R : ℕ) (μ : ℕ → ℕ → ℕ → ℕ) : Ideal (StarRing L N R) :=
  coefficientIdeal3 (starX L N R) (starY L N R) (starZ L N R) μ

abbrev Model (L N R : ℕ) (μ : ℕ → ℕ → ℕ → ℕ) :=
  StarRing L N R ⧸ ideal L N R μ

abbrev AdjointFamily (left right center : List ℕ) :=
  Model (left.length + 1) (left.length + right.length + center.length + 1)
    (right.length + 1) (adjointOrder left right center)

abbrev FiveFamily (left right center : List ℕ) :=
  Model left.length (left.length + right.length + center.length + 1)
    (right.length + 1) (fiveSiteOrder left right center)

/-- The primitive branch still retains a phantom x-variable. Its zero
capacity is eliminated by an actual quotient map in the base stage. -/
abbrev ThreeFamily (left right center : List ℕ) :=
  Model (left.length + 1) (left.length + right.length + center.length + 1)
    (right.length + 1) (threeSiteOrder left right center)

end
end VOA.DeligneAudit.A2.CVRectAdjointFamily
