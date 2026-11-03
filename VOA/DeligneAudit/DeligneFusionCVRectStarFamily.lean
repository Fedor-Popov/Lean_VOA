import VOA.DeligneAudit.DeligneFusionCVRectStarBase
import VOA.DeligneAudit.DeligneFusionCVRectStarCount
import VOA.DeligneAudit.DeligneFusionCVRectBound

/-!
# The actual finite canonical star family

This is the commutative polynomial quotient alone. A map from mixed
CV modules to its PBW version is not assumed or supplied here.
-/

namespace VOA.DeligneAudit.A2.CVRectStarFamily

open VOA.DeligneAudit.A2.CVRectStarBase
open VOA.DeligneAudit.A2.CVRectStarIdeal
open VOA.DeligneAudit.A2.CVRectStarCount
open VOA.DeligneAudit.A2.CVRectList

noncomputable section

def ideal (L N R : ℕ) (left right center : List ℕ) : Ideal (StarRing L N R) :=
  coefficientIdeal3 (starX L N R) (starY L N R) (starZ L N R) (starOrder left right center)

abbrev Model (L N R : ℕ) (left right center : List ℕ) :=
  StarRing L N R ⧸ ideal L N R left right center

abbrev Family (left right center : List ℕ) :=
  Model left.length (left.length + right.length + center.length) right.length left right center

def baseEquiv (right center : List ℕ) :
    Family [] right center ≃ₐ[ℂ] CVRectFamily.Family right center := by
  unfold Family Model ideal
  rw [List.length_nil, Nat.zero_add]
  exact zeroLeftEquiv right center

/-- The actual no-left-site star quotient has the proved two-color
product upper bound, without a mixed CV premise. -/
theorem base_bound (right center : List ℕ) :
    FiniteDimensional ℂ (Family [] right center) ∧
      Module.finrank ℂ (Family [] right center) ≤ starWeight [] right center := by
  have hb := CVRectBound.family_bound right center
  haveI := hb.1
  let E := (baseEquiv right center).toLinearEquiv
  refine ⟨E.symm.finiteDimensional, ?_⟩
  rw [starWeight_base]
  exact E.finrank_eq.le.trans hb.2

theorem starOrder_left_perm {left left' : List ℕ} (hp : left.Perm left')
    (right center : List ℕ) : starOrder left right center = starOrder left' right center := by
  funext p q r
  simp only [starOrder, excess_perm hp]

theorem finiteDimensional_left_perm {left left' : List ℕ} (hp : left.Perm left')
    (right center : List ℕ) [FiniteDimensional ℂ (Family left right center)] :
    FiniteDimensional ℂ (Family left' right center) := by
  have hf := (inferInstance : FiniteDimensional ℂ (Family left right center))
  unfold Family Model ideal at hf ⊢
  rw [hp.length_eq.symm, starOrder_left_perm hp.symm]
  exact hf

theorem finrank_left_perm {left left' : List ℕ} (hp : left.Perm left')
    (right center : List ℕ) :
    Module.finrank ℂ (Family left right center) = Module.finrank ℂ (Family left' right center) := by
  unfold Family Model ideal
  rw [hp.length_eq, starOrder_left_perm hp]

end

end VOA.DeligneAudit.A2.CVRectStarFamily

#print axioms VOA.DeligneAudit.A2.CVRectStarFamily.base_bound
#print axioms VOA.DeligneAudit.A2.CVRectStarFamily.finiteDimensional_left_perm
#print axioms VOA.DeligneAudit.A2.CVRectStarFamily.finrank_left_perm
