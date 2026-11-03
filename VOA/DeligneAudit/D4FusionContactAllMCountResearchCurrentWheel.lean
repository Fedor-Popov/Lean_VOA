import VOA.DeligneAudit.D4FusionContactAllMCountResearchWheelData

/-! # The uniform corrected-current wheel is an actual source relation

The short integer identity checks the two endpoint expression. Its
transport acts on the whole grouped quadratic coefficient, so all middle
current modes are retained. No all-m spanning or sharp count is asserted.
-/

namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch

open VOA.DeligneAudit.D4FusionContact.Polynomial
open VOA.DeligneAudit.D4FusionContact.M2Certificate
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.DeligneSector
open VOA.DeligneAudit.DeligneSector.D4

noncomputable section

/-- The clean two-mode wheel, prior to inserting middle-mode corrections. -/
def endpointWheel : MvPolynomial (Vars 2) ℂ := rowEval varIndex wheelTarget

def wheelExpression : WheelExpr := .scale 1 32 integerWheel.toWheel

/-- Exact finite integer cancellation, interpreted by actual derivations. -/
theorem wheelExpression_endpoint : twoEvalMap wheelExpression twoSeed = endpointWheel := by
  have hz := rowEval_eq_zero_of_collect varIndex _ integerWheel_check
  rw [rowEval_append, rowEval_scale] at hz
  have he : rowEval varIndex integerWheel.words = (32 : ℤ) • endpointWheel := by
    apply eq_of_sub_eq_zero
    simpa only [endpointWheel, sub_eq_add_neg, neg_smul] using hz
  simp only [wheelExpression, twoEvalMap, LinearMap.smul_apply,
    integerExpr_semantics, he]
  rw [← Int.cast_smul_eq_zsmul ℂ (32 : ℤ), smul_smul]
  norm_num

variable {m : ℕ} (b : BoundaryPair m)

/-- The source relation with every grouped middle-mode correction intact. -/
def currentWheel : MvPolynomial (Vars m) ℂ := corrected b wheelExpression

theorem currentWheel_mem_candidate : currentWheel b ∈ Polynomial.AllM.candidateIdeal m :=
  corrected_mem b wheelExpression

theorem currentWheel_mem_model : currentWheel b ∈ Polynomial.AllM.modelIdeal m :=
  (show Polynomial.AllM.candidateIdeal m ≤ Polynomial.AllM.modelIdeal m from
    le_sup_left) (currentWheel_mem_candidate b)

/-- The endpoint wheel is not asserted to vanish by itself. -/
theorem currentWheel_split : currentWheel b =
    MvPolynomial.rename b.embed endpointWheel + evalMap b wheelExpression (middleSeed b) := by
  simpa only [currentWheel, wheelExpression_endpoint] using corrected_split b wheelExpression

variable {V : Type} [AddCommGroup V] [Module ℂ V]
    (R : CurrentModule contactF V) (w : V)

theorem currentWheel_mem_ann (h : LocalWeylRelG D4sector R w m) :
    currentWheel b ∈ annIdeal R w (modeLetter m) := by
  have hm : 1 ≤ m := by have := b.top.isLt; omega
  exact Polynomial.AllM.source_candidateIdeal_le_ann hm h (currentWheel_mem_candidate b)

end
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch

#print axioms VOA.DeligneAudit.D4FusionContact.AllMCountResearch.wheelExpression_endpoint
#print axioms VOA.DeligneAudit.D4FusionContact.AllMCountResearch.currentWheel_mem_candidate
#print axioms VOA.DeligneAudit.D4FusionContact.AllMCountResearch.currentWheel_split
#print axioms VOA.DeligneAudit.D4FusionContact.AllMCountResearch.currentWheel_mem_ann
