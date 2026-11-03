import VOA.DeligneAudit.D4FusionContactAllMCountResearchColorFormula

/-! Exact 44-term finite leading polynomial, checked by integer cancellation. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch
open VOA.DeligneAudit.D4FusionContact.Polynomial
noncomputable section

-- Candidate coefficients from AllMCountResearchCartanLeading.json, scaled by64.
-- The following kernel cancellation independently verifies the candidate.
def colorTargetRow : Rows.Row 27 :=
  [([0,5,19,23],-32),
    ([0,5,20,22],-32),
    ([0,8,16,23],-32),
    ([0,8,17,22],-32),
    ([0,11,13,23],-32),
    ([0,11,14,22],32),
    ([1,3,20,23],-32),
    ([1,5,18,23],-32),
    ([1,5,20,21],32),
    ([1,8,17,21],-32),
    ([1,11,14,21],32),
    ([1,12,17,20],-32),
    ([1,14,15,20],-32),
    ([2,3,19,23],32),
    ([2,4,18,23],-32),
    ([2,5,19,21],-32),
    ([2,7,17,21],-32),
    ([2,10,14,21],-32),
    ([2,12,17,19],32),
    ([2,14,15,19],32),
    ([3,7,11,23],32),
    ([3,8,10,23],-32),
    ([4,6,17,20],32),
    ([4,9,14,20],-32),
    ([5,6,16,20],-32),
    ([5,7,11,21],-32),
    ([5,7,15,20],-32),
    ([5,8,10,21],32),
    ([5,8,15,19],-32),
    ([5,8,16,18],-64),
    ([5,9,13,20],-32),
    ([5,10,12,20],-32),
    ([5,11,12,19],-96),
    ([5,11,13,18],64),
    ([6,10,14,17],-32),
    ([6,11,14,16],-32),
    ([7,9,14,17],-32),
    ([7,11,12,17],32),
    ([7,11,14,15],32),
    ([8,9,13,17],-32),
    ([8,10,12,17],-96),
    ([8,10,14,15],-32),
    ([8,11,12,16],-128),
    ([8,11,13,15],64)]

theorem colorTargetRow_length : colorTargetRow.length = 44 := by decide +kernel

theorem colorFormulaRow_check :
    Rows.collect (colorFormulaRow ++ Rows.scale (-1) colorTargetRow) = [] := by
  decide +kernel

variable {m : ℕ} (b : BoundaryPair m)

theorem colorFormulaRow_eq_target :
    Rows.eval (colorValue b) colorFormulaRow = Rows.eval (colorValue b) colorTargetRow := by
  have hh := Rows.eval_zero_of_collect (colorValue b)
    (colorFormulaRow ++ Rows.scale (-1) colorTargetRow) colorFormulaRow_check
  rw [Rows.eval_append,Rows.eval_scale] at hh
  simpa only [neg_one_zsmul,add_neg_eq_zero] using hh

/-- The exact literal polynomial, including its rational coefficients. -/
def literalLeading : MvPolynomial (Vars m) ℂ :=
  (1/64:ℂ) • Rows.eval (colorValue b) colorTargetRow

theorem refinedLeading_eq_literal : refinedLeading b = literalLeading b := by
  have hh := colorFormulaRow_eq_target b
  rw [colorFormulaRow_eval] at hh
  have he := congrArg (fun p => (1/64:ℂ) • p) hh
  simpa only [smul_smul,one_div_mul_cancel (by norm_num : (64:ℂ) ≠ 0),one_smul,
    literalLeading] using he

/-- The whole actual relation has exactly this literal leading polynomial. -/
theorem refinedWheel_sub_literal_mem (ha : b.lower.val + 1 < b.top.val) :
    refinedWheel b - literalLeading b ∈ refinedLowSpan b := by
  rw [← refinedLeading_eq_literal]
  exact refinedWheel_sub_refinedLeading_mem b ha

theorem literalLeading_mem_candidate_sup_low (ha : b.lower.val + 1 < b.top.val) :
    literalLeading b ∈ (Polynomial.AllM.candidateIdeal m).restrictScalars ℂ ⊔
      refinedLowSpan b := by
  rw [← refinedLeading_eq_literal]
  exact refinedLeading_mem_candidate_sup_low b ha

end
#print axioms refinedWheel_sub_literal_mem
#print axioms literalLeading_mem_candidate_sup_low
#print axioms colorFormulaRow_check
#print axioms refinedLeading_eq_literal
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch
