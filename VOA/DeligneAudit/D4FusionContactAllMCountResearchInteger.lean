import VOA.DeligneAudit.D4FusionContactAllMCountResearchExpression

/-! # Integer word checks for short differential expressions

Closed checks run on finite integer word rows. Their equality is then
transported symbolically to the actual complex polynomial derivations.
-/

namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch

open VOA.DeligneAudit.D4FusionContact.Polynomial
open VOA.DeligneAudit.D4FusionContact.M2Certificate

noncomputable section

inductive IntegerExpr where
  | base
  | plus (a b : IntegerExpr)
  | scale (z : ℤ) (a : IntegerExpr)
  | mul (v : Fin 18) (a : IntegerExpr)
  | deriv (d : Fin 36) (a : IntegerExpr)

def IntegerExpr.toWheel : IntegerExpr → WheelExpr
  | .base => .base
  | .plus a b => .plus a.toWheel b.toWheel
  | .scale z a => .scale z 1 a.toWheel
  | .mul v a => .mul v a.toWheel
  | .deriv d a => .deriv d a.toWheel

def IntegerExpr.words : IntegerExpr → WordRow
  | .base => [([0,1],1)]
  | .plus a b => a.words ++ b.words
  | .scale z a => scaleRow z a.words
  | .mul v a => multiplyRow v a.words
  | .deriv d a => differentiateRow (images d) a.words

/-- Exact polynomial semantics of the finite integer checker. -/
theorem integerExpr_semantics (e : IntegerExpr) :
    twoEvalMap e.toWheel twoSeed = rowEval varIndex e.words := by
  induction e with
  | base => simp [IntegerExpr.toWheel,IntegerExpr.words,twoEvalMap,twoSeed,rowEval,
      polyWord,varIndex]
  | plus a b iha ihb =>
      simp only [IntegerExpr.toWheel,IntegerExpr.words,twoEvalMap,LinearMap.add_apply,
        rowEval_append,iha,ihb]
  | scale z a ih =>
      simp only [IntegerExpr.toWheel, IntegerExpr.words, twoEvalMap,
        Int.cast_one, div_one]
      rw [LinearMap.smul_apply, ih, rowEval_scale, Int.cast_smul_eq_zsmul]
  | mul v a ih =>
      simp only [IntegerExpr.toWheel,IntegerExpr.words,twoEvalMap,LinearMap.comp_apply,
        LinearMap.mulLeft_apply,rowEval_multiply,ih]
      exact mul_comm _ _
  | deriv d a ih =>
      simp only [IntegerExpr.toWheel,IntegerExpr.words,twoEvalMap,LinearMap.comp_apply,
        Derivation.coeFn_coe,rowEval_images,ih]

end
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch

#print axioms VOA.DeligneAudit.D4FusionContact.AllMCountResearch.integerExpr_semantics
