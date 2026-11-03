import VOA.DeligneAudit.D4FusionContactAllMCountResearchRefinedEnergy
import VOA.DeligneAudit.D4FusionContactAllMCountResearchBilinearBoundary

/-! An explicit finite-color leading term of each whole middle correction.
The remainder belongs to the actual strict lower-energy span. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch

open VOA.DeligneAudit.D4FusionContact.Polynomial
open VOA.DeligneAudit.D4FusionContact.M2Certificate
open BoundaryPair

noncomputable section
variable {m : ℕ} (b : BoundaryPair m)

def polarLeading (i j : Fin 9) (l : List (Fin 3)) : MvPolynomial (Vars m) ℂ :=
  modeX m i b.lower.val * modeX m j b.top.val *
    MvPolynomial.rename (nearestPair b).embed
      (middleBoundaryMap (twoEvalMap (leviOrbit l .base).toWheel twoSeed))

/-- Differentiate the entire relation before taking its leading part. -/
theorem polar_middle_sub_leading_mem (ha : b.lower.val + 1 < b.top.val)
    (i j : Fin 9) (l : List (Fin 3)) :
    g0Deriv m 0 (refinementMode b).val
      (modeX m i b.lower.val * modeX m j b.top.val *
        evalMap b (leviOrbit l .base).toWheel (middleSeed b)) -
      polarLeading b i j l ∈ refinedLowSpan b := by
  rw [(g0Deriv m 0 (refinementMode b).val).leibniz,
    (g0Deriv m 0 (refinementMode b).val).leibniz,
    h0Deriv_lower_mode,h0Deriv_top_mode_zero b ha,
    leviOrbit_middle_boundary b ha]
  have hmiddle := evalMap_levi_middle b l .base (middleSeed b) (middleSeed_mem b)
  have hh := (refinedLowSpan b).smul_mem (h0Weight i : ℂ)
    (low_endpoint_middle_mem b i j hmiddle)
  convert hh using 1
  simp only [polarLeading,Algebra.smul_def,Algebra.algebraMap_self_apply]
  ring

def pieceLeading : WheelPiece → MvPolynomial (Vars m) ℂ
  | .polar z i j l => (z : ℂ) • polarLeading b i.castSucc j.castSucc l
  | .square _ _ _ _ => 0

theorem piece_middle_sub_leading_mem (ha : b.lower.val + 1 < b.top.val)
    (t : WheelPiece) :
    g0Deriv m 0 (refinementMode b).val
      (evalMap b t.expression.toWheel (middleSeed b)) - pieceLeading b t ∈
        refinedLowSpan b := by
  cases t with
  | polar z i j l =>
      have h10 : (1 : Fin 2) ≠ 0 := by decide
      have he : evalMap b (WheelPiece.polar z i j l).expression.toWheel (middleSeed b) =
          (z : ℂ) • (modeX m i.castSucc b.lower.val * modeX m j.castSucc b.top.val *
            evalMap b (leviOrbit l .base).toWheel (middleSeed b)) := by
        simp only [WheelPiece.expression,IntegerExpr.toWheel,evalMap,LinearMap.smul_apply,
          LinearMap.comp_apply,LinearMap.mulLeft_apply,variable_flatten,
          BoundaryPair.embed,BoundaryPair.embedMode,h10,Int.cast_one,Fin.isValue,
          if_true,if_false,modeX,dif_pos b.lower.isLt,dif_pos b.top.isLt,mul_assoc,
          div_one]
      rw [he,Derivation.map_smul]
      change (z : ℂ) • _ - (z : ℂ) • _ ∈ refinedLowSpan b
      rw [← smul_sub]
      exact (refinedLowSpan b).smul_mem _
        (polar_middle_sub_leading_mem b ha i.castSucc j.castSucc l)
  | square z i j l =>
      have hzero := evalMap_levi_zero b l (.deriv 3 .base) (middleSeed b)
        (evalMap_square_middle_zero b)
      have he : evalMap b (WheelPiece.square z i j l).expression.toWheel (middleSeed b) = 0 := by
        simp only [WheelPiece.expression,IntegerExpr.toWheel,evalMap,
          LinearMap.smul_apply,LinearMap.comp_apply,LinearMap.mulLeft_apply,
          hzero,mul_zero,smul_zero]
      rw [he,map_zero]
      simpa only [pieceLeading,sub_zero] using (refinedLowSpan b).zero_mem


def piecesLeading (b : BoundaryPair m) : List WheelPiece → MvPolynomial (Vars m) ℂ
  | [] => 0
  | t :: l => pieceLeading b t + piecesLeading b l

theorem pieces_middle_sub_leading_mem (ha : b.lower.val + 1 < b.top.val)
    (l : List WheelPiece) :
    g0Deriv m 0 (refinementMode b).val
      (evalMap b (piecesExpression l).toWheel (middleSeed b)) - piecesLeading b l ∈
        refinedLowSpan b := by
  induction l with
  | nil =>
      simp only [piecesExpression,List.map_nil,List.foldr_nil,IntegerExpr.toWheel,
        evalMap,Int.cast_zero,zero_div,zero_smul,LinearMap.zero_apply,map_zero,
        piecesLeading,sub_zero]
      exact (refinedLowSpan b).zero_mem
  | cons t l ih =>
      change g0Deriv m 0 (refinementMode b).val
        (evalMap b (.plus t.expression.toWheel (piecesExpression l).toWheel)
          (middleSeed b)) - (pieceLeading b t + piecesLeading b l) ∈ _
      rw [evalMap,LinearMap.add_apply,map_add]
      convert (refinedLowSpan b).add_mem (piece_middle_sub_leading_mem b ha t) ih using 1
      module

def endpointLeading : MvPolynomial (Vars m) ℂ :=
  ((h0Weight 6 : ℂ) • leadingProduct b 5 6 1 2 +
    (h0Weight 5 : ℂ) • leadingProduct b 6 5 1 2) +
  ((h0Weight 6 : ℂ) • leadingProduct b 4 6 1 3 +
    (h0Weight 4 : ℂ) • leadingProduct b 6 4 1 3) +
  ((h0Weight 5 : ℂ) • leadingProduct b 4 5 2 3 +
    (h0Weight 4 : ℂ) • leadingProduct b 5 4 2 3)

theorem endpointLeading_eq (ha : b.lower.val + 1 < b.top.val) :
    g0Deriv m 0 (refinementMode b).val
      (MvPolynomial.rename b.embed endpointWheel) = endpointLeading b := by
  rw [endpointWheel_explicit,map_add,map_add,h0Deriv_endpointProduct b ha,
    h0Deriv_endpointProduct b ha,h0Deriv_endpointProduct b ha]
  rfl

def refinedLeading : MvPolynomial (Vars m) ℂ :=
  endpointLeading b + (1/32 : ℂ) • piecesLeading b wheelPieces

/-- Uniform explicit color formula for the leading part of the actual source relation. -/
theorem currentWheel_sub_refinedLeading_mem (ha : b.lower.val + 1 < b.top.val) :
    g0Deriv m 0 (refinementMode b).val (currentWheel b) - refinedLeading b ∈
      refinedLowSpan b := by
  rw [currentWheel_split,map_add,endpointLeading_eq b ha]
  simp only [wheelExpression,evalMap,LinearMap.smul_apply,Derivation.map_smul,
    integerWheel,Int.cast_one]
  change endpointLeading b + (1/32 : ℂ) • _ -
    (endpointLeading b + (1/32 : ℂ) • piecesLeading b wheelPieces) ∈ _
  convert (refinedLowSpan b).smul_mem (1/32 : ℂ)
    (pieces_middle_sub_leading_mem b ha wheelPieces) using 1
  module

theorem refinedWheel_sub_refinedLeading_mem (ha : b.lower.val + 1 < b.top.val) :
    refinedWheel b - refinedLeading b ∈ refinedLowSpan b := by
  have hn : ¬ b.lower.val + 1 = b.top.val := by omega
  rw [refinedWheel,if_neg hn]
  exact currentWheel_sub_refinedLeading_mem b ha


/-- The explicit leading polynomial is a genuine source reduction modulo
strictly lower energy. No completeness or normal-count premise is used. -/
theorem refinedLeading_mem_candidate_sup_low (ha : b.lower.val + 1 < b.top.val) :
    refinedLeading b ∈ (Polynomial.AllM.candidateIdeal m).restrictScalars ℂ ⊔
      refinedLowSpan b := by
  have hsource : refinedWheel b ∈
      (Polynomial.AllM.candidateIdeal m).restrictScalars ℂ ⊔ refinedLowSpan b :=
    Submodule.mem_sup_left (refinedWheel_mem_candidate b)
  have herror : refinedWheel b - refinedLeading b ∈
      (Polynomial.AllM.candidateIdeal m).restrictScalars ℂ ⊔ refinedLowSpan b :=
    Submodule.mem_sup_right (refinedWheel_sub_refinedLeading_mem b ha)
  have hh := Submodule.sub_mem _ hsource herror
  rw [sub_sub_cancel] at hh
  exact hh

end
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch

#print axioms VOA.DeligneAudit.D4FusionContact.AllMCountResearch.polar_middle_sub_leading_mem
#print axioms VOA.DeligneAudit.D4FusionContact.AllMCountResearch.piece_middle_sub_leading_mem

#print axioms VOA.DeligneAudit.D4FusionContact.AllMCountResearch.refinedWheel_sub_refinedLeading_mem

#print axioms VOA.DeligneAudit.D4FusionContact.AllMCountResearch.refinedLeading_mem_candidate_sup_low
