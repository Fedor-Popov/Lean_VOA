import VOA.DeligneAudit.D4FusionContactAllMCountResearchRefinedSpan

/-! # Uniform leading/lower-energy split of the actual refined wheel

The leading space has modes p,q-1,q,q. The lower space has the same
current degree and strictly lower convex energy. The fixed 44-term
coefficient vector and completeness of these reductions are not assumed.
-/

namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch

open VOA.DeligneAudit.D4FusionContact.Polynomial
open VOA.DeligneAudit.D4FusionContact.M2Certificate
open BoundaryPair

noncomputable section

variable {m : ℕ} (b : BoundaryPair m)

def leadingProduct (i j k l : Fin 9) : MvPolynomial (Vars m) ℂ :=
  modeX m i b.lower.val * modeX m j (b.top.val-1) *
    modeX m k b.top.val * modeX m l b.top.val

theorem leadingProduct_mem (i j k l : Fin 9) :
    leadingProduct b i j k l ∈ refinedLeadingSpan b :=
  Submodule.subset_span ⟨(i,j,k,l),rfl⟩

def endpointProduct (i j k l : Fin 9) : MvPolynomial (Vars m) ℂ :=
  modeX m i b.lower.val * modeX m j b.lower.val *
    (modeX m k b.top.val * modeX m l b.top.val)

theorem h0Deriv_endpointProduct (ha : b.lower.val + 1 < b.top.val) (i j k l : Fin 9) :
    g0Deriv m 0 (refinementMode b).val (endpointProduct b i j k l) =
      (h0Weight j : ℂ) • leadingProduct b i j k l +
        (h0Weight i : ℂ) • leadingProduct b j i k l := by
  rw [endpointProduct,(g0Deriv m 0 (refinementMode b).val).leibniz,
    (g0Deriv m 0 (refinementMode b).val).leibniz,
    (g0Deriv m 0 (refinementMode b).val).leibniz,
    h0Deriv_lower_mode,h0Deriv_lower_mode,
    h0Deriv_top_mode_zero b ha,h0Deriv_top_mode_zero b ha]
  simp only [leadingProduct,smul_eq_mul,mul_zero,zero_add,add_zero,Algebra.smul_def]
  ring

theorem endpointWheel_explicit : MvPolynomial.rename b.embed endpointWheel =
    endpointProduct b 5 6 1 2 + endpointProduct b 4 6 1 3 + endpointProduct b 4 5 2 3 := by
  have h3 : varIndex 3 = ((1:Fin 9),(1:Fin 2)) := by decide +kernel
  have h5 : varIndex 5 = ((2:Fin 9),(1:Fin 2)) := by decide +kernel
  have h7 : varIndex 7 = ((3:Fin 9),(1:Fin 2)) := by decide +kernel
  have h8 : varIndex 8 = ((4:Fin 9),(0:Fin 2)) := by decide +kernel
  have h10 : varIndex 10 = ((5:Fin 9),(0:Fin 2)) := by decide +kernel
  have h12 : varIndex 12 = ((6:Fin 9),(0:Fin 2)) := by decide +kernel
  simp [endpointWheel,wheelTarget,rowEval,polyWord,h3,h5,h7,h8,h10,h12,
    BoundaryPair.embed,BoundaryPair.embedMode,endpointProduct,modeX,
    b.lower.isLt,b.top.isLt]
  ring

theorem h0Deriv_endpoint_mem (ha : b.lower.val + 1 < b.top.val) :
    g0Deriv m 0 (refinementMode b).val
      (MvPolynomial.rename b.embed endpointWheel) ∈ refinedLeadingSpan b := by
  rw [endpointWheel_explicit,map_add,map_add,h0Deriv_endpointProduct b ha,
    h0Deriv_endpointProduct b ha,h0Deriv_endpointProduct b ha]
  exact (refinedLeadingSpan b).add_mem
    ((refinedLeadingSpan b).add_mem
      ((refinedLeadingSpan b).add_mem
        ((refinedLeadingSpan b).smul_mem _ (leadingProduct_mem b 5 6 1 2))
        ((refinedLeadingSpan b).smul_mem _ (leadingProduct_mem b 6 5 1 2)))
      ((refinedLeadingSpan b).add_mem
        ((refinedLeadingSpan b).smul_mem _ (leadingProduct_mem b 4 6 1 3))
        ((refinedLeadingSpan b).smul_mem _ (leadingProduct_mem b 6 4 1 3))))
    ((refinedLeadingSpan b).add_mem
      ((refinedLeadingSpan b).smul_mem _ (leadingProduct_mem b 4 5 2 3))
      ((refinedLeadingSpan b).smul_mem _ (leadingProduct_mem b 5 4 2 3)))

theorem h0Deriv_piece_middle_mem (ha : b.lower.val + 1 < b.top.val) (t : WheelPiece) :
    g0Deriv m 0 (refinementMode b).val
      (evalMap b t.expression.toWheel (middleSeed b)) ∈ RefinedSpace b := by
  cases t with
  | polar z i j l =>
      have hmiddle := evalMap_levi_middle b l .base (middleSeed b) (middleSeed_mem b)
      have hh := h0Deriv_polar_middle_mem b ha i.castSucc j.castSucc hmiddle
      have h10 : (1 : Fin 2) ≠ 0 := by decide
      have he : evalMap b (WheelPiece.polar z i j l).expression.toWheel (middleSeed b) =
          ((z:ℂ)/(1:ℂ)) • (modeX m i.castSucc b.lower.val * modeX m j.castSucc b.top.val *
            evalMap b (leviOrbit l .base).toWheel (middleSeed b)) := by
        simp only [WheelPiece.expression,IntegerExpr.toWheel,evalMap,LinearMap.smul_apply,
          LinearMap.comp_apply,LinearMap.mulLeft_apply,variable_flatten,
          BoundaryPair.embed,BoundaryPair.embedMode,h10,Int.cast_one,Fin.isValue,
          if_true,if_false,modeX,dif_pos b.lower.isLt,dif_pos b.top.isLt,mul_assoc]
      rw [he,Derivation.map_smul]
      exact (RefinedSpace b).smul_mem _ hh
  | square z i j l =>
      have hzero := evalMap_levi_zero b l (.deriv 3 .base) (middleSeed b)
        (evalMap_square_middle_zero b)
      have he : evalMap b (WheelPiece.square z i j l).expression.toWheel (middleSeed b) = 0 := by
        simp only [WheelPiece.expression,IntegerExpr.toWheel,evalMap,
          LinearMap.smul_apply,LinearMap.comp_apply,LinearMap.mulLeft_apply,
          hzero,mul_zero,smul_zero]
      rw [he,map_zero]
      exact (RefinedSpace b).zero_mem

theorem h0Deriv_pieces_middle_mem (ha : b.lower.val + 1 < b.top.val) (l : List WheelPiece) :
    g0Deriv m 0 (refinementMode b).val
      (evalMap b (piecesExpression l).toWheel (middleSeed b)) ∈ RefinedSpace b := by
  induction l with
  | nil =>
      simp only [piecesExpression,List.map_nil,List.foldr_nil,IntegerExpr.toWheel,
        evalMap,Int.cast_zero,zero_div,zero_smul,LinearMap.zero_apply,map_zero]
      exact (RefinedSpace b).zero_mem
  | cons t l ih =>
      change g0Deriv m 0 (refinementMode b).val
        (evalMap b (.plus t.expression.toWheel (piecesExpression l).toWheel)
          (middleSeed b)) ∈ _
      rw [evalMap,LinearMap.add_apply,map_add]
      exact (RefinedSpace b).add_mem (h0Deriv_piece_middle_mem b ha t) ih

theorem h0Deriv_currentWheel_mem (ha : b.lower.val + 1 < b.top.val) :
    g0Deriv m 0 (refinementMode b).val (currentWheel b) ∈ RefinedSpace b := by
  rw [currentWheel_split,map_add]
  apply Submodule.add_mem
  · exact Submodule.mem_sup_left (h0Deriv_endpoint_mem b ha)
  · simp only [wheelExpression,evalMap,LinearMap.smul_apply,Derivation.map_smul]
    exact (RefinedSpace b).smul_mem _ (h0Deriv_pieces_middle_mem b ha wheelPieces)

/-- For nonadjacent endpoints the actual refined source relation splits
into the stated leading mode pattern and strictly lower energy. -/
theorem refinedWheel_mem (ha : b.lower.val + 1 < b.top.val) :
    refinedWheel b ∈ RefinedSpace b := by
  have hn : ¬ b.lower.val + 1 = b.top.val := by omega
  rw [refinedWheel,if_neg hn]
  exact h0Deriv_currentWheel_mem b ha

end

#print axioms h0Deriv_currentWheel_mem
#print axioms refinedWheel_mem

end VOA.DeligneAudit.D4FusionContact.AllMCountResearch
