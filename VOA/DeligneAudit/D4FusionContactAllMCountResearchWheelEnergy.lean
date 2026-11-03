import VOA.DeligneAudit.D4FusionContactAllMCountResearchEnergy

/-! # The corrected-current wheel has strict lower energy

Every correction has degree four and the same current degree as the
endpoint wheel, but strictly lower convex mode energy. This verifies
one uniform straightening relation; it does not claim completeness or
termination of any global normal form.
-/

namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch

open VOA.DeligneAudit.D4FusionContact.Polynomial
open VOA.DeligneAudit.D4FusionContact.M2Certificate
open BoundaryPair

noncomputable section

variable {m : ℕ} (b : BoundaryPair m)

theorem evalMap_levi_zero (l : List (Fin 3)) (e : IntegerExpr)
    (p : MvPolynomial (Vars m) ℂ) (hp : evalMap b e.toWheel p = 0) :
    evalMap b (leviOrbit l e).toWheel p = 0 := by
  induction l with
  | nil => exact hp
  | cons i l ih =>
      change evalMap b (.deriv (leviIndex i) (leviOrbit l e).toWheel) p = _
      rw [evalMap_levi_step,ih,map_zero]

theorem piece_middle_energy (t : WheelPiece) :
    evalMap b t.expression.toWheel (middleSeed b) ∈ energySpan b := by
  cases t with
  | polar z i j l =>
      have hmiddle := evalMap_levi_middle b l .base (middleSeed b) (middleSeed_mem b)
      have he := endpoint_middle_mem b i.castSucc j.castSucc hmiddle
      have h10 : (1 : Fin 2) ≠ 0 := by decide
      simpa only [WheelPiece.expression,IntegerExpr.toWheel,evalMap,
        LinearMap.smul_apply,LinearMap.comp_apply,LinearMap.mulLeft_apply,
        variable_flatten,BoundaryPair.embed,BoundaryPair.embedMode,
        h10,Int.cast_one,Fin.isValue,if_true,if_false,mul_assoc] using
          (energySpan b).smul_mem ((z:ℂ)/(1:ℂ)) he
  | square z i j l =>
      have hzero := evalMap_levi_zero b l (.deriv 3 .base) (middleSeed b)
        (evalMap_square_middle_zero b)
      simp only [WheelPiece.expression,IntegerExpr.toWheel,evalMap,
        LinearMap.smul_apply,LinearMap.comp_apply,LinearMap.mulLeft_apply,
        hzero,mul_zero,smul_zero]
      exact (energySpan b).zero_mem

theorem pieces_middle_energy (l : List WheelPiece) :
    evalMap b (piecesExpression l).toWheel (middleSeed b) ∈ energySpan b := by
  induction l with
  | nil =>
      simp only [piecesExpression,List.map_nil,List.foldr_nil,IntegerExpr.toWheel,
        evalMap,Int.cast_zero,zero_div,zero_smul]
      exact (energySpan b).zero_mem
  | cons t l ih =>
      change evalMap b (.plus t.expression.toWheel (piecesExpression l).toWheel)
        (middleSeed b) ∈ _
      exact (energySpan b).add_mem (piece_middle_energy b t) ih

/-- All corrections lie in the actual strict-energy subspace. -/
theorem currentWheel_error_energy :
    evalMap b wheelExpression (middleSeed b) ∈ energySpan b := by
  simp only [wheelExpression,evalMap,LinearMap.smul_apply]
  exact (energySpan b).smul_mem _ (pieces_middle_energy b wheelPieces)

theorem currentWheel_sub_endpoint_energy :
    currentWheel b - MvPolynomial.rename b.embed endpointWheel ∈ energySpan b := by
  rw [currentWheel_split,add_sub_cancel_left]
  exact currentWheel_error_energy b

/-- Actual uniform endpoint straightening modulo the source ideal and
strictly lower energy. The source ideal has all coefficient multiplicities. -/
theorem endpointWheel_mem_candidate_sup_energy :
    MvPolynomial.rename b.embed endpointWheel ∈
      (Polynomial.AllM.candidateIdeal m).restrictScalars ℂ ⊔ energySpan b := by
  have hsource : currentWheel b ∈
      (Polynomial.AllM.candidateIdeal m).restrictScalars ℂ ⊔ energySpan b :=
    Submodule.mem_sup_left (currentWheel_mem_candidate b)
  have herror : evalMap b wheelExpression (middleSeed b) ∈
      (Polynomial.AllM.candidateIdeal m).restrictScalars ℂ ⊔ energySpan b :=
    Submodule.mem_sup_right (currentWheel_error_energy b)
  have hh := Submodule.sub_mem _ hsource herror
  rw [currentWheel_split,add_sub_cancel_right] at hh
  exact hh

/-- With no middle modes, the endpoint wheel itself is an actual relation. -/
theorem middleSpan_eq_bot_of_adjacent (ha : b.lower.val + 1 = b.top.val) :
    middleSpan b = ⊥ := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨z,rfl⟩
    have := z.left_lower
    have := z.left_upper
    omega
  · exact bot_le

theorem adjacent_endpointWheel_mem_candidate (ha : b.lower.val + 1 = b.top.val) :
    MvPolynomial.rename b.embed endpointWheel ∈ Polynomial.AllM.candidateIdeal m := by
  have hm := middleSeed_mem b
  rw [middleSpan_eq_bot_of_adjacent b ha,Submodule.mem_bot] at hm
  have he : currentWheel b = MvPolynomial.rename b.embed endpointWheel := by
    rw [currentWheel_split,hm,map_zero,add_zero]
  rw [← he]
  exact currentWheel_mem_candidate b

end

#print axioms currentWheel_error_energy
#print axioms currentWheel_sub_endpoint_energy
#print axioms endpointWheel_mem_candidate_sup_energy
#print axioms adjacent_endpointWheel_mem_candidate

end VOA.DeligneAudit.D4FusionContact.AllMCountResearch
