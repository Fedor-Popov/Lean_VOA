import VOA.DeligneAudit.D4FusionContactAllMCountResearchBilinearBoundary
import VOA.DeligneAudit.D4FusionContactAllMCountResearchRows

/-! # Exact integer semantics of the finite bilinear color operator -/

namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch

open VOA.DeligneAudit.D4FusionContact.Polynomial
open VOA.DeligneAudit.D4FusionContact.M2Certificate

noncomputable section

def lowerWordImages : WordImages := fun v =>
  if (varIndex v).2=0 then [(v,h0Weight (varIndex v).1)] else []

def swapWord (v : Fin 18) : Fin 18 :=
  flatten (varIndex v).1 (if (varIndex v).2=0 then 1 else 0)

def swapRow (r : WordRow) : WordRow := Rows.map swapWord r

/-- Twice the exact finite-color boundary operator, as integer words. -/
def boundaryRow (r : WordRow) : WordRow :=
  differentiateRow (images 0) r ++ scaleRow (-2) (differentiateRow lowerWordImages r) ++
    swapRow (differentiateRow (images 0) r)

theorem lowerWordImages_X (v : Fin 18) :
    imageEval varIndex (lowerWordImages v) = lowerH (MvPolynomial.X (varIndex v)) := by
  simp only [lowerWordImages,lowerH,MvPolynomial.mkDerivation_X]
  split_ifs
  · simp only [imageEval,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      add_zero,Int.cast_smul_eq_zsmul]
  · rfl

theorem rowEval_lowerH (r : WordRow) :
    rowEval varIndex (differentiateRow lowerWordImages r) = lowerH (rowEval varIndex r) :=
  rowEval_differentiateRow varIndex lowerWordImages lowerH lowerWordImages_X r

theorem swapWord_X (v : Fin 18) :
    MvPolynomial.X (varIndex (swapWord v)) =
      swapModesAlg (MvPolynomial.X (varIndex v)) := by
  simp only [swapWord,variable_flatten,swapModesAlg,MvPolynomial.rename_X,swapModes]

theorem polyWord_swap (w : Word) :
    polyWord ((w.map swapWord).map varIndex) = swapModesAlg (polyWord (w.map varIndex)) := by
  induction w with
  | nil => simp only [List.map_nil,polyWord,List.prod_nil,map_one]
  | cons v w ih =>
      change MvPolynomial.X (varIndex (swapWord v)) * polyWord ((w.map swapWord).map varIndex) =
        swapModesAlg (MvPolynomial.X (varIndex v) * polyWord (w.map varIndex))
      rw [map_mul,swapWord_X,ih]

theorem rowEval_swap (r : WordRow) :
    rowEval varIndex (swapRow r) = swapModesAlg (rowEval varIndex r) := by
  induction r with
  | nil => simp only [swapRow,Rows.map,List.map_nil,rowEval_nil,map_zero]
  | cons x r ih =>
      change x.2 • polyWord ((x.1.map swapWord).map varIndex) + rowEval varIndex (swapRow r) =
        swapModesAlg (x.2 • polyWord (x.1.map varIndex) + rowEval varIndex r)
      rw [map_add,map_zsmul,polyWord_swap,ih]

theorem rowEval_fullH (r : WordRow) :
    rowEval varIndex (differentiateRow (images 0) r) = g0Deriv 2 0 0 (rowEval varIndex r) := by
  simpa only [Polynomial.candidateDeriv,derivationIndex,Fin.isValue,ite_true,
    Nat.zero_div,Nat.zero_mod,Fin.val_zero] using rowEval_images 0 r

/-- The finite integer checker compiles the actual complex color operator. -/
theorem rowEval_boundary (r : WordRow) :
    rowEval varIndex (boundaryRow r) = (2:ℂ) • middleBoundaryMap (rowEval varIndex r) := by
  rw [boundaryRow,rowEval_append,rowEval_append,rowEval_scale,rowEval_lowerH,
    rowEval_swap,rowEval_fullH]
  change g0Deriv 2 0 0 (rowEval varIndex r) + (-2:ℤ) • lowerH (rowEval varIndex r) +
    swapModesAlg (g0Deriv 2 0 0 (rowEval varIndex r)) =
    (2:ℂ) • ((1/2:ℂ) • (g0Deriv 2 0 0 (rowEval varIndex r) -
      (2:ℂ) • lowerH (rowEval varIndex r) + swapModesAlg (g0Deriv 2 0 0 (rowEval varIndex r))))
  rw [← Int.cast_smul_eq_zsmul ℂ (-2:ℤ)]
  norm_num only [Int.cast_neg,Int.cast_ofNat]
  module

theorem rows_eval18 (r : WordRow) :
    Rows.eval (fun v => MvPolynomial.X (varIndex v)) r = rowEval varIndex r := by
  simp only [Rows.eval,Rows.wordEval,rowEval,polyWord,List.map_map,Function.comp_def]

/-- Near modes0,1 become fixed modes1,2 in the finite three-mode color ring. -/
def nearColorIndex (v : Fin 18) : Fin 27 :=
  ⟨3*(varIndex v).1.val+(varIndex v).2.val+1,by
    have h0 := (varIndex v).1.isLt
    have h1 := (varIndex v).2.isLt
    omega⟩

def colorIndex (v : Fin 27) : Vars 3 :=
  (⟨v.val/3,by omega⟩,⟨v.val%3,by omega⟩)

def nearColorEmbed (x : Vars 2) : Vars 3 :=
  (x.1,⟨x.2.val+1,by have := x.2.isLt; omega⟩)

theorem colorIndex_near (v : Fin 18) :
    colorIndex (nearColorIndex v) = nearColorEmbed (varIndex v) := by
  apply Prod.ext <;> apply Fin.ext <;> simp only [colorIndex,nearColorIndex,nearColorEmbed]
  all_goals have := (varIndex v).2.isLt; omega

end

#print axioms rowEval_boundary

end VOA.DeligneAudit.D4FusionContact.AllMCountResearch
