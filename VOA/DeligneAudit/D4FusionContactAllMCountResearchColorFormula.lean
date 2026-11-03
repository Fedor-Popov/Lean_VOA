import VOA.DeligneAudit.D4FusionContactAllMCountResearchColorRows
import VOA.DeligneAudit.D4FusionContactAllMCountResearchRefinedFormula

/-! Compile the uniform leading formula into an exact finite integer row.
The three formal slots are the actual modes p,q-1,q. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch
open VOA.DeligneAudit.D4FusionContact.Polynomial
open VOA.DeligneAudit.D4FusionContact.M2Certificate
open BoundaryPair
noncomputable section

def colorFlatten (c : Fin 9) (r : Fin 3) : Fin 27 :=
  ⟨3*c.val+r.val,by have := c.isLt; have := r.isLt; omega⟩

theorem colorIndex_flatten (c : Fin 9) (r : Fin 3) :
    colorIndex (colorFlatten c r) = (c,r) := by
  apply Prod.ext <;> apply Fin.ext <;> simp only [colorIndex,colorFlatten]
  all_goals have := r.isLt; omega

variable {m : ℕ} (b : BoundaryPair m)

def colorValue (v : Fin 27) : MvPolynomial (Vars m) ℂ :=
  let x := colorIndex v
  modeX m x.1 (if x.2=0 then b.lower.val else if x.2=1 then b.top.val-1 else b.top.val)

theorem colorValue_flatten (c : Fin 9) (r : Fin 3) :
    colorValue b (colorFlatten c r) =
      modeX m c (if r=0 then b.lower.val else if r=1 then b.top.val-1 else b.top.val) := by
  simp only [colorValue,colorIndex_flatten]

theorem colorValue_near (v : Fin 18) :
    colorValue b (nearColorIndex v) =
      MvPolynomial.rename (nearestPair b).embed (MvPolynomial.X (varIndex v)) := by
  rw [colorValue,colorIndex_near,MvPolynomial.rename_X]
  have ht := b.top.isLt
  have hn : b.top.val-1 < m := by omega
  have hm := (varIndex v).2.isLt
  simp only [nearColorEmbed,modeX,BoundaryPair.embed,BoundaryPair.embedMode,nearestPair]
  by_cases h : (varIndex v).2=0
  · simp [h,hn]
  · have hh : (varIndex v).2 = 1 := by apply Fin.ext; simp only [Fin.ext_iff] at h; omega
    simp [hh,ht]

theorem row_near_eval (r : WordRow) :
    Rows.eval (colorValue b) (Rows.map nearColorIndex r) =
      MvPolynomial.rename (nearestPair b).embed (rowEval varIndex r) := by
  rw [Rows.eval_map,← rows_eval18]
  have hh := Rows.eval_hom (A := MvPolynomial (Vars 2) ℂ)
    (B := MvPolynomial (Vars m) ℂ) (fun v => MvPolynomial.X (varIndex v))
    (MvPolynomial.rename (nearestPair b).embed).toRingHom r
  simpa only [colorValue_near] using hh.symm

def colorPolarRow (i j : Fin 9) (l : List (Fin 3)) : Rows.Row 27 :=
  Rows.multiply (colorFlatten i 0) (Rows.multiply (colorFlatten j 2)
    (Rows.map nearColorIndex (boundaryRow (leviOrbit l .base).words)))

theorem colorPolarRow_eval (i j : Fin 9) (l : List (Fin 3)) :
    Rows.eval (colorValue b) (colorPolarRow i j l) = (2:ℂ) • polarLeading b i j l := by
  rw [colorPolarRow,Rows.eval_multiply,Rows.eval_multiply,row_near_eval,
    rowEval_boundary,← integerExpr_semantics,map_smul]
  have h20 : (2:Fin 3) ≠ 0 := by decide
  have h21 : (2:Fin 3) ≠ 1 := by decide
  simp only [colorValue_flatten,polarLeading,Algebra.smul_def,if_neg h20,if_neg h21]
  norm_num
  ring

def colorPieceRow : WheelPiece → Rows.Row 27
  | .polar z i j l => Rows.scale z (colorPolarRow i.castSucc j.castSucc l)
  | .square _ _ _ _ => []

theorem colorPieceRow_eval (t : WheelPiece) :
    Rows.eval (colorValue b) (colorPieceRow t) = (2:ℂ) • pieceLeading b t := by
  cases t with
  | polar z i j l =>
      rw [colorPieceRow,Rows.eval_scale,colorPolarRow_eval]
      simp only [pieceLeading,← Int.cast_smul_eq_zsmul ℂ z,smul_smul,mul_comm]
  | square z i j l => simp only [colorPieceRow,Rows.eval_nil,pieceLeading,smul_zero]

def colorPiecesRow : List WheelPiece → Rows.Row 27
  | [] => []
  | t::l => colorPieceRow t ++ colorPiecesRow l

theorem colorPiecesRow_eval (l : List WheelPiece) :
    Rows.eval (colorValue b) (colorPiecesRow l) = (2:ℂ) • piecesLeading b l := by
  induction l with
  | nil => simp only [colorPiecesRow,Rows.eval_nil,piecesLeading,smul_zero]
  | cons t l ih => rw [colorPiecesRow,Rows.eval_append,colorPieceRow_eval,ih,
      piecesLeading,smul_add]

/-- A single ordered four-variable word. -/
def colorProductRow (i j k l : Fin 9) : Rows.Row 27 :=
  [(Rows.canonical [colorFlatten i 0,colorFlatten j 1,colorFlatten k 2,colorFlatten l 2],1)]

theorem colorProductRow_eval (i j k l : Fin 9) :
    Rows.eval (colorValue b) (colorProductRow i j k l) = leadingProduct b i j k l := by
  rw [colorProductRow,Rows.eval_cons,Rows.eval_nil,add_zero,one_smul,
    Rows.wordEval_canonical]
  have h20 : (2:Fin 3) ≠ 0 := by decide
  have h21 : (2:Fin 3) ≠ 1 := by decide
  have h10 : (1:Fin 3) ≠ 0 := by decide
  simp only [Rows.wordEval,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,
    colorValue_flatten,mul_one,leadingProduct,if_neg h20,if_neg h21,if_neg h10]
  norm_num
  ring

def colorEndpointRow : Rows.Row 27 :=
  Rows.scale (64*h0Weight 6) (colorProductRow 5 6 1 2) ++
  Rows.scale (64*h0Weight 5) (colorProductRow 6 5 1 2) ++
  Rows.scale (64*h0Weight 6) (colorProductRow 4 6 1 3) ++
  Rows.scale (64*h0Weight 4) (colorProductRow 6 4 1 3) ++
  Rows.scale (64*h0Weight 5) (colorProductRow 4 5 2 3) ++
  Rows.scale (64*h0Weight 4) (colorProductRow 5 4 2 3)

theorem colorEndpointRow_eval :
    Rows.eval (colorValue b) colorEndpointRow = (64:ℂ) • endpointLeading b := by
  simp only [colorEndpointRow,Rows.eval_append,Rows.eval_scale,colorProductRow_eval,
    ← Int.cast_smul_eq_zsmul ℂ,Int.cast_mul,Int.cast_ofNat,endpointLeading]
  module

/-- Sixty-four times the leading polynomial; all denominators are cleared. -/
def colorFormulaRow : Rows.Row 27 := colorEndpointRow ++ colorPiecesRow wheelPieces

theorem colorFormulaRow_eval :
    Rows.eval (colorValue b) colorFormulaRow = (64:ℂ) • refinedLeading b := by
  rw [colorFormulaRow,Rows.eval_append,colorEndpointRow_eval,colorPiecesRow_eval]
  simp only [refinedLeading,smul_add,smul_smul]
  norm_num

end
#print axioms colorFormulaRow_eval
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch
