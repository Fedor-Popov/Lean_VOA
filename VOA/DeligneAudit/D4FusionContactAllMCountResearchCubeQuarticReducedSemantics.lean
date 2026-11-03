import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeQuarticReducedCompiler
import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeQuarticReducedChecks

/-! Semantic content of the twenty fixed integer jet cancellations.
All jets are the actual unbounded polynomial derivative, before evaluation. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube.QuarticReduced
open QuarticReducedRows
noncomputable section

private theorem certOrders_check : ∀ i,
    (certProducts i).all (fun p => decide (p.a+p.b = certOrder i)) = true := by
  decide +kernel

theorem certProduct_orders (i : Fin 20) (p : ProductSpec) (hp : p ∈ certProducts i) :
    p.a+p.b = certOrder i := by
  exact of_decide_eq_true (List.all_eq_true.mp (certOrders_check i) p hp)

def jetTarget (j : ℕ) (h : Fin 8) : JetRing :=
  ((List.finRange 8).map fun c => channelWeight h c •
    (jetVarNat (8*j+c.val) *
      jetBase (orbit ℂ 4 (2-bit c 0) (2-bit c 1) (2-bit c 2)))).sum

def jetProduct (p : ProductSpec) : JetRing :=
  ((jetRaise : JetRing → JetRing)^[p.a]) (jetBase (orbit ℂ 2 p.x2 p.y2 p.z2)) *
    ((jetRaise : JetRing → JetRing)^[p.b]) (jetBase (orbit ℂ 3 p.x3 p.y3 p.z3))

theorem eval_baseRow (r a b c : ℕ) :
    eval jetVarNat (QuarticReducedRows.map Fin.val (orbitRow r a b c)) =
      jetBase (orbit ℂ r a b c) := by
  simpa only [jetRow,Function.iterate_zero_apply] using jetRow_eval 0 r a b c

private theorem eval_flatMap {ι A : Type*} [CommRing A]
    (v : ℕ → A) (l : List ι) (f : ι → Row ℕ) :
    eval v (l.flatMap f) = (l.map fun i => eval v (f i)).sum := by
  induction l with
  | nil => rfl
  | cons x l ih => rw [List.flatMap_cons,eval_append,ih,List.map_cons,List.sum_cons]

theorem targetRow_eval (j : ℕ) (h : Fin 8) :
    eval jetVarNat (targetRow j h) = jetTarget j h := by
  rw [targetRow,eval_collect,eval_flatMap]
  simp_rw [eval_scale,eval_mul,eval_cons,eval_nil,one_zsmul,add_zero,
    wordEval,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,eval_baseRow]
  rfl

theorem productRow_eval (p : ProductSpec) :
    eval jetVarNat (productRow p) = jetProduct p := by
  rw [productRow,eval_mul,jetRow_eval,jetRow_eval]
  rfl

private theorem eval_negativeProducts {A : Type*} [CommRing A]
    (v : ℕ → A) (l : List ProductSpec) :
    eval v (l.flatMap fun p => scale (-p.coeff) (productRow p)) =
      -(l.map fun p => p.coeff • eval v (productRow p)).sum := by
  induction l with
  | nil => simp
  | cons p l ih =>
      rw [List.flatMap_cons,eval_append,eval_scale,neg_smul,ih,
        List.map_cons,List.sum_cons]
      abel

/-- All tails of the fixed color-jet identity, with its nonzero integer multiplier. -/
theorem certificate_jet_identity (i : Fin 20) :
    certMultiplier i • jetTarget (certOrder i) (certChannel i) =
      ((certProducts i).map fun p => p.coeff • jetProduct p).sum := by
  have h := eval_zero_of_fastCollect jetVarNat (residualRow i) (certificate_check i)
  rw [residualRow,eval_append,eval_scale,targetRow_eval,eval_negativeProducts] at h
  simp_rw [productRow_eval] at h
  exact sub_eq_zero.mp (by simpa only [sub_eq_add_neg] using h)

end
#print axioms certProduct_orders
#print axioms certificate_jet_identity
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube.QuarticReduced
