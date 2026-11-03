/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoZhuFastSemanticRecurrence

/-!
# Fast Zhu-omega semantics: the f2 representative

The only input is the recurrence transport for the four powers.  No generic field expansion is
replayed here.
-/

namespace VOA.LatGen.WpTwoZhuFastSemantic

open VOA VOA.LatGen VOA.LatGen.Triplet
open VOA.IntegralLattice
open VOA.LatGen.Wp
open VOA.SparseRational HeisenbergN
open VOA.LatGen.WpTwoAMSparseCompute
open VOA.LatGen.WpTwoZhuSparseCompute
open VOA.LatGen.WpTwoZhuSparseSemantics

private noncomputable abbrev Ltwo : IntegralLattice := latP 2

theorem fTwoZhuRepresentative_coe_eq_eval_fast (hp : 1 ≤ 2) :
    ((fTwoZhuRepresentative (tripletWVOA 2 hp) : (tripletW 2 hp).carrier) :
        LatModuleGen Ltwo) =
      latStateGen Ltwo
        (evalZhuSparseQ WpTwoZhuSparseLhs.fTwoFastSparseQ) 0 := by
  simp only [fTwoZhuRepresentative, WpTwoZhuSparseLhs.fTwoFastSparseQ,
    Submodule.coe_add, Submodule.coe_sub, Submodule.coe_smul,
    evalZhuSparseQ_sumQ, evalZhuSparseQ_scaleQ, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [zhuOmegaPow_coe_eq_eval_fast hp 5,
    zhuOmegaPow_coe_eq_eval_fast hp 4,
    zhuOmegaPow_coe_eq_eval_fast hp 3,
    zhuOmegaPow_coe_eq_eval_fast hp 2]
  repeat' rw [latStateGen_add_boson]
  repeat' rw [latStateGen_smul_boson]
  norm_num
  rw [sub_eq_add_neg, ← neg_smul]
  abel

end VOA.LatGen.WpTwoZhuFastSemantic

section AxiomAudit
#print axioms VOA.LatGen.WpTwoZhuFastSemantic.fTwoZhuRepresentative_coe_eq_eval_fast
end AxiomAudit
