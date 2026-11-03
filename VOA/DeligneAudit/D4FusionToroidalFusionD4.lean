import VOA.DeligneAudit.D4FusionToroidalFusionRelations
import VOA.DeligneAudit.D4FusionToroidalFusionEvalGr
import VOA.DeligneAudit.D4FusionToroidalFusionGrRelations
import VOA.DeligneAudit.DeligneFusionD1TensorGD4

/-!
# The untruncated D4 toroidal evaluation model

The actual N-site tensor space has rank `29^N`. Its toroidal action is
untruncated; the truncated action belongs to the `t`-degree associated graded.
-/

namespace VOA.DeligneAudit.Toroidal.D4Fusion

open VOA.DeligneAudit.D1TensorG
open VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.DeligneSector.Sparse
open VOA.DeligneAudit.DeligneSector

noncomputable section

def action (N : ℕ) : Toroidal.ToroidalAction (fC 28 br) (D1TensorG.Space 28 N) :=
  Toroidal.d1EvalAction (fC 28 br) D1SiteG.D4Check.table_jacobi
    D1SiteG.D4Check.table_skewC (D1TensorG.points N)

def generator (N : ℕ) : D1TensorG.Space 28 N := D1TensorG.D4Check.highest N

/-- The N-site bigraded fusion-side action with `t^N = 0`. -/
def gradedAction (N : ℕ) :
    Toroidal.ToroidalModule (fC 28 br) N
      (Toroidal.FusionGr.Gr (action N) (generator N)) :=
  Toroidal.FusionGr.evalGrToroidal
    (fun _ => D1SiteG.rep (fC 28 br) D1SiteG.D4Check.table_jacobi
      D1SiteG.D4Check.table_skewC)
    (D1TensorG.points N) (generator N)

def gradedHighest (N : ℕ) :
    Toroidal.FusionGr.Gr (action N) (generator N) :=
  Toroidal.FusionGr.grGenerator (action N) (generator N)

theorem graded_raising (N : ℕ) (e : Fin 28) (he : D4sector.raising e)
    (i s : ℕ) :
    Toroidal.FusionGr.grOp (action N) (generator N) N e i s
      (gradedHighest N) = 0 :=
  Toroidal.FusionGr.highest_raising D4sector D1SiteG.D4Check.table_skewC
    (D1TensorG.points N) e he i s

theorem graded_lowering (N : ℕ) (hm : 0 < N) (x : Fin 28)
    (hx : D4sector.lowering x) :
    ((Toroidal.FusionGr.grOp (action N) (generator N) N x 0 0) ^
      (N * D4sector.lowExp x + 1)) (gradedHighest N) = 0 :=
  Toroidal.FusionGr.highest_lowering D4sector D1SiteG.D4Check.table_skewC
    (D1TensorG.points N) x hx hm

theorem dimension (N : ℕ) :
    Module.finrank ℂ (D1TensorG.Space 28 N) = 29 ^ N :=
  D1TensorG.D4Check.dimension N

end

end VOA.DeligneAudit.Toroidal.D4Fusion

#print axioms VOA.DeligneAudit.Toroidal.D4Fusion.action
#print axioms VOA.DeligneAudit.Toroidal.D4Fusion.gradedAction
#print axioms VOA.DeligneAudit.Toroidal.D4Fusion.graded_raising
#print axioms VOA.DeligneAudit.Toroidal.D4Fusion.graded_lowering
#print axioms VOA.DeligneAudit.Toroidal.D4Fusion.dimension
