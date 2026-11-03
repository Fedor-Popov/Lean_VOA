import VOA.DeligneAudit.DeligneFusionD1TensorGCyclic
import VOA.DeligneAudit.DeligneFusionD1SiteGD4

/-!
# Actual cyclic 29^N-dimensional D4 shifted tensor current models

This specializes the checked generic shifted tensor construction to D4's
finite bracket, Jacobi, skew and coadjoint cyclic-word certificates. All
site counts N, including zero, have an actual cyclic current model of the
displayed total rank. No graded Demazure character comparison is asserted.
-/

namespace VOA.DeligneAudit.D1TensorG.D4Check

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.DeligneSector
open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneSector.D4

noncomputable section

/-- The constructed D4 current action on its actual N-fold tensor space. -/
def currentRep (N : ℕ) : CurrentModule (fC 28 br) (D1TensorG.Space 28 N) :=
  D1TensorG.rep (fC 28 br) D1SiteG.D4Check.table_jacobi D1SiteG.D4Check.table_skewC
    (D1TensorG.points N)

/-- Tensor of the checked highest-root site generators. -/
def highest (N : ℕ) : D1TensorG.Space 28 N := D1TensorG.generator (27 : Fin 28)

/-- The actual tensor generator spans the whole model under D4 currents. -/
theorem current_cyclic (N : ℕ) :
    Submodule.span ℂ (Set.range fun l : List (Fin 28 × ℕ) =>
      wordOp (currentRep N) l (highest N)) = ⊤ :=
  D1TensorG.cyclic_top (fC 28 br) D1SiteG.D4Check.table_jacobi
    D1SiteG.D4Check.table_skewC (D1TensorG.points N) (D1TensorG.points_injective N)
      27 10 D1SiteG.D4Check.coadjoint_cyclic

/-- The constructed model's exact total dimension, proved from its tensor basis. -/
theorem dimension (N : ℕ) : Module.finrank ℂ (D1TensorG.Space 28 N) = 29 ^ N :=
  D1TensorG.finrank_space 28 N

end
end VOA.DeligneAudit.D1TensorG.D4Check

#print axioms VOA.DeligneAudit.D1TensorG.D4Check.current_cyclic
#print axioms VOA.DeligneAudit.D1TensorG.D4Check.dimension
