import VOA.DeligneAudit.DeligneFusionD1TensorGGrRank
import VOA.DeligneAudit.DeligneFusionD1TensorGD4

/-! Exact rank of the actual cyclic graded D4 tensor model, using only the
light checked bracket/Jacobi/skew/cyclic site data. No coefficientwise
Demazure comparison or canonical Ravinder identification is inferred. -/
namespace VOA.DeligneAudit.D1TensorG.Gr.D4Check

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneSector.D4

noncomputable section

abbrev modelSpace (N : ℕ) :=
  cyclicGr (D1TensorG.D4Check.currentRep N) (D1TensorG.D4Check.highest N)

def modelRep (N : ℕ) : CurrentModule (fC 28 br) (modelSpace N) :=
  cyclicRep (D1TensorG.D4Check.currentRep N) (D1TensorG.D4Check.highest N)

def modelGenerator (N : ℕ) : modelSpace N :=
  cyclicGenerator (D1TensorG.D4Check.currentRep N) (D1TensorG.D4Check.highest N)

theorem model_cyclic (N : ℕ) :
    Submodule.span ℂ (Set.range fun l : List (Fin 28 × ℕ) =>
      wordOp (modelRep N) l (modelGenerator N)) = ⊤ := cyclicRep_span _ _

/-- The finite actual cyclic graded D4 model has total rank 29^N. -/
theorem finite_dimension (N : ℕ) :
    FiniteDimensional ℂ (modelSpace N) ∧ Module.finrank ℂ (modelSpace N) = 29 ^ N := by
  have h := finite_rank_cyclicGr_of_span
    (D1TensorG.D4Check.currentRep N) (D1TensorG.D4Check.highest N)
    (D1TensorG.D4Check.current_cyclic N)
  exact ⟨h.1, h.2.trans (D1TensorG.D4Check.dimension N)⟩

end
end VOA.DeligneAudit.D1TensorG.Gr.D4Check

#print axioms VOA.DeligneAudit.D1TensorG.Gr.D4Check.finite_dimension
