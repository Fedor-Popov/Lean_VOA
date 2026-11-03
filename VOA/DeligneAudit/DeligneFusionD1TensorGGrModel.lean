import VOA.DeligneAudit.DeligneFusionD1TensorGGrRank
import VOA.DeligneAudit.DeligneFusionD1TensorGGrSat

/-! Actual finite cyclic graded tensor models with the proved source relations.
The model is the cyclic subtype, whose rank equals the actual tensor source
rank. No finiteness of the unused ambient quotient or Demazure character
comparison is asserted. -/
namespace VOA.DeligneAudit.D1TensorG.Gr

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.DeligneSector
open VOA.DeligneAudit.UnivG

noncomputable section
variable (S : DeligneSectorData)
variable (hskew : ∀ a b c, S.f a b c = -S.f b a c)

/-- The actual cyclic associated graded of the tensor at distinct integer sites. -/
abbrev tensorModelSpace (N : ℕ) :=
  cyclicGr (D1TensorG.rep S.f S.jacobi hskew (points N)) (generator S.c₀)

/-- The checked full current action restricted to the generated graded space. -/
def tensorModelRep (N : ℕ) : CurrentModule S.f (tensorModelSpace S hskew N) :=
  cyclicRep (D1TensorG.rep S.f S.jacobi hskew (points N)) (generator S.c₀)

def tensorModelGenerator (N : ℕ) : tensorModelSpace S hskew N :=
  cyclicGenerator (D1TensorG.rep S.f S.jacobi hskew (points N)) (generator S.c₀)

/-- Actual word cyclicity of the constructed graded representation. -/
theorem tensorModel_cyclic (N : ℕ) :
    Submodule.span ℂ (Set.range fun l : List (Fin S.n × ℕ) =>
      wordOp (tensorModelRep S hskew N) l (tensorModelGenerator S hskew N)) = ⊤ :=
  cyclicRep_span _ _

/-- The explicit source presentation and exact total rank are proved for
the actual finite cyclic graded model, with no realization or dimension input. -/
theorem tensor_graded_model (N : ℕ) :
    FiniteDimensional ℂ (tensorModelSpace S hskew N) ∧
      Sat S.f (tensorModelRep S hskew N) (tensorModelGenerator S hskew N) (tensorSpec S N) ∧
      Module.finrank ℂ (tensorModelSpace S hskew N) = (S.n + 1) ^ N := by
  obtain ⟨hfd, hsat, hrank⟩ := cyclic_source_model
    (D1TensorG.rep S.f S.jacobi hskew (points N)) (generator S.c₀)
    (sector_model_cyclic S hskew N) (tensor_filtSat S hskew (points N))
  refine ⟨hfd, hsat, ?_⟩
  exact hrank.trans (D1TensorG.finrank_space S.n N)

end
end VOA.DeligneAudit.D1TensorG.Gr

#print axioms VOA.DeligneAudit.D1TensorG.Gr.tensor_graded_model
