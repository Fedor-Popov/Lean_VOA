import VOA.DeligneAudit.DeligneFusionD1TensorGGrRankCyclic
import VOA.DeligneAudit.DeligneFusionD1TensorGGrDimension

/-!
# Rank of the actual cyclic current-degree model

A finite cyclic source attains its filtration at a finite degree. Coordinate
separation and rank-nullity then give the same total rank for the actual
cyclic graded module. No claim is made about the unused ambient quotient
or a Demazure character.
-/

namespace VOA.DeligneAudit.D1TensorG.Gr

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.UnivG

noncomputable section

variable {n : ℕ} {f : Fin n → Fin n → Fin n → ℂ}
variable {T : Type*} [AddCommGroup T] [Module ℂ T] [FiniteDimensional ℂ T]
variable (R : CurrentModule f T) (w : T)

theorem finrank_cyclicGr_eq_source_of_cutoff (B : ℕ) (hB : Fbelow R w B = ⊤) :
    Module.finrank ℂ (cyclicGr R w) = Module.finrank ℂ T := by
  calc
    Module.finrank ℂ (cyclicGr R w) =
        ∑ d ∈ Finset.range B, Module.finrank ℂ (cycDeg (grRep R w) (wg R w) d) :=
      finrank_cyclicGr_eq_sum R w B hB
    _ = Module.finrank ℂ (Fbelow R w B) := sum_finrank_eq_Fbelow R w B
    _ = Module.finrank ℂ T := by rw [hB]; simp

/-- Actual cyclicity of the finite source suffices for finite graded rank. -/
theorem finite_rank_cyclicGr_of_span
    (hspan : Submodule.span ℂ
      (Set.range fun l : List (Fin n × ℕ) => wordOp R l w) = ⊤) :
    FiniteDimensional ℂ (cyclicGr R w) ∧
      Module.finrank ℂ (cyclicGr R w) = Module.finrank ℂ T := by
  obtain ⟨B, hB⟩ := exists_Fbelow_top R w hspan
  exact ⟨finite_cyclicGr_of_cutoff R w B hB,
    finrank_cyclicGr_eq_source_of_cutoff R w B hB⟩

/-- Filtered generator relations hold exactly in the finite actual cyclic
graded representation, whose total rank equals the finite source rank. -/
theorem cyclic_source_model {spec : RelSpec n}
    (hspan : Submodule.span ℂ
      (Set.range fun l : List (Fin n × ℕ) => wordOp R l w) = ⊤)
    (hrel : FiltSat R w spec) :
    FiniteDimensional ℂ (cyclicGr R w) ∧
      Sat f (cyclicRep R w) (cyclicGenerator R w) spec ∧
      Module.finrank ℂ (cyclicGr R w) = Module.finrank ℂ T := by
  have h := finite_rank_cyclicGr_of_span R w hspan
  exact ⟨h.1, cyclicRep_filtSat R w hrel, h.2⟩

end

end VOA.DeligneAudit.D1TensorG.Gr

#print axioms VOA.DeligneAudit.D1TensorG.Gr.finite_rank_cyclicGr_of_span
#print axioms VOA.DeligneAudit.D1TensorG.Gr.cyclic_source_model
