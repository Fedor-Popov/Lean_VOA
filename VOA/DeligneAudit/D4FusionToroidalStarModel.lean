import VOA.DeligneAudit.D4FusionToroidalFinal
import VOA.DeligneAudit.DeligneFusionD1TensorGGrD4Model
import VOA.DeligneAudit.DeligneFusionD1TensorGGrSat

/-! The cyclic shifted tensor model gives the lower Demazure rank bound. -/

namespace VOA.DeligneAudit.Toroidal

open VOA.DeligneAudit.UnivG VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.D1TensorG.Gr

noncomputable section

theorem model_ravFam_sat (m : ℕ) :
    Sat D4sector.f (D4Check.modelRep m) (D4Check.modelGenerator m)
      (ravFam D4sector m 0) := by
  change Sat D4sector.f
    (cyclicRep (D1TensorG.D4Check.currentRep m) (D1TensorG.D4Check.highest m))
    (cyclicGenerator (D1TensorG.D4Check.currentRep m) (D1TensorG.D4Check.highest m))
    (tensorSpec D4sector m)
  exact cyclicRep_sat _ _
    (tensor_gr_sat D4sector D1SiteG.D4Check.table_skewC (D1TensorG.points m))

theorem demazure_rank_ge (m : ℕ)
    [FiniteDimensional ℂ (UModG D4sector.f (ravFam D4sector m 0))] :
    29 ^ m ≤ Module.finrank ℂ (UModG D4sector.f (ravFam D4sector m 0)) := by
  let h := model_ravFam_sat m
  have hsurj : Function.Surjective (univMapG h) := by
    apply LinearMap.range_eq_top.mp
    apply top_unique
    rw [← D4Check.model_cyclic m, Submodule.span_le]
    rintro _ ⟨l, rfl⟩
    exact ⟨wordOp (univRepG D4sector.f (ravFam D4sector m 0)) l
      (wUG D4sector.f (ravFam D4sector m 0)), univMapG_wordOp h l⟩
  rw [← (D4Check.finite_dimension m).2]
  exact LinearMap.finrank_le_finrank_of_surjective hsurj

end

end VOA.DeligneAudit.Toroidal

#print axioms VOA.DeligneAudit.Toroidal.model_ravFam_sat
#print axioms VOA.DeligneAudit.Toroidal.demazure_rank_ge
