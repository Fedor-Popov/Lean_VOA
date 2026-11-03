import VOA.DeligneAudit.D4FusionToroidalFusionD4RavFam
import VOA.DeligneAudit.D4FusionToroidalFusionUZeroGr
import VOA.DeligneAudit.D4FusionToroidalFusionUDegree

/-!
# Combined fusion-side build target

This import joins the concrete D4 toroidal action, its full Ravinder-family
highest-vector relations, and the available total and coadjoint rank bounds.
-/

namespace VOA.DeligneAudit.Toroidal.D4Fusion

open VOA.DeligneAudit.Toroidal

noncomputable section

theorem graded_total_rank_bound (N : ℕ) :
    FiniteDimensional ℂ (FusionGr.Gr (action N) (generator N)) ∧
      Module.finrank ℂ (FusionGr.Gr (action N) (generator N)) ≤ 29 ^ N :=
  FusionGr.d4_evalGr_rank_le N

theorem graded_coadjoint_rank_bound (N : ℕ) :
    FiniteDimensional ℂ
      (FusionGr.evalUZeroGr
        VOA.DeligneAudit.DeligneSector.D4.D4sector
        D1SiteG.D4Check.table_skewC (D1TensorG.points N)) ∧
    Module.finrank ℂ
      (FusionGr.evalUZeroGr
        VOA.DeligneAudit.DeligneSector.D4.D4sector
        D1SiteG.D4Check.table_skewC (D1TensorG.points N)) ≤ 28 ^ N :=
  FusionGr.d4_evalUZeroGr_rank_le N

end

end VOA.DeligneAudit.Toroidal.D4Fusion

#print axioms VOA.DeligneAudit.Toroidal.D4Fusion.graded_total_rank_bound
#print axioms VOA.DeligneAudit.Toroidal.D4Fusion.graded_coadjoint_rank_bound
