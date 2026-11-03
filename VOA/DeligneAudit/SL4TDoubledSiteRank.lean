import VOA.DeligneAudit.SL4TDoubledSiteFiltration
import VOA.DeligneAudit.SL4TDoubledSiteRankReduction

/-! The universal middle-weight rank bound with one fewer current mode than sites. -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

/-- The truncated local Weyl module of middle weight has the doubled-site rank bound. -/
theorem truncatedWeyl_sl4_doubledSite_rank_le (B : ℕ) (hB : 2 ≤ B) :
    FiniteDimensional ℂ (DoubledSiteModule B) ∧
      Module.finrank ℂ (DoubledSiteModule B) ≤ 20 * 6 ^ (B - 2) := by
  apply truncatedWeyl_sl4_doubledSite_rank_le_of_flags B hB
  intro q hq
  obtain ⟨hv, hA, hsites⟩ := (mem_mixedValidBlocks 0 B q).mp hq
  exact doubledSiteSpanningFiltration B hB q hv hA hsites

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.truncatedWeyl_sl4_doubledSite_rank_le
