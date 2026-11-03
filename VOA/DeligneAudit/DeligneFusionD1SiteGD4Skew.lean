import VOA.DeligneAudit.DeligneFusionD1SiteGD4SkewA
import VOA.DeligneAudit.DeligneFusionD1SiteGD4SkewB
import VOA.DeligneAudit.DeligneFusionD1SiteGD4SkewC
import VOA.DeligneAudit.DeligneFusionD1SiteGD4SkewD
import VOA.DeligneAudit.DeligneFusionD1SiteGD4SkewE
import VOA.DeligneAudit.DeligneFusionD1SiteGD4SkewF
import VOA.DeligneAudit.DeligneFusionD1SiteGD4SkewG

/-! # The concrete D4 skew table, with finite checks split into light rows -/

namespace VOA.DeligneAudit.D1SiteG.D4Check

open VOA.DeligneAudit.DeligneSector.Sparse
open VOA.DeligneAudit.DeligneSector.D4

noncomputable section

theorem table_skew (a b c : Fin 28) : fZ br a b c = -fZ br b a c := by
  fin_cases a
  · exact skew0 b c
  · exact skew1 b c
  · exact skew2 b c
  · exact skew3 b c
  · exact skew4 b c
  · exact skew5 b c
  · exact skew6 b c
  · exact skew7 b c
  · exact skew8 b c
  · exact skew9 b c
  · exact skew10 b c
  · exact skew11 b c
  · exact skew12 b c
  · exact skew13 b c
  · exact skew14 b c
  · exact skew15 b c
  · exact skew16 b c
  · exact skew17 b c
  · exact skew18 b c
  · exact skew19 b c
  · exact skew20 b c
  · exact skew21 b c
  · exact skew22 b c
  · exact skew23 b c
  · exact skew24 b c
  · exact skew25 b c
  · exact skew26 b c
  · exact skew27 b c

theorem table_skewC (a b c : Fin 28) : fC 28 br a b c = -fC 28 br b a c := by
  change ((fZ br a b c : ℤ) : ℂ) = -((fZ br b a c : ℤ) : ℂ)
  exact_mod_cast table_skew a b c

end

end VOA.DeligneAudit.D1SiteG.D4Check

#print axioms VOA.DeligneAudit.D1SiteG.D4Check.table_skewC

