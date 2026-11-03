import VOA.DeligneAudit.DeligneSectorD4Table

/-! # Light finite skew-table rows for the explicit D4 current site -/

namespace VOA.DeligneAudit.D1SiteG.D4Check

open VOA.DeligneAudit.DeligneSector.Sparse
open VOA.DeligneAudit.DeligneSector.D4

theorem skew24 : ∀ b c : Fin 28, fZ br 24 b c = -fZ br b 24 c := by
  decide +kernel

theorem skew25 : ∀ b c : Fin 28, fZ br 25 b c = -fZ br b 25 c := by
  decide +kernel

theorem skew26 : ∀ b c : Fin 28, fZ br 26 b c = -fZ br b 26 c := by
  decide +kernel

theorem skew27 : ∀ b c : Fin 28, fZ br 27 b c = -fZ br b 27 c := by
  decide +kernel

end VOA.DeligneAudit.D1SiteG.D4Check

