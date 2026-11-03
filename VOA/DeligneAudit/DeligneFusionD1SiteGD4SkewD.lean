import VOA.DeligneAudit.DeligneSectorD4Table

/-! # Light finite skew-table rows for the explicit D4 current site -/

namespace VOA.DeligneAudit.D1SiteG.D4Check

open VOA.DeligneAudit.DeligneSector.Sparse
open VOA.DeligneAudit.DeligneSector.D4

theorem skew12 : ∀ b c : Fin 28, fZ br 12 b c = -fZ br b 12 c := by
  decide +kernel

theorem skew13 : ∀ b c : Fin 28, fZ br 13 b c = -fZ br b 13 c := by
  decide +kernel

theorem skew14 : ∀ b c : Fin 28, fZ br 14 b c = -fZ br b 14 c := by
  decide +kernel

theorem skew15 : ∀ b c : Fin 28, fZ br 15 b c = -fZ br b 15 c := by
  decide +kernel

end VOA.DeligneAudit.D1SiteG.D4Check

