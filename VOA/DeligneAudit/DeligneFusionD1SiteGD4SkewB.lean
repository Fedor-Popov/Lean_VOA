import VOA.DeligneAudit.DeligneSectorD4Table

/-! # Light finite skew-table rows for the explicit D4 current site -/

namespace VOA.DeligneAudit.D1SiteG.D4Check

open VOA.DeligneAudit.DeligneSector.Sparse
open VOA.DeligneAudit.DeligneSector.D4

theorem skew4 : ∀ b c : Fin 28, fZ br 4 b c = -fZ br b 4 c := by
  decide +kernel

theorem skew5 : ∀ b c : Fin 28, fZ br 5 b c = -fZ br b 5 c := by
  decide +kernel

theorem skew6 : ∀ b c : Fin 28, fZ br 6 b c = -fZ br b 6 c := by
  decide +kernel

theorem skew7 : ∀ b c : Fin 28, fZ br 7 b c = -fZ br b 7 c := by
  decide +kernel

end VOA.DeligneAudit.D1SiteG.D4Check

