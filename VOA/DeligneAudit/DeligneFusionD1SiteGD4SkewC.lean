import VOA.DeligneAudit.DeligneSectorD4Table

/-! # Light finite skew-table rows for the explicit D4 current site -/

namespace VOA.DeligneAudit.D1SiteG.D4Check

open VOA.DeligneAudit.DeligneSector.Sparse
open VOA.DeligneAudit.DeligneSector.D4

theorem skew8 : ∀ b c : Fin 28, fZ br 8 b c = -fZ br b 8 c := by
  decide +kernel

theorem skew9 : ∀ b c : Fin 28, fZ br 9 b c = -fZ br b 9 c := by
  decide +kernel

theorem skew10 : ∀ b c : Fin 28, fZ br 10 b c = -fZ br b 10 c := by
  decide +kernel

theorem skew11 : ∀ b c : Fin 28, fZ br 11 b c = -fZ br b 11 c := by
  decide +kernel

end VOA.DeligneAudit.D1SiteG.D4Check

