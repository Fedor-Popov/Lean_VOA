import VOA.DeligneAudit.DeligneSectorD4Table

/-! # Light finite skew-table rows for the explicit D4 current site -/

namespace VOA.DeligneAudit.D1SiteG.D4Check

open VOA.DeligneAudit.DeligneSector.Sparse
open VOA.DeligneAudit.DeligneSector.D4

theorem skew16 : ∀ b c : Fin 28, fZ br 16 b c = -fZ br b 16 c := by
  decide +kernel

theorem skew17 : ∀ b c : Fin 28, fZ br 17 b c = -fZ br b 17 c := by
  decide +kernel

theorem skew18 : ∀ b c : Fin 28, fZ br 18 b c = -fZ br b 18 c := by
  decide +kernel

theorem skew19 : ∀ b c : Fin 28, fZ br 19 b c = -fZ br b 19 c := by
  decide +kernel

end VOA.DeligneAudit.D1SiteG.D4Check

