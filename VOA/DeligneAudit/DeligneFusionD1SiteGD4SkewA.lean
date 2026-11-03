import VOA.DeligneAudit.DeligneSectorD4Table

/-! # Light finite skew-table rows for the explicit D4 current site -/

namespace VOA.DeligneAudit.D1SiteG.D4Check

open VOA.DeligneAudit.DeligneSector.Sparse
open VOA.DeligneAudit.DeligneSector.D4

theorem skew0 : ∀ b c : Fin 28, fZ br 0 b c = -fZ br b 0 c := by
  decide +kernel

theorem skew1 : ∀ b c : Fin 28, fZ br 1 b c = -fZ br b 1 c := by
  decide +kernel

theorem skew2 : ∀ b c : Fin 28, fZ br 2 b c = -fZ br b 2 c := by
  decide +kernel

theorem skew3 : ∀ b c : Fin 28, fZ br 3 b c = -fZ br b 3 c := by
  decide +kernel

end VOA.DeligneAudit.D1SiteG.D4Check

