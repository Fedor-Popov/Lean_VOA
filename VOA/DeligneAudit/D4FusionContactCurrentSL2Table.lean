import VOA.DeligneAudit.D4FusionContactHighestRootTable

/-! # Remaining light highest-root sl₂ current-table identities -/

namespace VOA.DeligneAudit.D4FusionContact

open VOA.DeligneAudit.DeligneSector.Sparse
open VOA.DeligneAudit.DeligneSector.D4 (br)

theorem highest_root_heZ : ∀ c : Fin 28,
    fZ br 0 15 c + fZ br 1 15 c + fZ br 1 15 c +
      fZ br 2 15 c + fZ br 3 15 c = if c = 15 then 2 else 0 := by
  decide +kernel

theorem highest_root_he (c : Fin 28) :
    contactF 0 15 c + contactF 1 15 c + contactF 1 15 c +
      contactF 2 15 c + contactF 3 15 c = if c = 15 then 2 else 0 := by
  have hh := congrArg (fun x : ℤ => (x : ℂ)) (highest_root_heZ c)
  simpa only [Int.cast_add, Int.cast_ite, Int.cast_ofNat, Int.cast_zero] using hh

theorem highest_root_eeZ : ∀ c : Fin 28, fZ br 15 15 c = 0 := by decide +kernel

theorem highest_root_ee (c : Fin 28) : contactF 15 15 c = 0 := by
  change (fZ br 15 15 c : ℂ) = 0
  rw [highest_root_eeZ, Int.cast_zero]

end VOA.DeligneAudit.D4FusionContact
