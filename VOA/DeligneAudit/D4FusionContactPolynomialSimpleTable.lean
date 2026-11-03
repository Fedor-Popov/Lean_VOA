import VOA.DeligneAudit.D4FusionContactTable

/-! # Light simple-root 18 sl₂ table identities -/

namespace VOA.DeligneAudit.D4FusionContact.PolynomialSource

open VOA.DeligneAudit.DeligneSector.Sparse
open VOA.DeligneAudit.DeligneSector.D4 (br)

theorem simple_efZ : ∀ c : Fin 28, fZ br 6 18 c = if c = 1 then 1 else 0 := by
  decide +kernel

theorem simple_hfZ : ∀ c : Fin 28, fZ br 1 18 c = if c = 18 then -2 else 0 := by
  decide +kernel

theorem simple_ffZ : ∀ c : Fin 28, fZ br 18 18 c = 0 := by decide +kernel

theorem simple_ef (c : Fin 28) : contactF 6 18 c = if c = 1 then 1 else 0 := by
  change (fZ br 6 18 c : ℂ) = _
  rw [simple_efZ]
  split_ifs <;> norm_num

theorem simple_hf (c : Fin 28) : contactF 1 18 c = if c = 18 then -2 else 0 := by
  change (fZ br 1 18 c : ℂ) = _
  rw [simple_hfZ]
  split_ifs <;> norm_num

theorem simple_ff (c : Fin 28) : contactF 18 18 c = 0 := by
  change (fZ br 18 18 c : ℂ) = _
  rw [simple_ffZ, Int.cast_zero]

end VOA.DeligneAudit.D4FusionContact.PolynomialSource
