import VOA.DeligneAudit.D4FusionContactTable

/-! # Small typed highest-root sl₂ bracket checks -/

namespace VOA.DeligneAudit.D4FusionContact

open VOA.DeligneAudit.DeligneSector.Sparse
open VOA.DeligneAudit.DeligneSector.D4 (br)

theorem highest_root_efZ : ∀ c : Fin 28, fZ br 15 27 c =
    (if c = 0 then -1 else 0) + (if c = 1 then -1 else 0) +
    (if c = 1 then -1 else 0) + (if c = 2 then -1 else 0) + (if c = 3 then -1 else 0) := by
  decide +kernel

theorem highest_root_hfZ : ∀ c : Fin 28,
    fZ br 0 27 c + fZ br 1 27 c + fZ br 1 27 c + fZ br 2 27 c + fZ br 3 27 c =
      if c = 27 then -2 else 0 := by
  decide +kernel

theorem highest_root_ef (c : Fin 28) : contactF 15 27 c =
    (if c = 0 then -1 else 0) + (if c = 1 then -1 else 0) +
    (if c = 1 then -1 else 0) + (if c = 2 then -1 else 0) + (if c = 3 then -1 else 0) := by
  change (fZ br 15 27 c : ℂ) = _
  rw [highest_root_efZ]
  split_ifs <;> norm_num

theorem highest_root_hf (c : Fin 28) :
    contactF 0 27 c + contactF 1 27 c + contactF 1 27 c + contactF 2 27 c + contactF 3 27 c =
      if c = 27 then -2 else 0 := by
  change (fZ br 0 27 c : ℂ) + (fZ br 1 27 c : ℂ) + (fZ br 1 27 c : ℂ) +
    (fZ br 2 27 c : ℂ) + (fZ br 3 27 c : ℂ) = _
  simp only [← Int.cast_add]
  rw [highest_root_hfZ]
  split_ifs <;> norm_num

end VOA.DeligneAudit.D4FusionContact

#print axioms VOA.DeligneAudit.D4FusionContact.highest_root_ef
#print axioms VOA.DeligneAudit.D4FusionContact.highest_root_hf
