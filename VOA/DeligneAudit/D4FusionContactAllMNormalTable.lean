import VOA.DeligneAudit.D4FusionContactGradingTable

/-! Exact diagonal Cartan data for whole-ideal word polarization. -/
namespace VOA.DeligneAudit.D4FusionContact.Polynomial.AllMNormal

open VOA.DeligneAudit.DeligneSector.Sparse
open VOA.DeligneAudit.DeligneSector.D4 (br)

def cartanCoeff : Fin 9 → ℤ := ![-2, -1, -1, -1, 0, 0, 0, 1, -1]

theorem cartan_row_Z : ∀ i j : Fin 9,
    fZ br 1 (radIndex i) (radIndex j) = if j = i then cartanCoeff i else 0 := by
  decide +kernel

theorem cartan_row (i j : Fin 9) :
    contactF 1 (radIndex i) (radIndex j) = if j = i then (cartanCoeff i : ℂ) else 0 := by
  change (fZ br 1 (radIndex i) (radIndex j) : ℂ) = _
  rw [cartan_row_Z]
  split_ifs <;> norm_num

end VOA.DeligneAudit.D4FusionContact.Polynomial.AllMNormal
