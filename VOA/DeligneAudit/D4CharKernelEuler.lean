import VOA.DeligneAudit.D4CharThetaSpectators

/-! Each transported Euler factor is the corresponding existing factor in D4K.S. -/

namespace VOA.DeligneAudit.D4Char

open DeligneCharacter PowerSeries

noncomputable section

/-- The abstract inverse Euler series over the actual Laurent coefficient ring. -/
theorem rsEulerInv_R (a : D4K.R) :
    gtEulerInv rsNome rsPochhammerUnits a = rescale a (D4K.liftS D4K.eInv) := by
  apply PowerSeries.ext
  intro n
  simp only [gtEulerInv, coeff_mk, coeff_rescale, D4K.liftS, coeff_map, D4K.eInv,
    rsInvPoch_R]
  exact mul_comm _ _

/-- The abstract positive Euler series over the actual Laurent coefficient ring. -/
theorem rsEulerPos_R (a : D4K.R) :
    gtEulerPos rsNome rsPochhammerUnits a = rescale a (D4K.liftS D4K.ePos) := by
  apply PowerSeries.ext
  intro n
  simp only [gtEulerPos, coeff_mk, coeff_rescale, D4K.liftS, coeff_map, D4K.ePos]
  rw [rsInvPoch_R]
  simp only [rsNome, map_mul, map_pow, map_neg, map_one]
  ring

/-- The inverse hypermultiplet factor, with arbitrary Laurent weight and scalar. -/
theorem rsEulerInv_EInv (v : D4K.V) (c : D4K.Kq) :
    gtEulerInv rsNome rsPochhammerUnits (D4K.mon v c) =
      D4K.EInv c v 1 one_ne_zero := by
  rw [D4K.EInv, expand_one_apply, rsEulerInv_R]

/-- An Euler numerator factor of any positive s-degree. -/
theorem rsEulerPos_EPos (v : D4K.V) (c : D4K.Kq) (k : ℕ) (hk : k ≠ 0) :
    expand k hk (gtEulerPos rsNome rsPochhammerUnits (D4K.mon v c)) =
      D4K.EPos c v k hk := by
  rw [rsEulerPos_R]
  rfl

/-- Homogeneous rescaling of an inverse factor multiplies its Laurent monomial. -/
theorem rsRescale_EInv (v w : D4K.V) (c : D4K.Kq) :
    rescale (D4K.mon w 1) (gtEulerInv rsNome rsPochhammerUnits (D4K.mon v c)) =
      D4K.EInv c (w + v) 1 one_ne_zero := by
  rw [rsEulerInv_R, rescale_rescale, D4K.mon_mul_mon, mul_one, add_comm v w, ← rsEulerInv_R,
    rsEulerInv_EInv]

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.rsEulerInv_R
#print axioms VOA.DeligneAudit.D4Char.rsEulerPos_R
#print axioms VOA.DeligneAudit.D4Char.rsEulerInv_EInv
#print axioms VOA.DeligneAudit.D4Char.rsEulerPos_EPos
#print axioms VOA.DeligneAudit.D4Char.rsRescale_EInv
