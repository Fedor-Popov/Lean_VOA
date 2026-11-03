import VOA.DeligneAudit.D4CharRogersOrthogonal
import VOA.DeligneAudit.D4CharDownEuler
import VOA.DeligneAudit.DeligneCharacterD4Schur

/-! The integral q-series embedding and the scalar normalizations in the D4 kernel ring. -/

namespace VOA.DeligneAudit.D4Char

open DeligneCharacter PowerSeries

noncomputable section

/-- Embed a scalar in the actual D4 Laurent ring. -/
abbrev rsCoeff : D4K.Kq →+* D4K.R := algebraMap D4K.Kq D4K.R

/-- The nome of the mixed-Cauchy identity in the D4 Laurent ring. -/
def rsNome : D4K.R := rsCoeff D4K.qq

theorem rsQUnits : PochhammerUnits D4K.qq := by
  intro n
  exact isUnit_iff_ne_zero.mpr (D4K.qpoch_ne_zero n)

theorem rsPochhammerUnits : PochhammerUnits rsNome :=
  gtPochhammerUnits_map rsCoeff D4K.qq rsQUnits

/-- The abstract unit inverse is exactly the kernel's inverse Pochhammer. -/
theorem rsInvPoch_eq (n : ℕ) :
    gtInvPoch D4K.qq rsQUnits n = (D4K.qpoch n)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [mul_comm]
  exact gtPoch_mul_invPoch D4K.qq rsQUnits n

/-- The same normalization after embedding in the Laurent coefficient ring. -/
theorem rsInvPoch_R (n : ℕ) :
    gtInvPoch rsNome rsPochhammerUnits n = rsCoeff ((D4K.qpoch n)⁻¹) := by
  exact (gtInvPoch_map rsCoeff D4K.qq rsQUnits n).symm.trans
    (congrArg rsCoeff (rsInvPoch_eq n))

/-- The formal integral q-series map is injective, using all even r-coefficients. -/
theorem rsJmap_injective : Function.Injective D4K.jmap := by
  intro f g h
  apply PowerSeries.ext
  intro n
  have he := congrArg (fun F : D4K.Kq => F.coeff (2 * (n : ℤ))) h
  dsimp only at he
  rw [D4K.jmap_coeff_even, D4K.jmap_coeff_even] at he
  exact_mod_cast he

/-- Integral reciprocal Pochhammer coefficients specialize to the actual kernel values. -/
theorem rsJmap_invPoch (n : ℕ) :
    D4K.jmap (gtInvPoch (X : PowerSeries ℤ) (powerSeries_pochhammerUnits ℤ) n) =
      (D4K.qpoch n)⁻¹ := by
  have h := congrArg D4K.jmap
    (gtPoch_mul_invPoch (X : PowerSeries ℤ) (powerSeries_pochhammerUnits ℤ) n)
  have hp : D4K.jmap (CarrierChain.qpochGen (X : PowerSeries ℤ) n) = D4K.qpoch n := by
    simp only [CarrierChain.qpochGen, D4K.qpoch, map_prod, map_sub, map_one,
      map_pow, D4K.jmap_X]
  rw [map_mul, hp, map_one] at h
  apply eq_inv_of_mul_eq_one_left
  simpa only [mul_comm] using h

/-- The integral Euler inverse specializes to D4K.eInv. -/
theorem rsJmap_eulerInv :
    PowerSeries.map D4K.jmap
      (gtEulerInv (X : PowerSeries ℤ) (powerSeries_pochhammerUnits ℤ) 1) = D4K.eInv := by
  apply PowerSeries.ext
  intro n
  simp only [coeff_map, gtEulerInv, coeff_mk, one_pow, mul_one, D4K.eInv,
    rsJmap_invPoch]

/-- The integral Euler product specializes to D4K.ePos. -/
theorem rsJmap_eulerPos :
    PowerSeries.map D4K.jmap
      (gtEulerPos (X : PowerSeries ℤ) (powerSeries_pochhammerUnits ℤ) 1) = D4K.ePos := by
  apply PowerSeries.ext
  intro n
  simp only [coeff_map, gtEulerPos, coeff_mk, one_pow, mul_one, D4K.ePos,
    map_mul, map_pow, map_neg, map_one, D4K.jmap_X, rsJmap_invPoch]

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.rsQUnits
#print axioms VOA.DeligneAudit.D4Char.rsPochhammerUnits
#print axioms VOA.DeligneAudit.D4Char.rsInvPoch_eq
#print axioms VOA.DeligneAudit.D4Char.rsInvPoch_R
#print axioms VOA.DeligneAudit.D4Char.rsJmap_injective
#print axioms VOA.DeligneAudit.D4Char.rsJmap_invPoch
#print axioms VOA.DeligneAudit.D4Char.rsJmap_eulerInv
#print axioms VOA.DeligneAudit.D4Char.rsJmap_eulerPos
