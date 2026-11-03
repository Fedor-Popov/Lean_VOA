/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.LatticeTwistedGeneralBase
import VOA.Moonshine.LatticeTwistedLeading

/-! # Charge-parametric leading for even lattices
Adapted from `LatticeTwistedLeading` using only `TwistedCharge` relations.
The existing generic oscillator and lattice-state results are reused. -/
namespace VOA.Moonshine.LatticeTwistedGeneral
open LatticeTwisted MvPolynomial TwistedHeisenberg TwistedReduction HeisenbergN
open IntegralLattice LatGen Extraspecial
open Module (End)
open scoped BigOperators TensorProduct

section Lattice

open IntegralLattice LatGen Extraspecial

variable (L : IntegralLattice.{0}) (hEven : L.Even) (C : TwistedCharge L) (hPos : L.PosDef)

include hPos in
theorem cfT_YTL_YTL (α β : L.carrier) (k k' : ℤ)
    (t : Space L hEven C) :
    cfT 0 (YTL L hEven C α k (YTL L hEven C β k' (1 ⊗ₜ[ℂ] t)))
      = ((2 : ℂ) ^ (-(L.form α α)) * (2 : ℂ) ^ (-(L.form β β))
          * (if (-k - 2 + L.form α α) + (-k' - 2 + L.form β β) = 0 then
              fz ((L.form α β : ℤ) : ℂ) (-(-k - 2 + L.form α α)) else 0))
        • eT L hEven C α (eT L hEven C β t) := by
  rw [YTL_tmul, map_smul, YTL_tmul, map_smul, map_smul, cfT_tmul, smul_smul, smul_smul]
  rw [show coeff 0 (DD (chargeCoord L α) (-k - 2 + L.form α α) (DD (chargeCoord L β)
      (-k' - 2 + L.form β β) 1)) = constantCoeff (DD (chargeCoord L α) (-k - 2 + L.form α α)
        (DD (chargeCoord L β) (-k' - 2 + L.form β β) 1)) by rw [MvPolynomial.constantCoeff_eq],
    constantCoeff_DD_DD, show pair (chargeCoord L α) (chargeCoord L β) = ((L.form α β : ℤ) : ℂ) from
      sum_chargeCoord L hPos α β]
  congr 1
  ring

include hPos in
theorem cfT_YTL_YTL_swap (α β : L.carrier) (k k' : ℤ)
    (t : Space L hEven C) :
    cfT 0 (YTL L hEven C β k' (YTL L hEven C α k (1 ⊗ₜ[ℂ] t)))
      = ((2 : ℂ) ^ (-(L.form α α)) * (2 : ℂ) ^ (-(L.form β β))
          * (if (-k - 2 + L.form α α) + (-k' - 2 + L.form β β) = 0 then
              (-1 : ℂ) ^ (L.form α β) * fz ((L.form α β : ℤ) : ℂ) (-(-k' - 2 + L.form β β))
            else 0))
        • eT L hEven C α (eT L hEven C β t) := by
  rw [cfT_YTL_YTL L hEven C hPos β α k' k t, form_symm L β α,
    show eT L hEven C β (eT L hEven C α t) = (eT L hEven C β * eT L hEven C α) t from rfl,
    eT_swap, LinearMap.smul_apply, ← neg_one_zpow_eq_pow_natAbs, smul_smul]
  congr 1
  by_cases h : (-k - 2 + L.form α α) + (-k' - 2 + L.form β β) = 0
  · rw [if_pos (by omega), if_pos h]; ring
  · rw [if_neg (by omega), if_neg h]; ring

include hPos in
theorem cfT_prod_YTL (α β : L.carrier) (e e' ℓ N : ℤ)
    (t : Space L hEven C) :
    cfT 0 (mode (Fld.prod ℓ (YTLFld L hEven C α e) (YTLFld L hEven C β e')).1 N (1 ⊗ₜ[ℂ] t))
      = ((2 : ℂ) ^ (-(L.form α α)) * (2 : ℂ) ^ (-(L.form β β))
          * (if 2 * (ℓ + N) + e + e' + 4 = L.form α α + L.form β β then
              Vf (L.form α β) (L.form α α - 2 - e) ℓ else 0))
        • eT L hEven C α (eT L hEven C β t) := by
  obtain ⟨K1, hK1⟩ := YTL_truncation L hEven C β (1 ⊗ₜ[ℂ] t)
  obtain ⟨K2, hK2⟩ := YTL_truncation L hEven C α (1 ⊗ₜ[ℂ] t)
  set J : ℕ := (K1 - 2 * N - e').natAbs + (K2 - e).natAbs
    + (2 * ℓ - (L.form α α - 2 - e)).natAbs + (L.form α α - 2 - e).natAbs + 1 with hJ
  rw [Fld.mode_prod_iterate, finsum_eq_sum_of_support_subset _ (s := Finset.range J) (by
    intro j hj
    rw [Function.mem_support] at hj
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hc
    refine hj ?_
    rw [mode_YTLFld, mode_YTLFld, mode_YTLFld, mode_YTLFld, hK1 _ (by omega), hK2 _ (by omega),
      map_zero, map_zero, smul_zero, sub_zero, smul_zero]), map_sum,
    Vf_eq_range _ _ _ J (by omega) (by omega)]
  by_cases hc : 2 * (ℓ + N) + e + e' + 4 = L.form α α + L.form β β
  · rw [if_pos hc, Finset.mul_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, map_sub, map_smul, mode_YTLFld, mode_YTLFld, mode_YTLFld, mode_YTLFld,
      cfT_YTL_YTL L hEven C hPos, cfT_YTL_YTL_swap L hEven C hPos, if_pos (by omega),
      if_pos (by omega), smul_smul, ← sub_smul, smul_smul]
    congr 1
    rw [show -(-(2 * (ℓ - (j : ℤ)) + e) - 2 + L.form α α)
        = 2 * ℓ - 2 * (j : ℤ) - (L.form α α - 2 - e) by ring,
      show -(-(2 * (ℓ + N - (j : ℤ)) + e') - 2 + L.form β β)
        = L.form α α - 2 - e - 2 * (j : ℤ) by omega,
      zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
    ring
  · rw [if_neg hc, mul_zero, zero_smul]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [map_smul, map_sub, map_smul, mode_YTLFld, mode_YTLFld, mode_YTLFld, mode_YTLFld,
      cfT_YTL_YTL L hEven C hPos, cfT_YTL_YTL_swap L hEven C hPos, if_neg (by omega),
      if_neg (by omega)]
    simp

theorem Vf_eq_zero (n r' Q : ℤ) (h : (n.natAbs : ℤ) ≤ Q) : Vf n r' Q = 0 := by
  rw [Vf_taylor]
  exact Finset.sum_eq_zero fun u _ => by rw [if_neg (by omega), mul_zero]

include hPos in
theorem cfT_star_YTL (α β : L.carrier) (e e' q : ℤ) (I : ℕ)
    (hI : ((L.form α β).natAbs : ℤ) - q ≤ I)
    (t : Space L hEven C) :
    cfT 0 (mode (star ((e : ℂ) / 2) (YTLFld L hEven C α e) q (YTLFld L hEven C β e')).1 0
        (1 ⊗ₜ[ℂ] t))
      = ((2 : ℂ) ^ (-(L.form α α)) * (2 : ℂ) ^ (-(L.form β β))
          * (if 2 * q + e + e' + 4 = L.form α α + L.form β β then
              ∑ i ∈ Finset.range I, cbinom (-((e : ℂ) / 2)) i
                * Vf (L.form α β) (L.form α α - 2 - e) (q + i) else 0))
        • eT L hEven C α (eT L hEven C β t) := by
  have hloc := FLloc L hEven C hPos e e' (echg L α) (echg L β)
  rw [FL_echg L hEven C hPos, FL_echg L hEven C hPos] at hloc
  obtain ⟨K, hK⟩ := exists_prod_offset_zero hloc q
  rw [star_eq_sum_range _ _ q _ (K + I) (fun i hi => hK i (by omega))]
  change cfT 0 (modeL 0 _ (1 ⊗ₜ[ℂ] t)) = _
  rw [map_sum, LinearMap.sum_apply, map_sum]
  simp only [map_smul, LinearMap.smul_apply, modeL_apply, mode_fzmul, cfT_prod_YTL L hEven C hPos,
    smul_smul]
  rw [← Finset.sum_smul]
  congr 1
  by_cases hc : 2 * q + e + e' + 4 = L.form α α + L.form β β
  · rw [if_pos hc, ← Finset.sum_range_eq_of_vanish' I (K + I) (by omega) (fun i _ hi => by
      rw [Vf_eq_zero _ _ _ (by omega), mul_zero]), Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [if_pos (by omega)]
    ring
  · rw [if_neg hc, mul_zero]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [if_neg (by omega), mul_zero, mul_zero]

end Lattice

end VOA.Moonshine.LatticeTwistedGeneral
