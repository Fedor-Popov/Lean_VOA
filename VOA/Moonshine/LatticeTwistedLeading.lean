/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.LatticeTwistedScalar

/-!
# Vacuum expectations of twisted products of exponentials  (Moonshine step M6)

The vacuum-to-vacuum component `cfT 0 (Φ (1 ⊗ t))` of the twisted products of two twisted
exponential fields, in terms of the scalar sums `Vf` of `LatticeTwistedScalar`:

* `constantCoeff_sMz`, `DD_one`, `constantCoeff_DD_DD` — the two-point function of the
  dressings, `⟨1| DD v A DD u B |1⟩ = δ_{A+B,0} fco(⟨v,u⟩)_{−A}`;
* `cfT_YTL_YTL` — the two-point function of the twisted exponentials;
* `cfT_star_YTL` — the vacuum expectation of the `q`-th twisted product:
  `⟨1| (star (e/2) F_e(e^α) q F_{e'}(e^β))₀ |1⟩
     = 2^{−|α|²−|β|²} δ_{2q+e+e'+4, |α|²+|β|²} Σ_i C(−e/2,i) V(|α|²−2−e, q+i) · e_α e_β`.

## Status
All declarations `sorry`-free; `#print axioms` gives `[propext, Classical.choice, Quot.sound]`.
-/

namespace VOA.Moonshine.LatticeTwisted

open MvPolynomial TwistedHeisenberg TwistedReduction HeisenbergN
open Module (End)
open scoped BigOperators TensorProduct

section Dressing

variable {r : ℕ}

theorem constantCoeff_sM (v : Fin r → ℂ) (p : ℕ) :
    constantCoeff (sM v p) = if p = 0 then 1 else 0 := by
  have h := nexp_map (MvPolynomial.aeval (0 : ℕ × Fin r → ℂ)) (dM v) p
  rw [MvPolynomial.aeval_zero] at h
  have hd : (fun k => (MvPolynomial.aeval (0 : ℕ × Fin r → ℂ)) (dM v k)) = 0 := by
    funext k
    rw [MvPolynomial.aeval_zero]
    simp only [dM, vVarT, Pi.zero_apply]
    split_ifs
    · simp
    · simp
  have h0 : nexp (0 : ℕ → ℂ) p = if p = 0 then 1 else 0 := by
    rw [← coeff_nexpPS, nexpPS_zero, PowerSeries.coeff_one]
  rw [hd, h0] at h
  simpa [sM] using h

theorem constantCoeff_sMz (v : Fin r → ℂ) (p : ℤ) :
    constantCoeff (sMz v p) = if p = 0 then 1 else 0 := by
  rcases lt_or_ge p 0 with hp | hp
  · rw [sMz_of_neg v hp, map_zero, if_neg (by omega)]
  · obtain ⟨P, rfl⟩ : ∃ P : ℕ, p = P := ⟨p.toNat, by omega⟩
    rw [sMz_natCast, constantCoeff_sM]
    simp

theorem EpC_one (v : Fin r → ℂ) (q : ℕ) : EpC v q (1 : FockT r) = if q = 0 then 1 else 0 := by
  rw [show (1 : FockT r) = MvPolynomial.C 1 by rw [map_one], EpC_C]

theorem DD_one (v : Fin r → ℂ) (A : ℤ) : DD v A (1 : FockT r) = sMz v A := by
  rw [DD_apply_range v A 1 1 (fun q hq => by rw [EpC_one, if_neg (by omega)]),
    Finset.sum_range_one, EpC_one, if_pos rfl, Nat.cast_zero, add_zero, mul_one]

/-- **The two-point function of the dressings.** -/
theorem constantCoeff_DD_DD (v u : Fin r → ℂ) (A B : ℤ) :
    constantCoeff (DD v A (DD u B (1 : FockT r)))
      = if A + B = 0 then fz (pair v u) (-A) else 0 := by
  set J : ℕ := B.natAbs + 1
  rw [DD_one, show sMz u B = sMz u B * 1 by rw [mul_one],
    DD_sMz_mul v u A B 1 1 (fun q hq => by rw [EpC_one, if_neg (by omega)]) J (by omega),
    map_sum]
  simp only [Finset.sum_range_one, Nat.cast_zero, add_zero, EpC_one, if_true, mul_one,
    MvPolynomial.smul_eq_C_mul, map_mul, constantCoeff_C, constantCoeff_sMz]
  by_cases hAB : A + B = 0
  · rw [if_pos hAB]
    rcases lt_or_ge (-A) 0 with hA | hA
    · rw [fz, if_neg (by omega)]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [if_neg (by omega), zero_mul, mul_zero]
    · rw [Finset.sum_eq_single (-A).toNat (fun j _ hj => by rw [if_neg (by omega), zero_mul,
        mul_zero]) (fun h => absurd (Finset.mem_range.mpr (by omega)) h),
        if_pos (by omega), if_pos (by omega), mul_one, mul_one, fz, if_pos hA]
  · rw [if_neg hAB]
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases h1 : A + j = 0
    · rw [if_pos h1, if_neg (by omega), mul_zero, mul_zero]
    · rw [if_neg h1, zero_mul, mul_zero]

end Dressing

section Lattice

open IntegralLattice LatGen Extraspecial

variable (L : IntegralLattice.{0}) (hEven : L.Even) (hU : IsUnit (gramMat L).det) (hPos : L.PosDef)

include hPos in
/-- **The two-point function of the twisted exponentials.** -/
theorem cfT_YTL_YTL (α β : L.carrier) (k k' : ℤ)
    (t : Rep (cocMat L) (isUnit_det_cocMat L hEven hU)) :
    cfT 0 (YTL L hEven hU α k (YTL L hEven hU β k' (1 ⊗ₜ[ℂ] t)))
      = ((2 : ℂ) ^ (-(L.form α α)) * (2 : ℂ) ^ (-(L.form β β))
          * (if (-k - 2 + L.form α α) + (-k' - 2 + L.form β β) = 0 then
              fz ((L.form α β : ℤ) : ℂ) (-(-k - 2 + L.form α α)) else 0))
        • eT L hEven hU α (eT L hEven hU β t) := by
  rw [YTL_tmul, map_smul, YTL_tmul, map_smul, map_smul, cfT_tmul, smul_smul, smul_smul]
  rw [show coeff 0 (DD (chargeCoord L α) (-k - 2 + L.form α α) (DD (chargeCoord L β)
      (-k' - 2 + L.form β β) 1)) = constantCoeff (DD (chargeCoord L α) (-k - 2 + L.form α α)
        (DD (chargeCoord L β) (-k' - 2 + L.form β β) 1)) by rw [MvPolynomial.constantCoeff_eq],
    constantCoeff_DD_DD, show pair (chargeCoord L α) (chargeCoord L β) = ((L.form α β : ℤ) : ℂ) from
      sum_chargeCoord L hPos α β]
  congr 1
  ring

include hPos in
/-- The two-point function, with the exponentials in the opposite order. -/
theorem cfT_YTL_YTL_swap (α β : L.carrier) (k k' : ℤ)
    (t : Rep (cocMat L) (isUnit_det_cocMat L hEven hU)) :
    cfT 0 (YTL L hEven hU β k' (YTL L hEven hU α k (1 ⊗ₜ[ℂ] t)))
      = ((2 : ℂ) ^ (-(L.form α α)) * (2 : ℂ) ^ (-(L.form β β))
          * (if (-k - 2 + L.form α α) + (-k' - 2 + L.form β β) = 0 then
              (-1 : ℂ) ^ (L.form α β) * fz ((L.form α β : ℤ) : ℂ) (-(-k' - 2 + L.form β β))
            else 0))
        • eT L hEven hU α (eT L hEven hU β t) := by
  rw [cfT_YTL_YTL L hEven hU hPos β α k' k t, form_symm L β α,
    show eT L hEven hU β (eT L hEven hU α t) = (eT L hEven hU β * eT L hEven hU α) t from rfl,
    eT_swap, LinearMap.smul_apply, ← neg_one_zpow_eq_pow_natAbs, smul_smul]
  congr 1
  by_cases h : (-k - 2 + L.form α α) + (-k' - 2 + L.form β β) = 0
  · rw [if_pos (by omega), if_pos h]; ring
  · rw [if_neg (by omega), if_neg h]; ring

include hPos in
/-- **The vacuum expectation of a product of two twisted exponentials.** -/
theorem cfT_prod_YTL (α β : L.carrier) (e e' ℓ N : ℤ)
    (t : Rep (cocMat L) (isUnit_det_cocMat L hEven hU)) :
    cfT 0 (mode (Fld.prod ℓ (YTLFld L hEven hU α e) (YTLFld L hEven hU β e')).1 N (1 ⊗ₜ[ℂ] t))
      = ((2 : ℂ) ^ (-(L.form α α)) * (2 : ℂ) ^ (-(L.form β β))
          * (if 2 * (ℓ + N) + e + e' + 4 = L.form α α + L.form β β then
              Vf (L.form α β) (L.form α α - 2 - e) ℓ else 0))
        • eT L hEven hU α (eT L hEven hU β t) := by
  obtain ⟨K1, hK1⟩ := YTL_truncation L hEven hU β (1 ⊗ₜ[ℂ] t)
  obtain ⟨K2, hK2⟩ := YTL_truncation L hEven hU α (1 ⊗ₜ[ℂ] t)
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
      cfT_YTL_YTL L hEven hU hPos, cfT_YTL_YTL_swap L hEven hU hPos, if_pos (by omega),
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
      cfT_YTL_YTL L hEven hU hPos, cfT_YTL_YTL_swap L hEven hU hPos, if_neg (by omega),
      if_neg (by omega)]
    simp

theorem Vf_eq_zero (n r' Q : ℤ) (h : (n.natAbs : ℤ) ≤ Q) : Vf n r' Q = 0 := by
  rw [Vf_taylor]
  exact Finset.sum_eq_zero fun u _ => by rw [if_neg (by omega), mul_zero]

include hPos in
/-- **The vacuum expectation of the twisted product of two twisted exponentials.** -/
theorem cfT_star_YTL (α β : L.carrier) (e e' q : ℤ) (I : ℕ)
    (hI : ((L.form α β).natAbs : ℤ) - q ≤ I)
    (t : Rep (cocMat L) (isUnit_det_cocMat L hEven hU)) :
    cfT 0 (mode (star ((e : ℂ) / 2) (YTLFld L hEven hU α e) q (YTLFld L hEven hU β e')).1 0
        (1 ⊗ₜ[ℂ] t))
      = ((2 : ℂ) ^ (-(L.form α α)) * (2 : ℂ) ^ (-(L.form β β))
          * (if 2 * q + e + e' + 4 = L.form α α + L.form β β then
              ∑ i ∈ Finset.range I, cbinom (-((e : ℂ) / 2)) i
                * Vf (L.form α β) (L.form α α - 2 - e) (q + i) else 0))
        • eT L hEven hU α (eT L hEven hU β t) := by
  have hloc := FLloc L hEven hU hPos e e' (echg L α) (echg L β)
  rw [FL_echg L hEven hU hPos, FL_echg L hEven hU hPos] at hloc
  obtain ⟨K, hK⟩ := exists_prod_offset_zero hloc q
  rw [star_eq_sum_range _ _ q _ (K + I) (fun i hi => hK i (by omega))]
  change cfT 0 (modeL 0 _ (1 ⊗ₜ[ℂ] t)) = _
  rw [map_sum, LinearMap.sum_apply, map_sum]
  simp only [map_smul, LinearMap.smul_apply, modeL_apply, mode_fzmul, cfT_prod_YTL L hEven hU hPos,
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

end VOA.Moonshine.LatticeTwisted
