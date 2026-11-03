/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneMLDECubicOrders
import VOA.DeligneAudit.DeligneMLDECubicG2
import VOA.DeligneAudit.G2StarRiccati

/-!
# The `G2Level3EisLambert` from the heat equation at `u = ω eˣ`

The rational parts of orders `x⁰…x⁴` of the heat identity (*) at `u = ω eˣ`
(`level3_l0`, `level3_order1` … `level3_order4`), their `θ`-derivatives, and Ramanujan's identities at `q` and `q³`
imply, as explicit ideal memberships (certificates computed with sympy outside Lean;
checked here by `linear_combination`):

* `α : P₃ = 6P₁² - 36P₁P₁(q³) + P₁ + 54P₁(q³)² - 3P₁(q³) - 9P₃(q³)`,
* `β`, a weight-6 relation expressing `P₅ + 27P₅(q³)`,
* `δ`, a weight-8 relation involving `P₅(q³)`,

and from these, with `a = 1 + 6L₀` (`lambertA2`), the three relations of `G2Star.G2Level3EisLambert`:
`2a² = 3E₂(q³) - E₂`, `10a⁴ = E₄ + 9E₄(q³)` and the weight-12 relation `l6`.
-/

namespace VOA.DeligneAudit.DeligneMLDE.Heat

open PowerSeries VOA.QSeries VOA.QSeries.JTP

noncomputable section

theorem ps_natCast_ne_zero {n : ℕ} (hn : n ≠ 0) : (n : PowerSeries ℚ) ≠ 0 := by
  intro h
  have := congrArg constantCoeff h
  rw [map_natCast, map_zero] at this
  exact hn (by exact_mod_cast this)

theorem eulerOp_zero' : eulerOp (0 : PowerSeries ℚ) = 0 := by
  refine PowerSeries.ext fun n => ?_; simp

theorem eulerOp_neg (F : PowerSeries ℚ) : eulerOp (-F) = -eulerOp F := by
  refine PowerSeries.ext fun n => ?_; simp

theorem eulerOp_natMul (c : ℕ) [c.AtLeastTwo] (F : PowerSeries ℚ) :
    eulerOp ((OfNat.ofNat c : PowerSeries ℚ) * F) = (OfNat.ofNat c : PowerSeries ℚ) * eulerOp F := by
  rw [show (OfNat.ofNat c : PowerSeries ℚ) = PowerSeries.C (OfNat.ofNat c) from (map_ofNat _ c).symm,
    eulerOp_C_mul]

theorem eulerOp_ofNat' (c : ℕ) [c.AtLeastTwo] :
    eulerOp (no_index (OfNat.ofNat c : PowerSeries ℚ)) = 0 := by
  rw [show (OfNat.ofNat c : PowerSeries ℚ) = PowerSeries.C (OfNat.ofNat c) * 1 by
    rw [mul_one]; exact (map_ofNat _ c).symm, eulerOp_C_mul, eulerOp_one, mul_zero]

theorem eulerOp_ex3 (F : PowerSeries ℚ) : eulerOp (ex3 F) = 3 * ex3 (eulerOp F) := by
  refine PowerSeries.ext fun n => ?_
  rw [coeff_eulerOp, show (3 : PowerSeries ℚ) = PowerSeries.C 3 from (map_ofNat _ 3).symm,
    coeff_C_mul, coeff_expand, coeff_expand]
  split_ifs with h
  · obtain ⟨t, rfl⟩ := h
    rw [Nat.mul_div_cancel_left _ (by norm_num), coeff_eulerOp]; push_cast; ring
  · simp

/-- Splitting off the multiples of `3`: `lamQ (G d · cc₃(k) · kʲ) = -lamQ (G d kʲ) + 3^{j+1} (lamQ (G d kʲ))(q³)`. -/
theorem lamQ_cc3 (Gd : ℕ → ℚ) (j : ℕ) :
    lamQ (fun d k => Gd d * cc3 k * (k : ℚ) ^ j)
      = -lamQ (fun d k => Gd d * (k : ℚ) ^ j)
        + PowerSeries.C ((3 : ℚ) ^ (j + 1)) * ex3 (lamQ fun d k => Gd d * (k : ℚ) ^ j) := by
  have h : lamQ (fun d k => Gd d * cc3 k * (k : ℚ) ^ j) =
      lamQ (fun d k => -1 * (Gd d * (k : ℚ) ^ j)
        + 3 * (if 3 ∣ k then Gd d * (k : ℚ) ^ j else 0)) := by
    refine lamQ_congr fun d k _ => ?_
    unfold cc3
    by_cases h3 : 3 ∣ k
    · rw [if_pos (Nat.mod_eq_zero_of_dvd h3), if_pos h3]; ring
    · rw [if_neg (fun h' => h3 (Nat.dvd_of_mod_eq_zero h')), if_neg h3]; ring
  rw [h, lamQ_add, lamQ_smul, lamQ_smul, lamQ_dvd3]
  have h2 : lamQ (fun d k => Gd d * ((3 * k : ℕ) : ℚ) ^ j)
      = PowerSeries.C ((3 : ℚ) ^ j) * lamQ (fun d k => Gd d * (k : ℚ) ^ j) := by
    rw [← lamQ_smul]; exact lamQ_congr fun d k _ => by push_cast; ring
  rw [h2, map_mul, show ex3 (PowerSeries.C ((3 : ℚ) ^ j)) = PowerSeries.C ((3 : ℚ) ^ j) from
    by rw [map_pow, show (PowerSeries.C (3 : ℚ)) = 3 from map_ofNat _ 3, map_pow, map_ofNat]]
  simp only [map_neg, map_one, neg_one_mul, map_pow, map_mul, pow_succ]
  ring

theorem P1_pow : P1 = lamQ fun d k => (fun _ => (1 : ℚ)) d * (k : ℚ) ^ 1 := by
  rw [P1]; exact lamQ_congr fun d k _ => by simp

theorem XM1_eq : XM 1 = -P1 + 9 * ex3 P1 := by
  have h := lamQ_cc3 (fun _ => 1) 1
  rw [← P1_pow] at h
  rw [XM, show (9 : PowerSeries ℚ) = PowerSeries.C ((3 : ℚ) ^ (1 + 1)) by rw [map_pow, map_ofNat]; norm_num, ← h]
  exact lamQ_congr fun d k _ => by ring

theorem XM3_eq : XM 3 = -P3 + 81 * ex3 P3 := by
  have h := lamQ_cc3 (fun _ => 1) 3
  have hP : lamQ (fun d k => (fun _ => (1 : ℚ)) d * (k : ℚ) ^ 3) = P3 := by
    rw [P3]; exact lamQ_congr fun d k _ => by ring
  rw [hP] at h
  rw [XM, show (81 : PowerSeries ℚ) = PowerSeries.C ((3 : ℚ) ^ (3 + 1)) by rw [map_pow, map_ofNat]; norm_num, ← h]
  exact lamQ_congr fun d k _ => by ring

theorem XM5_eq : XM 5 = -P5 + 729 * ex3 P5 := by
  have h := lamQ_cc3 (fun _ => 1) 5
  have hP : lamQ (fun d k => (fun _ => (1 : ℚ)) d * (k : ℚ) ^ 5) = P5 := by
    rw [P5]; exact lamQ_congr fun d k _ => by ring
  rw [hP] at h
  rw [XM, show (729 : PowerSeries ℚ) = PowerSeries.C ((3 : ℚ) ^ (5 + 1)) by rw [map_pow, map_ofNat]; norm_num,
    ← h]
  exact lamQ_congr fun d k _ => by ring

theorem XN2_eq : XN 2 = -eulerOp P1 + 27 * ex3 (eulerOp P1) := by
  have h := lamQ_cc3 (fun d => (d : ℚ)) 2
  rw [← eulerOp_P1] at h
  rw [XN, show (27 : PowerSeries ℚ) = PowerSeries.C ((3 : ℚ) ^ (2 + 1)) by rw [map_pow, map_ofNat]; norm_num, ← h]

theorem XN4_eq : XN 4 = -eulerOp P3 + 243 * ex3 (eulerOp P3) := by
  have h := lamQ_cc3 (fun d => (d : ℚ)) 4
  rw [← eulerOp_P3] at h
  rw [XN, show (243 : PowerSeries ℚ) = PowerSeries.C ((3 : ℚ) ^ (4 + 1)) by rw [map_pow, map_ofNat]; norm_num,
    ← h]

theorem XD1_eq : XD 1 = eulerOp L0 := by
  rw [XD, L0, eulerOp_lamQ]; exact lamQ_congr fun d k _ => by ring

theorem XD3_eq : XD 3 = eulerOp (XL 2) := by
  rw [XD, XL, eulerOp_lamQ]; exact lamQ_congr fun d k _ => by ring

end

end VOA.DeligneAudit.DeligneMLDE.Heat

namespace VOA.DeligneAudit.G2Star

open PowerSeries VOA.QSeries VOA.QSeries.JTP VOA.DeligneAudit.DeligneMLDE.Heat
  VOA.DeligneAudit.DeligneMLDE.HeatK

noncomputable section

theorem lambertA2_eq : lambertA2 = 1 + 6 * L0 := by
  refine PowerSeries.ext fun n => ?_
  rw [lambertA2, coeff_mk, map_add, coeff_one,
    show (6 : PowerSeries ℚ) = PowerSeries.C 6 from (map_ofNat _ 6).symm, coeff_C_mul, coeff_L0]
  split_ifs with h
  · subst h; simp
  · simp only [zero_add]
    congr 1

theorem E4q_eq_P3 : E4q = 1 + 240 * P3 := by
  rw [E4q, eisQ_eq 4 240 P3 coeff_P3, map_ofNat]

theorem E6q_eq_P5 : E6q = 1 - 504 * P5 := by
  rw [E6q, eisQ_eq 6 (-504) P5 coeff_P5, map_neg, map_ofNat]; ring

set_option maxHeartbeats 4000000 in
/-- **the `G2Level3EisLambert`, proved** from the heat equation at `u = ω eˣ`, Ramanujan's
identities, and explicit ideal-membership certificates. -/
theorem g2Level3EisLambert : G2Level3EisLambert := by
  have hr0 : 3*L0^2 + L0 - P1 + 3*(ex3 P1) = 0 := by linear_combination level3_l0
  have ho1 : -6*L0*P1 + 54*L0*(ex3 P1) - 2*L0 - 3*(XL 2) - P1 + 9*(ex3 P1) + 6*(eulerOp L0) = 0 := by
    have h := level3_order1
    simp only [XL_zero, XM1_eq, XM3_eq, XM5_eq, XN2_eq, XN4_eq, XD1_eq, XD3_eq, N3_eq, map_neg, map_one, map_ofNat] at h
    linear_combination h
  have ho2 : -6*L0*(XL 2) - 8*L0*P1 + 72*L0*(ex3 P1) - 2*L0 - 5*(XL 2) + 2*P1^2 - 36*P1*(ex3 P1) + P3 + 162*(ex3 P1)^2 - 81*(ex3 P3) + 8*(eulerOp L0) + 54*(ex3 (eulerOp P1)) - 2*(eulerOp P1) = 0 := by
    have h := level3_order2
    simp only [XL_zero, XM1_eq, XM3_eq, XM5_eq, XN2_eq, XN4_eq, XD1_eq, XD3_eq, N3_eq, map_neg, map_one, map_ofNat] at h
    linear_combination h
  have ho3 : -12*L0*P1 - 6*L0*P3 + 108*L0*(ex3 P1) + 486*L0*(ex3 P3) - 2*L0 - 18*(XL 2)*P1 + 162*(XL 2)*(ex3 P1) - 12*(XL 2) - 3*(XL 4) - P3 + 81*(ex3 P3) + 12*(eulerOp L0) + 6*(eulerOp (XL 2)) = 0 := by
    have h := level3_order3
    simp only [XL_zero, XM1_eq, XM3_eq, XM5_eq, XN2_eq, XN4_eq, XD1_eq, XD3_eq, N3_eq, map_neg, map_one, map_ofNat] at h
    linear_combination h
  have ho4 : -6*L0*(XL 4) - 16*L0*P1 - 16*L0*P3 + 144*L0*(ex3 P1) + 1296*L0*(ex3 P3) - 2*L0 - 18*(XL 2)^2 - 48*(XL 2)*P1 + 432*(XL 2)*(ex3 P1) - 20*(XL 2) - 9*(XL 4) + 8*P1*P3 - 648*P1*(ex3 P3) - 72*P3*(ex3 P1) + P5 + 5832*(ex3 P1)*(ex3 P3) - 729*(ex3 P5) + 16*(eulerOp L0) + 16*(eulerOp (XL 2)) + 486*(ex3 (eulerOp P3)) - 2*(eulerOp P3) = 0 := by
    have h := level3_order4
    simp only [XL_zero, XM1_eq, XM3_eq, XM5_eq, XN2_eq, XN4_eq, XD1_eq, XD3_eq, N3_eq, map_neg, map_one, map_ofNat] at h
    linear_combination h
  have htr0 : 6*L0*(eulerOp L0) + (eulerOp L0) + 9*(ex3 (eulerOp P1)) - (eulerOp P1) = 0 := by
    have h := congrArg eulerOp hr0
    simp only [eulerOp_add, eulerOp_sub, eulerOp_mul, eulerOp_neg, eulerOp_zero', eulerOp_ofNat', eulerOp_one, eulerOp_ex3, pow_succ, pow_zero, one_mul, neg_mul, zero_mul, mul_zero, zero_add, add_zero] at h
    linear_combination h
  have hto1 : 162*L0*(ex3 (eulerOp P1)) - 6*L0*(eulerOp P1) - 6*P1*(eulerOp L0) + 54*(ex3 P1)*(eulerOp L0) - 2*(eulerOp L0) - 3*(eulerOp (XL 2)) + 6*(eulerOp (eulerOp L0)) + 27*(ex3 (eulerOp P1)) - (eulerOp P1) = 0 := by
    have h := congrArg eulerOp ho1
    simp only [eulerOp_add, eulerOp_sub, eulerOp_mul, eulerOp_neg, eulerOp_zero', eulerOp_ofNat', eulerOp_one, eulerOp_ex3, pow_succ, pow_zero, one_mul, neg_mul, zero_mul, mul_zero, zero_add, add_zero] at h
    linear_combination h
  have hto2 : -6*L0*(eulerOp (XL 2)) + 216*L0*(ex3 (eulerOp P1)) - 8*L0*(eulerOp P1) - 6*(XL 2)*(eulerOp L0) - 8*P1*(eulerOp L0) - 108*P1*(ex3 (eulerOp P1)) + 4*P1*(eulerOp P1) + 72*(ex3 P1)*(eulerOp L0) + 972*(ex3 P1)*(ex3 (eulerOp P1)) - 36*(ex3 P1)*(eulerOp P1) - 2*(eulerOp L0) - 5*(eulerOp (XL 2)) + 8*(eulerOp (eulerOp L0)) - 243*(ex3 (eulerOp P3)) + 162*(ex3 (eulerOp (eulerOp P1))) + (eulerOp P3) - 2*(eulerOp (eulerOp P1)) = 0 := by
    have h := congrArg eulerOp ho2
    simp only [eulerOp_add, eulerOp_sub, eulerOp_mul, eulerOp_neg, eulerOp_zero', eulerOp_ofNat', eulerOp_one, eulerOp_ex3, pow_succ, pow_zero, one_mul, neg_mul, zero_mul, mul_zero, zero_add, add_zero] at h
    linear_combination h
  have htt0 : 6*L0*(eulerOp (eulerOp L0)) + 6*(eulerOp L0)^2 + (eulerOp (eulerOp L0)) + 27*(ex3 (eulerOp (eulerOp P1))) - (eulerOp (eulerOp P1)) = 0 := by
    have h := congrArg eulerOp htr0
    simp only [eulerOp_add, eulerOp_sub, eulerOp_mul, eulerOp_neg, eulerOp_zero', eulerOp_ofNat', eulerOp_one, eulerOp_ex3, pow_succ, pow_zero, one_mul, neg_mul, zero_mul, mul_zero, zero_add, add_zero] at h
    linear_combination h
  have hR1 : 12*P1^2 - P1 - 5*P3 + 6*(eulerOp P1) = 0 := by
    have h := ramanujan
    simp only [map_ofNat] at h
    linear_combination h
  have hR3 : 5760*P1*P3 + 24*P1 - 240*P3 - 504*P5 + 720*(eulerOp P3) = 0 := by
    have h := ramanujan4
    simp only [map_ofNat] at h
    linear_combination h
  have hR5 : 12096*P1*P5 - 24*P1 - 57600*P3^2 - 480*P3 - 504*P5 + 1008*(eulerOp P5) = 0 := by
    have h := ramanujan6
    simp only [map_ofNat] at h
    linear_combination h
  have htR1 : 24*P1*(eulerOp P1) - (eulerOp P1) - 5*(eulerOp P3) + 6*(eulerOp (eulerOp P1)) = 0 := by
    have h := congrArg eulerOp hR1
    simp only [eulerOp_add, eulerOp_sub, eulerOp_mul, eulerOp_neg, eulerOp_zero', eulerOp_ofNat', eulerOp_one, eulerOp_ex3, pow_succ, pow_zero, one_mul, neg_mul, zero_mul, mul_zero, zero_add, add_zero] at h
    linear_combination h
  have hR1q : 12*(ex3 P1)^2 - (ex3 P1) - 5*(ex3 P3) + 6*(ex3 (eulerOp P1)) = 0 := by
    have h := congrArg ex3 hR1
    simp only [map_add, map_sub, map_mul, map_neg, map_pow, map_ofNat, map_zero] at h
    linear_combination h
  have hR3q : 5760*(ex3 P1)*(ex3 P3) + 24*(ex3 P1) - 240*(ex3 P3) - 504*(ex3 P5) + 720*(ex3 (eulerOp P3)) = 0 := by
    have h := congrArg ex3 hR3
    simp only [map_add, map_sub, map_mul, map_neg, map_pow, map_ofNat, map_zero] at h
    linear_combination h
  have hR5q : 12096*(ex3 P1)*(ex3 P5) - 24*(ex3 P1) - 57600*(ex3 P3)^2 - 480*(ex3 P3) - 504*(ex3 P5) + 1008*(ex3 (eulerOp P5)) = 0 := by
    have h := congrArg ex3 hR5
    simp only [map_add, map_sub, map_mul, map_neg, map_pow, map_ofNat, map_zero] at h
    linear_combination h
  have htR1q : 24*(ex3 P1)*(ex3 (eulerOp P1)) - (ex3 (eulerOp P1)) - 5*(ex3 (eulerOp P3)) + 6*(ex3 (eulerOp (eulerOp P1))) = 0 := by
    have h := congrArg ex3 htR1
    simp only [map_add, map_sub, map_mul, map_neg, map_pow, map_ofNat, map_zero] at h
    linear_combination h
  have hα : -6*P1^2 + 36*P1*(ex3 P1) - P1 + P3 - 54*(ex3 P1)^2 + 3*(ex3 P1) + 9*(ex3 P3) = 0 := by
    have key : ((7 : ℕ) : PowerSeries ℚ) * (-6*P1^2 + 36*P1*(ex3 P1) - P1 + P3 - 54*(ex3 P1)^2 + 3*(ex3 P1) + 9*(ex3 P3)) = 0 := by
      linear_combination (12*P1 - 108*(ex3 P1) + 4) * hr0 + (-6) * htr0 + (6*L0 + 5) * ho1 + (-3) * ho2 + (-2) * hR1 + (36) * hR1q
    exact (mul_eq_zero.mp key).resolve_left (ps_natCast_ne_zero (by norm_num))
  have hβ : -120*P1^3 + 1080*P1^2*(ex3 P1) - 30*P1^2 - 3240*P1*(ex3 P1)^2 + 180*P1*(ex3 P1) + 360*P1*(ex3 P3) - P1 + P5 + 3240*(ex3 P1)^3 - 270*(ex3 P1)^2 - 1080*(ex3 P1)*(ex3 P3) + 3*(ex3 P1) + 30*(ex3 P3) + 27*(ex3 P5) = 0 := by
    have key : ((3528 : ℕ) : PowerSeries ℚ) * (-120*P1^3 + 1080*P1^2*(ex3 P1) - 30*P1^2 - 3240*P1*(ex3 P1)^2 + 180*P1*(ex3 P1) + 360*P1*(ex3 P3) - P1 + P5 + 3240*(ex3 P1)^3 - 270*(ex3 P1)^2 - 1080*(ex3 P1)*(ex3 P3) + 3*(ex3 P1) + 30*(ex3 P3) + 27*(ex3 P5)) = 0 := by
      linear_combination (-25920*L0^2 - 8640*L0 + 99360*P1 - 177120*(ex3 P1) - 840) * hα + (-69120*P1^2 + 311040*P1*(ex3 P1) - 1440*P1 + 15840*P3 - 64800*(ex3 P1) - 116640*(ex3 P3) + 1920) * hr0 + (2880*L0 + 4320*(eulerOp L0) + 2400) * ho1 + (-1440) * ho2 + (8640*P1 - 77760*(ex3 P1)) * htr0 + (4320*L0 + 3600) * hto1 + (-2160) * hto2 + (-4320) * htt0 + (4320*L0^2 + 1440*L0 + 8640*P1 - 25920*(ex3 P1) - 120) * hR1 + (-116640*L0^2 - 38880*L0 - 51840*P1 + 155520*(ex3 P1) + 9720) * hR1q + (-1440) * htR1 + (77760) * htR1q + (-7) * hR3 + (-189) * hR3q
    exact (mul_eq_zero.mp key).resolve_left (ps_natCast_ne_zero (by norm_num))
  have hδ : 36*P1^4 - 432*P1^3*(ex3 P1) + 12*P1^3 + 1944*P1^2*(ex3 P1)^2 - 108*P1^2*(ex3 P1) - 360*P1^2*(ex3 P3) - 3888*P1*(ex3 P1)^3 + 324*P1*(ex3 P1)^2 + 2160*P1*(ex3 P1)*(ex3 P3) - 60*P1*(ex3 P3) - 84*P1*(ex3 P5) + 2916*(ex3 P1)^4 - 324*(ex3 P1)^3 - 3240*(ex3 P1)^2*(ex3 P3) + 180*(ex3 P1)*(ex3 P3) + 252*(ex3 P1)*(ex3 P5) - 300*(ex3 P3)^2 - 5*(ex3 P3) - 7*(ex3 P5) = 0 := by
    have key : ((38880 : ℕ) : PowerSeries ℚ) * (36*P1^4 - 432*P1^3*(ex3 P1) + 12*P1^3 + 1944*P1^2*(ex3 P1)^2 - 108*P1^2*(ex3 P1) - 360*P1^2*(ex3 P3) - 3888*P1*(ex3 P1)^3 + 324*P1*(ex3 P1)^2 + 2160*P1*(ex3 P1)*(ex3 P3) - 60*P1*(ex3 P3) - 84*P1*(ex3 P5) + 2916*(ex3 P1)^4 - 324*(ex3 P1)^3 - 3240*(ex3 P1)^2*(ex3 P3) + 180*(ex3 P1)*(ex3 P3) + 252*(ex3 P1)*(ex3 P5) - 300*(ex3 P3)^2 - 5*(ex3 P3) - 7*(ex3 P5)) = 0 := by
      linear_combination (-233280*L0*(XL 2) + 311040*L0*(eulerOp L0) + 25920*L0 - 38880*(XL 2) + 8640*P1^2 + 570240*P1*(ex3 P1) - 24480*P1 - 2880*P3 - 1788480*(ex3 P1)^2 + 125280*(ex3 P1) + 103680*(ex3 P3) + 51840*(eulerOp L0) + 2640) * hα + (-6912*P1 + 20736*(ex3 P1) - 576) * hβ + (-466560*(XL 2)^2 + 622080*(XL 2)*(eulerOp L0) + 103680*(XL 2) - 86400*P1*P3 + 6998400*P1*(ex3 P3) + 28800*P1 + 466560*P3*(ex3 P1) - 15840*P3 - 37791360*(ex3 P1)*(ex3 P3) - 155520*(ex3 P1) + 1283040*(ex3 P3) - 69120*(eulerOp L0) - 480) * hr0 + (311040*L0*(XL 2) + 51840*L0*P1 - 17280*L0*P3 - 155520*L0*(ex3 P1) + 1399680*L0*(ex3 P3) - 414720*L0*(eulerOp L0) - 24480*L0 + 77760*(XL 2)*P1 - 233280*(XL 2)*(ex3 P1) + 58320*(XL 2) + 34560*P1 + 2880*P3 - 103680*(ex3 P1) - 233280*(ex3 P3) - 69120*(eulerOp L0) - 3840) * ho1 + (-233280*L0*(XL 2) + 311040*L0*(eulerOp L0) + 25920*L0 - 38880*(XL 2) - 4320*P3 + 349920*(ex3 P3) + 51840*(eulerOp L0) + 5760) * ho2 + (-25920*L0*P1 + 77760*L0*(ex3 P1) - 2160*L0 - 38880*P1 + 116640*(ex3 P1) - 3240) * ho3 + (12960*P1 - 38880*(ex3 P1) + 1080) * ho4 + (34560*P1 - 103680*(ex3 P1) + 2880) * hto1 + (-25920*P1 + 77760*(ex3 P1) - 2160) * hto2 + (-77760*L0*(XL 2) + 103680*L0*(eulerOp L0) + 8640*L0 - 12960*(XL 2) + 51840*P1^2 - 311040*P1*(ex3 P1) + 8640*P1 - 1440*P3 + 466560*(ex3 P1)^2 - 25920*(ex3 P1) + 116640*(ex3 P3) + 17280*(eulerOp L0) + 2280) * hR1 + (2099520*L0*(XL 2) - 2799360*L0*(eulerOp L0) - 233280*L0 + 349920*(XL 2) - 466560*P1^2 + 2799360*P1*(ex3 P1) - 77760*P1 + 38880*P3 - 4199040*(ex3 P1)^2 + 233280*(ex3 P1) - 3149280*(ex3 P3) - 466560*(eulerOp L0) - 55080) * hR1q + (12*P1 - 36*(ex3 P1) + 1) * hR3 + (-12636*P1 + 37908*(ex3 P1) - 1053) * hR3q + (-8640*P1 + 25920*(ex3 P1) - 720) * htR1 + (699840*P1 - 2099520*(ex3 P1) + 58320) * htR1q
    exact (mul_eq_zero.mp key).resolve_left (ps_natCast_ne_zero (by norm_num))
  have e23 : E2q3 = 1 - 24 * ex3 P1 := by
    rw [E2q3, E2q_eq_P1, map_sub, map_one, map_mul, map_ofNat]
  have e43 : E4q3 = 1 + 240 * ex3 P3 := by
    rw [E4q3, E4q_eq_P3, map_add, map_one, map_mul, map_ofNat]
  have e63 : E6q3 = 1 - 504 * ex3 P5 := by
    rw [E6q3, E6q_eq_P5, map_sub, map_one, map_mul, map_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> rw [lambertA2_eq]
  · rw [e23, E2q_eq_P1]
    have key : ((1 : ℕ) : PowerSeries ℚ) * (72*L0^2 + 24*L0 - 24*P1 + 72*(ex3 P1)) = 0 := by
      linear_combination (24) * hr0
    have h0 := (mul_eq_zero.mp key).resolve_left (ps_natCast_ne_zero (by norm_num))
    linear_combination h0
  · rw [e43, E4q_eq_P3]
    have key : ((1 : ℕ) : PowerSeries ℚ) * (12960*L0^4 + 8640*L0^3 + 2160*L0^2 + 240*L0 - 240*P3 - 2160*(ex3 P3)) = 0 := by
      linear_combination (-240) * hα + (4320*L0^2 + 1440*L0 + 1440*P1 - 4320*(ex3 P1) + 240) * hr0
    have h0 := (mul_eq_zero.mp key).resolve_left (ps_natCast_ne_zero (by norm_num))
    linear_combination h0
  · rw [e43, E4q_eq_P3, e63, E6q_eq_P5]
    have key : ((1 : ℕ) : PowerSeries ℚ) * (591224832*L0^8 + 788299776*L0^7 + 459841536*L0^6 + 153280512*L0^5 + 31933440*L0^4 + 4257792*L0^3 - 290304*L0^2*P5 + 7838208*L0^2*(ex3 P5) + 339840*L0^2 - 96768*L0*P5 + 2612736*L0*(ex3 P5) + 11904*L0 + 57600*P3^2 - 1036800*P3*(ex3 P3) - 3840*P3 - 8064*P5 + 4665600*(ex3 P3)^2 + 34560*(ex3 P3) + 217728*(ex3 P5)) = 0 := by
      linear_combination (-290304*L0^2 - 96768*L0 - 8064) * hβ + (345600*P1^2 - 2073600*P1*(ex3 P1) + 57600*P1 + 57600*P3 + 3110400*(ex3 P1)^2 - 172800*(ex3 P1) - 1555200*(ex3 P3) - 3840) * hα + (197074944*L0^6 + 197074944*L0^5 + 65691648*L0^4*P1 - 197074944*L0^4*(ex3 P1) + 87588864*L0^4 + 43794432*L0^3*P1 - 131383296*L0^3*(ex3 P1) + 21897216*L0^3 + 21897216*L0^2*P1^2 - 131383296*L0^2*P1*(ex3 P1) + 14598144*L0^2*P1 + 197074944*L0^2*(ex3 P1)^2 - 43794432*L0^2*(ex3 P1) + 3345408*L0^2 + 7299072*L0*P1^2 - 43794432*L0*P1*(ex3 P1) + 2433024*L0*P1 + 65691648*L0*(ex3 P1)^2 - 7299072*L0*(ex3 P1) + 304128*L0 - 4313088*P1^3 + 38817792*P1^2*(ex3 P1) - 470016*P1^2 - 116453376*P1*(ex3 P1)^2 + 2820096*P1*(ex3 P1) + 34836480*P1*(ex3 P3) + 207360*P1 + 116453376*(ex3 P1)^3 - 4230144*(ex3 P1)^2 - 104509440*(ex3 P1)*(ex3 P3) - 622080*(ex3 P1) + 2903040*(ex3 P3) + 5225472*(ex3 P5) + 11904) * hr0 + (-62208) * hδ
    have h0 := (mul_eq_zero.mp key).resolve_left (ps_natCast_ne_zero (by norm_num))
    linear_combination h0

end

end VOA.DeligneAudit.G2Star

section AxiomAudit
#print axioms VOA.DeligneAudit.G2Star.g2Level3EisLambert
end AxiomAudit
