/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneMLDECubic

/-!
# Higher orders of the heat identity at `u = ω eˣ`

Orders `x¹`, `x²` of (*) at `u = ω eˣ`, rational parts (`level3_order1`, `level3_order2`), in terms of the
twisted Lambert series `XL j = ∑χ₋₃(k)kʲ q^{dk}`, `XM j = ∑(ω^k+ω^{-k})kʲ q^{dk}`,
`XN j = ∑ d(ω^k+ω^{-k})kʲ q^{dk}`, `XD j = ∑ dχ₋₃(k)kʲ q^{dk}`.
The coefficient-level `linear_combination` certificates (multiples of `ω² + ω + 1`) were computed with
sympy outside Lean.
-/

namespace VOA.DeligneAudit.DeligneMLDE.Heat

open PowerSeries

noncomputable section

def XL (j : ℕ) : PowerSeries ℚ := lamQ fun _ k => chi3 k * (k : ℚ) ^ j
def XM (j : ℕ) : PowerSeries ℚ := lamQ fun _ k => cc3 k * (k : ℚ) ^ j
def XN (j : ℕ) : PowerSeries ℚ := lamQ fun d k => (d : ℚ) * cc3 k * (k : ℚ) ^ j
def XD (j : ℕ) : PowerSeries ℚ := lamQ fun d k => (d : ℚ) * chi3 k * (k : ℚ) ^ j

theorem XL_zero : XL 0 = L0 := by
  rw [XL, L0]; exact lamQ_congr fun d k _ => by simp

theorem XM_one : XM 1 = M1 := by
  rw [XM, M1]; exact lamQ_congr fun d k _ => by simp

end

end VOA.DeligneAudit.DeligneMLDE.Heat

namespace VOA.DeligneAudit.DeligneMLDE.HeatK

open PowerSeries VOA.QSeries VOA.QSeries.JTP VOA.DeligneAudit.DeligneMLDE.Heat

open scoped BigOperators

noncomputable section

theorem split_ω3 (A B : ℚ) (h : (A : ℂ) + (B : ℂ) * ω3 = 0) : A = 0 ∧ B = 0 := by
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ratCast_re,
    Complex.ratCast_im, ω3, Complex.zero_re, Complex.zero_im, zero_mul, mul_zero, sub_zero,
    add_zero, zero_add] at hre him
  have h3 : Real.sqrt 3 / 2 ≠ 0 := by positivity
  have hB : (B : ℝ) = 0 := (mul_eq_zero.mp him).resolve_right h3
  have hB' : B = 0 := by exact_mod_cast hB
  refine ⟨?_, hB'⟩
  rw [hB] at hre
  have : (A : ℝ) = 0 := by linarith
  exact_mod_cast this

theorem pjR0' : pjK 0 (Rser (uW ω3 ω3_ne_zero)) = PowerSeries.C (-(ω3 - ω3⁻¹)) * toC (XL 0) := by
  rw [XL_zero]; exact pj0R

theorem pjR1' : pjK 1 (Rser (uW ω3 ω3_ne_zero)) = PowerSeries.C (-1) * toC (XM 1) := by
  rw [XM_one]; exact pj1R

theorem pjR2 : pjK 2 (Rser (uW ω3 ω3_ne_zero)) = PowerSeries.C (-(ω3 - ω3⁻¹) / 2) * toC (XL 2) := by
  rw [pjK_R, XL, ← lamK_map, ← lamK_smul]
  refine lamK_congr fun d k _ => ?_
  have h := ω3_sub_inv k
  simp only [Nat.factorial, Nat.cast_ofNat]
  push_cast
  linear_combination ((k : ℂ) ^ 2 / 2) * h

theorem pjR3 : pjK 3 (Rser (uW ω3 ω3_ne_zero)) = PowerSeries.C (-1 / 6) * toC (XM 3) := by
  rw [pjK_R, XM, ← lamK_map, ← lamK_smul]
  refine lamK_congr fun d k _ => ?_
  have h := ω3_add_inv k
  simp only [Nat.factorial, Nat.cast_ofNat]
  push_cast
  linear_combination (-(k : ℂ) ^ 3 / 6) * h

theorem pjR4 : pjK 4 (Rser (uW ω3 ω3_ne_zero)) = PowerSeries.C (-(ω3 - ω3⁻¹) / 24) * toC (XL 4) := by
  rw [pjK_R, XL, ← lamK_map, ← lamK_smul]
  refine lamK_congr fun d k _ => ?_
  have h := ω3_sub_inv k
  simp only [Nat.factorial]
  push_cast
  linear_combination ((k : ℂ) ^ 4 / 24) * h

theorem pjR5 : pjK 5 (Rser (uW ω3 ω3_ne_zero)) = PowerSeries.C (-1 / 120) * toC (XM 5) := by
  rw [pjK_R, XM, ← lamK_map, ← lamK_smul]
  refine lamK_congr fun d k _ => ?_
  have h := ω3_add_inv k
  simp only [Nat.factorial]
  push_cast
  linear_combination (-(k : ℂ) ^ 5 / 120) * h

theorem pjT3 : pjK 3 (Tser (uW ω3 ω3_ne_zero)) = PowerSeries.C (-(ω3 - ω3⁻¹) / 6) * toC (XD 3) := by
  rw [pjK_T, XD, ← lamK_map, ← lamK_smul]
  refine lamK_congr fun d k _ => ?_
  have h := ω3_sub_inv k
  simp only [Nat.factorial, OfNat.ofNat_ne_zero, if_false, add_zero]
  push_cast
  linear_combination ((d : ℂ) * k ^ 3 / 6) * h

theorem pjT4 : pjK 4 (Tser (uW ω3 ω3_ne_zero)) = PowerSeries.C (-1 / 24) * toC (XN 4) := by
  rw [pjK_T, XN, ← lamK_map, ← lamK_smul]
  refine lamK_congr fun d k _ => ?_
  have h := ω3_add_inv k
  simp only [Nat.factorial, OfNat.ofNat_ne_zero, if_false, add_zero]
  push_cast
  linear_combination (-(d : ℂ) * k ^ 4 / 24) * h

theorem pjT1 : pjK 1 (Tser (uW ω3 ω3_ne_zero)) = PowerSeries.C (-(ω3 - ω3⁻¹)) * toC (XD 1) := by
  rw [pjK_T, XD, ← lamK_map, ← lamK_smul]
  refine lamK_congr fun d k _ => ?_
  have h := ω3_sub_inv k
  simp only [Nat.factorial, Nat.cast_one, one_ne_zero, if_false, add_zero]
  push_cast
  linear_combination ((d : ℂ) * k) * h

theorem pjT2 : pjK 2 (Tser (uW ω3 ω3_ne_zero)) = PowerSeries.C (-1 / 2) * toC (XN 2) := by
  rw [pjK_T, XN, ← lamK_map, ← lamK_smul]
  refine lamK_congr fun d k _ => ?_
  have h := ω3_add_inv k
  simp only [Nat.factorial, Nat.cast_ofNat, OfNat.ofNat_ne_zero, if_false, add_zero]
  push_cast
  linear_combination (-(d : ℂ) * k ^ 2 / 2) * h

/-- Order `x^1` of (*) at `u = ω eˣ`, rational part. -/
theorem level3_order1 : PowerSeries.C (-3) * (XL 2) + PowerSeries.C (3) * (XL 0 * XM 1) + PowerSeries.C (3) * (XM 1 * XL 0) + PowerSeries.C (6) * (XD 1) + PowerSeries.C (1) * (XM 1) + PowerSeries.C (-2) * (XL 0) = 0 := by
  have h := star_pjK (uW ω3 ω3_ne_zero) (dx_uW ω3 ω3_ne_zero) 1
  simp only [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ,
    Finset.sum_range_zero, zero_add, pjK_one, pjK_C, coeff_uW, Nat.sub_zero, Nat.sub_self,
    Nat.reduceAdd, Nat.reduceSub, if_true, one_ne_zero, if_false, Nat.factorial, Nat.cast_one,
    Nat.cast_zero, Nat.cast_ofNat, OfNat.ofNat_ne_zero, Nat.succ_ne_zero] at h
  simp only [pjR0', pjR1', pjR2, pjR3, pjR4, pjR5, pjT1, pjT2, pjT3, pjT4, pj0T, C_mul_C_mulC] at h
  simp only [← map_mul] at h
  refine PowerSeries.ext fun n => ?_
  have hn := congrArg (coeff n) h
  simp only [sub_mul, add_mul, mul_sub, mul_add, neg_mul, mul_neg, neg_neg, map_add, map_sub,
    map_neg, mul_assoc, coeff_C_mul, coeff_map] at hn
  rw [ω3_inv] at hn
  have hω := ω3_sq_add
  set y0 := coeff n (XL 2)
  set y1 := coeff n (XL 0 * XM 1)
  set y2 := coeff n (XM 1 * XL 0)
  set y3 := coeff n (XD 1)
  set y4 := coeff n (XM 1)
  set y5 := coeff n (XL 0 * XL 0)
  set y6 := coeff n (N3)
  set y7 := coeff n (XL 0)
  have key : (((-3) * y0 + (3) * y1 + (3) * y2 + (6) * y3 + (1) * y4 + (-2) * y7 : ℚ) : ℂ) + (((-3) * y0 + (3) * y1 + (3) * y2 + (6) * y3 + (2) * y4 + (3) * y5 + (-2) * y6 + (-1) * y7 : ℚ) : ℂ) * ω3 = 0 := by
    simp only [eq_ratCast] at hn
    push_cast
    linear_combination hn - ((3 - ω3) * (y0 : ℂ) + (ω3 - 3) * (y1 : ℂ) + (ω3 - 3) * (y2 : ℂ) + (2*ω3 - 6) * (y3 : ℂ) + (-ω3^3 + 3*ω3^2 - 3*ω3) * (y5 : ℂ) + (2 - ω3) * (y7 : ℂ)) * hω
  have hA := (split_ω3 _ _ key).1
  simp only [map_add, coeff_C_mul, map_zero]
  linarith

/-- Order `x^2` of (*) at `u = ω eˣ`, rational part. -/
theorem level3_order2 : PowerSeries.C (-1) * (XM 3) + PowerSeries.C (-3) * (XL 0 * XL 2) + PowerSeries.C (2) * (XM 1 * XM 1) + PowerSeries.C (-3) * (XL 2 * XL 0) + PowerSeries.C (2) * (XN 2) + PowerSeries.C (-5) * (XL 2) + PowerSeries.C (4) * (XL 0 * XM 1) + PowerSeries.C (4) * (XM 1 * XL 0) + PowerSeries.C (8) * (XD 1) + PowerSeries.C (-2) * (XL 0) = 0 := by
  have h := star_pjK (uW ω3 ω3_ne_zero) (dx_uW ω3 ω3_ne_zero) 2
  simp only [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ,
    Finset.sum_range_zero, zero_add, pjK_one, pjK_C, coeff_uW, Nat.sub_zero, Nat.sub_self,
    Nat.reduceAdd, Nat.reduceSub, if_true, one_ne_zero, if_false, Nat.factorial, Nat.cast_one,
    Nat.cast_zero, Nat.cast_ofNat, OfNat.ofNat_ne_zero, Nat.succ_ne_zero] at h
  simp only [pjR0', pjR1', pjR2, pjR3, pjR4, pjR5, pjT1, pjT2, pjT3, pjT4, pj0T, C_mul_C_mulC] at h
  simp only [← map_mul] at h
  refine PowerSeries.ext fun n => ?_
  have hn := congrArg (coeff n) h
  simp only [sub_mul, add_mul, mul_sub, mul_add, neg_mul, mul_neg, neg_neg, map_add, map_sub,
    map_neg, mul_assoc, coeff_C_mul, coeff_map] at hn
  rw [ω3_inv] at hn
  have hω := ω3_sq_add
  set y0 := coeff n (XM 3)
  set y1 := coeff n (XL 0 * XL 2)
  set y2 := coeff n (XM 1 * XM 1)
  set y3 := coeff n (XL 2 * XL 0)
  set y4 := coeff n (XN 2)
  set y5 := coeff n (XL 2)
  set y6 := coeff n (XL 0 * XM 1)
  set y7 := coeff n (XM 1 * XL 0)
  set y8 := coeff n (XD 1)
  set y9 := coeff n (XM 1)
  set y10 := coeff n (XL 0 * XL 0)
  set y11 := coeff n (N3)
  set y12 := coeff n (XL 0)
  have key : (((-1/2) * y0 + (-3/2) * y1 + (1) * y2 + (-3/2) * y3 + (1) * y4 + (-5/2) * y5 + (2) * y6 + (2) * y7 + (4) * y8 + (-1) * y12 : ℚ) : ℂ) + (((1/2) * y0 + (3/2) * y1 + (-1) * y2 + (3/2) * y3 + (-1) * y4 + (-1/2) * y5 + (1) * y6 + (1) * y7 + (2) * y8 + (3/2) * y9 + (3/2) * y10 + (-1) * y11 + (-1/2) * y12 : ℚ) : ℂ) * ω3 = 0 := by
    simp only [eq_ratCast] at hn
    push_cast
    linear_combination hn - ((-ω3^3/2 + 2*ω3^2 - 3*ω3 + 3/2) * (y1 : ℂ) + (-ω3^3/2 + 2*ω3^2 - 3*ω3 + 3/2) * (y3 : ℂ) + (5/2 - 3*ω3/2) * (y5 : ℂ) + (ω3 - 2) * (y6 : ℂ) + (ω3 - 2) * (y7 : ℂ) + (2*ω3 - 4) * (y8 : ℂ) + (-ω3^3/2 + 3*ω3^2/2 - 3*ω3/2) * (y10 : ℂ) + (1 - ω3/2) * (y12 : ℂ)) * hω
  have hA := (split_ω3 _ _ key).1
  simp only [map_add, coeff_C_mul, map_zero]
  linarith

/-- Order `x^3` of (*) at `u = ω eˣ`, rational part. -/
theorem level3_order3 : PowerSeries.C (-3) * (XL 4) + PowerSeries.C (3) * (XL 0 * XM 3) + PowerSeries.C (9) * (XM 1 * XL 2) + PowerSeries.C (9) * (XL 2 * XM 1) + PowerSeries.C (3) * (XM 3 * XL 0) + PowerSeries.C (6) * (XD 3) + PowerSeries.C (1) * (XM 3) + PowerSeries.C (-12) * (XL 2) + PowerSeries.C (6) * (XL 0 * XM 1) + PowerSeries.C (6) * (XM 1 * XL 0) + PowerSeries.C (12) * (XD 1) + PowerSeries.C (-2) * (XL 0) = 0 := by
  have h := star_pjK (uW ω3 ω3_ne_zero) (dx_uW ω3 ω3_ne_zero) 3
  simp only [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ,
    Finset.sum_range_zero, zero_add, pjK_one, pjK_C, coeff_uW, Nat.sub_zero, Nat.sub_self,
    Nat.reduceAdd, Nat.reduceSub, if_true, one_ne_zero, if_false, Nat.factorial, Nat.cast_one,
    Nat.cast_zero, Nat.cast_ofNat, OfNat.ofNat_ne_zero, Nat.succ_ne_zero] at h
  simp only [pjR0', pjR1', pjR2, pjR3, pjR4, pjR5, pjT1, pjT2, pjT3, pjT4, pj0T, C_mul_C_mulC] at h
  simp only [← map_mul] at h
  refine PowerSeries.ext fun n => ?_
  have hn := congrArg (coeff n) h
  simp only [sub_mul, add_mul, mul_sub, mul_add, neg_mul, mul_neg, neg_neg, map_add, map_sub,
    map_neg, mul_assoc, coeff_C_mul, coeff_map] at hn
  rw [ω3_inv] at hn
  have hω := ω3_sq_add
  set y0 := coeff n (XL 4)
  set y1 := coeff n (XL 0 * XM 3)
  set y2 := coeff n (XM 1 * XL 2)
  set y3 := coeff n (XL 2 * XM 1)
  set y4 := coeff n (XM 3 * XL 0)
  set y5 := coeff n (XD 3)
  set y6 := coeff n (XM 3)
  set y7 := coeff n (XL 0 * XL 2)
  set y8 := coeff n (XM 1 * XM 1)
  set y9 := coeff n (XL 2 * XL 0)
  set y10 := coeff n (XN 2)
  set y11 := coeff n (XL 2)
  set y12 := coeff n (XL 0 * XM 1)
  set y13 := coeff n (XM 1 * XL 0)
  set y14 := coeff n (XD 1)
  set y15 := coeff n (XM 1)
  set y16 := coeff n (XL 0 * XL 0)
  set y17 := coeff n (N3)
  set y18 := coeff n (XL 0)
  have key : (((-1/2) * y0 + (1/2) * y1 + (3/2) * y2 + (3/2) * y3 + (1/2) * y4 + (1) * y5 + (1/6) * y6 + (-2) * y11 + (1) * y12 + (1) * y13 + (2) * y14 + (-1/3) * y18 : ℚ) : ℂ) + (((-1/2) * y0 + (1/2) * y1 + (3/2) * y2 + (3/2) * y3 + (1/2) * y4 + (1) * y5 + (2/3) * y6 + (3/2) * y7 + (-1) * y8 + (3/2) * y9 + (-1) * y10 + (-1) * y11 + (1/2) * y12 + (1/2) * y13 + (1) * y14 + (2/3) * y15 + (1/2) * y16 + (-1/3) * y17 + (-1/6) * y18 : ℚ) : ℂ) * ω3 = 0 := by
    simp only [eq_ratCast] at hn
    push_cast
    linear_combination hn - ((1/2 - ω3/6) * (y0 : ℂ) + (ω3/6 - 1/2) * (y1 : ℂ) + (ω3/2 - 3/2) * (y2 : ℂ) + (ω3/2 - 3/2) * (y3 : ℂ) + (ω3/6 - 1/2) * (y4 : ℂ) + (ω3/3 - 1) * (y5 : ℂ) + (-ω3^3/2 + 3*ω3^2/2 - 3*ω3/2) * (y7 : ℂ) + (-ω3^3/2 + 3*ω3^2/2 - 3*ω3/2) * (y9 : ℂ) + (2 - ω3) * (y11 : ℂ) + (ω3/2 - 1) * (y12 : ℂ) + (ω3/2 - 1) * (y13 : ℂ) + (ω3 - 2) * (y14 : ℂ) + (-ω3^3/6 + ω3^2/2 - ω3/2) * (y16 : ℂ) + (1/3 - ω3/6) * (y18 : ℂ)) * hω
  have hA := (split_ω3 _ _ key).1
  simp only [map_add, coeff_C_mul, map_zero]
  linarith

/-- Order `x^4` of (*) at `u = ω eˣ`, rational part. -/
theorem level3_order4 : PowerSeries.C (-1) * (XM 5) + PowerSeries.C (-3) * (XL 0 * XL 4) + PowerSeries.C (4) * (XM 1 * XM 3) + PowerSeries.C (-18) * (XL 2 * XL 2) + PowerSeries.C (4) * (XM 3 * XM 1) + PowerSeries.C (-3) * (XL 4 * XL 0) + PowerSeries.C (2) * (XN 4) + PowerSeries.C (-9) * (XL 4) + PowerSeries.C (8) * (XL 0 * XM 3) + PowerSeries.C (24) * (XM 1 * XL 2) + PowerSeries.C (24) * (XL 2 * XM 1) + PowerSeries.C (8) * (XM 3 * XL 0) + PowerSeries.C (16) * (XD 3) + PowerSeries.C (-20) * (XL 2) + PowerSeries.C (8) * (XL 0 * XM 1) + PowerSeries.C (8) * (XM 1 * XL 0) + PowerSeries.C (16) * (XD 1) + PowerSeries.C (-2) * (XL 0) = 0 := by
  have h := star_pjK (uW ω3 ω3_ne_zero) (dx_uW ω3 ω3_ne_zero) 4
  simp only [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ,
    Finset.sum_range_zero, zero_add, pjK_one, pjK_C, coeff_uW, Nat.sub_zero, Nat.sub_self,
    Nat.reduceAdd, Nat.reduceSub, if_true, one_ne_zero, if_false, Nat.factorial, Nat.cast_one,
    Nat.cast_zero, Nat.cast_ofNat, OfNat.ofNat_ne_zero, Nat.succ_ne_zero] at h
  simp only [pjR0', pjR1', pjR2, pjR3, pjR4, pjR5, pjT1, pjT2, pjT3, pjT4, pj0T, C_mul_C_mulC] at h
  simp only [← map_mul] at h
  refine PowerSeries.ext fun n => ?_
  have hn := congrArg (coeff n) h
  simp only [sub_mul, add_mul, mul_sub, mul_add, neg_mul, mul_neg, neg_neg, map_add, map_sub,
    map_neg, mul_assoc, coeff_C_mul, coeff_map] at hn
  rw [ω3_inv] at hn
  have hω := ω3_sq_add
  set y0 := coeff n (XM 5)
  set y1 := coeff n (XL 0 * XL 4)
  set y2 := coeff n (XM 1 * XM 3)
  set y3 := coeff n (XL 2 * XL 2)
  set y4 := coeff n (XM 3 * XM 1)
  set y5 := coeff n (XL 4 * XL 0)
  set y6 := coeff n (XN 4)
  set y7 := coeff n (XL 4)
  set y8 := coeff n (XL 0 * XM 3)
  set y9 := coeff n (XM 1 * XL 2)
  set y10 := coeff n (XL 2 * XM 1)
  set y11 := coeff n (XM 3 * XL 0)
  set y12 := coeff n (XD 3)
  set y13 := coeff n (XM 3)
  set y14 := coeff n (XL 0 * XL 2)
  set y15 := coeff n (XM 1 * XM 1)
  set y16 := coeff n (XL 2 * XL 0)
  set y17 := coeff n (XN 2)
  set y18 := coeff n (XL 2)
  set y19 := coeff n (XL 0 * XM 1)
  set y20 := coeff n (XM 1 * XL 0)
  set y21 := coeff n (XD 1)
  set y22 := coeff n (XM 1)
  set y23 := coeff n (XL 0 * XL 0)
  set y24 := coeff n (N3)
  set y25 := coeff n (XL 0)
  have key : (((-1/24) * y0 + (-1/8) * y1 + (1/6) * y2 + (-3/4) * y3 + (1/6) * y4 + (-1/8) * y5 + (1/12) * y6 + (-3/8) * y7 + (1/3) * y8 + (1) * y9 + (1) * y10 + (1/3) * y11 + (2/3) * y12 + (-5/6) * y18 + (1/3) * y19 + (1/3) * y20 + (2/3) * y21 + (-1/12) * y25 : ℚ) : ℂ) + (((1/24) * y0 + (1/8) * y1 + (-1/6) * y2 + (3/4) * y3 + (-1/6) * y4 + (1/8) * y5 + (-1/12) * y6 + (-1/8) * y7 + (1/6) * y8 + (1/2) * y9 + (1/2) * y10 + (1/6) * y11 + (1/3) * y12 + (5/12) * y13 + (3/4) * y14 + (-1/2) * y15 + (3/4) * y16 + (-1/2) * y17 + (-5/12) * y18 + (1/6) * y19 + (1/6) * y20 + (1/3) * y21 + (5/24) * y22 + (1/8) * y23 + (-1/12) * y24 + (-1/24) * y25 : ℚ) : ℂ) * ω3 = 0 := by
    simp only [eq_ratCast] at hn
    push_cast
    linear_combination hn - ((-ω3^3/24 + ω3^2/6 - ω3/4 + 1/8) * (y1 : ℂ) + (-ω3^3/4 + ω3^2 - 3*ω3/2 + 3/4) * (y3 : ℂ) + (-ω3^3/24 + ω3^2/6 - ω3/4 + 1/8) * (y5 : ℂ) + (3/8 - 5*ω3/24) * (y7 : ℂ) + (ω3/6 - 1/3) * (y8 : ℂ) + (ω3/2 - 1) * (y9 : ℂ) + (ω3/2 - 1) * (y10 : ℂ) + (ω3/6 - 1/3) * (y11 : ℂ) + (ω3/3 - 2/3) * (y12 : ℂ) + (-ω3^3/4 + 3*ω3^2/4 - 3*ω3/4) * (y14 : ℂ) + (-ω3^3/4 + 3*ω3^2/4 - 3*ω3/4) * (y16 : ℂ) + (5/6 - 5*ω3/12) * (y18 : ℂ) + (ω3/6 - 1/3) * (y19 : ℂ) + (ω3/6 - 1/3) * (y20 : ℂ) + (ω3/3 - 2/3) * (y21 : ℂ) + (-ω3^3/24 + ω3^2/8 - ω3/8) * (y23 : ℂ) + (1/12 - ω3/24) * (y25 : ℂ)) * hω
  have hA := (split_ω3 _ _ key).1
  simp only [map_add, coeff_C_mul, map_zero]
  linarith

end

end VOA.DeligneAudit.DeligneMLDE.HeatK

section AxiomAudit
#print axioms VOA.DeligneAudit.DeligneMLDE.HeatK.level3_order1
#print axioms VOA.DeligneAudit.DeligneMLDE.HeatK.level3_order2
#print axioms VOA.DeligneAudit.DeligneMLDE.HeatK.level3_order3
#print axioms VOA.DeligneAudit.DeligneMLDE.HeatK.level3_order4
end AxiomAudit
