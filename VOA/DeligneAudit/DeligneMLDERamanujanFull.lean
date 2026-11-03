/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneMLDERamanujan

/-!
# Ramanujan's identities for `θE₄` and `θE₆` from the heat equation

Orders `x⁵` and `x⁷` of the identity (*) at `u = eˣ` (`DeligneMLDEHeat`), together with orders
`x¹`, `x³` (`DeligneMLDERamanujan`), give

* `ramanujan4`: `720 θP₃ = 240P₃ - 24P₁ - 5760P₁P₃ + 504P₅`   (`3θE₄ = E₂E₄ - E₆`);
* `order_seven`: the weight-8 relation; with `E₄² = E₈` it gives `2θE₆ = E₂E₆ - E₄²`.

`E₈ = E₄²` (needed to reach Ramanujan's form of the third identity) is `DeligneMLDEEightSq`.
-/

namespace VOA.DeligneAudit.DeligneMLDE.Heat

open PowerSeries VOA.QSeries VOA.QSeries.JTP

open scoped BigOperators

noncomputable section

/-- `P₅ = ∑ σ₅(n) qⁿ`. -/
def P5 : PowerSeries ℚ := lamQ fun _ k => (k : ℚ) ^ 5
/-- `P₇ = ∑ σ₇(n) qⁿ`. -/
def P7 : PowerSeries ℚ := lamQ fun _ k => (k : ℚ) ^ 7

theorem eulerOp_P3 : eulerOp P3 = lamQ fun d k => (d : ℚ) * k ^ 4 := by
  rw [P3, eulerOp_lamQ]; exact lamQ_congr fun d k _ => by ring

theorem eulerOp_P5 : eulerOp P5 = lamQ fun d k => (d : ℚ) * k ^ 6 := by
  rw [P5, eulerOp_lamQ]; exact lamQ_congr fun d k _ => by ring

theorem r1_5 : pj 5 (Rser (uU 1 hε1)) = C (-1 / 60) * P5 := by
  rw [pj_R, P5, ← lamQ_smul]; exact lamQ_congr fun d k _ => by simp [Nat.factorial]; ring

theorem r1_6 : pj 6 (Rser (uU 1 hε1)) = 0 := by
  rw [pj_R, ← lamQ_zero]; exact lamQ_congr fun d k _ => by norm_num [Nat.factorial]

theorem r1_7 : pj 7 (Rser (uU 1 hε1)) = C (-1 / 2520) * P7 := by
  rw [pj_R, P7, ← lamQ_smul]; exact lamQ_congr fun d k _ => by simp [Nat.factorial]; ring

theorem r1_8 : pj 8 (Rser (uU 1 hε1)) = 0 := by
  rw [pj_R, ← lamQ_zero]; exact lamQ_congr fun d k _ => by norm_num [Nat.factorial]

theorem t1_4 : pj 4 (Tser (uU 1 hε1)) = C (-1 / 12) * eulerOp P3 := by
  rw [pj_T, eulerOp_P3, ← lamQ_smul]; exact lamQ_congr fun d k _ => by simp [Nat.factorial]; ring

theorem t1_5 : pj 5 (Tser (uU 1 hε1)) = 0 := by
  rw [pj_T, ← lamQ_zero]
  exact lamQ_congr fun d k _ => by rw [show ((-(k : ℚ)) ^ 5) = -(k : ℚ) ^ 5 by ring]; simp

theorem t1_6 : pj 6 (Tser (uU 1 hε1)) = C (-1 / 360) * eulerOp P5 := by
  rw [pj_T, eulerOp_P5, ← lamQ_smul]; exact lamQ_congr fun d k _ => by simp [Nat.factorial]; ring

theorem t1_7 : pj 7 (Tser (uU 1 hε1)) = 0 := by
  rw [pj_T, ← lamQ_zero]
  exact lamQ_congr fun d k _ => by rw [show ((-(k : ℚ)) ^ 7) = -(k : ℚ) ^ 7 by ring]; simp

/-- **`3θE₄ = E₂E₄ - E₆`**, in `P`-form. -/
theorem ramanujan4 :
    C 720 * eulerOp P3 = C 240 * P3 - C 24 * P1 - C 5760 * (P1 * P3) + C 504 * P5 := by
  have h := star_pj (uU 1 hε1) (dx_uU 1 hε1) 5
  simp only [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ,
    Finset.sum_range_zero, zero_add, pj_one, pjC1, Nat.sub_zero, Nat.sub_self, Nat.reduceAdd,
    Nat.reduceSub, if_true, one_ne_zero, if_false, Nat.factorial, Nat.cast_one, Nat.cast_zero,
    Nat.cast_ofNat, OfNat.ofNat_ne_zero] at h
  simp only [r1_0, r1_1, r1_2, r1_3, r1_4, r1_5, r1_6, t1_0, t1_1, t1_2, t1_3, t1_4, t1_5,
    order_one, zero_mul, mul_zero, add_zero, zero_add, C_mul_C_mul] at h
  refine PowerSeries.ext fun n => ?_
  have hn := congrArg (coeff n) h
  simp only [sub_mul, add_mul, mul_sub, mul_add, map_add, map_sub, coeff_C_mul, map_zero] at hn
  have h3 := congrArg (coeff n) ramanujan
  simp only [map_add, map_sub, coeff_C_mul, coeff_eulerOp] at h3
  simp only [map_add, map_sub, coeff_C_mul, coeff_eulerOp]
  have c13 : coeff n (P3 * P1) = coeff n (P1 * P3) := by rw [mul_comm]
  have c15 : coeff n (P5 * P1) = coeff n (P1 * P5) := by rw [mul_comm]
  norm_num at hn
  linarith

/-- **Order `x⁷`** of (*) at `u = eˣ` (times 2520). With `E₄² = E₈` and the lower identities it
is `2θE₆ = E₂E₆ - E₄²`. -/
theorem order_seven :
    C 9 * P7 - C 168 * (P1 * P5) - C 280 * (P3 * P3) - C 14 * eulerOp P5 + C 56 * P5
      - C 560 * (P1 * P3) - C 70 * eulerOp P3 + C 56 * P3 - C 84 * (P1 * P1) - C 42 * eulerOp P1
      + C 5 * P1 = 0 := by
  have h := star_pj (uU 1 hε1) (dx_uU 1 hε1) 7
  simp only [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ,
    Finset.sum_range_zero, zero_add, pj_one, pjC1, Nat.sub_zero, Nat.sub_self, Nat.reduceAdd,
    Nat.reduceSub, if_true, one_ne_zero, if_false, Nat.factorial, Nat.cast_one, Nat.cast_zero,
    Nat.cast_ofNat, OfNat.ofNat_ne_zero] at h
  simp only [r1_0, r1_1, r1_2, r1_3, r1_4, r1_5, r1_6, r1_7, r1_8, t1_0, t1_1, t1_2, t1_3, t1_4,
    t1_5, t1_6, t1_7, order_one, zero_mul, mul_zero, add_zero, zero_add, C_mul_C_mul] at h
  refine PowerSeries.ext fun n => ?_
  have hn := congrArg (coeff n) h
  simp only [sub_mul, add_mul, mul_sub, mul_add, map_add, map_sub, coeff_C_mul, map_zero] at hn
  have h3 := congrArg (coeff n) ramanujan
  simp only [map_add, map_sub, coeff_C_mul, coeff_eulerOp] at h3
  simp only [map_add, map_sub, coeff_C_mul, coeff_eulerOp, map_zero]
  have c13 : coeff n (P3 * P1) = coeff n (P1 * P3) := by rw [mul_comm]
  have c15 : coeff n (P5 * P1) = coeff n (P1 * P5) := by rw [mul_comm]
  norm_num at hn
  linarith

end

end VOA.DeligneAudit.DeligneMLDE.Heat

section AxiomAudit
#print axioms VOA.DeligneAudit.DeligneMLDE.Heat.ramanujan4
#print axioms VOA.DeligneAudit.DeligneMLDE.Heat.order_seven
end AxiomAudit
