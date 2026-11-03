/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneMLDEHeat

/-!
# Ramanujan's identity and its level-two companion, from the heat equation

Taking `x`-coefficients of the identity (*) of `DeligneMLDEHeat`,

  `(1 - u)(DR + R² - 2T) = (1 + u) R`,     `u = ε eˣ`,

gives identities between Lambert series in `ℚ⟦q⟧`.  Write
`lamQ F = ∑_n q^n ∑_{d k = n} F d k` (`d` the base of `q^{dk}`, `k` the geometric index).

* `ε = 1`, order `x¹`: `∑ d = ∑ k` (the divisor involution, for free);
  order `x³`: **Ramanujan** `12 P₁² = 5 P₃ + P₁ - 6 θP₁`, `P_j = lamQ (k^j)` (`ramanujan`).
* `ε = -1`, order `x⁰`: `H₁ = 2 lamQ(d(-1)^k) + P₁`;  order `x²`: the level-two identity
  `2θh₁ = 2h₁² + h₁ + h₂` with `h₁ = -2 lamQ((-1)^k k)`, `h₂ = -2 lamQ((-1)^k k³)`
  (`level_two`).
-/

namespace VOA.DeligneAudit.DeligneMLDE.Heat

open PowerSeries VOA.QSeries VOA.QSeries.JTP

open scoped BigOperators

noncomputable section

/-! ## Extracting `x`-coefficients -/

/-- `π_j`: the coefficient of `xʲ` in every `q`-coefficient. -/
def pj (j : ℕ) (F : PowerSeries A) : PowerSeries ℚ := mk fun n => coeff j (coeff n F)

@[simp] theorem coeff_pj (j n : ℕ) (F : PowerSeries A) : coeff n (pj j F) = coeff j (coeff n F) := by
  simp [pj]

theorem pj_add (j : ℕ) (F G : PowerSeries A) : pj j (F + G) = pj j F + pj j G := by
  refine PowerSeries.ext fun n => ?_; simp

theorem pj_sub (j : ℕ) (F G : PowerSeries A) : pj j (F - G) = pj j F - pj j G := by
  refine PowerSeries.ext fun n => ?_; simp

theorem pj_mul (j : ℕ) (F G : PowerSeries A) :
    pj j (F * G) = ∑ p ∈ Finset.antidiagonal j, pj p.1 F * pj p.2 G := by
  refine PowerSeries.ext fun n => ?_
  simp only [coeff_pj, coeff_mul, map_sum]
  rw [Finset.sum_comm]

theorem pj_C (j : ℕ) (a : A) : pj j (C a) = C (coeff j a) := by
  refine PowerSeries.ext fun n => ?_
  simp only [coeff_pj, coeff_C]; split_ifs <;> simp

theorem pj_one (j : ℕ) : pj j (1 : PowerSeries A) = C (if j = 0 then 1 else 0) := by
  rw [← map_one (C (R := A)), pj_C, coeff_one]

theorem pj_liftD (j : ℕ) (F : PowerSeries A) :
    pj j (liftD F) = C ((j : ℚ) + 1) * pj (j + 1) F := by
  refine PowerSeries.ext fun n => ?_
  simp only [coeff_pj, coeff_liftD, coeff_derivative, coeff_C_mul]
  ring

/-! ## Lambert-type series -/

/-- `lamQ F = ∑_n qⁿ ∑_{d k = n, d ≥ 1} F d k`. -/
def lamQ (F : ℕ → ℕ → ℚ) : PowerSeries ℚ :=
  mk fun n => ∑ m ∈ Finset.range n, if (m + 1) ∣ n then F (m + 1) (n / (m + 1)) else 0

theorem coeff_lamQ (F : ℕ → ℕ → ℚ) (n : ℕ) :
    coeff n (lamQ F) = ∑ m ∈ Finset.range n, if (m + 1) ∣ n then F (m + 1) (n / (m + 1)) else 0 := by
  simp [lamQ]

theorem lamQ_add (F G : ℕ → ℕ → ℚ) : lamQ (fun d k => F d k + G d k) = lamQ F + lamQ G := by
  refine PowerSeries.ext fun n => ?_
  simp only [coeff_lamQ, map_add, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  split_ifs <;> simp

theorem lamQ_smul (c : ℚ) (F : ℕ → ℕ → ℚ) : lamQ (fun d k => c * F d k) = C c * lamQ F := by
  refine PowerSeries.ext fun n => ?_
  simp only [coeff_lamQ, coeff_C_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  split_ifs <;> simp

theorem lamQ_congr {F G : ℕ → ℕ → ℚ} (h : ∀ d k, 1 ≤ d → F d k = G d k) : lamQ F = lamQ G := by
  refine PowerSeries.ext fun n => ?_
  simp only [coeff_lamQ]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [h _ _ (by omega)]

theorem lamQ_zero : lamQ (fun _ _ => 0) = 0 := by
  refine PowerSeries.ext fun n => ?_; simp [coeff_lamQ]

/-- `θ lamQ F = lamQ (d k F)`. -/
theorem eulerOp_lamQ (F : ℕ → ℕ → ℚ) :
    eulerOp (lamQ F) = lamQ (fun d k => (d : ℚ) * k * F d k) := by
  refine PowerSeries.ext fun n => ?_
  simp only [coeff_eulerOp, coeff_lamQ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  split_ifs with h
  · have e : (n : ℚ) = ((m + 1 : ℕ) : ℚ) * ((n / (m + 1) : ℕ) : ℚ) := by
      rw [← Nat.cast_mul, Nat.mul_div_cancel' h]
    rw [e]
  · simp

/-! ## The unit `u = ε eˣ`: coefficients of its powers -/

variable (ε : ℚ) (hε : ε * ε = 1)

theorem coeff_uU_pow (j k : ℕ) :
    coeff j (((uU ε hε : Aˣ) : A) ^ k) = ε ^ k * ((k : ℚ) ^ j / (j.factorial : ℚ)) := by
  change coeff j ((ε • exp ℚ) ^ k) = _
  rw [smul_pow, exp_pow_eq_rescale_exp, coeff_smul, coeff_rescale, coeff_exp, smul_eq_mul]
  rw [Algebra.algebraMap_self, RingHom.id_apply]
  ring

theorem coeff_uU_inv_pow (j k : ℕ) :
    coeff j (((uU ε hε)⁻¹ : Aˣ) ^ k : A) = ε ^ k * ((-(k : ℚ)) ^ j / (j.factorial : ℚ)) := by
  change coeff j ((ε • evalNegHom (exp ℚ)) ^ k) = _
  rw [smul_pow, evalNegHom, ← map_pow, exp_pow_eq_rescale_exp, coeff_smul, coeff_rescale,
    coeff_rescale, coeff_exp, smul_eq_mul]
  rw [Algebra.algebraMap_self, RingHom.id_apply, neg_pow]
  ring

theorem coeff_uU (j : ℕ) : coeff j ((uU ε hε : Aˣ) : A) = ε / (j.factorial : ℚ) := by
  have := coeff_uU_pow ε hε j 1
  simpa [one_pow, pow_one] using this

/-- `π_j R`. -/
theorem pj_R (j : ℕ) :
    pj j (Rser (uU ε hε)) =
      lamQ (fun _ k => ε ^ k * (((-(k : ℚ)) ^ j - (k : ℚ) ^ j) / (j.factorial : ℚ))) := by
  refine PowerSeries.ext fun n => ?_
  rw [coeff_pj, Rser, tailSum, coeff_mk, map_sum, map_sum, coeff_lamQ]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [Finset.mem_range] at hm
  rw [rho, map_sub, coeff_gs, coeff_gs]
  split_ifs with h1 h2 h3
  · rw [map_sub, coeff_uU_inv_pow, coeff_uU_pow]; ring
  · exact absurd h1.2 h2
  · exact absurd ⟨by omega, h3⟩ h1
  · simp

/-- `π_j T`. -/
theorem pj_T (j : ℕ) :
    pj j (Tser (uU ε hε)) =
      lamQ (fun d k => -(d : ℚ) * (ε ^ k * (((k : ℚ) ^ j + (-(k : ℚ)) ^ j) / (j.factorial : ℚ))
        + if j = 0 then 1 else 0)) := by
  refine PowerSeries.ext fun n => ?_
  rw [coeff_pj, Tser, tailSum, coeff_mk, map_sum, map_sum, coeff_lamQ]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [Finset.mem_range] at hm
  rw [tau, neg_mul, map_neg, coeff_C_mul, map_add, map_add, coeff_gs, coeff_gs, coeff_gs]
  have hd : ∀ y : A, coeff j ((((m + 1 : ℕ) : A)) * y) = ((m + 1 : ℕ) : ℚ) * coeff j y := by
    intro y; rw [← map_natCast (PowerSeries.C (R := ℚ)), PowerSeries.coeff_C_mul]
  by_cases h : m + 1 ∣ n
  · rw [if_pos ⟨by omega, h⟩, if_pos ⟨by omega, h⟩, if_pos ⟨by omega, h⟩, if_pos h, map_neg, hd,
      map_add, map_add, coeff_uU_inv_pow, coeff_uU_pow, one_pow, coeff_one]
    ring
  · rw [if_neg (fun h' => h h'.2), if_neg (fun h' => h h'.2), if_neg (fun h' => h h'.2), if_neg h]
    simp


/-! ## Expanding (*) at order `xʲ` -/

theorem star_pj (w : Aˣ) (hw : dx (w : A) = w) (j : ℕ) :
    ∑ p ∈ Finset.antidiagonal j, (pj p.1 1 - pj p.1 (C (w : A))) *
        (C ((p.2 : ℚ) + 1) * pj (p.2 + 1) (Rser w)
          + ∑ q ∈ Finset.antidiagonal p.2, pj q.1 (Rser w) * pj q.2 (Rser w)
          - (pj p.2 (Tser w) + pj p.2 (Tser w)))
      = ∑ p ∈ Finset.antidiagonal j, (pj p.1 1 + pj p.1 (C (w : A))) * pj p.2 (Rser w) := by
  have h := congrArg (pj j) (star_identity w hw)
  rw [two_mul, sq] at h
  simpa only [pj_mul, pj_add, pj_sub, pj_liftD] using h

theorem C_mul_C_mul (a b : ℚ) (F G : PowerSeries ℚ) : C a * F * (C b * G) = C (a * b) * (F * G) := by
  rw [map_mul]; ring

section LevelOne

theorem hε1 : (1 : ℚ) * 1 = 1 := by norm_num

/-- `P₁ = ∑ σ₁(n) qⁿ` (as `∑_{dk=n} k`). -/
def P1 : PowerSeries ℚ := lamQ fun _ k => (k : ℚ)
/-- `P₃ = ∑ σ₃(n) qⁿ`. -/
def P3 : PowerSeries ℚ := lamQ fun _ k => (k : ℚ) ^ 3
/-- `∑_{dk=n} d`. -/
def D1 : PowerSeries ℚ := lamQ fun d _ => (d : ℚ)

theorem eulerOp_P1 : eulerOp P1 = lamQ fun d k => (d : ℚ) * k ^ 2 := by
  rw [P1, eulerOp_lamQ]; exact lamQ_congr fun d k _ => by ring

theorem r1_0 : pj 0 (Rser (uU 1 hε1)) = 0 := by
  rw [pj_R, ← lamQ_zero]; exact lamQ_congr fun d k _ => by simp

theorem r1_1 : pj 1 (Rser (uU 1 hε1)) = C (-2) * P1 := by
  rw [pj_R, P1, ← lamQ_smul]; exact lamQ_congr fun d k _ => by simp; ring

theorem r1_2 : pj 2 (Rser (uU 1 hε1)) = 0 := by
  rw [pj_R, ← lamQ_zero]; exact lamQ_congr fun d k _ => by simp

theorem r1_3 : pj 3 (Rser (uU 1 hε1)) = C (-1 / 3) * P3 := by
  rw [pj_R, P3, ← lamQ_smul]; exact lamQ_congr fun d k _ => by simp [Nat.factorial]; ring

theorem r1_4 : pj 4 (Rser (uU 1 hε1)) = 0 := by
  rw [pj_R, ← lamQ_zero]; exact lamQ_congr fun d k _ => by norm_num [Nat.factorial]

theorem t1_0 : pj 0 (Tser (uU 1 hε1)) = C (-3) * D1 := by
  rw [pj_T, D1, ← lamQ_smul]; exact lamQ_congr fun d k _ => by simp; ring

theorem t1_1 : pj 1 (Tser (uU 1 hε1)) = 0 := by
  rw [pj_T, ← lamQ_zero]; exact lamQ_congr fun d k _ => by simp

theorem t1_2 : pj 2 (Tser (uU 1 hε1)) = C (-1) * eulerOp P1 := by
  rw [pj_T, eulerOp_P1, ← lamQ_smul]; exact lamQ_congr fun d k _ => by simp [Nat.factorial]

theorem t1_3 : pj 3 (Tser (uU 1 hε1)) = 0 := by
  rw [pj_T, ← lamQ_zero]
  exact lamQ_congr fun d k _ => by rw [show ((-(k : ℚ)) ^ 3) = -(k : ℚ) ^ 3 by ring]; simp

theorem pjC1 (a : ℕ) : pj a (C ((uU 1 hε1 : Aˣ) : A)) = C (1 / (a.factorial : ℚ)) := by
  rw [pj_C, coeff_uU]

theorem order_one : D1 = P1 := by
  have h := star_pj (uU 1 hε1) (dx_uU 1 hε1) 1
  simp only [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ,
    Finset.sum_range_zero, zero_add, pj_one, pjC1, Nat.sub_zero, Nat.sub_self, Nat.reduceAdd,
    Nat.reduceSub, if_true, one_ne_zero, if_false, Nat.factorial_zero, Nat.factorial_one,
    Nat.cast_one, Nat.cast_zero, Nat.cast_ofNat] at h
  simp only [r1_0, r1_1, r1_2, t1_0, t1_1, zero_mul, mul_zero, add_zero] at h
  refine PowerSeries.ext fun n => ?_
  have hn := congrArg (coeff n) h
  simp only [sub_mul, add_mul, mul_sub, mul_add, map_add, map_sub, coeff_C_mul, map_zero] at hn
  norm_num at hn
  linarith

/-- **Ramanujan's identity** `12 P₁² = 5 P₃ + P₁ - 6 θP₁` (i.e. `12 θE₂ = E₂² - E₄`), as
formal power series over `ℚ`. -/
theorem ramanujan : C 12 * (P1 * P1) = C 5 * P3 + P1 - C 6 * eulerOp P1 := by
  have h := star_pj (uU 1 hε1) (dx_uU 1 hε1) 3
  simp only [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ,
    Finset.sum_range_zero, zero_add, pj_one, pjC1, Nat.sub_zero, Nat.sub_self, Nat.reduceAdd,
    Nat.reduceSub, if_true, one_ne_zero, if_false, Nat.factorial, Nat.cast_one, Nat.cast_zero,
    Nat.cast_ofNat, OfNat.ofNat_ne_zero] at h
  simp only [r1_0, r1_1, r1_2, r1_3, r1_4, t1_0, t1_1, t1_2, t1_3, order_one, zero_mul, mul_zero,
    add_zero, zero_add, C_mul_C_mul] at h
  refine PowerSeries.ext fun n => ?_
  have hn := congrArg (coeff n) h
  simp only [sub_mul, add_mul, mul_sub, mul_add, map_add, map_sub, coeff_C_mul, map_zero] at hn
  simp only [map_add, map_sub, coeff_C_mul, coeff_eulerOp]
  norm_num at hn
  linarith

end LevelOne

section LevelTwo

theorem hεm : (-1 : ℚ) * -1 = 1 := by norm_num

/-- `H₁ = ∑_{dk=n} (-1)^k k`. -/
def H1 : PowerSeries ℚ := lamQ fun _ k => (-1 : ℚ) ^ k * k
/-- `H₃ = ∑_{dk=n} (-1)^k k³`. -/
def H3 : PowerSeries ℚ := lamQ fun _ k => (-1 : ℚ) ^ k * (k : ℚ) ^ 3
/-- `∑_{dk=n} (-1)^k d`. -/
def DS : PowerSeries ℚ := lamQ fun d k => (-1 : ℚ) ^ k * d

theorem eulerOp_H1 : eulerOp H1 = lamQ fun d k => (-1 : ℚ) ^ k * ((d : ℚ) * k ^ 2) := by
  rw [H1, eulerOp_lamQ]; exact lamQ_congr fun d k _ => by ring

theorem r2_0 : pj 0 (Rser (uU (-1) hεm)) = 0 := by
  rw [pj_R, ← lamQ_zero]; exact lamQ_congr fun d k _ => by simp

theorem r2_1 : pj 1 (Rser (uU (-1) hεm)) = C (-2) * H1 := by
  rw [pj_R, H1, ← lamQ_smul]; exact lamQ_congr fun d k _ => by simp; ring

theorem r2_2 : pj 2 (Rser (uU (-1) hεm)) = 0 := by
  rw [pj_R, ← lamQ_zero]; exact lamQ_congr fun d k _ => by simp

theorem r2_3 : pj 3 (Rser (uU (-1) hεm)) = C (-1 / 3) * H3 := by
  rw [pj_R, H3, ← lamQ_smul]; exact lamQ_congr fun d k _ => by simp [Nat.factorial]; ring

theorem t2_0 : pj 0 (Tser (uU (-1) hεm)) = C (-2) * DS + C (-1) * P1 := by
  rw [pj_T, DS, ← order_one, D1, ← lamQ_smul, ← lamQ_smul, ← lamQ_add]
  exact lamQ_congr fun d k _ => by simp; ring

theorem t2_1 : pj 1 (Tser (uU (-1) hεm)) = 0 := by
  rw [pj_T, ← lamQ_zero]; exact lamQ_congr fun d k _ => by simp

theorem t2_2 : pj 2 (Tser (uU (-1) hεm)) = C (-1) * eulerOp H1 := by
  rw [pj_T, eulerOp_H1, ← lamQ_smul]; exact lamQ_congr fun d k _ => by simp [Nat.factorial]; ring

theorem pjC2 (a : ℕ) : pj a (C ((uU (-1) hεm : Aˣ) : A)) = C (-1 / (a.factorial : ℚ)) := by
  rw [pj_C, coeff_uU, neg_div]

/-- Order `x⁰` at `ε = -1`: `H₁ = 2 DS + P₁`. -/
theorem order_zero_two : H1 = C 2 * DS + P1 := by
  have h := star_pj (uU (-1) hεm) (dx_uU (-1) hεm) 0
  simp only [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ,
    Finset.sum_range_zero, zero_add, pj_one, pjC2, Nat.sub_zero, Nat.sub_self, Nat.reduceAdd,
    if_true, Nat.factorial, Nat.cast_one, Nat.cast_zero] at h
  simp only [r2_0, r2_1, t2_0, zero_mul, mul_zero, add_zero, zero_add, C_mul_C_mul] at h
  refine PowerSeries.ext fun n => ?_
  have hn := congrArg (coeff n) h
  simp only [sub_mul, add_mul, mul_sub, mul_add, map_add, map_sub, coeff_C_mul, map_zero] at hn
  simp only [map_add, map_sub, coeff_C_mul]
  norm_num at hn
  linarith

/-- **The level-two identity** `4H₁² = H₁ + H₃ - 2θH₁`. -/
theorem level_two : C 4 * (H1 * H1) = H1 + H3 - C 2 * eulerOp H1 := by
  have h := star_pj (uU (-1) hεm) (dx_uU (-1) hεm) 2
  simp only [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ,
    Finset.sum_range_zero, zero_add, pj_one, pjC2, Nat.sub_zero, Nat.sub_self, Nat.reduceAdd,
    Nat.reduceSub, if_true, one_ne_zero, if_false, Nat.factorial, Nat.cast_one, Nat.cast_zero,
    Nat.cast_ofNat, OfNat.ofNat_ne_zero] at h
  simp only [r2_0, r2_1, r2_2, r2_3, t2_0, t2_1, t2_2, zero_mul, mul_zero, add_zero, zero_add,
    C_mul_C_mul] at h
  refine PowerSeries.ext fun n => ?_
  have hn := congrArg (coeff n) h
  simp only [sub_mul, add_mul, mul_sub, mul_add, map_add, map_sub, coeff_C_mul, map_zero] at hn
  simp only [map_add, map_sub, coeff_C_mul, coeff_eulerOp]
  have h0 := congrArg (coeff n) order_zero_two
  simp only [map_add, coeff_C_mul] at h0
  norm_num at hn
  linarith

end LevelTwo

end

end VOA.DeligneAudit.DeligneMLDE.Heat
