/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneCharacterD4Wp5

/-!
# The Schur integrand as a square (layer 6)

With `Y = -D log Den = ∑_{k} ∑_{p ≥ 1} (x^p - x^{-p}) r^{(2k+1)p}` and `W = D²Y = r W₁`:

* `C3_Den_Y`: `C₃(Den) = -Den³ · D²Y`;
* `integrand_sq`: `η(r²)¹⁰ · Θ(x) · M_num(x) = -Den⁸ · W₁²`, where
  `Θ = (q)(x²)(x⁻²)` and `M_num = (q)(qx²)(qx⁻²)` (`q = r²`).
-/

namespace VOA.DeligneAudit.DeligneCharacter.D4Wp

open PowerSeries VOA.QSeries VOA.QSeries.JTP

open scoped BigOperators

noncomputable section

/-- `∑_{p ≥ 1} c^p X^p`. -/
def geomC (c : L) : PowerSeries L := PowerSeries.mk fun k => if k = 0 then 0 else c ^ k

theorem one_sub_mul_geomC (c : L) : (1 - PowerSeries.C c * X) * geomC c = PowerSeries.C c * X := by
  ext k : 1
  rw [sub_mul, one_mul, mul_assoc, map_sub, coeff_C_mul, coeff_C_mul]
  rcases k with _ | k
  · simp [geomC]
  · rw [coeff_succ_X_mul, coeff_X]
    rcases k with _ | k
    · simp [geomC]
    · simp [geomC, pow_succ]; ring

/-- `∑_{p ≥ 1} c^p X^{(2k+1)p}`. -/
def gs (c : L) (k : ℕ) : PowerSeries L := expand (2 * k + 1) (by omega) (geomC c)

theorem one_sub_mul_gs (c : L) (k : ℕ) :
    (1 - PowerSeries.C c * X ^ (2 * k + 1)) * gs c k = PowerSeries.C c * X ^ (2 * k + 1) := by
  have h := congrArg (expand (2 * k + 1) (by omega)) (one_sub_mul_geomC c)
  simpa [gs, map_mul, map_sub, expand_C, expand_X] using h

theorem coeff_gs (c : L) (k n : ℕ) :
    coeff n (gs c k) = if (2 * k + 1) ∣ n then (if n / (2 * k + 1) = 0 then 0 else c ^ (n / (2 * k + 1)))
      else 0 := by
  rw [gs, coeff_expand]
  split_ifs <;> simp_all [geomC]

theorem X_pow_dvd_gs (c : L) (k : ℕ) : (X : PowerSeries L) ^ (k + 1) ∣ gs c k := by
  rw [PowerSeries.X_pow_dvd_iff]
  intro n hn
  rw [coeff_gs]
  split_ifs with h1 h2
  · rfl
  · exact absurd (Nat.div_eq_of_lt (by omega)) h2
  · rfl

theorem Da_one_sub_C_mono (j : ℤ) (e : ℕ) :
    DQ wa (1 - PowerSeries.C (mono j) * X ^ e) = -(PowerSeries.C (cst j) * (PowerSeries.C (mono j) * X ^ e)) := by
  rw [DQ_sub, DQ_one, DQ_mul, DQ_C, wd_mono, show DQ wa (X ^ e : PowerSeries L) = 0 from Da_X_pow e, map_mul]
  ring

/-- `Y = ∑_k (gs x k - gs x⁻¹ k)`. -/
def Yser : PowerSeries L := lsum' fun k => gs (mono 1) k - gs (mono (-1)) k

theorem Da_Den : Da Den = -Yser * Den := by
  rw [Yser, ← lsum'_neg]
  exact DQ_infProd _ _ ((pfA _).mul (pfA _))
    (fun k => (dvd_sub (X_pow_dvd_gs _ k) (X_pow_dvd_gs _ k)).neg_right) fun k => by
      show DQ wa (_ * _) = _
      rw [DQ_mul, Da_one_sub_C_mono, Da_one_sub_C_mono]
      have h1 := one_sub_mul_gs (mono 1) k
      have h2 := one_sub_mul_gs (mono (-1)) k
      simp only [Int.cast_one, Int.cast_neg, map_one, map_neg, one_mul, neg_mul]
      linear_combination
        ((1 - PowerSeries.C (mono (-1)) * X ^ (2 * k + 1))) * h1 -
        ((1 - PowerSeries.C (mono 1) * X ^ (2 * k + 1))) * h2

theorem DQ_neg' (F : PowerSeries L) : DQ wa (-F) = -DQ wa F := by
  ext n : 1; simp [wd_neg]

theorem C3_Den_Y : C3 Den = -Den ^ 3 * DQ wa (DQ wa Yser) := by
  have h1 : DQ wa Den = -Yser * Den := Da_Den
  have h2 : DQ wa (DQ wa Den) = (Yser ^ 2 - DQ wa Yser) * Den := by
    rw [h1, DQ_mul, DQ_neg', h1]; ring
  have h3 : DQ wa (DQ wa (DQ wa Den)) =
      (-DQ wa (DQ wa Yser) + 3 * Yser * DQ wa Yser - Yser ^ 3) * Den := by
    rw [h2, DQ_mul, DQ_sub, pow_two, DQ_mul, h1]; ring
  rw [C3]; simp only [Da]; rw [h3, h2, h1]; ring

/-- `W = D²Y`. -/
def Wser : PowerSeries L := DQ wa (DQ wa Yser)

/-- **The `x`-annulus form of `℘' = -σ(2z)/σ⁴`**: `-Den³ W = η⁶ r x⁻¹ Den(-x) ϑ(x)ϑ(-x)`. -/
theorem W_identity : -(Den ^ 3 * Wser) = etaR ^ 6 * X * PowerSeries.C (mono (-1)) * Denm * thxR := by
  rw [← C3_Den, C3_Den_Y, Wser]; ring

theorem coeff_zero_Yser : coeff 0 Yser = 0 := by
  rw [Yser, coeff_lsum' _ (fun k => dvd_sub (X_pow_dvd_gs _ k) (X_pow_dvd_gs _ k))]; rfl

/-- `W₁ = W/r`. -/
def W1 : PowerSeries L := PowerSeries.mk fun n => coeff (n + 1) Wser

theorem X_mul_W1 : X * W1 = Wser := by
  ext n : 1
  rcases n with _ | n
  · rw [coeff_zero_X_mul, Wser, coeff_DQ, coeff_DQ, coeff_zero_Yser, wd_zero, wd_zero]
  · rw [coeff_succ_X_mul, W1, coeff_mk]

/-! ## The integrand -/

def uf (k : ℕ) : PowerSeries L :=
  (1 - PowerSeries.C (mono 2) * X ^ (2 * k + 2)) * (1 - PowerSeries.C (mono (-2)) * X ^ (2 * k + 2))

theorem pf_uf : ProdFactors uf :=
  (pf_sub _ (fun k => 2 * k + 2) (fun k => by show k < 2 * k + 2; omega)).mul
    (pf_sub _ (fun k => 2 * k + 2) (fun k => by show k < 2 * k + 2; omega))

/-- `∏(1 - x²qᵐ)(1 - x⁻²qᵐ)`, `q = r²`. -/
def Uq : PowerSeries L := infProd uf

/-- `Θ(x) = (q)(x²)(x⁻²)`. -/
def ThX : PowerSeries L :=
  (1 - PowerSeries.C (mono 2)) * (1 - PowerSeries.C (mono (-2))) * etaR * Uq

/-- `M_num = (q)(qx²)(qx⁻²)`. -/
def Mnum : PowerSeries L := etaR * Uq

theorem C_mono_mul (i j : ℤ) :
    PowerSeries.C (mono i) * PowerSeries.C (mono j) = (PowerSeries.C (mono (i + j)) : PowerSeries L) := by
  rw [← map_mul, mono_mul]

/-- **Duplication on the `x`-annulus**: `(1 - x²)∏(1 - x²qᵐ)(1 - x⁻²qᵐ) = ϑ(x)ϑ(-x) Den(x) Den(-x)`. -/
theorem dup_x : (1 - PowerSeries.C (mono 2)) * Uq = thxR * Den * Denm := by
  have hDD : Den * Denm = infProd fun k =>
      (1 - PowerSeries.C (mono 2) * X ^ (4 * k + 2)) * (1 - PowerSeries.C (mono (-2)) * X ^ (4 * k + 2)) := by
    rw [Den, Denm, infProd_mul ((pfA _).mul (pfA _)) ((pfA' _).mul (pfA' _))]
    refine infProd_congr fun k => ?_
    have e1 := C_mono_mul 1 1
    have e2 := C_mono_mul (-1) (-1)
    norm_num at e1 e2
    rw [← e1, ← e2]; ring
  have hRR : Ra * Rc = infProd fun k =>
      (1 - PowerSeries.C (mono 2) * X ^ (4 * k + 4)) * (1 - PowerSeries.C (mono (-2)) * X ^ (4 * k + 4)) := by
    rw [Ra, Rc, infProd_mul (pf4 _ 1 le_rfl) (pf4 _ 1 le_rfl)]
  have hpf1 : ProdFactors fun k =>
      (1 - PowerSeries.C (mono 2) * X ^ (4 * k + 2)) * (1 - PowerSeries.C (mono (-2)) * X ^ (4 * k + 2)) :=
    (pf_sub _ (fun k => 4 * k + 2) (fun k => by show k < 4 * k + 2; omega)).mul
      (pf_sub _ (fun k => 4 * k + 2) (fun k => by show k < 4 * k + 2; omega))
  have hpf2 : ProdFactors fun k =>
      (1 - PowerSeries.C (mono 2) * X ^ (4 * k + 4)) * (1 - PowerSeries.C (mono (-2)) * X ^ (4 * k + 4)) :=
    (pf_sub _ (fun k => 4 * k + 4) (fun k => by show k < 4 * k + 4; omega)).mul
      (pf_sub _ (fun k => 4 * k + 4) (fun k => by show k < 4 * k + 4; omega))
  have hU : Uq = (Den * Denm) * (Ra * Rc) := by
    rw [Uq, ← infProd_pairs pf_uf, hDD, hRR, infProd_mul hpf1 hpf2]
    refine infProd_congr fun k => ?_
    rw [uf, uf]; ring_nf
  rw [hU, thxR]; ring

/-- **The Schur integrand is a square**: `η¹⁰ Θ M_num = -Den⁸ W₁²`. -/
theorem integrand_sq : etaR ^ 10 * (ThX * Mnum) = -(Den ^ 8 * W1 ^ 2) := by
  have hW := W_identity
  have hd := dup_x
  have hm2 : PowerSeries.C (mono (-2)) * PowerSeries.C (mono 2) = (1 : PowerSeries L) := by
    rw [C_mono_mul]; norm_num [mono_zero]
  have hm1 : PowerSeries.C (mono (-1)) * PowerSeries.C (mono (-1)) = (PowerSeries.C (mono (-2)) : PowerSeries L) := by
    rw [C_mono_mul]; norm_num
  rw [← X_mul_W1] at hW
  have hcm : (1 - PowerSeries.C (mono (-2)) : PowerSeries L) =
      -PowerSeries.C (mono (-2)) * (1 - PowerSeries.C (mono 2)) := by linear_combination -hm2
  have hsq : PowerSeries.C (mono (-2)) * etaR ^ 12 * X ^ 2 * (thxR * Denm) ^ 2 = Den ^ 6 * X ^ 2 * W1 ^ 2 := by
    linear_combination (-(etaR ^ 6 * X * PowerSeries.C (mono (-1)) * Denm * thxR +
      -(Den ^ 3 * (X * W1)))) * hW - etaR ^ 12 * X ^ 2 * (thxR * Denm) ^ 2 * hm1
  have e1 : etaR ^ 10 * (ThX * Mnum) =
      -PowerSeries.C (mono (-2)) * etaR ^ 12 * ((1 - PowerSeries.C (mono 2)) * Uq) ^ 2 := by
    rw [ThX, Mnum, hcm]; ring
  rw [hd] at e1
  have key : X ^ 2 * (etaR ^ 10 * (ThX * Mnum) + Den ^ 8 * W1 ^ 2) = 0 := by
    rw [e1]; linear_combination -Den ^ 2 * hsq
  have hX : (X : PowerSeries L) ^ 2 ≠ 0 := pow_ne_zero 2 PowerSeries.X_ne_zero
  rcases mul_eq_zero.mp key with h0 | h0
  · exact absurd h0 hX
  · linear_combination h0

end

end VOA.DeligneAudit.DeligneCharacter.D4Wp
