/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneCharacterD4Wp7

/-!
# The constant term of `W₁²` (layer 8)

`CT_x(W₁²) = -2 ∑_N (N+1) σ₃(N+1) r^{2N}`.
-/

namespace VOA.DeligneAudit.DeligneCharacter.D4Wp

open PowerSeries VOA.QSeries VOA.QSeries.JTP

open scoped BigOperators

noncomputable section

theorem mono_pow (j : ℤ) (p : ℕ) : mono j ^ p = mono (p * j) := by
  induction p with
  | zero => simp [mono_zero]
  | succ p ih => rw [pow_succ, ih, mono_mul]; push_cast; ring_nf

/-- Index box for pairs `(k, p)`. -/
def nbox (n : ℕ) : Finset (ℕ × ℕ) := Finset.range (n + 1) ×ˢ Finset.range (n + 1)

/-- `(k, p) ↦ (2k+1)(p+1)`. -/
def EY (i : ℕ × ℕ) : ℕ := (2 * i.1 + 1) * (i.2 + 1)

theorem hbox_EY : ∀ n i, EY i ≤ n → i ∈ nbox n := by
  intro n i hi
  rw [nbox, Finset.mem_product, Finset.mem_range, Finset.mem_range]
  rw [EY] at hi
  constructor <;> nlinarith

/-- The weight `x^{p+1} - x^{-(p+1)}`. -/
def wY (i : ℕ × ℕ) : L := mono (i.2 + 1) - mono (-((i.2 : ℤ) + 1))

theorem coeff_gs_sub (k n : ℕ) (hn : n ≠ 0) :
    coeff n (gs (mono 1) k - gs (mono (-1)) k) =
      if (2 * k + 1) ∣ n then mono (n / (2 * k + 1) : ℕ) - mono (-((n / (2 * k + 1) : ℕ) : ℤ)) else 0 := by
  rw [map_sub, coeff_gs, coeff_gs]
  split_ifs with h1 h2
  · exfalso; obtain ⟨t, ht⟩ := h1; rw [ht, Nat.mul_div_cancel_left _ (by omega)] at h2; subst h2; simp at ht
    exact hn ht
  · rw [mono_pow, mono_pow]; push_cast; ring_nf
  · simp

theorem Yser_eq : Yser = lat (fib nbox EY) wY := by
  ext n : 1
  rw [Yser, coeff_lsum' _ (fun k => dvd_sub (X_pow_dvd_gs _ k) (X_pow_dvd_gs _ k)), coeff_lat]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Finset.range_zero, Finset.sum_empty]
    symm; refine Finset.sum_eq_zero fun i hi => ?_
    rw [mem_fib hbox_EY, EY] at hi; exfalso; nlinarith [Nat.zero_le i.1, Nat.zero_le i.2]
  rw [Finset.sum_congr rfl fun k _ => coeff_gs_sub k n (by omega), ← Finset.sum_filter]
  refine Finset.sum_nbij' (fun k => (k, n / (2 * k + 1) - 1)) (fun i => i.1) ?_ ?_ ?_ ?_ ?_
  · intro k hk
    rw [Finset.mem_filter, Finset.mem_range] at hk
    rw [mem_fib hbox_EY, EY]
    obtain ⟨t, ht⟩ := hk.2
    have hq : (2 * k + 1) * t / (2 * k + 1) = t := Nat.mul_div_cancel_left t (by omega)
    have : 1 ≤ t := by rcases t with _ | t; · omega
                       · omega
    dsimp only; rw [ht, hq, Nat.sub_add_cancel this]
  · intro i hi
    rw [mem_fib hbox_EY, EY] at hi
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨by nlinarith, ⟨i.2 + 1, hi.symm⟩⟩
  · intro k _; rfl
  · intro i hi
    rw [mem_fib hbox_EY, EY] at hi
    ext
    · rfl
    · dsimp only; rw [← hi, Nat.mul_div_cancel_left _ (by omega)]; omega
  · intro k hk
    rw [Finset.mem_filter] at hk
    rw [wY]
    obtain ⟨t, ht⟩ := hk.2
    have hq : (2 * k + 1) * t / (2 * k + 1) = t := Nat.mul_div_cancel_left t (by omega)
    have : 1 ≤ t := by rcases t with _ | t; · rw [mul_zero] at ht; omega
                       · omega
    dsimp only
    rw [ht, hq]
    push_cast [Nat.cast_sub this]; ring_nf

/-- `(p+1)²(x^{p+1} - x^{-(p+1)})`. -/
def wW (i : ℕ × ℕ) : L := cst (((i.2 : ℚ) + 1) ^ 2) * wY i

theorem wd_wd_wY (i : ℕ × ℕ) : wd wa (wd wa (wY i)) = wW i := by
  rw [wW, wY, wd_sub, wd_sub, wd_mono, wd_mono, wd_cst_mul, wd_cst_mul, wd_mono, wd_mono]
  simp only [← mul_assoc, ← map_mul, mul_sub]
  congr 2 <;> push_cast <;> ring

theorem Wser_eq : Wser = lat (fib nbox EY) wW := by
  rw [Wser, Yser_eq, DQ_lat, DQ_lat]
  exact lat_congr _ wd_wd_wY

/-- `(k, p) ↦ (2k+1)(p+1) - 1`. -/
def EY1 (i : ℕ × ℕ) : ℕ := EY i - 1

theorem EY_pos (i : ℕ × ℕ) : 1 ≤ EY i := by rw [EY]; nlinarith [Nat.zero_le i.1, Nat.zero_le i.2]

theorem hbox_EY1 : ∀ n i, EY1 i ≤ n → i ∈ nbox n := by
  intro n i hi
  rw [EY1] at hi
  have h := EY_pos i
  rw [nbox, Finset.mem_product, Finset.mem_range, Finset.mem_range]
  rw [EY] at hi h
  have h2 : (2 * i.1 + 1) * (i.2 + 1) ≤ n + 1 := by omega
  constructor <;> nlinarith

theorem W1_eq : W1 = lat (fib nbox EY1) wW := by
  ext n : 1
  rw [W1, coeff_mk, Wser_eq, coeff_lat, coeff_lat]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext i
  rw [mem_fib hbox_EY, mem_fib hbox_EY1, EY1]
  have := EY_pos i
  omega

/-! ## Constant term in `x` -/

/-- The `x⁰`-coefficient, `ℚ[x^{±1}]⟦r⟧ → ℚ⟦r⟧`. -/
def ctx (F : PowerSeries L) : PowerSeries ℚ := PowerSeries.mk fun n => (coeff n F) 0

theorem ctx_lat {ι : Type*} (S : ℕ → Finset ι) (w : ι → L) :
    ctx (lat S w) = lat S (fun i => (w i) 0) := by
  ext n : 1
  rw [ctx, coeff_mk, coeff_lat, coeff_lat]
  exact Finsupp.finset_sum_apply _ _ _

theorem L_sub_apply (f g : L) (i : ℤ) : (f - g) i = f i - g i := Finsupp.sub_apply f g i

theorem mono_apply (j i : ℤ) : (mono j) i = if j = i then 1 else 0 := by
  rw [mono]; exact Finsupp.single_apply

theorem cst_mul_apply (c : ℚ) (f : L) (i : ℤ) : (cst c * f) i = c * f i := by
  rw [cst_apply]; exact AddMonoidAlgebra.single_zero_mul_apply _ _ _

theorem wW_mul_wW_zero (i i' : ℕ × ℕ) :
    (wW i * wW i') 0 = if i.2 = i'.2 then -2 * ((i.2 : ℚ) + 1) ^ 4 else 0 := by
  rw [wW, wW, show cst (((i.2 : ℚ) + 1) ^ 2) * wY i * (cst (((i'.2 : ℚ) + 1) ^ 2) * wY i') =
    cst (((i.2 : ℚ) + 1) ^ 2 * ((i'.2 : ℚ) + 1) ^ 2) * (wY i * wY i') by rw [map_mul]; ring,
    cst_mul_apply, wY, wY]
  simp only [sub_mul, mul_sub, mono_mul]
  simp only [L_sub_apply, mono_apply]
  by_cases h : i.2 = i'.2
  · rw [if_pos h, if_neg (by omega), if_pos (by rw [h]; ring), if_pos (by rw [h]; ring),
      if_neg (by omega), h]
    ring
  · rw [if_neg h, if_neg (by omega), if_neg (by intro h'; apply h; exact_mod_cast (by linarith : (i.2 : ℤ) = i'.2)),
      if_neg (by intro h'; apply h; exact_mod_cast (by linarith : (i.2 : ℤ) = i'.2)), if_neg (by omega)]
    ring

theorem hb2_EY1 : ∀ n (x : (ℕ × ℕ) × (ℕ × ℕ)), EY1 x.1 + EY1 x.2 ≤ n → x ∈ nbox n ×ˢ nbox n :=
  fun n x hx => Finset.mem_product.mpr ⟨hbox_EY1 n _ (by omega), hbox_EY1 n _ (by omega)⟩

theorem ctx_W1_sq_coeff (n : ℕ) :
    coeff n (ctx (W1 * W1)) = ∑ x ∈ fib (fun n => nbox n ×ˢ nbox n) (fun x => EY1 x.1 + EY1 x.2) n,
      if x.1.2 = x.2.2 then -2 * ((x.1.2 : ℚ) + 1) ^ 4 else 0 := by
  rw [W1_eq, lat_mul_fiber _ _ hbox_EY1 _ _ hbox_EY1, ctx_lat, coeff_lat]
  exact Finset.sum_congr rfl fun x _ => wW_mul_wW_zero x.1 x.2

theorem EY1_add (k k' p : ℕ) : EY1 (k, p) + EY1 (k', p) + 2 = 2 * ((k + k' + 1) * (p + 1)) := by
  rw [EY1, EY1, EY, EY]
  have h1 : 1 ≤ (2 * k + 1) * (p + 1) := by nlinarith
  have h2 : 1 ≤ (2 * k' + 1) * (p + 1) := by nlinarith
  dsimp only
  zify [h1, h2]; ring

/-- **The constant term of `W₁²`** at even order. -/
theorem ctx_W1_sq_even (N : ℕ) :
    coeff (2 * N) (ctx (W1 * W1)) = -2 * ((N + 1 : ℕ) : ℚ) * ∑ d ∈ (N + 1).divisors, (d : ℚ) ^ 3 := by
  rw [ctx_W1_sq_coeff, ← Finset.sum_filter]
  rw [Finset.mul_sum]
  rw [show ∑ d ∈ (N + 1).divisors, -2 * ((N + 1 : ℕ) : ℚ) * (d : ℚ) ^ 3 =
      ∑ d ∈ (N + 1).divisors, ∑ _q ∈ Finset.antidiagonal ((N + 1) / d - 1), -2 * (d : ℚ) ^ 4 by
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [Finset.sum_const, Finset.Nat.card_antidiagonal, nsmul_eq_mul]
    have hd' := Nat.dvd_of_mem_divisors hd
    have hpos : 0 < d := Nat.pos_of_mem_divisors hd
    obtain ⟨t, ht⟩ := hd'
    rw [ht, Nat.mul_div_cancel_left _ hpos]
    have ht1 : 1 ≤ t := by rcases t with _ | t; · simp at ht
                           · omega
    rw [Nat.sub_add_cancel ht1]; push_cast; ring]
  rw [Finset.sum_sigma']
  refine Finset.sum_nbij' (fun x => ⟨x.1.2 + 1, (x.1.1, x.2.1)⟩)
    (fun y => ((y.2.1, y.1 - 1), (y.2.2, y.1 - 1))) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨⟨k, p⟩, ⟨k', p'⟩⟩ hx
    rw [Finset.mem_filter, mem_fib hb2_EY1] at hx
    obtain ⟨h1, h2⟩ := hx
    dsimp only at h1 h2; subst h2
    have h3 := EY1_add k k' p
    have h4 : (k + k' + 1) * (p + 1) = N + 1 := by omega
    simp only [Finset.mem_sigma, Nat.mem_divisors, Finset.mem_antidiagonal]
    refine ⟨⟨⟨k + k' + 1, by rw [← h4, mul_comm]⟩, by omega⟩, ?_⟩
    rw [← h4, Nat.mul_div_cancel _ (by omega)]; omega
  · rintro ⟨d, ⟨k, k'⟩⟩ hy
    simp only [Finset.mem_sigma, Nat.mem_divisors, Finset.mem_antidiagonal] at hy
    obtain ⟨⟨⟨t, ht⟩, -⟩, h⟩ := hy
    have hd : 0 < d := by rcases d with _ | d; · simp at ht
                          · omega
    rw [ht, Nat.mul_div_cancel_left _ hd] at h
    rw [Finset.mem_filter, mem_fib hb2_EY1]
    refine ⟨?_, rfl⟩
    have h3 := EY1_add k k' (d - 1)
    rw [Nat.sub_add_cancel hd] at h3
    have ht0 : t ≠ 0 := by rintro rfl; simp at ht
    have hk : k + k' + 1 = t := by omega
    have h5 : (k + k' + 1) * d = N + 1 := by rw [hk, ht, mul_comm]
    dsimp only
    rw [h5] at h3
    omega
  · rintro ⟨⟨k, p⟩, ⟨k', p'⟩⟩ hx
    rw [Finset.mem_filter] at hx
    dsimp only at hx ⊢
    rw [hx.2]; simp
  · rintro ⟨d, ⟨k, k'⟩⟩ hy
    simp only [Finset.mem_sigma, Nat.mem_divisors] at hy
    have hd : 0 < d := Nat.pos_of_dvd_of_pos hy.1.1 (by omega)
    simp only [Sigma.mk.injEq]
    exact ⟨by omega, HEq.rfl⟩
  · rintro ⟨⟨k, p⟩, ⟨k', p'⟩⟩ hx
    rw [Finset.mem_filter] at hx
    dsimp only at hx ⊢
    push_cast; ring

/-- The constant term of `W₁²` vanishes at odd order. -/
theorem ctx_W1_sq_odd (N : ℕ) : coeff (2 * N + 1) (ctx (W1 * W1)) = 0 := by
  rw [ctx_W1_sq_coeff]
  refine Finset.sum_eq_zero fun x hx => ?_
  rw [mem_fib hb2_EY1] at hx
  split_ifs with h
  · exfalso
    obtain ⟨⟨k, p⟩, ⟨k', p'⟩⟩ := x
    dsimp only at h hx; subst h
    have := EY1_add k k' p
    omega
  · rfl

end

end VOA.DeligneAudit.DeligneCharacter.D4Wp
