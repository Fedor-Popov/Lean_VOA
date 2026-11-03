/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneMLDERamanujanAdapters

/-!
# Closed forms of the AK MLDE solution for `h∨ = 6s` (generic machinery)

For `h = h∨ = 6(t+1)` (`D₄, E₆, E₇, E₈` at `t = 0, 1, 2, 4`) the normalised AK solution is
`η^{2h-2} · ch = H` for a quasimodular form `H` of weight `h` and depth `≤ 1`, vanishing to order
`s = t + 1` at `q = 0`. In formal `q`-series with `P = ∏(1 - qⁿ)` and `k = 2h - 2 = 12t + 10`:

  `∑_N mldeCoeff h N · q^{N+s} = H · P⁻ᵏ / [q^s] H`.

This file proves this generically from two inputs on `H`:

* `HOde t H`: `144θ²H - 24h E₂θH + h(h-1)(E₂² - E₄)H = 0` (the AK equation transported to `H`);
* the low coefficients `[q^n] H = 0` for `n ≤ t` and `[q^{t+1}] H ≠ 0`.

Main result: `isAKSolution_of_HOde`, `eq_mldeCoeff_of_HOde`.

The transport identity `G_ode_of_HOde` (AK equation for `G = H·P⁻ᵏ` ⇔ `HOde` for `H`) uses only the
Ramanujan identity for `E₂`; the derivation of `HOde` for a concrete `H` uses all three.
-/

namespace VOA.DeligneAudit.DeligneCharacter.MLDEClosed

open PowerSeries VOA.QSeries VOA.QSeries.JTP VOA.DeligneAudit.DeligneCharacter.D4MLDE

noncomputable section

theorem eulerOp_natCast (n : ℕ) : eulerOp (n : PowerSeries ℚ) = 0 := by
  rw [← map_natCast (PowerSeries.C (R := ℚ)) n, show (PowerSeries.C (n : ℚ)) =
    PowerSeries.C (n : ℚ) * 1 by rw [mul_one], eulerOp_C_mul, eulerOp_one, mul_zero]

theorem eulerOp_ofNat (n : ℕ) [n.AtLeastTwo] : eulerOp (OfNat.ofNat n : PowerSeries ℚ) = 0 := by
  rw [← map_ofNat (PowerSeries.C (R := ℚ)) n, show (PowerSeries.C (OfNat.ofNat n : ℚ)) =
    PowerSeries.C (OfNat.ofNat n : ℚ) * 1 by rw [mul_one], eulerOp_C_mul, eulerOp_one, mul_zero]

theorem coeff_natCast_mul (n : ℕ) (f : PowerSeries ℚ) (N : ℕ) :
    coeff N ((n : PowerSeries ℚ) * f) = (n : ℚ) * coeff N f := by
  rw [← map_natCast (PowerSeries.C (R := ℚ)) n, coeff_C_mul]

theorem eulerOp_euler_pow (n : ℕ) :
    eulerOp ((euler : PowerSeries ℚ) ^ n) = -((n : PowerSeries ℚ) * euler ^ n * sigS 1) := by
  induction n with
  | zero => simp [eulerOp_one]
  | succ n ih => rw [pow_succ, eulerOp_mul, ih, eulerOp_euler]; push_cast; ring

/-- `P⁻ᵏ`. -/
def Qk (k : ℕ) : PowerSeries ℚ := reciprocalEuler ^ k

theorem euler_pow_mul_Qk (k : ℕ) : (euler : PowerSeries ℚ) ^ k * Qk k = 1 := by
  rw [Qk, ← mul_pow, euler_mul_reciprocal, one_pow]

theorem eulerOp_Qk (k : ℕ) : 24 * eulerOp (Qk k) = (k : PowerSeries ℚ) * Qk k * (1 - E2s) := by
  have h0 := congrArg eulerOp (euler_pow_mul_Qk k)
  rw [eulerOp_one, eulerOp_mul, eulerOp_euler_pow] at h0
  have hu : IsUnit ((euler : PowerSeries ℚ) ^ k) := isUnit_euler.pow k
  apply hu.mul_left_cancel
  rw [E2s]
  linear_combination 24 * h0 + (24 * (k : PowerSeries ℚ) * sigS 1) * euler_pow_mul_Qk k -
    (24 * (k : PowerSeries ℚ) * sigS 1) * euler_pow_mul_Qk k

theorem coeff_zero_Qk (k : ℕ) : coeff 0 (Qk k) = 1 := by
  rw [coeff_zero_eq_constantCoeff_apply, Qk, map_pow]
  have : constantCoeff (reciprocalEuler : PowerSeries ℚ) = 1 := by
    have h := congrArg constantCoeff (euler_mul_reciprocal (R := ℚ))
    rwa [map_mul, map_one, constantCoeff_euler, one_mul] at h
  rw [this, one_pow]

/-- **The transported AK equation** at `h = 6t+6`:
`144θ²H - 24h E₂θH + h(h-1)(E₂² - E₄)H = 0`. -/
def HOde (t : ℕ) (H : PowerSeries ℚ) : Prop :=
  144 * eulerOp (eulerOp H) - 24 * (6 * (t : PowerSeries ℚ) + 6) * E2s * eulerOp H +
    (6 * (t : PowerSeries ℚ) + 6) * (6 * (t : PowerSeries ℚ) + 5) * (E2s ^ 2 - E4s) * H = 0

theorem two_ne_zero' : (2 : PowerSeries ℚ) ≠ 0 := by
  intro h
  have := congrArg PowerSeries.constantCoeff h
  rw [map_ofNat, map_zero] at this
  norm_num at this

/-- The AK equation (times 24, in `G = q^s g`) for `G = H·P⁻ᵏ`, `k = 12t + 10`. -/
theorem G_ode_of_HOde (hR : RamanujanIdentities) (t : ℕ) (H : PowerSeries ℚ) (hH : HOde t H) :
    let G := H * Qk (12 * t + 10)
    let T := (t : PowerSeries ℚ)
    144 * eulerOp (eulerOp G) - 24 * (6 * T + 6) * eulerOp G -
      ((6 * T + 6) ^ 2 - 1) * (E4s - 1) * G + 24 * (1 - E2s) * eulerOp G -
      (12 * T + 10) * (1 - E2s) * G = 0 := by
  intro G T
  set A := E2s
  set B := E4s
  set Q := Qk (12 * t + 10)
  set tH := eulerOp H
  set ttH := eulerOp tH
  set tQ := eulerOp Q
  set ttQ := eulerOp tQ
  set a := eulerOp A
  have hode : 144 * ttH - 24 * (6 * T + 6) * A * tH + (6 * T + 6) * (6 * T + 5) * (A ^ 2 - B) * H = 0 :=
    hH
  have h2 : 12 * a = A ^ 2 - B := hR.e2
  have hq : 24 * tQ = (12 * T + 10) * Q * (1 - A) := by
    have := eulerOp_Qk (12 * t + 10); push_cast at this; exact this
  have hqd : 24 * ttQ = (12 * T + 10) * tQ * (1 - A) - (12 * T + 10) * Q * a := by
    have := congrArg eulerOp hq
    have n24 : eulerOp (24 : PowerSeries ℚ) = 0 := eulerOp_ofNat 24
    have n12 : eulerOp (12 : PowerSeries ℚ) = 0 := eulerOp_ofNat 12
    have n10 : eulerOp (10 : PowerSeries ℚ) = 0 := eulerOp_ofNat 10
    have nT : eulerOp T = 0 := eulerOp_natCast t
    simp only [eulerOp_mul, eulerOp_add, eulerOp_sub, eulerOp_one, n24, n12, n10, nT] at this
    linear_combination this
  have hG : eulerOp G = tH * Q + H * tQ := eulerOp_mul _ _
  have hGG : eulerOp (eulerOp G) = ttH * Q + 2 * tH * tQ + H * ttQ := by
    rw [hG, eulerOp_add, eulerOp_mul, eulerOp_mul]; ring
  rw [hGG, hG]
  have key : (2 : PowerSeries ℚ) * (144 * (ttH * Q + 2 * tH * tQ + H * ttQ) -
      24 * (6 * T + 6) * (tH * Q + H * tQ) - ((6 * T + 6) ^ 2 - 1) * (B - 1) * (H * Q) +
      24 * (1 - A) * (tH * Q + H * tQ) - (12 * T + 10) * (1 - A) * (H * Q)) = 0 := by
    linear_combination (2 * Q) * hode + (12 * H) * hqd +
      (24 * tH - (6 * T + 7) * A * H - (6 * T + 5) * H) * hq + (-2 * H * Q * (6 * T + 5)) * h2
  exact (mul_eq_zero.mp key).resolve_left two_ne_zero'

/-! ## Division by `q^s` -/

/-- `g = G/q^s`. -/
def gOf (s : ℕ) (G : PowerSeries ℚ) : PowerSeries ℚ := PowerSeries.mk fun N => coeff (N + s) G

theorem X_pow_mul_gOf (s : ℕ) (G : PowerSeries ℚ) (hG : ∀ n < s, coeff n G = 0) :
    X ^ s * gOf s G = G := by
  ext n : 1
  rw [coeff_X_pow_mul']
  split_ifs with h
  · rw [gOf, coeff_mk, Nat.sub_add_cancel h]
  · exact (hG n (by omega)).symm

theorem eulerOp_X_pow_mul (s : ℕ) (f : PowerSeries ℚ) :
    eulerOp (X ^ s * f) = (s : PowerSeries ℚ) * (X ^ s * f) + X ^ s * eulerOp f := by
  rw [eulerOp_mul, eulerOp_X_pow]; ring

/-- The AK equation (times 24) for `g = G/q^{t+1}`. -/
theorem g_ode_of_HOde (hR : RamanujanIdentities) (t : ℕ) (H : PowerSeries ℚ) (hH : HOde t H)
    (hlow : ∀ n < t + 1, coeff n (H * Qk (12 * t + 10)) = 0) :
    let g := gOf (t + 1) (H * Qk (12 * t + 10))
    let T := (t : PowerSeries ℚ)
    144 * eulerOp (eulerOp g) + 24 * (6 * T + 6) * eulerOp g -
      ((6 * T + 6) ^ 2 - 1) * (E4s - 1) * g + 24 * (1 - E2s) * eulerOp g +
      2 * (6 * T + 7) * (1 - E2s) * g = 0 := by
  intro g T
  have h := G_ode_of_HOde hR t H hH
  simp only at h
  rw [← X_pow_mul_gOf (t + 1) _ hlow, eulerOp_X_pow_mul, eulerOp_add, eulerOp_mul, eulerOp_natCast,
    eulerOp_X_pow_mul, eulerOp_X_pow_mul] at h
  have hx : X ^ (t + 1) * (144 * eulerOp (eulerOp g) + 24 * (6 * T + 6) * eulerOp g -
      ((6 * T + 6) ^ 2 - 1) * (E4s - 1) * g + 24 * (1 - E2s) * eulerOp g +
      2 * (6 * T + 7) * (1 - E2s) * g) = X ^ (t + 1) * 0 := by
    rw [mul_zero]; push_cast at h; linear_combination h
  exact X_pow_mul_cancel (t + 1) hx

/-! ## The recurrence -/

/-- **Generic closed form.** If `H` satisfies `HOde t H`, vanishes to order `t+1` and has
`[q^{t+1}] H = c ≠ 0`, then `N ↦ [q^{N+t+1}](H·P^{-(12t+10)})/c` solves the AK recurrence at
`h = 6t + 6`. -/
theorem isAKSolution_of_HOde (hR : RamanujanIdentities) (t : ℕ) (H : PowerSeries ℚ)
    (hH : HOde t H) (hlow : ∀ n < t + 1, coeff n (H * Qk (12 * t + 10)) = 0) (c : ℚ)
    (hc : coeff (t + 1) (H * Qk (12 * t + 10)) = c) (hc0 : c ≠ 0) :
    DeligneMLDE.IsAKSolution (K := ℚ) (6 * t + 6)
      (fun N => coeff N (gOf (t + 1) (H * Qk (12 * t + 10))) / c) := by
  set g := gOf (t + 1) (H * Qk (12 * t + 10)) with hg
  have hode := g_ode_of_HOde hR t H hH hlow
  try simp only at hode
  try rw [← hg] at hode
  constructor
  · rw [hg, gOf, coeff_mk, zero_add, hc, div_self hc0]
  · intro N hN
    have h := congrArg (coeff N) hode
    rw [E4s_sub_one, one_sub_E2s] at h
    set h6 : ℚ := ((6 * t + 6 : ℕ) : ℚ) with h6def
    have e : 144 * eulerOp (eulerOp g) + 24 * (6 * (t : PowerSeries ℚ) + 6) * eulerOp g -
        ((6 * (t : PowerSeries ℚ) + 6) ^ 2 - 1) * (240 * sigS 3) * g +
        24 * (24 * sigS 1) * eulerOp g + 2 * (6 * (t : PowerSeries ℚ) + 7) * (24 * sigS 1) * g =
        PowerSeries.C (144 : ℚ) * eulerOp (eulerOp g) + PowerSeries.C (24 * h6) * eulerOp g -
          PowerSeries.C (240 * (h6 ^ 2 - 1)) * (sigS 3 * g) +
          PowerSeries.C (576 : ℚ) * (sigS 1 * eulerOp g) +
          PowerSeries.C (48 * (h6 + 1)) * (sigS 1 * g) := by
      simp only [h6def, map_mul, map_add, map_sub, map_pow, map_natCast, map_ofNat, map_one]
      push_cast; ring
    rw [e] at h
    simp only [map_add, map_sub, map_zero, coeff_C_mul, coeff_sigS_mul, D4MLDE.coeff_eulerOp] at h
    have hsum : ∑ r ∈ Finset.range N,
          (DeligneMLDE.akKernel (6 * t + 6) N (r + 1) : ℚ) * coeff (N - (r + 1)) g =
        (240 * (h6 ^ 2 - 1) *
            ∑ r ∈ Finset.range N, (sigmaK 3 (r + 1) : ℚ) * coeff (N - (r + 1)) g -
          576 * ∑ r ∈ Finset.range N, (sigmaK 1 (r + 1) : ℚ) *
            (((N - (r + 1) : ℕ) : ℚ) * coeff (N - (r + 1)) g) -
          48 * (h6 + 1) *
            ∑ r ∈ Finset.range N, (sigmaK 1 (r + 1) : ℚ) * coeff (N - (r + 1)) g) / 24 := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
        ← Finset.sum_sub_distrib, Finset.sum_div]
      refine Finset.sum_congr rfl fun r hr => ?_
      have hr' : r + 1 ≤ N := Finset.mem_range.1 hr
      simp only [DeligneMLDE.akKernel, Nat.cast_sub hr', h6def]
      ring
    simp only [Rat.cast_id]
    simp only [← mul_div_assoc]
    rw [← Finset.sum_div, hsum]
    have key : (N : ℚ) * (6 * N + h6) * coeff N g =
        (240 * (h6 ^ 2 - 1) *
            ∑ r ∈ Finset.range N, (sigmaK 3 (r + 1) : ℚ) * coeff (N - (r + 1)) g -
          576 * ∑ r ∈ Finset.range N, (sigmaK 1 (r + 1) : ℚ) *
            (((N - (r + 1) : ℕ) : ℚ) * coeff (N - (r + 1)) g) -
          48 * (h6 + 1) *
            ∑ r ∈ Finset.range N, (sigmaK 1 (r + 1) : ℚ) * coeff (N - (r + 1)) g) / 24 := by
      linear_combination h / 24
    rw [key]

/-- **Generic closed form, identified with `mldeCoeff`.** -/
theorem eq_mldeCoeff_of_HOde (t : ℕ) (H : PowerSeries ℚ)
    (hH : HOde t H) (hlow : ∀ n < t + 1, coeff n (H * Qk (12 * t + 10)) = 0) (c : ℚ)
    (hc : coeff (t + 1) (H * Qk (12 * t + 10)) = c) (hc0 : c ≠ 0) (N : ℕ) :
    coeff (N + (t + 1)) (H * Qk (12 * t + 10)) / c = mldeCoeff (6 * t + 6) N := by
  have := DeligneMLDE.eq_mldeCoeff_of_isAKSolution
    (isAKSolution_of_HOde ramanujanIdentities t H hH hlow c hc hc0) N
  simpa [gOf] using this

/-! ## Low coefficients of `H·P⁻ᵏ` from those of `H` -/

theorem coeff_mul_Qk_low (s k : ℕ) (H : PowerSeries ℚ) (hH : ∀ n < s, coeff n H = 0) :
    (∀ n < s, coeff n (H * Qk k) = 0) ∧ coeff s (H * Qk k) = coeff s H := by
  obtain ⟨H', rfl⟩ : X ^ s ∣ H := by
    rw [X_pow_dvd_iff]; exact hH
  refine ⟨fun n hn => ?_, ?_⟩
  · rw [mul_assoc, coeff_X_pow_mul', if_neg (by omega)]
  · rw [mul_assoc, coeff_X_pow_mul', if_pos le_rfl, coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
      coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply, map_mul,
      ← coeff_zero_eq_constantCoeff_apply (Qk k), coeff_zero_Qk, mul_one]

/-! ## Finite coefficient bookkeeping (`Agrees`) -/

/-- `f` agrees with the integer list `l` in its first `l.length` coefficients. -/
def Agrees (f : PowerSeries ℚ) (l : List ℤ) : Prop :=
  ∀ i < l.length, coeff i f = ((l.getD i 0 : ℤ) : ℚ)

/-- Truncated convolution of integer lists (length of the first argument). -/
def lmul (l m : List ℤ) : List ℤ :=
  (List.range l.length).map fun i => ∑ j ∈ Finset.range (i + 1), l.getD j 0 * m.getD (i - j) 0

theorem getD_lmul (l m : List ℤ) (i : ℕ) (hi : i < l.length) :
    (lmul l m).getD i 0 = ∑ j ∈ Finset.range (i + 1), l.getD j 0 * m.getD (i - j) 0 := by
  rw [lmul, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
  rfl

theorem Agrees.mul {f g : PowerSeries ℚ} {l m : List ℤ} (hf : Agrees f l) (hg : Agrees g m)
    (hlm : l.length = m.length) : Agrees (f * g) (lmul l m) := by
  intro i hi
  have hi' : i < l.length := by simpa [lmul] using hi
  rw [getD_lmul l m i hi', coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun a b => coeff a f * coeff b g)]
  push_cast
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j ≤ i := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  rw [hf j (by omega), hg (i - j) (by omega)]

theorem Agrees.add {f g : PowerSeries ℚ} {l m : List ℤ} (hf : Agrees f l) (hg : Agrees g m)
    (hlm : l.length = m.length) : Agrees (f + g) (List.zipWith (· + ·) l m) := by
  intro i hi
  simp only [List.length_zipWith] at hi
  have h1 : i < l.length := by omega
  have h2 : i < m.length := by omega
  rw [map_add, hf i h1, hg i h2]
  simp [List.getD_eq_getElem?_getD, List.getElem?_zipWith, List.getElem?_eq_getElem h1,
    List.getElem?_eq_getElem h2]

theorem Agrees.sub {f g : PowerSeries ℚ} {l m : List ℤ} (hf : Agrees f l) (hg : Agrees g m)
    (hlm : l.length = m.length) : Agrees (f - g) (List.zipWith (· - ·) l m) := by
  intro i hi
  simp only [List.length_zipWith] at hi
  have h1 : i < l.length := by omega
  have h2 : i < m.length := by omega
  rw [map_sub, hf i h1, hg i h2]
  simp [List.getD_eq_getElem?_getD, List.getElem?_zipWith, List.getElem?_eq_getElem h1,
    List.getElem?_eq_getElem h2]

theorem Agrees.ofNat_mul (n : ℕ) [n.AtLeastTwo] {f : PowerSeries ℚ} {l : List ℤ} (hf : Agrees f l) :
    Agrees ((OfNat.ofNat n : PowerSeries ℚ) * f) (l.map ((n : ℤ) * ·)) := by
  intro i hi
  simp only [List.length_map] at hi
  rw [coeff_ofNat_mul, hf i hi]
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi]

theorem Agrees.congr {f : PowerSeries ℚ} {l l' : List ℤ} (hf : Agrees f l) (h : l = l') :
    Agrees f l' := h ▸ hf

theorem coeff_sigS (k n : ℕ) : coeff n (sigS k) = if n = 0 then 0 else (sigmaK k n : ℚ) := by
  simp [sigS]

/-- Generic Eisenstein agreement: `[qⁿ](1 + a·sigS k) = 1` or `a·σ_k(n)`. -/
theorem agrees_eis (a : ℤ) (k : ℕ) (L : ℕ) :
    Agrees (1 + (a : PowerSeries ℚ) * sigS k)
      ((List.range L).map fun n => if n = 0 then 1 else a * (sigmaK k n : ℤ)) := by
  intro i hi
  simp only [List.length_map, List.length_range] at hi
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi, map_add,
    ← map_intCast (PowerSeries.C (R := ℚ)) a, coeff_C_mul, coeff_sigS, coeff_one]
  rcases i with _ | i <;> simp

theorem E2s_eq : E2s = 1 + ((-24 : ℤ) : PowerSeries ℚ) * sigS 1 := by rw [E2s]; push_cast; ring
theorem E4s_eq : E4s = 1 + ((240 : ℤ) : PowerSeries ℚ) * sigS 3 := by rw [E4s]; push_cast; ring
theorem E6s_eq : E6s = 1 + ((-504 : ℤ) : PowerSeries ℚ) * sigS 5 := by rw [E6s]; push_cast; ring

theorem agrees_E2s (L : ℕ) :
    Agrees E2s ((List.range L).map fun n => if n = 0 then 1 else -24 * (sigmaK 1 n : ℤ)) := by
  rw [E2s_eq]; exact agrees_eis _ _ _
theorem agrees_E4s (L : ℕ) :
    Agrees E4s ((List.range L).map fun n => if n = 0 then 1 else 240 * (sigmaK 3 n : ℤ)) := by
  rw [E4s_eq]; exact agrees_eis _ _ _
theorem agrees_E6s (L : ℕ) :
    Agrees E6s ((List.range L).map fun n => if n = 0 then 1 else -504 * (sigmaK 5 n : ℤ)) := by
  rw [E6s_eq]; exact agrees_eis _ _ _

example : Agrees E4s [1, 240, 2160, 6720] :=
  (agrees_E4s 4).congr (by decide)

example : Agrees (E4s * E4s) [1, 480, 61920, 1050240] := by
  have h4 : Agrees E4s [1, 240, 2160, 6720] := (agrees_E4s 4).congr (by decide)
  exact (h4.mul h4 rfl).congr (by decide)

end

end VOA.DeligneAudit.DeligneCharacter.MLDEClosed
