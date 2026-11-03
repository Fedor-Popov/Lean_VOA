/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneMLDERamanujanAdapters

/-!
# Closed form of the E₆ MLDE solution (`h∨ = 12`, `L_{-3}(E₆)`)

With `H = 7E₆² + 5E₄³ - 12E₂E₄E₆` (weight 12, depth 1) and `P = ∏(1 - qⁿ)`:

  `∑_N mldeCoeff 12 N · q^{N+2} = H · P⁻²² / 3991680`,

i.e. `η²² · ch L_{-3}(E₆) = (∑ nσ₉(n)qⁿ - Δ)/1050` (checked numerically through `q³⁰`).

* `H_ode`: `12θ²H - 24E₂θH + 11(E₂² - E₄)H = 0` from Ramanujan's identities (integer certificate);
* `G_ode`, `g_ode`: the AK equation at `h = 12` for `G = H·P⁻²²` and `g = G/q²`;
* **`e6Target_eq_mldeCoeff`**: `[q^{N+2}](H·P⁻²²)/3991680 = mldeCoeff 12 N`, unconditionally
  (Ramanujan's identities are the `D4MLDE.ramanujanIdentities`).
-/

namespace VOA.DeligneAudit.DeligneCharacter.E6MLDE

open PowerSeries VOA.QSeries VOA.QSeries.JTP VOA.DeligneAudit.DeligneCharacter.D4MLDE

noncomputable section

/-- `H = 7E₆² + 5E₄³ - 12E₂E₄E₆`. -/
def H6 : PowerSeries ℚ := 7 * E6s ^ 2 + 5 * E4s ^ 3 - 12 * E2s * E4s * E6s

theorem eulerOp_ofNat (n : ℕ) [n.AtLeastTwo] : eulerOp (OfNat.ofNat n : PowerSeries ℚ) = 0 := by
  rw [← map_ofNat (PowerSeries.C (R := ℚ)) n, show (PowerSeries.C (OfNat.ofNat n : ℚ)) =
    PowerSeries.C (OfNat.ofNat n : ℚ) * 1 by rw [mul_one], eulerOp_C_mul, eulerOp_one, mul_zero]

/-- **The weight-12 equation for `H`.** -/
theorem H_ode (hR : RamanujanIdentities) :
    12 * eulerOp (eulerOp H6) - 24 * E2s * eulerOp H6 + 11 * (E2s ^ 2 - E4s) * H6 = 0 := by
  set A := E2s
  set B := E4s
  set C := E6s
  set a := eulerOp A with ha
  set b := eulerOp B with hb
  set c := eulerOp C with hc
  set aa := eulerOp a with haa
  set bb := eulerOp b with hbb
  set cc := eulerOp c with hcc
  have n7 : eulerOp (7 : PowerSeries ℚ) = 0 := eulerOp_ofNat 7
  have n5 : eulerOp (5 : PowerSeries ℚ) = 0 := eulerOp_ofNat 5
  have n12 : eulerOp (12 : PowerSeries ℚ) = 0 := eulerOp_ofNat 12
  have h2 : 12 * a = A ^ 2 - B := hR.e2
  have h4 : 3 * b = A * B - C := hR.e4
  have h6 : 2 * c = A * C - B ^ 2 := hR.e6
  have h2d : 12 * aa = 2 * A * a - b := by
    have := congrArg eulerOp h2
    rwa [eulerOp_ofNat_mul, eulerOp_sub, eulerOp_sq] at this
  have h4d : 3 * bb = a * B + A * b - c := by
    have := congrArg eulerOp h4
    rwa [eulerOp_ofNat_mul, eulerOp_sub, eulerOp_mul] at this
  have h6d : 2 * cc = a * C + A * c - 2 * B * b := by
    have := congrArg eulerOp h6
    rwa [eulerOp_ofNat_mul, eulerOp_sub, eulerOp_mul, eulerOp_sq] at this
  have eH0 : H6 = 7 * (C * C) + 5 * (B * B * B) - 12 * (A * B * C) := by rw [H6]; ring
  have eH : eulerOp H6 = 7 * (c * C + C * c) + 5 * ((b * B + B * b) * B + B * B * b) -
      12 * ((a * B + A * b) * C + A * B * c) := by
    rw [eH0]
    simp only [eulerOp_add, eulerOp_sub, eulerOp_mul, n7, n5, n12, zero_mul, zero_add]
    rw [← ha, ← hb, ← hc]
  have eHH : eulerOp (eulerOp H6) = 7 * (cc * C + c * c + (c * c + C * cc)) +
      5 * (((bb * B + b * b + (b * b + B * bb)) * B + (b * B + B * b) * b) +
        ((b * B + B * b) * b + B * B * bb)) -
      12 * (((aa * B + a * b + (a * b + A * bb)) * C + (a * B + A * b) * c) +
        ((a * B + A * b) * c + A * B * cc)) := by
    rw [eH]
    simp only [eulerOp_add, eulerOp_sub, eulerOp_mul, n7, n5, n12, zero_mul, zero_add]
    rw [← ha, ← hb, ← hc, ← haa, ← hbb, ← hcc]
  rw [eHH, eH, H6]
  linear_combination (-12 * B * C) * h2d + (60 * B ^ 2 - 48 * A * C) * h4d + (84 * C - 72 * A * B) * h6d +
    (-24 * C * b - 24 * B * c + 12 * A * B * C + 5 * B ^ 3 + 7 * C ^ 2) * h2 +
    (120 * B * b - 96 * A * c - 12 * A * B ^ 2 + 72 * A ^ 2 * C - 84 * B * C) * h4 +
    (84 * c - 12 * A * C + 48 * A ^ 2 * B - 60 * B ^ 2) * h6

/-- `P⁻²²`. -/
def Q22 : PowerSeries ℚ := reciprocalEuler ^ 22

theorem euler_pow_mul_Q22 : (euler : PowerSeries ℚ) ^ 22 * Q22 = 1 := by
  rw [Q22, ← mul_pow, euler_mul_reciprocal, one_pow]

theorem eulerOp_Q22 : 24 * eulerOp Q22 = 22 * Q22 * (1 - E2s) := by
  have h0 := congrArg eulerOp euler_pow_mul_Q22
  rw [eulerOp_one, eulerOp_mul, show (22 : ℕ) = 21 + 1 from rfl, eulerOp_pow_succ, eulerOp_euler] at h0
  have hu : IsUnit ((euler : PowerSeries ℚ) ^ 22) := isUnit_euler.pow 22
  apply hu.mul_left_cancel
  rw [E2s]
  have e22 : (euler : PowerSeries ℚ) ^ 22 = euler ^ 21 * euler := by ring
  rw [e22]
  push_cast at h0
  linear_combination 24 * h0 + 0 * euler_pow_mul_Q22

/-- `G = H·P⁻²²`. -/
def G6 : PowerSeries ℚ := H6 * Q22

theorem G_ode (hR : RamanujanIdentities) :
    144 * eulerOp (eulerOp G6) - 288 * eulerOp G6 - 143 * (E4s - 1) * G6 +
      24 * (1 - E2s) * eulerOp G6 - 22 * (1 - E2s) * G6 = 0 := by
  set H := H6
  set A := E2s
  set B := E4s
  set Q := Q22
  set tH := eulerOp H
  set ttH := eulerOp tH
  set tQ := eulerOp Q
  set ttQ := eulerOp tQ
  set a := eulerOp A
  have hode : 12 * ttH - 24 * A * tH + 11 * (A ^ 2 - B) * H = 0 := H_ode hR
  have h2 : 12 * a = A ^ 2 - B := hR.e2
  have hq : 24 * tQ = 22 * Q * (1 - A) := eulerOp_Q22
  have hqd : 24 * ttQ = 22 * tQ * (1 - A) - 22 * Q * a := by
    have := congrArg eulerOp hq
    rw [eulerOp_ofNat_mul, eulerOp_mul, eulerOp_ofNat_mul, eulerOp_sub, eulerOp_one] at this
    linear_combination this
  have hG : eulerOp (H * Q) = tH * Q + H * tQ := eulerOp_mul _ _
  have hGG : eulerOp (eulerOp (H * Q)) = ttH * Q + 2 * tH * tQ + H * ttQ := by
    rw [hG, eulerOp_add, eulerOp_mul, eulerOp_mul]; ring
  rw [G6, hGG, hG]
  have key : (2 : PowerSeries ℚ) * (144 * (ttH * Q + 2 * tH * tQ + H * ttQ) - 288 * (tH * Q + H * tQ) -
      143 * (B - 1) * (H * Q) + 24 * (1 - A) * (tH * Q + H * tQ) - 22 * (1 - A) * (H * Q)) = 0 := by
    linear_combination (24 * Q) * hode + (12 * H) * hqd + (24 * tH - 11 * H - 13 * H * A) * hq +
      (-22 * H * Q) * h2
  have h2ne : (2 : PowerSeries ℚ) ≠ 0 := by
    intro h
    have := congrArg PowerSeries.constantCoeff h
    rw [map_ofNat, map_zero] at this
    norm_num at this
  exact (mul_eq_zero.mp key).resolve_left h2ne

/-! ## Low coefficients -/

theorem coeff_E2s_012 : coeff 0 E2s = 1 ∧ coeff 1 E2s = -24 ∧ coeff 2 E2s = -72 := by
  have hd : Nat.divisors 2 = {1, 2} := by decide
  refine ⟨?_, ?_, ?_⟩ <;> simp [E2s, sigS, coeff_one, sigmaK, hd] <;> norm_num

theorem coeff_E4s_012 : coeff 0 E4s = 1 ∧ coeff 1 E4s = 240 ∧ coeff 2 E4s = 2160 := by
  have hd : Nat.divisors 2 = {1, 2} := by decide
  refine ⟨?_, ?_, ?_⟩ <;> simp [E4s, sigS, coeff_one, sigmaK, hd] <;> norm_num

theorem coeff_E6s_012 : coeff 0 E6s = 1 ∧ coeff 1 E6s = -504 ∧ coeff 2 E6s = -16632 := by
  have hd : Nat.divisors 2 = {1, 2} := by decide
  refine ⟨?_, ?_, ?_⟩ <;> simp [E6s, sigS, coeff_one, sigmaK, hd] <;> norm_num

theorem coeff_mul_012 (f g : PowerSeries ℚ) :
    coeff 0 (f * g) = coeff 0 f * coeff 0 g ∧
    coeff 1 (f * g) = coeff 0 f * coeff 1 g + coeff 1 f * coeff 0 g ∧
    coeff 2 (f * g) = coeff 0 f * coeff 2 g + coeff 1 f * coeff 1 g + coeff 2 f * coeff 0 g := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [coeff_mul, Finset.Nat.antidiagonal_succ] <;> ring

theorem coeff_H6_012 : coeff 0 H6 = 0 ∧ coeff 1 H6 = 0 ∧ coeff 2 H6 = 3991680 := by
  obtain ⟨a0, a1, a2⟩ := coeff_E2s_012
  obtain ⟨b0, b1, b2⟩ := coeff_E4s_012
  obtain ⟨c0, c1, c2⟩ := coeff_E6s_012
  have eH : H6 = PowerSeries.C (7 : ℚ) * (E6s * E6s) + PowerSeries.C (5 : ℚ) * (E4s * (E4s * E4s)) -
      PowerSeries.C (12 : ℚ) * (E2s * (E4s * E6s)) := by
    rw [H6, map_ofNat, map_ofNat, map_ofNat]; ring
  rw [eH]
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul]
  obtain ⟨m0, m1, m2⟩ := coeff_mul_012 E6s E6s
  obtain ⟨n0, n1, n2⟩ := coeff_mul_012 E4s E4s
  obtain ⟨o0, o1, o2⟩ := coeff_mul_012 E4s (E4s * E4s)
  obtain ⟨p0, p1, p2⟩ := coeff_mul_012 E4s E6s
  obtain ⟨r0, r1, r2⟩ := coeff_mul_012 E2s (E4s * E6s)
  rw [m0, m1, m2, o0, o1, o2, n0, n1, n2, r0, r1, r2, p0, p1, p2, a0, a1, a2, b0, b1, b2, c0, c1, c2]
  norm_num

theorem coeff_zero_Q22 : coeff 0 Q22 = 1 := by
  rw [coeff_zero_eq_constantCoeff_apply, Q22, map_pow]
  have : constantCoeff (reciprocalEuler : PowerSeries ℚ) = 1 := by
    have h := congrArg constantCoeff (euler_mul_reciprocal (R := ℚ))
    rwa [map_mul, map_one, constantCoeff_euler, one_mul] at h
  rw [this, one_pow]

theorem coeff_G6_012 : coeff 0 G6 = 0 ∧ coeff 1 G6 = 0 ∧ coeff 2 G6 = 3991680 := by
  obtain ⟨h0, h1, h2⟩ := coeff_H6_012
  obtain ⟨m0, m1, m2⟩ := coeff_mul_012 H6 Q22
  rw [G6, m0, m1, m2, h0, h1, h2, coeff_zero_Q22]
  norm_num

/-! ## The equation for `g = G/q²` -/

/-- `g = G/q²`. -/
def g6 : PowerSeries ℚ := PowerSeries.mk fun N => coeff (N + 2) G6

theorem X_sq_mul_g6 : X ^ 2 * g6 = G6 := by
  ext n : 1
  rw [coeff_X_pow_mul']
  split_ifs with h
  · rw [g6, coeff_mk, Nat.sub_add_cancel h]
  · rcases n with _ | _ | n
    · exact coeff_G6_012.1.symm
    · exact coeff_G6_012.2.1.symm
    · omega

theorem eulerOp_X_sq_mul (f : PowerSeries ℚ) : eulerOp (X ^ 2 * f) = 2 * (X ^ 2 * f) + X ^ 2 * eulerOp f := by
  rw [eulerOp_mul, eulerOp_X_pow]; push_cast; ring

theorem g_ode (hR : RamanujanIdentities) :
    144 * eulerOp (eulerOp g6) + 288 * eulerOp g6 - 143 * (E4s - 1) * g6 +
      24 * (1 - E2s) * eulerOp g6 + 26 * (1 - E2s) * g6 = 0 := by
  have h := G_ode hR
  rw [← X_sq_mul_g6, eulerOp_X_sq_mul, eulerOp_add, eulerOp_ofNat_mul, eulerOp_X_sq_mul,
    eulerOp_X_sq_mul] at h
  have hx : X ^ 2 * (144 * eulerOp (eulerOp g6) + 288 * eulerOp g6 - 143 * (E4s - 1) * g6 +
      24 * (1 - E2s) * eulerOp g6 + 26 * (1 - E2s) * g6) = X ^ 2 * 0 := by
    rw [mul_zero]; linear_combination h
  exact X_pow_mul_cancel 2 hx

/-! ## The recurrence -/

/-- **The E₆ target**: `[q^{N+2}] H·P⁻²² / 3991680`. -/
def e6Target (N : ℕ) : ℚ := coeff N g6 / 3991680

theorem e6Target_isAKSolution (hR : RamanujanIdentities) :
    DeligneMLDE.IsAKSolution (K := ℚ) 12 e6Target := by
  constructor
  · rw [e6Target, g6, coeff_mk, coeff_G6_012.2.2]; norm_num
  · intro N hN
    have h := congrArg (coeff N) (g_ode hR)
    rw [E4s_sub_one, one_sub_E2s] at h
    rw [show 144 * eulerOp (eulerOp g6) + 288 * eulerOp g6 - 143 * (240 * sigS 3) * g6 +
          24 * (24 * sigS 1) * eulerOp g6 + 26 * (24 * sigS 1) * g6 =
        144 * eulerOp (eulerOp g6) + 288 * eulerOp g6 - 34320 * (sigS 3 * g6) +
          576 * (sigS 1 * eulerOp g6) + 624 * (sigS 1 * g6) by ring] at h
    simp only [map_add, map_sub, map_zero] at h
    rw [coeff_ofNat_mul 144, coeff_ofNat_mul 288, coeff_ofNat_mul 34320, coeff_ofNat_mul 576,
      coeff_ofNat_mul 624, coeff_sigS_mul, coeff_sigS_mul, coeff_sigS_mul, coeff_eulerOp,
      coeff_eulerOp] at h
    simp only [coeff_eulerOp, Nat.cast_ofNat] at h
    have hsum : ∑ r ∈ Finset.range N, (DeligneMLDE.akKernel 12 N (r + 1) : ℚ) * e6Target (N - (r + 1)) =
        (34320 * ∑ r ∈ Finset.range N, (sigmaK 3 (r + 1) : ℚ) * coeff (N - (r + 1)) g6 -
          576 * ∑ r ∈ Finset.range N, (sigmaK 1 (r + 1) : ℚ) *
            (((N - (r + 1) : ℕ) : ℚ) * coeff (N - (r + 1)) g6) -
          624 * ∑ r ∈ Finset.range N, (sigmaK 1 (r + 1) : ℚ) * coeff (N - (r + 1)) g6) /
            (24 * 3991680) := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
        ← Finset.sum_sub_distrib, Finset.sum_div]
      refine Finset.sum_congr rfl fun r hr => ?_
      have hr' : r + 1 ≤ N := Finset.mem_range.1 hr
      simp only [DeligneMLDE.akKernel, e6Target, Nat.cast_sub hr']
      push_cast
      ring
    simp only [Rat.cast_id]
    rw [hsum, e6Target]
    linear_combination h / (24 * 3991680)

/-- **The E₆ MLDE solution in closed form**: `mldeCoeff 12 N = [q^{N+2}] H·P⁻²²/3991680`. -/
theorem e6Target_eq_mldeCoeff (N : ℕ) : e6Target N = mldeCoeff 12 N := by
  simpa using DeligneMLDE.eq_mldeCoeff_of_isAKSolution (e6Target_isAKSolution ramanujanIdentities) N

end

end VOA.DeligneAudit.DeligneCharacter.E6MLDE

section AxiomAudit
#print axioms VOA.DeligneAudit.DeligneCharacter.E6MLDE.e6Target_eq_mldeCoeff
end AxiomAudit
