/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneCharacterD4Final
import VOA.DeligneAudit.DeligneMLDE
import VOA.Commutative.FourTriangular

/-!
# The D₄ target series solves the Arakawa–Kawasetsu recurrence

Over `ℚ⟦q⟧`, with `θ = q d/dq` (`eulerOp`), put

  `E₂ = 1 - 24 ∑ σ₁(n)qⁿ`, `E₄ = 1 + 240 ∑ σ₃(n)qⁿ`, `E₆ = 1 - 504 ∑ σ₅(n)qⁿ`, `P = ∏(1-qⁿ)`,

and `G = (θE₄/240)·P⁻¹⁰ = ∑_N t_N q^{N+1}`, i.e. `t_N = [q^N] q^{-7/12}E₄′/(240η¹⁰)`.

* `eulerOp_euler`: `θP = -P·∑σ₁(n)qⁿ` (logarithmic derivative of the Euler product; proved);
* `RamanujanIdentities` (named here): `12θE₂ = E₂² - E₄`, `3θE₄ = E₂E₄ - E₆`, `2θE₆ = E₂E₆ - E₄²`.
  Proved: `D4MLDE.ramanujanIdentities` (`DeligneMLDERamanujanAdapters.lean`);
* **`d4E4Target_isAKSolution`**: `RamanujanIdentities → IsAKSolution 6 t` (proved), hence
  `d4E4Target_eq_mldeCoeff`: `t_N = mldeCoeff 6 N`;
* `D4SchurEqE4` (named here): the Schur index `d4SchurQ` equals `t` (the elliptic evaluation
  `½ CT_x Θ(x) M = q^{-7/12}E₄′/(240η¹⁰)`).  Proved: `D4Wp.d4SchurEqE4`
  (`DeligneCharacterD4Wp12.lean`);
* **`d4SchurQ_eq_mldeCoeff`**: `D4SchurEqE4 → RamanujanIdentities → d4SchurQ N = mldeCoeff 6 N`;
* `d4ClassS_of_mlde`: class S for `W` follows from `mldeCoeff 6 N ≤ dim W_N` (the AK/MLDE side).

(It was checked symbolically, outside Lean, that, given the three Ramanujan identities, the order-2 AK equation for
`G` is an identity of polynomials in `E₂, E₄, E₆`; no further relation is used.)
-/

namespace VOA.DeligneAudit.DeligneCharacter.D4MLDE

open PowerSeries VOA.QSeries VOA.QSeries.JTP

noncomputable section

/-- `∑_{n ≥ 1} σ_k(n) qⁿ`. -/
def sigS (k : ℕ) : PowerSeries ℚ := PowerSeries.mk fun n => if n = 0 then 0 else (sigmaK k n : ℚ)

def E2s : PowerSeries ℚ := 1 - 24 * sigS 1
def E4s : PowerSeries ℚ := 1 + 240 * sigS 3
def E6s : PowerSeries ℚ := 1 - 504 * sigS 5

/-- **Ramanujan's identities** (named input) as formal `q`-series identities.
Proved: `D4MLDE.ramanujanIdentities` (`DeligneMLDERamanujanAdapters.lean`). -/
structure RamanujanIdentities : Prop where
  e2 : 12 * eulerOp E2s = E2s ^ 2 - E4s
  e4 : 3 * eulerOp E4s = E2s * E4s - E6s
  e6 : 2 * eulerOp E6s = E2s * E6s - E4s ^ 2

/-! ## The logarithmic derivative of the Euler product -/

/-- `L_n = ∑_{i<n} (i+1) q^{i+1}/(1-q^{i+1})`. -/
def lamb (n : ℕ) : PowerSeries ℚ :=
  ∑ i ∈ Finset.range n, PowerSeries.C ((i : ℚ) + 1) * X ^ (i + 1) * geomInvSeries (i + 1)

theorem eulerOp_qFactorial (n : ℕ) :
    eulerOp (qFactorial (X : PowerSeries ℚ) n) = -(qFactorial X n * lamb n) := by
  induction n with
  | zero => simp [lamb, eulerOp_one]
  | succ n ih =>
      have hl : lamb (n + 1) = lamb n +
          PowerSeries.C ((n : ℚ) + 1) * X ^ (n + 1) * geomInvSeries (n + 1) := by
        rw [lamb, Finset.sum_range_succ, ← lamb]
      rw [qFactorial_succ, eulerOp_mul, ih, hl, eulerOp_sub, eulerOp_one, eulerOp_X_pow]
      have hg := one_sub_X_pow_mul_geomInvSeries (R := ℚ) (n + 1) (Nat.succ_pos n)
      have : ((n + 1 : ℕ) : PowerSeries ℚ) = PowerSeries.C ((n : ℚ) + 1) := by
        rw [show ((n : ℚ) + 1) = ((n + 1 : ℕ) : ℚ) by push_cast; ring, map_natCast]
      rw [this]
      linear_combination (qFactorial X n * PowerSeries.C ((n : ℚ) + 1) * X ^ (n + 1)) * hg

theorem coeff_lamb_term (i m : ℕ) :
    coeff m (PowerSeries.C ((i : ℚ) + 1) * X ^ (i + 1) * geomInvSeries (i + 1) : PowerSeries ℚ) =
      if (i + 1) ∣ m ∧ m ≠ 0 then ((i : ℚ) + 1) else 0 := by
  rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul', geomInvSeries, coeff_mk]
  by_cases h : i + 1 ≤ m
  · rw [if_pos h]
    have hd : (i + 1 ∣ m - (i + 1)) ↔ (i + 1 ∣ m) := by
      constructor
      · intro hd; have := Nat.dvd_add hd (dvd_refl (i + 1)); rwa [Nat.sub_add_cancel h] at this
      · intro hd; exact Nat.dvd_sub hd (dvd_refl _)
    by_cases hdm : i + 1 ∣ m
    · rw [if_pos (hd.mpr hdm), if_pos ⟨hdm, by omega⟩, mul_one]
    · rw [if_neg (fun h' => hdm (hd.mp h')), if_neg (fun h' => hdm h'.1), mul_zero]
  · rw [if_neg h, mul_zero, if_neg]
    rintro ⟨hdm, hm0⟩
    exact h (Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) hdm)

theorem coeff_lamb (n m : ℕ) (hm : m ≤ n) : coeff m (lamb n) = coeff m (sigS 1) := by
  rw [lamb, map_sum, sigS, coeff_mk]
  simp only [coeff_lamb_term]
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · simp
  · rw [if_neg hm0.ne', sigmaK, Nat.cast_sum]
    simp only [pow_one, hm0.ne', ne_eq, not_false_eq_true, and_true]
    rw [← Finset.sum_filter]
    refine Finset.sum_bij (fun i _ => i + 1) ?_ ?_ ?_ ?_
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_range] at hi
      exact Nat.mem_divisors.mpr ⟨hi.2, hm0.ne'⟩
    · intro i _ j _ h; dsimp only at h; omega
    · intro d hd
      have hd' := Nat.mem_divisors.mp hd
      have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd'.1 hm0
      have hdm : d ≤ m := Nat.le_of_dvd hm0 hd'.1
      refine ⟨d - 1, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_range]
        refine ⟨by omega, ?_⟩
        rw [Nat.sub_add_cancel hdpos]; exact hd'.1
      · dsimp only; omega
    · intro i _; push_cast; ring

/-- **The logarithmic derivative of the Euler product**: `θP = -P·∑σ₁(n)qⁿ`. -/
theorem eulerOp_euler : eulerOp (euler : PowerSeries ℚ) = -((euler : PowerSeries ℚ) * sigS 1) := by
  ext d
  have h1 : coeff d (eulerOp (euler : PowerSeries ℚ)) =
      coeff d (eulerOp (qFactorial (X : PowerSeries ℚ) d)) := by
    simp only [eulerOp, coeff_mk]
    rw [coeff_euler d d le_rfl]
  rw [h1, eulerOp_qFactorial, map_neg, map_neg, coeff_mul, coeff_mul]
  congr 1
  refine Finset.sum_congr rfl fun p hp => ?_
  have hp' := Finset.mem_antidiagonal.mp hp
  rw [coeff_euler p.1 d (by omega), coeff_lamb d p.2 (by omega)]

/-! ## The ODE for `G = θE₄ · P⁻¹⁰` -/

theorem eulerOp_ofNat_mul (n : ℕ) [n.AtLeastTwo] (f : PowerSeries ℚ) :
    eulerOp ((OfNat.ofNat n : PowerSeries ℚ) * f) = OfNat.ofNat n * eulerOp f := by
  rw [← map_ofNat (PowerSeries.C (R := ℚ)) n, eulerOp_C_mul]

/-- `P⁻¹⁰`. -/
def Qinv : PowerSeries ℚ := reciprocalEuler ^ 10

theorem euler_pow_mul_Qinv : (euler : PowerSeries ℚ) ^ 10 * Qinv = 1 := by
  rw [Qinv, ← mul_pow, euler_mul_reciprocal, one_pow]

theorem eulerOp_Qinv : 24 * eulerOp Qinv = 10 * Qinv * (1 - E2s) := by
  have h0 := congrArg eulerOp euler_pow_mul_Qinv
  rw [eulerOp_one, eulerOp_mul, show (10 : ℕ) = 9 + 1 from rfl, eulerOp_pow_succ, eulerOp_euler]
    at h0
  have hu : IsUnit ((euler : PowerSeries ℚ) ^ 10) := isUnit_euler.pow 10
  apply hu.mul_left_cancel
  rw [E2s]
  have e10 : (euler : PowerSeries ℚ) ^ 10 = euler ^ 9 * euler := by ring
  rw [e10]
  push_cast at h0
  linear_combination 24 * h0 + 0 * euler_pow_mul_Qinv

/-- **The AK equation for `G = θE₄ · P⁻¹⁰`** (all coefficients cleared), from Ramanujan's identities. -/
theorem G_ode (hR : RamanujanIdentities) :
    288 * eulerOp (eulerOp (eulerOp E4s * Qinv)) - 288 * eulerOp (eulerOp E4s * Qinv) -
        70 * (E4s - 1) * (eulerOp E4s * Qinv) + 48 * (1 - E2s) * eulerOp (eulerOp E4s * Qinv) -
        20 * (1 - E2s) * (eulerOp E4s * Qinv) = 0 := by
  set e2 := E2s
  set e4 := E4s
  set e6 := E6s
  set q := Qinv
  set a2 := eulerOp e2
  set a4 := eulerOp e4
  set a6 := eulerOp e6
  set b2 := eulerOp a2
  set b4 := eulerOp a4
  set b6 := eulerOp a6
  set c4 := eulerOp b4
  set dq := eulerOp q
  set ddq := eulerOp dq
  have h2 : 12 * a2 = e2 ^ 2 - e4 := hR.e2
  have h4 : 3 * a4 = e2 * e4 - e6 := hR.e4
  have h6 : 2 * a6 = e2 * e6 - e4 ^ 2 := hR.e6
  have h2d : 12 * b2 = 2 * e2 * a2 - a4 := by
    have := congrArg eulerOp h2
    rwa [eulerOp_ofNat_mul, eulerOp_sub, eulerOp_sq] at this
  have h4d : 3 * b4 = a2 * e4 + e2 * a4 - a6 := by
    have := congrArg eulerOp h4
    rwa [eulerOp_ofNat_mul, eulerOp_sub, eulerOp_mul] at this
  have h6d : 2 * b6 = a2 * e6 + e2 * a6 - 2 * e4 * a4 := by
    have := congrArg eulerOp h6
    rwa [eulerOp_ofNat_mul, eulerOp_sub, eulerOp_mul, eulerOp_sq] at this
  have h4dd : 3 * c4 = b2 * e4 + 2 * a2 * a4 + e2 * b4 - b6 := by
    have := congrArg eulerOp h4d
    rw [eulerOp_ofNat_mul, eulerOp_sub, eulerOp_add, eulerOp_mul, eulerOp_mul] at this
    linear_combination this
  have hq : 24 * dq = 10 * q * (1 - e2) := eulerOp_Qinv
  have hqd : 24 * ddq = 10 * dq * (1 - e2) - 10 * q * a2 := by
    have := congrArg eulerOp hq
    rw [eulerOp_ofNat_mul, eulerOp_mul, eulerOp_ofNat_mul, eulerOp_sub, eulerOp_one] at this
    linear_combination this
  have hDG : eulerOp (a4 * q) = b4 * q + a4 * dq := eulerOp_mul _ _
  have hDDG : eulerOp (eulerOp (a4 * q)) = c4 * q + 2 * b4 * dq + a4 * ddq := by
    rw [hDG, eulerOp_add, eulerOp_mul, eulerOp_mul]; ring
  rw [hDDG, hDG]
  linear_combination (12 * a4) * hqd + (24 * b4 - 5 * a4 - 7 * e2 * a4) * hq + (96 * q) * h4dd +
    (-64 * e2 * q) * h4d + (-48 * q) * h6d + (8 * e4 * q) * h2d + (8 * e2 * q) * h6 +
    (6 * e4 * q + 24 * a2 * q + 2 * e2 ^ 2 * q) * h4 + (-2 * e2 * e4 * q - 6 * e6 * q) * h2

/-! ## From the ODE to the recurrence -/

/-- `G = θE₄·P⁻¹⁰`. -/
def Gser : PowerSeries ℚ := eulerOp E4s * Qinv

/-- `g = G/q`. -/
def gser : PowerSeries ℚ := PowerSeries.mk fun N => coeff (N + 1) Gser

/-- **The D₄ target**: `t_N = [q^N] q^{-7/12} E₄′/(240 η¹⁰)`. -/
def d4E4Target (N : ℕ) : ℚ := coeff N gser / 240

theorem coeff_zero_Gser : coeff 0 Gser = 0 := by
  rw [Gser, coeff_mul, Finset.Nat.antidiagonal_zero, Finset.sum_singleton]
  simp [eulerOp]

theorem X_mul_gser : X * gser = Gser := by
  ext n
  rcases n with _ | n
  · rw [coeff_zero_X_mul, coeff_zero_Gser]
  · rw [coeff_succ_X_mul, gser, coeff_mk]

theorem eulerOp_X_mul (f : PowerSeries ℚ) : eulerOp (X * f) = X * f + X * eulerOp f := by
  rw [eulerOp_mul, show (X : PowerSeries ℚ) = X ^ 1 from (pow_one _).symm, eulerOp_X_pow]
  simp

theorem g_ode (hR : RamanujanIdentities) :
    288 * eulerOp (eulerOp gser) + 288 * eulerOp gser - 70 * (E4s - 1) * gser +
      48 * (1 - E2s) * eulerOp gser + 28 * (1 - E2s) * gser = 0 := by
  have h := G_ode hR
  rw [← Gser, ← X_mul_gser, eulerOp_X_mul, eulerOp_add, eulerOp_X_mul, eulerOp_X_mul] at h
  have hx : X * (288 * eulerOp (eulerOp gser) + 288 * eulerOp gser - 70 * (E4s - 1) * gser +
      48 * (1 - E2s) * eulerOp gser + 28 * (1 - E2s) * gser) = X * 0 := by
    rw [mul_zero]; linear_combination h
  exact X_pow_mul_cancel 1 (by simpa using hx)

theorem coeff_sigS_mul (k : ℕ) (f : PowerSeries ℚ) (N : ℕ) :
    coeff N (sigS k * f) = ∑ r ∈ Finset.range N, (sigmaK k (r + 1) : ℚ) * coeff (N - (r + 1)) f := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i (sigS k) * coeff j f),
    Finset.sum_range_succ']
  simp [sigS]

theorem coeff_ofNat_mul (n : ℕ) [n.AtLeastTwo] (f : PowerSeries ℚ) (N : ℕ) :
    coeff N ((OfNat.ofNat n : PowerSeries ℚ) * f) = (n : ℚ) * coeff N f := by
  rw [← map_ofNat (PowerSeries.C (R := ℚ)) n, coeff_C_mul]
  rfl

theorem coeff_eulerOp (f : PowerSeries ℚ) (N : ℕ) : coeff N (eulerOp f) = (N : ℚ) * coeff N f := by
  simp [eulerOp]

theorem E4s_sub_one : E4s - 1 = 240 * sigS 3 := by rw [E4s]; ring
theorem one_sub_E2s : 1 - E2s = 24 * sigS 1 := by rw [E2s]; ring

theorem constantCoeff_Qinv : coeff 0 Qinv = 1 := by
  rw [coeff_zero_eq_constantCoeff_apply, Qinv, map_pow]
  have : constantCoeff (reciprocalEuler : PowerSeries ℚ) = 1 := by
    have h := congrArg constantCoeff (euler_mul_reciprocal (R := ℚ))
    rwa [map_mul, map_one, constantCoeff_euler, one_mul] at h
  rw [this, one_pow]

/-- **The D₄ target solves the AK recurrence** (`h∨ = 6`), given Ramanujan's identities. -/
theorem d4E4Target_isAKSolution (hR : RamanujanIdentities) :
    DeligneMLDE.IsAKSolution (K := ℚ) 6 d4E4Target := by
  constructor
  · rw [d4E4Target, gser, coeff_mk, Gser, coeff_mul, Finset.Nat.antidiagonal_succ]
    simp [constantCoeff_Qinv, E4s, sigS]
    rw [coeff_ofNat_mul]
    simp [sigmaK]
  · intro N hN
    have h := congrArg (coeff N) (g_ode hR)
    rw [E4s_sub_one, one_sub_E2s] at h
    rw [show 288 * eulerOp (eulerOp gser) + 288 * eulerOp gser - 70 * (240 * sigS 3) * gser +
          48 * (24 * sigS 1) * eulerOp gser + 28 * (24 * sigS 1) * gser =
        288 * eulerOp (eulerOp gser) + 288 * eulerOp gser - 16800 * (sigS 3 * gser) +
          1152 * (sigS 1 * eulerOp gser) + 672 * (sigS 1 * gser) by ring] at h
    simp only [map_add, map_sub, map_zero] at h
    rw [coeff_ofNat_mul 288, coeff_ofNat_mul 288, coeff_ofNat_mul 16800, coeff_ofNat_mul 1152,
      coeff_ofNat_mul 672, coeff_sigS_mul, coeff_sigS_mul, coeff_sigS_mul, coeff_eulerOp,
      coeff_eulerOp] at h
    simp only [coeff_eulerOp, Nat.cast_ofNat] at h
    have hsum : ∑ r ∈ Finset.range N, (DeligneMLDE.akKernel 6 N (r + 1) : ℚ) * d4E4Target (N - (r + 1)) =
        (16800 * ∑ r ∈ Finset.range N, (sigmaK 3 (r + 1) : ℚ) * coeff (N - (r + 1)) gser -
          1152 * ∑ r ∈ Finset.range N, (sigmaK 1 (r + 1) : ℚ) *
            (((N - (r + 1) : ℕ) : ℚ) * coeff (N - (r + 1)) gser) -
          672 * ∑ r ∈ Finset.range N, (sigmaK 1 (r + 1) : ℚ) * coeff (N - (r + 1)) gser) / 11520 := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
        ← Finset.sum_sub_distrib, Finset.sum_div]
      refine Finset.sum_congr rfl fun r hr => ?_
      have hr' : r + 1 ≤ N := Finset.mem_range.1 hr
      simp only [DeligneMLDE.akKernel, d4E4Target, Nat.cast_sub hr']
      push_cast
      ring
    simp only [Rat.cast_id]
    rw [hsum, d4E4Target]
    linear_combination h / 11520

/-- The D₄ target equals the normalized AK solution at `h∨ = 6`. -/
theorem d4E4Target_eq_mldeCoeff (hR : RamanujanIdentities) (N : ℕ) :
    d4E4Target N = mldeCoeff 6 N := by
  simpa using DeligneMLDE.eq_mldeCoeff_of_isAKSolution (d4E4Target_isAKSolution hR) N

/-- **Named input**: the D₄ Schur index `½ CT_x Θ(x) M` equals `q^{-7/12}E₄′/(240η¹⁰)`.
Proved: `D4Wp.d4SchurEqE4` (`DeligneCharacterD4Wp12.lean`). -/
def D4SchurEqE4 : Prop := ∀ N, D4K.d4SchurQ N = d4E4Target N

/-- **The D₄ Schur index solves the AK MLDE**: `d4SchurQ N = mldeCoeff 6 N`. -/
theorem d4SchurQ_eq_mldeCoeff (hS : D4SchurEqE4) (hR : RamanujanIdentities) (N : ℕ) :
    D4K.d4SchurQ N = mldeCoeff 6 N :=
  (hS N).trans (d4E4Target_eq_mldeCoeff hR N)

/-- Class S for `W` from the MLDE-side lower bound `mldeCoeff 6 N ≤ dim W_N`. -/
theorem d4ClassS_of_mlde {V : Type*} [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) (hS : D4SchurEqE4) (hR : RamanujanIdentities)
    (hW : ∀ N : ℕ, mldeCoeff 6 N ≤ (Module.finrank ℂ (W.grading N) : ℚ)) : D4ClassS W :=
  ⟨fun N => (d4SchurQ_eq_mldeCoeff hS hR N).trans_le (hW N)⟩

/-- Finite guard: the AK coefficients at `h∨ = 6` agree with the `ℕ`-valued D₄ target. -/
theorem mldeCoeff_six_small :
    (List.range 4).map (mldeCoeff 6) = (List.range 4).map fun N => (d4TargetCoeff N : ℚ) := by
  decide +kernel

end

end VOA.DeligneAudit.DeligneCharacter.D4MLDE

section AxiomAudit
#print axioms VOA.DeligneAudit.DeligneCharacter.D4MLDE.d4E4Target_isAKSolution
#print axioms VOA.DeligneAudit.DeligneCharacter.D4MLDE.d4SchurQ_eq_mldeCoeff
#print axioms VOA.DeligneAudit.DeligneCharacter.D4MLDE.d4ClassS_of_mlde
#print axioms VOA.DeligneAudit.DeligneCharacter.D4MLDE.mldeCoeff_six_small
end AxiomAudit
