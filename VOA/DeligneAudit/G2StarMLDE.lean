/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.G2StarReduction
import VOA.DeligneAudit.DeligneMLDE
import VOA.Commutative.FourTriangular

/-!
# `G2KWEqMLDE` from Ramanujan's identities and level-3 Eisenstein inputs

The Kac–Wakimoto form `T = θ_{A₂}(q)(q³;q³)⁶/(q;q)⁸` of the `G₂` target solves the AK
recurrence with
`h = 4` (`g2KWEqMLDE_of_inputs`), given

* `RamanujanFormal`: `12 θE₂ = E₂² - E₄`, `3 θE₄ = E₂E₄ - E₆` (level one; proved:
  `G2Star.ramanujanFormal` in `DeligneMLDERamanujanAdapters.lean`), and
* `G2Level3Inputs` (Ramanujan's theory of signature 3, with `a = θ_{A₂}`,
  `c³ = 27q(q³;q³)⁹/(q;q)³`):
  `2a² = 3E₂(q³) - E₂(q)`, `E₄ = a⁴ + 8ac³`, `9E₄(q³) = 9a⁴ - 8ac³`, `E₆ = a⁶ - 20a³c³ - 8c⁶`,
  `27E₆(q³) = 27a⁶ - 36a³c³ + 8c⁶`.

Route: `θ log(q^{5/12}T) = θ log a + (3/4)E₂(q³) - (1/3)E₂(q)` (product log-derivative, proved
here),
the MLDE `(θ - E₂/6)θ f = (15/144)E₄ f` for `f = q^{5/12}T` reduces to a polynomial identity
certified
by an explicit `linear_combination`, and the MLDE is equivalent coefficientwise to the AK
recurrence.
-/

namespace VOA.DeligneAudit.G2Star

open PowerSeries VOA.QSeries VOA.QSeries.JTP VOA.DeligneAudit.DeligneCharacter
open VOA.DeligneAudit.DeligneMLDE

open scoped BigOperators

noncomputable section

/-! ## Formal Eisenstein series over `ℚ` -/

/-- `1 + c Σ_{n ≥ 1} σ_{k-1}(n) qⁿ`. -/
def eisQ (k : ℕ) (c : ℚ) : PowerSeries ℚ :=
  PowerSeries.mk fun n => if n = 0 then 1 else c * sigmaK (k - 1) n

/-- `E₂`, `E₄`, `E₆`. -/
def E2q : PowerSeries ℚ := eisQ 2 (-24)
def E4q : PowerSeries ℚ := eisQ 4 240
def E6q : PowerSeries ℚ := eisQ 6 (-504)

/-- **Ramanujan's identities** (level one), as a named input.
Proved: `G2Star.ramanujanFormal` (`DeligneMLDERamanujanAdapters.lean`). -/
structure RamanujanFormal : Prop where
  r1 : 12 * eulerOp E2q = E2q ^ 2 - E4q
  r2 : 3 * eulerOp E4q = E2q * E4q - E6q

/-! ## The logarithmic derivative of the Euler product -/

/-- `Σ_{n ≥ 1} σ(n) qⁿ`. -/
def sigma1Series : PowerSeries ℚ := PowerSeries.mk fun n => if n = 0 then 0 else (sigmaK 1 n : ℚ)

theorem E2q_eq : E2q = 1 - 24 * sigma1Series := by
  rw [show (24 : PowerSeries ℚ) * sigma1Series = PowerSeries.C 24 * sigma1Series by
    rw [map_ofNat]]
  ext n
  rw [E2q, eisQ, sigma1Series, map_sub, coeff_one, coeff_C_mul, coeff_mk, coeff_mk]
  split_ifs <;> simp_all

/-- The finite Lambert sums `Σ_{m ≤ N} m qᵐ/(1 - qᵐ)`. -/
def lambertPart (N : ℕ) : PowerSeries ℚ :=
  ∑ k ∈ Finset.range N, ((k + 1 : ℕ) : PowerSeries ℚ) * (X ^ (k + 1) * geomInvSeries (k + 1))

theorem eulerOp_partialEuler (N : ℕ) :
    eulerOp (∏ k ∈ Finset.range N, (1 - X ^ (k + 1) : PowerSeries ℚ)) =
      -(∏ k ∈ Finset.range N, (1 - X ^ (k + 1) : PowerSeries ℚ)) * lambertPart N := by
  induction N with
  | zero => simp [lambertPart, eulerOp_one]
  | succ N ih =>
      have hs : lambertPart (N + 1) = lambertPart N +
          ((N + 1 : ℕ) : PowerSeries ℚ) * (X ^ (N + 1) * geomInvSeries (N + 1)) :=
        Finset.sum_range_succ _ _
      rw [Finset.prod_range_succ, eulerOp_mul, ih, eulerOp_sub, eulerOp_one, eulerOp_X_pow, hs]
      have hg := one_sub_X_pow_mul_geomInvSeries (R := ℚ) (N + 1) (Nat.succ_pos N)
      linear_combination ((∏ k ∈ Finset.range N, (1 - X ^ (k + 1) : PowerSeries ℚ)) *
        ((N + 1 : ℕ) : PowerSeries ℚ) * X ^ (N + 1)) * hg

theorem coeff_lambertPart (N d : ℕ) (hd : d ≤ N) :
    coeff d (lambertPart N) = coeff d sigma1Series := by
  rw [lambertPart, map_sum]
  have hterm : ∀ k ∈ Finset.range N,
      coeff d (((k + 1 : ℕ) : PowerSeries ℚ) * (X ^ (k + 1) * geomInvSeries (k + 1))) =
        if (k + 1) ∣ d ∧ 0 < d then ((k + 1 : ℕ) : ℚ) else 0 := by
    intro k _
    rw [← map_natCast (PowerSeries.C (R := ℚ)), coeff_C_mul, coeff_X_pow_mul', geomInvSeries]
    by_cases hkd : k + 1 ≤ d
    · rw [if_pos hkd, coeff_mk]
      have hiff : (k + 1 ∣ d - (k + 1)) ↔ ((k + 1) ∣ d ∧ 0 < d) := by
        constructor
        · intro h
          refine ⟨?_, by omega⟩
          have := Nat.dvd_add h (dvd_refl (k + 1))
          rwa [Nat.sub_add_cancel hkd] at this
        · rintro ⟨h, _⟩
          exact Nat.dvd_sub h (dvd_refl _)
      by_cases h : (k + 1) ∣ d ∧ 0 < d
      · rw [if_pos (hiff.mpr h), if_pos h, mul_one]
      · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h, mul_zero]
    · rw [if_neg hkd, mul_zero, if_neg]
      rintro ⟨h, hpos⟩
      exact hkd (Nat.le_of_dvd hpos h)
  rw [Finset.sum_congr rfl hterm, sigma1Series, coeff_mk]
  split_ifs with h0
  · subst h0; simp
  · rw [sigmaK, Nat.divisors]
    push_cast
    rw [← Finset.sum_filter]
    simp only [pow_one]
    apply Finset.sum_nbij' (fun k => k + 1) (fun m => m - 1)
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico] at hk ⊢
      exact ⟨⟨by omega, by have := Nat.le_of_dvd (by omega) hk.2.1; omega⟩, hk.2.1⟩
    · intro m hm
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico] at hm ⊢
      refine ⟨by omega, ?_, by omega⟩
      rw [Nat.sub_add_cancel (by omega)]; exact hm.2
    · intro k _; simp
    · intro m hm
      simp only [Finset.mem_filter, Finset.mem_Ico] at hm
      omega
    · intro k _; push_cast; ring

/-- **`θ (q;q)_∞ = (q;q)_∞ (E₂ - 1)/24`.** -/
theorem eulerOp_euler : 24 * eulerOp (euler : PowerSeries ℚ) = euler * (E2q - 1) := by
  apply eq_of_agreeTo
  intro N
  have hP := agreeTo_infProd (prodFactors_euler (R := ℚ)) N
  rw [← euler_eq_infProd] at hP
  have hL : AgreeTo (N + 1) (lambertPart N) sigma1Series :=
    AgreeTo.of_coeff fun d hd => coeff_lambertPart N d (by omega)
  have h1 := (hP.eulerOp.mul_left 24).trans (AgreeTo.of_eq (by rw [eulerOp_partialEuler]))
  have h2 := (hP.symm.mul hL).mul_left (-24 : PowerSeries ℚ)
  rw [E2q_eq]
  refine (h1.trans (AgreeTo.of_eq (by ring))).trans (h2.trans (AgreeTo.of_eq (by ring)))

/-! ## Operator lemmas -/

@[simp] theorem eulerOp_ofNat_mul (n : ℕ) [n.AtLeastTwo] (f : PowerSeries ℚ) :
    eulerOp ((no_index (OfNat.ofNat n : PowerSeries ℚ)) * f) = OfNat.ofNat n * eulerOp f := by
  rw [show (OfNat.ofNat n : PowerSeries ℚ) = PowerSeries.C (OfNat.ofNat n) by rw [map_ofNat],
    eulerOp_C_mul]

@[simp] theorem eulerOp_ofNat (n : ℕ) [n.AtLeastTwo] :
    eulerOp (no_index (OfNat.ofNat n : PowerSeries ℚ)) = 0 := by
  have := eulerOp_ofNat_mul n 1
  rwa [mul_one, eulerOp_one, mul_zero] at this

theorem eulerOp_expand3 (f : PowerSeries ℚ) :
    eulerOp (expand 3 (by norm_num) f) = 3 * expand 3 (by norm_num) (eulerOp f) := by
  ext n
  rw [show (3 : PowerSeries ℚ) = PowerSeries.C 3 by rw [map_ofNat], coeff_C_mul, coeff_eulerOp,
    coeff_expand, coeff_expand]
  split_ifs with h
  · obtain ⟨m, rfl⟩ := h
    rw [Nat.mul_div_cancel_left _ (by norm_num), coeff_eulerOp]
    push_cast; ring
  · simp

/-! ## The objects over `ℚ` -/

/-- `θ_{A₂}` over `ℚ`. -/
def AQ : PowerSeries ℚ := PowerSeries.map (Int.castRingHom ℚ) thetaA2

/-- `(q³;q³)_∞` over `ℚ`. -/
def euler3Q : PowerSeries ℚ := expand 3 (by norm_num) euler

/-- `(q³;q³)⁶_∞/(q;q)⁸_∞`. -/
def PQ : PowerSeries ℚ := euler3Q ^ 6 * reciprocalEuler ^ 8

/-- `c³ = 27q(q³;q³)⁹/(q;q)³`. -/
def CQ : PowerSeries ℚ := 27 * X * euler3Q ^ 9 * reciprocalEuler ^ 3

/-- `T = θ_{A₂}(q³;q³)⁶/(q;q)⁸` over `ℚ`. -/
def TQ : PowerSeries ℚ := AQ * PQ

def E2q3 : PowerSeries ℚ := expand 3 (by norm_num) E2q
def E4q3 : PowerSeries ℚ := expand 3 (by norm_num) E4q
def E6q3 : PowerSeries ℚ := expand 3 (by norm_num) E6q

/-- **The level-3 inputs** (Ramanujan's theory of signature 3), with `a = θ_{A₂}`. -/
structure G2Level3Inputs : Prop where
  b1 : 2 * AQ ^ 2 = 3 * E2q3 - E2q
  c2 : E4q = AQ ^ 4 + 8 * AQ * CQ
  c3 : 9 * E4q3 = 9 * AQ ^ 4 - 8 * AQ * CQ
  c4 : E6q = AQ ^ 6 - 20 * AQ ^ 3 * CQ - 8 * CQ ^ 2
  c5 : 27 * E6q3 = 27 * AQ ^ 6 - 36 * AQ ^ 3 * CQ + 8 * CQ ^ 2

theorem map_euler_Q : PowerSeries.map (Int.castRingHom ℚ) (euler : PowerSeries ℤ) = euler := by
  ext d
  rw [coeff_map, coeff_euler d d le_rfl, coeff_euler d d le_rfl, ← coeff_map, map_qFactorial,
    map_X]

theorem map_reciprocalEuler_Q :
    PowerSeries.map (Int.castRingHom ℚ) (reciprocalEuler : PowerSeries ℤ) = reciprocalEuler := by
  have h := congrArg (PowerSeries.map (Int.castRingHom ℚ)) (euler_mul_reciprocal (R := ℤ))
  rw [map_mul, map_euler_Q, map_one] at h
  have hu : (euler : PowerSeries ℚ) ≠ 0 := isUnit_euler.ne_zero
  exact mul_left_cancel₀ hu (h.trans (euler_mul_reciprocal (R := ℚ)).symm)

theorem map_g2KW : PowerSeries.map (Int.castRingHom ℚ) g2KW = TQ := by
  rw [g2KW, TQ, PQ, map_mul, map_mul, map_pow, map_pow, map_reciprocalEuler_Q, euler3, euler3Q,
    PowerSeries.map_expand, map_euler_Q, AQ, mul_assoc]

/-! ## Logarithmic derivatives of the products -/

theorem eulerOp_euler3Q : 8 * eulerOp euler3Q = euler3Q * (E2q3 - 1) := by
  rw [euler3Q, eulerOp_expand3, E2q3]
  have h := congrArg (expand 3 (by norm_num : 3 ≠ 0)) eulerOp_euler
  rw [map_mul, map_mul, map_sub, map_one, map_ofNat] at h
  linear_combination h

theorem eulerOp_reciprocalEuler :
    24 * eulerOp (reciprocalEuler : PowerSeries ℚ) = -reciprocalEuler * (E2q - 1) := by
  have h1 : eulerOp ((euler : PowerSeries ℚ) * reciprocalEuler) = 0 := by
    rw [euler_mul_reciprocal, eulerOp_one]
  rw [eulerOp_mul] at h1
  have hu : (euler : PowerSeries ℚ) ≠ 0 := isUnit_euler.ne_zero
  apply mul_left_cancel₀ hu
  have h2 := eulerOp_euler
  linear_combination (24 : PowerSeries ℚ) * h1 - reciprocalEuler * h2

theorem eulerOp_PQ : 12 * eulerOp PQ = PQ * (9 * E2q3 - 4 * E2q - 5) := by
  have e6 : eulerOp (euler3Q ^ 6) = 6 * euler3Q ^ 5 * eulerOp euler3Q := by
    have := eulerOp_pow_succ euler3Q 5; push_cast at this; exact this
  have e8 : eulerOp (reciprocalEuler ^ 8 : PowerSeries ℚ) =
      8 * reciprocalEuler ^ 7 * eulerOp reciprocalEuler := by
    have := eulerOp_pow_succ (reciprocalEuler : PowerSeries ℚ) 7; push_cast at this; exact this
  rw [PQ, eulerOp_mul, e6, e8]
  linear_combination (9 * euler3Q ^ 5 * reciprocalEuler ^ 8) * eulerOp_euler3Q +
    (4 * euler3Q ^ 6 * reciprocalEuler ^ 7) * eulerOp_reciprocalEuler

/-! ## The MLDE -/

/-- `144 · [(θ+α)² - (E₂/6)(θ+α) - κE₄] T` with `α = 5/12`, `κ = 15/144`. -/
def mldeExpr (T : PowerSeries ℚ) : PowerSeries ℚ :=
  144 * eulerOp (eulerOp T) + 120 * eulerOp T + 25 * T - 24 * E2q * eulerOp T - 10 * E2q * T -
    15 * E4q * T

theorem constantCoeff_AQ : constantCoeff AQ = 1 := by
  rw [AQ, ← coeff_zero_eq_constantCoeff_apply, coeff_map, thetaA2, coeff_mk]
  have : ((Finset.Icc (-((0 : ℕ) : ℤ)) ((0 : ℕ) : ℤ) ×ˢ
      Finset.Icc (-((0 : ℕ) : ℤ)) ((0 : ℕ) : ℤ)).filter
      fun p : ℤ × ℤ => p.1 ^ 2 - p.1 * p.2 + p.2 ^ 2 = ((0 : ℕ) : ℤ)).card = 1 := by decide
  rw [this]; simp

theorem isUnit_AQ : IsUnit AQ :=
  isUnit_iff_constantCoeff.mpr (by rw [constantCoeff_AQ]; exact isUnit_one)

/-- **The MLDE for the KW form**, from the named inputs. -/
theorem mldeExpr_TQ (hR : RamanujanFormal) (hL : G2Level3Inputs) : mldeExpr TQ = 0 := by
  set A := AQ
  set P := PQ
  set C := CQ
  set e1 := E2q
  set e3 := E2q3
  set E4 := E4q
  set E43 := E4q3
  set E6 := E6q
  set E63 := E6q3
  set dA := eulerOp A
  set ddA := eulerOp (eulerOp A)
  set dP := eulerOp P
  set ddP := eulerOp (eulerOp P)
  set de1 := eulerOp e1
  set de3 := eulerOp e3
  set dE4 := eulerOp E4
  set dE43 := eulerOp E43
  set dde1 := eulerOp (eulerOp e1)
  set dde3 := eulerOp (eulerOp e3)
  have h_dP : 12 * dP = P * (9 * e3 - 4 * e1 - 5) := eulerOp_PQ
  have h_ddP : 12 * ddP = dP * (9 * e3 - 4 * e1 - 5) + P * (9 * de3 - 4 * de1) := by
    have h := congrArg eulerOp h_dP
    simp only [eulerOp_mul, eulerOp_sub, eulerOp_ofNat] at h
    linear_combination h
  have h_de1 : 12 * de1 = e1 ^ 2 - E4 := hR.r1
  have h_dE4 : 3 * dE4 = e1 * E4 - E6 := hR.r2
  have h_de3 : 4 * de3 = e3 ^ 2 - E43 := by
    have h := congrArg (expand 3 (by norm_num : 3 ≠ 0)) hR.r1
    rw [map_mul, map_sub, map_pow, map_ofNat] at h
    have h3 := eulerOp_expand3 E2q
    simp only [e3, de3, E43, E2q3, E4q3] at h h3 ⊢
    linear_combination h + 4 * h3
  have h_dE43 : dE43 = e3 * E43 - E63 := by
    have h := congrArg (expand 3 (by norm_num : 3 ≠ 0)) hR.r2
    rw [map_mul, map_sub, map_mul, map_ofNat] at h
    have h3 := eulerOp_expand3 E4q
    simp only [e3, dE43, E43, E63, E2q3, E4q3, E6q3] at h h3 ⊢
    linear_combination h + h3
  have h_dde1 : 12 * dde1 = 2 * e1 * de1 - dE4 := by
    have h := congrArg eulerOp hR.r1
    simp only [eulerOp_ofNat_mul, eulerOp_sub, eulerOp_sq] at h
    linear_combination h
  have h_dde3 : 4 * dde3 = 2 * e3 * de3 - dE43 := by
    have h := congrArg eulerOp h_de3
    simp only [eulerOp_ofNat_mul, eulerOp_sub, eulerOp_sq] at h
    linear_combination h
  have hB1 : 2 * A ^ 2 = 3 * e3 - e1 := hL.b1
  have hD1 : 4 * A * dA = 3 * de3 - de1 := by
    have h := congrArg eulerOp hB1
    simp only [eulerOp_ofNat_mul, eulerOp_sub, eulerOp_sq] at h
    linear_combination h
  have hD2 : 4 * dA ^ 2 + 4 * A * ddA = 3 * dde3 - dde1 := by
    have h := congrArg eulerOp hD1
    simp only [eulerOp_sub, eulerOp_mul, eulerOp_ofNat] at h
    linear_combination h
  have hC2 : E4 = A ^ 4 + 8 * A * C := hL.c2
  have hC3 : 9 * E43 = 9 * A ^ 4 - 8 * A * C := hL.c3
  have hC4 : E6 = A ^ 6 - 20 * A ^ 3 * C - 8 * C ^ 2 := hL.c4
  have hC5 : 27 * E63 = 27 * A ^ 6 - 36 * A ^ 3 * C + 8 * C ^ 2 := hL.c5
  have hT1 : eulerOp TQ = dA * P + A * dP := by rw [TQ, eulerOp_mul]
  have hT2 : eulerOp (eulerOp TQ) = ddA * P + 2 * dA * dP + A * ddP := by
    rw [hT1, eulerOp_add, eulerOp_mul, eulerOp_mul]; ring
  have key : 16 * A ^ 3 * mldeExpr TQ = 0 := by
    rw [mldeExpr, hT2, hT1, show TQ = A * P from rfl]
    linear_combination (-96*A^4*e1 + 144*A^4*e3 + 80*A^4 + 384*A^3*dA) * h_dP +
      (192*A^4) * h_ddP +
      (-148*A^4*P - 8*A^2*P*e1 + 60*A^2*P*e3 + 48*A*P*dA + E4*P - 9*E43*P) * h_de1 +
      (1188*A^4*P - 324*A^2*P*e3 - 432*A*P*dA - 9*E4*P + 81*E43*P) * h_de3 +
      (16*A^2*P) * h_dE4 +
      (-432*A^2*P) * h_dE43 +
      (-48*A^2*P) * h_dde1 +
      (432*A^2*P) * h_dde3 +
      (-504*A^6*P + 252*A^4*P*e1 - 756*A^4*P*e3 - 2016*A^3*P*dA + 22*A^2*E4*P + 18*A^2*E43*P
        - 8*A^2*P*e1^2 + 36*A^2*P*e1*e3 + 108*A^2*P*e3^2 + 48*A*P*dA*e1 + 144*A*P*dA*e3
        + E4*P*e1 + 3*E4*P*e3 - 9*E43*P*e1 - 27*E43*P*e3) * hB1 +
      (1008*A^4*P - 720*A^2*P*e3 - 576*A*P*dA - 12*E4*P + 108*E43*P) * hD1 +
      (576*A^2*P) * hD2 +
      (-137*A^4*P - 8*A*C*P - E4*P + 18*E43*P) * hC2 +
      (-143*A^4*P + 24*A*C*P - 9*E43*P) * hC3 +
      (-16*A^2*P) * hC4 +
      (16*A^2*P) * hC5
  have hA : (16 * A ^ 3 : PowerSeries ℚ) ≠ 0 := by
    apply mul_ne_zero
    · intro h
      have := congrArg (PowerSeries.constantCoeff) h
      rw [map_ofNat, map_zero] at this
      norm_num at this
    · exact pow_ne_zero 3 isUnit_AQ.ne_zero
  exact (mul_eq_zero.mp key).resolve_left hA

/-! ## From the MLDE to the AK recurrence -/

theorem coeff_mul_split (f g : PowerSeries ℚ) (N : ℕ) :
    coeff N (f * g) = coeff 0 f * coeff N g +
      ∑ k ∈ Finset.range N, coeff (k + 1) f * coeff (N - (k + 1)) g := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i f * coeff j g),
    Finset.sum_range_succ']
  simp only [Nat.sub_zero]
  ring

@[simp] theorem coeff_ofNat_mul' (n : ℕ) [n.AtLeastTwo] (f : PowerSeries ℚ) (N : ℕ) :
    coeff N ((no_index (OfNat.ofNat n : PowerSeries ℚ)) * f) = OfNat.ofNat n * coeff N f := by
  rw [show (OfNat.ofNat n : PowerSeries ℚ) = PowerSeries.C (OfNat.ofNat n) by rw [map_ofNat],
    coeff_C_mul]

theorem coeff_eisQ_zero (k : ℕ) (c : ℚ) : coeff 0 (eisQ k c) = 1 := by simp [eisQ]

theorem coeff_eisQ_succ (k : ℕ) (c : ℚ) (n : ℕ) :
    coeff (n + 1) (eisQ k c) = c * sigmaK (k - 1) (n + 1) := by simp [eisQ]

/-- **An MLDE solution with constant term `1` solves the AK recurrence** (`h = 4`). -/
theorem isAKSolution_of_mldeExpr (T : PowerSeries ℚ) (h0 : coeff 0 T = 1)
    (hT : mldeExpr T = 0) : IsAKSolution (K := ℚ) 4 (fun N => coeff N T) := by
  refine ⟨h0, fun N hN => ?_⟩
  have h := congrArg (coeff N) hT
  rw [mldeExpr] at h
  simp only [map_add, map_sub, map_zero, coeff_ofNat_mul', mul_assoc] at h
  rw [coeff_mul_split, coeff_mul_split, coeff_mul_split] at h
  simp only [E2q, E4q, coeff_eisQ_zero, coeff_eisQ_succ, coeff_eulerOp] at h
  set t := fun j => coeff j T
  have hS1 : ∀ k ∈ Finset.range N, (((N - (k + 1) : ℕ) : ℚ)) = (N : ℚ) - ((k + 1 : ℕ) : ℚ) := by
    intro k hk
    have := Finset.mem_range.mp hk
    rw [Nat.cast_sub (by omega)]
  have hsum : (∑ r ∈ Finset.range N, (akKernel 4 N (r + 1) : ℚ) * coeff (N - (r + 1)) T) =
      ∑ k ∈ Finset.range N, (150 * (sigmaK 3 (k + 1) : ℚ) * coeff (N - (k + 1)) T -
        24 * (sigmaK 1 (k + 1) : ℚ) * ((N - (k + 1) : ℕ) : ℚ) * coeff (N - (k + 1)) T -
        10 * (sigmaK 1 (k + 1) : ℚ) * coeff (N - (k + 1)) T) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [akKernel, hS1 k hk]
    push_cast
    ring
  have e1 : (∑ k ∈ Finset.range N, -24 * (sigmaK (2 - 1) (k + 1) : ℚ) *
      (((N - (k + 1) : ℕ) : ℚ) * coeff (N - (k + 1)) T)) =
      -24 * ∑ k ∈ Finset.range N, (sigmaK 1 (k + 1) : ℚ) * ((N - (k + 1) : ℕ) : ℚ) *
        coeff (N - (k + 1)) T := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; norm_num; ring
  have e2 : (∑ k ∈ Finset.range N, -24 * (sigmaK (2 - 1) (k + 1) : ℚ) * coeff (N - (k + 1)) T) =
      -24 * ∑ k ∈ Finset.range N, (sigmaK 1 (k + 1) : ℚ) * coeff (N - (k + 1)) T := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; norm_num; ring
  have e3 : (∑ k ∈ Finset.range N, 240 * (sigmaK (4 - 1) (k + 1) : ℚ) * coeff (N - (k + 1)) T) =
      240 * ∑ k ∈ Finset.range N, (sigmaK 3 (k + 1) : ℚ) * coeff (N - (k + 1)) T := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; norm_num; ring
  rw [e1, e2, e3] at h
  have g1 : (∑ k ∈ Finset.range N, 150 * (sigmaK 3 (k + 1) : ℚ) * coeff (N - (k + 1)) T) =
      150 * ∑ k ∈ Finset.range N, (sigmaK 3 (k + 1) : ℚ) * coeff (N - (k + 1)) T := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring
  have g2 : (∑ k ∈ Finset.range N, 24 * (sigmaK 1 (k + 1) : ℚ) * ((N - (k + 1) : ℕ) : ℚ) *
      coeff (N - (k + 1)) T) = 24 * ∑ k ∈ Finset.range N, (sigmaK 1 (k + 1) : ℚ) *
        ((N - (k + 1) : ℕ) : ℚ) * coeff (N - (k + 1)) T := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring
  have g3 : (∑ k ∈ Finset.range N, 10 * (sigmaK 1 (k + 1) : ℚ) * coeff (N - (k + 1)) T) =
      10 * ∑ k ∈ Finset.range N, (sigmaK 1 (k + 1) : ℚ) * coeff (N - (k + 1)) T := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring
  simp only [Rat.cast_id]
  rw [hsum, Finset.sum_sub_distrib, Finset.sum_sub_distrib, g1, g2, g3]
  push_cast
  linear_combination (1 / 24 : ℚ) * h

theorem coeff_zero_TQ : coeff 0 TQ = 1 := by
  have hr : constantCoeff (reciprocalEuler : PowerSeries ℚ) = 1 := by
    rw [reciprocalEuler, constantCoeff_invOfUnit]; simp
  rw [coeff_zero_eq_constantCoeff_apply, TQ, PQ, map_mul, map_mul, map_pow, map_pow,
    constantCoeff_AQ, euler3Q, constantCoeff_expand, constantCoeff_euler, hr]
  simp

/-- **`G2KWEqMLDE` from Ramanujan's identities and the level-3 inputs.** -/
theorem g2KWEqMLDE_of_inputs (hR : RamanujanFormal) (hL : G2Level3Inputs) : G2KWEqMLDE :=
  ⟨fun N => by
    have h := eq_mldeCoeff_of_isAKSolution
      (isAKSolution_of_mldeExpr TQ coeff_zero_TQ (mldeExpr_TQ hR hL)) N
    simp only [Rat.cast_id] at h
    rw [← h, ← map_g2KW, coeff_map]
    rfl⟩

/-- **`G2StarIdentity` from the Demazure half, Ramanujan, and the level-3 inputs.** -/
theorem g2StarIdentity_of_inputs (hD : G2DemazureEqKW) (hR : RamanujanFormal)
    (hL : G2Level3Inputs) : G2StarIdentity :=
  g2StarIdentity_of_reduction hD (g2KWEqMLDE_of_inputs hR hL)

/-! ## The level-3 inputs from a smaller core -/

theorem eulerOp_E2q3 (hR : RamanujanFormal) : 4 * eulerOp E2q3 = E2q3 ^ 2 - E4q3 := by
  have h := congrArg (expand 3 (by norm_num : 3 ≠ 0)) hR.r1
  rw [map_mul, map_sub, map_pow, map_ofNat] at h
  have h3 := eulerOp_expand3 E2q
  simp only [E2q3, E4q3] at h3 ⊢
  linear_combination h + 4 * h3

theorem eulerOp_E4q3 (hR : RamanujanFormal) : eulerOp E4q3 = E2q3 * E4q3 - E6q3 := by
  have h := congrArg (expand 3 (by norm_num : 3 ≠ 0)) hR.r2
  rw [map_mul, map_sub, map_mul, map_ofNat] at h
  have h3 := eulerOp_expand3 E4q
  simp only [E2q3, E4q3, E6q3] at h3 ⊢
  linear_combination h + h3

/-- `1/(q³;q³)_∞`. -/
def recE3 : PowerSeries ℚ := expand 3 (by norm_num) reciprocalEuler

/-- `b³ = (q;q)⁹_∞/(q³;q³)³_∞`. -/
def BQ : PowerSeries ℚ := euler ^ 9 * recE3 ^ 3

theorem eulerOp_recE3 : 8 * eulerOp recE3 = -recE3 * (E2q3 - 1) := by
  rw [recE3, eulerOp_expand3, E2q3]
  have h := congrArg (expand 3 (by norm_num : 3 ≠ 0)) eulerOp_reciprocalEuler
  rw [map_mul, map_mul, map_sub, map_neg, map_one, map_ofNat] at h
  linear_combination h

theorem eulerOp_BQ : 8 * eulerOp BQ = 3 * BQ * (E2q - E2q3) := by
  have e9 : eulerOp ((euler : PowerSeries ℚ) ^ 9) = 9 * euler ^ 8 * eulerOp euler := by
    have := eulerOp_pow_succ (euler : PowerSeries ℚ) 8; push_cast at this; exact this
  have e3 : eulerOp (recE3 ^ 3) = 3 * recE3 ^ 2 * eulerOp recE3 := by
    have := eulerOp_pow_succ recE3 2; push_cast at this; exact this
  rw [BQ, eulerOp_mul, e9, e3]
  linear_combination (3 * euler ^ 8 * recE3 ^ 3) * eulerOp_euler +
    (3 * euler ^ 9 * recE3 ^ 2) * eulerOp_recE3

theorem eulerOp_CQ : 8 * eulerOp CQ = CQ * (9 * E2q3 - E2q) := by
  have e9 : eulerOp (euler3Q ^ 9) = 9 * euler3Q ^ 8 * eulerOp euler3Q := by
    have := eulerOp_pow_succ euler3Q 8; push_cast at this; exact this
  have e3 : eulerOp ((reciprocalEuler : PowerSeries ℚ) ^ 3) =
      3 * reciprocalEuler ^ 2 * eulerOp reciprocalEuler := by
    have := eulerOp_pow_succ (reciprocalEuler : PowerSeries ℚ) 2; push_cast at this; exact this
  have hX : eulerOp (X : PowerSeries ℚ) = X := by
    have := eulerOp_X_pow (R := ℚ) 1; simpa using this
  rw [CQ, eulerOp_mul, eulerOp_mul, eulerOp_ofNat_mul, hX, e9, e3]
  linear_combination (27 * X * reciprocalEuler ^ 3 * 9 * euler3Q ^ 8) * eulerOp_euler3Q +
    (27 * X * euler3Q ^ 9 * reciprocalEuler ^ 2) * eulerOp_reciprocalEuler

/-- **The level-3 core**: Borwein's cubic identity `a³ = b³ + c³`, `2a² = 3E₂(q³) - E₂`, and
`10a⁴ = E₄ + 9E₄(q³)`. -/
structure G2Level3Core : Prop where
  l1 : AQ ^ 3 = BQ + CQ
  l2 : 2 * AQ ^ 2 = 3 * E2q3 - E2q
  l3 : 10 * AQ ^ 4 = E4q + 9 * E4q3

theorem two_ne_zero_Q : (2 : PowerSeries ℚ) ≠ 0 := by
  intro h; have := congrArg constantCoeff h; rw [map_ofNat, map_zero] at this; norm_num at this

/-- **The five level-3 inputs from the core** (with Ramanujan). -/
theorem g2Level3Inputs_of_core (hR : RamanujanFormal) (hc : G2Level3Core) : G2Level3Inputs := by
  set a := AQ
  set B := BQ
  set C := CQ
  set e1 := E2q
  set e3 := E2q3
  set E4 := E4q
  set E43 := E4q3
  set E6 := E6q
  set E63 := E6q3
  set da := eulerOp a
  set dB := eulerOp B
  set dC := eulerOp C
  set de1 := eulerOp e1
  set de3 := eulerOp e3
  set dE4 := eulerOp E4
  set dE43 := eulerOp E43
  have hL1 : a ^ 3 = B + C := hc.l1
  have hL2 : 2 * a ^ 2 = 3 * e3 - e1 := hc.l2
  have hR1 : 12 * de1 = e1 ^ 2 - E4 := hR.r1
  have hR13 : 4 * de3 = e3 ^ 2 - E43 := eulerOp_E2q3 hR
  have hR2 : 3 * dE4 = e1 * E4 - E6 := hR.r2
  have hR23 : dE43 = e3 * E43 - E63 := eulerOp_E4q3 hR
  have hFB : 8 * dB = 3 * B * (e1 - e3) := eulerOp_BQ
  have hFC : 8 * dC = C * (9 * e3 - e1) := eulerOp_CQ
  have hdL1 : 3 * a ^ 2 * da = dB + dC := by
    have h := congrArg eulerOp hL1
    rw [eulerOp_add] at h
    have hp := eulerOp_pow_succ a 2
    push_cast at hp
    rw [hp] at h
    linear_combination h
  have hdL2 : 4 * a * da = 3 * de3 - de1 := by
    have h := congrArg eulerOp hL2
    simp only [eulerOp_ofNat_mul, eulerOp_sub, eulerOp_sq] at h
    linear_combination h
  have ha : a ≠ 0 := isUnit_AQ.ne_zero
  have hdiff : E4 - 9 * E43 = -8 * a ^ 4 + 16 * a * C := by
    have key : a * (E4 - 9 * E43 + 8 * a ^ 4 - 16 * a * C) = 0 := by
      linear_combination (a) * hR1 + (-9 * a) * hR13 + (-12 * a) * hdL2 + (16) * hdL1 +
        (2) * hFB + (2) * hFC + (-6 * e1 + 6 * e3) * hL1 +
        (-8 * C + 4 * a ^ 3 + a * e1 + 3 * a * e3) * hL2
    have := (mul_eq_zero.mp key).resolve_left ha
    linear_combination this
  have hC2 : E4 = a ^ 4 + 8 * a * C := by
    apply mul_left_cancel₀ two_ne_zero_Q
    linear_combination hdiff - hc.l3
  have hC3 : 9 * E43 = 9 * a ^ 4 - 8 * a * C := by
    apply mul_left_cancel₀ two_ne_zero_Q
    linear_combination -hdiff - hc.l3
  have hdC2 : dE4 = 4 * a ^ 3 * da + 8 * da * C + 8 * a * dC := by
    have h := congrArg eulerOp hC2
    have hp := eulerOp_pow_succ a 3
    push_cast at hp
    simp only [eulerOp_add, eulerOp_mul, eulerOp_ofNat, hp] at h
    linear_combination h
  have hdC3 : 9 * dE43 = 36 * a ^ 3 * da - 8 * da * C - 8 * a * dC := by
    have h := congrArg eulerOp hC3
    have hp := eulerOp_pow_succ a 3
    push_cast at hp
    simp only [eulerOp_sub, eulerOp_mul, eulerOp_ofNat, hp] at h
    linear_combination h
  have h2a : (2 * a ^ 2 : PowerSeries ℚ) ≠ 0 := mul_ne_zero two_ne_zero_Q (pow_ne_zero 2 ha)
  refine ⟨hL2, hC2, hC3, ?_, ?_⟩
  · apply mul_left_cancel₀ h2a
    linear_combination (6*C*e1 - 6*C*e3 + 3*a^3*e1 - 3*a^3*e3) * hL1 +
      (-16*C - 8*a^3) * hdL1 +
      (8*C^2 + 4*C*a^3 + 2*E4*a^2 - 3*a^6) * hL2 +
      (-2*C - a^3) * hFB +
      (-2*C - 7*a^3) * hFC +
      (-4*a^4 + 6*a^2*e3) * hC2 +
      (-6*a^2) * hdC2 +
      (2*a^2) * hR2
  · apply mul_left_cancel₀ h2a
    linear_combination (-6*C*e1 + 6*C*e3 + 27*a^3*e1 - 27*a^3*e3) * hL1 +
      (16*C - 72*a^3) * hdL1 +
      (-8*C^2 + 36*C*a^3 - 27*a^6) * hL2 +
      (2*C - 9*a^3) * hFB +
      (2*C - 3*a^3) * hFC +
      (6*a^2*e3) * hC3 +
      (-6*a^2) * hdC3 +
      (54*a^2) * hR23

/-- **`G2KWEqMLDE` from Ramanujan and the level-3 core.** -/
theorem g2KWEqMLDE_of_core (hR : RamanujanFormal) (hc : G2Level3Core) : G2KWEqMLDE :=
  g2KWEqMLDE_of_inputs hR (g2Level3Inputs_of_core hR hc)

end

end VOA.DeligneAudit.G2Star

section AxiomAudit
#print axioms VOA.DeligneAudit.G2Star.eulerOp_euler
#print axioms VOA.DeligneAudit.G2Star.mldeExpr_TQ
#print axioms VOA.DeligneAudit.G2Star.isAKSolution_of_mldeExpr
#print axioms VOA.DeligneAudit.G2Star.g2KWEqMLDE_of_inputs
#print axioms VOA.DeligneAudit.G2Star.g2StarIdentity_of_inputs
#print axioms VOA.DeligneAudit.G2Star.g2KWEqMLDE_of_core
end AxiomAudit
