/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.G2StarMLDE
import VOA.DeligneAudit.DeligneMLDERamanujanAdapters

/-!
# Borwein's cubic identity from Eisenstein relations, by ODE uniqueness

With `a = θ_{A₂}`, `b³ = (q;q)⁹/(q³;q³)³`, `c³ = 27q(q³;q³)⁹/(q;q)³`, we prove
`a³ = b³ + c³` (and hence the whole `G2Level3Core`) from Ramanujan's identities and three
**Eisenstein relations** (`G2Level3Eis`):

* `2a² = 3E₂(q³) - E₂`,
* `10a⁴ = E₄ + 9E₄(q³)`,
* `16a²(E₆ - 27E₆(q³)) + 416a⁸ - 16a⁴(G + 8a⁴) + (G + 8a⁴)² = 0`, with `G = E₄ - 9E₄(q³)`.

These three are exactly what the heat equation of the Jacobi triple product at a primitive cube
root of unity yields at orders `0` to `4` (given `a = 1 + 6 Σ χ₋₃(d) qⁿ`).

Route (no modular forms):

1. `48 a θa = 4a²E₂ + 4a⁴ + G` from the first relation and Ramanujan.
2. `d := G + 8a⁴ - 16 a c³` satisfies `48a² θd = d (d + 32a⁴ + 16a²E₂ + 16ac³)`
   (an explicit `linear_combination`), and `d ≡ 0 mod q²`; the indicial root is `1`, so `d = 0`
   (`eq_zero_of_mul_eulerOp`).
3. `ψ := b³ + c³ - a³` then satisfies `4θψ = (E₂ - a²)ψ` with `ψ(0) = 0`, so `ψ = 0`.
-/

namespace VOA.DeligneAudit.G2Star

open PowerSeries VOA.QSeries VOA.QSeries.JTP VOA.DeligneAudit.DeligneCharacter

noncomputable section

/-! ## Uniqueness for first-order `θ`-equations -/

/-- If `U θd = H d` and `d` has vanishing coefficients at every indicial root
`n U(0) = H(0)`, then `d = 0`. -/
theorem eq_zero_of_mul_eulerOp (U H d : PowerSeries ℚ) (h : U * eulerOp d = H * d)
    (hroot : ∀ n : ℕ, (n : ℚ) * constantCoeff U = constantCoeff H → coeff n d = 0) :
    d = 0 := by
  ext n
  rw [map_zero]
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hc := congrArg (coeff n) h
    rw [coeff_mul, coeff_mul] at hc
    have hL : ∑ p ∈ Finset.antidiagonal n, coeff p.1 U * coeff p.2 (eulerOp d) =
        constantCoeff U * ((n : ℚ) * coeff n d) := by
      rw [Finset.sum_eq_single (0, n)]
      · simp
      · rintro ⟨i, j⟩ hp hne
        have hp' := Finset.mem_antidiagonal.mp hp
        have hj : j < n := by
          rcases Nat.eq_zero_or_pos i with hi | hi
          · exact absurd (by simp_all) hne
          · simp only at hp'; omega
        simp [coeff_eulerOp, ih j hj]
      · intro h0; exact absurd (Finset.mem_antidiagonal.mpr (by simp)) h0
    have hR : ∑ p ∈ Finset.antidiagonal n, coeff p.1 H * coeff p.2 d =
        constantCoeff H * coeff n d := by
      rw [Finset.sum_eq_single (0, n)]
      · simp
      · rintro ⟨i, j⟩ hp hne
        have hp' := Finset.mem_antidiagonal.mp hp
        have hj : j < n := by
          rcases Nat.eq_zero_or_pos i with hi | hi
          · exact absurd (by simp_all) hne
          · simp only at hp'; omega
        simp [ih j hj]
      · intro h0; exact absurd (Finset.mem_antidiagonal.mpr (by simp)) h0
    rw [hL, hR] at hc
    by_cases hn : (n : ℚ) * constantCoeff U = constantCoeff H
    · exact hroot n hn
    · have : ((n : ℚ) * constantCoeff U - constantCoeff H) * coeff n d = 0 := by
        linear_combination hc
      exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hn)

/-! ## Low-order coefficients -/

theorem coeff_one_AQ : coeff 1 AQ = 6 := by
  rw [AQ, coeff_map, thetaA2, coeff_mk]
  have : ((Finset.Icc (-((1 : ℕ) : ℤ)) ((1 : ℕ) : ℤ) ×ˢ
      Finset.Icc (-((1 : ℕ) : ℤ)) ((1 : ℕ) : ℤ)).filter
      fun p : ℤ × ℤ => p.1 ^ 2 - p.1 * p.2 + p.2 ^ 2 = ((1 : ℕ) : ℤ)).card = 6 := by decide
  rw [this]; simp

theorem constantCoeff_reciprocalEuler_Q :
    constantCoeff (reciprocalEuler : PowerSeries ℚ) = 1 := by
  rw [reciprocalEuler, constantCoeff_invOfUnit]; simp

theorem constantCoeff_euler3Q : constantCoeff euler3Q = 1 := by
  rw [euler3Q, constantCoeff_expand, constantCoeff_euler]

theorem constantCoeff_recE3 : constantCoeff recE3 = 1 := by
  rw [recE3, constantCoeff_expand, constantCoeff_reciprocalEuler_Q]

theorem constantCoeff_BQ : constantCoeff BQ = 1 := by
  rw [BQ, map_mul, map_pow, map_pow, constantCoeff_euler, constantCoeff_recE3]; simp

theorem coeff_CQ_zero : coeff 0 CQ = 0 := by
  rw [CQ, mul_comm (27 : PowerSeries ℚ) X, mul_assoc, mul_assoc, coeff_zero_X_mul]

theorem coeff_CQ_one : coeff 1 CQ = 27 := by
  rw [CQ, mul_comm (27 : PowerSeries ℚ) X, mul_assoc, mul_assoc, coeff_succ_X_mul,
    coeff_ofNat_mul', coeff_zero_eq_constantCoeff_apply, map_mul, map_pow, map_pow,
    constantCoeff_euler3Q, constantCoeff_reciprocalEuler_Q]
  norm_num

theorem coeff_E4q_one : coeff 1 E4q = 240 := by
  rw [E4q, coeff_eisQ_succ]; simp [sigmaK]

theorem coeff_E4q3_zero : coeff 0 E4q3 = 1 := by
  rw [E4q3, coeff_zero_eq_constantCoeff_apply, constantCoeff_expand,
    ← coeff_zero_eq_constantCoeff_apply, E4q, coeff_eisQ_zero]

theorem coeff_E4q3_one : coeff 1 E4q3 = 0 := by
  rw [E4q3, coeff_expand]; simp

theorem constantCoeff_E2q : constantCoeff E2q = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply]; exact coeff_eisQ_zero 2 (-24)

theorem four_ne_zero_Q : (4 : PowerSeries ℚ) ≠ 0 := by
  intro h; have := congrArg constantCoeff h; rw [map_ofNat, map_zero] at this; norm_num at this

theorem constantCoeff_E4q : constantCoeff E4q = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, E4q, coeff_eisQ_zero]

theorem constantCoeff_E4q3 : constantCoeff E4q3 = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_E4q3_zero]

theorem constantCoeff_CQ : constantCoeff CQ = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_CQ_zero]

theorem coeff_zero_eisDefect :
    coeff 0 (E4q - 9 * E4q3 + 8 * AQ ^ 4 - 16 * AQ * CQ) = 0 := by
  rw [coeff_zero_eq_constantCoeff_apply]
  simp only [map_sub, map_add, map_mul, map_pow, map_ofNat, constantCoeff_AQ, constantCoeff_E4q,
    constantCoeff_E4q3, constantCoeff_CQ]
  norm_num

theorem coeff_one_mul (f g : PowerSeries ℚ) :
    coeff 1 (f * g) = coeff 0 f * coeff 1 g + coeff 1 f * coeff 0 g := by
  rw [coeff_mul, Finset.Nat.antidiagonal_succ]
  simp

theorem coeff_one_eisDefect :
    coeff 1 (E4q - 9 * E4q3 + 8 * AQ ^ 4 - 16 * AQ * CQ) = 0 := by
  have h0 : coeff 0 AQ = 1 := by rw [coeff_zero_eq_constantCoeff_apply, constantCoeff_AQ]
  have h2 : coeff 0 (AQ ^ 2) = 1 := by
    rw [coeff_zero_eq_constantCoeff_apply, map_pow, constantCoeff_AQ, one_pow]
  have ha2 : coeff 1 (AQ ^ 2) = 12 := by
    rw [sq, coeff_one_mul, h0, coeff_one_AQ]; norm_num
  have ha4 : coeff 1 (AQ ^ 4) = 24 := by
    rw [show AQ ^ 4 = AQ ^ 2 * AQ ^ 2 by ring, coeff_one_mul, h2, ha2]; norm_num
  have haC : coeff 1 (AQ * CQ) = 27 := by
    rw [coeff_one_mul, h0, coeff_one_AQ, coeff_CQ_one, coeff_CQ_zero]; norm_num
  simp only [map_sub, map_add, coeff_ofNat_mul', mul_assoc]
  rw [ha4, haC, coeff_E4q3_one, coeff_E4q_one]
  norm_num

/-! ## The Eisenstein relations and the cubic identity -/

/-- **Three Eisenstein relations at level 3** for `a = θ_{A₂}`. -/
structure G2Level3Eis : Prop where
  l2 : 2 * AQ ^ 2 = 3 * E2q3 - E2q
  l3 : 10 * AQ ^ 4 = E4q + 9 * E4q3
  l6 : 16 * AQ ^ 2 * (E6q - 27 * E6q3) + 416 * AQ ^ 8 -
      16 * AQ ^ 4 * (E4q - 9 * E4q3 + 8 * AQ ^ 4) + (E4q - 9 * E4q3 + 8 * AQ ^ 4) ^ 2 = 0

/-- `48 a θa = 4a²E₂ + 4a⁴ + E₄ - 9E₄(q³)`. -/
theorem eulerOp_AQ (hR : RamanujanFormal) (h2 : 2 * AQ ^ 2 = 3 * E2q3 - E2q) :
    48 * AQ * eulerOp AQ = 4 * AQ ^ 2 * E2q + 4 * AQ ^ 4 + E4q - 9 * E4q3 := by
  have hdL2 : 4 * AQ * eulerOp AQ = 3 * eulerOp E2q3 - eulerOp E2q := by
    have h := congrArg eulerOp h2
    simp only [eulerOp_ofNat_mul, eulerOp_sub, eulerOp_sq] at h
    linear_combination h
  have hR1 := hR.r1
  have hR13 := eulerOp_E2q3 hR
  linear_combination 12 * hdL2 - hR1 + 9 * hR13 + (-2 * AQ ^ 2 - E2q - 3 * E2q3) * h2

/-- **The Eisenstein difference**: `E₄ - 9E₄(q³) = -8a⁴ + 16ac³`. -/
theorem eisDiff_of_eis (hR : RamanujanFormal) (hE : G2Level3Eis) :
    E4q - 9 * E4q3 = -8 * AQ ^ 4 + 16 * AQ * CQ := by
  set a := AQ
  set C := CQ
  set e1 := E2q
  set e3 := E2q3
  set E4 := E4q
  set E43 := E4q3
  set E6 := E6q
  set E63 := E6q3
  set da := eulerOp a
  set dC := eulerOp C
  set dE4 := eulerOp E4
  set dE43 := eulerOp E43
  have hda : 48 * a * da = 4 * a ^ 2 * e1 + 4 * a ^ 4 + E4 - 9 * E43 := eulerOp_AQ hR hE.l2
  have hR2 : 3 * dE4 = e1 * E4 - E6 := hR.r2
  have hR23 : dE43 = e3 * E43 - E63 := eulerOp_E4q3 hR
  have hFC : 8 * dC = C * (9 * e3 - e1) := eulerOp_CQ
  have hL2 : 2 * a ^ 2 = 3 * e3 - e1 := hE.l2
  have hL3 : 10 * a ^ 4 = E4 + 9 * E43 := hE.l3
  have hL6 := hE.l6
  set d := E4 - 9 * E43 + 8 * a ^ 4 - 16 * a * C with hd_def
  have hdd : eulerOp d = dE4 - 9 * dE43 + 32 * a ^ 3 * da - 16 * (da * C + a * dC) := by
    have hp := eulerOp_pow_succ a 3
    push_cast at hp
    simp only [hd_def, eulerOp_sub, eulerOp_add, eulerOp_mul, eulerOp_ofNat, hp]
    ring
  have hODE : (48 * a ^ 2) * eulerOp d = (d + 32 * a ^ 4 + 16 * a ^ 2 * e1 + 16 * a * C) * d := by
    rw [hdd]
    linear_combination (16 * a ^ 2) * hR2 + (-432 * a ^ 2) * hR23 + (-96 * a ^ 3) * hFC +
      (16 * a * (-C + 2 * a ^ 3)) * hda + (-1) * hL6 + (144 * a ^ 2 * (2 * C * a + E43)) * hL2 +
      (16 * a ^ 4) * hL3
  have ha0 : constantCoeff a = 1 := constantCoeff_AQ
  have hd0 : coeff 0 d = 0 := coeff_zero_eisDefect
  have hd1 : coeff 1 d = 0 := coeff_one_eisDefect
  have hdz : d = 0 := by
    refine eq_zero_of_mul_eulerOp _ _ d hODE fun n hn => ?_
    have hE20 : constantCoeff e1 = 1 := constantCoeff_E2q
    have hC0 : constantCoeff C = 0 := by rw [← coeff_zero_eq_constantCoeff_apply, coeff_CQ_zero]
    have hd0' : constantCoeff d = 0 := by rw [← coeff_zero_eq_constantCoeff_apply, hd0]
    simp only [map_mul, map_add, map_pow, map_ofNat, ha0, hE20, hC0, hd0'] at hn
    have : (n : ℚ) = 1 := by linear_combination hn / 48
    have hn1 : n = 1 := by exact_mod_cast this
    subst hn1; exact hd1
  linear_combination hdz

/-- **Borwein's cubic identity** `a³ = b³ + c³`, from Ramanujan and the Eisenstein
relations. -/
theorem borweinCubic_of_eis (hR : RamanujanFormal) (hE : G2Level3Eis) : AQ ^ 3 = BQ + CQ := by
  have hdz := eisDiff_of_eis hR hE
  have hda := eulerOp_AQ hR hE.l2
  have hFB := eulerOp_BQ
  have hFC := eulerOp_CQ
  have hL2 := hE.l2
  set ψ := BQ + CQ - AQ ^ 3 with hψ
  have hODE : 4 * eulerOp ψ = (E2q - AQ ^ 2) * ψ := by
    have hp := eulerOp_pow_succ AQ 2
    push_cast at hp
    rw [hψ, eulerOp_sub, eulerOp_add, hp]
    have h4 : (4 : PowerSeries ℚ) * (4 * (eulerOp BQ + eulerOp CQ - ((2 + 1 : ℕ) : PowerSeries ℚ) *
        AQ ^ 2 * eulerOp AQ) - (E2q - AQ ^ 2) * (BQ + CQ - AQ ^ 3)) = 0 := by
      push_cast
      linear_combination 2 * hFB + 2 * hFC - AQ * hda - AQ * hdz + (2 * (BQ - 3 * CQ)) * hL2
    have := (mul_eq_zero.mp h4).resolve_left four_ne_zero_Q
    linear_combination this
  have hz : ψ = 0 := by
    refine eq_zero_of_mul_eulerOp 4 _ ψ hODE fun n hn => ?_
    simp only [map_sub, map_pow, map_ofNat, constantCoeff_AQ, constantCoeff_E2q] at hn
    have hn0 : n = 0 := by
      have : (n : ℚ) = 0 := by linear_combination hn / 4
      exact_mod_cast this
    subst hn0
    rw [hψ, coeff_zero_eq_constantCoeff_apply, map_sub, map_add, map_pow, constantCoeff_BQ,
      constantCoeff_AQ, ← coeff_zero_eq_constantCoeff_apply, coeff_CQ_zero]
    norm_num
  linear_combination -hz

/-- **The level-3 core from the Eisenstein relations.** -/
theorem g2Level3Core_of_eis (hR : RamanujanFormal) (hE : G2Level3Eis) : G2Level3Core :=
  ⟨borweinCubic_of_eis hR hE, hE.l2, hE.l3⟩

/-- **`G2KWEqMLDE` from Ramanujan and the Eisenstein relations.** -/
theorem g2KWEqMLDE_of_eis (hR : RamanujanFormal) (hE : G2Level3Eis) : G2KWEqMLDE :=
  g2KWEqMLDE_of_core hR (g2Level3Core_of_eis hR hE)

/-! ## The Lambert form of `a` (interface with the heat equation at `u = ω eˣ`) -/

/-- The character `χ₋₃` of `ℤ/3`: `0, 1, -1` on `k ≡ 0, 1, 2 (mod 3)`. -/
def chi3 (k : ℕ) : ℚ := if k % 3 = 1 then 1 else if k % 3 = 2 then -1 else 0

/-- `1 + 6 Σ_{n ≥ 1} (Σ_{d ∣ n} χ₋₃(d)) qⁿ`, the Lambert form of `θ_{A₂}`. -/
def lambertA2 : PowerSeries ℚ :=
  PowerSeries.mk fun n => if n = 0 then 1 else 6 * ∑ d ∈ n.divisors, chi3 d

/-- **Lorenz's formula** `θ_{A₂} = 1 + 6 Σ χ₋₃(d) qⁿ` (named here).
Proved: `G2Star.lorenzA2` (`G2StarLorenz.lean`). -/
def LorenzA2 : Prop := AQ = lambertA2

/-- **The three Eisenstein relations for the Lambert series** `a_L = lambertA2` (named; the
expected output of the heat equation at `u = ω eˣ`, orders `x⁰` to `x⁴`). -/
structure G2Level3EisLambert : Prop where
  l2 : 2 * lambertA2 ^ 2 = 3 * E2q3 - E2q
  l3 : 10 * lambertA2 ^ 4 = E4q + 9 * E4q3
  l6 : 16 * lambertA2 ^ 2 * (E6q - 27 * E6q3) + 416 * lambertA2 ^ 8 -
      16 * lambertA2 ^ 4 * (E4q - 9 * E4q3 + 8 * lambertA2 ^ 4) +
      (E4q - 9 * E4q3 + 8 * lambertA2 ^ 4) ^ 2 = 0

theorem g2Level3Eis_of_lambert (hL : LorenzA2) (hE : G2Level3EisLambert) : G2Level3Eis := by
  unfold LorenzA2 at hL
  exact ⟨hL ▸ hE.l2, hL ▸ hE.l3, hL ▸ hE.l6⟩

/-! ## With Ramanujan discharged (the `G2Star.ramanujanFormal`) -/

/-- **The level-3 core from the three Eisenstein relations alone.** -/
theorem g2Level3Core_of_eis' (hE : G2Level3Eis) : G2Level3Core :=
  g2Level3Core_of_eis ramanujanFormal hE

/-- **`G2KWEqMLDE` from the three Eisenstein relations alone.** -/
theorem g2KWEqMLDE_of_eis' (hE : G2Level3Eis) : G2KWEqMLDE :=
  g2KWEqMLDE_of_eis ramanujanFormal hE

/-- **`G2StarIdentity` from the Demazure/KW comparison and the three Eisenstein relations.** -/
theorem g2StarIdentity_of_eis (hD : G2DemazureEqKW) (hE : G2Level3Eis) : G2StarIdentity :=
  g2StarIdentity_of_reduction hD (g2KWEqMLDE_of_eis' hE)

/-- **The level-3 core from Lorenz's formula and the Lambert-form Eisenstein relations.** -/
theorem g2Level3Core_of_lambert (hL : LorenzA2) (hE : G2Level3EisLambert) : G2Level3Core :=
  g2Level3Core_of_eis' (g2Level3Eis_of_lambert hL hE)

end

end VOA.DeligneAudit.G2Star

section AxiomAudit
#print axioms VOA.DeligneAudit.G2Star.eq_zero_of_mul_eulerOp
#print axioms VOA.DeligneAudit.G2Star.eisDiff_of_eis
#print axioms VOA.DeligneAudit.G2Star.borweinCubic_of_eis
#print axioms VOA.DeligneAudit.G2Star.g2Level3Core_of_eis
#print axioms VOA.DeligneAudit.G2Star.g2KWEqMLDE_of_eis
#print axioms VOA.DeligneAudit.G2Star.g2KWEqMLDE_of_eis'
#print axioms VOA.DeligneAudit.G2Star.g2StarIdentity_of_eis
#print axioms VOA.DeligneAudit.G2Star.g2Level3Core_of_lambert
end AxiomAudit
