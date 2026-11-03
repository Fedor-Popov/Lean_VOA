/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneCharacterExceptional
import VOA.Commutative.JacobiTripleGauss

/-!
# The G₂ star identity: named reduction and closed forms of the target

`G2StarIdentity` (`DeligneCharacterExceptional`) says
`D_N = [q^N] Σ_n q^n Hilb_q D(1,nθ)/(q)_n` equals `mldeCoeff 4 N` (Arakawa–Kawasetsu recurrence).

A numerical study outside Lean (Demazure side computed from
scratch through `n = 18`, so exact through `q^18`) found two closed forms of the target:

* **Kac–Wakimoto form** (`g2KW`): `F = θ_{A₂}(q) (q³;q³)_∞⁶ / (q;q)_∞⁸`,
  `θ_{A₂} = Σ_{x,y ∈ ℤ} q^{x² - xy + y²}`;
* **CM form** (`G2CMIdentity`): `(q;q)_∞^{14} F = (1/6) Σ_{α ∈ ℤ[ω]} Re(α⁶) q^{N(α) - 1}`,
  `Re((a + bω)⁶) = (a² - 4ab + b²)(a² + 2ab - 2b²)(2a² - 2ab - b²)/2`: a lacunary Hecke theta
  series of
  weight `7` for `ℚ(√-3)`.  (Parallel to A₂: `(q;q)_∞⁸ F_{A₂} = (q²;q²)_∞⁸`, again lacunary.)

Equivalently `(q;q)_∞⁶ F = θ_{A₂}(q) · ((q³;q³)³_∞/(q;q)_∞)²`, a theta series of a rank-6 lattice
coset
(`(q³;q³)³/(q;q) = Σ_{m,n} q^{m² + mn + n² + m + n}`, Borwein).

This file states the reduction `G2StarIdentity ⟸ G2DemazureEqKW ∧ G2KWEqMLDE` and records the CM
identity as a named target-side statement.  No elementary proof of the Demazure side is known.
-/

namespace VOA.DeligneAudit.G2Star

open PowerSeries VOA.QSeries VOA.QSeries.JTP VOA.DeligneAudit.DeligneCharacter

noncomputable section

/-- `θ_{A₂}(q) = Σ_{x,y ∈ ℤ} q^{x² - xy + y²}`. -/
def thetaA2 : PowerSeries ℤ :=
  PowerSeries.mk fun N => (((Finset.Icc (-(N : ℤ)) N ×ˢ Finset.Icc (-(N : ℤ)) N).filter
    fun p : ℤ × ℤ => p.1 ^ 2 - p.1 * p.2 + p.2 ^ 2 = (N : ℤ)).card : ℤ)

/-- `(q³;q³)_∞`. -/
def euler3 : PowerSeries ℤ := expand 3 (by norm_num) euler

/-- The Kac–Wakimoto vacuum character of `L_{-5/3}(G₂)`, unflavoured:
`θ_{A₂}(q)(q³;q³)_∞⁶/(q;q)_∞⁸`. -/
def g2KW : PowerSeries ℤ := thetaA2 * euler3 ^ 6 * reciprocalEuler ^ 8

/-- `Re((a + bω)⁶)·2` as an integer polynomial. -/
def re6x2 (a b : ℤ) : ℤ := (a ^ 2 - 4 * a * b + b ^ 2) * (a ^ 2 + 2 * a * b - 2 * b ^ 2) *
  (2 * a ^ 2 - 2 * a * b - b ^ 2)

/-- The weight-7 CM form `(1/6) Σ_{α ∈ ℤ[ω]} Re(α⁶) q^{N(α)-1}` (the division is exact). -/
def g2CM : PowerSeries ℤ :=
  PowerSeries.mk fun N =>
    (∑ p ∈ (Finset.Icc (-(N : ℤ) - 1) (N + 1) ×ˢ Finset.Icc (-(N : ℤ) - 1) (N + 1)).filter
      (fun p : ℤ × ℤ => p.1 ^ 2 - p.1 * p.2 + p.2 ^ 2 = (N : ℤ) + 1), re6x2 p.1 p.2) / 12

/-- The Demazure side as a power series. -/
def g2DemazureSeries : PowerSeries ℤ :=
  PowerSeries.mk fun N => (demazureSumCoeff g2DemazureHilb N : ℤ)

/-- **Demazure = Kac–Wakimoto** (the deep half; Macdonald/Cherednik theory at `t = 0` in the
paper). -/
structure G2DemazureEqKW : Prop where
  eq : g2DemazureSeries = g2KW

/-- **Kac–Wakimoto = AK recurrence** (a modular-forms statement about the target alone). -/
structure G2KWEqMLDE : Prop where
  eq : ∀ N, ((coeff N g2KW : ℤ) : ℚ) = mldeCoeff 4 N

/-- **The CM form of the target** (target side only; a theta-function identity). -/
structure G2CMIdentity : Prop where
  eq : euler ^ 14 * g2KW = g2CM

/-- The star identity from the two named halves. -/
theorem g2StarIdentity_of_reduction (h1 : G2DemazureEqKW) (h2 : G2KWEqMLDE) : G2StarIdentity := by
  refine ⟨fun N => ?_⟩
  have h := congrArg (coeff N) h1.eq
  rw [g2DemazureSeries, PowerSeries.coeff_mk] at h
  rw [← h2.eq N, ← h]
  push_cast
  rfl

/-- Equivalent form of the deep half through the CM identity:
`(q;q)_∞^{14} · Σ_n q^n Hilb D(1,nθ)/(q)_n = (1/6) Σ_α Re(α⁶) q^{N(α)-1}`. -/
theorem g2DemazureEqKW_of_CM (hcm : G2CMIdentity) (h : euler ^ 14 * g2DemazureSeries = g2CM) :
    G2DemazureEqKW := by
  refine ⟨?_⟩
  have hu : IsUnit ((euler : PowerSeries ℤ) ^ 14) := isUnit_euler.pow 14
  exact hu.mul_left_cancel (h.trans hcm.eq.symm)

end

end VOA.DeligneAudit.G2Star

section AxiomAudit
#print axioms VOA.DeligneAudit.G2Star.g2StarIdentity_of_reduction
#print axioms VOA.DeligneAudit.G2Star.g2DemazureEqKW_of_CM
end AxiomAudit
