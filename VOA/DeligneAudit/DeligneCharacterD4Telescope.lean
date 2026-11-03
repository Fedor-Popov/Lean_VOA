/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import Mathlib

/-!
# The D₄ telescoping identity (paper d4, eq. (T))

In the paper's D₄ proof the constant term of `K·S` is split into a `q`-shift telescope and the
`√q`-shifted kernel.  The algebraic heart is a rational-function identity in `q, t, x` that is
*linear* in the two values `P(x)`, `P(x⁻¹)` of the hypermultiplet polynomial; here they are
independent symbols `P₁, P₂`.  With `D₊(y) = (1-ty²)(1-qty²)`:

* `S = (P₁/D₊(x) - x² P₂/D₊(x⁻¹)) / ((1-t)(1-x²))`,
* `R₁(y, P_y) = (1-q⁻¹y⁻²) P_y / ((1-t)(1-y²)D₊(y))`,
* `H(y, P_y, P_{y⁻¹}) = q⁻¹y⁻² P_y/((1-y²)D₊(y)) - y² P_{y⁻¹}/((1-y²)(1-ty⁻²)(1-qty⁻²))`,

and (T) reads `S - (R₁(x) + R₁(x⁻¹))/2 = (H(x) + H(x⁻¹))/(2(1-t))`.  It holds in any field, on the
locus where the denominators are nonzero.
-/

namespace VOA.DeligneAudit.DeligneCharacter

variable {K : Type*} [Field K]

/-- `D₊(y) = (1-ty²)(1-qty²)`. -/
def dPlus (q t y : K) : K := (1 - t * y ^ 2) * (1 - q * t * y ^ 2)

def telS (q t x P₁ P₂ : K) : K :=
  (P₁ / dPlus q t x - x ^ 2 * P₂ / dPlus q t x⁻¹) / ((1 - t) * (1 - x ^ 2))

def telR1 (q t y Py : K) : K :=
  (1 - q⁻¹ * y⁻¹ ^ 2) * Py / ((1 - t) * (1 - y ^ 2) * dPlus q t y)

def telH (q t y Py Pyi : K) : K :=
  q⁻¹ * y⁻¹ ^ 2 * Py / ((1 - y ^ 2) * dPlus q t y) -
    y ^ 2 * Pyi / ((1 - y ^ 2) * (1 - t * y⁻¹ ^ 2) * (1 - q * t * y⁻¹ ^ 2))

/-- **The telescoping identity (T)**, on the locus where every displayed factor is nonzero. -/
theorem telescope [CharZero K] (q t x P₁ P₂ : K) (hq : q ≠ 0) (hx : x ≠ 0) (ht : 1 - t ≠ 0)
    (hx2 : 1 - x ^ 2 ≠ 0) (h1 : 1 - t * x ^ 2 ≠ 0)
    (h3 : x ^ 2 - t ≠ 0) (h4 : x ^ 2 - q * t ≠ 0) :
    telS q t x P₁ P₂ - (telR1 q t x P₁ + telR1 q t x⁻¹ P₂) / 2 =
      (telH q t x P₁ P₂ + telH q t x⁻¹ P₂ P₁) / (2 * (1 - t)) := by
  have e1 : 1 - x⁻¹ ^ 2 = -(1 - x ^ 2) / x ^ 2 := by field_simp; ring
  have e2 : dPlus q t x⁻¹ = (x ^ 2 - t) * (x ^ 2 - q * t) / x ^ 4 := by
    unfold dPlus; field_simp
  have e3 : 1 - t * x⁻¹ ^ 2 = (x ^ 2 - t) / x ^ 2 := by field_simp
  have e4 : 1 - q * t * x⁻¹ ^ 2 = (x ^ 2 - q * t) / x ^ 2 := by field_simp
  have e5 : (1 : K) - q⁻¹ * x⁻¹⁻¹ ^ 2 = (q - x ^ 2) / q := by rw [inv_inv]; field_simp
  have e6 : (1 : K) - q⁻¹ * x⁻¹ ^ 2 = (q * x ^ 2 - 1) / (q * x ^ 2) := by field_simp
  have hd : dPlus q t x = (1 - t * x ^ 2) * (1 - q * t * x ^ 2) := rfl
  unfold telS telR1 telH
  rw [e1, e2, e3, e4, e5, e6, hd, inv_inv]
  field_simp
  ring

end VOA.DeligneAudit.DeligneCharacter

section AxiomAudit
#print axioms VOA.DeligneAudit.DeligneCharacter.telescope
end AxiomAudit
