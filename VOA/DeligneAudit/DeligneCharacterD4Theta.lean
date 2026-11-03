/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import Mathlib

/-!
# The theta measure of the D₄ Schur integral, in explicit form

The D₄ kernel is `K = ½ Θ(x) M(s,x,z)` with the theta measure
`Θ(x) = (q;q)_∞ (x²;q)_∞ (x⁻²;q)_∞` and `M` a power series in `s` whose coefficients are Laurent
*polynomials* in `x` (and `z`).  The Jacobi triple product,

  `(q;q)_∞ (x²;q)_∞ (q x⁻²;q)_∞ = ∑_{k ∈ ℤ} (-1)^k q^{k(k-1)/2} x^{2k}`,

gives `Θ(x) = (1 - x⁻²) ∑_k (-1)^k q^{k(k-1)/2} x^{2k}`.  So the constant term
`CT_x Θ(x) F(x)` of a Laurent polynomial `F` is the explicit linear functional

  `thetaCT F = ∑_j F_j θ_{-j}`,  `θ_{2k} = (-1)^k (q^{k(k-1)/2} + q^{k(k+1)/2})`,  `θ_odd = 0`.

This file supplies:
* `jtpCoeff`, `thetaCoeff`, `thetaPrimeCoeff`: the explicit coefficient families of
  `∑ (-1)^k q^{C(k,2)} x^{2k}`, of `Θ`, and of `Θ' = Θ/(1-x²) = (q)(qx²)(x⁻²)`;
* `TwoVariableJTP`: the two-variable Jacobi triple product as a named statement, in the
  division-free truncated form that the `AgreeTo` calculus proves;
* `thetaCoeff_eq_jtp`, `thetaCoeff_eq_prime`: `Θ = (1-x⁻²)·JTP` and `Θ = (1-x²)Θ'`
  coefficientwise;
* `thetaCT`, `thetaCT_one`: the functional and the initial value `½ CT_x Θ = 1`.

Agreement of `thetaCoeff`, `thetaPrimeCoeff` with the literal products was checked numerically
through `q^{29}`, `|j| ≤ 10`.
-/

namespace VOA.DeligneAudit.DeligneCharacter

open PowerSeries LaurentPolynomial

noncomputable section

/-- `C(k,2) = k(k-1)/2` for an integer `k`, as a natural number. -/
def triC (k : ℤ) : ℕ := (k * (k - 1) / 2).toNat

/-- Coefficient of `x^j` in `∑_k (-1)^k q^{C(k,2)} x^{2k}`. -/
def jtpCoeff (j : ℤ) : PowerSeries ℤ :=
  if Even j then (-1) ^ (j / 2).natAbs * X ^ triC (j / 2) else 0

/-- Coefficient of `x^j` in `Θ(x) = (q)(x²)(x⁻²)`. -/
def thetaCoeff (j : ℤ) : PowerSeries ℤ := jtpCoeff j - jtpCoeff (j + 2)

/-- Coefficient of `x^j` in `Θ'(x) = (q)(qx²)(x⁻²) = ∑_k (-1)^k q^{C(k+1,2)} x^{2k}`. -/
def thetaPrimeCoeff (j : ℤ) : PowerSeries ℤ :=
  if Even j then (-1) ^ (j / 2).natAbs * X ^ triC (j / 2 + 1) else 0

theorem triC_nonneg (k : ℤ) : 0 ≤ k * (k - 1) / 2 := by
  apply Int.ediv_nonneg _ (by norm_num)
  rcases le_or_gt k 0 with h | h
  · nlinarith
  · nlinarith

/-- `C(k+1,2) = C(k,2) + k`: the exponent law behind every `q`-shift of the theta measure
(`Θ(√q x) = Θ'(x)(1 - q⁻¹x⁻²)` and `Θ'(qx) = q⁻³x⁻⁴ Θ'(x)`). -/
theorem triC_succ (k : ℤ) : (triC (k + 1) : ℤ) = triC k + k := by
  unfold triC
  rw [Int.toNat_of_nonneg (triC_nonneg (k + 1)), Int.toNat_of_nonneg (triC_nonneg k)]
  have : (k + 1) * (k + 1 - 1) = k * (k - 1) + 2 * k := by ring
  rw [this, Int.add_mul_ediv_left _ _ (by norm_num : (2 : ℤ) ≠ 0)]

/-- `Θ = (1 - x⁻²) · ∑ (-1)^k q^{C(k,2)} x^{2k}`, by definition. -/
theorem thetaCoeff_eq_jtp (j : ℤ) : thetaCoeff j = jtpCoeff j - jtpCoeff (j + 2) := rfl

theorem neg_one_pow_natAbs_add_one {R : Type*} [Ring R] (k : ℤ) :
    (-1 : R) ^ (k + 1).natAbs = -((-1 : R) ^ k.natAbs) := by
  rcases Int.even_or_odd k with hk | hk
  · have h1 : Odd (k + 1).natAbs := Int.natAbs_odd.mpr (Even.add_one hk)
    rw [h1.neg_one_pow, (Int.natAbs_even.mpr hk).neg_one_pow]
  · have h1 : Even (k + 1).natAbs := Int.natAbs_even.mpr (Odd.add_one hk)
    rw [h1.neg_one_pow, (Int.natAbs_odd.mpr hk).neg_one_pow, neg_neg]

/-- `Θ = (1 - x²) Θ'` coefficientwise. -/
theorem thetaCoeff_eq_prime (j : ℤ) :
    thetaCoeff j = thetaPrimeCoeff j - thetaPrimeCoeff (j - 2) := by
  unfold thetaCoeff jtpCoeff thetaPrimeCoeff
  rcases Int.even_or_odd j with ⟨k, rfl⟩ | hodd
  · have e1 : Even (k + k + 2) := ⟨k + 1, by ring⟩
    have e2 : Even (k + k - 2) := ⟨k - 1, by ring⟩
    have d0 : (k + k) / 2 = k := by omega
    have d1 : (k + k + 2) / 2 = k + 1 := by omega
    have d2 : (k + k - 2) / 2 = k - 1 := by omega
    rw [if_pos ⟨k, rfl⟩, if_pos e1, if_pos ⟨k, rfl⟩, if_pos e2, d0, d1, d2,
      show k - 1 + 1 = k by ring, neg_one_pow_natAbs_add_one]
    have h3 : (-1 : PowerSeries ℤ) ^ k.natAbs = -((-1) ^ (k - 1).natAbs) := by
      have := neg_one_pow_natAbs_add_one (R := PowerSeries ℤ) (k - 1)
      rwa [show k - 1 + 1 = k by ring] at this
    rw [h3]
    ring
  · have o1 : ¬ Even (j + 2) := by
      rw [Int.not_even_iff_odd]; exact hodd.add_even even_two
    have o2 : ¬ Even (j - 2) := by
      rw [Int.not_even_iff_odd]; exact hodd.sub_even even_two
    rw [if_neg (Int.not_even_iff_odd.mpr hodd), if_neg o1, if_neg (Int.not_even_iff_odd.mpr hodd),
      if_neg o2]

/-- The constant-term functional `F ↦ CT_x Θ(x) F(x)` on Laurent polynomials in `x` with
coefficients in any algebra over `ℤ⟦q⟧`. -/
def thetaCT {A : Type*} [CommRing A] [Algebra (PowerSeries ℤ) A] (F : A[T;T⁻¹]) : A :=
  F.sum fun j c => c * algebraMap (PowerSeries ℤ) A (thetaCoeff (-j))

/-- `θ₀ = 2`, i.e. `½ CT_x Θ = 1`: the initial value of the D₄ recursion. -/
theorem thetaCoeff_zero : thetaCoeff 0 = 2 := by
  simp [thetaCoeff, jtpCoeff, triC]
  norm_num

/-- The truncated two-variable triple product `∏_{i<M} (1-q^{i+1})(1-q^i x²)(1-q^{i+1}x⁻²)`. -/
def jtpTrunc (M : ℕ) : (PowerSeries ℤ)[T;T⁻¹] :=
  ∏ i ∈ Finset.range M,
    (LaurentPolynomial.C (1 - X ^ (i + 1)) * (1 - LaurentPolynomial.C (X ^ i) * T 2) *
      (1 - LaurentPolynomial.C (X ^ (i + 1)) * T (-2)))

/-- **The two-variable Jacobi triple product** (named input, proved as `VOA.QSeries.JTP.twoVariableJTP`): every
`q`-degree below the truncation order is exact. -/
structure TwoVariableJTP : Prop where
  eq : ∀ (M : ℕ) (j : ℤ) (d : ℕ), d < M → coeff d (jtpTrunc M j) = coeff d (jtpCoeff j)

end

end VOA.DeligneAudit.DeligneCharacter

section AxiomAudit
#print axioms VOA.DeligneAudit.DeligneCharacter.thetaCoeff_eq_prime
#print axioms VOA.DeligneAudit.DeligneCharacter.thetaCoeff_zero
#print axioms VOA.DeligneAudit.DeligneCharacter.triC_succ
end AxiomAudit
