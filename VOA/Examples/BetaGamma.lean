/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Foundations.Locality
import VOA.Foundations.Parity
import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# The `βγ` symplectic bosons — half-integer moding **without** parity

Two mutually conjugate **even** fields `β(z)`, `γ(z)` of conformal weight `1/2`, with the
canonical *commutation* relations

  `β₍ₘ₎γ₍ₙ₎ - γ₍ₙ₎β₍ₘ₎ = δ_{m+n+1,0}`,   `[β,β] = [γ,γ] = 0`.

This is the **Axis A without Axis B** corner of the super-convention test suite
(Axis A: half-integer moding; Axis B: odd parity).  The fields are half-moded — weight `1/2`, so the physicists'
modes sit in `ℤ + 1/2` — yet they are *commuting*, not anticommuting.  Locality here is
therefore at `ε = 1`, i.e. ordinary `Local`.

Together with `Examples.BCGhosts` (parity, integer weights) and `Examples.FreeFermion`
(both), this is the empirical check that the two generalizations are genuinely independent:
`βγ` is half-moded and bosonic, `bc` is integer-moded and fermionic, and neither axis was
built to presuppose the other.  It also matters for the associated-variety programme: `βγ` is
the standard first example of a quasi-lisse vertex algebra that is not lisse.

## Construction

The Fock space is the polynomial algebra on two families of variables.  `β` is created by
multiplication by an `inl` variable and annihilated by `∂/∂(inr)`; `γ` the other way round,
with a sign chosen so that the pairing comes out as `+δ`.  The cross-pairing is what makes
`β` and `γ` conjugate to each other, exactly as `b` and `c` are in `Examples.BCGhosts` — the
only difference between the two systems, at the level of modes, is commutator versus
anticommutator.

## References
* Kac, *VA for Beginners* §3.6 (`βγ`, the "symplectic bosons"); Arakawa–Kawasetsu,
  *Quasi-lisse vertex algebras and modular linear differential equations* (2018), §5.
-/

namespace VOA

namespace BetaGamma

open MvPolynomial

/-- The Fock space: polynomials in two families of variables. -/
noncomputable abbrev Fock := MvPolynomial (ℕ ⊕ ℕ) ℂ

/-- Partial derivatives commute.  Mathlib does not carry this, so it is proved here by the
standard induction on monomials. -/
theorem pderiv_comm (i j : ℕ ⊕ ℕ) (f : Fock) :
    pderiv i (pderiv j f) = pderiv j (pderiv i f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p k hp =>
      -- the only awkward terms are `pderiv` of a constant, which vanish whatever the
      -- orientation of the index comparison
      have hz : ∀ a b c : ℕ ⊕ ℕ, pderiv a (if b = c then (1 : Fock) else 0) = 0 := by
        intro a b c; by_cases h : b = c <;> simp [h]
      simp only [pderiv_mul, pderiv_X, map_add, hp, Pi.single_apply, hz, mul_zero, add_zero]
      ring

/-- Multiplication by a variable, as an endomorphism. -/
noncomputable def mulX (i : ℕ ⊕ ℕ) : Module.End ℂ Fock := LinearMap.mulLeft ℂ (X i)

/-- Differentiation with respect to a variable, as an endomorphism. -/
noncomputable def der (i : ℕ ⊕ ℕ) : Module.End ℂ Fock := (pderiv i).toLinearMap

@[simp] theorem der_apply (i : ℕ ⊕ ℕ) (f : Fock) : der i f = pderiv i f := rfl

@[simp] theorem mulX_apply (i : ℕ ⊕ ℕ) (f : Fock) : mulX i f = X i * f := rfl

/-! ## The generic commutation relations -/

theorem mulX_comm (i j : ℕ ⊕ ℕ) (f : Fock) : mulX i (mulX j f) = mulX j (mulX i f) := by
  simp only [mulX_apply, ← mul_assoc, mul_comm (X i) (X j)]

theorem der_comm (i j : ℕ ⊕ ℕ) (f : Fock) : der i (der j f) = der j (der i f) := by
  simp only [der_apply]
  exact pderiv_comm i j f

/-- **The Heisenberg relation** `[∂_i, X_j·] = δ_{ij}`. -/
theorem der_mulX_comm (i j : ℕ ⊕ ℕ) (f : Fock) :
    der i (mulX j f) - mulX j (der i f) = (if i = j then (1 : ℂ) else 0) • f := by
  simp only [der_apply, mulX_apply]
  rw [pderiv_mul, pderiv_X, add_sub_cancel_right]
  by_cases h : i = j
  · subst h; simp
  · rw [if_neg h]
    simp [Ne.symm h]

/-- When the indices differ, differentiation and multiplication simply commute. -/
theorem der_mulX_of_ne {i j : ℕ ⊕ ℕ} (h : i ≠ j) (f : Fock) :
    der i (mulX j f) = mulX j (der i f) := by
  have hc := der_mulX_comm i j f
  rw [if_neg h, zero_smul, sub_eq_zero] at hc
  exact hc

/-! ## The two fields -/

/-- `β`: created by the `inl` variables, annihilated by `∂/∂(inr)`.

⚠ **Not a field.**  As a `FormalDist`, the argument `n` is the `z`-exponent (coefficient of
`zⁿ`), not the mode index; this definition puts creation operators at every negative exponent,
so for each nonzero `x` the coefficient applied to `x` is nonzero for infinitely many
negative `n`: the series is **not lower-truncated**
(certificate `L17Cert.freeFermion_psi_not_isField`, `Notes/Textbook/certificates/L17_Checks.lean`,
for `psi`; the same indexing is used for `beta`, `gamma`).  The (anti)commutation relations below
are statements about the operator family `n ↦ beta n` and are unaffected. -/
noncomputable def beta : FormalDist (Module.End ℂ Fock) :=
  fun n => if 0 ≤ n then der (Sum.inr n.toNat) else mulX (Sum.inl (-n - 1).toNat)

/-- `γ`: created by the `inr` variables, annihilated by `-∂/∂(inl)`.  ⚠ Same indexing as `beta`:
**not lower-truncated**, hence not a field (see `beta`). -/
noncomputable def gamma : FormalDist (Module.End ℂ Fock) :=
  fun n => if 0 ≤ n then -der (Sum.inl n.toNat) else mulX (Sum.inr (-n - 1).toNat)

/-- **`β` commutes with itself.** -/
theorem beta_comm (m n : ℤ) : beta m * beta n - beta n * beta m = 0 := by
  refine LinearMap.ext fun f => ?_
  simp only [LinearMap.sub_apply, Module.End.mul_apply, beta, LinearMap.zero_apply]
  by_cases hm : 0 ≤ m <;> by_cases hn : 0 ≤ n <;> simp only [hm, hn, if_true, if_false]
  · rw [der_comm, sub_self]
  · rw [der_mulX_of_ne (by simp), sub_self]
  · rw [der_mulX_of_ne (by simp), sub_self]
  · rw [mulX_comm, sub_self]

/-- **`γ` commutes with itself.** -/
theorem gamma_comm (m n : ℤ) : gamma m * gamma n - gamma n * gamma m = 0 := by
  refine LinearMap.ext fun f => ?_
  simp only [LinearMap.sub_apply, Module.End.mul_apply, gamma, LinearMap.zero_apply]
  by_cases hm : 0 ≤ m <;> by_cases hn : 0 ≤ n <;>
    simp only [hm, hn, if_true, if_false, LinearMap.neg_apply, map_neg, neg_neg]
  · rw [der_comm, sub_self]
  · rw [der_mulX_of_ne (by simp)]; abel
  · rw [der_mulX_of_ne (by simp)]; abel
  · rw [mulX_comm, sub_self]

/-- **The `βγ` canonical commutation relation**: `[β₍ₘ₎, γ₍ₙ₎] = δ_{m+n+1,0}`. -/
theorem beta_gamma_comm (m n : ℤ) :
    beta m * gamma n - gamma n * beta m = if m + n + 1 = 0 then 1 else 0 := by
  refine LinearMap.ext fun f => ?_
  simp only [LinearMap.sub_apply, Module.End.mul_apply, beta, gamma]
  by_cases hm : 0 ≤ m <;> by_cases hn : 0 ≤ n <;> simp only [hm, hn, if_true, if_false]
  · -- both annihilation
    rw [if_neg (by omega)]
    simp only [LinearMap.neg_apply, map_neg]
    rw [der_comm, sub_neg_eq_add, neg_add_cancel]
    simp
  · -- `β` annihilates `inr`, `γ` creates `inr`: the pairing
    rw [der_mulX_comm]
    by_cases h : m + n + 1 = 0
    · rw [if_pos h, if_pos (by simp; omega : (Sum.inr m.toNat : ℕ ⊕ ℕ) = Sum.inr (-n - 1).toNat)]
      simp
    · rw [if_neg h, if_neg (by simp; omega : ¬(Sum.inr m.toNat : ℕ ⊕ ℕ) = Sum.inr (-n - 1).toNat)]
      simp
  · -- `β` creates `inl`, `γ` annihilates `inl`: the pairing, with the sign
    simp only [LinearMap.neg_apply, map_neg]
    rw [sub_neg_eq_add, add_comm, ← sub_eq_add_neg, der_mulX_comm]
    by_cases h : m + n + 1 = 0
    · rw [if_pos h, if_pos (by simp; omega : (Sum.inl n.toNat : ℕ ⊕ ℕ) = Sum.inl (-m - 1).toNat)]
      simp
    · rw [if_neg h, if_neg (by simp; omega : ¬(Sum.inl n.toNat : ℕ ⊕ ℕ) = Sum.inl (-m - 1).toNat)]
      simp
  · -- both creation
    rw [if_neg (by omega), mulX_comm, sub_self]
    simp

/-! ## Locality — at `ε = 1`, because `βγ` is bosonic -/

/-- `β` is local with itself (its commutator vanishes identically). -/
theorem beta_local : Local beta beta := by
  rw [← localε_one_iff]
  exact localε_of_car 0 (by intro m n; rw [one_smul]; simpa using beta_comm m n)

/-- `γ` is local with itself. -/
theorem gamma_local : Local gamma gamma := by
  rw [← localε_one_iff]
  exact localε_of_car 0 (by intro m n; rw [one_smul]; simpa using gamma_comm m n)

/-- **`β` and `γ` are mutually local** in the *ordinary* sense — `ε = 1`, `koszul 0 0 = 1` —
even though both fields are half-moded.  This is the point of the example: half-integer
moding (Axis A) does not by itself force a sign (Axis B). -/
theorem beta_gamma_local : Local beta gamma := by
  rw [← localε_one_iff]
  exact localε_of_car 1 (by intro m n; rw [one_smul]; exact beta_gamma_comm m n)

/-- Restated with the Koszul sign: both fields are **even**, so the sign is `1`. -/
theorem beta_gamma_localε_koszul : Localε (koszul 0 0) beta gamma := by
  rw [koszul_zero_left, localε_one_iff]
  exact beta_gamma_local

end BetaGamma

end VOA
