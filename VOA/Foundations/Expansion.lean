/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Foundations.FormalCalculus
import VOA.Foundations.Locality

/-!
# The expansion maps `ι_z` and the δ-function jump  (Gannon §5.1.2; FLM §8.10)

A rational function such as `(z₁ - z₂)ⁿ` (`n ∈ ℤ`) has **two** formal-distribution
expansions, depending on which variable is treated as "dominant":

* `ι₁₂((z₁-z₂)ⁿ) = expandPos n` — expand in **nonnegative powers of `z₂`**:
  `(z₁-z₂)ⁿ = ∑_{k≥0} \binom{n}{k} (-1)ᵏ z₁^{n-k} z₂ᵏ`.
* `ι₂₁((z₁-z₂)ⁿ) = expandNeg n` — expand in **nonnegative powers of `z₁`**:
  `(z₁-z₂)ⁿ = ∑_{k≥0} (-1)^{n+k} \binom{n}{k} z₁ᵏ z₂^{n-k}`.

For `n ≥ 0` the two agree (it is a genuine Laurent polynomial); for `n < 0` they differ,
and the difference is supported on the antidiagonal — the **δ-function jump**.  The
canonical case `n = -1` gives the fundamental identity (Gannon 5.1.2; FLM (8.10.x))
`ι₁₂(1/(z₁-z₂)) - ι₂₁(1/(z₁-z₂)) = δ(z₁/z₂)`, where `δ(z₁/z₂) = ∑_{k} z₁ᵏ z₂^{-k-1}` has
coefficient `[m+n+1=0]`.  This is the analytic source of the locality ⇔ Jacobi mechanism
(`Foundations.Locality.local_iff_deltaSum`): `(z₁-z₂)·δ(z₁/z₂) = 0` exhibits `δ` as a
single `deltaDeriv 0`-term.

This file builds these expansions and proves the `n = -1` δ-jump `sorry`-free.  It is the
first ingredient of the reconstruction/duality theorems (the `ι_z` calculus needed for weak
associativity and Goddard uniqueness); see `README.md`.

## Dependencies
* `VOA.Foundations.FormalCalculus` (`gBinom`, `FormalDist₂`),
  `VOA.Foundations.Locality` (`mulBySub`).

## Status
Complete & `sorry`-free / axiom-free.  All listed targets — the two
expansions `expandPos`/`expandNeg`, the canonical δ-jump
`expandPos (-1) - expandNeg (-1) = deltaForm` (`expand_jump`), and `mulBySub_deltaForm`
(`(z₁-z₂)·deltaForm = 0`) — are proved (`#print axioms = [propext, Classical.choice,
Quot.sound]`).  (The general-`n` `ι_z` multiplicativity is not a target of this file; it is
`expandPos_mul`/`expandNeg_mul` in `Foundations.IotaZExpansion`.)

## References
* Gannon §5.1.2; Frenkel–Lepowsky–Meurman §8.10; Kac, *VA for Beginners* §2.
-/

namespace VOA

open scoped BigOperators

/-! ## The integer sign `(-1)ⁿ` -/

/-- The sign `(-1)ⁿ` for `n ∈ ℤ`, as a complex number (avoiding `zpow`). -/
def negOnePow (n : ℤ) : ℂ := if Even n then 1 else -1

theorem negOnePow_mul_self (n : ℤ) : negOnePow n * negOnePow n = 1 := by
  rw [negOnePow]; split_ifs <;> norm_num

/-- The recurrence `(-1)^{n+1} = -(-1)ⁿ`. -/
theorem negOnePow_succ (n : ℤ) : negOnePow (n + 1) = - negOnePow n := by
  simp only [negOnePow]
  by_cases h : Even n
  · rw [if_neg (by rw [Int.even_add_one]; exact not_not.mpr h), if_pos h]
  · rw [if_pos (Int.even_add_one.mpr h), if_neg h]; norm_num

/-- On `ℕ`-exponents, `negOnePow` is the genuine power `(-1)ᵏ`. -/
theorem negOnePow_natCast (k : ℕ) : negOnePow (k : ℤ) = (-1 : ℂ) ^ k := by
  induction k with
  | zero => simp [negOnePow]
  | succ k ih => rw [Nat.cast_succ, negOnePow_succ, ih, pow_succ]; ring

/-! ## The generalized binomial coefficient at `-1` -/

/-- `∏_{i<k} (-1 - i) = (-1)ᵏ · k!` over `ℂ`. -/
theorem prod_neg_one_sub (k : ℕ) :
    ∏ i ∈ Finset.range k, ((-1 : ℂ) - (i : ℂ)) = (-1) ^ k * (k.factorial : ℂ) := by
  induction k with
  | zero => simp
  | succ k ih => rw [Finset.prod_range_succ, ih, Nat.factorial_succ]; push_cast; ring

/-- `C(-1, k) = (-1)ᵏ` (Gannon 5.1.4a at `n = -1`). -/
theorem gBinom_neg_one (k : ℕ) : gBinom (-1) k = (-1 : ℂ) ^ k := by
  rw [gBinom, show (((-1 : ℤ) : ℂ)) = -1 by norm_num, prod_neg_one_sub, mul_div_assoc,
    div_self (by exact_mod_cast Nat.factorial_ne_zero k), mul_one]

/-! ## The two expansions of `(z₁ - z₂)ⁿ` -/

/-- `ι₁₂((z₁-z₂)ⁿ)`: expansion of `(z₁-z₂)ⁿ` in **nonnegative powers of `z₂`** (Gannon
§5.1.2).  Coefficient of `z₁ᵃz₂ᵇ` is `(-1)ᵇ C(n,b)` when `b ≥ 0` and `a = n-b`. -/
noncomputable def expandPos (n : ℤ) : FormalDist₂ ℂ :=
  fun a b => if 0 ≤ b ∧ a = n - b then negOnePow b * gBinom n b.toNat else 0

/-- `ι₂₁((z₁-z₂)ⁿ)`: expansion of `(z₁-z₂)ⁿ` in **nonnegative powers of `z₁`** (Gannon
§5.1.2).  Coefficient of `z₁ᵃz₂ᵇ` is `(-1)^{n+a} C(n,a)` when `a ≥ 0` and `b = n-a`. -/
noncomputable def expandNeg (n : ℤ) : FormalDist₂ ℂ :=
  fun a b => if 0 ≤ a ∧ b = n - a then negOnePow (n + a) * gBinom n a.toNat else 0

@[simp] theorem expandPos_apply (n a b : ℤ) :
    expandPos n a b = if 0 ≤ b ∧ a = n - b then negOnePow b * gBinom n b.toNat else 0 := rfl

@[simp] theorem expandNeg_apply (n a b : ℤ) :
    expandNeg n a b = if 0 ≤ a ∧ b = n - a then negOnePow (n + a) * gBinom n a.toNat else 0 := rfl

/-! ## The formal delta and the canonical δ-jump (`n = -1`) -/

/-- The formal delta `δ(z₁/z₂) = ∑_{k} z₁ᵏ z₂^{-k-1}`: coefficient of `z₁ᵐz₂ⁿ` is
`[m+n+1=0]` (Gannon 5.1.2, Locality's normalization). -/
def deltaForm : FormalDist₂ ℂ := fun m n => if m + n + 1 = 0 then 1 else 0

@[simp] theorem deltaForm_apply (m n : ℤ) :
    deltaForm m n = if m + n + 1 = 0 then 1 else 0 := rfl

/-- `ι₁₂(1/(z₁-z₂))` has coefficient `1` on `{b ≥ 0, a = -1-b}` and `0` elsewhere. -/
theorem expandPos_neg_one (a b : ℤ) :
    expandPos (-1) a b = if 0 ≤ b ∧ a = -1 - b then 1 else 0 := by
  rw [expandPos_apply]
  by_cases h : 0 ≤ b ∧ a = -1 - b
  · rw [if_pos h, if_pos h, gBinom_neg_one, ← negOnePow_natCast,
      Int.toNat_of_nonneg h.1, negOnePow_mul_self]
  · rw [if_neg h, if_neg h]

/-- `ι₂₁(1/(z₁-z₂))` has coefficient `-1` on `{a ≥ 0, b = -1-a}` and `0` elsewhere. -/
theorem expandNeg_neg_one (a b : ℤ) :
    expandNeg (-1) a b = if 0 ≤ a ∧ b = -1 - a then -1 else 0 := by
  rw [expandNeg_apply]
  by_cases h : 0 ≤ a ∧ b = -1 - a
  · rw [if_pos h, if_pos h, gBinom_neg_one, ← negOnePow_natCast, Int.toNat_of_nonneg h.1]
    have hpar : negOnePow (-1 + a) = - negOnePow a := by
      have hs := negOnePow_succ (a - 1)
      rw [show a - 1 + 1 = a by ring] at hs
      rw [show (-1 + a : ℤ) = a - 1 by ring, hs, neg_neg]
    rw [hpar, neg_mul, negOnePow_mul_self]
  · rw [if_neg h, if_neg h]

/-- **The δ-function jump** (Gannon 5.1.2; FLM §8.10): the two expansions of `1/(z₁-z₂)`
differ by the formal delta, `ι₁₂(1/(z₁-z₂)) - ι₂₁(1/(z₁-z₂)) = δ(z₁/z₂)`.  This is the
analytic identity behind locality ⇔ Jacobi. -/
theorem expand_jump : expandPos (-1) - expandNeg (-1) = deltaForm := by
  ext m n
  change expandPos (-1) m n - expandNeg (-1) m n = deltaForm m n
  rw [expandPos_neg_one, expandNeg_neg_one, deltaForm_apply]
  by_cases hmn : m + n + 1 = 0
  · rw [if_pos hmn]
    by_cases hn : 0 ≤ n
    · rw [if_pos ⟨hn, by omega⟩, if_neg (by rintro ⟨ha, _⟩; omega)]; ring
    · rw [if_neg (by rintro ⟨hn', _⟩; omega), if_pos ⟨by omega, by omega⟩]; ring
  · rw [if_neg hmn, if_neg (by rintro ⟨_, h⟩; omega), if_neg (by rintro ⟨_, h⟩; omega)]; ring

/-- `(z₁-z₂)·δ(z₁/z₂) = 0`: the delta is annihilated by `(z₁-z₂)`, exhibiting it as a
single `deltaDeriv 0`-term and tying the δ-jump to `local_iff_deltaSum`. -/
theorem mulBySub_deltaForm : mulBySub (deltaForm : FormalDist₂ ℂ) = 0 := by
  ext m n
  rw [mulBySub_apply]
  change deltaForm (m - 1) n - deltaForm m (n - 1) = (0 : ℂ)
  rw [deltaForm_apply, deltaForm_apply]
  by_cases h : m + n = 0
  · rw [if_pos (by omega), if_pos (by omega)]; ring
  · rw [if_neg (by omega), if_neg (by omega)]; ring

end VOA
