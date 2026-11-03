/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Foundations.FormalSeries
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Tactic.Module
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-!
# M8h-0: the translation equation `L D = (∂₁ + ∂₂) D` for two-variable distributions

For a `ℂ`-module `V` with an operator `L` (the translation `L₋₁`), a two-variable distribution
`D(z₁, z₂) = ∑ D(m,n) z₁ᵐ z₂ⁿ` satisfies the **translation equation** (`TEq`) when

  `L D(m,n) = (m+1) D(m+1,n) + (n+1) D(m,n+1)`,   i.e. `L D = (∂₁ + ∂₂) D`.

Products `W̄(t₁,z₁) W(t₂,z₂) 𝟙` of translation-covariant operators on the vacuum satisfy it.  This
file collects the elementary facts used for the vacuum step of DGM (4.22):

* `TEq.mulBySubPow` — `(z₁ − z₂)ᴺ` preserves the equation (`∂₁ + ∂₂` kills `z₁ − z₂`);
* `TEq.zero_of_neg_left` — a solution vanishing for `n < 0`, and at `n = 0` for `m < 0`, vanishes
  for all `m < 0`;
* `TEq.eq_zero_of_quadrant` — a solution supported on `m, n ≥ 0` that vanishes on the boundary
  `m = 0` is zero;
* `TEq.closed_form` — a solution supported on `m, n ≥ 0` is `D(z₁,z₂) = e^{z₂L} D(z₁ − z₂, 0)`:
  `D(m,n) = ∑_{s+r=n} C(m+r, r) (−1)ʳ / s! · Lˢ D(m+r, 0)`.

## Status
`sorry`-free; generic.
-/

namespace VOA.Moonshine.M8h0

open Module (End)
open scoped BigOperators

variable {V : Type*} [AddCommGroup V] [Module ℂ V] (L : End ℂ V)

/-- The translation equation `L D = (∂₁ + ∂₂) D`. -/
def TEq (D : FormalDist₂ V) : Prop :=
  ∀ m n : ℤ, L (D m n) = ((m + 1 : ℤ) : ℂ) • D (m + 1) n + ((n + 1 : ℤ) : ℂ) • D m (n + 1)

variable {L}

theorem TEq.mulBySub {D : FormalDist₂ V} (h : TEq L D) : TEq L (mulBySub D) := by
  intro m n
  simp only [mulBySub_apply, map_sub]
  rw [h (m - 1) n, h m (n - 1)]
  simp only [sub_add_cancel, add_sub_cancel_right]
  push_cast
  module

theorem TEq.mulBySubPow {D : FormalDist₂ V} (h : TEq L D) (N : ℕ) : TEq L (mulBySubPow N D) := by
  induction N with
  | zero => simpa using h
  | succ N ih => rw [mulBySubPow_succ, LinearMap.comp_apply]; exact ih.mulBySub

theorem TEq.swap {D : FormalDist₂ V} (h : TEq L D) : TEq L (fun m n => D n m) := by
  intro m n
  rw [h n m, add_comm]

theorem TEq.sub {D D' : FormalDist₂ V} (h : TEq L D) (h' : TEq L D') : TEq L (D - D') := by
  intro m n
  change L (D m n - D' m n) = _ • (D (m + 1) n - D' (m + 1) n) + _ • (D m (n + 1) - D' m (n + 1))
  rw [map_sub, h, h']
  module

theorem natCast_succ_ne_zero (k : ℕ) : (((k : ℤ) + 1 : ℤ) : ℂ) ≠ 0 := by
  push_cast; exact_mod_cast Nat.succ_ne_zero k

/-- A solution vanishing for `n < 0`, and at `n = 0` for `m < 0`, vanishes for all `m < 0`. -/
theorem TEq.zero_of_neg_left {D : FormalDist₂ V} (h : TEq L D) (hn : ∀ m n, n < 0 → D m n = 0)
    (h0 : ∀ m, m < 0 → D m 0 = 0) : ∀ m n, m < 0 → D m n = 0 := by
  have key : ∀ k : ℕ, ∀ m, m < 0 → D m k = 0 := by
    intro k
    induction k with
    | zero => exact fun m hm => h0 m hm
    | succ k ih =>
      intro m hm
      have e := h m k
      rw [ih m hm, map_zero] at e
      have e2 : ((m + 1 : ℤ) : ℂ) • D (m + 1) k = 0 := by
        by_cases hm1 : m + 1 < 0
        · rw [ih _ hm1, smul_zero]
        · rw [show m + 1 = 0 by omega]; simp
      rw [e2, zero_add] at e
      have := (smul_eq_zero.mp e.symm).resolve_left (natCast_succ_ne_zero k)
      exact_mod_cast this
  intro m n hm
  by_cases hn0 : n < 0
  · exact hn m n hn0
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k := ⟨n.toNat, by omega⟩
    exact key k m hm

/-- A quadrant-supported solution vanishing on `m = 0` is zero. -/
theorem TEq.eq_zero_of_quadrant {D : FormalDist₂ V} (h : TEq L D)
    (hq : ∀ m n, (m < 0 ∨ n < 0) → D m n = 0) (h0 : ∀ n, D 0 n = 0) : D = 0 := by
  have key : ∀ k : ℕ, ∀ n, D k n = 0 := by
    intro k
    induction k with
    | zero => exact h0
    | succ k ih =>
      intro n
      have e := h k n
      rw [ih n, map_zero, ih (n + 1), smul_zero, add_zero] at e
      have := (smul_eq_zero.mp e.symm).resolve_left (natCast_succ_ne_zero k)
      exact_mod_cast this
  refine FormalDist₂.ext fun m n => ?_
  by_cases hm : m < 0
  · exact hq m n (Or.inl hm)
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, m = k := ⟨m.toNat, by omega⟩
    exact key k n

/-! ## The closed form `D(z₁,z₂) = e^{z₂L} D(z₁−z₂, 0)` on the quadrant -/

/-- The coefficient `C(m+r, r)(−1)ʳ/s!`. -/
noncomputable def tcoef (m s r : ℕ) : ℂ :=
  ((m + r).choose r : ℂ) * (-1 : ℂ) ^ r * ((s.factorial : ℂ))⁻¹

theorem tcoef_succ_s (m s r : ℕ) : ((s + 1 : ℕ) : ℂ) * tcoef m (s + 1) r = tcoef m s r := by
  unfold tcoef
  rw [Nat.factorial_succ, Nat.cast_mul]
  have : (s.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero s
  have h1 : ((s + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero s
  field_simp

theorem tcoef_succ_r (m s r : ℕ) :
    ((r + 1 : ℕ) : ℂ) * tcoef m s (r + 1) = -(((m + 1 : ℕ) : ℂ) * tcoef (m + 1) s r) := by
  unfold tcoef
  have hc : ((m + (r + 1)).choose (r + 1) : ℂ) * ((r + 1 : ℕ) : ℂ)
      = ((m + 1 + r).choose r : ℂ) * ((m + 1 : ℕ) : ℂ) := by
    have := Nat.choose_succ_right_eq (m + (r + 1)) r
    rw [show m + (r + 1) - r = m + 1 by omega, show m + (r + 1) = m + 1 + r by omega] at this
    rw [show m + (r + 1) = m + 1 + r by omega]
    exact_mod_cast this
  rw [pow_succ]
  linear_combination (-(1 : ℂ)) ^ r * (s.factorial : ℂ)⁻¹ * (-1) * hc

/-- **The closed form**: a solution of `L D = (∂₁+∂₂)D` supported on the quadrant
`m, n ≥ 0` satisfies `D(m,n) = ∑_{s+r=n} C(m+r,r)(−1)ʳ/s! · Lˢ D(m+r,0)`. -/
theorem TEq.closed_form {D : FormalDist₂ V} (h : TEq L D) :
    ∀ n m : ℕ, D m n = ∑ p ∈ Finset.antidiagonal n,
      tcoef m p.1 p.2 • (L ^ p.1) (D ((m + p.2 : ℕ) : ℤ) 0) := by
  intro n
  induction n with
  | zero =>
    intro m
    simp [tcoef]
  | succ n ih =>
    intro m
    have e := h m n
    -- `(n+1) D(m,n+1) = L D(m,n) − (m+1) D(m+1,n)`
    have hn1 : (((n : ℤ) + 1 : ℤ) : ℂ) ≠ 0 := natCast_succ_ne_zero n
    refine smul_right_injective V hn1 ?_
    simp only
    have e' : (((n : ℤ) + 1 : ℤ) : ℂ) • D m (n + 1)
        = L (D m n) - (((m : ℤ) + 1 : ℤ) : ℂ) • D (m + 1) n := by
      rw [e]; abel
    rw [show ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 by push_cast; ring, e', ih m,
      show ((m : ℤ) + 1) = ((m + 1 : ℕ) : ℤ) by push_cast; ring, ih (m + 1)]
    -- split `n + 1 = s + r` on the antidiagonal
    have hsplit : (((n : ℤ) + 1 : ℤ) : ℂ) • ∑ p ∈ Finset.antidiagonal (n + 1),
          tcoef m p.1 p.2 • (L ^ p.1) (D ((m + p.2 : ℕ) : ℤ) 0)
        = ∑ p ∈ Finset.antidiagonal (n + 1),
            ((p.1 : ℂ) * tcoef m p.1 p.2) • (L ^ p.1) (D ((m + p.2 : ℕ) : ℤ) 0)
          + ∑ p ∈ Finset.antidiagonal (n + 1),
            ((p.2 : ℂ) * tcoef m p.1 p.2) • (L ^ p.1) (D ((m + p.2 : ℕ) : ℤ) 0) := by
      rw [Finset.smul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [Finset.mem_antidiagonal] at hp
      rw [smul_smul, ← add_smul]
      congr 1
      have : (p.1 : ℂ) + p.2 = (((n : ℤ) + 1 : ℤ) : ℂ) := by push_cast; exact_mod_cast hp
      rw [← add_mul, this]
    rw [hsplit, Finset.Nat.sum_antidiagonal_succ, Finset.Nat.sum_antidiagonal_succ']
    simp only [Nat.cast_zero, zero_mul, zero_smul, zero_add]
    rw [sub_eq_add_neg]
    congr 1
    · rw [map_sum L]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [map_smul, ← Module.End.mul_apply, ← pow_succ', tcoef_succ_s]
    · rw [Finset.smul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [tcoef_succ_r, show m + (p.2 + 1) = m + 1 + p.2 by omega, smul_smul, ← neg_smul]
      congr 1

end VOA.Moonshine.M8h0
