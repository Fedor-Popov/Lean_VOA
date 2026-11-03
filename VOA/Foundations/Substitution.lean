/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Foundations.IteratedLaurent
import Mathlib.Data.Int.Interval

/-!
# The substitution `z₁ ↦ z₀ + z₂` and its multiplicativity  (Gannon §5.1.2; FLM §8.10)

The general-`n` companion to `Foundations.Expansion`.  Where `Expansion` builds the two
expansions `expandPos`/`expandNeg` of `(z₁-z₂)ⁿ` and proves the canonical `n=-1` δ-jump,
this file builds the **substitution operator** `subst` realizing `ι_{z₂,z₀}`: replace `z₁`
by `z₀+z₂` in a two-variable distribution `f(z₁,z₂)` that is lower-truncated in `z₂`
(`IsBddBelow₂`), expanding each `(z₀+z₂)ᵐ` in nonnegative powers of `z₂`.  Coefficient of
`z₀ᵃz₂ᵇ`:
  `(subst f) a b = ∑_{k} C(a+k, k) · f(a+k, b-k)`,
summed over `k : ℤ` with the convention `C(·,k) = 0` for `k < 0` (so only `k ≥ 0`
contribute); lower-truncation makes each such sum finite.

The technical heart is the **keystone multiplicativity** (`subst_mulBySub`):
  `subst((z₁-z₂)·f) = z₀·subst(f)`,
i.e. the substitution turns multiplication by `(z₁-z₂)` into multiplication by
`z₀ = (z₀+z₂)-z₂`.  This is the algebraic identity behind the change of variables in the
weak-associativity / duality theorems (Gannon 5.1.9; Kac §4).  Its proof is purely
formal: **Pascal's rule** for the generalized binomial (`cbz_pascal`,
`gBinom_succ_pascal`) plus an index shift `k ↦ k+1`.

This is the **general-`n` multiplicativity** not proved in `Foundations.Expansion`; it is
proved here `sorry`-free.

## Dependencies
* `VOA.Foundations.IteratedLaurent` (`IsBddBelow₂`, `mulBySub`, `mulBySubPow`),
  hence `FormalCalculus` (`gBinom`, `finsum_int_succ_shift`) and `FormalSeries`
  (`shiftZ₁`).

## Status
Complete & `sorry`-free / axiom-free.  The generalized-binomial Pascal
calculus (`gBinom_mul_factorial`, `gBinom_succ_pascal`, `cbz_pascal`), the substitution `subst`
with its finiteness (`subst_summand_finite`), and the keystone multiplicativity `subst_mulBySub`
/ `subst_mulBySubPow` are proved (`#print axioms = [propext, Classical.choice, Quot.sound]`).
This discharges the deferred general-`n` `ι_z` multiplicativity of `Foundations.Expansion`.  (The
downstream
reconstruction — weak associativity 5.1.9, which additionally needs Dong's lemma — lives
in `Core`; see `README.md`.)

## References
* Gannon §5.1.2; Frenkel–Lepowsky–Meurman §8.10; Kac, *VA for Beginners* §2, §4.
-/

namespace VOA

open scoped BigOperators

universe u
variable {𝒲 : Type u} [AddCommGroup 𝒲] [Module ℂ 𝒲]

/-! ## Generalized-binomial Pascal calculus -/

/-- Peel the leading factor of a falling product: `∏_{i<m+1}(x-i) = x·∏_{i<m}((x-1)-i)`. -/
theorem prod_falling_succ (x : ℂ) (m : ℕ) :
    (∏ i ∈ Finset.range (m + 1), (x - (i : ℂ)))
      = x * ∏ i ∈ Finset.range m, ((x - 1) - (i : ℂ)) := by
  rw [Finset.prod_range_succ' (fun i => x - (i : ℂ)) m,
    show (x - ((0 : ℕ) : ℂ)) = x by push_cast; ring, mul_comm]
  congr 1
  exact Finset.prod_congr rfl (fun i _ => by push_cast; ring)

/-- Clearing the factorial denominator: `k! · C(n,k) = ∏_{i<k}(n-i)` (Gannon 5.1.4a). -/
theorem gBinom_mul_factorial (n : ℤ) (k : ℕ) :
    (k.factorial : ℂ) * gBinom n k = ∏ i ∈ Finset.range k, ((n : ℂ) - (i : ℂ)) := by
  rw [gBinom, mul_div_cancel₀ _ (by exact_mod_cast Nat.factorial_ne_zero k)]

/-- **Pascal's rule** for the generalized binomial: `C(n,j+1) = C(n-1,j+1) + C(n-1,j)`. -/
theorem gBinom_succ_pascal (n : ℤ) (j : ℕ) :
    gBinom n (j + 1) = gBinom (n - 1) (j + 1) + gBinom (n - 1) j := by
  have hfac_ne : (((j + 1).factorial : ℂ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (j + 1)
  have hn1 : ((n - 1 : ℤ) : ℂ) = (n : ℂ) - 1 := by push_cast; ring
  refine mul_left_cancel₀ hfac_ne ?_
  rw [mul_add, gBinom_mul_factorial n (j + 1), gBinom_mul_factorial (n - 1) (j + 1),
    prod_falling_succ (n : ℂ) j, Finset.prod_range_succ (fun i => ((n - 1 : ℤ) : ℂ) - (i : ℂ)) j,
    Nat.factorial_succ, Nat.cast_mul, mul_assoc, gBinom_mul_factorial (n - 1) j,
    Nat.cast_add, Nat.cast_one]
  simp only [hn1]
  ring

/-! ## The integer-indexed binomial `cbz` -/

/-- Integer-indexed generalized binomial `C(n,k)`, zero for `k < 0` (so we may sum over
`k : ℤ` and reindex cleanly). -/
noncomputable def cbz (n k : ℤ) : ℂ := if 0 ≤ k then gBinom n k.toNat else 0

theorem cbz_apply_neg (n : ℤ) {k : ℤ} (hk : k < 0) : cbz n k = 0 := if_neg (by omega)

theorem cbz_apply_nonneg (n : ℤ) {k : ℤ} (hk : 0 ≤ k) : cbz n k = gBinom n k.toNat :=
  if_pos hk

@[simp] theorem cbz_zero (n : ℤ) : cbz n 0 = 1 := by
  rw [cbz_apply_nonneg n le_rfl]; simp

/-- **Pascal's rule** for the integer binomial `cbz`: `C(n,k) = C(n-1,k) + C(n-1,k-1)`,
all `n k : ℤ` (with the `k<0` convention `C(·,k)=0`). -/
theorem cbz_pascal (n k : ℤ) : cbz n k = cbz (n - 1) k + cbz (n - 1) (k - 1) := by
  rcases lt_trichotomy k 0 with hk | hk | hk
  · rw [cbz_apply_neg n hk, cbz_apply_neg (n - 1) hk, cbz_apply_neg (n - 1) (by omega)]; ring
  · subst hk
    simp only [cbz_zero]
    rw [show (0 : ℤ) - 1 = -1 by ring, cbz_apply_neg (n - 1) (show (-1 : ℤ) < 0 by norm_num)]
    ring
  · obtain ⟨j, rfl⟩ : ∃ j : ℕ, k = (j : ℤ) + 1 := ⟨(k - 1).toNat, by omega⟩
    rw [cbz_apply_nonneg n (by omega), cbz_apply_nonneg (n - 1) (by omega),
      cbz_apply_nonneg (n - 1) (show (0 : ℤ) ≤ (j : ℤ) + 1 - 1 by omega),
      show ((j : ℤ) + 1).toNat = j + 1 by omega, show ((j : ℤ) + 1 - 1).toNat = j by omega]
    exact gBinom_succ_pascal n j

/-! ## The substitution operator -/

/-- The **`z₂`-dominant substitution** `z₁ ↦ z₀ + z₂` (Gannon §5.1.2; the `ι_{z₂,z₀}` map):
replace `z₁` by `z₀+z₂` in `f(z₁,z₂)`, expanding each `(z₀+z₂)ᵐ` in nonnegative powers of
`z₂`.  Coefficient of `z₀ᵃz₂ᵇ` is `∑_{k} C(a+k,k) · f(a+k, b-k)` (`k : ℤ`, `C(·,k)=0` for
`k<0`).  Well-defined (each coefficient a finite sum) on distributions lower-truncated in
`z₂` (`IsBddBelow₂`); see `subst_summand_finite`. -/
noncomputable def subst (f : FormalDist₂ 𝒲) : FormalDist₂ 𝒲 :=
  fun a b => ∑ᶠ k : ℤ, cbz (a + k) k • f (a + k) (b - k)

@[simp] theorem subst_apply (f : FormalDist₂ 𝒲) (a b : ℤ) :
    subst f a b = ∑ᶠ k : ℤ, cbz (a + k) k • f (a + k) (b - k) := rfl

/-- For `f` bounded below in `z₂`, any summand `c k · f(a+k, b-k)` with `c` vanishing below
`lo` has finite support in `k` (the binomial forces `k ≥ lo`; lower-truncation forces
`k ≤ b-B`).  This is what makes `subst f` algebraically defined. -/
theorem subst_summand_finite {f : FormalDist₂ 𝒲} (hf : IsBddBelow₂ f) (a b lo : ℤ) (c : ℤ → ℂ)
    (hc : ∀ k, k < lo → c k = 0) :
    (Function.support (fun k : ℤ => c k • f (a + k) (b - k))).Finite := by
  obtain ⟨B, hB⟩ := hf
  apply Set.Finite.subset (Set.finite_Icc lo (b - B))
  intro k hk
  rw [Function.mem_support] at hk
  rw [Set.mem_Icc]
  exact ⟨not_lt.mp fun h => hk (by rw [hc k h, zero_smul]),
         not_lt.mp fun h => hk (by rw [hB (a + k) (b - k) (by omega), smul_zero])⟩

/-! ## Keystone multiplicativity -/

/-- **Keystone multiplicativity of the substitution** (Gannon §5.1.2): substituting
`z₁ = z₀+z₂` turns multiplication by `(z₁-z₂)` into multiplication by `z₀`, i.e.
`subst((z₁-z₂)·f) = z₀·subst(f)` (with `z₀·` realized as `shiftZ₁` in the `(z₀,z₂)`
variables).  Proved coefficient-wise from Pascal's rule (`cbz_pascal`) and the index shift
`k ↦ k+1`. -/
theorem subst_mulBySub {f : FormalDist₂ 𝒲} (hf : IsBddBelow₂ f) :
    subst (mulBySub f) = shiftZ₁ (subst f) := by
  ext a b
  rw [shiftZ₁_apply, subst_apply, subst_apply]
  have hLHS : (∑ᶠ k : ℤ, cbz (a + k) k • mulBySub f (a + k) (b - k))
      = (∑ᶠ k : ℤ, cbz (a + k) k • f (a - 1 + k) (b - k))
        - (∑ᶠ k : ℤ, cbz (a + k) k • f (a + k) (b - 1 - k)) := by
    rw [← finsum_sub_distrib
        (subst_summand_finite hf (a - 1) b 0 _ (fun k _ => cbz_apply_neg _ (by omega)))
        (subst_summand_finite hf a (b - 1) 0 _ (fun k _ => cbz_apply_neg _ (by omega)))]
    refine finsum_congr fun k => ?_
    rw [mulBySub_apply, smul_sub,
      show a + k - 1 = a - 1 + k from by ring, show b - k - 1 = b - 1 - k from by ring]
  rw [hLHS, sub_eq_iff_eq_add]
  have hAR : (∑ᶠ k : ℤ, cbz (a + k) k • f (a - 1 + k) (b - k))
      - (∑ᶠ k : ℤ, cbz (a - 1 + k) k • f (a - 1 + k) (b - k))
      = ∑ᶠ k : ℤ, cbz (a + k) k • f (a + k) (b - 1 - k) := by
    rw [← finsum_sub_distrib
        (subst_summand_finite hf (a - 1) b 0 _ (fun k _ => cbz_apply_neg _ (by omega)))
        (subst_summand_finite hf (a - 1) b 0 _ (fun k _ => cbz_apply_neg _ (by omega)))]
    rw [show (∑ᶠ k : ℤ, (cbz (a + k) k • f (a - 1 + k) (b - k)
              - cbz (a - 1 + k) k • f (a - 1 + k) (b - k)))
          = ∑ᶠ k : ℤ, cbz (a - 1 + k) (k - 1) • f (a - 1 + k) (b - k) from
        finsum_congr fun k => by
          rw [← sub_smul]; congr 1
          have hp := cbz_pascal (a + k) k
          rw [show a + k - 1 = a - 1 + k from by ring] at hp
          rw [hp]; ring]
    rw [← finsum_int_succ_shift (fun k : ℤ => cbz (a - 1 + k) (k - 1) • f (a - 1 + k) (b - k))]
    refine finsum_congr fun k => ?_
    dsimp only
    rw [show a - 1 + (k + 1) = a + k from by ring, show k + 1 - 1 = k from by ring,
      show b - (k + 1) = b - 1 - k from by ring]
  rw [add_comm]
  exact sub_eq_iff_eq_add.mp hAR

/-- The iterated keystone: `subst((z₁-z₂)ᴺ·f) = z₀ᴺ·subst(f)` (Gannon §5.1.2). -/
theorem subst_mulBySubPow {f : FormalDist₂ 𝒲} (hf : IsBddBelow₂ f) (N : ℕ) :
    subst (mulBySubPow N f) = (shiftZ₁^[N]) (subst f) := by
  induction N with
  | zero => simp
  | succ k ih =>
      rw [mulBySubPow_succ, LinearMap.comp_apply,
        subst_mulBySub (hf.mulBySubPow k), ih, Function.iterate_succ', Function.comp_apply]

end VOA
