/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Foundations.Locality

/-!
# Lower-truncated distributions and the `(z₁-z₂)` cancellation  (Gannon §5.1.2)

The technical heart of the reconstruction/duality theorems (Gannon 5.1.9, Goddard
uniqueness): on the space `𝒲[[z₁^±]]((z₂))` of distributions lower-truncated in `z₂`
(uniformly in `z₁`, with no condition on the `z₁`-powers) the element `z₁-z₂` is a
non–zero-divisor, so a distribution annihilated by `(z₁-z₂)ᴺ` *and lying in that space*
must already vanish.  We do **not** need Mathlib's `HahnSeries` field: the relevant
sub-class is the **lower-truncated** distributions

  `IsBddBelow₂ f  :↔  ∃ B, ∀ m n, n < B → f m n = 0`  (the `z₂`-support is bounded below,
   uniformly in the `z₁`-power),

which is exactly what the products `Y(u,z₁)Y(v,z₂)x` satisfy (VA5 regularity makes
`(Y v)ₙ x = 0` for `n ≪ 0`, killing the whole `z₁`-column).  On this sub-class the
cancellation is elementary: Proposition 5.1.2 (`eq_deltaDeriv_zero_of_mulBySub_eq_zero`)
makes a `(z₁-z₂)`-annihilated distribution constant along antidiagonals, and a lower
truncation along *every* antidiagonal then forces it to be `0`.

## Dependencies
* `VOA.Foundations.Locality` (`mulBySub`, `mulBySubPow`, `deltaDeriv`,
  `eq_deltaDeriv_zero_of_mulBySub_eq_zero`).

## Status
Complete & `sorry`-free / axiom-free.  The lower-truncated
predicate `IsBddBelow₂`, its stability under `mulBySub`/`mulBySubPow`, and the cancellation
engine `eq_zero_of_mulBySubPow_of_bddBelow` are proved (`#print axioms = [propext,
Classical.choice, Quot.sound]`).  This is the "`𝒱((z))((w))` fields framework" underlying
the duality theorems.

## References
* Gannon §5.1.2 (Prop 5.1.2); Frenkel–Lepowsky–Meurman §8.10; Kac, *VA for Beginners* §4
  (Goddard uniqueness, "fields" and lower truncation).
-/

namespace VOA

universe u

variable {𝒲 : Type u} [AddCommGroup 𝒲] [Module ℂ 𝒲]

/-! ## Lower-truncated two-variable distributions -/

/-- A two-variable distribution is **lower-truncated in `z₂`** when its `z₂`-support is
bounded below, uniformly in the `z₁`-power: `∃ B, ∀ m n, n < B → f m n = 0`.  This is the
sub-class `𝒲[[z₁^±]]((z₂))` (no truncation in `z₁`; strictly larger than `𝒲((z₁))((z₂))`)
relevant to locality (Gannon §5.1.2); the iterated products
`Y(u,z₁)Y(v,z₂)x` lie in it by VA5. -/
def IsBddBelow₂ (f : FormalDist₂ 𝒲) : Prop := ∃ B : ℤ, ∀ m n : ℤ, n < B → f m n = 0

/-- Lower truncation is preserved by multiplication by `(z₁-z₂)`. -/
theorem IsBddBelow₂.mulBySub {f : FormalDist₂ 𝒲} (h : IsBddBelow₂ f) :
    IsBddBelow₂ (mulBySub f) := by
  obtain ⟨B, hB⟩ := h
  refine ⟨B, fun m n hn => ?_⟩
  rw [mulBySub_apply, hB (m - 1) n hn, hB m (n - 1) (by omega), sub_zero]

/-- Lower truncation is preserved by multiplication by `(z₁-z₂)ᴺ`. -/
theorem IsBddBelow₂.mulBySubPow (N : ℕ) {f : FormalDist₂ 𝒲} (h : IsBddBelow₂ f) :
    IsBddBelow₂ (mulBySubPow N f) := by
  induction N with
  | zero => simpa using h
  | succ k ih => rw [mulBySubPow_succ, LinearMap.comp_apply]; exact ih.mulBySub

/-! ## The cancellation -/

/-- **Antidiagonal cancellation (`N = 1`).** A lower-truncated `f` annihilated by
`(z₁-z₂)` is zero.  By Proposition 5.1.2 (`eq_deltaDeriv_zero_of_mulBySub_eq_zero`) such an
`f` is constant along antidiagonals (`f m n = f (-1) (m+n+1)`); lower truncation along
each antidiagonal then forces `f = 0` (Gannon §5.1.2). -/
theorem eq_zero_of_mulBySub_of_bddBelow {f : FormalDist₂ 𝒲} (hsub : mulBySub f = 0)
    (hbb : IsBddBelow₂ f) : f = 0 := by
  obtain ⟨B, hB⟩ := hbb
  have hf := eq_deltaDeriv_zero_of_mulBySub_eq_zero hsub
  have key : ∀ a b : ℤ, f a b = f (-1) (a + b + 1) := by
    intro a b
    conv_lhs => rw [hf]
    simp [deltaDeriv_apply]
  ext m n
  change f m n = 0
  rw [key m n]
  have e : f (-1) (m + n + 1) = f (m + n - (B - 1)) (B - 1) := by
    rw [key (m + n - (B - 1)) (B - 1)]; congr 1; ring
  rw [e]
  exact hB _ _ (by omega)

/-- **The `(z₁-z₂)ᴺ` cancellation** (the irreducible core of the reconstruction theorem):
a lower-truncated distribution annihilated by `(z₁-z₂)ᴺ` is zero.  Equivalently, `z₁-z₂`
is a non–zero-divisor on `𝒲((z₁))((z₂))` (Gannon §5.1.2; Kac §4).  Proved by induction on
`N`, peeling one `(z₁-z₂)` at a time with `eq_zero_of_mulBySub_of_bddBelow`. -/
theorem eq_zero_of_mulBySubPow_of_bddBelow :
    ∀ (N : ℕ) (f : FormalDist₂ 𝒲), mulBySubPow N f = 0 → IsBddBelow₂ f → f = 0
  | 0, _, hN, _ => by simpa using hN
  | N + 1, f, hN, hbb => by
      have hsub : mulBySub (mulBySubPow N f) = 0 := by
        rw [← LinearMap.comp_apply, ← mulBySubPow_succ]; exact hN
      have hN' : mulBySubPow N f = 0 :=
        eq_zero_of_mulBySub_of_bddBelow hsub (hbb.mulBySubPow N)
      exact eq_zero_of_mulBySubPow_of_bddBelow N f hN' hbb

end VOA
