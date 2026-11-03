/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.StrictSpanning
import VOA.Core.BorcherdsIdentity

/-!
# Gaberdiel–Neitzke Lemma 7 — the identity that removes a repeated mode

From the primary source (`hep-th/0009235`):

> **Lemma 6.**  `V₍₋N₁₎(V₍₋N₂₎(ψ)χ) = ∑_L C(N₂+L−1, L) V₍₋N₂₋L₎(ψ)V₍₋N₁₊L₎(χ)
>   + (−1)^{N₂+1} ∑_L C(N₂+L−1, L) V₍₋N₁₋N₂₋L₎(χ)V₍L₎(ψ)`.
>
> **Lemma 7.**  `V₍₋N₎(ψ)V₍₋N₎(χ) = V₍₋₂N₊₁₎(V₍₋₁₎(ψ)χ) − ∑_{L≥0, L≠N} V₍₋₁₋L₎(ψ)V₍₋₂N₊₁₊L₎(χ)
>   − ∑_{M≥0} V₍₋₂N₋M₎(χ)V₍M₎(ψ)`.  *"This follows from Lemma 6 with `N₁ = 2N−1`, `N₂ = 1`."*

**Lemma 6 is already in the repository**: it is `Core.BorcherdsIdentity.mode_iterate`, the
all-integer Borcherds iterate formula (Gannon 5.1.7d), unconditional.  Specialising `ℓ = −1`
(where `gBinom (−1) i = (−1)^i` cancels the sign) and then isolating the `i = n−1` term gives
Lemma 7 verbatim.

**Lemma 7 is the step that removes a repeated mode index** in GN Prop. 8: on the right-hand side
every surviving mode index is `2n−1` or `> n`, strictly above the repeated `n`.  It is therefore
the algebraic core of the one remaining input to residual **(b)**.

## Main results

* `mode_iterate_neg_one` — GN Lemma 6 at `ℓ = −1`;
* `gn_lemma7` — GN Lemma 7.

## Status
Proved, axiom-clean, `pbw`-free, no `sorry`.
-/

namespace VOA

open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- **GN Lemma 6 at `ℓ = −1`.**  The two signs cancel (`gBinom (−1) i = (−1)^i`), leaving a
plain sum of the two orderings. -/
theorem mode_iterate_neg_one (W : VertexOperatorAlgebra 𝒱) (u v : 𝒱) (N : ℤ) (x : 𝒱) :
    W.smul (W.smul u (-1) v) N x
      = ∑ᶠ i : ℕ, (W.smul u (-1 - (i : ℤ)) (W.smul v (N + (i : ℤ)) x)
          + W.smul v (-1 + N - (i : ℤ)) (W.smul u (i : ℤ) x)) := by
  rw [VertexOperatorAlgebra.mode_iterate W u v (-1) N x]
  refine finsum_congr (fun i => ?_)
  rw [gBinom_neg_one]
  have h1 : ((-1 : ℂ) ^ i * (-1 : ℂ) ^ i) = 1 := by
    rw [← mul_pow]; norm_num
  have h2 : ((-1 : ℂ) ^ ((-1 : ℤ))) = -1 := by norm_num
  rw [h1, one_smul, h2, neg_smul, one_smul, sub_neg_eq_add]

section Lemma7

variable (W : VertexOperatorAlgebra 𝒱)

/-- The first family of Lemma 7 has finite support. -/
theorem gn7_supportA_finite (u v x : 𝒱) (M : ℤ) :
    (Function.support (fun i : ℕ =>
      W.smul u (-1 - (i : ℤ)) (W.smul v (M + (i : ℤ)) x))).Finite := by
  obtain ⟨Nv, hNv⟩ := W.toPreVertexAlgebra.smul_eventually_zero v x
  apply Set.Finite.subset (Set.finite_Iio ((Nv - M).toNat))
  intro i hi
  rw [Function.mem_support] at hi
  by_contra hc
  rw [Set.mem_Iio, not_lt] at hc
  refine hi ?_
  have hge : (Nv - M : ℤ) ≤ (i : ℤ) := by
    rcases le_or_gt 0 (Nv - M) with h0 | h0
    · rw [← Int.toNat_of_nonneg h0]; exact_mod_cast hc
    · omega
  rw [hNv (M + i) (by omega), W.smul_zero_right]

/-- The second family of Lemma 7 has finite support. -/
theorem gn7_supportB_finite (u v x : 𝒱) (M : ℤ) :
    (Function.support (fun i : ℕ =>
      W.smul v (M - (i : ℤ)) (W.smul u (i : ℤ) x))).Finite := by
  obtain ⟨Nu, hNu⟩ := W.toPreVertexAlgebra.smul_eventually_zero u x
  apply Set.Finite.subset (Set.finite_Iio (Nu.toNat))
  intro i hi
  rw [Function.mem_support] at hi
  by_contra hc
  rw [Set.mem_Iio, not_lt] at hc
  refine hi ?_
  have hge : (Nu : ℤ) ≤ (i : ℤ) := by
    rcases le_or_gt 0 Nu with h0 | h0
    · rw [← Int.toNat_of_nonneg h0]; exact_mod_cast hc
    · omega
  rw [hNu i (by omega), W.smul_zero_right]

/-- **Gaberdiel–Neitzke Lemma 7.**  A repeated mode index `n` is removed: on the right every
mode index is either `2n − 1` or strictly larger than `n`. -/
theorem gn_lemma7 (u v x : 𝒱) (n : ℕ) (hn : 1 ≤ n) :
    W.smul u (-(n : ℤ)) (W.smul v (-(n : ℤ)) x)
      = W.smul (W.smul u (-1) v) (-2 * (n : ℤ) + 1) x
        - (∑ᶠ i : ℕ, if i = n - 1 then 0
            else W.smul u (-1 - (i : ℤ)) (W.smul v (-2 * (n : ℤ) + 1 + (i : ℤ)) x))
        - ∑ᶠ i : ℕ, W.smul v (-2 * (n : ℤ) - (i : ℤ)) (W.smul u (i : ℤ) x) := by
  classical
  set A : ℕ → 𝒱 := fun i =>
    W.smul u (-1 - (i : ℤ)) (W.smul v (-2 * (n : ℤ) + 1 + (i : ℤ)) x) with hA
  set B : ℕ → 𝒱 := fun i =>
    W.smul v (-2 * (n : ℤ) - (i : ℤ)) (W.smul u (i : ℤ) x) with hB
  have hfinA : (Function.support A).Finite := gn7_supportA_finite W u v x (-2 * (n : ℤ) + 1)
  have hfinB : (Function.support B).Finite := gn7_supportB_finite W u v x (-2 * (n : ℤ))
  -- Lemma 6 at `ℓ = -1`, `N = -2n+1`
  have hL6 : W.smul (W.smul u (-1) v) (-2 * (n : ℤ) + 1) x = ∑ᶠ i : ℕ, (A i + B i) := by
    rw [mode_iterate_neg_one W u v (-2 * (n : ℤ) + 1) x]
    refine finsum_congr (fun i => ?_)
    rw [hA, hB]
    congr 2
    ring
  -- split off the `i = n-1` term of the `A`-family
  have hAn : A (n - 1) = W.smul u (-(n : ℤ)) (W.smul v (-(n : ℤ)) x) := by
    have hc : (((n - 1 : ℕ)) : ℤ) = (n : ℤ) - 1 := by
      push_cast [Nat.cast_sub hn]; ring
    show W.smul u (-1 - (((n - 1 : ℕ)) : ℤ))
      (W.smul v (-2 * (n : ℤ) + 1 + (((n - 1 : ℕ)) : ℤ)) x)
      = W.smul u (-(n : ℤ)) (W.smul v (-(n : ℤ)) x)
    rw [hc]
    congr 2 <;> ring
  have hite : (Function.support (fun i : ℕ => if i = n - 1 then A i else 0)).Finite := by
    refine Set.Finite.subset (Set.finite_singleton (n - 1)) ?_
    intro i hi
    rw [Function.mem_support] at hi
    by_contra hc
    exact hi (if_neg hc)
  have hite2 : (Function.support (fun i : ℕ => if i = n - 1 then 0 else A i)).Finite := by
    refine Set.Finite.subset hfinA ?_
    intro i hi
    rw [Function.mem_support] at hi ⊢
    by_cases hc : i = n - 1
    · exact absurd (if_pos hc) hi
    · rwa [if_neg hc] at hi
  have hsplitA : ∑ᶠ i : ℕ, A i
      = A (n - 1) + ∑ᶠ i : ℕ, (if i = n - 1 then 0 else A i) := by
    have hdecomp : ∀ i : ℕ, A i
        = (if i = n - 1 then A i else 0) + (if i = n - 1 then 0 else A i) := by
      intro i
      by_cases h : i = n - 1 <;> simp [h]
    rw [finsum_congr hdecomp, finsum_add_distrib hite hite2]
    congr 1
    exact (finsum_eq_single _ (n - 1) (fun i hi => if_neg hi)).trans (if_pos rfl)
  rw [hL6, finsum_add_distrib hfinA hfinB, hsplitA, hAn]
  abel

end Lemma7

end VOA
