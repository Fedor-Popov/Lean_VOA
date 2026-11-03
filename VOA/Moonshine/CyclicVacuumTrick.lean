/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Core.Borcherds

/-!
# Cyclicity from a vacuum-producing pair  (Moonshine step M8f — general lemma)

Let `W` be a vertex operator algebra and `a, b ∈ W` with

  `a₍ₖ₎ b = c·𝟙`  (`c ≠ 0`)   and   `a₍ⱼ₎ b = 0` for `j > k`.

Then **every** `v ∈ W` lies in the span of the iterated products `(v₍ᵢ₎a)₍ⱼ₎ b`
(`mem_span_iterate_of_vacuum`).

*Proof.* Let `N` be such that `v₍ₙ₎ b = 0` for `n ≥ N` (VA5), put `m = max N 0` and apply the
Borcherds identity (`VertexOperatorAlgebra.jacobi`) with `(u, v, x) = (v, a, b)` and indices
`(ℓ, m, n) = (-1-m, m, k)`:

  `∑ᵢ (-1)ⁱ C(ℓ,i) (v₍₋₁₋ᵢ₎ a₍ₖ₊ᵢ₎ b − (-1)^ℓ a₍ℓ₊ₖ₋ᵢ₎ v₍ₘ₊ᵢ₎ b) = ∑ᵢ C(m,i) (v₍ℓ₊ᵢ₎ a)₍ₘ₊ₖ₋ᵢ₎ b`.

On the left only `i = 0` survives (`C(ℓ,i) = 0` for `i < 0`; `a₍ₖ₊ᵢ₎ b = 0` and `v₍ₘ₊ᵢ₎ b = 0` for
`i > 0`; and `v₍ₘ₎ b = 0`), giving `v₍₋₁₎(c𝟙) = c·v`.  The right side is a combination of the
claimed spanning vectors.  ∎

This is the mechanism behind the cyclicity of the frame sector `V₃⁺` over `V₀⁺`
(`Moonshine/CyclicFrameSectors.lean`): with `a = b = x₀ ∈ V₃⁺`, `x₀₍ₖ₎x₀ = c𝟙`, every `v ∈ V₃⁺` is a
combination of `u₍ⱼ₎ x₀` with `u = v₍ᵢ₎x₀ ∈ V₃⁺·V₃⁺ ⊆ V₀⁺`.

## Main results
* `VOA.finsum_mem_submodule_of_forall` — a `finsum` of members of a submodule is a member.
* `VOA.VertexOperatorAlgebra.mem_span_iterate_of_vacuum`.

## Status
`sorry`-free; `#print axioms mem_span_iterate_of_vacuum = [propext, Classical.choice, Quot.sound]`.
Unconditional (the only hypotheses are the displayed ones on `a, b`).
-/

namespace VOA

open Module (End)

universe u

/-- A `finsum` of members of a submodule lies in the submodule (infinite support gives `0`). -/
theorem finsum_mem_submodule_of_forall {ι M : Type*} [AddCommGroup M] [Module ℂ M]
    (p : Submodule ℂ M)
    (f : ι → M) (h : ∀ i, f i ∈ p) : (∑ᶠ i, f i) ∈ p := by
  by_cases hf : (Function.support f).Finite
  · rw [finsum_eq_sum _ hf]
    exact Submodule.sum_mem _ (fun i _ => h i)
  · rw [finsum_of_infinite_support hf]
    exact p.zero_mem

namespace VertexOperatorAlgebra

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- **The vacuum trick.**  If `a₍ₖ₎ b = c·𝟙` with `c ≠ 0` and `a₍ⱼ₎ b = 0` for `j > k`, then every
`v` is a linear combination of the iterated products `(v₍ᵢ₎ a)₍ⱼ₎ b`. -/
theorem mem_span_iterate_of_vacuum (W : VertexOperatorAlgebra 𝒱) {a b : 𝒱} {k : ℤ} {c : ℂ}
    (hc : c ≠ 0) (hk : W.smul a k b = c • W.vacuum)
    (hk' : ∀ j : ℤ, k < j → W.smul a j b = 0) (v : 𝒱) :
    v ∈ Submodule.span ℂ {y | ∃ i j : ℤ, y = W.smul (W.smul v i a) j b} := by
  set S := Submodule.span ℂ {y | ∃ i j : ℤ, y = W.smul (W.smul v i a) j b}
  obtain ⟨N, hN'⟩ := W.regularity v b
  have hN : ∀ n : ℤ, N ≤ n → W.smul v n b = 0 := hN'
  set m : ℤ := max N 0 with hm
  have hJ := jacobi W v a b (-1 - m) m k
  have hL : (∑ᶠ i : ℤ, (negOnePow i * cbz (-1 - m) i) •
      (W.smul v (-1 - m + m - i) (W.smul a (k + i) b)
        - negOnePow (-1 - m) • W.smul a (-1 - m + k - i) (W.smul v (m + i) b))) = c • v := by
    rw [finsum_eq_single _ (0 : ℤ) ?_]
    · have hv0 : W.smul v (m + 0) b = 0 := hN _ (by omega)
      rw [hv0, add_zero, hk, show -1 - m + m - 0 = (-1 : ℤ) by ring, cbz_zero,
        show negOnePow 0 = 1 by simp [negOnePow]]
      simp only [one_mul, one_smul]
      rw [PreVertexAlgebra.smul_smul_right, PreVertexAlgebra.smul_vacuum_neg_one,
        PreVertexAlgebra.smul_zero_right, smul_zero, sub_zero]
    · intro i hi
      rcases lt_or_gt_of_ne hi with h | h
      · rw [cbz_apply_neg _ h, mul_zero, zero_smul]
      · rw [hk' (k + i) (by omega), hN (m + i) (by omega), PreVertexAlgebra.smul_zero_right,
          PreVertexAlgebra.smul_zero_right, smul_zero, sub_zero, smul_zero]
  rw [hL] at hJ
  have hmem : c • v ∈ S := by
    rw [hJ]
    refine finsum_mem_submodule_of_forall S _
      (fun i => Submodule.smul_mem _ _ (Submodule.subset_span ?_))
    exact ⟨-1 - m + i, m + k - i, rfl⟩
  have h2 := Submodule.smul_mem S c⁻¹ hmem
  rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at h2

end VertexOperatorAlgebra

end VOA
