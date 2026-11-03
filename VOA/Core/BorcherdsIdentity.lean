/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Core.OPE
import VOA.Core.Reconstruction
import VOA.Core.SkewSymmetry

/-!
# The Jacobi / Borcherds identity  (Gannon §5.1.3, pp. 320–321)

The locality axiom VA4 can be repackaged as a single master identity, "the Jacobi
identity since it plays an analogous role in VOAs as the Jacobi identity plays in Lie
algebras."

* **Commutator formula** (`ℓ = 0`, eq. 5.1.7c): `[u₍ₘ₎, v₍ₙ₎] = ∑_{i≥0} C(m,i) (u₍ᵢ₎v)₍ₘ₊ₙ₋ᵢ₎`.
* **Iterate / "associativity" formula** (`m = 0`, eq. 5.1.7d):
  `(u₍ℓ₎v)₍ₙ₎ = ∑_{i≥0} (-1)ⁱ C(ℓ,i)(u₍ℓ₋ᵢ₎ v₍ₙ₊ᵢ₎ - (-1)^ℓ v₍ℓ₊ₙ₋ᵢ₎ u₍ᵢ₎)`.
* **Borcherds' identity** (5.1.7b): the coefficient of `z₀^ℓ z₁^m z₂^n`:
  `∑_{i≥0} (-1)ⁱ C(ℓ,i) (u₍ℓ₊ₘ₋ᵢ₎(v₍ₙ₊ᵢ₎) - (-1)^ℓ v₍ℓ₊ₙ₋ᵢ₎(u₍ₘ₊ᵢ₎))`
  `= ∑_{i≥0} C(m,i) (u₍ℓ₊ᵢ₎ v)₍ₘ₊ₙ₋ᵢ₎`.

## Architecture (this file is downstream of the reconstruction cascade)

The structural OPE lemmas (`bracket_deltaSum`, `mode_commutator_structural`) live upstream in
`Core.OPE` (so `Core.Reconstruction` can consume them); this file imports them back, together with
the **proved** duality/iterate cascade `Core.Reconstruction` (`nth_product`, `assoc_nonneg`,
`assoc_neg`, `mode_commutator`, `mode_iterate_borcherds_nonneg`) and skew-symmetry
`Core.SkewSymmetry` (`skew`, `skew_mode`), and assembles the full Jacobi/Borcherds cluster.

## Dependencies
* `Core.OPE`, `Core.Reconstruction`, `Core.SkewSymmetry`.

## What is proved here (`sorry`-free / axiom-free)

* `jacobi_commutator` — **the commutator formula 5.1.7c** (`ℓ = 0`), re-exposed from
  `Core.Reconstruction.mode_commutator`.
* **`mode_iterate`** — **the iterate formula 5.1.7d for ALL `ℓ ∈ ℤ`**.  The `ℓ ≥ 0` branch
  comes from `mode_iterate_borcherds_nonneg`; the **`ℓ < 0` branch** (`mode_iterate_neg`) is
  proved here from the negative duality `assoc_neg` by expanding the normal-ordered product
  `negProd` (`assoc_neg_mode_expand`), splitting the `ℤ`-`finsum` over the diagonal into the
  `m ≥ 0` and `m ≤ -(k+1)` reindexings (`finsum_split_nat_neg`), and matching the
  negative-binomial coefficients term-by-term (`iterate_neg_term`, via `posfac_eq`/`negfac_eq`
  and `gBinom_negsucc`).  This is the genuinely hard `ℓ < 0` case the project had flagged.

## Status
`jacobi_commutator` (5.1.7c) and `mode_iterate` (5.1.7d, **all `ℓ`**, incl. the
hard `ℓ < 0` branch) are proved `sorry`/axiom-free (`#print axioms = [propext, Classical.choice,
Quot.sound]`).  The full arbitrary-`(ℓ,m,n)` **`borcherds` (5.1.7b)** and the master **`jacobi`**
(mode-form of 5.1.7a) are proved in the companion file `Core.Borcherds` (downstream of this
one), axiom-clean — proved NOT by a δ-function calculus but by an `m`-induction on the Pascal
recursion `B(ℓ,m+1,n)=B(ℓ,m,n+1)+B(ℓ+1,m,n)` with two bases (`mode_iterate` at `m=0`,
`mode_commutator` at `ℓ=0`); the `m<0` step is pinned to the `ℓ=0` boundary by an anti-diagonal
argument (`antidiag_pin`).  See `Core.Borcherds`.

## References
* Gannon §5.1.3, eqs. (5.1.7); Frenkel–Lepowsky–Meurman; Lepowsky–Li Ch. 3; Kac.
-/

namespace VOA

open Module (End)
open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace VertexOperatorAlgebra

/-- **The commutator formula 5.1.7c** (Gannon), re-exposed in this file as the `ℓ = 0` slice of
the Borcherds identity: `[u₍ₐ₎, v₍ᵦ₎] = ∑_j C(a,j)·(u₍ⱼ₎v)₍ₐ₊ᵦ₋ⱼ₎` (a finite sum, `N` the
locality bound).  Proved in `Core.Reconstruction.mode_commutator`. -/
theorem jacobi_commutator (W : VertexOperatorAlgebra 𝒱) (u v : 𝒱) (a b : ℤ) :
    ∃ N : ℕ, ⁅mode (W.Y u) a, mode (W.Y v) b⁆
      = ∑ j : Fin N, gBinom a (j : ℕ) • mode (W.Y (W.smul u (j : ℕ) v)) (a + b - (j : ℕ)) :=
  mode_commutator W u v a b

theorem negone_sq_pow (i : ℕ) : (-1 : ℂ) ^ i * (-1 : ℂ) ^ i = 1 := by
  rw [← pow_add, ← two_mul, pow_mul]; norm_num

/-- `(1/k!)·∏_{j<k}(i+1+j) = C(k+i,i) = (-1)^i·gBinom(-(k+1),i)`. -/
theorem posfac_eq (k i : ℕ) :
    (k.factorial : ℂ)⁻¹ * (∏ j ∈ Finset.range k, ((i : ℂ) + 1 + (j : ℂ)))
      = (-1 : ℂ) ^ i * gBinom (-(k:ℤ) - 1) i := by
  rw [gBinom_negsucc, asc_prod_cast i k,
    show (i + k).factorial = (k + i).factorial from by rw [Nat.add_comm]]
  have hfi : (i.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos i).ne'
  have hfk : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
  rw [mul_div_assoc, ← mul_assoc, negone_sq_pow, one_mul]
  field_simp

/-- `(1/k!)·∏_{j<k}(-(k+1)-i+1+j) = (-1)^k·(-1)^i·gBinom(-(k+1),i)`. -/
theorem negfac_eq (k i : ℕ) :
    (k.factorial : ℂ)⁻¹ * (∏ j ∈ Finset.range k, ((-(k:ℂ) - 1 - (i:ℂ)) + 1 + (j : ℂ)))
      = (-1 : ℂ) ^ k * ((-1 : ℂ) ^ i * gBinom (-(k:ℤ) - 1) i) := by
  have hsimp : (∏ j ∈ Finset.range k, ((-(k:ℂ) - 1 - (i:ℂ)) + 1 + (j : ℂ)))
      = ∏ j ∈ Finset.range k, ((-(k:ℂ) - (i:ℂ)) + (j : ℂ)) := by
    apply Finset.prod_congr rfl; intro j _; ring
  rw [hsimp, sing_prod_cast i k, gBinom_negsucc,
    show (i + k).factorial = (k + i).factorial from by rw [Nat.add_comm]]
  have hfi : (i.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos i).ne'
  have hfk : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
  rw [show (-1 : ℂ) ^ i * ((-1) ^ i * ↑(k + i).factorial / (↑k.factorial * ↑i.factorial))
        = ↑(k + i).factorial / (↑k.factorial * ↑i.factorial) from by
      rw [← mul_div_assoc, ← mul_assoc, negone_sq_pow, one_mul]]
  field_simp

/-- Reindex a `ℤ`-`finsum` supported on `m ≤ -(k+1)` to a `ℕ`-`finsum` via `m = -(k+1)-i`. -/
theorem finsum_le_neg_shift (F : ℤ → 𝒱) (k : ℕ)
    (h : ∀ m : ℤ, -(k:ℤ) - 1 < m → F m = 0) :
    (∑ᶠ m : ℤ, F m) = ∑ᶠ i : ℕ, F (-(k:ℤ) - 1 - i) := by
  have hφinj : Function.Injective (fun i : ℕ => (-(k:ℤ) - 1 - (i : ℤ))) := by
    intro a b hab; simp only at hab; omega
  have hsupp : Function.support F ⊆ Set.range (fun i : ℕ => (-(k:ℤ) - 1 - (i : ℤ))) := by
    intro m hm
    rw [Function.mem_support] at hm
    by_contra hcon
    refine hm (h m ?_)
    by_contra hle
    push_neg at hle
    exact hcon ⟨(-(k:ℤ) - 1 - m).toNat, by simp only; omega⟩
  rw [← finsum_mem_of_support_subset' F _ hsupp, finsum_mem_range hφinj]

theorem neg_one_zpow_negsucc (k : ℕ) : (-1 : ℂ) ^ (-(k:ℤ) - 1) = -((-1 : ℂ) ^ k) := by
  rw [show (-(k:ℤ) - 1) = -(((k + 1 : ℕ)) : ℤ) from by push_cast; ring, zpow_neg, zpow_natCast,
    ← inv_pow, inv_neg_one, pow_succ, mul_neg_one]

/-- The combined `(m = i)` + `(m = -(k+1)-i)` term of the `negProd` expansion equals the
Borcherds-iterate summand at index `i`. -/
theorem iterate_neg_term (W : VertexOperatorAlgebra 𝒱) (u v : 𝒱) (k : ℕ) (N : ℤ) (x : 𝒱)
    (i : ℕ) :
    (k.factorial : ℂ)⁻¹ • (normalOrdered ((deriv^[k]) (W.Y u)) (W.Y v) (i : ℤ) (-N-1-i) x
        + normalOrdered ((deriv^[k]) (W.Y u)) (W.Y v) (-(k:ℤ)-1-i) (-N-1-(-(k:ℤ)-1-i)) x)
      = ((-1:ℂ)^i * gBinom (-(k:ℤ)-1) i) •
          (W.smul u (-(k:ℤ)-1-i) (W.smul v (N+i) x)
            - ((-1:ℂ)^(-(k:ℤ)-1)) • W.smul v (-(k:ℤ)-1+N-i) (W.smul u i x)) := by
  -- index identities (End equalities, via `mode_apply`)
  have hu1 : (W.Y u) ((i : ℤ) + k) = mode (W.Y u) (-(k:ℤ) - 1 - i) := by
    rw [mode_apply]; congr 1; ring
  have hv1 : (W.Y v) (-N - 1 - (i:ℤ)) = mode (W.Y v) (N + i) := by
    rw [mode_apply]; congr 1; ring
  have hv2 : (W.Y v) (-N - 1 - (-(k:ℤ) - 1 - i)) = mode (W.Y v) (-(k:ℤ) - 1 + N - i) := by
    rw [mode_apply]; congr 1; ring
  have hu2 : (W.Y u) ((-(k:ℤ) - 1 - i) + (k:ℤ)) = mode (W.Y u) i := by
    rw [mode_apply]; congr 1; ring
  -- expand the two normal-ordered terms
  rw [normalOrdered_apply, if_pos (by exact_mod_cast Nat.zero_le i), Module.End.mul_apply,
    deriv_pow_apply, normalOrdered_apply,
    if_neg (by omega : ¬ (0 : ℤ) ≤ -(k:ℤ) - 1 - i), Module.End.mul_apply, deriv_pow_apply]
  -- convert ℤ-zsmul to ℂ-smul on the End, then apply
  rw [← Int.cast_smul_eq_zsmul ℂ, ← Int.cast_smul_eq_zsmul ℂ, LinearMap.smul_apply,
    LinearMap.smul_apply, hu1, hv1, hv2, hu2]
  simp only [← PreVertexAlgebra.smul_def]
  rw [PreVertexAlgebra.smul_smul_right, smul_add, smul_smul, smul_smul,
    show ((k.factorial:ℂ)⁻¹ * ((∏ j ∈ Finset.range k, ((i:ℤ) + 1 + (j:ℤ)) : ℤ) : ℂ))
        = (-1:ℂ)^i * gBinom (-(k:ℤ)-1) i from by
      rw [Int.cast_prod]; push_cast; exact posfac_eq k i,
    show ((k.factorial:ℂ)⁻¹ * ((∏ j ∈ Finset.range k, ((-(k:ℤ) - 1 - i) + 1 + (j:ℤ)) : ℤ) : ℂ))
        = (-1:ℂ)^k * ((-1:ℂ)^i * gBinom (-(k:ℤ)-1) i) from by
      rw [Int.cast_prod]; push_cast; exact negfac_eq k i]
  rw [smul_sub, neg_one_zpow_negsucc]
  module

/-- Step 1: expand `(u₍₋ₖ₋₁₎v)₍ₙ₎ x` via `assoc_neg` + `negProd`/`nprod`. -/
theorem assoc_neg_mode_expand (W : VertexOperatorAlgebra 𝒱) (u v : 𝒱) (k : ℕ) (N : ℤ) (x : 𝒱) :
    W.smul (W.smul u (-(k:ℤ)-1) v) N x
      = (k.factorial : ℂ)⁻¹ • ∑ᶠ m : ℤ,
          normalOrdered ((deriv^[k]) (W.Y u)) (W.Y v) m (-N-1-m) x := by
  rw [PreVertexAlgebra.smul_def, mode_apply, assoc_neg W u v k, negProd_apply, nprod_apply]

/-- Split a finitely-supported `ℤ`-`finsum`, vanishing on `-(k+1) < m < 0`, into the `m ≥ 0`
part (reindexed `m = i`) plus the `m ≤ -(k+1)` part (reindexed `m = -(k+1)-i`). -/
theorem finsum_split_nat_neg (f : ℤ → 𝒱) (k : ℕ) (hfin : (Function.support f).Finite)
    (hmid : ∀ m : ℤ, -(k:ℤ) - 1 < m → m < 0 → f m = 0) :
    (∑ᶠ m : ℤ, f m) = ∑ᶠ i : ℕ, (f (i : ℤ) + f (-(k:ℤ) - 1 - i)) := by
  classical
  have hfP : (Function.support fun m : ℤ => if 0 ≤ m then f m else 0).Finite :=
    hfin.subset (fun m hm => by
      rw [Function.mem_support] at hm ⊢
      by_cases h : 0 ≤ m
      · rw [if_pos h] at hm; exact hm
      · rw [if_neg h] at hm; exact absurd rfl hm)
  have hfN : (Function.support fun m : ℤ => if 0 ≤ m then 0 else f m).Finite :=
    hfin.subset (fun m hm => by
      rw [Function.mem_support] at hm ⊢
      by_cases h : 0 ≤ m
      · rw [if_pos h] at hm; exact absurd rfl hm
      · rw [if_neg h] at hm; exact hm)
  have hiA : Function.Injective (fun i : ℕ => (i : ℤ)) := Nat.cast_injective
  have hiB : Function.Injective (fun i : ℕ => -(k:ℤ) - 1 - (i : ℤ)) :=
    fun a b hab => by simp only at hab; omega
  have hA : (Function.support fun i : ℕ => f (i : ℤ)).Finite :=
    (hfin.preimage hiA.injOn).subset (fun i hi => by rw [Function.mem_support] at hi; exact hi)
  have hB : (Function.support fun i : ℕ => f (-(k:ℤ) - 1 - i)).Finite :=
    (hfin.preimage hiB.injOn).subset (fun i hi => by rw [Function.mem_support] at hi; exact hi)
  rw [show (∑ᶠ m : ℤ, f m)
        = ∑ᶠ m : ℤ, ((if 0 ≤ m then f m else 0) + (if 0 ≤ m then 0 else f m)) from
      finsum_congr (fun m => by by_cases h : 0 ≤ m <;> simp [h]),
    finsum_add_distrib hfP hfN,
    show (∑ᶠ m : ℤ, if 0 ≤ m then f m else 0) = ∑ᶠ i : ℕ, f (i : ℤ) from
      (finsum_nat_to_int (fun i => f (i : ℤ)) _ (fun p hp => by rw [if_neg (not_le.mpr hp)])
        (fun j => by rw [if_pos (by exact_mod_cast Nat.zero_le j)])).symm,
    show (∑ᶠ m : ℤ, if 0 ≤ m then 0 else f m) = ∑ᶠ i : ℕ, f (-(k:ℤ) - 1 - i) from by
      rw [finsum_le_neg_shift _ k (fun m hm => by
        by_cases h0 : 0 ≤ m
        · rw [if_pos h0]
        · rw [if_neg h0]; exact hmid m hm (not_le.mp h0))]
      exact finsum_congr (fun i => by rw [if_neg (by omega : ¬ (0:ℤ) ≤ -(k:ℤ) - 1 - i)]),
    ← finsum_add_distrib hA hB]

/-- **Borcherds iterate, negative branch** (Gannon 5.1.7d, `ℓ = -(k+1) < 0`). -/
theorem mode_iterate_neg (W : VertexOperatorAlgebra 𝒱) (u v : 𝒱) (k : ℕ) (N : ℤ) (x : 𝒱) :
    W.smul (W.smul u (-(k:ℤ) - 1) v) N x
      = ∑ᶠ i : ℕ, ((-1:ℂ)^i * gBinom (-(k:ℤ)-1) i) •
          (W.smul u (-(k:ℤ)-1-i) (W.smul v (N+i) x)
            - ((-1:ℂ)^(-(k:ℤ)-1)) • W.smul v (-(k:ℤ)-1+N-i) (W.smul u i x)) := by
  rw [assoc_neg_mode_expand]
  set ha := (W.isField_Y u).deriv_iterate k
  set hb := W.isField_Y v
  have hfin : (Function.support fun m : ℤ =>
      normalOrdered ((deriv^[k]) (W.Y u)) (W.Y v) m (-N-1-m) x).Finite :=
    normalOrdered_diag_support_finite ha hb (-N-1) x
  have hmid : ∀ m : ℤ, -(k:ℤ) - 1 < m → m < 0 →
      normalOrdered ((deriv^[k]) (W.Y u)) (W.Y v) m (-N-1-m) x = 0 := by
    intro m hm1 hm2
    rw [normalOrdered_apply, if_neg (not_le.mpr hm2), Module.End.mul_apply, deriv_pow_apply]
    rw [show (∏ j ∈ Finset.range k, (m + 1 + (j:ℤ))) = 0 from
      Finset.prod_eq_zero (i := (-m-1).toNat) (Finset.mem_range.mpr (by omega))
        (by rw [Int.toNat_of_nonneg (by omega)]; ring), zero_smul, LinearMap.zero_apply,
      map_zero]
  have hinjA : Function.Injective (fun i : ℕ => (i : ℤ)) := Nat.cast_injective
  have hinjB : Function.Injective (fun i : ℕ => -(k:ℤ) - 1 - (i : ℤ)) :=
    fun a b hab => by simp only at hab; omega
  have hA : (Function.support fun i : ℕ =>
      normalOrdered ((deriv^[k]) (W.Y u)) (W.Y v) (i:ℤ) (-N-1-(i:ℤ)) x).Finite :=
    (hfin.preimage hinjA.injOn).subset (fun i hi => hi)
  have hB : (Function.support fun i : ℕ =>
      normalOrdered ((deriv^[k]) (W.Y u)) (W.Y v) (-(k:ℤ)-1-(i:ℤ)) (-N-1-(-(k:ℤ)-1-(i:ℤ))) x).Finite :=
    (hfin.preimage hinjB.injOn).subset (fun i hi => hi)
  have hsum_fin : (Function.support fun i : ℕ =>
      normalOrdered ((deriv^[k]) (W.Y u)) (W.Y v) (i:ℤ) (-N-1-(i:ℤ)) x
        + normalOrdered ((deriv^[k]) (W.Y u)) (W.Y v) (-(k:ℤ)-1-(i:ℤ)) (-N-1-(-(k:ℤ)-1-(i:ℤ))) x).Finite := by
    refine (hA.union hB).subset (fun i hi => ?_)
    rw [Function.mem_support] at hi
    by_contra hc
    rw [Set.mem_union, Function.mem_support, Function.mem_support, not_or, not_not, not_not] at hc
    exact hi (by rw [hc.1, hc.2, add_zero])
  rw [finsum_split_nat_neg _ k hfin hmid, smul_finsum' (k.factorial : ℂ)⁻¹ hsum_fin]
  exact finsum_congr (fun i => iterate_neg_term W u v k N x i)

theorem gBinom_natCast_eq_zero {k i : ℕ} (h : k < i) : gBinom (k:ℤ) i = 0 := by
  rw [gBinom, Finset.prod_eq_zero (Finset.mem_range.mpr h) (by push_cast; ring), zero_div]

/-- **The iterate formula (Gannon 5.1.7d), for ALL `ℓ ∈ ℤ`.** -/
theorem mode_iterate (W : VertexOperatorAlgebra 𝒱) (u v : 𝒱) (ℓ N : ℤ) (x : 𝒱) :
    W.smul (W.smul u ℓ v) N x
      = ∑ᶠ i : ℕ, ((-1:ℂ)^i * gBinom ℓ i) •
          (W.smul u (ℓ - i) (W.smul v (N + i) x)
            - ((-1:ℂ)^ℓ) • W.smul v (ℓ + N - i) (W.smul u i x)) := by
  rcases lt_or_ge ℓ 0 with hℓ | hℓ
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, ℓ = -(k:ℤ) - 1 := ⟨(-ℓ - 1).toNat, by omega⟩
    exact mode_iterate_neg W u v k N x
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, ℓ = (k:ℤ) := ⟨ℓ.toNat, by omega⟩
    rw [finsum_eq_finsetSum_of_support_subset _ (s := Finset.range (k + 1)) (by
      intro i hi
      rw [Function.mem_support] at hi
      by_contra hc
      rw [Finset.coe_range, Set.mem_Iio, not_lt] at hc
      exact hi (by rw [gBinom_natCast_eq_zero (by omega : k < i), mul_zero, zero_smul]))]
    have happ := DFunLike.congr_fun (mode_iterate_borcherds_nonneg W u v k N) x
    rw [show W.smul (W.smul u (k:ℤ) v) N x = mode (W.Y (W.smul u (k:ℤ) v)) N x from rfl, happ,
      LinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [LinearMap.smul_apply, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
      Module.End.mul_apply, ← zpow_natCast (-1:ℂ) k]
    simp only [← PreVertexAlgebra.smul_def]

end VertexOperatorAlgebra

end VOA
