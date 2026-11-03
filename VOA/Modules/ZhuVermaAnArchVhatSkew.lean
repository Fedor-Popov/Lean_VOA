/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchVhatDescent
import VOA.Core.SkewSymmetry
import VOA.Foundations.IotaZExpansion
import VOA.Modules.ZhuRingResidue

/-!
# The loop skew identity `VHat.VHatGenSkew` (⟹ `VHatAntisymm`)

This file closes the last remaining obligation of `ZhuVermaAnArchVhatDescent.lean` for antisymmetry
of the Frenkel–Zhu loop Lie algebra `V̂`: the generator-level skew identity `VHatGenSkew`, hence
(via the already-proved reduction `vhatAntisymm_of_genSkew`) the full antisymmetry `VHatAntisymm`.

## The mathematics

`vhatBracket_gen` unfolds the bracket on generators to the Borcherds OPE sum
`⁅u(m), v(k)⁆ = Σᵢ C(m,i)·(u₍ᵢ₎v)(m+k-i)`.  Skew-symmetry of the VOA (Gannon 5.1.8,
`Core.SkewSymmetry.skew_mode`) reads, mode-wise,
`u₍ᵢ₎v = Σⱼ (j!)⁻¹·sgn(-i-1-j)·Tʲ((W.Y v)(-i-1-j) u)`, and `(W.Y v)(-i-1-j) u = v₍ᵢ₊ⱼ₎u`.
Substituting and collapsing the `Tʲ`-tower in `V̂` via `gen_T_pow`
(`gen (Tʲw)(n) = (-1)ʲ·j!·C(n,j)·gen w (n-j)`), every `(j!)⁻¹·(-1)ʲ·j!` cancels and
`sgn(-i-1-j) = -(-1)ⁱ·(-1)ʲ`, so the LHS becomes the *double* generator sum
`-Σᵢ Σⱼ (-1)ⁱ·C(m,i)·C(m+k-i,j)·(v₍ᵢ₊ⱼ₎u)(k+m-(i+j))`.
Grouping by `l := i+j` (a fixed total degree `k+m-l`), the coefficient of `(v₍l₎u)(k+m-l)` is
`-Σᵢ (-1)ⁱ·C(m,i)·C(m+k-i,l-i) = -C(k,l)` — the loop-level analogue of `Core.Skew`.  That matches
`-Σₗ C(k,l)·(v₍l₎u)(k+m-l) = -⁅v(k), u(m)⁆`, which is exactly `VHatGenSkew`.

## The scalar core

The whole deep content is the **signed binomial convolution**
`Σᵢ (-1)ⁱ·C(m,i)·C(m+k-i,l-i) = C(k,l)`  (`cbz_signed_skew_convol`, engine-verified).
It follows from the generalized-binomial Vandermonde (`Foundations.IotaZExpansion.cbz_vandermonde`)
after one **upper-negation** of the *second* factor — in which the running index `i` cancels in the
upper slot (`(l-i)-(m+k-i)-1 = l-m-k-1`), turning the sum into a genuine Vandermonde convolution
`Σᵢ C(m,i)·C(l-m-k-1,l-i) = C(l-k-1,l)`, plus a final upper-negation `C(k,l) = (-1)ˡ·C(l-k-1,l)`.

## Status
Green, `sorry`/axiom-free.  `VHatGenSkew` and `VHatAntisymm` closed unconditionally.

## References
DLM3 §4; H. Li, hep-th/9406211 §2; Gannon §5.1.3 (5.1.8), §5.3.2 Thm 5.3.4.
-/

namespace VOA

open VertexOperatorAlgebra PreVertexAlgebra
open scoped BigOperators
open Finsupp

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace VHat

/-! ## The scalar core: a signed binomial convolution via Vandermonde + upper negation -/

/-- **Upper negation for the generalized binomial product.**
`∏_{i<k}(n-i) = (-1)ᵏ·∏_{i<k}((k-1-n)-i)`: reflecting the range maps each factor `n-i` to
`-((k-1-n)-i)`. -/
theorem gBinom_prod_upper_neg (n : ℤ) (k : ℕ) :
    (∏ i ∈ Finset.range k, ((n : ℂ) - (i : ℂ)))
      = (-1 : ℂ) ^ k * ∏ i ∈ Finset.range k, ((((k : ℤ) - 1 - n : ℤ) : ℂ) - (i : ℂ)) := by
  -- (-1)^k = ∏_{i<k} (-1), then pair the products and reflect the second factor
  rw [show ((-1 : ℂ) ^ k) = ∏ _i ∈ Finset.range k, (-1 : ℂ) from by
        rw [Finset.prod_const, Finset.card_range],
    ← Finset.prod_mul_distrib]
  rw [← Finset.prod_range_reflect
      (fun i => (-1 : ℂ) * ((((k : ℤ) - 1 - n : ℤ) : ℂ) - (i : ℂ))) k]
  refine Finset.prod_congr rfl fun i hi => ?_
  have hi' : i < k := Finset.mem_range.mp hi
  have hik : (((k - 1 - i : ℕ) : ℂ)) = ((k : ℂ) - 1 - (i : ℂ)) := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
  push_cast
  rw [hik]
  ring

/-- **Upper negation for `cbz`** (over an integer lower index `l`):
`cbz n l = (-1)ˡ·cbz (l-n-1) l`.  For `l < 0` both sides vanish; for `l ≥ 0` it is
`gBinom_prod_upper_neg` divided by `l!`. -/
theorem cbz_upper_neg (n l : ℤ) :
    cbz n l = negOnePow l * cbz (l - n - 1) l := by
  rcases lt_or_ge l 0 with hl | hl
  · rw [cbz_apply_neg n hl, cbz_apply_neg (l - n - 1) hl, mul_zero]
  · obtain ⟨L, rfl⟩ := Int.eq_ofNat_of_zero_le hl
    rw [cbz_apply_nonneg n (by exact_mod_cast Nat.zero_le L),
      cbz_apply_nonneg (((L : ℤ)) - n - 1) (by exact_mod_cast Nat.zero_le L),
      negOnePow_natCast, gBinom, gBinom, Int.toNat_natCast]
    rw [gBinom_prod_upper_neg n L]
    rw [show (((L : ℤ) - n - 1 : ℤ)) = (((L : ℤ)) - 1 - n : ℤ) from by ring]
    rw [mul_div_assoc]

/-- **The signed skew binomial convolution** (engine-verified):
`Σᶠ i, (-1)ⁱ·C(m,i)·C(m+k-i,l-i) = C(k,l)`.  Upper-negate the second factor: its upper index
`(l-i)-(m+k-i)-1 = l-m-k-1` is *independent of `i`*, so the sum becomes a Vandermonde convolution
of the two fixed-upper-index families `C(m,·)` and `C(l-m-k-1,·)`. -/
theorem cbz_signed_skew_convol (m k l : ℤ) :
    (∑ᶠ i : ℤ, negOnePow i * (cbz m i * cbz (m + k - i) (l - i))) = cbz k l := by
  -- rewrite each term: (-1)^i · C(m,i) · C(m+k-i, l-i)
  --   = (-1)^i · C(m,i) · (-1)^{l-i} · C(l-m-k-1, l-i)   [upper-neg of 2nd factor]
  --   = (-1)^l · C(m,i) · C(l-m-k-1, l-i).
  have hterm : ∀ i : ℤ,
      negOnePow i * (cbz m i * cbz (m + k - i) (l - i))
        = negOnePow l * (cbz m i * cbz (l - m - k - 1) (l - i)) := by
    intro i
    rw [cbz_upper_neg (m + k - i) (l - i),
      show ((l - i) - (m + k - i) - 1 : ℤ) = (l - m - k - 1 : ℤ) from by ring]
    have hsign : negOnePow i * negOnePow (l - i) = negOnePow l := by
      rw [← negOnePow_add, show i + (l - i) = l from by ring]
    rw [show negOnePow i * (cbz m i * (negOnePow (l - i) * cbz (l - m - k - 1) (l - i)))
          = (negOnePow i * negOnePow (l - i)) * (cbz m i * cbz (l - m - k - 1) (l - i)) from by
        ring, hsign]
  rw [finsum_congr hterm]
  -- pull out (-1)^l, recognize Vandermonde Σᶠ i, C(m,i)·C(l-m-k-1, l-i) = C(m + (l-m-k-1), l)
  rw [← mul_finsum (fun i : ℤ => cbz m i * cbz (l - m - k - 1) (l - i)) (negOnePow l),
    cbz_mul_vandermonde m (l - m - k - 1) l,
    show (m + (l - m - k - 1) : ℤ) = (l - k - 1 : ℤ) from by ring]
  -- C(k,l) = (-1)^l · C(l-k-1, l)
  rw [cbz_upper_neg k l]

/-! ## The generator as a linear map (to commute `gen` through finsums) -/

/-- `gen W · n : 𝒱 →ₗ[ℂ] V̂` packaging `gen W w n = mk W (single n w)` as a `ℂ`-linear map in `w`
(so `map_finsum`/`map_smul` apply to the skew-mode finsum). -/
noncomputable def genL (W : VertexOperatorAlgebra 𝒱) (n : ℤ) : 𝒱 →ₗ[ℂ] VHatCarrier W :=
  (mk W).comp (Finsupp.lsingle n)

@[simp] theorem genL_apply (W : VertexOperatorAlgebra 𝒱) (n : ℤ) (w : 𝒱) :
    genL W n w = gen W w n := rfl

/-! ## The per-`i` skew expansion of a single generator

`gen (u₍ᵢ₎v)(m+k-i)`, after `skew_mode` + the `Tʲ`-collapse `gen_T_pow`, equals a single finsum over
`j` of `gen (v₍ᵢ₊ⱼ₎u)`-generators, with the scalar coefficient `-(-1)ⁱ·C(m+k-i,j)`. -/

/-- `gen W (u₍ᵢ₎v)(m+k-i) = Σᶠ j, (-(-1)ⁱ·C(m+k-i,j))·gen W (v₍ᵢ₊ⱼ₎u)(m+k-i-j)`.
The `sgn(-i-1-j)·(j!)⁻¹·(-1)ʲ·j!` collapses to `-(-1)ⁱ` (independent of `j`), and `gen_T_pow`
supplies the `C(m+k-i,j)` binomial. -/
theorem gen_smul_skew_expand (W : VertexOperatorAlgebra 𝒱) (u v : 𝒱) (m k : ℤ) (i : ℕ) :
    gen W (W.smul u i v) (m + k - i)
      = ∑ᶠ j : ℕ, (-(negOnePow (i : ℤ)) * gBinom (m + k - i) j)
          • gen W (W.smul v ((i : ℤ) + j) u) (m + k - i - j) := by
  -- substitute skew_mode for u₍ᵢ₎v, commute genL through, then collapse the Tʲ-tower
  change genL W (m + k - i) (W.smul u (i : ℤ) v) = _
  rw [skew_mode W u v (i : ℤ),
    map_finsum (genL W (m + k - i)) (skew_support_finite W u v (-(i : ℤ) - 1))]
  refine finsum_congr fun j => ?_
  rw [map_smul, map_smul, genL_apply]
  -- rewrite the inner mode (W.Y v)(-i-1-j) u as v₍ᵢ₊ⱼ₎u and collapse Tʲ on the generator
  have hidx : (W.Y v) (-(i : ℤ) - 1 - (j : ℤ)) u = W.smul v ((i : ℤ) + (j : ℤ)) u := by
    rw [PreVertexAlgebra.smul_def, mode_apply,
      show -((i : ℤ) + (j : ℤ)) - 1 = -(i : ℤ) - 1 - (j : ℤ) from by ring]
  rw [hidx, gen_T_pow W (W.smul v ((i : ℤ) + (j : ℤ)) u) (m + k - i) j,
    show (m + k - (i : ℤ) - (j : ℤ)) = (m + k - i - j) from by push_cast; ring]
  -- combine the three scalar factors:  (j!)⁻¹ • sgn(-i-1-j) • ((-1)ʲ j! C(m+k-i,j)) • (gen …)
  rw [smul_smul, smul_smul]
  congr 1
  -- (j!)⁻¹ · sgn(-i-1-j) · ((-1)ʲ · j! · C(m+k-i,j)) = -(-1)ⁱ · C(m+k-i,j)
  -- First: sgn(-i-1-j) = -(-1)ⁱ·(-1)ʲ  (so the (-1)ʲ from gen_T_pow cancels the sign's j-parity).
  have hone : negOnePow (1 : ℤ) = (-1 : ℂ) := by
    rw [show (1 : ℤ) = ((1 : ℕ) : ℤ) from rfl, negOnePow_natCast]; norm_num
  have hsgn : sgn (-(i : ℤ) - 1 - (j : ℤ)) = -((-1 : ℂ) ^ i) * (-1 : ℂ) ^ j := by
    show negOnePow (-(i : ℤ) - 1 - (j : ℤ)) = _
    rw [show (-(i : ℤ) - 1 - (j : ℤ)) = -((i : ℤ) + 1) + (-(j : ℤ)) from by ring,
      negOnePow_add, negOnePow_neg', negOnePow_neg', negOnePow_add, hone,
      negOnePow_natCast, negOnePow_natCast]
    ring
  have hfacne : ((j.factorial : ℂ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  rw [hsgn, negOnePow_natCast]
  field_simp
  rw [show (((-1 : ℂ) ^ j) ^ 2) = ((-1 : ℂ) ^ 2) ^ j from by rw [← pow_mul, ← pow_mul, Nat.mul_comm],
    neg_one_sq, one_pow]
  ring

/-! ## Trimming the skew finsum to a `Finset.range (2N)` sum keyed by the total degree `l = i+j` -/

/-- The per-`i` skew expansion, **reindexed onto the total degree `l := i+j`** and trimmed to a
*uniform* `Finset.range (2N)` (independent of `i`).  For each `i < N`:
`gBinom m i • gen(u₍ᵢ₎v)(m+k-i)
   = Σ_{l ∈ range (2N)} (gBinom m i · -(-1)ⁱ · cbz (m+k-i) (l-i)) • gen(v₍l₎u)(k+m-l)`.
`cbz (m+k-i)(l-i) = 0` for `l < i`, and `v₍l₎u = 0` for `l ≥ N`, so the padding (the `l`-terms
outside the image of `j ↦ i+j` on `range N`) all vanish. -/
theorem gen_smul_skew_range (W : VertexOperatorAlgebra 𝒱) (u v : 𝒱) (m k : ℤ) (i : ℕ) {N : ℕ}
    (hi : i < N) (hNv : ∀ p : ℕ, N ≤ p → W.smul v p u = 0) :
    (gBinom m i) • gen W (W.smul u i v) (m + k - i)
      = ∑ l ∈ Finset.range (2 * N),
          ((gBinom m i) * (-(negOnePow (i : ℤ)) * cbz (m + k - i) ((l : ℤ) - i)))
            • gen W (W.smul v (l : ℤ) u) (k + m - l) := by
  classical
  have hfin : Function.HasFiniteSupport fun j : ℕ =>
      (-(negOnePow (i : ℤ)) * gBinom (m + k - i) j)
      • gen W (W.smul v ((i : ℤ) + j) u) (m + k - i - j) := by
    refine Set.Finite.subset (Set.finite_Iio N) ?_
    intro j hj
    rw [Function.mem_support] at hj
    rw [Set.mem_Iio]
    by_contra hcon
    rw [not_lt] at hcon
    refine hj ?_
    rw [show W.smul v ((i : ℤ) + (j : ℤ)) u = 0 from by
      rw [show ((i : ℤ) + (j : ℤ)) = ((i + j : ℕ) : ℤ) from by push_cast; ring]
      exact hNv (i + j) (by omega), gen_zero_left, smul_zero]
  rw [gen_smul_skew_expand W u v m k i, smul_finsum' _ hfin]
  -- abbreviation for the l-indexed summand
  set G : ℕ → VHatCarrier W := fun l =>
    ((gBinom m i) * (-(negOnePow (i : ℤ)) * cbz (m + k - i) ((l : ℤ) - i)))
      • gen W (W.smul v (l : ℤ) u) (k + m - l) with hG
  -- the j-finsum is supported on j < N (terms with i+j ≥ N carry v₍i+j₎u = 0)
  have hsupp : (Function.support fun j : ℕ =>
        (gBinom m i) • ((-(negOnePow (i : ℤ)) * gBinom (m + k - i) j)
          • gen W (W.smul v ((i : ℤ) + j) u) (m + k - i - j))) ⊆ Finset.range N := by
    intro j hj
    rw [Function.mem_support] at hj
    rw [Finset.coe_range, Set.mem_Iio]
    by_contra hcon
    rw [not_lt] at hcon
    refine hj ?_
    rw [show W.smul v ((i : ℤ) + (j : ℤ)) u = 0 from by
      rw [show ((i : ℤ) + (j : ℤ)) = ((i + j : ℕ) : ℤ) from by push_cast; ring]
      exact hNv (i + j) (by omega), gen_zero_left, smul_zero, smul_zero]
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  -- the j-th summand equals G (i+j):  match cbz (m+k-i) ((i+j)-i) = gBinom (m+k-i) j and degrees
  have hjterm : ∀ j : ℕ,
      (gBinom m i) • ((-(negOnePow (i : ℤ)) * gBinom (m + k - i) j)
        • gen W (W.smul v ((i : ℤ) + j) u) (m + k - i - j)) = G (i + j) := by
    intro j
    rw [hG]
    simp only
    rw [smul_smul,
      show (((i + j : ℕ) : ℤ) - (i : ℤ)) = (j : ℤ) from by push_cast; ring,
      cbz_apply_nonneg (m + k - i) (by exact_mod_cast Nat.zero_le j), Int.toNat_natCast,
      show (k + m - ((i + j : ℕ) : ℤ)) = (m + k - i - j) from by push_cast; ring,
      show (((i : ℤ) + (j : ℤ))) = (((i + j : ℕ)) : ℤ) from by push_cast; ring]
  rw [Finset.sum_congr rfl (fun j _ => hjterm j)]
  -- reindex j ↦ l = i + j (image is Ico i (i+N) ⊆ range (2N)); pad to range (2N) by zeros
  -- per l, the summand value is 0 outside the image: either cbz = 0 (l<i) or v = 0 (l≥N)
  have hGzero : ∀ l : ℕ, (¬ ∃ j, j < N ∧ i + j = l) → G l = 0 := by
    intro l hl
    simp only [hG]
    rcases lt_or_ge l i with hli | hli
    · rw [cbz_apply_neg (m + k - i) (by exact_mod_cast (by omega : (l : ℤ) - i < 0))]
      simp
    · have hjN : N ≤ l - i := by
        by_contra hc
        exact hl ⟨l - i, by omega, by omega⟩
      rw [show W.smul v (l : ℤ) u = 0 from hNv l (by omega), gen_zero_left, smul_zero]
  -- now: Σ_{j∈range N} G(i+j) = Σ_{l∈range (2N)} G l
  let emb : ℕ ↪ ℕ := ⟨fun j => i + j, fun a b h => by simpa using h⟩
  rw [show (∑ j ∈ Finset.range N, G (i + j))
        = ∑ l ∈ (Finset.range N).map emb, G l from by
      rw [Finset.sum_map]; rfl]
  refine Finset.sum_subset (fun l hl => ?_) (fun l _ hlmap => ?_)
  · rw [Finset.mem_map] at hl
    obtain ⟨j, hj, rfl⟩ := hl
    rw [Finset.mem_range] at hj
    refine Finset.mem_range.mpr ?_
    show i + j < 2 * N
    omega
  · refine hGzero l ?_
    rintro ⟨j, hj, hij⟩
    refine hlmap ?_
    rw [Finset.mem_map]
    exact ⟨j, Finset.mem_range.mpr hj, hij⟩

/-- The signed skew convolution as a `Finset.range` sum (valid once the range covers `[0,l]`,
i.e. `l < N`):  `Σ_{i∈range N} (-1)ⁱ·C(m,i)·cbz(m+k-i)(l-i) = cbz k l`. -/
theorem cbz_signed_skew_convol_range (m k : ℤ) {l : ℤ} {N : ℕ} (hl : l < (N : ℤ)) :
    ∑ i ∈ Finset.range N, negOnePow (i : ℤ) * (cbz m (i : ℤ) * cbz (m + k - i) (l - i)) = cbz k l := by
  rw [← cbz_signed_skew_convol m k l]
  refine (ZhuRes.finsumZ_eq_range_sum (N := N)
    (fun p : ℤ => negOnePow p * (cbz m p * cbz (m + k - p) (l - p))) ?_ ?_).symm
  · intro p hp
    dsimp only
    rw [cbz_apply_neg m hp, zero_mul, mul_zero]
  · intro p hp
    dsimp only
    rw [cbz_apply_neg (m + k - p) (show (l - p) < 0 from by omega), mul_zero, mul_zero]

/-! ## `VHatGenSkew` and `VHatAntisymm` -/

/-- **The generator-level loop skew identity** `VHatGenSkew` (⟹ `VHatAntisymm`).
Substitute `skew_mode` for `u₍ᵢ₎v` in `⁅u(m), v(k)⁆ = Σᵢ C(m,i)·(u₍ᵢ₎v)(m+k-i)`, collapse the
`Tʲ`-tower (`gen_smul_skew_range`), swap the order of summation, and collapse the inner `i`-sum by the
signed binomial convolution `cbz_signed_skew_convol_range` to `-C(k,l)`, matching
`-⁅v(k), u(m)⁆ = -Σₗ C(k,l)·(v₍l₎u)(k+m-l)`. -/
theorem vhatGenSkew (W : VertexOperatorAlgebra 𝒱) (hD : VHat.BracketDescends W) :
    VHatGenSkew W hD := by
  classical
  intro u v m k
  -- choose a uniform bound N: u₍ᵢ₎v = 0 and v₍p₎u = 0 for index ≥ N
  obtain ⟨N1, hN1⟩ := W.smul_eventually_zero u v
  obtain ⟨N2, hN2⟩ := W.smul_eventually_zero v u
  set N : ℕ := (max N1 N2).toNat + 1 with hNdef
  have hNu : ∀ i : ℕ, N ≤ i → W.smul u i v = 0 := fun i hi =>
    hN1 (i : ℤ) (by
      have := le_max_left N1 N2; have := Int.self_le_toNat (max N1 N2)
      have : (N : ℤ) ≤ (i : ℤ) := by exact_mod_cast hi
      omega)
  have hNv : ∀ p : ℕ, N ≤ p → W.smul v p u = 0 := fun p hp =>
    hN2 (p : ℤ) (by
      have := le_max_right N1 N2; have := Int.self_le_toNat (max N1 N2)
      have : (N : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp
      omega)
  -- LHS: expand the bracket and trim to a range-N sum
  rw [vhatBracket_gen W hD u v m k]
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.range N) (by
    intro i hi
    rw [Function.mem_support] at hi
    rw [Finset.coe_range, Set.mem_Iio]
    by_contra hcon
    rw [not_lt] at hcon
    exact hi (by rw [hNu i hcon, gen_zero_left, smul_zero]))]
  -- replace each i-summand by its skew expansion (a range-(2N) l-sum)
  rw [Finset.sum_congr rfl (fun i hi =>
    gen_smul_skew_range W u v m k i (Finset.mem_range.mp hi) hNv)]
  -- swap the two finite sums
  rw [Finset.sum_comm]
  -- RHS: expand and trim to a range-(2N) sum
  rw [vhatBracket_gen W hD v u k m]
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.range (2 * N)) (by
    intro l hl
    rw [Function.mem_support] at hl
    rw [Finset.coe_range, Set.mem_Iio]
    by_contra hcon
    rw [not_lt] at hcon
    exact hl (by rw [hNv l (by omega), gen_zero_left, smul_zero]))]
  rw [← Finset.sum_neg_distrib]
  -- termwise (over l): the inner i-sum of scalars collapses to -C(k,l) on the same generator
  refine Finset.sum_congr rfl fun l hl => ?_
  have hlN : (l : ℤ) < (N : ℤ) ∨ (N : ℤ) ≤ (l : ℤ) := lt_or_ge _ _
  -- factor the inner i-sum's scalar out of the common generator gen(v₍l₎u)(k+m-l)
  rw [← Finset.sum_smul,
    show (k + m - (l : ℤ)) = (m + k - l) from by ring]
  rcases hlN with hlN | hlN
  · -- l < N: the i-sum of scalars equals -C(k,l)
    congr 1
    rw [show (∑ i ∈ Finset.range N,
            (gBinom m i) * (-(negOnePow (i : ℤ)) * cbz (m + k - i) ((l : ℤ) - i)))
          = - ∑ i ∈ Finset.range N,
              negOnePow (i : ℤ) * (cbz m (i : ℤ) * cbz (m + k - i) ((l : ℤ) - i)) from by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [cbz_apply_nonneg m (by exact_mod_cast Nat.zero_le i), Int.toNat_natCast]
        ring,
      cbz_signed_skew_convol_range m k hlN,
      cbz_apply_nonneg k (by exact_mod_cast (by omega : (0 : ℤ) ≤ l)), Int.toNat_natCast,
      neg_smul]
  · -- l ≥ N: gen(v₍l₎u)(k+m-l) = 0, both sides vanish
    rw [show W.smul v (l : ℤ) u = 0 from hNv l (by exact_mod_cast hlN), gen_zero_left,
      smul_zero, smul_zero, neg_zero]

/-- **`VHatAntisymm` for `V̂`** — closed via the proved reduction `vhatAntisymm_of_genSkew`. -/
theorem vhatAntisymm (W : VertexOperatorAlgebra 𝒱) (hD : VHat.BracketDescends W) :
    VHat.VHatAntisymm W hD :=
  vhatAntisymm_of_genSkew W hD (vhatGenSkew W hD)

end VHat

end VOA
