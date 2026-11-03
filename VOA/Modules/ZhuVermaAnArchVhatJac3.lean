/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchVhatJac2
import VOA.Modules.ZhuRingResidue
import VOA.Modules.ZhuVermaAnArchVhatSkew

/-!
# Closing the depth-graded loop-Jacobi crux `VHat.GenJacobiDepth`

`ZhuVermaAnArchVhatJac2.lean` reduced the loop-bracket Jacobi `VHat.VHatLeibniz` (the `LieRing (V̂)`
Jacobi input) to the **single per-total-degree generator identity** `VHat.GenJacobiDepth` — the
depth-graded slice of the master Borcherds identity `Core.Borcherds.jacobi` (Gannon 5.1.7b).  This
file discharges `GenJacobiDepth` **unconditionally and axiom-free**, and proves the resulting
unconditional `LieRing`/`LieAlgebra` structure on `V̂`.

## The mathematics

Fix a depth `s` and the common loop degree `D = m+k+l-s`.  Reindex the depth-`s` antidiagonal
slices so all OPE products land at degree `D`.  Subtracting the cyclic term `RHS2` from `LHS`
collects, on the antidiagonal `i+j=s`, the **mode commutator** `a₍ᵢ₎(b₍ⱼ₎c) − b₍ⱼ₎(a₍ᵢ₎c)`.
The `ℓ=0` slice of `Core.Borcherds.jacobi` (with inner vector `x := c`) evaluates this commutator:
`a₍ᵢ₎(b₍ⱼ₎c) − b₍ⱼ₎(a₍ᵢ₎c) = Σ_t C(i,t)·(a₍ₜ₎b)₍ᵢ₊ⱼ₋ₜ₎c = Σ_t C(i,t)·(a₍ₜ₎b)₍ₛ₋ₜ₎c`.
Wrapping in `gen(·)(D)`, swapping the two finite sums, and collapsing the inner antidiagonal sum by
the scalar Vandermonde core
`Σ_{i+j=s} C(m,i)·C(k,j)·C(i,t) = C(m,t)·C(m+k−t,s−t)`  (`cbz_genJacobi_core`, engine-verified)
turns `LHS − RHS2` into exactly `RHS1` (reindexed `i ↦ t`, `p ↦ s−t`).  That is `GenJacobiDepth`.

## The scalar core

`cbz_genJacobi_core` is the genuine combinatorial residual.  It follows from the
subset-of-subset identity `C(m,i)·C(i,t) = C(m,t)·C(m−t,i−t)` (`cbz_subsetOfSubset`) plus the
generalized-binomial Vandermonde `Foundations.IotaZExpansion.cbz_mul_vandermonde`.

## Status
Green, `sorry`/axiom-free.  `GenJacobiDepth` closed unconditionally; `VHat.VHatLeibniz` and the
unconditional `LieRing`/`LieAlgebra (V̂)` follow.

## References
DLM3 §4; Gannon §5.1.3 (5.1.7b/c), §5.3.2 Thm 5.3.4; `Core.Borcherds.jacobi`.
-/

namespace VOA

open VertexOperatorAlgebra PreVertexAlgebra
open scoped BigOperators
open Finsupp

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace VHat

/-! ## The scalar Vandermonde core -/

/-- The falling factorial `fall n k = ∏_{r<k}(n−r)` splits at `t`:
`fall m (t+u) = fall m t · fall (m−t) u`. -/
theorem fall_split (m : ℤ) (t u : ℕ) :
    (∏ r ∈ Finset.range (t + u), ((m : ℂ) - (r : ℂ)))
      = (∏ r ∈ Finset.range t, ((m : ℂ) - (r : ℂ)))
          * ∏ r ∈ Finset.range u, (((m - (t : ℤ) : ℤ) : ℂ) - (r : ℂ)) := by
  rw [Finset.prod_range_add (fun r => ((m : ℂ) - (r : ℂ))) t u]
  congr 1
  refine Finset.prod_congr rfl fun r _ => ?_
  push_cast; ring

/-- `fall i t · (i−t)! = i!` (for `t ≤ i`): the falling factorial closes to a factorial ratio. -/
theorem fall_self_mul (i t : ℕ) (hti : t ≤ i) :
    (∏ r ∈ Finset.range t, ((i : ℂ) - (r : ℂ))) * ((i - t).factorial : ℂ)
      = (i.factorial : ℂ) := by
  -- `gBinom i t · t! = fall i t` and `C(i,t)·t!·(i-t)! = i!` since `C(i,t)=choose(i,t)` for nat i.
  have ht : ((t.factorial : ℂ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero t
  -- fall i t = t! · gBinom i t = t! · choose i t (matching casts)
  have hprod : (∏ r ∈ Finset.range t, ((i : ℂ) - (r : ℂ)))
      = ((t.factorial : ℂ)) * (Nat.choose i t : ℂ) := by
    have h := gBinom_mul_factorial (i : ℤ) t
    rw [gBinom_natCast_eq_choose hti] at h
    rw [show (∏ r ∈ Finset.range t, ((i : ℂ) - (r : ℂ)))
          = ∏ r ∈ Finset.range t, (((i : ℤ) : ℂ) - (r : ℂ)) from by push_cast; ring]
    rw [← h]
  rw [hprod]
  have hfac := Nat.choose_mul_factorial_mul_factorial hti  -- choose i t * t! * (i-t)! = i!
  have hcast : ((t.factorial : ℂ)) * (Nat.choose i t : ℂ) * ((i - t).factorial : ℂ)
      = (i.factorial : ℂ) := by
    have := congrArg (Nat.cast : ℕ → ℂ) hfac
    push_cast at this; linear_combination this
  linear_combination hcast

/-- **Subset-of-subset for `gBinom`** (integer `m`, naturals `i t` with `t ≤ i`):
`C(m,i)·C(i,t) = C(m,t)·C(m−t,i−t)`.  Proved from the falling-factorial product form. -/
theorem cbz_subsetOfSubset (m : ℤ) {i t : ℕ} (hti : t ≤ i) :
    gBinom m i * gBinom (i : ℤ) t = gBinom m t * gBinom (m - (t : ℤ)) (i - t) := by
  have hfi : ((i.factorial : ℂ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
  have hft : ((t.factorial : ℂ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero t
  have hfit : (((i - t).factorial : ℂ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (i - t)
  -- the four falling-product identities for the gBinoms involved
  have eA : ((i.factorial : ℂ)) * gBinom m i = ∏ r ∈ Finset.range i, ((m : ℂ) - (r : ℂ)) :=
    gBinom_mul_factorial m i
  have eB : ((t.factorial : ℂ)) * gBinom (i : ℤ) t
      = ∏ r ∈ Finset.range t, ((i : ℂ) - (r : ℂ)) := by
    rw [gBinom_mul_factorial (i : ℤ) t]; push_cast; ring
  have eC : ((t.factorial : ℂ)) * gBinom m t = ∏ r ∈ Finset.range t, ((m : ℂ) - (r : ℂ)) :=
    gBinom_mul_factorial m t
  have eD : (((i - t).factorial : ℂ)) * gBinom (m - (t : ℤ)) (i - t)
      = ∏ r ∈ Finset.range (i - t), (((m - (t : ℤ) : ℤ) : ℂ) - (r : ℂ)) :=
    gBinom_mul_factorial (m - (t : ℤ)) (i - t)
  -- fall m i splits at t (using i = t + (i-t))
  have eSplit : (∏ r ∈ Finset.range i, ((m : ℂ) - (r : ℂ)))
      = (∏ r ∈ Finset.range t, ((m : ℂ) - (r : ℂ)))
          * ∏ r ∈ Finset.range (i - t), (((m - (t : ℤ) : ℤ) : ℂ) - (r : ℂ)) := by
    conv_lhs => rw [show i = t + (i - t) from by omega]
    rw [fall_split m t (i - t)]
  -- fall i t · (i-t)! = i!
  have eSelf := fall_self_mul i t hti
  -- now establish the identity after clearing t!·(i-t)!·i!  (all nonzero)
  refine mul_left_cancel₀ hfi (mul_left_cancel₀ hft (mul_left_cancel₀ hfit ?_))
  -- transform goal into a polynomial identity in the falling products
  have key :
      ((i - t).factorial : ℂ) * (((t.factorial : ℂ)) * (((i.factorial : ℂ))
          * (gBinom m i * gBinom (i : ℤ) t)))
      = ((i - t).factorial : ℂ) * (((t.factorial : ℂ)) * (((i.factorial : ℂ))
          * (gBinom m t * gBinom (m - (t : ℤ)) (i - t)))) := by
    -- LHS = (i!·C(m,i))·(t!·C(i,t))·(i-t)! = fall m i · fall i t · (i-t)!
    -- RHS = (i!) · (t!·C(m,t)) · ((i-t)!·C(m-t,i-t)) = i! · fall m t · fall (m-t)(i-t)
    have hL : ((i - t).factorial : ℂ) * (((t.factorial : ℂ)) * (((i.factorial : ℂ))
          * (gBinom m i * gBinom (i : ℤ) t)))
        = (((i.factorial : ℂ)) * gBinom m i)
            * (((t.factorial : ℂ)) * gBinom (i : ℤ) t) * ((i - t).factorial : ℂ) := by ring
    have hR : ((i - t).factorial : ℂ) * (((t.factorial : ℂ)) * (((i.factorial : ℂ))
          * (gBinom m t * gBinom (m - (t : ℤ)) (i - t))))
        = ((i.factorial : ℂ)) * (((t.factorial : ℂ)) * gBinom m t)
            * ((((i - t).factorial : ℂ)) * gBinom (m - (t : ℤ)) (i - t)) := by ring
    rw [hL, hR, eA, eB, eC, eD]
    rw [eSplit]
    -- goal: fall m t · fall (m-t)(i-t) · (fall i t) · (i-t)! = i! · fall m t · fall(m-t)(i-t)
    -- close by substituting fall i t · (i-t)! = i! (= eSelf)
    linear_combination ((∏ r ∈ Finset.range t, ((m : ℂ) - (r : ℂ)))
        * ∏ r ∈ Finset.range (i - t), (((m - (t : ℤ) : ℤ) : ℂ) - (r : ℂ))) * eSelf
  -- conclude: the remaining goal is exactly `key` up to commutativity
  linear_combination key

/-- **The scalar Vandermonde core (engine-verified).**
`Σ_{i+j=s} C(m,i)·C(k,j)·C(i,t) = C(m,t)·C(m+k−t,s−t)` for integer `m k`, naturals `s`, `t ≤ s`. -/
theorem cbz_genJacobi_core (m k : ℤ) (s t : ℕ) (hts : t ≤ s) :
    (∑ q ∈ Finset.antidiagonal s, gBinom m q.1 * gBinom k q.2 * gBinom (q.1 : ℤ) t)
      = gBinom m t * gBinom (m + k - (t : ℤ)) (s - t) := by
  classical
  -- convert the antidiagonal to a `range (s+1)` sum over `i ↦ (i, s-i)`
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => gBinom m i * gBinom k j * gBinom (i : ℤ) t) s]
  -- term-wise: for i < t, gBinom i t = 0; for i ≥ t, subset-of-subset.
  -- rewrite each term using cbz so we can pull out gBinom m t and apply vandermonde_range
  have hterm : ∀ i ∈ Finset.range (s + 1),
      gBinom m i * gBinom k (s - i) * gBinom (i : ℤ) t
        = gBinom m t * (cbz (m - (t : ℤ)) ((i : ℤ) - (t : ℤ)) * cbz k ((s : ℤ) - (i : ℤ))) := by
    intro i hi
    have his : i ≤ s := by have := Finset.mem_range.mp hi; omega
    rcases lt_or_ge i t with hit | hit
    · -- i < t : both gBinom i t = 0 (since i < t) and cbz (m-t)(i-t) = 0 (i-t < 0)
      rw [gBinom_natCast_eq_zero hit, mul_zero,
        cbz_apply_neg (m - (t : ℤ)) (by exact_mod_cast (by omega : (i : ℤ) - t < 0)),
        zero_mul, mul_zero]
    · -- i ≥ t : subset-of-subset, then express both shifted gBinoms as cbz
      rw [show gBinom m i * gBinom k (s - i) * gBinom (i : ℤ) t
            = gBinom k (s - i) * (gBinom m i * gBinom (i : ℤ) t) from by ring,
        cbz_subsetOfSubset m hit]
      -- gBinom (m-t) (i-t) = cbz (m-t) (i-t)  (nonneg index, with Nat-to-Int sub matching)
      rw [cbz_apply_nonneg (m - (t : ℤ)) (by exact_mod_cast (by omega : (0 : ℤ) ≤ (i : ℤ) - t)),
        show ((i : ℤ) - (t : ℤ)).toNat = i - t from by omega,
        cbz_apply_nonneg k (by exact_mod_cast (by omega : (0 : ℤ) ≤ (s : ℤ) - i)),
        show ((s : ℤ) - (i : ℤ)).toNat = s - i from by omega]
      ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  congr 1
  -- Inner sum:  Σ_{i∈range(s+1)} cbz (m-t)(i-t) · cbz k (s-i)  = gBinom (m-t+k) (s-t)
  rw [show (m + k - (t : ℤ)) = ((m - (t : ℤ)) + k) from by ring]
  rw [show gBinom ((m - (t : ℤ)) + k) (s - t) = cbz ((m - (t : ℤ)) + k) ((s : ℤ) - (t : ℤ)) from by
    rw [cbz_apply_nonneg _ (by exact_mod_cast (by omega : (0 : ℤ) ≤ (s : ℤ) - t)),
      show ((s : ℤ) - (t : ℤ)).toNat = s - t from by omega]]
  -- Pass the finite `range (s+1)` sum to the all-ℤ finsum with running integer index `p = i`.
  rw [show (∑ i ∈ Finset.range (s + 1),
        cbz (m - (t : ℤ)) ((i : ℤ) - (t : ℤ)) * cbz k ((s : ℤ) - (i : ℤ)))
      = ∑ᶠ p : ℤ, cbz (m - (t : ℤ)) (p - (t : ℤ)) * cbz k ((s : ℤ) - p) from by
    refine (ZhuRes.finsumZ_eq_range_sum
        (fun p : ℤ => cbz (m - (t : ℤ)) (p - (t : ℤ)) * cbz k ((s : ℤ) - p)) (N := s + 1)
        (fun p hp => by
          dsimp only
          rw [cbz_apply_neg (m - (t : ℤ)) (by omega : p - (t : ℤ) < 0), zero_mul])
        (fun p hp => by
          dsimp only
          rw [cbz_apply_neg k (by push_cast at hp ⊢; omega : (s : ℤ) - p < 0), mul_zero])).symm]
  -- shift the integer index `p ↦ q + t`, turning it into the bare Vandermonde at degree (s-t).
  rw [← cbz_mul_vandermonde (m - (t : ℤ)) k ((s : ℤ) - (t : ℤ))]
  rw [← finsum_comp_equiv (Equiv.addRight (t : ℤ))]
  refine finsum_congr fun q => ?_
  simp only [Equiv.coe_addRight]
  congr 2 <;> ring

/-! ## The `ℓ=0` mode commutator (clean vector form of `Core.Borcherds.jacobi`) -/

/-- **Mode commutator, vector form** (the `ℓ=0` slice of `Core.Borcherds.jacobi`, with the inner
vector `x := c`):
`a₍M₎(b₍ₙ₎c) − b₍ₙ₎(a₍M₎c) = Σᶠ_t C(M,t)·(a₍ₜ₎b)₍M₊ₙ₋ₜ₎c`  for all integers `M, n`.
The LHS Jacobi finsum collapses on the `δ`-row `cbz 0 i = δ_{i0}`. -/
theorem mode_commutator_vec (W : VertexOperatorAlgebra 𝒱) (a b c : 𝒱) (M n : ℤ) :
    W.smul a M (W.smul b n c) - W.smul b n (W.smul a M c)
      = ∑ᶠ t : ℤ, cbz M t • W.smul (W.smul a t b) (M + n - t) c := by
  have hj := jacobi W a b c 0 M n
  -- collapse the LHS Jacobi finsum to the `i = 0` term
  have hn0 : negOnePow (0 : ℤ) = (1 : ℂ) := by simp [negOnePow]
  rw [show (∑ᶠ i : ℤ, (negOnePow i * cbz 0 i) •
        (W.smul a (0 + M - i) (W.smul b (n + i) c)
          - negOnePow 0 • W.smul b (0 + n - i) (W.smul a (M + i) c)))
      = W.smul a M (W.smul b n c) - W.smul b n (W.smul a M c) from by
    rw [finsum_eq_single _ (0 : ℤ) (fun i hi => by
      rw [cbz_zero_left, if_neg hi, mul_zero, zero_smul])]
    rw [cbz_zero_left, if_pos rfl, mul_one, hn0, one_smul, one_smul]
    rw [show (0 + M - 0 : ℤ) = M from by ring, show (n + 0 : ℤ) = n from by ring,
      show (0 + n - 0 : ℤ) = n from by ring, show (M + 0 : ℤ) = M from by ring]] at hj
  -- rewrite the RHS `cbz`/`ℓ+i` into the stated form (ℓ = 0)
  rw [hj]
  refine finsum_congr fun t => ?_
  simp only [zero_add]

/-! ## `gen` as a linear map (to commute `gen` through the commutator finsum) -/

/-- `gen W · n : 𝒱 →ₗ[ℂ] V̂`, packaging `gen W w n = mk W (single n w)` as a linear map in `w`. -/
noncomputable def genLM (W : VertexOperatorAlgebra 𝒱) (n : ℤ) : 𝒱 →ₗ[ℂ] VHatCarrier W :=
  (mk W).comp (Finsupp.lsingle n)

@[simp] theorem genLM_apply (W : VertexOperatorAlgebra 𝒱) (n : ℤ) (w : 𝒱) :
    genLM W n w = gen W w n := rfl

/-! ## Per-`q` commutator wrapping at the common loop degree -/

/-- The commutator-finsum is finitely supported (for `genLM` wrapping). -/
theorem commVec_gen_support_finite (W : VertexOperatorAlgebra 𝒱) (a b c : 𝒱) (M n D : ℤ) :
    (Function.support fun t : ℤ =>
      cbz M t • gen W (W.smul (W.smul a t b) (M + n - t) c) D).Finite := by
  classical
  -- support: `t ≥ 0` (else cbz = 0) and `t < N(a,b)` (else `a₍ₜ₎b = 0`).
  obtain ⟨Nab, hNab⟩ := W.smul_eventually_zero a b
  refine Set.Finite.subset (Set.finite_Icc (0 : ℤ) Nab) ?_
  intro t ht
  rw [Function.mem_support] at ht
  rw [Set.mem_Icc]
  refine ⟨?_, ?_⟩
  · by_contra h
    exact ht (by rw [cbz_apply_neg M (by omega), zero_smul])
  · by_contra h
    exact ht (by
      rw [show W.smul a t b = 0 from hNab t (by omega), W.smul_zero_left,
        gen_zero_left, smul_zero])

/-- **Per-`q` commutator at degree `D`.**  Wrapping `mode_commutator_vec` in `genLM W D`:
`gen(a₍M₎(b₍ₙ₎c))(D) − gen(b₍ₙ₎(a₍M₎c))(D) = Σᶠ_t cbz M t • gen((a₍ₜ₎b)₍M₊ₙ₋ₜ₎c)(D)`. -/
theorem gen_commutator (W : VertexOperatorAlgebra 𝒱) (a b c : 𝒱) (M n D : ℤ) :
    gen W (W.smul a M (W.smul b n c)) D - gen W (W.smul b n (W.smul a M c)) D
      = ∑ᶠ t : ℤ, cbz M t • gen W (W.smul (W.smul a t b) (M + n - t) c) D := by
  have h := congrArg (genLM W D) (mode_commutator_vec W a b c M n)
  rw [map_sub, genLM_apply, genLM_apply] at h
  rw [h, map_finsum (genLM W D) ?_]
  · refine finsum_congr fun t => ?_
    rw [map_smul, genLM_apply]
  · -- finiteness of the pre-image family
    obtain ⟨Nab, hNab⟩ := W.smul_eventually_zero a b
    classical
    refine Set.Finite.subset (Set.finite_Icc (0 : ℤ) Nab) ?_
    intro t ht
    rw [Function.mem_support] at ht
    rw [Set.mem_Icc]
    refine ⟨?_, ?_⟩
    · by_contra hh
      exact ht (by rw [cbz_apply_neg M (by omega), zero_smul])
    · by_contra hh
      exact ht (by
        rw [show W.smul a t b = 0 from hNab t (by omega),
          W.smul_zero_left, smul_zero])

/-! ## Closing `GenJacobiDepth` -/

/-- A module-valued version of `ZhuRes.finsumZ_eq_range_sum`: an `ℤ`-finsum into any
`AddCommMonoid` collapses to a `range N` sum when the summand vanishes off `[0, N)`. -/
theorem finsumZ_eq_range_sum_mod {M : Type*} [AddCommMonoid M] (F : ℤ → M) {N : ℕ}
    (hlo : ∀ p : ℤ, p < 0 → F p = 0) (hhi : ∀ p : ℤ, (N : ℤ) ≤ p → F p = 0) :
    ∑ᶠ p : ℤ, F p = ∑ i ∈ Finset.range N, F (i : ℤ) := by
  classical
  have hsubset : Function.support F ⊆ ↑((Finset.range N).map ⟨(Int.ofNat ·), by
      intro a b h; simpa using h⟩) := by
    intro p hp
    rw [Function.mem_support] at hp
    have hp0 : 0 ≤ p := by by_contra h; exact hp (hlo p (by omega))
    have hpN : p < (N : ℤ) := by by_contra h; exact hp (hhi p (by omega))
    simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe, Finset.mem_range,
      Function.Embedding.coeFn_mk]
    exact ⟨p.toNat, by omega, by simp [Int.toNat_of_nonneg hp0]⟩
  rw [finsum_eq_finsetSum_of_support_subset F hsubset, Finset.sum_map]
  rfl

/-- The scalar core in the reflected `range (s+1)` shape used by the assembly:
`Σ_{j≤s} C(k,j)·C(m,s−j)·C(s−j,t) = C(m,t)·C(m+k−t,s−t)`  (`t ≤ s`). -/
theorem cbz_genJacobi_core_range (m k : ℤ) (s t : ℕ) (hts : t ≤ s) :
    (∑ j ∈ Finset.range (s + 1), gBinom k j * gBinom m (s - j) * gBinom ((s - j : ℕ) : ℤ) t)
      = gBinom m t * gBinom (m + k - (t : ℤ)) (s - t) := by
  rw [← cbz_genJacobi_core m k s t hts]
  -- antidiagonal sum  Σ_q C(m,q.1)C(k,q.2)C(q.1,t)  via range (q.1 = i, q.2 = s-i)
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => gBinom m i * gBinom k j * gBinom (i : ℤ) t) s]
  -- reflect i ↦ s - i to match the C(k,j)·C(m,s-j)·C(s-j,t) shape
  rw [← Finset.sum_range_reflect
      (fun i => gBinom m i * gBinom k (s - i) * gBinom (i : ℤ) t) (s + 1)]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjs : j ≤ s := by have := Finset.mem_range.mp hj; omega
  rw [show s + 1 - 1 - j = s - j from by omega, show ((s - (s - j) : ℕ)) = j from by omega]
  ring

/-- The depth-`s` LHS slice as a `range (s+1)` sum at the common degree `D = m+k+l-s`. -/
theorem genJacobi_lhs_range (W : VertexOperatorAlgebra 𝒱) (a b c : 𝒱) (m k l : ℤ) (s : ℕ) :
    (∑ q ∈ Finset.antidiagonal s, (gBinom k q.1) • (gBinom m q.2) •
        gen W (W.smul a q.2 (W.smul b q.1 c)) (m + (k + l - q.1) - q.2))
      = ∑ j ∈ Finset.range (s + 1), (gBinom k j) • (gBinom m (s - j)) •
          gen W (W.smul a ((s - j : ℕ) : ℤ) (W.smul b j c)) (m + k + l - (s : ℤ)) := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun j i => (gBinom k j) • (gBinom m i) •
        gen W (W.smul a (i : ℤ) (W.smul b j c)) (m + (k + l - (j : ℤ)) - (i : ℤ))) s]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjs : j ≤ s := by have := Finset.mem_range.mp hj; omega
  rw [show m + (k + l - (j : ℤ)) - (((s - j : ℕ)) : ℤ) = m + k + l - (s : ℤ) from by
    rw [show (((s - j : ℕ)) : ℤ) = (s : ℤ) - (j : ℤ) from by
      rw [Nat.cast_sub hjs]]; ring]

/-- The depth-`s` RHS2 (cyclic) slice as a `range (s+1)` sum, **reindexed** (`i ↦ s−i`) and at the
common degree, so it aligns term-wise with the LHS as a commutator. -/
theorem genJacobi_rhs2_range (W : VertexOperatorAlgebra 𝒱) (a b c : 𝒱) (m k l : ℤ) (s : ℕ) :
    (∑ q ∈ Finset.antidiagonal s, (gBinom m q.1) • (gBinom k q.2) •
        gen W (W.smul b q.2 (W.smul a q.1 c)) (k + (m + l - q.1) - q.2))
      = ∑ j ∈ Finset.range (s + 1), (gBinom k j) • (gBinom m (s - j)) •
          gen W (W.smul b j (W.smul a ((s - j : ℕ) : ℤ) c)) (m + k + l - (s : ℤ)) := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i p => (gBinom m i) • (gBinom k p) •
        gen W (W.smul b (p : ℤ) (W.smul a (i : ℤ) c)) (k + (m + l - (i : ℤ)) - (p : ℤ))) s]
  rw [← Finset.sum_range_reflect
      (fun i => (gBinom m i) • (gBinom k (s - i)) •
        gen W (W.smul b ((s - i : ℕ) : ℤ) (W.smul a (i : ℤ) c))
          (k + (m + l - (i : ℤ)) - (((s - i : ℕ)) : ℤ))) (s + 1)]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjs : j ≤ s := by have := Finset.mem_range.mp hj; omega
  -- index after reflect: i = s + 1 - 1 - j = s - j
  rw [show s + 1 - 1 - j = s - j from by omega]
  -- now both indices are `s - j`; rewrite the OPE indices and degree
  rw [show ((s - (s - j) : ℕ)) = j from by omega]
  rw [show k + (m + l - (((s - j : ℕ)) : ℤ)) - ((j : ℤ)) = m + k + l - (s : ℤ) from by
    rw [show (((s - j : ℕ)) : ℤ) = (s : ℤ) - (j : ℤ) from by rw [Nat.cast_sub hjs]]; ring]
  rw [smul_comm (gBinom m (s - j)) (gBinom k j)]

/-- The depth-`s` RHS1 slice as a `range (s+1)` sum at the common degree. -/
theorem genJacobi_rhs1_range (W : VertexOperatorAlgebra 𝒱) (a b c : 𝒱) (m k l : ℤ) (s : ℕ) :
    (∑ q ∈ Finset.antidiagonal s, (gBinom m q.1) • (gBinom (m + k - q.1) q.2) •
        gen W (W.smul (W.smul a q.1 b) q.2 c) (m + k - q.1 + l - q.2))
      = ∑ t ∈ Finset.range (s + 1), (gBinom m t) • (gBinom (m + k - (t : ℤ)) (s - t)) •
          gen W (W.smul (W.smul a (t : ℤ) b) ((s - t : ℕ) : ℤ) c) (m + k + l - (s : ℤ)) := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun t p => (gBinom m t) • (gBinom (m + k - (t : ℤ)) p) •
        gen W (W.smul (W.smul a (t : ℤ) b) (p : ℤ) c) (m + k - (t : ℤ) + l - (p : ℤ))) s]
  refine Finset.sum_congr rfl fun t ht => ?_
  have hts : t ≤ s := by have := Finset.mem_range.mp ht; omega
  rw [show m + k - (t : ℤ) + l - (((s - t : ℕ)) : ℤ) = m + k + l - (s : ℤ) from by
    rw [show (((s - t : ℕ)) : ℤ) = (s : ℤ) - (t : ℤ) from by rw [Nat.cast_sub hts]]; ring]

/-- **`GenJacobiDepth` holds unconditionally.**  The depth-graded slice of `Core.Borcherds.jacobi`
(`mode_commutator_vec`), assembled with the scalar Vandermonde core `cbz_genJacobi_core_range`. -/
theorem genJacobiDepth_holds (W : VertexOperatorAlgebra 𝒱) (hD : BracketDescends W) :
    GenJacobiDepth W hD := by
  classical
  intro a b c m k l s
  -- normalise all three slices to `range (s+1)` sums at the common degree `D = m+k+l-s`
  rw [genJacobi_lhs_range W a b c m k l s, genJacobi_rhs1_range W a b c m k l s,
    genJacobi_rhs2_range W a b c m k l s]
  set D : ℤ := m + k + l - (s : ℤ) with hDdef
  -- it suffices to prove `LHS_r - RHS2_r = RHS1_r`
  rw [← sub_eq_iff_eq_add]
  rw [← Finset.sum_sub_distrib]
  -- per `j`: combine the two terms into the wrapped commutator
  have hcomm : ∀ j ∈ Finset.range (s + 1),
      ((gBinom k j) • (gBinom m (s - j)) • gen W (W.smul a ((s - j : ℕ) : ℤ) (W.smul b j c)) D
        - (gBinom k j) • (gBinom m (s - j)) • gen W (W.smul b j (W.smul a ((s - j : ℕ) : ℤ) c)) D)
        = (gBinom k j) • (gBinom m (s - j)) •
            ∑ᶠ t : ℤ, cbz ((s - j : ℕ) : ℤ) t •
              gen W (W.smul (W.smul a t b) ((s : ℤ) - t) c) D := by
    intro j hj
    have hjs : j ≤ s := by have := Finset.mem_range.mp hj; omega
    rw [← smul_sub, ← smul_sub]
    congr 2
    -- the commutator at indices M = s-j, n = j, degree D, with M+n = s
    have hc := gen_commutator W a b c ((s - j : ℕ) : ℤ) (j : ℤ) D
    rw [show (((s - j : ℕ)) : ℤ) + (j : ℤ) = (s : ℤ) from by
      rw [Nat.cast_sub hjs]; ring] at hc
    exact hc
  rw [Finset.sum_congr rfl hcomm]
  -- abbreviation for the (a₍ₜ₎b)₍s-t₎c generator at degree D
  set G : ℕ → VHatCarrier W := fun t =>
    gen W (W.smul (W.smul a (t : ℤ) b) ((s : ℤ) - (t : ℤ)) c) D with hG
  -- Step 1: each `j`-term becomes a `range (s+1)` sum over `t` with the scalar core coefficient.
  have hstep1 : ∀ j ∈ Finset.range (s + 1),
      (gBinom k j) • (gBinom m (s - j)) •
          (∑ᶠ t : ℤ, cbz ((s - j : ℕ) : ℤ) t •
            gen W (W.smul (W.smul a t b) ((s : ℤ) - t) c) D)
        = ∑ t ∈ Finset.range (s + 1),
            ((gBinom k j) * (gBinom m (s - j)) * gBinom ((s - j : ℕ) : ℤ) t) • G t := by
    intro j hj
    have hjs : j ≤ s := by have := Finset.mem_range.mp hj; omega
    -- collapse the ℤ-finsum to `range (s+1)`
    have hcollapse : (∑ᶠ t : ℤ, cbz ((s - j : ℕ) : ℤ) t •
              gen W (W.smul (W.smul a t b) ((s : ℤ) - t) c) D)
          = ∑ t ∈ Finset.range (s + 1), cbz ((s - j : ℕ) : ℤ) (t : ℤ) • G t := by
      rw [finsumZ_eq_range_sum_mod
          (fun t : ℤ => cbz ((s - j : ℕ) : ℤ) t •
            gen W (W.smul (W.smul a t b) ((s : ℤ) - t) c) D) (N := s + 1)
          (fun p hp => by dsimp only; rw [cbz_apply_neg _ hp, zero_smul])
          (fun p hp => by
            dsimp only
            rw [cbz_lt (by exact_mod_cast (by omega : (0 : ℤ) ≤ ((s - j : ℕ) : ℤ)))
              (by push_cast; rw [Nat.cast_sub hjs]; omega), zero_smul])]
    rw [hcollapse, Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    -- normalise the scalar: cbz ((s-j):ℤ) (t:ℤ) = gBinom (s-j) t
    have hcbzg : cbz ((s - j : ℕ) : ℤ) (t : ℤ) = gBinom ((s - j : ℕ) : ℤ) t := by
      rw [cbz_apply_nonneg _ (by exact_mod_cast (Nat.zero_le t)), Int.toNat_natCast]
    rw [hcbzg, smul_smul, smul_smul, hG, mul_assoc]
  rw [Finset.sum_congr rfl hstep1]
  -- Step 2: swap the two finite sums and collapse the inner `j`-sum by the scalar core.
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t ht => ?_
  have hts : t ≤ s := by have := Finset.mem_range.mp ht; omega
  rw [← Finset.sum_smul, cbz_genJacobi_core_range m k s t hts, hG, smul_smul,
    show (((s - t : ℕ)) : ℤ) = (s : ℤ) - (t : ℤ) from by rw [Nat.cast_sub hts]]

/-! ## Unconditional `VHatLeibniz`, `LieRing` and `LieAlgebra` on `V̂` -/

/-- **The loop-bracket Jacobi/Leibniz identity holds unconditionally** on `V̂` (DLM3 §4): the
descended bracket satisfies `leibniz_lie`.  This is `VHatLeibniz_of_genJacobiDepth` fed by the
proven `genJacobiDepth_holds`, at the closed descent obligation `bracketDescends`. -/
theorem vhatLeibniz_holds (W : VertexOperatorAlgebra 𝒱) :
    VHatLeibniz W (bracketDescends W) :=
  VHatLeibniz_of_genJacobiDepth W (bracketDescends W)
    (genJacobiDepth_holds W (bracketDescends W))

/-- **The unconditional `LieRing` structure on `V̂`** (DLM3 §4 Frenkel–Zhu affinisation): all three
obligations are theorems — `bracketDescends` (descent), `vhatAntisymm` (skew),
`vhatLeibniz_holds` (Jacobi). -/
@[reducible]
noncomputable def lieRing (W : VertexOperatorAlgebra 𝒱) : LieRing (VHatCarrier W) :=
  lieRingOfData W (bracketDescends W)
    (vhatAntisymm W (bracketDescends W)) (vhatLeibniz_holds W)

/-- **The unconditional `LieAlgebra ℂ` structure on `V̂`.** -/
@[reducible]
noncomputable def lieAlgebra (W : VertexOperatorAlgebra 𝒱) :
    letI := lieRing W
    LieAlgebra ℂ (VHatCarrier W) :=
  lieAlgebraOfData W (bracketDescends W)
    (vhatAntisymm W (bracketDescends W)) (vhatLeibniz_holds W)

end VHat

end VOA
