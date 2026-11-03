/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.LatticeChargeMContraction

/-!
# The cross-charge FLM contraction (charges `+1` and `-1`, pairing `⟨α,-α⟩ = -2`)

The cross-charge generalization of the same-charge contraction
`LatExp.EminusCm1_contraction`.  Here the left exponential carries charge `+1`
(`aExpCZ 1`) and the right creation half carries charge `-1` (`EminusC (-1)`), so the
boson pairing is `⟨α,-α⟩ = -2`.  Unlike the self-pairing `+2` case (a three-term
`(1-z₂/z₁)²` shift) the cross pairing `-2` yields the **full** geometric series
`(1-z₂/z₁)⁻²` with triangular coefficients `m+1`:

`E⁺(α,z₁)E⁻(-α,z₂) = (1-z₂/z₁)⁻² · E⁻(-α,z₂)E⁺(α,z₁)`,

i.e. in coefficient form

`aExpCZ 1 N ∘ E⁻(-α)_b = ∑_{m} (m+1) · E⁻(-α)_{b-m} ∘ aExpCZ 1 (N-m)`.

Proved `sorry`/`pbw`-free by strong induction, mirroring `EminusCm1_contraction`.
-/

namespace VOA
namespace LatExp

open scoped BigOperators
open Module (End)
open HeisenbergN (oscN vacuumN)

/-! ## §A  Auxiliary scalar identities -/

/-- Triangular sum: `∑_{i<s} 2(i+1) = s(s+1)`. -/
theorem two_mul_succ_sum (s : ℕ) :
    ∑ i ∈ Finset.range s, (2 : ℂ) * ((i : ℂ) + 1) = (s : ℂ) * ((s : ℂ) + 1) := by
  induction s with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- The combine-step scalar identity: `(m+1)(N-m) + m(m+1) = N(m+1)`. -/
theorem combine_scalar (N m : ℂ) :
    (m + 1) * (N - m) + m * (m + 1) = N * (m + 1) := by ring

/-! ## §B  The Part-B double-sum reindexing -/

/-- The fiber scalar: over the pairs `(j,i) ∈ range P ×ˢ range (P+1)` with `i+j+1 = s`
(for `1 ≤ s ≤ P`), the weights `2(i+1)` sum to the triangular number `s(s+1)`. -/
theorem partB_fiber_scalar (P s : ℕ) (_hs1 : 1 ≤ s) (hsP : s ≤ P) :
    ∑ p ∈ (Finset.range P ×ˢ Finset.range (P + 1)).filter
            (fun p => p.2 + p.1 + 1 = s),
        ((2 : ℂ) * ((p.2 : ℂ) + 1)) = (s : ℂ) * ((s : ℂ) + 1) := by
  classical
  -- The fiber is in bijection with `i ∈ range s` via `i ↦ (s-1-i, i)`.
  rw [← two_mul_succ_sum s]
  refine Finset.sum_nbij' (fun p => p.2) (fun i => (s - 1 - i, i)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
    simp only [Finset.mem_range]; omega
  · intro i hi
    simp only [Finset.mem_range] at hi
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    omega
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
    obtain ⟨⟨_, _⟩, heq⟩ := hp
    ext
    · simp; omega
    · simp
  · intro i _hi; rfl
  · intro p _hp; rfl

/-- The Part-B double sum, grouped by the total shift `s = i+j+1`.  For a family `g : ℕ → M`
with `g s = 0` whenever `P < s`, the double sum over `j < P`, `i ≤ P` of
`2(i+1) • g(i+j+1)` collects into the triangular single sum `∑_{s ≤ P} s(s+1) • g s`. -/
theorem partB_reindex {M : Type*} [AddCommGroup M] [Module ℂ M] (g : ℕ → M) (P : ℕ)
    (hg : ∀ s, P < s → g s = 0) :
    ∑ j ∈ Finset.range P, ∑ i ∈ Finset.range (P + 1),
        ((2 : ℂ) * ((i : ℂ) + 1)) • g (i + j + 1)
      = ∑ s ∈ Finset.range (P + 1), ((s : ℂ) * ((s : ℂ) + 1)) • g s := by
  classical
  -- Step 1: collapse the double sum into a single sum over the product Finset.
  rw [← Finset.sum_product']
  -- Step 2: group fiberwise by `s = i + j + 1`, landing in `range (2*P+1)`.
  have hmaps : ∀ p ∈ Finset.range P ×ˢ Finset.range (P + 1),
      p.2 + p.1 + 1 ∈ Finset.range (2 * P + 1) := by
    intro p hp
    simp only [Finset.mem_product, Finset.mem_range] at hp
    simp only [Finset.mem_range]; omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
      (fun p => ((2 : ℂ) * ((p.2 : ℂ) + 1)) • g (p.2 + p.1 + 1))]
  -- Step 3: each fiber-sum equals `(s(s+1)) • g s` for `1 ≤ s ≤ P`, and `0` otherwise.
  have hfib : ∀ s ∈ Finset.range (2 * P + 1),
      (∑ p ∈ (Finset.range P ×ˢ Finset.range (P + 1)).filter
              (fun p => p.2 + p.1 + 1 = s),
          ((2 : ℂ) * ((p.2 : ℂ) + 1)) • g (p.2 + p.1 + 1))
        = if s ∈ Finset.range (P + 1) then ((s : ℂ) * ((s : ℂ) + 1)) • g s else 0 := by
    intro s _
    -- On the fiber, `g (p.2+p.1+1) = g s`, so pull `g s` out of the scalar sum.
    have hrw : ∀ p ∈ (Finset.range P ×ˢ Finset.range (P + 1)).filter
            (fun p => p.2 + p.1 + 1 = s),
        ((2 : ℂ) * ((p.2 : ℂ) + 1)) • g (p.2 + p.1 + 1)
          = ((2 : ℂ) * ((p.2 : ℂ) + 1)) • g s := by
      intro p hp
      simp only [Finset.mem_filter] at hp
      rw [hp.2]
    rw [Finset.sum_congr rfl hrw, ← Finset.sum_smul]
    by_cases hmem : s ∈ Finset.range (P + 1)
    · rw [if_pos hmem]
      simp only [Finset.mem_range] at hmem
      by_cases hs0 : s = 0
      · -- `s = 0` fiber is empty (since `p.2+p.1+1 ≥ 1`).
        subst hs0
        rw [Finset.filter_false_of_mem (by intro p _ h; omega), Finset.sum_empty,
          zero_smul, Nat.cast_zero, zero_mul, zero_smul]
      · rw [partB_fiber_scalar P s (by omega) (by omega)]
    · rw [if_neg hmem]
      simp only [Finset.mem_range, not_lt] at hmem
      -- `s > P`: `g s = 0` so the whole fiber-sum vanishes.
      rw [hg s (by omega), smul_zero]
  rw [Finset.sum_congr rfl hfib, Finset.sum_ite_mem,
    Finset.inter_eq_right.mpr (by intro x hx; simp only [Finset.mem_range] at hx ⊢; omega)]

/-! ## §C  The cross-charge FLM contraction (the main induction) -/

/-- **The cross-charge FLM contraction** (the `aExpCZ`/`EminusC` coefficient form): the
`z₁`-dominant reordering of `E⁺(α,z₁)E⁻(-α,z₂)`.  Cross pairing `⟨α,-α⟩ = -2`,
so the **full** geometric series `(1-z₂/z₁)⁻²` with triangular coefficients `m+1`.
Axiom-clean, `pbw`-free. -/
theorem aExpCZ1_comp_EminusCm1 (N : ℤ) (hN : 0 ≤ N) (b : ℤ) :
    (aExpCZ 1 N).comp (EminusC (-1) b)
      = ∑ m ∈ Finset.range (N.toNat + 1),
          ((m : ℂ) + 1) • (EminusC (-1) (b - m)).comp (aExpCZ 1 (N - m)) := by
  suffices H : ∀ n : ℕ, ∀ N b : ℤ, N.toNat ≤ n → 0 ≤ N →
      (aExpCZ 1 N).comp (EminusC (-1) b)
        = ∑ m ∈ Finset.range (N.toNat + 1),
            ((m : ℂ) + 1) • (EminusC (-1) (b - m)).comp (aExpCZ 1 (N - m)) by
    exact H N.toNat N b le_rfl hN
  intro n
  induction n with
  | zero =>
    intro N b hN hN0
    have hN0' : N = 0 := by omega
    subst hN0'
    rw [aExpCZ_zero, LinearMap.id_comp, Int.toNat_zero, Finset.sum_range_one]
    simp only [Nat.cast_zero, zero_add, sub_zero, one_smul, aExpCZ_zero, LinearMap.comp_id]
  | succ n ih =>
    intro N b hN hN0
    by_cases hsmall : N.toNat ≤ n
    · exact ih N b hsmall hN0
    · have hN1 : 1 ≤ N := by omega
      have hNn : N.toNat = n + 1 := by omega
      have hNne : (N : ℂ) ≠ 0 := by
        simp only [ne_eq, Int.cast_eq_zero]; omega
      -- The reassembled "column" family.
      set g : ℕ → Module.End ℂ B :=
        fun s => (EminusC (-1) (b - (s : ℤ))).comp (aExpCZ 1 (N - (s : ℤ))) with hg
      -- `g s = 0` for `s > N.toNat` (the right `aExpCZ` index goes negative).
      have hgzero : ∀ s : ℕ, N.toNat < s → g s = 0 := by
        intro s hs
        simp only [hg]
        rw [aExpCZ_neg 1 (show N - (s : ℤ) < 0 by omega), LinearMap.comp_zero]
      -- Step 1: expand LHS via the (c = 1) Newton recursion.
      have hLHS : (aExpCZ 1 N).comp (EminusC (-1) b)
          = (N : ℂ)⁻¹ • ∑ j ∈ Finset.range N.toNat,
              (-(α ((j : ℤ) + 1))).comp ((aExpCZ 1 (N - 1 - j)).comp (EminusC (-1) b)) := by
        rw [aExpCZ_recursion 1 N hN1, one_smul, LinearMap.smul_comp, sum_comp']
        simp only [LinearMap.comp_assoc]
      -- Step 2: per `j`, IH + move `α` past + range-extension to a uniform `i`-range.
      have hterm : ∀ j ∈ Finset.range N.toNat,
          (-(α ((j : ℤ) + 1))).comp ((aExpCZ 1 (N - 1 - j)).comp (EminusC (-1) b))
            = ∑ i ∈ Finset.range (N.toNat + 1),
                ( ((i : ℂ) + 1) • (EminusC (-1) (b - (i : ℤ))).comp
                    ((-(α ((j : ℤ) + 1))).comp (aExpCZ 1 (N - 1 - (j : ℤ) - (i : ℤ))))
                  + ((2 : ℂ) * ((i : ℂ) + 1)) • g (i + j + 1) ) := by
        intro j hj
        simp only [Finset.mem_range] at hj
        have hNj0 : 0 ≤ N - 1 - (j : ℤ) := by omega
        have hNjn : (N - 1 - (j : ℤ)).toNat ≤ n := by omega
        -- Apply IH, then distribute `(-(α(j+1))).comp` and move it past each `EminusC`.
        rw [ih (N - 1 - (j : ℤ)) b hNjn hNj0, comp_sum']
        -- First: rewrite each IH-term (range `(N-1-j).toNat+1`) into PartA + PartB.
        have hbody : ∀ i ∈ Finset.range ((N - 1 - (j : ℤ)).toNat + 1),
            (-(α ((j : ℤ) + 1))).comp (((i : ℂ) + 1) •
                (EminusC (-1) (b - (i : ℤ))).comp (aExpCZ 1 (N - 1 - (j : ℤ) - (i : ℤ))))
              = ((i : ℂ) + 1) • (EminusC (-1) (b - (i : ℤ))).comp
                  ((-(α ((j : ℤ) + 1))).comp (aExpCZ 1 (N - 1 - (j : ℤ) - (i : ℤ))))
                + ((2 : ℂ) * ((i : ℂ) + 1)) • g (i + j + 1) := by
          intro i _
          have hb : b - (i : ℤ) - ((j : ℤ) + 1) = b - ((i + j + 1 : ℕ) : ℤ) := by
            push_cast; ring
          have hNi : N - 1 - (j : ℤ) - (i : ℤ) = N - ((i + j + 1 : ℕ) : ℤ) := by
            push_cast; ring
          rw [LinearMap.comp_smul, move_alphaC_past_EminusC]
          simp only [smul_sub, hg]
          rw [hb, hNi, smul_smul]
          module
        rw [Finset.sum_congr rfl hbody]
        -- Range-extension: extend `range ((N-1-j).toNat+1)` to `range (N.toNat+1)`; extras vanish.
        have htn : (N - 1 - (j : ℤ)).toNat + 1 ≤ N.toNat + 1 := by
          have hNeq := Int.toNat_of_nonneg hN0
          have : (N - 1 - (j : ℤ)).toNat ≤ N.toNat := by
            rw [Int.toNat_le]; omega
          omega
        refine Finset.sum_subset
          (by intro x hx; simp only [Finset.mem_range] at hx ⊢; omega) ?_
        intro i _ hi
        simp only [Finset.mem_range, not_lt] at hi
        -- For `i ≥ (N-1-j).toNat+1`, both `aExpCZ 1 (N-1-j-i)` and `g (i+j+1)` vanish.
        have hibig : (N - 1 - (j : ℤ)).toNat + 1 ≤ (i : ℕ) := by omega
        have h1 : aExpCZ 1 (N - 1 - (j : ℤ) - (i : ℤ)) = 0 := by
          apply aExpCZ_neg 1
          have hle := Int.self_le_toNat (N - 1 - (j : ℤ))
          have : ((N - 1 - (j : ℤ)).toNat : ℤ) + 1 ≤ (i : ℤ) := by exact_mod_cast hibig
          omega
        have h2 : g (i + j + 1) = 0 := by
          simp only [hg]
          rw [aExpCZ_neg 1 (show N - ((i + j + 1 : ℕ) : ℤ) < 0 by push_cast; omega),
            LinearMap.comp_zero]
        rw [h1, h2, LinearMap.comp_zero, LinearMap.comp_zero, smul_zero, smul_zero, add_zero]
      -- Step 3a: the Part-A double sum reassembles to `∑_i ((i+1)(N-i))•g i`.
      have hPartA : (∑ j ∈ Finset.range N.toNat, ∑ i ∈ Finset.range (N.toNat + 1),
              ((i : ℂ) + 1) • (EminusC (-1) (b - (i : ℤ))).comp
                ((-(α ((j : ℤ) + 1))).comp (aExpCZ 1 (N - 1 - (j : ℤ) - (i : ℤ)))))
          = ∑ i ∈ Finset.range (N.toNat + 1),
              (((i : ℂ) + 1) * ((N : ℂ) - (i : ℂ))) • g i := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i hi => ?_
        simp only [Finset.mem_range] at hi
        -- Pull `(i+1)•` and the left `EminusC` out of the `j`-sum, then reassemble.
        rw [← Finset.smul_sum]
        have hidx : ∀ j ∈ Finset.range N.toNat,
            (-(α ((j : ℤ) + 1))).comp (aExpCZ 1 (N - 1 - (j : ℤ) - (i : ℤ)))
              = (-(α ((j : ℤ) + 1))).comp (aExpCZ 1 ((N - (i : ℤ)) - 1 - (j : ℤ))) := by
          intro j _
          rw [show N - 1 - (j : ℤ) - (i : ℤ) = (N - (i : ℤ)) - 1 - (j : ℤ) from by ring]
        have hcol : (∑ j ∈ Finset.range N.toNat,
              (EminusC (-1) (b - (i : ℤ))).comp
                ((-(α ((j : ℤ) + 1))).comp (aExpCZ 1 (N - 1 - (j : ℤ) - (i : ℤ)))))
            = (EminusC (-1) (b - (i : ℤ))).comp
                (((N : ℂ) - (i : ℂ)) • aExpCZ 1 (N - (i : ℤ))) := by
          rw [← comp_sum']
          congr 1
          have hreass := aExpCZ_sum_reassembly 1 (N - (i : ℤ)) N.toNat
            (by rw [Int.toNat_le]; push_cast [Int.toNat_of_nonneg hN0]; omega)
          rw [one_smul] at hreass
          rw [Finset.sum_congr rfl hidx, hreass]
          push_cast; ring_nf
        rw [hcol, LinearMap.comp_smul, smul_smul]
      -- Step 3b: the Part-B double sum reindexes to `∑_s (s(s+1))•g s`.
      have hPartB : (∑ j ∈ Finset.range N.toNat, ∑ i ∈ Finset.range (N.toNat + 1),
              ((2 : ℂ) * ((i : ℂ) + 1)) • g (i + j + 1))
          = ∑ s ∈ Finset.range (N.toNat + 1), ((s : ℂ) * ((s : ℂ) + 1)) • g s :=
        partB_reindex g N.toNat hgzero
      -- Step 4: combine Part A + Part B, apply the scalar identity, cancel `N⁻¹·N`.
      rw [hLHS, Finset.sum_congr rfl hterm]
      simp only [Finset.sum_add_distrib]
      rw [hPartA, hPartB, ← Finset.sum_add_distrib]
      -- Now: `(N:ℂ)⁻¹ • ∑_m (((m+1)(N-m) + m(m+1)) • g m) = ∑_m (m+1) • g m`.
      have hcombine : ∀ m ∈ Finset.range (N.toNat + 1),
          (((m : ℂ) + 1) * ((N : ℂ) - (m : ℂ))) • g m
              + ((m : ℂ) * ((m : ℂ) + 1)) • g m
            = (N : ℂ) • (((m : ℂ) + 1) • g m) := by
        intro m _
        rw [← add_smul, combine_scalar, smul_smul]
      rw [Finset.sum_congr rfl hcombine, ← Finset.smul_sum, smul_smul,
        inv_mul_cancel₀ hNne, one_smul]

/-- **The cross-charge FLM contraction** in `E⁺(α)`/`E⁻(-α)` coefficient form (for `a ≤ 0`,
where `E⁺(α)_a = aExpCZ 1 (-a)` is the genuine creation series):
`E⁺(α)_a ∘ E⁻(-α)_b = ∑_{m} (m+1) · E⁻(-α)_{b-m} ∘ E⁺(α)_{a+m}`, the
`z₁`-dominant `(1-z₂/z₁)⁻²` (cross pairing `⟨α,-α⟩ = -2`). -/
theorem EplusC1_comp_EminusCm1 (a b : ℤ) (ha : a ≤ 0) :
    (EplusC 1 a).comp (EminusC (-1) b)
      = ∑ m ∈ Finset.range ((-a).toNat + 1),
          ((m : ℂ) + 1) • (EminusC (-1) (b - m)).comp (EplusC 1 (a + m)) := by
  rw [EplusC_eq_aExpCZ 1 a, aExpCZ1_comp_EminusCm1 (-a) (by omega) b]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [EplusC_eq_aExpCZ 1 (a + (m : ℤ)),
    show -(a + (m : ℤ)) = -a - (m : ℤ) from by ring]

end LatExp
end VOA
