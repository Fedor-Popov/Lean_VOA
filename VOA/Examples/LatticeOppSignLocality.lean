/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.LatticeSameSignLocality

/-!
# Opposite-sign + full general-charge lattice locality (STAGE 3, the `mm' ≤ -1` half)

The remaining (opposite-sign) half of the general charge-pair mutual locality
`Local (Yemα m) (Yemα m')`.  Combined with the same-sign / charge-`0` results of
`LatticeSameSignLocality`, this closes the FULL general-charge locality

* `Yemα_local (m m' : ℤ) : Local (Yemα m) (Yemα m')`.

For `mm' ≤ -1` the pairing `P = 2mm' < 0` is the (negative) head of the **infinite** geometric
contraction `(1-z₂/z₁)^P`, with kernel `kZ P = kZ (-Pn)` (`Pn = -2mm' = 2|m||m'|`).  The two OPE
orderings of the boson dressings `EEC m`, `EEC m'` therefore agree only after multiplying by
`(z₁-z₂)^{Pn}`, which is exactly bound-`Pn` mutual locality (the general analog of the charge-`±1`
keystone `Yemα_cross_local`, bound `2`, generalized from `[1,-2,1]` to the full `Pn`-fold finite
difference with binomial weights `wt Pn i`).

This file ports the general-charge OPE machinery (`kappa`/`kZ`/`wt`, `Wgen`, `hExpand1_gen`,
`hExpand2_gen`, `mulBySubPow_binom`, `wt_kZ_conv`) and assembles the opposite-sign locality on top.

All `pbw`-free / axiom-clean (`[propext, Classical.choice, Quot.sound]`).
-/

open VOA VOA.LatExp VOA.LatticeVOA
open Module (End)
open scoped TensorProduct BigOperators
namespace VOA.LatExp

noncomputable def kappa (P : ℂ) : ℕ → ℂ
  | 0 => 1
  | (i + 1) => ((i : ℂ) + 1)⁻¹ * (-P * ∑ j ∈ Finset.range (i + 1),
      if hj : j < i + 1 then kappa P j else 0)
  decreasing_by all_goals simp_all

theorem kappa_zero (P : ℂ) : kappa P 0 = 1 := by rw [kappa]

theorem kappa_succ (P : ℂ) (i : ℕ) :
    kappa P (i + 1) = ((i : ℂ) + 1)⁻¹ * (-P * ∑ j ∈ Finset.range (i + 1), kappa P j) := by
  rw [kappa]
  congr 2
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [dif_pos (Finset.mem_range.mp hj)]

/-- The combine recursion: `(i:ℂ)·κ P i = -P·∑_{j<i} κ P j`. -/
theorem kappa_combine (P : ℂ) (i : ℕ) :
    (i : ℂ) * kappa P i = -P * ∑ j ∈ Finset.range i, kappa P j := by
  match i with
  | 0 => simp
  | (k + 1) =>
    rw [kappa_succ]
    have hne : ((k : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero k
    push_cast
    rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]

/-- The 2-term recursion: `(s+1)·κ P (s+1) = (s - P)·κ P s`. -/
theorem kappa_two_term (P : ℂ) (s : ℕ) :
    ((s : ℂ) + 1) * kappa P (s + 1) = ((s : ℂ) - P) * kappa P s := by
  have h1 := kappa_combine P (s + 1)
  have h2 := kappa_combine P s
  rw [Finset.sum_range_succ] at h1
  push_cast at h1 h2 ⊢
  rw [mul_add, ← h2] at h1
  rw [h1]; ring

/-- **Vandermonde convolution** of kernels: `∑_{i=0}^s κA(i)·κB(s-i) = κ(A+B)(s)`. -/
theorem kappa_conv (A Bb : ℂ) (s : ℕ) :
    ∑ i ∈ Finset.range (s + 1), kappa A i * kappa Bb (s - i) = kappa (A + Bb) s := by
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    match s with
    | 0 => simp [kappa_zero]
    | (t + 1) =>
      have hne : ((t : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero t
      rw [← mul_right_inj' hne]
      -- RHS: (t+1)·κ(A+B)(t+1) = (t - (A+B))·κ(A+B)(t)  [2-term], and IH gives κ(A+B)(t).
      rw [kappa_two_term (A + Bb) t, ← ih t (by omega)]
      -- LHS: (t+1)·∑_{i=0}^{t+1} κA(i)κB(t+1-i).  Write (t+1) = i + (t+1-i).
      rw [Finset.mul_sum]
      have hsplit : ∀ i ∈ Finset.range (t + 1 + 1),
          ((t : ℂ) + 1) * (kappa A i * kappa Bb (t + 1 - i))
            = ((i : ℂ) * kappa A i) * kappa Bb (t + 1 - i)
              + kappa A i * (((t + 1 - i : ℕ) : ℂ) * kappa Bb (t + 1 - i)) := by
        intro i hi
        simp only [Finset.mem_range] at hi
        have hcast : ((t : ℂ) + 1) = (i : ℂ) + ((t + 1 - i : ℕ) : ℂ) := by
          push_cast [Nat.cast_sub (by omega : i ≤ t + 1)]; ring
        rw [hcast]; ring
      rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
      -- Sum1: ∑_{i} (i·κA i)·κB(t+1-i).  i=0 term vanishes; reindex i=i'+1 via 2-term.
      have hS1 : (∑ i ∈ Finset.range (t + 1 + 1),
            ((i : ℂ) * kappa A i) * kappa Bb (t + 1 - i))
          = ∑ i' ∈ Finset.range (t + 1), (((i' : ℂ) - A) * kappa A i') * kappa Bb (t - i') := by
        rw [Finset.sum_range_succ']
        simp only [Nat.cast_zero, zero_mul, add_zero]
        refine Finset.sum_congr rfl fun i' hi' => ?_
        simp only [Finset.mem_range] at hi'
        have hr : (((i' + 1 : ℕ) : ℂ)) * kappa A (i' + 1) = ((i' : ℂ) - A) * kappa A i' := by
          have := kappa_two_term A i'; push_cast at this ⊢; linear_combination this
        rw [hr, show t + 1 - (i' + 1) = t - i' from by omega]
      -- Sum2: ∑_{i} κA i·((t+1-i)·κB(t+1-i)).  i=t+1 term vanishes; 2-term on κB.
      have hS2 : (∑ i ∈ Finset.range (t + 1 + 1),
            kappa A i * (((t + 1 - i : ℕ) : ℂ) * kappa Bb (t + 1 - i)))
          = ∑ i ∈ Finset.range (t + 1), kappa A i * ((((t - i : ℕ) : ℂ) - Bb) * kappa Bb (t - i)) := by
        rw [Finset.sum_range_succ]
        simp only [show t + 1 - (t + 1) = 0 from by omega, Nat.cast_zero, zero_mul, mul_zero,
          add_zero]
        refine Finset.sum_congr rfl fun i hi => ?_
        simp only [Finset.mem_range] at hi
        have h2 := kappa_two_term Bb (t - i)
        have hr : (((t + 1 - i : ℕ) : ℂ)) * kappa Bb (t + 1 - i)
            = (((t - i : ℕ) : ℂ) - Bb) * kappa Bb (t - i) := by
          rw [show t + 1 - i = (t - i) + 1 from by omega]; push_cast at h2 ⊢; linear_combination h2
        rw [hr]
      rw [hS1, hS2, ← Finset.sum_add_distrib]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      simp only [Finset.mem_range] at hi
      rw [Nat.cast_sub (by omega : i ≤ t)]
      ring

/-! ### Identification of `kappa (n:ℂ)` with the binomial weight (same-sign, nat `P`). -/

/-- The binomial weight `wt P i = (-1)^i C(P,i)` (the closed form of `kappa (P:ℂ)`). -/
noncomputable def wt (P i : ℕ) : ℂ := (-1)^i * (P.choose i)

theorem wt_vanish (P i : ℕ) (h : P < i) : wt P i = 0 := by
  rw [wt, Nat.choose_eq_zero_of_lt h]; simp

theorem wt_partial (Q m : ℕ) :
    ∑ i ∈ Finset.range (m + 1), wt (Q + 1) i = (-1)^m * (Q.choose m) := by
  induction m with
  | zero => simp [wt]
  | succ k ih =>
    rw [Finset.sum_range_succ, ih, wt, Nat.choose_succ_succ Q k]
    push_cast; ring

/-- The `wt` combine recursion (same as `kappa_combine`). -/
theorem wt_combine (Q t : ℕ) (ht : 1 ≤ t) :
    (t : ℂ) * wt (Q + 1) t = -((Q : ℂ) + 1) * ∑ i ∈ Finset.range t, wt (Q + 1) i := by
  obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega⟩
  rw [wt_partial Q k, wt]
  have hkeyN : ((k + 1) * (Q + 1).choose (k + 1) : ℕ) = ((Q + 1) * Q.choose k : ℕ) := by
    have h := Nat.succ_mul_choose_eq Q k
    simp only [Nat.succ_eq_add_one] at h
    rw [h]; ring
  have hkey : ((k : ℂ) + 1) * ((Q + 1).choose (k + 1) : ℂ) = ((Q : ℂ) + 1) * (Q.choose k : ℂ) := by
    exact_mod_cast hkeyN
  have hpow : (-1 : ℂ)^(k+1) = -((-1:ℂ)^k) := by rw [pow_succ]; ring
  rw [hpow]; push_cast; push_cast at hkey
  linear_combination (-(((-1:ℂ))^k)) * hkey

/-- `kappa (n:ℂ) = wt n` for nat `n` (same recursion + uniqueness, by strong induction). -/
theorem kappa_eq_wt (n i : ℕ) : kappa (n : ℂ) i = wt n i := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    match i with
    | 0 => rw [kappa_zero, wt]; simp
    | (k + 1) =>
      have hsum : ∑ j ∈ Finset.range (k + 1), kappa (n : ℂ) j
          = ∑ j ∈ Finset.range (k + 1), wt n j :=
        Finset.sum_congr rfl fun j hj => ih j (by simp only [Finset.mem_range] at hj; omega)
      have hne : ((k : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero k
      have hk := kappa_combine (n : ℂ) (k + 1)
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        rw [kappa_succ, hsum]; simp only [Nat.cast_zero, neg_zero, zero_mul, mul_zero]
        rw [wt, Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, mul_zero]
      · obtain ⟨Q, rfl⟩ : ∃ Q, n = Q + 1 := ⟨n - 1, by omega⟩
        have hwc := wt_combine Q (k + 1) (by omega)
        rw [hsum] at hk
        -- (k+1)·kappa(k+1) = -(Q+1)·∑ wt = (k+1)·wt(k+1)
        push_cast at hk hwc ⊢
        rw [← mul_right_inj' hne]
        rw [hk, ← hwc]

/-- `kappa 0 = δ`. -/
theorem kappa_zero_kernel (s : ℕ) : kappa (0 : ℂ) s = if s = 0 then 1 else 0 := by
  match s with
  | 0 => rw [kappa_zero, if_pos rfl]
  | (t + 1) =>
    rw [kappa_succ, if_neg (by omega)]; simp

/-- `wt` symmetry for EVEN `P`: `wt P i = wt P (P - i)` (for `i ≤ P`). -/
theorem wt_symm_even (P i : ℕ) (hev : Even P) (hi : i ≤ P) : wt P i = wt P (P - i) := by
  rw [wt, wt, Nat.choose_symm hi]
  congr 1
  obtain ⟨r, hr⟩ := hev
  have hP : P = i + (P - i) := by omega
  have h2 : (-1 : ℂ)^P = 1 := by rw [hr, show r + r = 2 * r from by ring, pow_mul]; ring
  have h1 : (-1 : ℂ)^i * (-1)^(P - i) = 1 := by rw [← pow_add, ← hP, h2]
  have hne : ((-1 : ℂ))^i ≠ 0 := pow_ne_zero _ (by norm_num)
  have hu : (-1 : ℂ)^i * (-1)^i = 1 := by rw [← pow_add, ← two_mul, pow_mul]; ring
  have heq : (-1 : ℂ)^i * (-1)^(P - i) = (-1)^i * (-1)^i := by rw [h1, hu]
  exact (mul_left_cancel₀ hne heq).symm

/-! ## The general two-charge contraction (any sign), kernel `kappa (2cc')`. -/

/-- The Part-B reindex with abstract kernel `κ`: the residual double sum reindexes to
`∑_s (∑_{i<s} κ i)•g s`. -/
theorem partB_reindex_gen {M : Type*} [AddCommGroup M] [Module ℂ M]
    (g : ℕ → M) (P : ℕ) (κ : ℕ → ℂ) (hg : ∀ s, P < s → g s = 0) :
    ∑ j ∈ Finset.range P, ∑ i ∈ Finset.range (P + 1), κ i • g (i + j + 1)
      = ∑ s ∈ Finset.range (P + 1), (∑ i ∈ Finset.range s, κ i) • g s := by
  classical
  rw [← Finset.sum_product']
  have hmaps : ∀ p ∈ Finset.range P ×ˢ Finset.range (P + 1),
      p.2 + p.1 + 1 ∈ Finset.range (2 * P + 1) := by
    intro p hp; simp only [Finset.mem_product, Finset.mem_range] at hp
    simp only [Finset.mem_range]; omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun p => κ p.2 • g (p.2 + p.1 + 1))]
  have hfib : ∀ s ∈ Finset.range (2 * P + 1),
      (∑ p ∈ (Finset.range P ×ˢ Finset.range (P + 1)).filter
              (fun p => p.2 + p.1 + 1 = s), κ p.2 • g (p.2 + p.1 + 1))
        = if s ∈ Finset.range (P + 1) then (∑ i ∈ Finset.range s, κ i) • g s else 0 := by
    intro s _
    have hrw : ∀ p ∈ (Finset.range P ×ˢ Finset.range (P + 1)).filter
            (fun p => p.2 + p.1 + 1 = s), κ p.2 • g (p.2 + p.1 + 1) = κ p.2 • g s := by
      intro p hp; simp only [Finset.mem_filter] at hp; rw [hp.2]
    rw [Finset.sum_congr rfl hrw, ← Finset.sum_smul]
    by_cases hmem : s ∈ Finset.range (P + 1)
    · rw [if_pos hmem]
      simp only [Finset.mem_range] at hmem
      congr 1
      -- ∑ over the fiber of κ p.2 = ∑_{i<s} κ i, via i ↦ (s-1-i, i)
      by_cases hs0 : s = 0
      · subst hs0
        rw [Finset.filter_false_of_mem (by intro p _ h; omega), Finset.sum_empty,
          Finset.range_zero, Finset.sum_empty]
      · obtain ⟨r, rfl⟩ : ∃ r, s = r + 1 := ⟨s - 1, by omega⟩
        refine Finset.sum_nbij' (fun p => p.2) (fun i => (r - i, i)) ?_ ?_ ?_ ?_ ?_
        · intro p hp; simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
          simp only [Finset.mem_range]; omega
        · intro i hi; simp only [Finset.mem_range] at hi
          simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]; omega
        · intro p hp; simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
          obtain ⟨⟨_, _⟩, heq⟩ := hp; ext <;> simp <;> omega
        · intro i _; rfl
        · intro p _; rfl
    · rw [if_neg hmem]
      simp only [Finset.mem_range, not_lt] at hmem
      rw [hg s (by omega), smul_zero]
  rw [Finset.sum_congr rfl hfib, Finset.sum_ite_mem,
    Finset.inter_eq_right.mpr (by intro x hx; simp only [Finset.mem_range] at hx ⊢; omega)]

/-- **The general two-charge FLM contraction**: for left charge `c` (Newton factor `c`) and right
creation charge `c'` (move residual `2c'`), with pairing `P = 2cc'`,
`aExpCZ c N ∘ EminusC c' b = ∑_{i ≤ N.toNat} κ_P(i) • EminusC c'(b-i) ∘ aExpCZ c (N-i)`. -/
theorem aExpCZ_comp_EminusC_gen (c c' : ℂ) (N : ℤ) (hN : 0 ≤ N) (b : ℤ) :
    (aExpCZ c N).comp (EminusC c' b)
      = ∑ m ∈ Finset.range (N.toNat + 1),
          kappa (2 * c * c') m • (EminusC c' (b - m)).comp (aExpCZ c (N - m)) := by
  set P := 2 * c * c' with hP
  suffices H : ∀ n : ℕ, ∀ N b : ℤ, N.toNat ≤ n → 0 ≤ N →
      (aExpCZ c N).comp (EminusC c' b)
        = ∑ m ∈ Finset.range (N.toNat + 1),
            kappa P m • (EminusC c' (b - m)).comp (aExpCZ c (N - m)) by
    exact H N.toNat N b le_rfl hN
  intro n
  induction n with
  | zero =>
    intro N b hN hN0
    have hN0' : N = 0 := by omega
    subst hN0'
    rw [aExpCZ_zero, LinearMap.id_comp, Int.toNat_zero, Finset.sum_range_one]
    simp only [Nat.cast_zero, sub_zero, kappa_zero, one_smul, aExpCZ_zero,
      LinearMap.comp_id]
  | succ n ih =>
    intro N b hN hN0
    by_cases hsmall : N.toNat ≤ n
    · exact ih N b hsmall hN0
    · have hN1 : 1 ≤ N := by omega
      have hNn : N.toNat = n + 1 := by omega
      have hNne : (N : ℂ) ≠ 0 := by simp only [ne_eq, Int.cast_eq_zero]; omega
      set g : ℕ → Module.End ℂ B :=
        fun s => (EminusC c' (b - (s : ℤ))).comp (aExpCZ c (N - (s : ℤ))) with hg
      have hgzero : ∀ s : ℕ, N.toNat < s → g s = 0 := by
        intro s hs; simp only [hg]
        rw [aExpCZ_neg c (show N - (s : ℤ) < 0 by omega), LinearMap.comp_zero]
      have hLHS : (aExpCZ c N).comp (EminusC c' b)
          = (N : ℂ)⁻¹ • c • ∑ j ∈ Finset.range N.toNat,
              (-(α ((j : ℤ) + 1))).comp ((aExpCZ c (N - 1 - j)).comp (EminusC c' b)) := by
        rw [aExpCZ_recursion c N hN1, LinearMap.smul_comp, LinearMap.smul_comp, sum_comp']
        simp only [LinearMap.comp_assoc]
      have hterm : ∀ j ∈ Finset.range N.toNat,
          (-(α ((j : ℤ) + 1))).comp ((aExpCZ c (N - 1 - j)).comp (EminusC c' b))
            = ∑ i ∈ Finset.range (N.toNat + 1),
                ( kappa P i • (EminusC c' (b - (i : ℤ))).comp
                    ((-(α ((j : ℤ) + 1))).comp (aExpCZ c (N - 1 - (j : ℤ) - (i : ℤ))))
                  + (-(2 * c') * kappa P i) • g (i + j + 1) ) := by
        intro j hj
        simp only [Finset.mem_range] at hj
        have hNj0 : 0 ≤ N - 1 - (j : ℤ) := by omega
        have hNjn : (N - 1 - (j : ℤ)).toNat ≤ n := by omega
        rw [ih (N - 1 - (j : ℤ)) b hNjn hNj0, comp_sum']
        have hbody : ∀ i ∈ Finset.range ((N - 1 - (j : ℤ)).toNat + 1),
            (-(α ((j : ℤ) + 1))).comp (kappa P i •
                (EminusC c' (b - (i : ℤ))).comp (aExpCZ c (N - 1 - (j : ℤ) - (i : ℤ))))
              = kappa P i • (EminusC c' (b - (i : ℤ))).comp
                  ((-(α ((j : ℤ) + 1))).comp (aExpCZ c (N - 1 - (j : ℤ) - (i : ℤ))))
                + (-(2 * c') * kappa P i) • g (i + j + 1) := by
          intro i _
          have hb : b - (i : ℤ) - ((j : ℤ) + 1) = b - ((i + j + 1 : ℕ) : ℤ) := by push_cast; ring
          have hNi : N - 1 - (j : ℤ) - (i : ℤ) = N - ((i + j + 1 : ℕ) : ℤ) := by push_cast; ring
          rw [LinearMap.comp_smul, move_alphaC_past_EminusC]
          simp only [smul_sub, hg]
          rw [hb, hNi, smul_smul]
          module
        rw [Finset.sum_congr rfl hbody]
        have htn : (N - 1 - (j : ℤ)).toNat + 1 ≤ N.toNat + 1 := by
          have : (N - 1 - (j : ℤ)).toNat ≤ N.toNat := by rw [Int.toNat_le]; omega
          omega
        refine Finset.sum_subset
          (by intro x hx; simp only [Finset.mem_range] at hx ⊢; omega) ?_
        intro i _ hi
        simp only [Finset.mem_range, not_lt] at hi
        have hibig : (N - 1 - (j : ℤ)).toNat + 1 ≤ (i : ℕ) := by omega
        have h1 : aExpCZ c (N - 1 - (j : ℤ) - (i : ℤ)) = 0 := by
          apply aExpCZ_neg c
          have hle := Int.self_le_toNat (N - 1 - (j : ℤ))
          have : ((N - 1 - (j : ℤ)).toNat : ℤ) + 1 ≤ (i : ℤ) := by exact_mod_cast hibig
          omega
        have h2 : g (i + j + 1) = 0 := by
          simp only [hg]
          rw [aExpCZ_neg c (show N - ((i + j + 1 : ℕ) : ℤ) < 0 by push_cast; omega),
            LinearMap.comp_zero]
        rw [h1, h2, LinearMap.comp_zero, LinearMap.comp_zero, smul_zero, smul_zero, add_zero]
      -- Part A: reassemble (with the Newton `c•`) to `∑_i ((N-i)·κ i)•g i`.
      have hPartA : c • (∑ j ∈ Finset.range N.toNat, ∑ i ∈ Finset.range (N.toNat + 1),
              kappa P i • (EminusC c' (b - (i : ℤ))).comp
                ((-(α ((j : ℤ) + 1))).comp (aExpCZ c (N - 1 - (j : ℤ) - (i : ℤ)))))
          = ∑ i ∈ Finset.range (N.toNat + 1), (((N : ℂ) - (i : ℂ)) * kappa P i) • g i := by
        rw [Finset.sum_comm]
        rw [show (c • ∑ i ∈ Finset.range (N.toNat + 1), ∑ j ∈ Finset.range N.toNat,
              kappa P i • (EminusC c' (b - (i : ℤ))).comp
                ((-(α ((j : ℤ) + 1))).comp (aExpCZ c (N - 1 - (j : ℤ) - (i : ℤ)))))
            = ∑ i ∈ Finset.range (N.toNat + 1), c • ∑ j ∈ Finset.range N.toNat,
              kappa P i • (EminusC c' (b - (i : ℤ))).comp
                ((-(α ((j : ℤ) + 1))).comp (aExpCZ c (N - 1 - (j : ℤ) - (i : ℤ)))) from
          Finset.smul_sum]
        refine Finset.sum_congr rfl fun i hi => ?_
        simp only [Finset.mem_range] at hi
        have hreass := aExpCZ_sum_reassembly c (N - (i : ℤ)) N.toNat
          (by rw [Int.toNat_le]; push_cast [Int.toNat_of_nonneg hN0]; omega)
        -- inner sum (no kappa, no c): ∑_j (EminusC).comp((-α)∘aExpCZ(N-1-j-i))
        have hcolbare : (∑ j ∈ Finset.range N.toNat,
              (EminusC c' (b - (i : ℤ))).comp
                ((-(α ((j : ℤ) + 1))).comp (aExpCZ c (N - 1 - (j : ℤ) - (i : ℤ)))))
            = (EminusC c' (b - (i : ℤ))).comp
                (∑ j ∈ Finset.range N.toNat,
                  (-(α ((j : ℤ) + 1))).comp (aExpCZ c ((N - (i : ℤ)) - 1 - (j : ℤ)))) := by
          rw [comp_sum']
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [show N - 1 - (j : ℤ) - (i : ℤ) = (N - (i : ℤ)) - 1 - (j : ℤ) from by ring]
        have hcol : c • (∑ j ∈ Finset.range N.toNat,
              kappa P i • (EminusC c' (b - (i : ℤ))).comp
                ((-(α ((j : ℤ) + 1))).comp (aExpCZ c (N - 1 - (j : ℤ) - (i : ℤ)))))
            = kappa P i • (EminusC c' (b - (i : ℤ))).comp
                (((N : ℂ) - (i : ℂ)) • aExpCZ c (N - (i : ℤ))) := by
          rw [← Finset.smul_sum, smul_comm c (kappa P i), hcolbare, ← LinearMap.comp_smul, hreass]
          push_cast
          ring_nf
        rw [hcol, LinearMap.comp_smul, smul_smul]
        rw [hg]
        congr 1
        ring
      -- Part B: reindex to `∑_s (-(2c')·∑_{i<s}κ i)•g s` (with the Newton `c•`).
      have hPartB : c • (∑ j ∈ Finset.range N.toNat, ∑ i ∈ Finset.range (N.toNat + 1),
              (-(2 * c') * kappa P i) • g (i + j + 1))
          = ∑ s ∈ Finset.range (N.toNat + 1),
              (c * (-(2 * c') * ∑ i ∈ Finset.range s, kappa P i)) • g s := by
        rw [show (fun j => ∑ i ∈ Finset.range (N.toNat + 1),
              (-(2 * c') * kappa P i) • g (i + j + 1))
            = (fun j => ∑ i ∈ Finset.range (N.toNat + 1),
              (kappa P i) • ((-(2 * c')) • g (i + j + 1))) from by
            funext j; refine Finset.sum_congr rfl fun i _ => ?_; rw [smul_smul, mul_comm]]
        rw [partB_reindex_gen (fun s => (-(2 * c')) • g s) N.toNat (kappa P)
          (fun s hs => by simp only; rw [hgzero s hs, smul_zero])]
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [smul_smul, smul_smul]; congr 1; ring
      -- Step 4: combine.  hLHS = N⁻¹ • c • (PartA-sum + PartB-sum).
      rw [hLHS, Finset.sum_congr rfl hterm]
      simp only [Finset.sum_add_distrib]
      rw [smul_add, hPartA, hPartB, ← Finset.sum_add_distrib]
      have hcombine : ∀ m ∈ Finset.range (N.toNat + 1),
          (((N : ℂ) - (m : ℂ)) * kappa P m) • g m
              + (c * (-(2 * c') * ∑ i ∈ Finset.range m, kappa P i)) • g m
            = (N : ℂ) • (kappa P m • g m) := by
        intro m _
        rw [← add_smul, smul_smul]
        congr 1
        have hcm : (m : ℂ) * kappa P m = -P * ∑ i ∈ Finset.range m, kappa P i := kappa_combine P m
        -- (N-m)·κ m + c·(-(2c')·∑) = N·κ m, using m·κ m = -P·∑, P = 2cc'.
        rw [hP] at hcm
        linear_combination (-1 : ℂ) * hcm
      rw [Finset.sum_congr rfl hcombine, ← Finset.smul_sum, smul_smul,
        inv_mul_cancel₀ hNne, one_smul]

/-- The `EplusC`/`EminusC` coefficient form of the general contraction (for `a ≤ 0`). -/
theorem EplusC_comp_EminusC_gen (c c' : ℂ) (a b : ℤ) (ha : a ≤ 0) :
    (EplusC c a).comp (EminusC c' b)
      = ∑ m ∈ Finset.range ((-a).toNat + 1),
          kappa (2 * c * c') m • (EminusC c' (b - m)).comp (EplusC c (a + m)) := by
  rw [EplusC_eq_aExpCZ c a, aExpCZ_comp_EminusC_gen c c' (-a) (by omega) b]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [EplusC_eq_aExpCZ c (a + (m : ℤ)), show -(a + (m : ℤ)) = -a - (m : ℤ) from by ring]

/-! ## Geometric (ℤ-finsum) form of the contraction, uniform in `a`. -/

/-- The pairing kernel as a `ℤ → ℂ` function (zero on negatives). -/
noncomputable def kZ (P : ℂ) (i : ℤ) : ℂ := if 0 ≤ i then kappa P i.toNat else 0

theorem kZ_neg (P : ℂ) {i : ℤ} (h : i < 0) : kZ P i = 0 := by rw [kZ, if_neg (by omega)]

theorem kZ_nonneg (P : ℂ) {i : ℤ} (h : 0 ≤ i) : kZ P i = kappa P i.toNat := by
  rw [kZ, if_pos h]

/-- `kZ (Pn:ℂ)` vanishes outside `[0, Pn]`. -/
theorem kZ_nat_vanish (Pn : ℕ) (i : ℤ) (h : (Pn : ℤ) < i) : kZ (Pn : ℂ) i = 0 := by
  rw [kZ_nonneg _ (by omega), kappa_eq_wt, wt_vanish]; omega

/-- Same-sign kernel symmetry: for even nat `Pn`, `kZ (Pn:ℂ) i = kZ (Pn:ℂ) (Pn - i)` for all `i`. -/
theorem kZ_same_symm (Pn : ℕ) (hev : Even Pn) (i : ℤ) :
    kZ (Pn : ℂ) i = kZ (Pn : ℂ) ((Pn : ℤ) - i) := by
  rcases (show i < 0 ∨ (0 ≤ i ∧ i ≤ Pn) ∨ (Pn : ℤ) < i from by omega) with hlt | ⟨h0, hP⟩ | hgt
  · rw [kZ_neg _ hlt, kZ_nat_vanish Pn _ (by omega)]
  · rw [kZ_nonneg _ h0, kZ_nonneg _ (by omega), kappa_eq_wt, kappa_eq_wt,
      wt_symm_even Pn i.toNat hev (by omega),
      show Pn - i.toNat = ((Pn : ℤ) - i).toNat from by omega]
  · rw [kZ_nat_vanish Pn _ hgt, kZ_neg _ (by omega)]

/-- **The `Pn`-fold finite-difference δ-extraction** (the general analog of `kpos_second_diff`):
`∑_{i=0}^{Pn} wt Pn i · kZ (-Pn:ℂ) (s - i) = [s = 0]`. -/
theorem wt_kZ_conv (Pn : ℕ) (s : ℤ) :
    ∑ i ∈ Finset.range (Pn + 1), wt Pn i * kZ (-(Pn : ℂ)) (s - i)
      = if s = 0 then 1 else 0 := by
  rcases (show s < 0 ∨ 0 ≤ s from by omega) with hs | hs
  · rw [if_neg (by omega)]
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [kZ_neg _ (by omega), mul_zero]
  · set sn := s.toNat with hsn
    have hssn : s = (sn : ℤ) := (Int.toNat_of_nonneg hs).symm
    have hconv := kappa_conv (Pn : ℂ) (-(Pn : ℂ)) sn
    rw [show (Pn : ℂ) + -(Pn : ℂ) = 0 from by ring, kappa_zero_kernel] at hconv
    rw [show (if s = 0 then (1 : ℂ) else 0) = (if sn = 0 then (1 : ℂ) else 0) from by
      rw [hssn]; simp, ← hconv, hssn]
    -- Convert LHS body wt·kZ to kappa·kappa (matching hconv), then reconcile ranges.
    have hbody : ∀ i ∈ Finset.range (min (Pn + 1) (sn + 1)),
        wt Pn i * kZ (-(Pn : ℂ)) ((sn : ℤ) - i)
          = kappa (Pn : ℂ) i * kappa (-(Pn : ℂ)) (sn - i) := by
      intro i hi
      simp only [Finset.mem_range, lt_min_iff] at hi
      rw [kappa_eq_wt, kZ_nonneg _ (show (0 : ℤ) ≤ (sn : ℤ) - i by omega),
        show ((sn : ℤ) - i).toNat = sn - i from by omega]
    by_cases hsP : sn ≤ Pn
    · rw [show min (Pn + 1) (sn + 1) = sn + 1 from by omega] at hbody
      rw [show (∑ i ∈ Finset.range (Pn + 1), wt Pn i * kZ (-(Pn : ℂ)) ((sn : ℤ) - i))
            = ∑ i ∈ Finset.range (sn + 1), wt Pn i * kZ (-(Pn : ℂ)) ((sn : ℤ) - i) from
        (Finset.sum_subset (s₁ := Finset.range (sn + 1)) (s₂ := Finset.range (Pn + 1))
          (by intro x hx; simp only [Finset.mem_range] at hx ⊢; omega)
          (fun i _ hi => by
            simp only [Finset.mem_range, not_lt] at hi
            rw [kZ_neg _ (show ((sn : ℤ) - i) < 0 by
              have : (sn : ℤ) < (i : ℤ) := by exact_mod_cast hi
              omega), mul_zero])).symm]
      exact (Finset.sum_congr rfl hbody)
    · rw [show min (Pn + 1) (sn + 1) = Pn + 1 from by omega] at hbody
      rw [show (∑ i ∈ Finset.range (sn + 1), kappa (Pn : ℂ) i * kappa (-(Pn : ℂ)) (sn - i))
            = ∑ i ∈ Finset.range (Pn + 1), kappa (Pn : ℂ) i * kappa (-(Pn : ℂ)) (sn - i) from
        (Finset.sum_subset (s₁ := Finset.range (Pn + 1)) (s₂ := Finset.range (sn + 1))
          (by intro x hx; simp only [Finset.mem_range] at hx ⊢; omega)
          (fun i _ hi => by
            simp only [Finset.mem_range, not_lt] at hi
            rw [kappa_eq_wt, wt_vanish Pn i (by omega), zero_mul])).symm]
      exact (Finset.sum_congr rfl hbody)

/-- **The pointwise contraction as a ℤ-finsum** (uniform in `a`):
`E⁺(cα)_a E⁻(c'α)_q Z = ∑ᶠ_m kZ P m · E⁻(c'α)_{q-m} E⁺(cα)_{a+m} Z`, `P = 2cc'`. -/
theorem EplusC_EminusC_geom (c c' : ℂ) (a q : ℤ) (Z : B) :
    EplusC c a (EminusC c' q Z)
      = ∑ᶠ m : ℤ, kZ (2 * c * c') m • EminusC c' (q - m) (EplusC c (a + m) Z) := by
  set P := 2 * c * c' with hP
  have hsub : (Function.support
      (fun m : ℤ => kZ P m • EminusC c' (q - m) (EplusC c (a + m) Z)))
      ⊆ (Finset.Icc (0 : ℤ) (-a) : Finset ℤ) := by
    intro m hm
    rw [Function.mem_support] at hm
    simp only [Finset.coe_Icc, Set.mem_Icc]
    refine ⟨?_, ?_⟩
    · by_contra h; exact hm (by rw [kZ_neg P (by omega), zero_smul])
    · by_contra h
      rw [EplusC_pos c (show (0 : ℤ) < a + m by omega), LinearMap.zero_apply, map_zero,
        smul_zero] at hm
      exact hm rfl
  rw [finsum_eq_sum_of_support_subset _ hsub]
  by_cases ha : a ≤ 0
  · have hrng := EplusC_comp_EminusC_gen c c' a q ha
    have happ := DFunLike.congr_fun hrng Z
    simp only [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply] at happ
    rw [happ]
    refine Finset.sum_nbij' (fun (i : ℕ) => (i : ℤ)) (fun (m : ℤ) => m.toNat) ?_ ?_ ?_ ?_ ?_
    · intro i hi; simp only [Finset.mem_range] at hi; simp only [Finset.mem_Icc]; omega
    · intro m hm; simp only [Finset.mem_Icc] at hm; simp only [Finset.mem_range]; omega
    · intro i _; simp
    · intro m hm; simp only [Finset.mem_Icc] at hm; exact Int.toNat_of_nonneg hm.1
    · intro i hi
      simp only [Finset.mem_range] at hi
      rw [kZ_nonneg P (show (0 : ℤ) ≤ (i : ℤ) by positivity), Int.toNat_natCast]
  · push_neg at ha
    rw [EplusC_pos c ha, LinearMap.zero_apply]
    refine (Finset.sum_eq_zero fun m hm => ?_).symm
    simp only [Finset.mem_Icc] at hm
    rw [EplusC_pos c (show (0 : ℤ) < a + m by omega), LinearMap.zero_apply, map_zero, smul_zero]

/-! ## The fully normal-ordered four-fold `Wgen` and the OPE expansions. -/

/-- The fully normal-ordered four-fold operator
`Wgen c c' C D = :E⁻(cα)E⁻(c'α)E⁺(cα)E⁺(c'α):` (the general analog of `Wcross`). -/
noncomputable def Wgen (c c' : ℂ) (C D : ℤ) (x : B) : B :=
  ∑ᶠ pq : ℤ × ℤ,
    EminusC c pq.1 (EminusC c' pq.2 (EplusC c (C - pq.1) (EplusC c' (D - pq.2) x)))

/-- The `E⁺(cα)`-shift support is finite. -/
theorem EpC_shift_support_finite (c : ℂ) (b : ℤ) (y : B) :
    (Function.support (fun q : ℤ => EplusC c (b - q) y)).Finite := by
  obtain ⟨B0, hB0⟩ := EplusC_isField c y
  apply Set.Finite.subset (Set.finite_Icc b (b - B0))
  intro q hq
  rw [Function.mem_support] at hq
  rw [Set.mem_Icc]
  refine ⟨?_, ?_⟩
  · by_contra h; exact hq (by rw [EplusC_pos c (show (0 : ℤ) < b - q by omega)]; rfl)
  · by_contra h; exact hq (hB0 (b - q) (by omega))

/-- The cross-charge creation halves commute (both left-mult on commutative `B`). -/
theorem EminusC_comm_crossC (c c' : ℂ) (a b : ℤ) :
    (EminusC c a).comp (EminusC c' b) = (EminusC c' b).comp (EminusC c a) := by
  refine LinearMap.ext fun p => ?_
  simp only [LinearMap.comp_apply]
  by_cases ha : 0 ≤ a
  · by_cases hb : 0 ≤ b
    · rw [EminusC_apply, EminusC_apply, if_pos ha, if_pos hb, EminusOpC, EminusOpC,
        LinearMap.mulLeft_apply, LinearMap.mulLeft_apply, LinearMap.mulLeft_apply,
        LinearMap.mulLeft_apply, mul_left_comm]
    · rw [EminusC_neg c' (show b < 0 by omega)]; simp
  · rw [EminusC_neg c (show a < 0 by omega)]; simp

/-- The cross-charge annihilation halves commute. -/
theorem EplusC_comm_crossC (c c' : ℂ) (a b : ℤ) :
    (EplusC c a).comp (EplusC c' b) = (EplusC c' b).comp (EplusC c a) := by
  rw [EplusC_eq_aExpCZ, EplusC_eq_aExpCZ]
  by_cases ha : 0 ≤ -a
  · by_cases hb : 0 ≤ -b
    · rw [aExpCZ_nonneg c ha, aExpCZ_nonneg c' hb]; exact aExpC_commute_cross c c' _ _
    · rw [aExpCZ_neg c' (show -b < 0 by omega)]; simp
  · rw [aExpCZ_neg c (show -a < 0 by omega)]; simp

theorem EminusC_comm_cross_apply (c c' : ℂ) (q r : ℤ) (Y : B) :
    EminusC c' q (EminusC c r Y) = EminusC c r (EminusC c' q Y) := by
  have h := DFunLike.congr_fun (EminusC_comm_crossC c c' r q) Y
  simpa only [LinearMap.comp_apply] using h.symm

theorem EplusC_comm_cross_apply (c c' : ℂ) (a b : ℤ) (Y : B) :
    EplusC c' a (EplusC c b Y) = EplusC c b (EplusC c' a Y) := by
  have h := DFunLike.congr_fun (EplusC_comm_crossC c c' b a) Y
  simpa only [LinearMap.comp_apply] using h.symm

/-- The marginal `q`-support of `EEC c` is finite. -/
theorem EEC_marg_finite (c : ℂ) (s : ℤ) (x : B) :
    (Function.support (fun q : ℤ => EminusC c q (EplusC c (s - q) x))).Finite := by
  obtain ⟨B0, hB0⟩ := EplusC_isField c x
  apply Set.Finite.subset (Set.finite_Icc (0 : ℤ) (s - B0))
  intro q hq
  rw [Function.mem_support] at hq
  rw [Set.mem_Icc]
  refine ⟨?_, ?_⟩
  · by_contra h; exact hq (by rw [EminusC_neg c (show q < 0 by omega), LinearMap.zero_apply])
  · by_contra h; exact hq (by rw [hB0 (s - q) (by omega), map_zero])

/-- `EEC c C (EEC c' D x)` unfolded into a nested double finsum. -/
theorem EE_nest_gen (c c' : ℂ) (C D : ℤ) (x : B) :
    EEC c C (EEC c' D x) = ∑ᶠ q : ℤ, ∑ᶠ p : ℤ,
      EminusC c p (EplusC c (C - p) (EminusC c' q (EplusC c' (D - q) x))) := by
  rw [EEC_apply_conv c' D x, map_finsum (EEC c C) (EEC_marg_finite c' D x)]
  refine finsum_congr fun q => ?_
  rw [EEC_apply_conv c C]

/-- The four-fold support of `Wgen` is finite. -/
theorem Wgen_fourfold_finite (c c' : ℂ) (C D : ℤ) (x : B) :
    (Function.support (fun pq : ℤ × ℤ =>
      EminusC c pq.1 (EminusC c' pq.2
        (EplusC c (C - pq.1) (EplusC c' (D - pq.2) x))))).Finite := by
  set Sq := Function.support (fun q : ℤ => EplusC c' (D - q) x) with hSq
  have hSqfin : Sq.Finite := EpC_shift_support_finite c' D x
  set P := ⋃ q ∈ Sq, Function.support
      (fun p : ℤ => EplusC c (C - p) (EplusC c' (D - q) x)) with hP
  have hPfin : P.Finite :=
    hSqfin.biUnion (fun q _ => EpC_shift_support_finite c C (EplusC c' (D - q) x))
  apply Set.Finite.subset (hPfin.prod hSqfin)
  intro pq hpq
  rw [Function.mem_support] at hpq
  have hq : pq.2 ∈ Sq := by
    rw [hSq, Function.mem_support]; intro h
    exact hpq (by rw [h, map_zero, map_zero, map_zero])
  refine Set.mem_prod.mpr ⟨?_, hq⟩
  rw [hP]; refine Set.mem_biUnion hq (Function.mem_support.mpr ?_)
  intro h; exact hpq (by rw [h, map_zero, map_zero])

theorem Wgen_eq_nestQ (c c' : ℂ) (C D : ℤ) (x : B) :
    Wgen c c' C D x = ∑ᶠ q : ℤ, ∑ᶠ p : ℤ,
      EminusC c p (EminusC c' q (EplusC c (C - p) (EplusC c' (D - q) x))) := by
  rw [Wgen, ← finsum_comp_equiv (Equiv.prodComm ℤ ℤ)
      (f := fun pq : ℤ × ℤ =>
        EminusC c pq.1 (EminusC c' pq.2 (EplusC c (C - pq.1) (EplusC c' (D - pq.2) x))))]
  rw [finsum_curry _ ((Wgen_fourfold_finite c c' C D x).preimage
      ((Equiv.prodComm ℤ ℤ).injective.injOn))]
  refine finsum_congr fun q => finsum_congr fun p => ?_
  simp only [Equiv.prodComm_apply, Prod.swap_prod_mk]

theorem Wgen_eq_nestP (c c' : ℂ) (C D : ℤ) (x : B) :
    Wgen c c' C D x = ∑ᶠ p : ℤ, ∑ᶠ q : ℤ,
      EminusC c p (EminusC c' q (EplusC c (C - p) (EplusC c' (D - q) x))) := by
  rw [Wgen, finsum_curry _ (Wgen_fourfold_finite c c' C D x)]

theorem Wgen_inner_finite (c c' : ℂ) (C D : ℤ) (x : B) :
    (Function.support (fun q : ℤ => ∑ᶠ p : ℤ,
      EminusC c p (EminusC c' q (EplusC c (C - p) (EplusC c' (D - q) x))))).Finite := by
  apply Set.Finite.subset (EpC_shift_support_finite c' D x)
  intro q hq
  rw [Function.mem_support] at hq ⊢
  intro h
  exact hq (finsum_eq_zero_of_forall_eq_zero fun p => by rw [h, map_zero, map_zero, map_zero])

theorem Wgen_inner_finite_P (c c' : ℂ) (C D : ℤ) (x : B) :
    (Function.support (fun p : ℤ => ∑ᶠ q : ℤ,
      EminusC c p (EminusC c' q (EplusC c (C - p) (EplusC c' (D - q) x))))).Finite := by
  apply Set.Finite.subset ((Wgen_fourfold_finite c c' C D x).image Prod.fst)
  intro p hp
  rw [Function.mem_support] at hp
  obtain ⟨q, hq⟩ : ∃ q : ℤ,
      EminusC c p (EminusC c' q (EplusC c (C - p) (EplusC c' (D - q) x))) ≠ 0 := by
    by_contra hcon; push_neg at hcon
    exact hp (finsum_eq_zero_of_forall_eq_zero hcon)
  exact ⟨(p, q), Function.mem_support.mpr hq, rfl⟩

/-- Per-term geometric expansion: rewrite one nested `(p,q)` summand of `EE_nest_gen` through
the contraction `EplusC_EminusC_geom`, pushing `E⁻(cα)_p` inside the `m`-sum. -/
theorem term_geom_gen (c c' : ℂ) (C D p q : ℤ) (x : B) :
    EminusC c p (EplusC c (C - p) (EminusC c' q (EplusC c' (D - q) x)))
      = ∑ᶠ m : ℤ, kZ (2 * c * c') m • EminusC c p
          (EminusC c' (q - m) (EplusC c (C - p + m) (EplusC c' (D - q) x))) := by
  rw [EplusC_EminusC_geom c c' (C - p) q (EplusC c' (D - q) x)]
  rw [map_finsum (EminusC c p)
    (by
      apply Set.Finite.subset (Set.finite_Icc (0 : ℤ) (p - C))
      intro m hm
      rw [Function.mem_support] at hm
      rw [Set.mem_Icc]
      refine ⟨?_, ?_⟩
      · by_contra h; exact hm (by rw [kZ_neg _ (by omega), zero_smul])
      · by_contra h
        exact hm (by rw [EplusC_pos c (show (0 : ℤ) < C - p + m by omega), LinearMap.zero_apply,
          map_zero, smul_zero])
    : (Function.support (fun m : ℤ =>
        kZ (2 * c * c') m • EminusC c' (q - m) (EplusC c (C - p + m) (EplusC c' (D - q) x)))).Finite)]
  refine finsum_congr fun m => ?_
  rw [map_smul]

/-- The shear `Equiv` on `ℤ³`: `(m, q', p) ↦ (q'+m, p, m)`. -/
def shear3g : (ℤ × ℤ × ℤ) ≃ (ℤ × ℤ × ℤ) where
  toFun := fun mqp => (mqp.2.1 + mqp.1, mqp.2.2, mqp.1)
  invFun := fun qpm => (qpm.2.2, qpm.1 - qpm.2.2, qpm.2.1)
  left_inv := by intro ⟨m, q, p⟩; simp
  right_inv := by intro ⟨q, p, m⟩; simp

/-- The source body `G3g (q,p,m)` of the OPE triple sum. -/
noncomputable def G3g (c c' : ℂ) (C D : ℤ) (x : B) (qpm : ℤ × ℤ × ℤ) : B :=
  kZ (2 * c * c') qpm.2.2 • EminusC c qpm.2.1
    (EminusC c' (qpm.1 - qpm.2.2)
      (EplusC c (C - qpm.2.1 + qpm.2.2) (EplusC c' (D - qpm.1) x)))

theorem G3g_support_finite (c c' : ℂ) (C D : ℤ) (x : B) :
    (Function.support (G3g c c' C D x)).Finite := by
  set Sq := Function.support (fun q : ℤ => EplusC c' (D - q) x) with hSq
  have hSqfin : Sq.Finite := EpC_shift_support_finite c' D x
  set T : Set (ℤ × ℤ × ℤ) :=
    ⋃ q ∈ Sq, ⋃ m ∈ Set.Icc (0 : ℤ) q,
      (fun p : ℤ => (q, p, m)) ''
        Function.support (fun p : ℤ => EplusC c (C + m - p) (EplusC c' (D - q) x)) with hT
  have hTfin : T.Finite := by
    refine hSqfin.biUnion fun q _ => ?_
    refine (Set.finite_Icc (0 : ℤ) q).biUnion fun m _ => ?_
    exact (EpC_shift_support_finite c (C + m) (EplusC c' (D - q) x)).image _
  apply Set.Finite.subset hTfin
  intro qpm hqpm
  obtain ⟨q, p, m⟩ := qpm
  rw [Function.mem_support, G3g] at hqpm
  simp only at hqpm
  have hqS : q ∈ Sq := by
    rw [hSq, Function.mem_support]; intro h
    exact hqpm (by rw [h, map_zero, map_zero, map_zero, smul_zero])
  have hm0 : 0 ≤ m := by
    by_contra h; exact hqpm (by rw [kZ_neg _ (by omega), zero_smul])
  have hmq : m ≤ q := by
    by_contra h
    exact hqpm (by rw [EminusC_neg c' (show q - m < 0 by omega), LinearMap.zero_apply,
      map_zero, smul_zero])
  have hpS : p ∈ Function.support
      (fun p : ℤ => EplusC c (C + m - p) (EplusC c' (D - q) x)) := by
    rw [Function.mem_support]; intro h
    apply hqpm
    rw [show C - p + m = C + m - p from by ring, h, map_zero, map_zero, smul_zero]
  rw [hT, Set.mem_iUnion]
  exact ⟨q, Set.mem_iUnion.mpr ⟨hqS, Set.mem_iUnion.mpr ⟨m, Set.mem_iUnion.mpr
    ⟨Set.mem_Icc.mpr ⟨hm0, hmq⟩, Set.mem_image_of_mem _ hpS⟩⟩⟩⟩

/-- **The first OPE expansion**: the `z₁`-dominant ordering, resummed onto `Wgen`. -/
theorem hExpand1_gen (c c' : ℂ) (C D : ℤ) (x : B) :
    EEC c C (EEC c' D x)
      = ∑ᶠ m : ℤ, kZ (2 * c * c') m • Wgen c c' (C + m) (D - m) x := by
  rw [EE_nest_gen]
  rw [show (∑ᶠ q : ℤ, ∑ᶠ p : ℤ,
        EminusC c p (EplusC c (C - p) (EminusC c' q (EplusC c' (D - q) x))))
      = ∑ᶠ q : ℤ, ∑ᶠ p : ℤ, ∑ᶠ m : ℤ, G3g c c' C D x (q, p, m) from
    finsum_congr fun q => finsum_congr fun p => by rw [term_geom_gen c c' C D p q x]; rfl]
  rw [← finsum_curry₃ (G3g c c' C D x) (G3g_support_finite c c' C D x),
    ← finsum_comp_equiv shear3g (f := G3g c c' C D x),
    finsum_curry₃ _ ((G3g_support_finite c c' C D x).preimage shear3g.injective.injOn)]
  refine finsum_congr fun m => ?_
  rw [show (∑ᶠ q' : ℤ, ∑ᶠ p : ℤ, G3g c c' C D x (shear3g (m, q', p)))
      = ∑ᶠ q' : ℤ, ∑ᶠ p : ℤ, kZ (2 * c * c') m • EminusC c p
          (EminusC c' q' (EplusC c (C + m - p) (EplusC c' (D - m - q') x))) from
    finsum_congr fun q' => finsum_congr fun p => by
      simp only [G3g, shear3g, Equiv.coe_fn_mk]
      rw [show q' + m - m = q' from by ring, show C - p + m = C + m - p from by ring,
        show D - (q' + m) = D - m - q' from by ring]]
  rw [Wgen_eq_nestQ]
  rw [smul_finsum' (kZ (2 * c * c') m) (Wgen_inner_finite c c' (C + m) (D - m) x)]
  refine finsum_congr fun q' => ?_
  rw [smul_finsum' (kZ (2 * c * c') m)
    (by
      apply Set.Finite.subset (EpC_shift_support_finite c (C + m) (EplusC c' (D - m - q') x))
      intro p hp; rw [Function.mem_support] at hp ⊢
      intro h; exact hp (by rw [h, map_zero, map_zero])
    : (Function.support (fun p : ℤ =>
        EminusC c p (EminusC c' q' (EplusC c (C + m - p) (EplusC c' (D - m - q') x))))).Finite)]

/-- Cross `EE`-nesting (second ordering). -/
theorem EE_nest_gen2 (c c' : ℂ) (C D : ℤ) (x : B) :
    EEC c' D (EEC c C x) = ∑ᶠ p : ℤ, ∑ᶠ q : ℤ,
      EminusC c' q (EplusC c' (D - q) (EminusC c p (EplusC c (C - p) x))) := by
  rw [EEC_apply_conv c C x, map_finsum (EEC c' D) (EEC_marg_finite c C x)]
  refine finsum_congr fun p => ?_
  rw [EEC_apply_conv c' D]

/-- Per-term geometric expansion (second ordering). -/
theorem term_geom2_gen (c c' : ℂ) (C D p q : ℤ) (x : B) :
    EminusC c' q (EplusC c' (D - q) (EminusC c p (EplusC c (C - p) x)))
      = ∑ᶠ m : ℤ, kZ (2 * c * c') m • EminusC c (p - m)
          (EminusC c' q (EplusC c (C - p) (EplusC c' (D - q + m) x))) := by
  rw [show (2 * c * c' : ℂ) = 2 * c' * c from by ring] at *
  rw [EplusC_EminusC_geom c' c (D - q) p (EplusC c (C - p) x)]
  rw [map_finsum (EminusC c' q)
    (by
      apply Set.Finite.subset (Set.finite_Icc (0 : ℤ) (q - D))
      intro m hm
      rw [Function.mem_support] at hm
      rw [Set.mem_Icc]
      refine ⟨?_, ?_⟩
      · by_contra h; exact hm (by rw [kZ_neg _ (by omega), zero_smul])
      · by_contra h
        exact hm (by rw [EplusC_pos c' (show (0 : ℤ) < D - q + m by omega), LinearMap.zero_apply,
          map_zero, smul_zero])
    : (Function.support (fun m : ℤ =>
        kZ (2 * c' * c) m • EminusC c (p - m) (EplusC c' (D - q + m) (EplusC c (C - p) x)))).Finite)]
  refine finsum_congr fun m => ?_
  rw [map_smul, EminusC_comm_cross_apply c' c, EplusC_comm_cross_apply c' c]

/-- The source body `G3g' (p,q,m)` of the second OPE triple sum. -/
noncomputable def G3g' (c c' : ℂ) (C D : ℤ) (x : B) (pqm : ℤ × ℤ × ℤ) : B :=
  kZ (2 * c * c') pqm.2.2 • EminusC c (pqm.1 - pqm.2.2)
    (EminusC c' pqm.2.1
      (EplusC c (C - pqm.1) (EplusC c' (D - pqm.2.1 + pqm.2.2) x)))

/-- The pre-reorder body, pointwise equal to `G3g'`. -/
noncomputable def G3gpre (c c' : ℂ) (C D : ℤ) (x : B) (pqm : ℤ × ℤ × ℤ) : B :=
  kZ (2 * c * c') pqm.2.2 • EminusC c' pqm.2.1
    (EminusC c (pqm.1 - pqm.2.2)
      (EplusC c' (D - pqm.2.1 + pqm.2.2) (EplusC c (C - pqm.1) x)))

theorem G3g'_eq_G3gpre (c c' : ℂ) (C D : ℤ) (x : B) : G3g' c c' C D x = G3gpre c c' C D x := by
  funext pqm
  obtain ⟨p, q, m⟩ := pqm
  simp only [G3g', G3gpre]
  rw [EminusC_comm_cross_apply c' c, EplusC_comm_cross_apply c' c]

theorem G3g'_support_finite (c c' : ℂ) (C D : ℤ) (x : B) :
    (Function.support (G3g' c c' C D x)).Finite := by
  rw [G3g'_eq_G3gpre]
  set Sp := Function.support (fun p : ℤ => EplusC c (C - p) x) with hSp
  have hSpfin : Sp.Finite := EpC_shift_support_finite c C x
  set T : Set (ℤ × ℤ × ℤ) :=
    ⋃ p ∈ Sp, ⋃ m ∈ Set.Icc (0 : ℤ) p,
      (fun q : ℤ => (p, q, m)) ''
        Function.support (fun q : ℤ => EplusC c' (D + m - q) (EplusC c (C - p) x)) with hT
  have hTfin : T.Finite := by
    refine hSpfin.biUnion fun p _ => ?_
    refine (Set.finite_Icc (0 : ℤ) p).biUnion fun m _ => ?_
    exact (EpC_shift_support_finite c' (D + m) (EplusC c (C - p) x)).image _
  apply Set.Finite.subset hTfin
  intro pqm hpqm
  obtain ⟨p, q, m⟩ := pqm
  rw [Function.mem_support, G3gpre] at hpqm
  simp only at hpqm
  have hpS : p ∈ Sp := by
    rw [hSp, Function.mem_support]; intro h
    exact hpqm (by rw [h, map_zero, map_zero, map_zero, smul_zero])
  have hm0 : 0 ≤ m := by
    by_contra h; exact hpqm (by rw [kZ_neg _ (by omega), zero_smul])
  have hmp : m ≤ p := by
    by_contra h
    exact hpqm (by rw [EminusC_neg c (show p - m < 0 by omega), LinearMap.zero_apply,
      map_zero, smul_zero])
  have hqS : q ∈ Function.support
      (fun q : ℤ => EplusC c' (D + m - q) (EplusC c (C - p) x)) := by
    rw [Function.mem_support]; intro h
    apply hpqm
    rw [show D - q + m = D + m - q from by ring, h, map_zero, map_zero, smul_zero]
  rw [hT, Set.mem_iUnion]
  exact ⟨p, Set.mem_iUnion.mpr ⟨hpS, Set.mem_iUnion.mpr ⟨m, Set.mem_iUnion.mpr
    ⟨Set.mem_Icc.mpr ⟨hm0, hmp⟩, Set.mem_image_of_mem _ hqS⟩⟩⟩⟩

/-- **The second OPE expansion**: the `z₂`-dominant ordering. -/
theorem hExpand2_gen (c c' : ℂ) (C D : ℤ) (x : B) :
    EEC c' D (EEC c C x)
      = ∑ᶠ m : ℤ, kZ (2 * c * c') m • Wgen c c' (C - m) (D + m) x := by
  rw [EE_nest_gen2]
  rw [show (∑ᶠ p : ℤ, ∑ᶠ q : ℤ,
        EminusC c' q (EplusC c' (D - q) (EminusC c p (EplusC c (C - p) x))))
      = ∑ᶠ p : ℤ, ∑ᶠ q : ℤ, ∑ᶠ m : ℤ, G3g' c c' C D x (p, q, m) from
    finsum_congr fun p => finsum_congr fun q => by rw [term_geom2_gen c c' C D p q x]; rfl]
  rw [← finsum_curry₃ (G3g' c c' C D x) (G3g'_support_finite c c' C D x),
    ← finsum_comp_equiv shear3g (f := G3g' c c' C D x),
    finsum_curry₃ _ ((G3g'_support_finite c c' C D x).preimage shear3g.injective.injOn)]
  refine finsum_congr fun m => ?_
  rw [show (∑ᶠ p' : ℤ, ∑ᶠ q : ℤ, G3g' c c' C D x (shear3g (m, p', q)))
      = ∑ᶠ p' : ℤ, ∑ᶠ q : ℤ, kZ (2 * c * c') m • EminusC c p'
          (EminusC c' q (EplusC c (C - m - p') (EplusC c' (D + m - q) x))) from
    finsum_congr fun p' => finsum_congr fun q => by
      simp only [G3g', shear3g, Equiv.coe_fn_mk]
      rw [show p' + m - m = p' from by ring, show C - (p' + m) = C - m - p' from by ring,
        show D - q + m = D + m - q from by ring]]
  rw [Wgen_eq_nestP]
  rw [smul_finsum' (kZ (2 * c * c') m) (Wgen_inner_finite_P c c' (C - m) (D + m) x)]
  refine finsum_congr fun p' => ?_
  rw [smul_finsum' (kZ (2 * c * c') m)
    (by
      apply Set.Finite.subset (EpC_shift_support_finite c' (D + m) (EplusC c (C - m - p') x))
      intro q hq; rw [Function.mem_support] at hq ⊢
      intro h; exact hq (by
        rw [← EplusC_comm_cross_apply c c' (D + m - q) (C - m - p'), h, map_zero, map_zero])
    : (Function.support (fun q : ℤ =>
        EminusC c p' (EminusC c' q (EplusC c (C - m - p') (EplusC c' (D + m - q) x))))).Finite)]

/-! ## The binomial expansion of `mulBySubPow` (the `Pn`-fold finite difference). -/

/-- `mulBySubPow Pn f m n = ∑_{i=0}^{Pn} wt Pn i • f (m-(Pn-i)) (n-i)`, the binomial expansion
of `(z₁-z₂)^Pn = (shiftZ₁ - shiftZ₂)^Pn` (both shifts commute). -/
theorem mulBySubPow_binom {W : Type*} [AddCommGroup W] [Module ℂ W]
    (Pn : ℕ) (f : FormalDist₂ W) (m n : ℤ) :
    mulBySubPow Pn f m n
      = ∑ i ∈ Finset.range (Pn + 1), wt Pn i • f (m - ((Pn : ℤ) - i)) (n - i) := by
  induction Pn generalizing m n with
  | zero => simp [mulBySubPow_zero, wt]
  | succ k ih =>
    rw [mulBySubPow_succ, LinearMap.comp_apply, mulBySub_apply, ih (m - 1) n, ih m (n - 1)]
    set g : ℕ → W := fun i => f (m - ((k + 1 : ℤ) - i)) (n - i) with hgdef
    have hL : (∑ i ∈ Finset.range (k + 1), wt k i • f (m - 1 - ((k : ℤ) - i)) (n - i))
        = ∑ i ∈ Finset.range (k + 1), wt k i • g i := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hgdef, show m - 1 - ((k : ℤ) - i) = m - ((k + 1 : ℤ) - i) from by ring]
    have hR : (∑ i ∈ Finset.range (k + 1), wt k i • f (m - ((k : ℤ) - i)) (n - 1 - i))
        = ∑ i ∈ Finset.range (k + 1), wt k i • g (i + 1) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hgdef]; congr 2 <;> · push_cast; ring
    rw [hL, hR]
    -- Normalize the RHS `f`-body to `g i` (defeq via the cast `↑(k+1) = (k+1:ℤ)`).
    have hRHS : (∑ i ∈ Finset.range (k + 1 + 1), wt (k + 1) i • f (m - ((k + 1 : ℤ) - i)) (n - i))
        = ∑ i ∈ Finset.range (k + 1 + 1), wt (k + 1) i • g i := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hgdef]
    rw [show (∑ i ∈ Finset.range (k + 1 + 1),
            wt (k + 1) i • f (m - ((↑(k + 1) : ℤ) - i)) (n - i))
          = ∑ i ∈ Finset.range (k + 1 + 1), wt (k + 1) i • g i from by
        rw [← hRHS]; push_cast; rfl]
    -- Goal: (∑_{i<k+1} wt k i•g i) − (∑_{i<k+1} wt k i•g(i+1)) = ∑_{i<k+2} wt(k+1) i•g i.
    -- Expand the RHS over `range (k+2)`; collect `g`-coefficients via Pascal.
    -- RHS = ∑_{i<k+1} (wt k i)•g i  −  ∑_{i<k+1} (wt k i)•g(i+1).
    -- Reindex the second LHS-sum `∑_{i<k+1} wt k i • g(i+1)` to `∑_{j∈[1,k+1]} wt k (j-1) • g j`.
    rw [Finset.sum_range_succ' (fun i => wt (k + 1) i • g i) (k + 1)]
    -- now RHS = (∑_{i<k+1} wt(k+1)(i+1)•g(i+1)) + wt(k+1) 0 • g 0.
    rw [show wt (k + 1) 0 • g 0 = wt k 0 • g 0 from by
      rw [show wt (k + 1) 0 = wt k 0 from by rw [wt, wt]; simp]]
    have hbody : ∀ i ∈ Finset.range (k + 1),
        wt (k + 1) (i + 1) • g (i + 1)
          = (if i = k then (0 : W) else wt k (i + 1) • g (i + 1)) - wt k i • g (i + 1) := by
      intro i hi
      simp only [Finset.mem_range] at hi
      by_cases hik : i = k
      · subst hik
        rw [if_pos rfl, zero_sub, ← neg_smul]; congr 1
        rw [wt, wt, Nat.choose_self, Nat.choose_self]; push_cast; ring
      · rw [if_neg hik, ← sub_smul]; congr 1
        rw [wt, wt, wt, Nat.choose_succ_succ k i]; push_cast; ring
    rw [Finset.sum_congr rfl hbody, Finset.sum_sub_distrib]
    -- The `if`-sum drops its `i=k` term, becoming `∑_{i<k} wt k (i+1)•g(i+1)`.
    rw [show (∑ i ∈ Finset.range (k + 1),
            (if i = k then (0 : W) else wt k (i + 1) • g (i + 1)))
          = ∑ i ∈ Finset.range k, wt k (i + 1) • g (i + 1) from by
        rw [Finset.sum_range_succ, if_pos rfl, add_zero]
        refine Finset.sum_congr rfl fun i hi => ?_
        simp only [Finset.mem_range] at hi; rw [if_neg (by omega)]]
    -- LHS first sum: ∑_{i<k+1} wt k i•g i = wt k 0 • g 0 + ∑_{i<k} wt k (i+1)•g(i+1).
    rw [Finset.sum_range_succ' (fun i => wt k i • g i) k]
    abel

/-! ## §O  The opposite-sign locality (`mm' ≤ -1`, bound `Pn = -2mm'`) -/

/-- The anti-diagonal `s`-support of `s ↦ kZ (-Pn) (s - c) • Wgen cc c' (u+s) (v-s) p` is finite:
`kZ` cuts off `s < c` (since `kZ (-Pn)` vanishes on negatives), and the innermost field
`E⁺(c'α)_{(v-s)-q'} p` forces `s ≤ v - B0(p)`. -/
theorem Wgen_antidiag_shift_finite (Pn : ℕ) (cc c' : ℂ) (u v c : ℤ) (p : B) :
    (Function.support
      (fun s : ℤ => kZ (-(Pn : ℂ)) (s - c) • Wgen cc c' (u + s) (v - s) p)).Finite := by
  obtain ⟨B0, hB0⟩ := EplusC_isField c' p
  apply Set.Finite.subset (Set.finite_Icc c (v - B0))
  intro s hs
  rw [Function.mem_support] at hs
  rw [Set.mem_Icc]
  refine ⟨?_, ?_⟩
  · by_contra h; exact hs (by rw [kZ_neg _ (by omega), zero_smul])
  · by_contra h
    apply hs
    rw [Wgen, finsum_eq_zero_of_forall_eq_zero, smul_zero]
    intro pq
    by_cases hq : 0 ≤ pq.2
    · rw [hB0 ((v - s) - pq.2) (by omega), map_zero, map_zero, map_zero]
    · rw [EminusC_neg c' (show pq.2 < 0 by omega), LinearMap.zero_apply, map_zero]

/-- `Wgen cc c' C D p` vanishes when `C` is below the `E⁺(ccα)`-field lower truncation of `p`:
commute `E⁺(ccα)_{C-p'}` to the innermost (applied to `p`) — forcing `C - p' ≥ B1(p)` with
`p' ≥ 0`, i.e. `C ≥ B1(p)`. -/
theorem Wgen_eq_zero_of_C_small (cc c' : ℂ) (C D : ℤ) (p : B) (B1 : ℤ)
    (hB1 : ∀ n : ℤ, n < B1 → EplusC cc n p = 0) (hC : C < B1) : Wgen cc c' C D p = 0 := by
  rw [Wgen, finsum_eq_zero_of_forall_eq_zero]
  intro pq
  by_cases hp1 : 0 ≤ pq.1
  · rw [← EplusC_comm_cross_apply cc c' (D - pq.2) (C - pq.1) p,
      hB1 (C - pq.1) (by omega), map_zero, map_zero, map_zero]
  · rw [EminusC_neg cc (show pq.1 < 0 by omega), LinearMap.zero_apply]

/-- The reflected anti-diagonal `s`-support of `s ↦ kZ (-Pn) ((-s) - c) • Wgen cc c' (u+s) (v-s) p`
is finite: `kZ` cuts off `s > -c`, and the `E⁺(ccα)`-field on `p` forces `u + s ≥ B1(p)`,
i.e. `s ≥ B1 - u`. -/
theorem Wgen_antidiag_negshift_finite (Pn : ℕ) (cc c' : ℂ) (u v c : ℤ) (p : B) :
    (Function.support
      (fun s : ℤ => kZ (-(Pn : ℂ)) ((-s) - c) • Wgen cc c' (u + s) (v - s) p)).Finite := by
  obtain ⟨B1, hB1⟩ := EplusC_isField cc p
  apply Set.Finite.subset (Set.finite_Icc (B1 - u) (-c))
  intro s hs
  rw [Function.mem_support] at hs
  rw [Set.mem_Icc]
  refine ⟨?_, ?_⟩
  · by_contra h
    exact hs (by rw [Wgen_eq_zero_of_C_small cc c' (u + s) (v - s) p B1 hB1 (by omega),
      smul_zero])
  · by_contra h
    exact hs (by rw [kZ_neg _ (by omega), zero_smul])

/-- **The `Pn`-fold finite-difference collapse, left ordering** (`hExpand1_gen` + `wt_kZ_conv`):
`∑_{i=0}^{Pn} wt Pn i • EEC cc (u+i) (EEC c' (v-i) p) = Wgen cc c' u v p`, when `2·cc·c' = -Pn`. -/
theorem collapseL (Pn : ℕ) (cc c' : ℂ) (hP : 2 * cc * c' = -(Pn : ℂ)) (u v : ℤ) (p : B) :
    (∑ i ∈ Finset.range (Pn + 1), wt Pn i • EEC cc (u + (i : ℤ)) (EEC c' (v - (i : ℤ)) p))
      = Wgen cc c' u v p := by
  -- Rewrite each `i`-term as a `∑ᶠ_s` over the common antidiagonal `Wgen (u+s) (v-s)`.
  have hterm : ∀ i ∈ Finset.range (Pn + 1),
      EEC cc (u + (i : ℤ)) (EEC c' (v - (i : ℤ)) p)
        = ∑ᶠ s : ℤ, kZ (-(Pn : ℂ)) (s - (i : ℤ)) • Wgen cc c' (u + s) (v - s) p := by
    intro i _
    rw [hExpand1_gen cc c' (u + (i : ℤ)) (v - (i : ℤ)) p, hP]
    rw [← finsum_comp_equiv (Equiv.addRight (i : ℤ))
        (f := fun s : ℤ => kZ (-(Pn : ℂ)) (s - (i : ℤ)) • Wgen cc c' (u + s) (v - s) p)]
    refine finsum_congr fun s => ?_
    simp only [Equiv.coe_addRight]
    rw [show s + (i : ℤ) - (i : ℤ) = s from by ring,
      show u + (i : ℤ) + s = u + (s + (i : ℤ)) from by ring,
      show v - (i : ℤ) - s = v - (s + (i : ℤ)) from by ring]
  rw [Finset.sum_congr rfl (fun i hi => by rw [hterm i hi])]
  -- Pull the finite `i`-sum past the `∑ᶠ_s`, collapse the kernel by `wt_kZ_conv`.
  have hsmul : ∀ i ∈ Finset.range (Pn + 1),
      (wt Pn i • ∑ᶠ s : ℤ, kZ (-(Pn : ℂ)) (s - (i : ℤ)) • Wgen cc c' (u + s) (v - s) p)
        = ∑ᶠ s : ℤ, (wt Pn i * kZ (-(Pn : ℂ)) (s - (i : ℤ))) • Wgen cc c' (u + s) (v - s) p := by
    intro i _
    rw [smul_finsum' (wt Pn i) (Wgen_antidiag_shift_finite Pn cc c' u v (i : ℤ) p)]
    refine finsum_congr fun s => ?_
    rw [smul_smul]
  rw [Finset.sum_congr rfl hsmul]
  rw [← finsum_finset_sum_comm (Finset.range (Pn + 1))
      (fun i s => (wt Pn i * kZ (-(Pn : ℂ)) (s - (i : ℤ))) • Wgen cc c' (u + s) (v - s) p)
      (fun i _ => (Wgen_antidiag_shift_finite Pn cc c' u v (i : ℤ) p).subset
        (fun s hs => by
          rw [Function.mem_support] at hs ⊢
          simp only at hs ⊢
          exact fun h => hs (by rw [mul_smul, h, smul_zero])))]
  rw [show (∑ᶠ s : ℤ, ∑ i ∈ Finset.range (Pn + 1),
            (wt Pn i * kZ (-(Pn : ℂ)) (s - (i : ℤ))) • Wgen cc c' (u + s) (v - s) p)
        = ∑ᶠ s : ℤ, (if s = 0 then (1 : ℂ) else 0) • Wgen cc c' (u + s) (v - s) p from
      finsum_congr fun s => by rw [← Finset.sum_smul, ← wt_kZ_conv Pn s]]
  rw [finsum_eq_single _ (0 : ℤ) (fun s hs => by rw [if_neg hs, zero_smul])]
  rw [if_pos rfl, one_smul, show u + 0 = u from by ring, show v - 0 = v from by ring]

/-- **The `Pn`-fold finite-difference collapse, right ordering** (`hExpand2_gen` + `wt_kZ_conv`):
`∑_{i=0}^{Pn} wt Pn i • EEC c' (v+i) (EEC cc (u-i) p) = Wgen cc c' u v p`, when `2·cc·c' = -Pn`. -/
theorem collapseR (Pn : ℕ) (cc c' : ℂ) (hP : 2 * cc * c' = -(Pn : ℂ)) (u v : ℤ) (p : B) :
    (∑ i ∈ Finset.range (Pn + 1), wt Pn i • EEC c' (v + (i : ℤ)) (EEC cc (u - (i : ℤ)) p))
      = Wgen cc c' u v p := by
  -- Land each `i`-term on the SAME `(u+s)(v-s)` antidiagonal, but with the REFLECTED kernel
  -- `kZ(-Pn)((-s)-i)` (the `z₂`-dominant ordering reverses the contraction direction).
  have hterm : ∀ i ∈ Finset.range (Pn + 1),
      EEC c' (v + (i : ℤ)) (EEC cc (u - (i : ℤ)) p)
        = ∑ᶠ s : ℤ, kZ (-(Pn : ℂ)) ((-s) - (i : ℤ)) • Wgen cc c' (u + s) (v - s) p := by
    intro i _
    rw [hExpand2_gen cc c' (u - (i : ℤ)) (v + (i : ℤ)) p, hP]
    rw [← finsum_comp_equiv (Equiv.subLeft (-(i : ℤ)))
        (f := fun s : ℤ => kZ (-(Pn : ℂ)) ((-s) - (i : ℤ)) • Wgen cc c' (u + s) (v - s) p)]
    refine finsum_congr fun s => ?_
    simp only [Equiv.subLeft_apply]
    rw [show -(-(i : ℤ) - s) - (i : ℤ) = s from by ring,
      show u - (i : ℤ) - s = u + (-(i : ℤ) - s) from by ring,
      show v + (i : ℤ) + s = v - (-(i : ℤ) - s) from by ring]
  rw [Finset.sum_congr rfl (fun i hi => by rw [hterm i hi])]
  have hsmul : ∀ i ∈ Finset.range (Pn + 1),
      (wt Pn i • ∑ᶠ s : ℤ, kZ (-(Pn : ℂ)) ((-s) - (i : ℤ)) • Wgen cc c' (u + s) (v - s) p)
        = ∑ᶠ s : ℤ, (wt Pn i * kZ (-(Pn : ℂ)) ((-s) - (i : ℤ))) • Wgen cc c' (u + s) (v - s) p := by
    intro i _
    rw [smul_finsum' (wt Pn i) (Wgen_antidiag_negshift_finite Pn cc c' u v (i : ℤ) p)]
    refine finsum_congr fun s => ?_
    rw [smul_smul]
  rw [Finset.sum_congr rfl hsmul]
  rw [← finsum_finset_sum_comm (Finset.range (Pn + 1))
      (fun i s => (wt Pn i * kZ (-(Pn : ℂ)) ((-s) - (i : ℤ))) • Wgen cc c' (u + s) (v - s) p)
      (fun i _ => (Wgen_antidiag_negshift_finite Pn cc c' u v (i : ℤ) p).subset
        (fun s hs => by
          rw [Function.mem_support] at hs ⊢
          simp only at hs ⊢
          exact fun h => hs (by rw [mul_smul, h, smul_zero])))]
  rw [show (∑ᶠ s : ℤ, ∑ i ∈ Finset.range (Pn + 1),
            (wt Pn i * kZ (-(Pn : ℂ)) ((-s) - (i : ℤ))) • Wgen cc c' (u + s) (v - s) p)
        = ∑ᶠ s : ℤ, (if s = 0 then (1 : ℂ) else 0) • Wgen cc c' (u + s) (v - s) p from
      finsum_congr fun s => by
        rw [← Finset.sum_smul,
          show (if s = 0 then (1 : ℂ) else 0) = (if (-s) = 0 then (1 : ℂ) else 0) from by
            by_cases hs : s = 0 <;> simp [hs],
          ← wt_kZ_conv Pn (-s)]]
  rw [finsum_eq_single _ (0 : ℤ) (fun s hs => by rw [if_neg hs, zero_smul])]
  rw [if_pos rfl, one_smul, show u + 0 = u from by ring, show v - 0 = v from by ring]

/-! ## §Oloc  The opposite-sign bracket `(z₁-z₂)^Pn`-annihilation and locality -/

/-- **The opposite-sign binomial collapse of `term2`**: reindex `i ↦ Pn - i` (using the even
weight symmetry `wt_symm_even`) so the `(V-i, U+i)` summand matches `collapseR`'s `(v+i, u-i)`
shape; it collapses to `Wgen cc c' (U+Pn) (V-Pn) p`. -/
theorem collapseR2 (Pn : ℕ) (cc c' : ℂ) (hP : 2 * cc * c' = -(Pn : ℂ)) (hev : Even Pn)
    (U V : ℤ) (p : B) :
    (∑ i ∈ Finset.range (Pn + 1),
        wt Pn i • EEC c' (V - (i : ℤ)) (EEC cc (U + (i : ℤ)) p))
      = Wgen cc c' (U + (Pn : ℤ)) (V - (Pn : ℤ)) p := by
  rw [← collapseR Pn cc c' hP (U + (Pn : ℤ)) (V - (Pn : ℤ)) p]
  refine (Finset.sum_nbij' (i := fun i => Pn - i) (j := fun i => Pn - i) ?_ ?_ ?_ ?_ ?_).symm
  · intro i hi; simp only [Finset.mem_range] at hi ⊢; omega
  · intro i hi; simp only [Finset.mem_range] at hi ⊢; omega
  · intro i hi; simp only [Finset.mem_range] at hi; simp only []; omega
  · intro i hi; simp only [Finset.mem_range] at hi; simp only []; omega
  · intro i hi
    simp only [Finset.mem_range] at hi
    rw [← wt_symm_even Pn i hev (by omega),
      show ((Pn - i : ℕ) : ℤ) = (Pn : ℤ) - (i : ℤ) from by omega]
    congr 2 <;> ring

/-- **The opposite-sign bracket's `(z₁-z₂)^Pn` finite difference vanishes on every basis state**
(`Pn = -2mm'`).  Via `mulBySubPow_binom` the `Pn`-fold difference of the bracket splits into the
two `EEC`-orderings, each collapsing (`collapseL` / `collapseR2`) to the SAME `Wgen`, which cancel. -/
theorem Yemα_oppSign_bracket_binom_on_state (m m' : ℤ) (hsign : m * m' ≤ -1)
    (j k n : ℤ) (p : B) :
    mulBySubPow ((-2 * m * m').toNat) (bracketDist (Yemα m) (Yemα m')) j k
        (p ⊗ₜ[ℂ] eVec n) = 0 := by
  set Pn : ℕ := (-2 * m * m').toNat with hPndef
  have hPnZ : (Pn : ℤ) = -2 * m * m' := by rw [hPndef, Int.toNat_of_nonneg (by nlinarith)]
  have hPnC : 2 * (m : ℂ) * (m' : ℂ) = -(Pn : ℂ) := by
    have h : ((Pn : ℤ) : ℂ) = ((-2 * m * m' : ℤ) : ℂ) := by exact_mod_cast hPnZ
    push_cast at h; rw [h]; ring
  have hev : Even Pn := by
    refine ⟨(-(m * m')).toNat, ?_⟩
    have : (Pn : ℤ) = (-(m * m')).toNat + (-(m * m')).toNat := by
      rw [hPnZ, Int.toNat_of_nonneg (by nlinarith)]; ring
    exact_mod_cast this
  -- `mulBySubPow_binom` (End-level), then evaluate at the basis state.
  rw [show mulBySubPow Pn (bracketDist (Yemα m) (Yemα m')) j k
        = ∑ i ∈ Finset.range (Pn + 1),
            wt Pn i • bracketDist (Yemα m) (Yemα m') (j - ((Pn : ℤ) - i)) (k - i) from
      mulBySubPow_binom Pn (bracketDist (Yemα m) (Yemα m')) j k]
  rw [LinearMap.coeFn_sum, Finset.sum_apply]
  simp only [LinearMap.smul_apply]
  -- per `i`: reduce the bracket on the basis state.
  rw [show (∑ i ∈ Finset.range (Pn + 1),
          wt Pn i • bracketDist (Yemα m) (Yemα m') (j - ((Pn : ℤ) - i)) (k - i) (p ⊗ₜ[ℂ] eVec n))
        = ∑ i ∈ Finset.range (Pn + 1), wt Pn i •
            ((EEC (m : ℂ) ((j - 2 * m * n) + (i : ℤ)) (EEC (m' : ℂ) ((k - 2 * m' * n) - (i : ℤ)) p)
              - EEC (m' : ℂ) (((k - 2 * m' * n) - 2 * m' * m) - (i : ℤ))
                  (EEC (m : ℂ) (((j - 2 * m * n) + 2 * m * m') + (i : ℤ)) p))
            ⊗ₜ[ℂ] eVec (n + m + m')) from
      Finset.sum_congr rfl fun i _ => by
        rw [reduce_mixed]
        have e1 : (j - ((Pn : ℤ) - i) - 2 * m * n) - 2 * m * m' = (j - 2 * m * n) + (i : ℤ) := by
          rw [hPnZ]; ring
        have e2 : k - i - 2 * m' * n = (k - 2 * m' * n) - (i : ℤ) := by ring
        rw [e1, e2]
        have e3 : (k - 2 * m' * n) - (i : ℤ) - 2 * m' * m
            = ((k - 2 * m' * n) - 2 * m' * m) - (i : ℤ) := by ring
        have e4 : j - ((Pn : ℤ) - i) - 2 * m * n
            = ((j - 2 * m * n) + 2 * m * m') + (i : ℤ) := by rw [hPnZ]; ring
        rw [e3, e4]]
  -- split the difference, pull out `⊗ eVec`, collapse each ordering.
  rw [show (∑ i ∈ Finset.range (Pn + 1), wt Pn i •
          ((EEC (m : ℂ) ((j - 2 * m * n) + (i : ℤ)) (EEC (m' : ℂ) ((k - 2 * m' * n) - (i : ℤ)) p)
            - EEC (m' : ℂ) (((k - 2 * m' * n) - 2 * m' * m) - (i : ℤ))
                (EEC (m : ℂ) (((j - 2 * m * n) + 2 * m * m') + (i : ℤ)) p))
          ⊗ₜ[ℂ] eVec (n + m + m')))
        = ((∑ i ∈ Finset.range (Pn + 1),
              wt Pn i • EEC (m : ℂ) ((j - 2 * m * n) + (i : ℤ))
                (EEC (m' : ℂ) ((k - 2 * m' * n) - (i : ℤ)) p))
            - (∑ i ∈ Finset.range (Pn + 1),
              wt Pn i • EEC (m' : ℂ) (((k - 2 * m' * n) - 2 * m' * m) - (i : ℤ))
                (EEC (m : ℂ) (((j - 2 * m * n) + 2 * m * m') + (i : ℤ)) p)))
          ⊗ₜ[ℂ] eVec (n + m + m') from by
      rw [← Finset.sum_sub_distrib, TensorProduct.sum_tmul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [TensorProduct.smul_tmul', smul_sub]]
  -- LHS-sum collapses (collapseL) ; RHS-sum collapses (collapseR2) ; both equal the same `Wgen`.
  rw [collapseL Pn (m : ℂ) (m' : ℂ) hPnC (j - 2 * m * n) (k - 2 * m' * n) p,
    collapseR2 Pn (m : ℂ) (m' : ℂ) hPnC hev ((j - 2 * m * n) + 2 * m * m')
      ((k - 2 * m' * n) - 2 * m' * m) p]
  rw [show ((j - 2 * m * n) + 2 * m * m') + (Pn : ℤ) = j - 2 * m * n from by rw [hPnZ]; ring,
    show ((k - 2 * m' * n) - 2 * m' * m) - (Pn : ℤ) = k - 2 * m' * n from by rw [hPnZ]; ring,
    sub_self, TensorProduct.zero_tmul]

/-- **The opposite-sign bracket's `(z₁-z₂)^Pn` annihilator vanishes** as a two-variable
distribution (`Pn = -2mm'`).  Lifts `Yemα_oppSign_bracket_binom_on_state` to all of `LatModule`
by `TensorProduct`/`Finsupp` induction. -/
theorem Yemα_oppSign_bracket_binom (m m' : ℤ) (hsign : m * m' ≤ -1) :
    mulBySubPow ((-2 * m * m').toNat) (bracketDist (Yemα m) (Yemα m')) = 0 := by
  refine FormalDist₂.ext fun j k => ?_
  refine LinearMap.ext fun y => ?_
  change mulBySubPow ((-2 * m * m').toNat) (bracketDist (Yemα m) (Yemα m')) j k y = 0
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero]
  | add y1 y2 h1 h2 => rw [map_add, h1, h2, add_zero]
  | tmul p g =>
      induction g using Finsupp.induction_linear with
      | zero => erw [TensorProduct.tmul_zero, map_zero]
      | add g1 g2 h1 h2 => erw [TensorProduct.tmul_add, map_add, h1, h2, add_zero]
      | single nn a =>
          rw [(Finsupp.smul_single_one nn a).symm]
          erw [TensorProduct.tmul_smul, map_smul,
            show (Finsupp.single nn (1 : ℂ) : LatGrp) = eVec nn from rfl,
            Yemα_oppSign_bracket_binom_on_state m m' hsign, smul_zero]

/-- **The opposite-sign mutual locality** `Local (Yemα m) (Yemα m')` (`mm' ≤ -1`,
bound `Pn = -2mm' = 2|m||m'|`). -/
theorem Yemα_oppSign_local (m m' : ℤ) (hsign : m * m' ≤ -1) : Local (Yemα m) (Yemα m') :=
  ⟨(-2 * m * m').toNat, Yemα_oppSign_bracket_binom m m' hsign⟩

/-- **The FULL general charge-pair mutual locality** of the `A₁` lattice vertex operators:
`Local (Yemα m) (Yemα m')` for ALL charges `m, m' : ℤ`.  Assembled by `rcases` on the sign of
`m*m'`: same-sign (`Yemα_sameSign_local`), charge-`0` (`Yemα_zeroLeft/Right_local`), and
opposite-sign (`Yemα_oppSign_local`).  `sorry`/`pbw`-free. -/
theorem Yemα_local (m m' : ℤ) : Local (Yemα m) (Yemα m') := by
  rcases (show 1 ≤ m * m' ∨ m = 0 ∨ m' = 0 ∨ m * m' ≤ -1 from by
    rcases lt_trichotomy (m * m') 0 with h | h | h
    · exact Or.inr (Or.inr (Or.inr (by omega)))
    · rcases mul_eq_zero.mp h with hm | hm'
      · exact Or.inr (Or.inl hm)
      · exact Or.inr (Or.inr (Or.inl hm'))
    · exact Or.inl (by omega)) with hpos | hm0 | hm'0 | hneg
  · exact Yemα_sameSign_local m m' hpos
  · rw [hm0]; exact Yemα_zeroLeft_local m'
  · rw [hm'0]; exact Yemα_zeroRight_local m
  · exact Yemα_oppSign_local m m' hneg

end VOA.LatExp
