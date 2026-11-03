/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.LatticeCrossContraction
import VOA.Examples.LatticeLocalityDiag

/-!
# Cross-charge mutual locality of the charge-`±1` lattice vertex operators

The fourth (cross) entry of the pairwise mutual-locality data for the `A₁` lattice VOA:
`Local (Yemα 1) (Yemα (-1))` (cross pairing `⟨α,-α⟩ = -2`, bound `N = 2`).

Unlike the diagonal (self-pairing `+2`) case — where the lattice operators commute *exactly*
(bound `0`) — the cross pairing `-2` yields the full geometric series with triangular kernel
`(m+1)`, whose `[1,-2,1]` second-difference convolution is a Kronecker `δ`.  The two `OPE`
orderings of the boson dressings `EEC 1`, `EEC (-1)` therefore agree only after multiplying by
`(z₁-z₂)²`, which is exactly bound-`2` mutual locality.

All `sorry`/`admit`/`axiom`/`pbw`-free.
-/

namespace VOA
namespace LatExp

open scoped BigOperators TensorProduct
open Module (End)
open HeisenbergN (vacuumN)
open LatticeVOA (LatModule LatGrp eVec latState latVacuum)

/-! ## §1  Cross-charge half-commutativities -/

/-- The cross-charge creation halves commute (both are left-multiplications on the commutative
ring `B`; mirror of `EminusC_comm`). -/
theorem EminusC1_comm_EminusCm1 (a b : ℤ) :
    (EminusC 1 a).comp (EminusC (-1) b) = (EminusC (-1) b).comp (EminusC 1 a) := by
  refine LinearMap.ext fun p => ?_
  simp only [LinearMap.comp_apply]
  by_cases ha : 0 ≤ a
  · by_cases hb : 0 ≤ b
    · rw [EminusC_apply, EminusC_apply, if_pos ha, if_pos hb, EminusOpC, EminusOpC,
        LinearMap.mulLeft_apply, LinearMap.mulLeft_apply, LinearMap.mulLeft_apply,
        LinearMap.mulLeft_apply, mul_left_comm]
    · rw [EminusC_neg (-1) (show b < 0 by omega)]; simp
  · rw [EminusC_neg 1 (show a < 0 by omega)]; simp

/-- `aExpC` cross-charge commutation: `aExpC c M` commutes with `aExpC c' N` for *any* two
charges (the `α` modes pairwise commute, and the scalar charges are central). -/
theorem aExpC_commute_cross (c c' : ℂ) (M N : ℕ) : Commute (aExpC c M) (aExpC c' N) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    match N with
    | 0 => rw [aExpC_zero]; exact Commute.one_right _
    | (K + 1) =>
      rw [aExpC_succ]
      refine Commute.smul_right (Commute.smul_right ?_ _) _
      refine Commute.sum_right _ _ _ (fun m hm => ?_)
      refine Commute.mul_right ?_ (ih (K - m) (by simp only [Finset.mem_range] at hm; omega))
      exact (aExpC_commute_alpha c M m).neg_right

/-- The cross-charge annihilation halves commute:
`E⁺(α)_a ∘ E⁺(-α)_b = E⁺(-α)_b ∘ E⁺(α)_a` (mirror of `EplusC_comm`). -/
theorem EplusC1_comm_EplusCm1 (a b : ℤ) :
    (EplusC 1 a).comp (EplusC (-1) b) = (EplusC (-1) b).comp (EplusC 1 a) := by
  rw [EplusC_eq_aExpCZ, EplusC_eq_aExpCZ]
  by_cases ha : 0 ≤ -a
  · by_cases hb : 0 ≤ -b
    · rw [aExpCZ_nonneg 1 ha, aExpCZ_nonneg (-1) hb]; exact aExpC_commute_cross 1 (-1) _ _
    · rw [aExpCZ_neg (-1) (show -b < 0 by omega)]; simp
  · rw [aExpCZ_neg 1 (show -a < 0 by omega)]; simp

/-! ## §2  The charge-swapped cross contraction `E⁺(-α)_a E⁻(α)_b` -/

/-- **The charge-swapped cross-charge FLM contraction** (`aExpCZ (-1)`/`EminusC 1` coefficient
form): the `z₁`-dominant reordering of `E⁺(-α,z₁)E⁻(α,z₂)`.  Cross pairing `⟨-α,α⟩ = -2`, so the
**full** geometric series `(1-z₂/z₁)⁻²` with triangular coefficients `m+1`.  Mirror of
`aExpCZ1_comp_EminusCm1` with the left charge `-1` (recursion factor `(-1)`) and the right
creation charge `1` (move residual `2·1`).  Axiom-clean, `pbw`-free. -/
theorem aExpCZm1_comp_EminusC1 (N : ℤ) (hN : 0 ≤ N) (b : ℤ) :
    (aExpCZ (-1) N).comp (EminusC 1 b)
      = ∑ m ∈ Finset.range (N.toNat + 1),
          ((m : ℂ) + 1) • (EminusC 1 (b - m)).comp (aExpCZ (-1) (N - m)) := by
  suffices H : ∀ n : ℕ, ∀ N b : ℤ, N.toNat ≤ n → 0 ≤ N →
      (aExpCZ (-1) N).comp (EminusC 1 b)
        = ∑ m ∈ Finset.range (N.toNat + 1),
            ((m : ℂ) + 1) • (EminusC 1 (b - m)).comp (aExpCZ (-1) (N - m)) by
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
        fun s => (EminusC 1 (b - (s : ℤ))).comp (aExpCZ (-1) (N - (s : ℤ))) with hg
      have hgzero : ∀ s : ℕ, N.toNat < s → g s = 0 := by
        intro s hs
        simp only [hg]
        rw [aExpCZ_neg (-1) (show N - (s : ℤ) < 0 by omega), LinearMap.comp_zero]
      -- Step 1: expand LHS via the (c = -1) Newton recursion (factor `-1`).
      have hLHS : (aExpCZ (-1) N).comp (EminusC 1 b)
          = (N : ℂ)⁻¹ • (-1 : ℂ) • ∑ j ∈ Finset.range N.toNat,
              (-(α ((j : ℤ) + 1))).comp ((aExpCZ (-1) (N - 1 - j)).comp (EminusC 1 b)) := by
        rw [aExpCZ_recursion (-1) N hN1, LinearMap.smul_comp, LinearMap.smul_comp, sum_comp']
        simp only [LinearMap.comp_assoc]
      -- Step 2: per `j`, IH + move `α` past + range-extension to a uniform `i`-range.
      have hterm : ∀ j ∈ Finset.range N.toNat,
          (-(α ((j : ℤ) + 1))).comp ((aExpCZ (-1) (N - 1 - j)).comp (EminusC 1 b))
            = ∑ i ∈ Finset.range (N.toNat + 1),
                ( ((i : ℂ) + 1) • (EminusC 1 (b - (i : ℤ))).comp
                    ((-(α ((j : ℤ) + 1))).comp (aExpCZ (-1) (N - 1 - (j : ℤ) - (i : ℤ))))
                  + (-(2 : ℂ) * ((i : ℂ) + 1)) • g (i + j + 1) ) := by
        intro j hj
        simp only [Finset.mem_range] at hj
        have hNj0 : 0 ≤ N - 1 - (j : ℤ) := by omega
        have hNjn : (N - 1 - (j : ℤ)).toNat ≤ n := by omega
        rw [ih (N - 1 - (j : ℤ)) b hNjn hNj0, comp_sum']
        have hbody : ∀ i ∈ Finset.range ((N - 1 - (j : ℤ)).toNat + 1),
            (-(α ((j : ℤ) + 1))).comp (((i : ℂ) + 1) •
                (EminusC 1 (b - (i : ℤ))).comp (aExpCZ (-1) (N - 1 - (j : ℤ) - (i : ℤ))))
              = ((i : ℂ) + 1) • (EminusC 1 (b - (i : ℤ))).comp
                  ((-(α ((j : ℤ) + 1))).comp (aExpCZ (-1) (N - 1 - (j : ℤ) - (i : ℤ))))
                + (-(2 : ℂ) * ((i : ℂ) + 1)) • g (i + j + 1) := by
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
        have htn : (N - 1 - (j : ℤ)).toNat + 1 ≤ N.toNat + 1 := by
          have hNeq := Int.toNat_of_nonneg hN0
          have : (N - 1 - (j : ℤ)).toNat ≤ N.toNat := by
            rw [Int.toNat_le]; omega
          omega
        refine Finset.sum_subset
          (by intro x hx; simp only [Finset.mem_range] at hx ⊢; omega) ?_
        intro i _ hi
        simp only [Finset.mem_range, not_lt] at hi
        have hibig : (N - 1 - (j : ℤ)).toNat + 1 ≤ (i : ℕ) := by omega
        have h1 : aExpCZ (-1) (N - 1 - (j : ℤ) - (i : ℤ)) = 0 := by
          apply aExpCZ_neg (-1)
          have hle := Int.self_le_toNat (N - 1 - (j : ℤ))
          have : ((N - 1 - (j : ℤ)).toNat : ℤ) + 1 ≤ (i : ℤ) := by exact_mod_cast hibig
          omega
        have h2 : g (i + j + 1) = 0 := by
          simp only [hg]
          rw [aExpCZ_neg (-1) (show N - ((i + j + 1 : ℕ) : ℤ) < 0 by push_cast; omega),
            LinearMap.comp_zero]
        rw [h1, h2, LinearMap.comp_zero, LinearMap.comp_zero, smul_zero, smul_zero, add_zero]
      -- Step 3a: the Part-A double sum reassembles to `∑_i (-(i+1)(N-i))•g i` (factor `-1`).
      have hPartA : (∑ j ∈ Finset.range N.toNat, ∑ i ∈ Finset.range (N.toNat + 1),
              ((i : ℂ) + 1) • (EminusC 1 (b - (i : ℤ))).comp
                ((-(α ((j : ℤ) + 1))).comp (aExpCZ (-1) (N - 1 - (j : ℤ) - (i : ℤ)))))
          = ∑ i ∈ Finset.range (N.toNat + 1),
              ((-1 : ℂ) * (((i : ℂ) + 1) * ((N : ℂ) - (i : ℂ)))) • g i := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i hi => ?_
        simp only [Finset.mem_range] at hi
        rw [← Finset.smul_sum]
        have hidx : ∀ j ∈ Finset.range N.toNat,
            (-(α ((j : ℤ) + 1))).comp (aExpCZ (-1) (N - 1 - (j : ℤ) - (i : ℤ)))
              = (-(α ((j : ℤ) + 1))).comp (aExpCZ (-1) ((N - (i : ℤ)) - 1 - (j : ℤ))) := by
          intro j _
          rw [show N - 1 - (j : ℤ) - (i : ℤ) = (N - (i : ℤ)) - 1 - (j : ℤ) from by ring]
        have hcol : (∑ j ∈ Finset.range N.toNat,
              (EminusC 1 (b - (i : ℤ))).comp
                ((-(α ((j : ℤ) + 1))).comp (aExpCZ (-1) (N - 1 - (j : ℤ) - (i : ℤ)))))
            = (EminusC 1 (b - (i : ℤ))).comp
                ((-1 : ℂ) • (((N : ℂ) - (i : ℂ)) • aExpCZ (-1) (N - (i : ℤ)))) := by
          rw [← comp_sum']
          congr 1
          have hreass := aExpCZ_sum_reassembly (-1) (N - (i : ℤ)) N.toNat
            (by rw [Int.toNat_le]; push_cast [Int.toNat_of_nonneg hN0]; omega)
          rw [Finset.sum_congr rfl hidx]
          -- `hreass : (-1) • ∑ = ↑(N-i) • aExp`, so `∑ = (-1) • (↑(N-i) • aExp)`.
          have : (∑ m ∈ Finset.range N.toNat,
                (-(α ((m : ℤ) + 1))).comp (aExpCZ (-1) ((N - (i : ℤ)) - 1 - (m : ℤ))))
              = (-1 : ℂ) • (((N - (i : ℤ) : ℤ) : ℂ) • aExpCZ (-1) (N - (i : ℤ))) := by
            rw [← hreass, smul_smul]; norm_num
          rw [this, smul_smul, smul_smul]
          congr 1
          push_cast; ring
        rw [hcol, LinearMap.comp_smul, LinearMap.comp_smul, smul_smul, smul_smul]
        simp only [hg]
        congr 1
        ring
      -- Step 3b: the Part-B double sum reindexes to `∑_s (-(s(s+1)))•g s` (factor `-1`).
      have hPartB : (∑ j ∈ Finset.range N.toNat, ∑ i ∈ Finset.range (N.toNat + 1),
              (-(2 : ℂ) * ((i : ℂ) + 1)) • g (i + j + 1))
          = ∑ s ∈ Finset.range (N.toNat + 1), ((-1 : ℂ) * ((s : ℂ) * ((s : ℂ) + 1))) • g s := by
        have key := partB_reindex (M := Module.End ℂ B) (fun s => (-1 : ℂ) • g s) N.toNat
          (fun s hs => by simp only []; rw [hgzero s hs, smul_zero])
        -- Massage `partB_reindex` (with `(-1)•g`) into our negated-kernel form.
        rw [show (fun j => ∑ i ∈ Finset.range (N.toNat + 1),
              (-(2 : ℂ) * ((i : ℂ) + 1)) • g (i + j + 1))
            = (fun j => ∑ i ∈ Finset.range (N.toNat + 1),
              ((2 : ℂ) * ((i : ℂ) + 1)) • ((-1 : ℂ) • g (i + j + 1))) from by
            funext j; refine Finset.sum_congr rfl fun i _ => ?_
            rw [smul_smul]; congr 1; ring]
        rw [key]
        refine Finset.sum_congr rfl fun s _ => ?_
        simp only []
        rw [smul_smul]; congr 1; ring
      -- Step 4: combine Part A + Part B; the `[1]·N` kernel survives, cancel `N⁻¹·N`.
      rw [hLHS, Finset.sum_congr rfl hterm]
      simp only [Finset.sum_add_distrib]
      rw [hPartA, hPartB, ← Finset.sum_add_distrib]
      have hcombine : ∀ m ∈ Finset.range (N.toNat + 1),
          ((-1 : ℂ) * (((m : ℂ) + 1) * ((N : ℂ) - (m : ℂ)))) • g m
              + ((-1 : ℂ) * ((m : ℂ) * ((m : ℂ) + 1))) • g m
            = ((-1 : ℂ) * (N : ℂ)) • (((m : ℂ) + 1) • g m) := by
        intro m _
        rw [← add_smul, smul_smul]
        congr 1
        ring
      rw [Finset.sum_congr rfl hcombine, ← Finset.smul_sum, smul_smul, smul_smul,
        show (N : ℂ)⁻¹ * (-1) * (-1 * (N : ℂ)) = (N : ℂ)⁻¹ * (N : ℂ) from by ring,
        inv_mul_cancel₀ hNne, one_smul]

/-- **The charge-swapped cross contraction** in `E⁺(-α)`/`E⁻(α)` coefficient form (for `a ≤ 0`):
`E⁺(-α)_a ∘ E⁻(α)_b = ∑_{m} (m+1) · E⁻(α)_{b-m} ∘ E⁺(-α)_{a+m}`. -/
theorem EplusCm1_comp_EminusC1 (a b : ℤ) (ha : a ≤ 0) :
    (EplusC (-1) a).comp (EminusC 1 b)
      = ∑ m ∈ Finset.range ((-a).toNat + 1),
          ((m : ℂ) + 1) • (EminusC 1 (b - m)).comp (EplusC (-1) (a + m)) := by
  rw [EplusC_eq_aExpCZ (-1) a, aExpCZm1_comp_EminusC1 (-a) (by omega) b]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [EplusC_eq_aExpCZ (-1) (a + (m : ℤ)),
    show -(a + (m : ℤ)) = -a - (m : ℤ) from by ring]

/-! ## §3  The fully normal-ordered four-fold operator `Wcross` and the OPE expansions -/

/-- The triangular geometric kernel `kpos m = (m+1)` for `m ≥ 0`, `0` otherwise. -/
noncomputable def kpos (m : ℤ) : ℂ := if 0 ≤ m then (m : ℂ) + 1 else 0

theorem kpos_neg {m : ℤ} (h : m < 0) : kpos m = 0 := by rw [kpos, if_neg (by omega)]

theorem kpos_nonneg {m : ℤ} (h : 0 ≤ m) : kpos m = (m : ℂ) + 1 := by rw [kpos, if_pos h]

/-- The fully normal-ordered four-fold cross-charge operator
`Wcross C D = :E⁻(α)E⁻(-α)E⁺(α)E⁺(-α):` (the cross analog of `EEData.Tv`). -/
noncomputable def Wcross (C D : ℤ) (x : B) : B :=
  ∑ᶠ pq : ℤ × ℤ,
    EminusC 1 pq.1 (EminusC (-1) pq.2 (EplusC 1 (C - pq.1) (EplusC (-1) (D - pq.2) x)))

/-! ### Support-finiteness bookkeeping for the cross four-fold sums -/

/-- The `E⁺(-α)`-shift support is finite (it is a field). -/
theorem EpM_shift_support_finite (b : ℤ) (y : B) :
    (Function.support (fun q : ℤ => EplusC (-1) (b - q) y)).Finite := by
  obtain ⟨B0, hB0⟩ := EplusC_isField (-1) y
  apply Set.Finite.subset (Set.finite_Icc b (b - B0))
  intro q hq
  rw [Function.mem_support] at hq
  rw [Set.mem_Icc]
  refine ⟨?_, ?_⟩
  · by_contra h
    exact hq (by rw [EplusC_pos (-1) (show (0 : ℤ) < b - q by omega)]; rfl)
  · by_contra h
    exact hq (hB0 (b - q) (by omega))

/-- The `E⁺(α)`-shift support is finite. -/
theorem EpP_shift_support_finite (b : ℤ) (y : B) :
    (Function.support (fun p : ℤ => EplusC 1 (b - p) y)).Finite := by
  obtain ⟨B0, hB0⟩ := EplusC_isField 1 y
  apply Set.Finite.subset (Set.finite_Icc b (b - B0))
  intro p hp
  rw [Function.mem_support] at hp
  rw [Set.mem_Icc]
  refine ⟨?_, ?_⟩
  · by_contra h
    exact hp (by rw [EplusC_pos 1 (show (0 : ℤ) < b - p by omega)]; rfl)
  · by_contra h
    exact hp (hB0 (b - p) (by omega))

/-- **The pointwise cross contraction as a `ℤ`-finsum** (the `(1-z₂/z₁)⁻²` geometric series,
uniform in `a`): `E⁺(α)_a E⁻(-α)_q Z = ∑ᶠ_m kpos m · E⁻(-α)_{q-m} E⁺(α)_{a+m} Z`.  For `a ≤ 0`
this is the finite range form `EplusC1_comp_EminusCm1`; for `a > 0` both sides vanish. -/
theorem EplusC1_EminusCm1_geom (a q : ℤ) (Z : B) :
    EplusC 1 a (EminusC (-1) q Z)
      = ∑ᶠ m : ℤ, kpos m • EminusC (-1) (q - m) (EplusC 1 (a + m) Z) := by
  -- The ℤ-finsum collapses to `Finset.range ((-a).toNat + 1)` (support subset).
  have hsub : (Function.support
      (fun m : ℤ => kpos m • EminusC (-1) (q - m) (EplusC 1 (a + m) Z)))
      ⊆ (Finset.Icc (0 : ℤ) (-a) : Finset ℤ) := by
    intro m hm
    rw [Function.mem_support] at hm
    simp only [Finset.coe_Icc, Set.mem_Icc]
    refine ⟨?_, ?_⟩
    · by_contra h
      exact hm (by rw [kpos_neg (by omega), zero_smul])
    · by_contra h
      rw [EplusC_pos 1 (show (0 : ℤ) < a + m by omega), LinearMap.zero_apply, map_zero,
        smul_zero] at hm
      exact hm rfl
  rw [finsum_eq_sum_of_support_subset _ hsub]
  by_cases ha : a ≤ 0
  · -- finite range form
    have hrng := EplusC1_comp_EminusCm1 a q ha
    have happ := DFunLike.congr_fun hrng Z
    simp only [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply] at happ
    rw [happ]
    -- Reindex `Finset.range ((-a).toNat+1) → Finset.Icc 0 (-a)` via `i ↦ (i:ℤ)`.
    refine Finset.sum_nbij' (fun (i : ℕ) => (i : ℤ)) (fun (m : ℤ) => m.toNat) ?_ ?_ ?_ ?_ ?_
    · intro i hi; simp only [Finset.mem_range] at hi; simp only [Finset.mem_Icc]; omega
    · intro m hm; simp only [Finset.mem_Icc] at hm; simp only [Finset.mem_range]; omega
    · intro i _; simp
    · intro m hm; simp only [Finset.mem_Icc] at hm; exact Int.toNat_of_nonneg hm.1
    · intro i hi
      simp only [Finset.mem_range] at hi
      rw [kpos_nonneg (show (0 : ℤ) ≤ (i : ℤ) by positivity)]
      push_cast
      ring_nf
  · -- a > 0: both sides vanish
    push_neg at ha
    rw [EplusC_pos 1 ha, LinearMap.zero_apply]
    refine (Finset.sum_eq_zero fun m hm => ?_).symm
    simp only [Finset.mem_Icc] at hm
    rw [EplusC_pos 1 (show (0 : ℤ) < a + m by omega), LinearMap.zero_apply, map_zero, smul_zero]

/-- **The charge-swapped pointwise cross contraction as a `ℤ`-finsum**:
`E⁺(-α)_a E⁻(α)_q Z = ∑ᶠ_m kpos m · E⁻(α)_{q-m} E⁺(-α)_{a+m} Z`. -/
theorem EplusCm1_EminusC1_geom (a q : ℤ) (Z : B) :
    EplusC (-1) a (EminusC 1 q Z)
      = ∑ᶠ m : ℤ, kpos m • EminusC 1 (q - m) (EplusC (-1) (a + m) Z) := by
  have hsub : (Function.support
      (fun m : ℤ => kpos m • EminusC 1 (q - m) (EplusC (-1) (a + m) Z)))
      ⊆ (Finset.Icc (0 : ℤ) (-a) : Finset ℤ) := by
    intro m hm
    rw [Function.mem_support] at hm
    simp only [Finset.coe_Icc, Set.mem_Icc]
    refine ⟨?_, ?_⟩
    · by_contra h
      exact hm (by rw [kpos_neg (by omega), zero_smul])
    · by_contra h
      rw [EplusC_pos (-1) (show (0 : ℤ) < a + m by omega), LinearMap.zero_apply, map_zero,
        smul_zero] at hm
      exact hm rfl
  rw [finsum_eq_sum_of_support_subset _ hsub]
  by_cases ha : a ≤ 0
  · have hrng := EplusCm1_comp_EminusC1 a q ha
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
      rw [kpos_nonneg (show (0 : ℤ) ≤ (i : ℤ) by positivity)]
      push_cast
      ring_nf
  · push_neg at ha
    rw [EplusC_pos (-1) ha, LinearMap.zero_apply]
    refine (Finset.sum_eq_zero fun m hm => ?_).symm
    simp only [Finset.mem_Icc] at hm
    rw [EplusC_pos (-1) (show (0 : ℤ) < a + m by omega), LinearMap.zero_apply, map_zero, smul_zero]

/-! ### The cross `EE`-nesting (mirror of `EEData.EE_nest`) -/

/-- The marginal `q`-support of `EEC c` is finite. -/
theorem EEC_marg_support_finite_c (c : ℂ) (s : ℤ) (x : B) :
    (Function.support (fun q : ℤ => EminusC c q (EplusC c (s - q) x))).Finite := by
  obtain ⟨B0, hB0⟩ := EplusC_isField c x
  apply Set.Finite.subset (Set.finite_Icc (0 : ℤ) (s - B0))
  intro q hq
  rw [Function.mem_support] at hq
  rw [Set.mem_Icc]
  refine ⟨?_, ?_⟩
  · by_contra h
    exact hq (by rw [EminusC_neg c (show q < 0 by omega), LinearMap.zero_apply])
  · by_contra h
    exact hq (by rw [hB0 (s - q) (by omega), map_zero])

/-- **Cross `EE`-nesting**: unfold both `EEC` convolutions into a nested double `finsum`. -/
theorem EE_nest_cross (C D : ℤ) (x : B) :
    EEC 1 C (EEC (-1) D x) = ∑ᶠ q : ℤ, ∑ᶠ p : ℤ,
      EminusC 1 p (EplusC 1 (C - p) (EminusC (-1) q (EplusC (-1) (D - q) x))) := by
  rw [EEC_apply_conv (-1) D x, map_finsum (EEC 1 C) (EEC_marg_support_finite_c (-1) D x)]
  refine finsum_congr fun q => ?_
  rw [EEC_apply_conv 1 C]

/-- The `m`-finsum (cross geometric series) support, for fixed `(C, D, p, q, x)`, is finite:
`kpos m = 0` for `m < 0`, and `E⁺(α)_{C-p+m} = 0` for `m > p - C`. -/
theorem geom_m_support_finite (W : B) (C p q : ℤ) :
    (Function.support (fun m : ℤ =>
      kpos m • EminusC 1 p (EminusC (-1) (q - m) (EplusC 1 (C - p + m) W)))).Finite := by
  apply Set.Finite.subset (Set.finite_Icc (0 : ℤ) (p - C))
  intro m hm
  rw [Function.mem_support] at hm
  rw [Set.mem_Icc]
  refine ⟨?_, ?_⟩
  · by_contra h
    exact hm (by rw [kpos_neg (by omega), zero_smul])
  · by_contra h
    exact hm (by rw [EplusC_pos 1 (show (0 : ℤ) < C - p + m by omega), LinearMap.zero_apply,
      map_zero, map_zero, smul_zero])

/-- **Per-term geometric expansion**: rewrite one nested `(p,q)` summand of `EE_nest_cross`
through the cross contraction `EplusC1_EminusCm1_geom`, pushing `E⁻(α)_p` inside the `m`-sum. -/
theorem term_geom (C D p q : ℤ) (x : B) :
    EminusC 1 p (EplusC 1 (C - p) (EminusC (-1) q (EplusC (-1) (D - q) x)))
      = ∑ᶠ m : ℤ, kpos m • EminusC 1 p
          (EminusC (-1) (q - m) (EplusC 1 (C - p + m) (EplusC (-1) (D - q) x))) := by
  rw [EplusC1_EminusCm1_geom (C - p) q (EplusC (-1) (D - q) x)]
  rw [map_finsum (EminusC 1 p)
    (by
      apply Set.Finite.subset (Set.finite_Icc (0 : ℤ) (p - C))
      intro m hm
      rw [Function.mem_support] at hm
      rw [Set.mem_Icc]
      refine ⟨?_, ?_⟩
      · by_contra h
        exact hm (by rw [kpos_neg (by omega), zero_smul])
      · by_contra h
        exact hm (by rw [EplusC_pos 1 (show (0 : ℤ) < C - p + m by omega), LinearMap.zero_apply,
          map_zero, smul_zero])
    : (Function.support (fun m : ℤ =>
        kpos m • EminusC (-1) (q - m) (EplusC 1 (C - p + m) (EplusC (-1) (D - q) x)))).Finite)]
  refine finsum_congr fun m => ?_
  rw [map_smul]

/-! ### `Wcross` in nested form and the global OPE reindex (`hExpand1`) -/

/-- `Wcross` written as a nested `q`-then-`p` `finsum` (mirror of `EEData.Tv_eq_nestQ`). -/
theorem Wcross_eq_nestQ (C D : ℤ) (x : B) :
    Wcross C D x = ∑ᶠ q : ℤ, ∑ᶠ p : ℤ,
      EminusC 1 p (EminusC (-1) q (EplusC 1 (C - p) (EplusC (-1) (D - q) x))) := by
  -- The product four-fold support is finite; curry it (the `(p,q) ↦ (q,p)` swap).
  have hfin : (Function.support (fun pq : ℤ × ℤ =>
      EminusC 1 pq.1 (EminusC (-1) pq.2 (EplusC 1 (C - pq.1) (EplusC (-1) (D - pq.2) x))))).Finite := by
    -- support ⊆ (E⁺(α) shift support) ×ˢ (E⁺(-α) shift support)
    set Sq := Function.support (fun q : ℤ => EplusC (-1) (D - q) x) with hSq
    have hSqfin : Sq.Finite := EpM_shift_support_finite D x
    set P := ⋃ q ∈ Sq, Function.support
        (fun p : ℤ => EplusC 1 (C - p) (EplusC (-1) (D - q) x)) with hP
    have hPfin : P.Finite :=
      hSqfin.biUnion (fun q _ => EpP_shift_support_finite C (EplusC (-1) (D - q) x))
    apply Set.Finite.subset (hPfin.prod hSqfin)
    intro pq hpq
    rw [Function.mem_support] at hpq
    have hq : pq.2 ∈ Sq := by
      rw [hSq, Function.mem_support]; intro h
      exact hpq (by rw [h, map_zero, map_zero, map_zero])
    refine Set.mem_prod.mpr ⟨?_, hq⟩
    rw [hP]; refine Set.mem_biUnion hq (Function.mem_support.mpr ?_)
    intro h; exact hpq (by rw [h, map_zero, map_zero])
  rw [Wcross, ← finsum_comp_equiv (Equiv.prodComm ℤ ℤ)
      (f := fun pq : ℤ × ℤ =>
        EminusC 1 pq.1 (EminusC (-1) pq.2 (EplusC 1 (C - pq.1) (EplusC (-1) (D - pq.2) x))))]
  rw [finsum_curry _ ((hfin).preimage ((Equiv.prodComm ℤ ℤ).injective.injOn))]
  refine finsum_congr fun q => finsum_congr fun p => ?_
  simp only [Equiv.prodComm_apply, Prod.swap_prod_mk]

/-- The same four-fold support, used for `Wcross_eq_nestP`. -/
theorem Wcross_fourfold_support_finite (C D : ℤ) (x : B) :
    (Function.support (fun pq : ℤ × ℤ =>
      EminusC 1 pq.1 (EminusC (-1) pq.2
        (EplusC 1 (C - pq.1) (EplusC (-1) (D - pq.2) x))))).Finite := by
  set Sq := Function.support (fun q : ℤ => EplusC (-1) (D - q) x) with hSq
  have hSqfin : Sq.Finite := EpM_shift_support_finite D x
  set P := ⋃ q ∈ Sq, Function.support
      (fun p : ℤ => EplusC 1 (C - p) (EplusC (-1) (D - q) x)) with hP
  have hPfin : P.Finite :=
    hSqfin.biUnion (fun q _ => EpP_shift_support_finite C (EplusC (-1) (D - q) x))
  apply Set.Finite.subset (hPfin.prod hSqfin)
  intro pq hpq
  rw [Function.mem_support] at hpq
  have hq : pq.2 ∈ Sq := by
    rw [hSq, Function.mem_support]; intro h
    exact hpq (by rw [h, map_zero, map_zero, map_zero])
  refine Set.mem_prod.mpr ⟨?_, hq⟩
  rw [hP]; refine Set.mem_biUnion hq (Function.mem_support.mpr ?_)
  intro h; exact hpq (by rw [h, map_zero, map_zero])

/-- `Wcross` written as a nested `p`-then-`q` `finsum`. -/
theorem Wcross_eq_nestP (C D : ℤ) (x : B) :
    Wcross C D x = ∑ᶠ p : ℤ, ∑ᶠ q : ℤ,
      EminusC 1 p (EminusC (-1) q (EplusC 1 (C - p) (EplusC (-1) (D - q) x))) := by
  rw [Wcross, finsum_curry _ (Wcross_fourfold_support_finite C D x)]

/-- The `p`-marginal support of `Wcross`'s `p`-outer nested form is finite (bounded by the
projection of the four-fold support onto the `p`-coordinate). -/
theorem Wcross_inner_support_finite_P (C D : ℤ) (x : B) :
    (Function.support (fun p : ℤ => ∑ᶠ q : ℤ,
      EminusC 1 p (EminusC (-1) q (EplusC 1 (C - p) (EplusC (-1) (D - q) x))))).Finite := by
  apply Set.Finite.subset ((Wcross_fourfold_support_finite C D x).image Prod.fst)
  intro p hp
  rw [Function.mem_support] at hp
  -- some `q` makes the four-fold term nonzero; its `p`-projection is `p`.
  obtain ⟨q, hq⟩ : ∃ q : ℤ,
      EminusC 1 p (EminusC (-1) q (EplusC 1 (C - p) (EplusC (-1) (D - q) x))) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hp (finsum_eq_zero_of_forall_eq_zero hcon)
  exact ⟨(p, q), Function.mem_support.mpr hq, rfl⟩

/-- The shear `Equiv` on `ℤ³`: `(m, q', p) ↦ (q'+m, p, m)`, with inverse `(q,p,m) ↦ (m, q-m, p)`.
Carries the target `m`-outer index to the source `q`-outer index of `EE_nest_cross`. -/
def shear3 : (ℤ × ℤ × ℤ) ≃ (ℤ × ℤ × ℤ) where
  toFun := fun mqp => (mqp.2.1 + mqp.1, mqp.2.2, mqp.1)
  invFun := fun qpm => (qpm.2.2, qpm.1 - qpm.2.2, qpm.2.1)
  left_inv := by intro ⟨m, q, p⟩; simp
  right_inv := by intro ⟨q, p, m⟩; simp

/-- The source body `G3 (q,p,m)` of the OPE triple sum. -/
noncomputable def G3 (C D : ℤ) (x : B) (qpm : ℤ × ℤ × ℤ) : B :=
  kpos qpm.2.2 • EminusC 1 qpm.2.1
    (EminusC (-1) (qpm.1 - qpm.2.2)
      (EplusC 1 (C - qpm.2.1 + qpm.2.2) (EplusC (-1) (D - qpm.1) x)))

/-- Joint (`ℤ³`) support finiteness of `G3`, organized as `q ∈ Sq`, `m ∈ Icc 0 q`,
`p ∈` (field shift support at `C+m`). -/
theorem G3_support_finite (C D : ℤ) (x : B) : (Function.support (G3 C D x)).Finite := by
  set Sq := Function.support (fun q : ℤ => EplusC (-1) (D - q) x) with hSq
  have hSqfin : Sq.Finite := EpM_shift_support_finite D x
  set T : Set (ℤ × ℤ × ℤ) :=
    ⋃ q ∈ Sq, ⋃ m ∈ Set.Icc (0 : ℤ) q,
      (fun p : ℤ => (q, p, m)) ''
        Function.support (fun p : ℤ => EplusC 1 (C + m - p) (EplusC (-1) (D - q) x)) with hT
  have hTfin : T.Finite := by
    refine hSqfin.biUnion fun q _ => ?_
    refine (Set.finite_Icc (0 : ℤ) q).biUnion fun m _ => ?_
    exact (EpP_shift_support_finite (C + m) (EplusC (-1) (D - q) x)).image _
  apply Set.Finite.subset hTfin
  intro qpm hqpm
  obtain ⟨q, p, m⟩ := qpm
  rw [Function.mem_support, G3] at hqpm
  simp only at hqpm
  have hqS : q ∈ Sq := by
    rw [hSq, Function.mem_support]; intro h
    exact hqpm (by rw [h, map_zero, map_zero, map_zero, smul_zero])
  have hm0 : 0 ≤ m := by
    by_contra h; exact hqpm (by rw [kpos_neg (by omega), zero_smul])
  have hmq : m ≤ q := by
    by_contra h
    exact hqpm (by rw [EminusC_neg (-1) (show q - m < 0 by omega), LinearMap.zero_apply,
      map_zero, smul_zero])
  have hpS : p ∈ Function.support
      (fun p : ℤ => EplusC 1 (C + m - p) (EplusC (-1) (D - q) x)) := by
    rw [Function.mem_support]; intro h
    apply hqpm
    rw [show C - p + m = C + m - p from by ring, h, map_zero, map_zero, smul_zero]
  rw [hT, Set.mem_iUnion]
  exact ⟨q, Set.mem_iUnion.mpr ⟨hqS, Set.mem_iUnion.mpr ⟨m, Set.mem_iUnion.mpr
    ⟨Set.mem_Icc.mpr ⟨hm0, hmq⟩, Set.mem_image_of_mem _ hpS⟩⟩⟩⟩

/-- The `q`-then-`p` marginal support of `Wcross`'s nested form (for fixed `m`, to pull `kpos m`
out of the inner double sum).  This is the same finite four-fold support as `Wcross_eq_nestQ`. -/
theorem Wcross_inner_support_finite (C D : ℤ) (x : B) :
    (Function.support (fun q : ℤ => ∑ᶠ p : ℤ,
      EminusC 1 p (EminusC (-1) q (EplusC 1 (C - p) (EplusC (-1) (D - q) x))))).Finite := by
  apply Set.Finite.subset (EpM_shift_support_finite D x)
  intro q hq
  rw [Function.mem_support] at hq ⊢
  intro h
  exact hq (finsum_eq_zero_of_forall_eq_zero fun p => by
    rw [h, map_zero, map_zero, map_zero])

/-- **The first OPE expansion** (`hExpand1`): the `z₁`-dominant ordering of the cross boson
dressings, resummed onto the normal-ordered `Wcross` with the triangular kernel `kpos`. -/
theorem hExpand1 (C D : ℤ) (x : B) :
    EEC 1 C (EEC (-1) D x) = ∑ᶠ m : ℤ, kpos m • Wcross (C + m) (D - m) x := by
  -- 1. EE_nest_cross + per-term geometric expansion.
  rw [EE_nest_cross]
  rw [show (∑ᶠ q : ℤ, ∑ᶠ p : ℤ,
        EminusC 1 p (EplusC 1 (C - p) (EminusC (-1) q (EplusC (-1) (D - q) x))))
      = ∑ᶠ q : ℤ, ∑ᶠ p : ℤ, ∑ᶠ m : ℤ, G3 C D x (q, p, m) from
    finsum_congr fun q => finsum_congr fun p => by
      rw [term_geom C D p q x]; rfl]
  -- 2-3. flatten (curry₃ reverse) then shear-reindex (comp_equiv reverse).
  rw [← finsum_curry₃ (G3 C D x) (G3_support_finite C D x),
    ← finsum_comp_equiv shear3 (f := G3 C D x),
    finsum_curry₃ _ ((G3_support_finite C D x).preimage shear3.injective.injOn)]
  -- 4-6. recognize each `m`-slice as `kpos m • Wcross (C+m) (D-m) x`.
  refine finsum_congr fun m => ?_
  rw [show (∑ᶠ q' : ℤ, ∑ᶠ p : ℤ, G3 C D x (shear3 (m, q', p)))
      = ∑ᶠ q' : ℤ, ∑ᶠ p : ℤ, kpos m • EminusC 1 p
          (EminusC (-1) q' (EplusC 1 (C + m - p) (EplusC (-1) (D - m - q') x))) from
    finsum_congr fun q' => finsum_congr fun p => by
      simp only [G3, shear3, Equiv.coe_fn_mk]
      rw [show q' + m - m = q' from by ring, show C - p + m = C + m - p from by ring,
        show D - (q' + m) = D - m - q' from by ring]]
  rw [Wcross_eq_nestQ]
  rw [smul_finsum' (kpos m) (Wcross_inner_support_finite (C + m) (D - m) x)]
  refine finsum_congr fun q' => ?_
  rw [smul_finsum' (kpos m)
    (by
      apply Set.Finite.subset (EpP_shift_support_finite (C + m) (EplusC (-1) (D - m - q') x))
      intro p hp; rw [Function.mem_support] at hp ⊢
      intro h; exact hp (by rw [h, map_zero, map_zero])
    : (Function.support (fun p : ℤ =>
        EminusC 1 p (EminusC (-1) q' (EplusC 1 (C + m - p) (EplusC (-1) (D - m - q') x))))).Finite)]

/-! ### The second OPE expansion `hExpand2` (the `z₂`-dominant ordering) -/

/-- Applied creation-half commutativity: `E⁻(-α)_q E⁻(α)_r Y = E⁻(α)_r E⁻(-α)_q Y`. -/
theorem EminusCm1_EminusC1_apply (q r : ℤ) (Y : B) :
    EminusC (-1) q (EminusC 1 r Y) = EminusC 1 r (EminusC (-1) q Y) := by
  have h := DFunLike.congr_fun (EminusC1_comm_EminusCm1 r q) Y
  simpa only [LinearMap.comp_apply] using h.symm

/-- Applied annihilation-half commutativity: `E⁺(-α)_a E⁺(α)_b Y = E⁺(α)_b E⁺(-α)_a Y`. -/
theorem EplusCm1_EplusC1_apply (a b : ℤ) (Y : B) :
    EplusC (-1) a (EplusC 1 b Y) = EplusC 1 b (EplusC (-1) a Y) := by
  have h := DFunLike.congr_fun (EplusC1_comm_EplusCm1 b a) Y
  simpa only [LinearMap.comp_apply] using h.symm

/-- **Cross `EE`-nesting (second ordering)**. -/
theorem EE_nest_cross2 (C D : ℤ) (x : B) :
    EEC (-1) D (EEC 1 C x) = ∑ᶠ p : ℤ, ∑ᶠ q : ℤ,
      EminusC (-1) q (EplusC (-1) (D - q) (EminusC 1 p (EplusC 1 (C - p) x))) := by
  rw [EEC_apply_conv 1 C x, map_finsum (EEC (-1) D) (EEC_marg_support_finite_c 1 C x)]
  refine finsum_congr fun p => ?_
  rw [EEC_apply_conv (-1) D]

/-- **Per-term geometric expansion (second ordering)**: apply the charge-swapped contraction and
the two creation/annihilation commutativities to land in `Wcross` order. -/
theorem term_geom2 (C D p q : ℤ) (x : B) :
    EminusC (-1) q (EplusC (-1) (D - q) (EminusC 1 p (EplusC 1 (C - p) x)))
      = ∑ᶠ m : ℤ, kpos m • EminusC 1 (p - m)
          (EminusC (-1) q (EplusC 1 (C - p) (EplusC (-1) (D - q + m) x))) := by
  rw [EplusCm1_EminusC1_geom (D - q) p (EplusC 1 (C - p) x)]
  rw [map_finsum (EminusC (-1) q)
    (by
      apply Set.Finite.subset (Set.finite_Icc (0 : ℤ) (q - D))
      intro m hm
      rw [Function.mem_support] at hm
      rw [Set.mem_Icc]
      refine ⟨?_, ?_⟩
      · by_contra h
        exact hm (by rw [kpos_neg (by omega), zero_smul])
      · by_contra h
        exact hm (by rw [EplusC_pos (-1) (show (0 : ℤ) < D - q + m by omega), LinearMap.zero_apply,
          map_zero, smul_zero])
    : (Function.support (fun m : ℤ =>
        kpos m • EminusC 1 (p - m) (EplusC (-1) (D - q + m) (EplusC 1 (C - p) x)))).Finite)]
  refine finsum_congr fun m => ?_
  rw [map_smul, EminusCm1_EminusC1_apply, EplusCm1_EplusC1_apply]

/-- The source body `G3' (p,q,m)` of the second OPE triple sum. -/
noncomputable def G3' (C D : ℤ) (x : B) (pqm : ℤ × ℤ × ℤ) : B :=
  kpos pqm.2.2 • EminusC 1 (pqm.1 - pqm.2.2)
    (EminusC (-1) pqm.2.1
      (EplusC 1 (C - pqm.1) (EplusC (-1) (D - pqm.2.1 + pqm.2.2) x)))

/-- The pre-reorder body (operators in `EE_nest_cross2` order), pointwise equal to `G3'`. -/
noncomputable def G3pre (C D : ℤ) (x : B) (pqm : ℤ × ℤ × ℤ) : B :=
  kpos pqm.2.2 • EminusC (-1) pqm.2.1
    (EminusC 1 (pqm.1 - pqm.2.2)
      (EplusC (-1) (D - pqm.2.1 + pqm.2.2) (EplusC 1 (C - pqm.1) x)))

theorem G3'_eq_G3pre (C D : ℤ) (x : B) : G3' C D x = G3pre C D x := by
  funext pqm
  obtain ⟨p, q, m⟩ := pqm
  simp only [G3', G3pre]
  rw [EminusCm1_EminusC1_apply, EplusCm1_EplusC1_apply]

/-- Joint support finiteness of `G3'` (via the pre-reorder body, bound `p`-outer). -/
theorem G3'_support_finite (C D : ℤ) (x : B) : (Function.support (G3' C D x)).Finite := by
  rw [G3'_eq_G3pre]
  set Sp := Function.support (fun p : ℤ => EplusC 1 (C - p) x) with hSp
  have hSpfin : Sp.Finite := EpP_shift_support_finite C x
  set T : Set (ℤ × ℤ × ℤ) :=
    ⋃ p ∈ Sp, ⋃ m ∈ Set.Icc (0 : ℤ) p,
      (fun q : ℤ => (p, q, m)) ''
        Function.support (fun q : ℤ => EplusC (-1) (D + m - q) (EplusC 1 (C - p) x)) with hT
  have hTfin : T.Finite := by
    refine hSpfin.biUnion fun p _ => ?_
    refine (Set.finite_Icc (0 : ℤ) p).biUnion fun m _ => ?_
    exact (EpM_shift_support_finite (D + m) (EplusC 1 (C - p) x)).image _
  apply Set.Finite.subset hTfin
  intro pqm hpqm
  obtain ⟨p, q, m⟩ := pqm
  rw [Function.mem_support, G3pre] at hpqm
  simp only at hpqm
  have hpS : p ∈ Sp := by
    rw [hSp, Function.mem_support]; intro h
    exact hpqm (by rw [h, map_zero, map_zero, map_zero, smul_zero])
  have hm0 : 0 ≤ m := by
    by_contra h; exact hpqm (by rw [kpos_neg (by omega), zero_smul])
  have hmp : m ≤ p := by
    by_contra h
    exact hpqm (by rw [EminusC_neg 1 (show p - m < 0 by omega), LinearMap.zero_apply,
      map_zero, smul_zero])
  have hqS : q ∈ Function.support
      (fun q : ℤ => EplusC (-1) (D + m - q) (EplusC 1 (C - p) x)) := by
    rw [Function.mem_support]; intro h
    apply hpqm
    rw [show D - q + m = D + m - q from by ring, h, map_zero, map_zero, smul_zero]
  rw [hT, Set.mem_iUnion]
  exact ⟨p, Set.mem_iUnion.mpr ⟨hpS, Set.mem_iUnion.mpr ⟨m, Set.mem_iUnion.mpr
    ⟨Set.mem_Icc.mpr ⟨hm0, hmp⟩, Set.mem_image_of_mem _ hqS⟩⟩⟩⟩

/-- **The second OPE expansion** (`hExpand2`): the `z₂`-dominant ordering. -/
theorem hExpand2 (C D : ℤ) (x : B) :
    EEC (-1) D (EEC 1 C x) = ∑ᶠ m : ℤ, kpos m • Wcross (C - m) (D + m) x := by
  rw [EE_nest_cross2]
  rw [show (∑ᶠ p : ℤ, ∑ᶠ q : ℤ,
        EminusC (-1) q (EplusC (-1) (D - q) (EminusC 1 p (EplusC 1 (C - p) x))))
      = ∑ᶠ p : ℤ, ∑ᶠ q : ℤ, ∑ᶠ m : ℤ, G3' C D x (p, q, m) from
    finsum_congr fun p => finsum_congr fun q => by
      rw [term_geom2 C D p q x]; rfl]
  rw [← finsum_curry₃ (G3' C D x) (G3'_support_finite C D x),
    ← finsum_comp_equiv shear3 (f := G3' C D x),
    finsum_curry₃ _ ((G3'_support_finite C D x).preimage shear3.injective.injOn)]
  refine finsum_congr fun m => ?_
  rw [show (∑ᶠ p' : ℤ, ∑ᶠ q : ℤ, G3' C D x (shear3 (m, p', q)))
      = ∑ᶠ p' : ℤ, ∑ᶠ q : ℤ, kpos m • EminusC 1 p'
          (EminusC (-1) q (EplusC 1 (C - m - p') (EplusC (-1) (D + m - q) x))) from
    finsum_congr fun p' => finsum_congr fun q => by
      simp only [G3', shear3, Equiv.coe_fn_mk]
      rw [show p' + m - m = p' from by ring, show C - (p' + m) = C - m - p' from by ring,
        show D - q + m = D + m - q from by ring]]
  rw [Wcross_eq_nestP]
  rw [smul_finsum' (kpos m) (Wcross_inner_support_finite_P (C - m) (D + m) x)]
  refine finsum_congr fun p' => ?_
  rw [smul_finsum' (kpos m)
    (by
      apply Set.Finite.subset (EpM_shift_support_finite (D + m) x)
      intro q hq; rw [Function.mem_support] at hq ⊢
      intro h; exact hq (by rw [h, map_zero, map_zero, map_zero])
    : (Function.support (fun q : ℤ =>
        EminusC 1 p' (EminusC (-1) q (EplusC 1 (C - m - p')
          (EplusC (-1) (D + m - q) x))))).Finite)]

/-! ## §4  The `[1, -2, 1]` kernel convolution is a Kronecker `δ` -/

/-- **The δ-convolution scalar identity**: `kpos s − 2·kpos(s−1) + kpos(s−2) = [s = 0]`. -/
theorem kpos_second_diff (s : ℤ) :
    kpos s - 2 * kpos (s - 1) + kpos (s - 2) = if s = 0 then 1 else 0 := by
  rcases (show s ≤ -1 ∨ s = 0 ∨ s = 1 ∨ 2 ≤ s from by omega) with h | h | h | h
  · rw [kpos_neg (by omega), kpos_neg (by omega), kpos_neg (by omega), if_neg (by omega)]; ring
  · subst h
    rw [kpos_nonneg (le_refl 0), kpos_neg (by norm_num), kpos_neg (by norm_num), if_pos rfl]
    push_cast; ring
  · subst h
    rw [kpos_nonneg (by norm_num), kpos_nonneg (by norm_num), kpos_neg (by norm_num),
      if_neg (by norm_num)]
    push_cast; ring
  · rw [kpos_nonneg (by omega), kpos_nonneg (by omega), kpos_nonneg (by omega), if_neg (by omega)]
    push_cast; ring

/-- The anti-diagonal `s`-support of `kpos s • Wcross (u+s) (v-s) p` is finite: `kpos` cuts off
`s < 0`, and the innermost `E⁺(-α)_{(v-s)-q'} p` (a field) forces `s ≤ v - B0(p)`. -/
theorem Wcross_antidiag_support_finite (u v : ℤ) (p : B) :
    (Function.support (fun s : ℤ => kpos s • Wcross (u + s) (v - s) p)).Finite := by
  obtain ⟨B0, hB0⟩ := EplusC_isField (-1) p
  apply Set.Finite.subset (Set.finite_Icc (0 : ℤ) (v - B0))
  intro s hs
  rw [Function.mem_support] at hs
  rw [Set.mem_Icc]
  refine ⟨?_, ?_⟩
  · by_contra h
    exact hs (by rw [kpos_neg (by omega), zero_smul])
  · by_contra h
    -- For `s > v - B0`: every `(p',q')` four-fold term vanishes (`E⁺(-α)_{(v-s)-q'} p = 0`).
    apply hs
    rw [Wcross, finsum_eq_zero_of_forall_eq_zero, smul_zero]
    intro pq
    by_cases hq : 0 ≤ pq.2
    · rw [hB0 ((v - s) - pq.2) (by omega), map_zero, map_zero, map_zero]
    · rw [EminusC_neg (-1) (show pq.2 < 0 by omega), LinearMap.zero_apply, map_zero]

/-- The shifted anti-diagonal support `s ↦ kpos (s-c) • Wcross (u+s) (v-s) p` is finite. -/
theorem Wcross_antidiag_shift_support_finite (u v c : ℤ) (p : B) :
    (Function.support (fun s : ℤ => kpos (s - c) • Wcross (u + s) (v - s) p)).Finite := by
  obtain ⟨B0, hB0⟩ := EplusC_isField (-1) p
  apply Set.Finite.subset (Set.finite_Icc c (v - B0))
  intro s hs
  rw [Function.mem_support] at hs
  rw [Set.mem_Icc]
  refine ⟨?_, ?_⟩
  · by_contra h
    exact hs (by rw [kpos_neg (by omega), zero_smul])
  · by_contra h
    apply hs
    rw [Wcross, finsum_eq_zero_of_forall_eq_zero, smul_zero]
    intro pq
    by_cases hq : 0 ≤ pq.2
    · rw [hB0 ((v - s) - pq.2) (by omega), map_zero, map_zero, map_zero]
    · rw [EminusC_neg (-1) (show pq.2 < 0 by omega), LinearMap.zero_apply, map_zero]

/-- **The left second difference equals `Wcross`** (`hExpand1` + the δ-convolution). -/
theorem secondDiff_L (u v : ℤ) (p : B) :
    EEC 1 u (EEC (-1) v p) - (2 : ℂ) • EEC 1 (u + 1) (EEC (-1) (v - 1) p)
        + EEC 1 (u + 2) (EEC (-1) (v - 2) p)
      = Wcross u v p := by
  -- Expand each EEC-product, reindex to the common `Wcross (u+s) (v-s) p`.
  rw [hExpand1 u v p,
    show EEC 1 (u + 1) (EEC (-1) (v - 1) p) = ∑ᶠ s : ℤ, kpos (s - 1) • Wcross (u + s) (v - s) p from by
      rw [hExpand1 (u + 1) (v - 1) p,
        ← finsum_comp_equiv (Equiv.addRight (1 : ℤ))
          (f := fun s : ℤ => kpos (s - 1) • Wcross (u + s) (v - s) p)]
      refine finsum_congr fun m => ?_
      simp only [Equiv.coe_addRight]
      rw [show m + 1 - 1 = m from by ring, show u + (m + 1) = u + 1 + m from by ring,
        show v - (m + 1) = v - 1 - m from by ring],
    show EEC 1 (u + 2) (EEC (-1) (v - 2) p) = ∑ᶠ s : ℤ, kpos (s - 2) • Wcross (u + s) (v - s) p from by
      rw [hExpand1 (u + 2) (v - 2) p,
        ← finsum_comp_equiv (Equiv.addRight (2 : ℤ))
          (f := fun s : ℤ => kpos (s - 2) • Wcross (u + s) (v - s) p)]
      refine finsum_congr fun m => ?_
      simp only [Equiv.coe_addRight]
      rw [show m + 2 - 2 = m from by ring, show u + (m + 2) = u + 2 + m from by ring,
        show v - (m + 2) = v - 2 - m from by ring]]
  -- Combine the three `s`-sums into one, apply the δ identity.
  have hfin0 := Wcross_antidiag_support_finite u v p
  have hfin1 := Wcross_antidiag_shift_support_finite u v 1 p
  have hfin2 := Wcross_antidiag_shift_support_finite u v 2 p
  have hfin1' : (Function.support (fun s : ℤ =>
      (2 : ℂ) • (kpos (s - 1) • Wcross (u + s) (v - s) p))).Finite :=
    hfin1.subset (Function.support_smul_subset_right (fun _ => (2 : ℂ))
      (fun s => kpos (s - 1) • Wcross (u + s) (v - s) p))
  rw [smul_finsum' (2 : ℂ) hfin1,
    ← finsum_sub_distrib hfin0 hfin1',
    ← finsum_add_distrib ((hfin0.union hfin1').subset (Function.support_sub _ _)) hfin2]
  rw [show (∑ᶠ s : ℤ, (kpos s • Wcross (u + s) (v - s) p
          - (2 : ℂ) • (kpos (s - 1) • Wcross (u + s) (v - s) p)
          + kpos (s - 2) • Wcross (u + s) (v - s) p))
      = ∑ᶠ s : ℤ, (if s = 0 then (1 : ℂ) else 0) • Wcross (u + s) (v - s) p from
    finsum_congr fun s => by
      rw [smul_smul, ← kpos_second_diff s]; module]
  rw [finsum_eq_single _ (0 : ℤ) (fun s hs => by rw [if_neg hs, zero_smul])]
  rw [if_pos rfl, one_smul, show u + 0 = u from by ring, show v - 0 = v from by ring]

/-- `Wcross C D p` vanishes when `C` is below the `E⁺(α)`-field lower truncation of `p`:
commuting `E⁺(α)_{C-p'}` to the innermost (applied to `p`) forces `C - p' ≥ B1(p)` with
`p' ≥ 0`, i.e. `C ≥ B1(p)`. -/
theorem Wcross_eq_zero_of_C_small (C D : ℤ) (p : B) (B1 : ℤ)
    (hB1 : ∀ n : ℤ, n < B1 → EplusC 1 n p = 0) (hC : C < B1) : Wcross C D p = 0 := by
  rw [Wcross, finsum_eq_zero_of_forall_eq_zero]
  intro pq
  by_cases hp1 : 0 ≤ pq.1
  · -- commute `E⁺(α)_{C-p'}` past `E⁺(-α)_{D-q'}` to hit `p`, then field-truncate it.
    rw [← EplusCm1_EplusC1_apply (D - pq.2) (C - pq.1) p,
      hB1 (C - pq.1) (by omega), map_zero, map_zero, map_zero]
  · rw [EminusC_neg 1 (show pq.1 < 0 by omega), LinearMap.zero_apply]

/-- The shifted anti-diagonal support `s ↦ kpos (-c - s) • Wcross (u+s) (v-s) p` is finite:
`kpos` cuts off `s > -c`, and the `E⁺(α)`-field on `p` forces `u + s ≥ B1(p)`, i.e. `s ≥ B1 - u`. -/
theorem Wcross_antidiag_negshift_support_finite (u v c : ℤ) (p : B) :
    (Function.support (fun s : ℤ => kpos (-c - s) • Wcross (u + s) (v - s) p)).Finite := by
  obtain ⟨B1, hB1⟩ := EplusC_isField 1 p
  apply Set.Finite.subset (Set.finite_Icc (B1 - u) (-c))
  intro s hs
  rw [Function.mem_support] at hs
  rw [Set.mem_Icc]
  refine ⟨?_, ?_⟩
  · by_contra h
    exact hs (by rw [Wcross_eq_zero_of_C_small (u + s) (v - s) p B1 hB1 (by omega), smul_zero])
  · by_contra h
    exact hs (by rw [kpos_neg (by omega), zero_smul])

/-- **The right second difference equals `Wcross`** (`hExpand2` + the δ-convolution). -/
theorem secondDiff_R (u v : ℤ) (p : B) :
    EEC (-1) v (EEC 1 u p) - (2 : ℂ) • EEC (-1) (v + 1) (EEC 1 (u - 1) p)
        + EEC (-1) (v + 2) (EEC 1 (u - 2) p)
      = Wcross u v p := by
  rw [show EEC (-1) v (EEC 1 u p) = ∑ᶠ s : ℤ, kpos (-s) • Wcross (u + s) (v - s) p from by
      rw [hExpand2 u v p,
        ← finsum_comp_equiv (Equiv.subLeft (0 : ℤ))
          (f := fun s : ℤ => kpos (-s) • Wcross (u + s) (v - s) p)]
      refine finsum_congr fun m => ?_
      simp only [Equiv.subLeft_apply]
      rw [show -(0 - m) = m from by ring, show u + (0 - m) = u - m from by ring,
        show v - (0 - m) = v + m from by ring],
    show EEC (-1) (v + 1) (EEC 1 (u - 1) p)
        = ∑ᶠ s : ℤ, kpos (-1 - s) • Wcross (u + s) (v - s) p from by
      rw [hExpand2 (u - 1) (v + 1) p,
        ← finsum_comp_equiv (Equiv.subLeft (-1 : ℤ))
          (f := fun s : ℤ => kpos (-1 - s) • Wcross (u + s) (v - s) p)]
      refine finsum_congr fun m => ?_
      simp only [Equiv.subLeft_apply]
      rw [show -1 - (-1 - m) = m from by ring, show u + (-1 - m) = u - 1 - m from by ring,
        show v - (-1 - m) = v + 1 + m from by ring],
    show EEC (-1) (v + 2) (EEC 1 (u - 2) p)
        = ∑ᶠ s : ℤ, kpos (-2 - s) • Wcross (u + s) (v - s) p from by
      rw [hExpand2 (u - 2) (v + 2) p,
        ← finsum_comp_equiv (Equiv.subLeft (-2 : ℤ))
          (f := fun s : ℤ => kpos (-2 - s) • Wcross (u + s) (v - s) p)]
      refine finsum_congr fun m => ?_
      simp only [Equiv.subLeft_apply]
      rw [show -2 - (-2 - m) = m from by ring, show u + (-2 - m) = u - 2 - m from by ring,
        show v - (-2 - m) = v + 2 + m from by ring]]
  have hfin0 : (Function.support (fun s : ℤ => kpos (-s) • Wcross (u + s) (v - s) p)).Finite := by
    have := Wcross_antidiag_negshift_support_finite u v 0 p
    simpa only [neg_zero, zero_sub] using this
  have hfin1 := Wcross_antidiag_negshift_support_finite u v 1 p
  have hfin2 := Wcross_antidiag_negshift_support_finite u v 2 p
  have hfin1' : (Function.support (fun s : ℤ =>
      (2 : ℂ) • (kpos (-1 - s) • Wcross (u + s) (v - s) p))).Finite :=
    hfin1.subset (Function.support_smul_subset_right (fun _ => (2 : ℂ))
      (fun s => kpos (-1 - s) • Wcross (u + s) (v - s) p))
  rw [smul_finsum' (2 : ℂ) hfin1,
    ← finsum_sub_distrib hfin0 hfin1',
    ← finsum_add_distrib ((hfin0.union hfin1').subset (Function.support_sub _ _)) hfin2]
  rw [show (∑ᶠ s : ℤ, (kpos (-s) • Wcross (u + s) (v - s) p
          - (2 : ℂ) • (kpos (-1 - s) • Wcross (u + s) (v - s) p)
          + kpos (-2 - s) • Wcross (u + s) (v - s) p))
      = ∑ᶠ s : ℤ, (if s = 0 then (1 : ℂ) else 0) • Wcross (u + s) (v - s) p from
    finsum_congr fun s => by
      have hδ := kpos_second_diff (-s)
      rw [show -s - 1 = -1 - s from by ring, show -s - 2 = -2 - s from by ring,
        show (if -s = 0 then (1 : ℂ) else 0) = (if s = 0 then (1 : ℂ) else 0) from by
          by_cases hs : s = 0 <;> simp [hs]] at hδ
      rw [smul_smul, ← hδ]; module]
  rw [finsum_eq_single _ (0 : ℤ) (fun s hs => by rw [if_neg hs, zero_smul])]
  rw [if_pos rfl, one_smul, show u + 0 = u from by ring, show v - 0 = v from by ring]

/-! ## §5  The cross bracket, its second difference, and the main locality theorem -/

/-- **The cross bracket on a basis state** `p ⊗ e^{nα}`, in the `u = j-2n`, `v = k+2n` variables. -/
theorem Yemα_cross_bracket_on_state (j k n : ℤ) (p : B) :
    bracketDist (Yemα 1) (Yemα (-1)) j k (p ⊗ₜ[ℂ] eVec n)
      = (EEC 1 ((j - 2 * n) + 2) (EEC (-1) (k + 2 * n) p)
          - EEC (-1) ((k + 2 * n) + 2) (EEC 1 (j - 2 * n) p)) ⊗ₜ[ℂ] eVec n := by
  rw [bracketDist_apply, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply]
  rw [Yemα_tmul, Yemα_tmul, Yemα_tmul, Yemα_tmul]
  rw [show n + (-1) = n - 1 from by ring, show n + 1 = n + 1 from rfl]
  rw [show (k - 2 * (-1) * n : ℤ) = k + 2 * n from by ring,
    show (j - 2 * 1 * (n - 1) : ℤ) = (j - 2 * n) + 2 from by ring,
    show (j - 2 * 1 * n : ℤ) = j - 2 * n from by ring,
    show (k - 2 * (-1) * (n + 1) : ℤ) = (k + 2 * n) + 2 from by ring,
    show (n - 1 + 1 : ℤ) = n from by ring, show (n + 1 + -1 : ℤ) = n from by ring]
  simp only [Int.cast_one, Int.cast_neg]
  rw [← TensorProduct.sub_tmul]

/-- **The cross bracket's second difference vanishes on every basis state** — in the exact form
produced by `mulBySub (mulBySub …)` (no auxiliary `smul`).  Both `secondDiff_L` and `secondDiff_R`
collapse to `Wcross u v p`, which cancel. -/
theorem Yemα_cross_bracket_sdiff_on_state (j k n : ℤ) (p : B) :
    bracketDist (Yemα 1) (Yemα (-1)) (j - 2) k (p ⊗ₜ[ℂ] eVec n)
        - bracketDist (Yemα 1) (Yemα (-1)) (j - 1) (k - 1) (p ⊗ₜ[ℂ] eVec n)
      - (bracketDist (Yemα 1) (Yemα (-1)) (j - 1) (k - 1) (p ⊗ₜ[ℂ] eVec n)
          - bracketDist (Yemα 1) (Yemα (-1)) j (k - 2) (p ⊗ₜ[ℂ] eVec n)) = 0 := by
  simp only [Yemα_cross_bracket_on_state]
  set u := j - 2 * n with hu
  set v := k + 2 * n with hv
  rw [show (j - 2 - 2 * n : ℤ) = u - 2 from by rw [hu]; ring,
    show (j - 1 - 2 * n : ℤ) = u - 1 from by rw [hu]; ring,
    show (k - 1 + 2 * n : ℤ) = v - 1 from by rw [hv]; ring,
    show (k - 2 + 2 * n : ℤ) = v - 2 from by rw [hv]; ring]
  rw [← TensorProduct.sub_tmul, ← TensorProduct.sub_tmul, ← TensorProduct.sub_tmul]
  rw [show (EEC 1 (u - 2 + 2) (EEC (-1) v p) - EEC (-1) (v + 2) (EEC 1 (u - 2) p)
          - (EEC 1 (u - 1 + 2) (EEC (-1) (v - 1) p) - EEC (-1) (v - 1 + 2) (EEC 1 (u - 1) p))
          - (EEC 1 (u - 1 + 2) (EEC (-1) (v - 1) p) - EEC (-1) (v - 1 + 2) (EEC 1 (u - 1) p)
              - (EEC 1 (u + 2) (EEC (-1) (v - 2) p) - EEC (-1) (v - 2 + 2) (EEC 1 u p))))
      = (EEC 1 u (EEC (-1) v p) - (2 : ℂ) • EEC 1 (u + 1) (EEC (-1) (v - 1) p)
          + EEC 1 (u + 2) (EEC (-1) (v - 2) p))
        - (EEC (-1) v (EEC 1 u p) - (2 : ℂ) • EEC (-1) (v + 1) (EEC 1 (u - 1) p)
            + EEC (-1) (v + 2) (EEC 1 (u - 2) p)) from by
      rw [show u - 2 + 2 = u from by ring, show u - 1 + 2 = u + 1 from by ring,
        show v - 1 + 2 = v + 1 from by ring, show v - 2 + 2 = v from by ring]
      simp only [two_smul]
      abel]
  rw [secondDiff_L u v p, secondDiff_R u v p, sub_self, TensorProduct.zero_tmul]

/-- **The cross bracket's second power `(z₁ - z₂)²` annihilator vanishes** as a two-variable
distribution. -/
theorem Yemα_cross_bracket_sdiff :
    mulBySubPow 2 (bracketDist (Yemα 1) (Yemα (-1))) = 0 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, mulBySubPow_succ', mulBySubPow_one]
  refine FormalDist₂.ext fun j k => ?_
  refine LinearMap.ext fun y => ?_
  rw [mulBySub_apply, mulBySub_apply, mulBySub_apply]
  show bracketDist (Yemα 1) (Yemα (-1)) (j - 1 - 1) k y
      - bracketDist (Yemα 1) (Yemα (-1)) (j - 1) (k - 1) y
    - (bracketDist (Yemα 1) (Yemα (-1)) (j - 1) (k - 1) y
        - bracketDist (Yemα 1) (Yemα (-1)) j (k - 1 - 1) y)
    = (0 : FormalDist₂ (Module.End ℂ LatModule)) j k y
  rw [show (0 : FormalDist₂ (Module.End ℂ LatModule)) j k y = (0 : LatModule) from rfl,
    show j - 1 - 1 = j - 2 from by ring, show k - 1 - 1 = k - 2 from by ring]
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero, sub_zero, sub_self]
  | add y1 y2 h1 h2 =>
      simp only [map_add]
      rw [show ∀ a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ : LatModule,
            (a₁ + a₂) - (b₁ + b₂) - ((c₁ + c₂) - (d₁ + d₂))
              = (a₁ - b₁ - (c₁ - d₁)) + (a₂ - b₂ - (c₂ - d₂)) from
          fun a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ => by abel]
      rw [h1, h2, add_zero]
  | tmul p g =>
      induction g using Finsupp.induction_linear with
      | zero => erw [TensorProduct.tmul_zero]; simp only [map_zero, sub_zero, sub_self]
      | add g1 g2 h1 h2 =>
          erw [TensorProduct.tmul_add]
          simp only [map_add]
          rw [show ∀ a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ : LatModule,
                (a₁ + a₂) - (b₁ + b₂) - ((c₁ + c₂) - (d₁ + d₂))
                  = (a₁ - b₁ - (c₁ - d₁)) + (a₂ - b₂ - (c₂ - d₂)) from
              fun a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ => by abel]
          rw [h1, h2, add_zero]
      | single n a =>
          rw [(Finsupp.smul_single_one n a).symm]
          erw [TensorProduct.tmul_smul]
          simp only [map_smul, ← smul_sub]
          erw [Yemα_cross_bracket_sdiff_on_state]
          rw [smul_zero]

/-- **`Local (Yemα 1) (Yemα (-1))`** — the cross-charge mutual locality of the `A₁` lattice vertex
operators (cross pairing `⟨α,-α⟩ = -2`, bound `N = 2`).  `sorry`/`pbw`-free. -/
theorem Yemα_cross_local : Local (Yemα 1) (Yemα (-1)) := ⟨2, Yemα_cross_bracket_sdiff⟩

end LatExp
end VOA
