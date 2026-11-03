/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.LatticeChargeMFields
import VOA.Examples.LatticeLocalityCore

/-!
# The charge-`c` FLM exponential contraction (self-pairing `⟨cα,cα⟩ = 2c²`)

The charge-`c` generalization of the `LatExp.LatticeFields` §8 contraction
`E⁺(α,z₁)E⁻(α,z₂) = (1-z₂/z₁)²·E⁻(α,z₂)E⁺(α,z₁)`.  For a self-pairing charge `c` with `c² = 1`
(i.e. `c = ±1`, `⟨cα,cα⟩ = 2c² = 2`) the contraction is again the three-term `(1-z₂/z₁)²` shift:
`E⁺(cα)_a E⁻(cα)_b = E⁻(cα)_b E⁺(cα)_a − 2 E⁻(cα)_{b-1} E⁺(cα)_{a+1} + E⁻(cα)_{b-2} E⁺(cα)_{a+2}`.

Together with the field/commutativity helpers (`EplusC_pos`, `EminusC_comm`, `EplusC_comm`,
`EEC_apply_conv`) this packages the charge-`c` boson factor into an `EEData` (`LatticeLocalityCore`),
yielding the charge-`±1` diagonal mutual locality.  All `sorry`-free, `pbw`-free.
-/

namespace VOA
namespace LatExp

open scoped BigOperators
open Module (End)
open HeisenbergN (oscN vacuumN)

/-! ## §A  Field/commutativity helpers for the charge-`c` halves -/

/-- `E⁺(cα)` is annihilation-only: zero on strictly positive `z`-powers. -/
theorem EplusC_pos (c : ℂ) {t : ℤ} (ht : 0 < t) : EplusC c t = 0 := by
  rw [EplusC_apply, if_neg (by omega)]

/-- The charge-`c` creation halves commute (both are left-multiplications on the commutative
ring `B`). -/
theorem EminusC_comm (c : ℂ) (a b : ℤ) :
    (EminusC c a).comp (EminusC c b) = (EminusC c b).comp (EminusC c a) := by
  refine LinearMap.ext fun p => ?_
  simp only [LinearMap.comp_apply]
  by_cases ha : 0 ≤ a
  · by_cases hb : 0 ≤ b
    · rw [EminusC_apply, EminusC_apply, if_pos ha, if_pos hb, EminusOpC, EminusOpC,
        LinearMap.mulLeft_apply, LinearMap.mulLeft_apply, LinearMap.mulLeft_apply,
        LinearMap.mulLeft_apply, mul_left_comm]
    · rw [EminusC_neg c (show b < 0 by omega)]; simp
  · rw [EminusC_neg c (show a < 0 by omega)]; simp

/-! ## §B  The ℤ-extended charge-`c` annihilation exponential `aExpCZ` -/

/-- ℤ-extension of `aExpC c` (the `E⁺(cα)` mode coefficient), zero on negative indices. -/
noncomputable def aExpCZ (c : ℂ) (N : ℤ) : Module.End ℂ B := if 0 ≤ N then aExpC c N.toNat else 0

theorem aExpCZ_neg (c : ℂ) {N : ℤ} (h : N < 0) : aExpCZ c N = 0 := by
  rw [aExpCZ, if_neg (by omega)]

theorem aExpCZ_nonneg (c : ℂ) {N : ℤ} (h : 0 ≤ N) : aExpCZ c N = aExpC c N.toNat := by
  rw [aExpCZ, if_pos h]

theorem aExpCZ_zero (c : ℂ) : aExpCZ c 0 = LinearMap.id := by
  rw [aExpCZ_nonneg c le_rfl]; simp [aExpC_zero]

/-- `E⁺(cα)` coefficient as the ℤ-extended `aExpC`: `EplusC c a = aExpCZ c (-a)`. -/
theorem EplusC_eq_aExpCZ (c : ℂ) (a : ℤ) : EplusC c a = aExpCZ c (-a) := by
  rw [EplusC_apply, aExpCZ]
  by_cases h : a ≤ 0
  · rw [if_pos h, if_pos (by omega)]
  · rw [if_neg h, if_neg (by omega)]

/-- The `aExpC` Newton recursion, ℤ-extended: for `N ≥ 1`,
`aExpCZ c N = N⁻¹ • c • ∑_{m<N} (-α_{m+1}) ∘ aExpCZ c (N-1-m)`. -/
theorem aExpCZ_recursion (c : ℂ) (N : ℤ) (hN : 1 ≤ N) :
    aExpCZ c N = (N : ℂ)⁻¹ • c • ∑ m ∈ Finset.range N.toNat,
      (-(α ((m : ℤ) + 1))).comp (aExpCZ c (N - 1 - m)) := by
  obtain ⟨K, hK⟩ : ∃ K : ℕ, N.toNat = K + 1 := ⟨N.toNat - 1, by omega⟩
  have hNK : N = (K : ℤ) + 1 := by omega
  rw [aExpCZ_nonneg c (by omega), hK, aExpC_succ, hNK]
  push_cast
  congr 2
  apply Finset.sum_congr rfl
  intro m hm
  simp only [Finset.mem_range] at hm
  congr 2
  rw [aExpCZ_nonneg c (by omega)]
  congr 1
  omega

/-- Reassembly (all `L : ℤ`): for any range `K ≥ L.toNat`, `c • (Newton sum) = L • aExpCZ c L`. -/
theorem aExpCZ_sum_reassembly (c : ℂ) (L : ℤ) (K : ℕ) (hK : L.toNat ≤ K) :
    c • ∑ m ∈ Finset.range K, (-(α ((m : ℤ) + 1))).comp (aExpCZ c (L - 1 - m))
      = (L : ℂ) • aExpCZ c L := by
  by_cases hL : 1 ≤ L
  · have hsplit : ∑ m ∈ Finset.range K, (-(α ((m : ℤ) + 1))).comp (aExpCZ c (L - 1 - m))
        = ∑ m ∈ Finset.range L.toNat, (-(α ((m : ℤ) + 1))).comp (aExpCZ c (L - 1 - m)) := by
      refine (Finset.sum_subset (s₁ := Finset.range L.toNat) (s₂ := Finset.range K)
        (by intro x hx; simp only [Finset.mem_range] at hx ⊢; omega) ?_).symm
      intro m _ hm
      simp only [Finset.mem_range, not_lt] at hm
      rw [aExpCZ_neg c (by omega), LinearMap.comp_zero]
    rw [hsplit, aExpCZ_recursion c L hL, smul_smul, smul_smul,
      mul_inv_cancel₀ (by simp only [ne_eq]; exact_mod_cast (by omega : (L : ℤ) ≠ 0)), one_mul]
  · have hsum0 : ∑ m ∈ Finset.range K, (-(α ((m : ℤ) + 1))).comp (aExpCZ c (L - 1 - m)) = 0 := by
      refine Finset.sum_eq_zero fun m _ => ?_
      rw [aExpCZ_neg c (by omega), LinearMap.comp_zero]
    rw [hsum0, smul_zero]
    rcases lt_or_eq_of_le (by omega : L ≤ 0) with hlt | heq
    · rw [aExpCZ_neg c hlt, smul_zero]
    · subst heq; simp

/-! ## §C  The single-mode charge-`c` contraction and the move lemma -/

/-- Helper: `EminusC c t = EminusOpC c t.toNat` for `t ≥ 0`. -/
theorem EminusC_nonneg (c : ℂ) {t : ℤ} (ht : 0 ≤ t) : EminusC c t = EminusOpC c t.toNat := by
  rw [EminusC_apply, if_pos ht]

/-- Single-mode charge-`c` contraction in the `(m:ℤ)+1` index form. -/
theorem alphaC_succ_comp_EminusC (c : ℂ) (m : ℕ) (b : ℤ) :
    (α ((m : ℤ) + 1)).comp (EminusC c b)
      = (EminusC c b).comp (α ((m : ℤ) + 1))
        + (2 * c) • EminusC c (b - ((m : ℤ) + 1)) := by
  have hα : α ((m : ℤ) + 1) = α ((m + 1 : ℕ) : ℤ) := by norm_cast
  rw [hα]
  by_cases hb : 0 ≤ b
  · rw [EminusC_nonneg c hb, alpha_comp_EminusOpC c (m + 1) b.toNat (by omega)]
    congr 1
    by_cases hmN : m + 1 ≤ b.toNat
    · rw [if_pos hmN, EminusC_nonneg c (show (0 : ℤ) ≤ b - ((m : ℤ) + 1) by omega),
        show b.toNat - (m + 1) = (b - ((m : ℤ) + 1)).toNat from by omega]
    · rw [if_neg hmN, EminusC_neg c (show b - ((m : ℤ) + 1) < 0 by omega), smul_zero]
  · rw [EminusC_neg c (by omega), EminusC_neg c (show b - ((m : ℤ) + 1) < 0 by omega)]
    simp [α, EminusC, EminusOpC]

/-- Move `-α_{m+1}` past a left `EminusC c b` inside a composition (the charge-`c` contraction). -/
theorem move_alphaC_past_EminusC (c : ℂ) (m : ℕ) (b : ℤ) (X : Module.End ℂ B) :
    (-(α ((m : ℤ) + 1))).comp ((EminusC c b).comp X)
      = (EminusC c b).comp ((-(α ((m : ℤ) + 1))).comp X)
        - (2 * c) • ((EminusC c (b - ((m : ℤ) + 1))).comp X) := by
  rw [← LinearMap.comp_assoc, LinearMap.neg_comp, alphaC_succ_comp_EminusC]
  simp only [LinearMap.neg_comp, LinearMap.add_comp, LinearMap.smul_comp, LinearMap.comp_assoc,
    LinearMap.comp_neg]
  abel

/-! ## §D  The charge-`(-1)` FLM exponential contraction (the main induction) -/

/-- **The charge-`(-1)` FLM contraction** (the `aExpCZ`/`EminusC` coefficient form): the
`z₁`-dominant reordering of `E⁺(-α,z₁)E⁻(-α,z₂)`.  Self-pairing `⟨-α,-α⟩ = 2`, so the three-term
`(1-z₂/z₁)²` shift.  Mirrors `LatExp.Eminus_contraction` with the charge-`(-1)` recursion factor
`(-1)` and contraction constant `2·(-1) = -2` (whose product `(-1)·(-2) = 2` reproduces the `⟨α,α⟩`
structure constant).  Axiom-clean, `pbw`-free. -/
theorem EminusCm1_contraction (N b : ℤ) :
    (aExpCZ (-1) N).comp (EminusC (-1) b)
      = (EminusC (-1) b).comp (aExpCZ (-1) N)
        - (2 : ℂ) • ((EminusC (-1) (b - 1)).comp (aExpCZ (-1) (N - 1)))
        + (EminusC (-1) (b - 2)).comp (aExpCZ (-1) (N - 2)) := by
  suffices H : ∀ n : ℕ, ∀ N b : ℤ, N.toNat ≤ n →
      (aExpCZ (-1) N).comp (EminusC (-1) b)
        = (EminusC (-1) b).comp (aExpCZ (-1) N)
          - (2 : ℂ) • ((EminusC (-1) (b - 1)).comp (aExpCZ (-1) (N - 1)))
          + (EminusC (-1) (b - 2)).comp (aExpCZ (-1) (N - 2)) by
    exact H N.toNat N b le_rfl
  intro n
  induction n with
  | zero =>
    intro N b hN
    by_cases h0 : N = 0
    · subst h0
      rw [aExpCZ_zero, aExpCZ_neg (-1) (by norm_num : (0:ℤ) - 1 < 0),
          aExpCZ_neg (-1) (by norm_num : (0:ℤ) - 2 < 0)]
      simp
    · rw [aExpCZ_neg (-1) (by omega : N < 0), aExpCZ_neg (-1) (by omega : N - 1 < 0),
          aExpCZ_neg (-1) (by omega : N - 2 < 0)]
      simp
  | succ n ih =>
    intro N b hN
    by_cases hsmall : N.toNat ≤ n
    · exact ih N b hsmall
    · have hN1 : 1 ≤ N := by omega
      have hNn : N.toNat = n + 1 := by omega
      have hNne : (N : ℂ) ≠ 0 := by
        simp only [ne_eq, Int.cast_eq_zero]; omega
      set f : ℕ → Module.End ℂ B :=
        fun k => -(2 * (-1 : ℂ)) • ((EminusC (-1) (b - 1 - (k : ℤ))).comp (aExpCZ (-1) (N - 1 - (k : ℤ)))) with hf
      have hfK : f N.toNat = 0 := by
        simp only [hf]
        rw [aExpCZ_neg (-1) (by omega : N - 1 - (N.toNat : ℤ) < 0), LinearMap.comp_zero, smul_zero]
      have hfK1 : f (N.toNat + 1) = 0 := by
        simp only [hf]
        push_cast
        rw [aExpCZ_neg (-1) (show N - 1 - ((N.toNat : ℤ) + 1) < 0 by omega),
          LinearMap.comp_zero, smul_zero]
      have hLHS : (aExpCZ (-1) N).comp (EminusC (-1) b)
          = (N : ℂ)⁻¹ • (-1 : ℂ) • ∑ m ∈ Finset.range N.toNat,
              (-(α ((m : ℤ) + 1))).comp ((aExpCZ (-1) (N - 1 - m)).comp (EminusC (-1) b)) := by
        rw [aExpCZ_recursion (-1) N hN1, LinearMap.smul_comp, LinearMap.smul_comp, sum_comp']
        simp only [LinearMap.comp_assoc]
      have hterm : ∀ m ∈ Finset.range N.toNat,
          (-(α ((m : ℤ) + 1))).comp ((aExpCZ (-1) (N - 1 - m)).comp (EminusC (-1) b))
            = ( (EminusC (-1) b).comp ((-(α ((m : ℤ) + 1))).comp (aExpCZ (-1) (N - 1 - m)))
                - (2 : ℂ) • ((EminusC (-1) (b - 1)).comp ((-(α ((m : ℤ) + 1))).comp (aExpCZ (-1) (N - 1 - 1 - m))))
                + (EminusC (-1) (b - 2)).comp ((-(α ((m : ℤ) + 1))).comp (aExpCZ (-1) (N - 2 - 1 - m))) )
              + (f m - (2 : ℂ) • f (m + 1) + f (m + 2)) := by
        intro m _
        rw [ih (N - 1 - m) b (by omega), LinearMap.comp_add, LinearMap.comp_sub,
          LinearMap.comp_smul, move_alphaC_past_EminusC, move_alphaC_past_EminusC,
          move_alphaC_past_EminusC]
        simp only [hf]
        push_cast
        ring_nf
        module
      have hCol : ∀ (e : Module.End ℂ B) (L : ℤ), L.toNat ≤ N.toNat →
          (∑ m ∈ Finset.range N.toNat, e.comp ((-(α ((m : ℤ) + 1))).comp (aExpCZ (-1) (L - 1 - (m : ℤ)))))
            = e.comp ((-1 : ℂ) • ((L : ℂ) • aExpCZ (-1) L)) := by
        intro e L hL
        rw [← comp_sum']
        congr 1
        rw [← aExpCZ_sum_reassembly (-1) L N.toNat hL, smul_smul]
        norm_num
      have hGS : (∑ m ∈ Finset.range N.toNat,
            ( (EminusC (-1) b).comp ((-(α ((m : ℤ) + 1))).comp (aExpCZ (-1) (N - 1 - m)))
              - (2 : ℂ) • ((EminusC (-1) (b - 1)).comp ((-(α ((m : ℤ) + 1))).comp (aExpCZ (-1) (N - 1 - 1 - m))))
              + (EminusC (-1) (b - 2)).comp ((-(α ((m : ℤ) + 1))).comp (aExpCZ (-1) (N - 2 - 1 - m))) ))
          = (EminusC (-1) b).comp ((-1 : ℂ) • ((N : ℂ) • aExpCZ (-1) N))
            - (2 : ℂ) • ((EminusC (-1) (b - 1)).comp ((-1 : ℂ) • (((N - 1 : ℤ) : ℂ) • aExpCZ (-1) (N - 1))))
            + (EminusC (-1) (b - 2)).comp ((-1 : ℂ) • (((N - 2 : ℤ) : ℂ) • aExpCZ (-1) (N - 2))) := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.smul_sum,
          hCol (EminusC (-1) b) N le_rfl, hCol (EminusC (-1) (b - 1)) (N - 1) (by omega),
          hCol (EminusC (-1) (b - 2)) (N - 2) (by omega)]
      rw [hLHS, inv_smul_eq_iff₀ hNne, Finset.sum_congr rfl hterm, Finset.sum_add_distrib,
        sdiff_telescope f N.toNat, hfK, hfK1, hGS]
      simp only [hf, LinearMap.comp_smul]
      push_cast
      ring_nf
      module

/-- **The charge-`(-1)` FLM contraction** in `E⁺(-α)`/`E⁻(-α)` coefficient form. -/
theorem EplusCm1_comp_EminusCm1 (a b : ℤ) :
    (EplusC (-1) a).comp (EminusC (-1) b)
      = (EminusC (-1) b).comp (EplusC (-1) a)
        - (2 : ℂ) • ((EminusC (-1) (b - 1)).comp (EplusC (-1) (a + 1)))
        + (EminusC (-1) (b - 2)).comp (EplusC (-1) (a + 2)) := by
  rw [EplusC_eq_aExpCZ (-1) a, EplusC_eq_aExpCZ (-1) (a + 1), EplusC_eq_aExpCZ (-1) (a + 2),
    show (-(a + 1) : ℤ) = -a - 1 from by ring, show (-(a + 2) : ℤ) = -a - 2 from by ring]
  exact EminusCm1_contraction (-a) b

/-! ## §E  Self-commutativity of `E⁺(cα)` and the convolution form of `EEC` -/

/-- `E⁺(cα)`'s building block `aExpC c N` commutes with every positive boson mode `α(j+1)`. -/
theorem aExpC_commute_alpha (c : ℂ) (N j : ℕ) : Commute (aExpC c N) (α ((j : ℤ) + 1)) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    match N with
    | 0 => rw [aExpC_zero]; exact Commute.one_left _
    | (M + 1) =>
      rw [aExpC_succ]
      refine Commute.smul_left (Commute.smul_left ?_ _) _
      refine Commute.sum_left _ _ _ (fun m hm => ?_)
      refine Commute.mul_left ?_ (ih (M - m) (by simp only [Finset.mem_range] at hm; omega))
      exact (alpha_commute (by omega) (by omega)).neg_left

/-- The charge-`c` annihilation halves commute: `aExpC c M ∘ aExpC c N = aExpC c N ∘ aExpC c M`. -/
theorem aExpC_commute (c : ℂ) (M N : ℕ) : Commute (aExpC c M) (aExpC c N) := by
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

/-- The charge-`c` annihilation halves commute: `E⁺(cα)_a ∘ E⁺(cα)_b = E⁺(cα)_b ∘ E⁺(cα)_a`. -/
theorem EplusC_comm (c : ℂ) (a b : ℤ) :
    (EplusC c a).comp (EplusC c b) = (EplusC c b).comp (EplusC c a) := by
  rw [EplusC_eq_aExpCZ, EplusC_eq_aExpCZ]
  by_cases ha : 0 ≤ -a
  · by_cases hb : 0 ≤ -b
    · rw [aExpCZ_nonneg c ha, aExpCZ_nonneg c hb]; exact aExpC_commute c _ _
    · rw [aExpCZ_neg c (show -b < 0 by omega)]; simp
  · rw [aExpCZ_neg c (show -a < 0 by omega)]; simp

/-- `EEC c` is the **honest convolution** `E⁻(cα)·E⁺(cα)`: `EEC c s x = ∑ᶠ_m E⁻(cα)_m E⁺(cα)_{s-m} x`. -/
theorem EEC_apply_conv (c : ℂ) (s : ℤ) (x : B) :
    EEC c s x = ∑ᶠ m : ℤ, EminusC c m (EplusC c (s - m) x) := by
  rw [EEC, nprod_apply]
  refine finsum_congr fun m => ?_
  rw [normalOrdered_apply]
  by_cases hm : 0 ≤ m
  · rw [if_pos hm, Module.End.mul_apply]
  · rw [if_neg hm, Module.End.mul_apply, EminusC_neg c (show m < 0 by omega)]; simp

end LatExp
end VOA
