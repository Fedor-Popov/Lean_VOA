/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.TwoSeriesCharacterAGEval
import VOA.Examples.TwoSeriesCharacterAGCombinatorics
import VOA.Examples.TwoSeriesCharacterGramRank
import VOA.Examples.TwoSeriesCharacterEndpoint

/-!
# The Andrews–Gordon identity, and the vacuum character of `M(2, 2n+3)`

* `GG n i` — the Gordon generating series `Σ gC n i m N x^m q^N`; it satisfies Andrews'
  recursion `G_{a+1} = G_a + x^a q^a G_{n+1-a}(xq)` (`GG_rec`, from `gC_succ`).
* `HH n i = FF · A_i` satisfies the same recursion (`HH_rec`, from `AA_functional` and
  `FF_functional`) with the same boundary values; the recursion has a unique solution
  (`GG_eq_HH`, induction on the `q`-degree).
* `gordon_sum_eq_rcq` — **the Andrews–Gordon identity**, coefficientwise:
  `#{partitions of N into parts ≥ 2 with f_m + f_{m+1} ≤ n} = Σ_k (-1)^k p(N - k((2n+3)k+2n+1)/2)`.
* `gordonLowerBound_twoSeries` — `GordonLowerBound c_{2,2n+3} n`, **proved** for every `n`
  (Andrews–Gordon + the proved Feigin–Fuchs rank bound `KacGram.rcq_le_finrank`).
* `twoSeries_character` — `dim L(c_{2,2n+3})_N = Σ_r gordonCoeff n N r = rcq n N`.
* `twoSeries_hpbw` — the refined PBW character input `hpbw`, proved.

Everything is proved outright.  The coset-transfer consequence
`twoSeries_gradedUnitary_of_affine_invariants_gordon_final` (Affine GU ⇒ GU of `M(2,2n+3)`,
conditional on `hA` and `hinv`) is in `TwoSeriesCharacterGU.lean`, so that this
file does not import the graded-unitarity files.
-/

namespace VOA.TwoSeriesCharacter.AG

open PowerSeries
open scoped BigOperators

noncomputable section

variable (n : ℕ)

/-! ## §1  The Gordon series and its recursion -/

/-- The Gordon series `Σ gC n i m N x^m q^N`. -/
def GG (i : ℕ) : PowerSeries R :=
  PowerSeries.mk fun m => PowerSeries.mk fun N => ((gC n i m N : ℕ) : ℚ)

theorem coeff_GG (i m N : ℕ) : coeff N (coeff m (GG n i)) = ((gC n i m N : ℕ) : ℚ) := by
  rw [GG, PowerSeries.coeff_mk, PowerSeries.coeff_mk]

/-- The coefficients of `x^a q^a G(xq)`. -/
theorem coeff_shift (a m N : ℕ) (G : PowerSeries R) :
    coeff N (coeff m (xx ^ a * CC (qq ^ a) * resc G)) =
      if a ≤ m ∧ m ≤ N then coeff (N - m) (coeff (m - a) G) else 0 := by
  rw [mul_assoc, xx, coeff_X_pow_mul']
  by_cases ham : a ≤ m
  · rw [if_pos ham, CC, coeff_C_mul, coeff_resc, ← mul_assoc, ← pow_add,
      show a + (m - a) = m by omega, coeff_qq_pow_mul]
    by_cases hmN : m ≤ N
    · rw [if_pos hmN, if_pos ⟨ham, hmN⟩]
    · rw [if_neg hmN, if_neg (fun h => hmN h.2)]
  · rw [if_neg ham, if_neg (fun h => ham h.1), map_zero]

theorem GG_rec (a : ℕ) (ha : a ≤ n) :
    GG n (a + 1) = GG n a + xx ^ a * CC (qq ^ a) * resc (GG n (n + 1 - a)) := by
  refine PowerSeries.ext fun m => PowerSeries.ext fun N => ?_
  rw [map_add, map_add, coeff_shift, coeff_GG, coeff_GG, gC_succ n a m N ha]
  split_ifs with h
  · rw [coeff_GG]; push_cast; ring
  · simp

theorem GG_zero : GG n 0 = 0 := by
  refine PowerSeries.ext fun m => PowerSeries.ext fun N => ?_
  rw [coeff_GG, gC_zero]; simp

theorem constantCoeff_GG (i : ℕ) (hi : 1 ≤ i) : constantCoeff (GG n i) = 1 := by
  refine PowerSeries.ext fun N => ?_
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_GG, gC_zero_length n i N hi, coeff_one]
  split_ifs <;> simp

/-! ## §2  `FF · A_i` satisfies the same recursion -/

/-- `FF · A_i`. -/
def HH (i : ℕ) : PowerSeries R := FF * AA (n + 1) i

theorem HH_rec (a : ℕ) (ha : a ≤ n) :
    HH n (a + 1) = HH n a + xx ^ a * CC (qq ^ a) * resc (HH n (n + 1 - a)) := by
  have hf := AA_functional (n + 1) a (n - a) (by omega)
  rw [show n - a + 1 = n + 1 - a by omega] at hf
  have hA : AA (n + 1) (a + 1) = AA (n + 1) a +
      xx ^ a * CC (qq ^ a) * (1 - CC qq * xx) * resc (AA (n + 1) (n + 1 - a)) := by
    rw [← hf]; ring
  unfold HH
  rw [hA, map_mul, ← FF_functional]
  ring

theorem HH_zero : HH n 0 = 0 := by
  rw [HH, AA_zero, mul_zero]

theorem constantCoeff_HH (i : ℕ) (hi : 1 ≤ i) : constantCoeff (HH n i) = 1 := by
  rw [HH, map_mul, constantCoeff_FF, constantCoeff_AA _ i hi, one_mul]

/-! ## §3  Uniqueness -/

theorem GG_eq_HH : ∀ i ≤ n + 1, GG n i = HH n i := by
  set D : ℕ → PowerSeries R := fun i => GG n i - HH n i with hD
  have hrec : ∀ a ≤ n, D (a + 1) = D a + xx ^ a * CC (qq ^ a) * resc (D (n + 1 - a)) := by
    intro a ha
    simp only [hD]
    rw [GG_rec n a ha, HH_rec n a ha, map_sub]
    ring
  have h0 : D 0 = 0 := by simp only [hD]; rw [GG_zero, HH_zero, sub_zero]
  have hc : ∀ i, 1 ≤ i → constantCoeff (D i) = 0 := by
    intro i hi
    simp only [hD]
    rw [map_sub, constantCoeff_GG n i hi, constantCoeff_HH n i hi, sub_self]
  have key : ∀ N i, i ≤ n + 1 → ∀ m, coeff N (coeff m (D i)) = 0 := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ihN =>
    intro i
    induction i with
    | zero => intro _ m; rw [h0]; simp
    | succ a iha =>
      intro hi m
      rcases Nat.eq_zero_or_pos m with hm | hm
      · subst hm
        rw [coeff_zero_eq_constantCoeff_apply, hc (a + 1) (by omega), map_zero]
      · rw [hrec a (by omega), map_add, map_add, iha (by omega) m, zero_add, coeff_shift]
        split_ifs with h
        · exact ihN (N - m) (by omega) (n + 1 - a) (by omega) (m - a)
        · rfl
  intro i hi
  have : D i = 0 :=
    PowerSeries.ext fun m => PowerSeries.ext fun N => by rw [key N i hi m]; simp
  exact sub_eq_zero.mp (by simpa only [hD] using this)

/-! ## §4  The Andrews–Gordon identity -/

theorem two_mul_tri : ∀ s, 2 * tri s = s * (s + 1)
  | 0 => rfl
  | s + 1 => by rw [tri, mul_add, mul_add, two_mul_tri s]; ring

/-- The exponent `E_s = (n+1)s² + ns + s(s+1)/2 = eeq n s`. -/
theorem exponent_eq (s : ℕ) :
    (((n + 1) * s * s + (n + 1 - 1) * s + tri s : ℕ) : ℤ) = KacGram.eeq n s := by
  symm
  apply KacGram.eeq_param
  have h := two_mul_tri s
  rw [show n + 1 - 1 = n by omega]
  have h' : (2 * (tri s : ℤ)) = (s : ℤ) * ((s : ℤ) + 1) := by exact_mod_cast h
  push_cast
  linear_combination h'

theorem exponent_eq' (s : ℕ) :
    (((n + 1) * s * s + (n + 1 - 1) * s + tri s : ℕ) : ℤ) + 2 * s + 1 =
      KacGram.eeq n (-(s : ℤ) - 1) := by
  symm
  apply KacGram.eeq_param
  have h := two_mul_tri s
  rw [show n + 1 - 1 = n by omega]
  have h' : (2 * (tri s : ℤ)) = (s : ℤ) * ((s : ℤ) + 1) := by exact_mod_cast h
  push_cast
  linear_combination h'

theorem neg_one_pow_R (s : ℕ) : ((-1 : R) ^ s) = PowerSeries.C ((-1 : ℚ) ^ s) := by
  rw [map_pow, map_neg, map_one]

/-- The coefficient of one term of `A_1(1)`. -/
theorem coeff_term_one (E s N2 : ℕ) :
    coeff N2 ((-1 : R) ^ s * qq ^ E * (1 - qq ^ ((2 * s + 1) * 1))) =
      (-1 : ℚ) ^ s * ((if N2 = E then 1 else 0) - (if N2 = E + (2 * s + 1) then 1 else 0)) := by
  rw [mul_assoc, neg_one_pow_R, coeff_C_mul, mul_sub, mul_one, ← pow_add, map_sub, qq,
    coeff_X_pow, coeff_X_pow, mul_one]

theorem sum_antidiagonal_indicator (f : ℕ → ℚ) (N e : ℕ) :
    ∑ u ∈ Finset.antidiagonal N, f u.1 * (if u.2 = e then 1 else 0) =
      if e ≤ N then f (N - e) else 0 := by
  simp only [mul_ite, mul_one, mul_zero]
  split_ifs with he
  · rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
    have : (Finset.antidiagonal N).filter (fun u : ℕ × ℕ => u.2 = e) = {(N - e, e)} := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_antidiagonal, Finset.mem_singleton]
      constructor
      · rintro ⟨h1, h2⟩; ext <;> simp <;> omega
      · rintro rfl; simp; omega
    rw [this, Finset.sum_singleton]
  · refine Finset.sum_eq_zero fun u hu => ?_
    rw [if_neg]
    have := Finset.mem_antidiagonal.mp hu
    omega

theorem pp_cast_shift (N e : ℕ) :
    (if e ≤ N then ((VOA.RRLower.pp ((N - e : ℕ) : ℤ) : ℤ) : ℚ) else 0) =
      ((VOA.RRLower.pp ((N : ℤ) - (e : ℤ)) : ℤ) : ℚ) := by
  split_ifs with h
  · rw [Nat.cast_sub h]
  · rw [VOA.RRLower.pp_of_neg (by omega), Int.cast_zero]

theorem sgn_nat (s : ℕ) : VOA.RRLower.sgn (s : ℤ) = (-1) ^ s := by
  unfold VOA.RRLower.sgn
  rcases Nat.even_or_odd s with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · rw [if_pos (by push_cast; omega), show t + t = 2 * t by ring, pow_mul]; simp
  · rw [if_neg (by push_cast; omega), pow_succ, pow_mul]; simp

theorem sgn_neg (s : ℕ) : VOA.RRLower.sgn (-(s : ℤ) - 1) = -(-1) ^ s := by
  unfold VOA.RRLower.sgn
  rcases Nat.even_or_odd s with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · rw [if_neg (by push_cast; omega), show t + t = 2 * t by ring, pow_mul]; simp
  · rw [if_pos (by push_cast; omega), pow_succ, pow_mul]; simp

/-- `rcq` as a sum over `s ≤ N` of the pairs `k = s`, `k = -s-1`. -/
theorem rcq_eq_range (N : ℕ) :
    KacGram.rcq n N = ∑ s ∈ Finset.range (N + 1), (-1) ^ s *
      (VOA.RRLower.pp ((N : ℤ) - KacGram.eeq n s) -
        VOA.RRLower.pp ((N : ℤ) - KacGram.eeq n (-(s : ℤ) - 1))) := by
  unfold KacGram.rcq
  rw [← Finset.Ico_union_Ico_eq_Ico (b := 0) (by omega) (by omega),
    Finset.sum_union (Finset.Ico_disjoint_Ico_consecutive _ _ _)]
  have h1 : Finset.Ico (0 : ℤ) ((N : ℤ) + 1) = (Finset.range (N + 1)).map Nat.castEmbedding := by
    ext x
    simp only [Finset.mem_Ico, Finset.mem_map, Finset.mem_range, Nat.castEmbedding_apply]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨x.toNat, by omega, by omega⟩
    · rintro ⟨a, ha, rfl⟩; omega
  have h2 : Finset.Ico (-(N : ℤ) - 1) 0 = (Finset.range (N + 1)).map
      ⟨fun s : ℕ => -(s : ℤ) - 1, fun a b h => by simp only at h; omega⟩ := by
    ext x
    simp only [Finset.mem_Ico, Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨(-x - 1).toNat, by omega, by omega⟩
    · rintro ⟨a, ha, rfl⟩; omega
  rw [h1, h2, Finset.sum_map, Finset.sum_map, add_comm, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [Nat.castEmbedding_apply, Function.Embedding.coeFn_mk, sgn_nat, sgn_neg]
  ring

/-- **The Andrews–Gordon identity** (Rocha-Caridi form), coefficientwise. -/
theorem gordon_sum_eq_rcq (N : ℕ) :
    ((∑ r ∈ Finset.range (N + 1), gordonCoeff n (N : ℤ) r : ℕ) : ℤ) = KacGram.rcq n N := by
  have hK : 1 ≤ n + 1 := by omega
  -- the Gordon side as `ev (GG n 1)`
  have hG : ((∑ r ∈ Finset.range (N + 1), gordonCoeff n (N : ℤ) r : ℕ) : ℚ) =
      coeff N (ev (GG n 1)) := by
    rw [coeff_ev, SS, map_sum]
    simp only [coeff_GG, gordonCoeff_eq_gC]
    push_cast
    rfl
  have hE : ev (GG n 1) = ev FF * ev (AA (n + 1) 1) := by
    rw [GG_eq_HH n 1 (by omega), HH, ev_mul Adm_FF (Adm_AA _ 1)]
  rw [hE, coeff_mul] at hG
  -- expand `A_1(1)`
  have hA : ∀ u ∈ Finset.antidiagonal N, coeff u.1 (ev FF) * coeff u.2 (ev (AA (n + 1) 1)) =
      ∑ s ∈ Finset.range (N + 1), (-1 : ℚ) ^ s *
        (((VOA.RRLower.pp (u.1 : ℤ) : ℤ) : ℚ) *
            (if u.2 = (n + 1) * s * s + (n + 1 - 1) * s + tri s then 1 else 0) -
          ((VOA.RRLower.pp (u.1 : ℤ) : ℤ) : ℚ) *
            (if u.2 = (n + 1) * s * s + (n + 1 - 1) * s + tri s + (2 * s + 1) then 1 else 0)) := by
    intro u hu
    have hu' := Finset.mem_antidiagonal.mp hu
    rw [coeff_ev_FF, coeff_ev_AA _ hK 1 u.2]
    rw [Finset.mul_sum]
    -- extend the `s`-range from `u.2` to `N`
    have hext : ∀ s ∈ Finset.range (N + 1), s ∉ Finset.range (u.2 + 1) →
        ((VOA.RRLower.pp (u.1 : ℤ) : ℤ) : ℚ) * coeff u.2 ((-1 : R) ^ s *
          qq ^ ((n + 1) * s * s + (n + 1 - 1) * s + tri s) * (1 - qq ^ ((2 * s + 1) * 1))) = 0 := by
      intro s _ hs
      rw [Finset.mem_range] at hs
      rw [coeff_term_one]
      have h1 : u.2 ≠ (n + 1) * s * s + (n + 1 - 1) * s + tri s := by
        have : s ≤ (n + 1) * s * s := by
          calc s ≤ s * s := Nat.le_mul_self s
            _ ≤ (n + 1) * (s * s) := Nat.le_mul_of_pos_left _ (by omega)
            _ = (n + 1) * s * s := by ring
        omega
      rw [if_neg h1, if_neg (by omega)]
      ring
    rw [Finset.sum_subset (Finset.range_subset_range.mpr (by omega : u.2 + 1 ≤ N + 1)) hext]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [coeff_term_one]
    ring
  rw [Finset.sum_congr rfl hA, Finset.sum_comm] at hG
  have hS : ∀ s ∈ Finset.range (N + 1),
      ∑ u ∈ Finset.antidiagonal N, (-1 : ℚ) ^ s *
        (((VOA.RRLower.pp (u.1 : ℤ) : ℤ) : ℚ) *
            (if u.2 = (n + 1) * s * s + (n + 1 - 1) * s + tri s then 1 else 0) -
          ((VOA.RRLower.pp (u.1 : ℤ) : ℤ) : ℚ) *
            (if u.2 = (n + 1) * s * s + (n + 1 - 1) * s + tri s + (2 * s + 1) then 1 else 0)) =
      (((-1) ^ s * (VOA.RRLower.pp ((N : ℤ) - KacGram.eeq n s) -
        VOA.RRLower.pp ((N : ℤ) - KacGram.eeq n (-(s : ℤ) - 1))) : ℤ) : ℚ) := by
    intro s _
    rw [← Finset.mul_sum, Finset.sum_sub_distrib,
      sum_antidiagonal_indicator (fun k => ((VOA.RRLower.pp (k : ℤ) : ℤ) : ℚ)),
      sum_antidiagonal_indicator (fun k => ((VOA.RRLower.pp (k : ℤ) : ℤ) : ℚ)),
      pp_cast_shift, pp_cast_shift]
    push_cast
    have hE1 : ((n : ℤ) + 1) * s * s + n * s + (tri s : ℤ) = KacGram.eeq n s := by
      have := exponent_eq n s
      rw [show n + 1 - 1 = n by omega] at this
      push_cast at this
      exact this
    have hE2 : KacGram.eeq n s + (2 * s + 1) = KacGram.eeq n (-(s : ℤ) - 1) := by
      have := exponent_eq' n s
      rw [exponent_eq] at this
      linarith
    rw [hE1, hE2]
  rw [Finset.sum_congr rfl hS, ← Int.cast_sum, ← rcq_eq_range] at hG
  exact_mod_cast hG

end

end VOA.TwoSeriesCharacter.AG

namespace VOA.TwoSeries

open VirGradedUnitarity VirGoodFil
open scoped BigOperators

/-- **The total Andrews–Gordon lower bound for `M(2, 2n+3)`, proved for every `n`.** -/
theorem gordonLowerBound_twoSeries (n : ℕ) :
    VOA.TwoSeriesCharacter.GordonLowerBound (twoSeriesLevels n).c n := by
  intro N
  rw [twoSeriesLevels_c_eq_bsaCharge]
  have h1 := VOA.TwoSeriesCharacter.AG.gordon_sum_eq_rcq n N
  have h2 := VOA.TwoSeriesCharacter.KacGram.rcq_le_finrank n N
  rw [← h1] at h2
  exact_mod_cast h2

/-- **The vacuum character of `M(2, 2n+3)`**: `dim L(c_{2,2n+3})_N` equals the Andrews–Gordon
count and the Rocha-Caridi alternating sum. -/
theorem twoSeries_character (n N : ℕ) :
    Module.finrank ℂ ((VOA.VirSimple.virasoroSimple (twoSeriesLevels n).c).grading (N : ℤ)) =
      ∑ r ∈ Finset.range (N + 1), VOA.TwoSeriesCharacter.gordonCoeff n (N : ℤ) r ∧
    ((∑ r ∈ Finset.range (N + 1), VOA.TwoSeriesCharacter.gordonCoeff n (N : ℤ) r : ℕ) : ℤ) =
      VOA.TwoSeriesCharacter.KacGram.rcq n N :=
  ⟨le_antisymm
    (VOA.TwoSeriesCharacter.finrank_grading_le_gordon _ n (twoSeries_hasJetRelations_all n) N)
    (gordonLowerBound_twoSeries n N),
   VOA.TwoSeriesCharacter.AG.gordon_sum_eq_rcq n N⟩

/-- **The refined PBW character of `M(2, 2n+3)`** — exactly the `hpbw` input, proved. -/
theorem twoSeries_hpbw (n : ℕ) :
    ∀ (N : ℤ) (p : ℕ), ∑ r ∈ Finset.range (p + 1), VOA.TwoSeriesCharacter.gordonCoeff n N r ≤
      Module.finrank ℂ ((virGradedFlag (twoSeriesLevels n).c).pieceIn p N) :=
  twoSeries_hpbw_of_gordonLowerBound n (gordonLowerBound_twoSeries n)

end VOA.TwoSeries
