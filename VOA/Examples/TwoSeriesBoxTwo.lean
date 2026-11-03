/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.TwoSeriesBoxSpan

/-!
# `BoxCount 2 r` for every `r`

For `n = 2` the reduction `boxW_le_span_small` spans the box image (`k = r - N` jets among
`T_0, …, T_{N-1}`) by the reversed monomials `Π_i T_{N-1-γ_i}` with all `γ_i ≤ N - k`.  Sorting
`γ` and placing ones at the positions `γ_i + i` turns such a `γ` into a binary word with `k` ones,
whose socle degree is the weight of the monomial:

* `wordS S` — the binary word with ones on `S ⊆ Fin N`; `invS S`, `coinvS S` — the pairs
  (one, zero) in increasing and decreasing order, with `invS S + coinvS S = |S| (N - |S|)`;
* `exists_finset_of_box` — for `γ_i ≤ N - k` there is `S` with `|S| = k`,
  `Π_i T_{N-1-γ_i} = Π_{a ∈ S} T_{N-1-#{b < a, b ∉ S}}` and `coinvS S = Σ γ_i`;
* `socleDegree_wordS` — the socle degree of `wordS S` is `N + |S|² + |S| + invS S`;
* `boxCount_two` — **`BoxCount 2 r` is proved for every `r`**;
* `twoSeries_gradedUnitary_of_strictModel_box_two` — the `n = 2` endpoint (`M(2,7)`), with
  the counting half discharged: conditional only on `hA`, detection and `BoxInclusion 2 r`.

Everything is proved outright.
-/

namespace VOA.TwoSeries.StrictModel

open MvPolynomial VOA.SocleEval
open VOA.GradedUnitaryCohomology VirGradedUnitarity Sl2CosetConcrete

noncomputable section

/-! ### Binary words from sets -/

/-- The binary word with ones exactly on `S`. -/
def wordS {N : ℕ} (S : Finset (Fin N)) : Fin N → Fin 2 := fun a => if a ∈ S then 1 else 0

theorem wordS_eq_one {N : ℕ} (S : Finset (Fin N)) (a : Fin N) : wordS S a = 1 ↔ a ∈ S := by
  unfold wordS; split_ifs with h <;> simp [h]

theorem wordS_eq_zero {N : ℕ} (S : Finset (Fin N)) (a : Fin N) : wordS S a = 0 ↔ a ∉ S := by
  unfold wordS; split_ifs with h <;> simp [h]

theorem sum_wordS {N : ℕ} (S : Finset (Fin N)) :
    ∑ j, (((wordS S j : Fin 2) : ℕ) + 1) = N + S.card := by
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    mul_one, add_comm]
  congr 1
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ S)]
  have h1 : ∑ x ∈ Finset.univ.filter (· ∈ S), ((wordS S x : Fin 2) : ℕ) = S.card := by
    have : ∀ x ∈ Finset.univ.filter (· ∈ S), ((wordS S x : Fin 2) : ℕ) = 1 := by
      intro x hx
      rw [Finset.mem_filter] at hx
      rw [(wordS_eq_one S x).mpr hx.2]
      rfl
    rw [Finset.sum_congr rfl this, Finset.sum_const, smul_eq_mul, mul_one,
      Finset.filter_mem_eq_inter, Finset.univ_inter]
  have h2 : ∑ x ∈ Finset.univ.filter (· ∉ S), ((wordS S x : Fin 2) : ℕ) = 0 := by
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [Finset.mem_filter] at hx
    rw [(wordS_eq_zero S x).mpr hx.2]
    rfl
  rw [h1, h2, add_zero]

/-- Pairs (one, zero) in increasing order. -/
def invS {N : ℕ} (S : Finset (Fin N)) : ℕ :=
  (Finset.univ.filter fun p : Fin N × Fin N => p.1 < p.2 ∧ p.1 ∈ S ∧ p.2 ∉ S).card

/-- Pairs (one, zero) in decreasing order. -/
def coinvS {N : ℕ} (S : Finset (Fin N)) : ℕ :=
  (Finset.univ.filter fun p : Fin N × Fin N => p.2 < p.1 ∧ p.1 ∈ S ∧ p.2 ∉ S).card

theorem invS_add_coinvS {N : ℕ} (S : Finset (Fin N)) :
    invS S + coinvS S = S.card * (N - S.card) := by
  classical
  have hprod : (S ×ˢ Sᶜ).card = S.card * (N - S.card) := by
    rw [Finset.card_product, Finset.card_compl, Fintype.card_fin]
  rw [← hprod, invS, coinvS, ← Finset.card_union_of_disjoint]
  · congr 1
    ext ⟨a, b⟩
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_product, Finset.mem_compl]
    constructor
    · rintro (⟨-, ha, hb⟩ | ⟨-, ha, hb⟩) <;> exact ⟨ha, hb⟩
    · rintro ⟨ha, hb⟩
      have hne : a ≠ b := fun h => hb (h ▸ ha)
      rcases lt_or_gt_of_ne hne with h | h
      · exact Or.inl ⟨h, ha, hb⟩
      · exact Or.inr ⟨h, ha, hb⟩
  · rw [Finset.disjoint_left]
    rintro ⟨a, b⟩ h1 h2
    simp only [Finset.mem_filter] at h1 h2
    exact lt_asymm h1.2.1 h2.2.1

theorem coinvS_eq_sum {N : ℕ} (S : Finset (Fin N)) :
    coinvS S = ∑ a ∈ S, (Finset.univ.filter fun b => b < a ∧ b ∉ S).card := by
  classical
  rw [coinvS, Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_prod_type,
    ← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ S)]
  have h2 : ∑ x ∈ Finset.univ.filter (· ∉ S), ∑ y : Fin N,
      (if y < x ∧ x ∈ S ∧ y ∉ S then 1 else 0) = 0 :=
    Finset.sum_eq_zero fun x hx => Finset.sum_eq_zero fun y _ => by
      rw [Finset.mem_filter] at hx; rw [if_neg (fun h => hx.2 h.2.1)]
  rw [h2, add_zero, Finset.filter_mem_eq_inter, Finset.univ_inter]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [ha, true_and]

/-! ### The socle degree of a binary word -/

theorem clusterAtLeast_wordS {N : ℕ} (S : Finset (Fin N)) :
    clusterAtLeast (wordS S) 1 = S.card := by
  unfold clusterAtLeast
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    by_contra ha
    rw [(wordS_eq_zero S a).mpr ha] at h
    exact absurd h (by decide)
  · intro ha
    rw [(wordS_eq_one S a).mpr ha]
    decide

theorem inversions_wordS {N : ℕ} (S : Finset (Fin N)) : inversions (wordS S) = invS S := by
  unfold inversions invS
  congr 1
  ext ⟨a, b⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  refine and_congr_right fun _ => ?_
  constructor
  · intro h
    have ha : wordS S a = 1 := by
      rcases Fin.exists_fin_two.mp ⟨wordS S a, rfl⟩ with h' | h'
      · rw [h'] at h; exact absurd h (Fin.not_lt_zero _)
      · exact h'
    have hb : wordS S b = 0 := by
      rcases Fin.exists_fin_two.mp ⟨wordS S b, rfl⟩ with h' | h'
      · exact h'
      · rw [h', ha] at h; exact absurd h (lt_irrefl _)
    exact ⟨(wordS_eq_one S a).mp ha, (wordS_eq_zero S b).mp hb⟩
  · rintro ⟨ha, hb⟩
    rw [(wordS_eq_one S a).mpr ha, (wordS_eq_zero S b).mpr hb]
    decide

/-- **The socle degree of a binary word**: `N + |S|² + |S| + invS S`. -/
theorem socleDegree_wordS {N : ℕ} (S : Finset (Fin N)) :
    socleDegree (wordS S) = N + (S.card ^ 2 + S.card) + invS S := by
  unfold socleDegree
  rw [inversions_wordS]
  congr 2
  rw [show Finset.Ico 1 2 = {1} by rfl, Finset.sum_singleton, clusterAtLeast_wordS]

/-! ### From a box exponent to a set -/

theorem card_filter_lt_mem_image {N k : ℕ} (p : Fin k → Fin N) (hp : StrictMono p) (i : Fin k) :
    (Finset.univ.filter fun b => b < p i ∧ b ∈ Finset.univ.image p).card = i := by
  classical
  have h : (Finset.univ.filter fun b => b < p i ∧ b ∈ Finset.univ.image p) =
      (Finset.Iio i).image p := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_Iio]
    constructor
    · rintro ⟨hb, j, rfl⟩
      exact ⟨j, hp.lt_iff_lt.mp hb, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨hp hj, j, rfl⟩
  rw [h, Finset.card_image_of_injective _ hp.injective, Fin.card_Iio]

theorem card_filter_lt_not_mem_image {N k : ℕ} (p : Fin k → Fin N) (hp : StrictMono p)
    (i : Fin k) :
    (Finset.univ.filter fun b => b < p i ∧ b ∉ Finset.univ.image p).card = (p i : ℕ) - i := by
  classical
  have htot := Finset.card_filter_add_card_filter_not (s := Finset.univ.filter (· < p i))
    (fun b => b ∈ Finset.univ.image p)
  rw [Finset.filter_filter, Finset.filter_filter] at htot
  have hIio : (Finset.univ.filter (· < p i)).card = p i := by
    rw [show (Finset.univ.filter (· < p i)) = Finset.Iio (p i) by ext; simp, Fin.card_Iio]
  rw [hIio, card_filter_lt_mem_image p hp i] at htot
  omega

/-- **From a box exponent to a set**: sorting `γ` and placing ones at `γ_i + i`. -/
theorem exists_finset_of_box (n : ℕ) {N k : ℕ} (γ : Fin k →₀ ℕ) (hγ : ∀ i, γ i + k ≤ N) :
    ∃ S : Finset (Fin N), S.card = k ∧
      ∏ i, tn n (N - 1 - γ i) =
        ∏ a ∈ S, tn n (N - 1 - (Finset.univ.filter fun b => b < a ∧ b ∉ S).card) ∧
      coinvS S = ∑ i, γ i := by
  classical
  set σ := Tuple.sort (fun i => γ i) with hσ
  have hg : Monotone fun i => γ (σ i) := Tuple.monotone_sort _
  let p : Fin k → Fin N := fun i => ⟨γ (σ i) + i, by have := hγ (σ i); have := i.2; omega⟩
  have hp : StrictMono p := by
    intro i j hij
    have h1 : γ (σ i) ≤ γ (σ j) := hg hij.le
    simp only [p, Fin.mk_lt_mk]
    have : (i : ℕ) < j := hij
    omega
  set S := Finset.univ.image p with hS
  have hcount : ∀ i, (Finset.univ.filter fun b => b < p i ∧ b ∉ S).card = γ (σ i) := by
    intro i
    rw [hS, card_filter_lt_not_mem_image p hp i]
    simp only [p]
    omega
  refine ⟨S, ?_, ?_, ?_⟩
  · rw [hS, Finset.card_image_of_injective _ hp.injective, Finset.card_univ, Fintype.card_fin]
  · rw [hS, Finset.prod_image (hp.injective.injOn), ← hS]
    simp_rw [hcount]
    exact (Fintype.prod_equiv σ _ _ fun _ => rfl).symm
  · rw [coinvS_eq_sum, hS, Finset.sum_image (hp.injective.injOn), ← hS]
    simp_rw [hcount]
    exact Fintype.sum_equiv σ _ _ fun _ => rfl

/-! ### The word monomials and the count -/

/-- The monomial of a binary word: `Π_{a : x_a = 1} T_{N₁ - 1 - #{b < a : x_b = 0}}`. -/
def wordMonoF {N₁ : ℕ} (x : Fin N₁ → Fin 2) : Rn 2 :=
  ∏ a, if x a = 1 then tn 2 (N₁ - 1 - (Finset.univ.filter fun b => b < a ∧ x b = 0).card) else 1

theorem wordMonoF_wordS {N : ℕ} (S : Finset (Fin N)) :
    wordMonoF (wordS S) =
      ∏ a ∈ S, tn 2 (N - 1 - (Finset.univ.filter fun b => b < a ∧ b ∉ S).card) := by
  classical
  rw [wordMonoF, ← Finset.prod_filter]
  have h1 : (Finset.univ.filter fun a => wordS S a = 1) = S := by
    ext a; simp [wordS_eq_one]
  rw [h1]
  refine Finset.prod_congr rfl fun a _ => ?_
  congr 3
  ext b
  simp [wordS_eq_zero]

/-- **`BoxCount 2 r` holds for every `r`.** -/
theorem boxCount_two (r : ℕ) : BoxCount 2 r := by
  classical
  intro d N hN
  set k := r - N with hk
  have hk1 : 1 ≤ k := by omega
  have hr : r = N + k := by omega
  let ι := {i : SocleIndex 2 r // ((socleDegree i.2.1 : ℕ) : ℤ) = d ∧ (i.1 : ℕ) = N}
  let F : ι → Rn 2 := fun i => wordMonoF i.1.2.1
  have hsub : psiMono 2 N '' {γ : Fin k →₀ ℕ | (∀ i, γ i < (2 - 1) * N + 1 - k) ∧
      ((Finsupp.degree γ : ℕ) : ℤ) + (d - (r : ℕ)) = k * N} ⊆ Set.range F := by
    rintro _ ⟨γ, ⟨hγ, hdeg⟩, rfl⟩
    have hγ' : ∀ i, γ i + k ≤ N := fun i => by have := hγ i; omega
    have hkN : k ≤ N := by have := hγ' ⟨0, by omega⟩; omega
    obtain ⟨S, hSk, hprod, hco⟩ := exists_finset_of_box 2 γ hγ'
    have hinv := invS_add_coinvS S
    rw [hSk, hco] at hinv
    rw [degree_eq_sum] at hdeg
    have hsum : ∑ j, (((wordS S j : Fin 2) : ℕ) + 1) = r := by rw [sum_wordS, hSk, hr]
    have hdeg' : ((socleDegree (wordS S) : ℕ) : ℤ) = d := by
      rw [socleDegree_wordS, hSk]
      have h4 : k * (N - k) + k * k = k * N := by
        rw [← Nat.mul_add, Nat.sub_add_cancel hkN]
      push_cast
      have hinvZ : ((invS S : ℕ) : ℤ) + ((∑ i, γ i : ℕ) : ℤ) = ((k * (N - k) : ℕ) : ℤ) := by
        exact_mod_cast hinv
      have h4Z : ((k * (N - k) : ℕ) : ℤ) + (k : ℤ) * k = (k : ℤ) * N := by exact_mod_cast h4
      have hrZ : (r : ℤ) = N + k := by exact_mod_cast hr
      nlinarith
    refine ⟨⟨⟨⟨N, by omega⟩, ⟨wordS S, hsum⟩⟩, hdeg', rfl⟩, ?_⟩
    change wordMonoF (wordS S) = psiMono 2 N γ
    rw [wordMonoF_wordS, ← hprod, psiMono]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [if_pos (by have := hγ' i; omega)]
  have hle : boxW (tn 2) N (r - N) (d - (r : ℕ)) ≤ Submodule.span ℂ (Set.range F) :=
    (boxW_le_span_small 2 N k (d - (r : ℕ))).trans (Submodule.span_mono hsub)
  refine (Submodule.rank_mono hle).trans ((rank_span_le _).trans
    (Cardinal.mk_range_le.trans (le_of_eq ?_)))
  exact (Nat.cast_card (α := ι)).symm

/-- **Affine GU ⇒ GU of `M(2, 7)` (`n = 2`)**, `#print axioms`-clean, conditional on `hA`,
detection `det` and the structural half `BoxInclusion 2 r`; the counting half is proved
(`boxCount_two`). -/
theorem twoSeries_gradedUnitary_of_strictModel_box_two
    (hA : GradedUnitary (affineForm (twoSeriesLevels 2))
      (affineRealStructure (twoSeriesLevels 2)) (affineFlag (twoSeriesLevels 2)))
    (det : TwoSeriesModelDetects 2) (incl : ∀ r, BoxInclusion 2 r) :
    VirGradedUnitary (twoSeriesLevels 2).c (targetRealStructure (twoSeriesLevels 2)) :=
  twoSeries_gradedUnitary_of_strictModel_box 2 (by norm_num) hA det incl boxCount_two

end

end VOA.TwoSeries.StrictModel
