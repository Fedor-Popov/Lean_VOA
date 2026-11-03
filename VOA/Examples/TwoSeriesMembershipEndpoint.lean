/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.TwoSeriesMembershipTest

/-!
# The membership bound from a statement without model words

The remaining input `ModelSocleMembership n r` of the two-series endpoint concerns the
membership spaces `vMem` of the model `S_{n,r}`.  The two preceding files bound each membership
space, with proofs, by two spaces that do not mention the model words:

* `vMem_le_tMonW` — `T`-polynomials of degree `r - N` and weight `d - r`;
* `vMem_le_testSp` — the test space: `τ(J + x̃) · v₀^{2N}` lies in the span of products of `r`
  jets of `u², uv, v²`, modulo the jets of `(J + x̃)ⁿ`;

and the cases `N ≥ r` are proved outright (`modelSocleMembership_of_below`).  This file states the
remaining input in that reduced form and splits it in two:

* `TestBound n r` — **the remaining input, in plain words**: *for `N < r`, the `T`-polynomials
  of degree `r - N` and weight `d - r` in `R_n` passing the test form a space of dimension at
  most the number of socle words with `N` letters, size `r` and degree `d`*;
* `boxW t N k e` — the span of the products `t_{m₁} ⋯ t_{m_k}` of weight `e` with every
  `m_i < N` (only the jets `T_0, …, T_{N-1}` occur);
* `BoxInclusion n r` — *a `T`-polynomial passing the test lies in the span of the jets
  `T_0, …, T_{N-1}`* (structural);
* `BoxCount n r` — *the image in `R_n` of the polynomials in `T_0, …, T_{N-1}` of degree `r - N`
  and weight `d - r` has dimension at most the socle-word count* (a finitized
  Feigin–Stoyanovsky spanning statement in `R_n` alone);
* `modelSocleMembership_of_testBound`, `testBound_of_box`;
* `boxCount_single` — **`BoxCount` in `T`-degree one is proved** (`r = N + 1`, every `n ≥ 2`);
* `twoSeries_gradedUnitary_of_strictModel_testBound`,
  `twoSeries_gradedUnitary_of_strictModel_box` — the endpoints with the reduced inputs.

Numerical evidence (exact linear algebra mod `p = 1000003`, not a
proof): the dimension of the test space equals both the box dimension and the socle-word count in
every slot checked (`n = 2`: `r ≤ 6`, weight `≤ 9`; `n = 3`: `r ≤ 6`, weight `≤ 9`; `n = 4`:
`r ≤ 6`, weight `≤ 10`; 364 slots, 110 with nonzero count).  With the plain substitution `T ↦ J`
(no `x̃`) the test space is strictly larger at `T`-degree `≥ n` (`n = 2`), and with `T ↦ J + z̃`
it is also too large; with `x̃` or `ỹ` it is sharp (`n = 2`, `r ≤ 5`, weight `≤ 7`).

Everything is proved outright from the stated hypotheses.
-/

namespace VOA.TwoSeries.StrictModel

open MvPolynomial VOA.SymbolModel VOA.InvariantSymbol VOA.SocleEval
open VOA.AdamovicSymbol Module
open VOA.GradedUnitaryCohomology VirGradedUnitarity Sl2CosetConcrete

noncomputable section

/-- The socle-word count of the membership bound. -/
abbrev socleCount (n r : ℕ) (d : ℤ) (N : ℕ) : ℕ :=
  Nat.card {i : SocleIndex n r // ((socleDegree i.2.1 : ℕ) : ℤ) = d ∧ (i.1 : ℕ) = N}

/-- **The remaining input in reduced form**: for `N < r`, the `T`-polynomials of degree `r - N`
and weight `d - r` in `R_n` that pass the test form a space of dimension at most the socle-word
count. -/
def TestBound (n r : ℕ) : Prop :=
  ∀ (d : ℤ) (N : ℕ), N < r →
    Module.rank ℂ ↥(tMonW (Rn n) (tn n) (r - N) (d - r) ⊓ testSp n r N) ≤ socleCount n r d N

/-- **The membership bound from the reduced input.** -/
theorem modelSocleMembership_of_testBound {n r : ℕ} (hn : 1 ≤ n) (h : TestBound n r) :
    ModelSocleMembership n r :=
  modelSocleMembership_of_below hn fun d N hN =>
    (Submodule.rank_mono (le_inf (vMem_le_tMonW (Rn n) (tn n) hN.le d)
      (vMem_le_testSp n r d N))).trans (h d N hN)

/-! ### The box split -/

section Box

variable {R : Type} [CommRing R] [Algebra ℂ R]

/-- The span of the products `t_{m₁} ⋯ t_{m_k}` of weight `Σ (m_i + 1) = e` with all `m_i < N`. -/
def boxW (t : ℕ → R) (N k : ℕ) (e : ℤ) : Submodule ℂ R :=
  Submodule.span ℂ {x | ∃ l : List ℕ, l.length = k ∧ (((l.map fun m => m + 1).sum : ℕ) : ℤ) = e ∧
    (∀ m ∈ l, m < N) ∧ (l.map t).prod = x}

theorem boxW_le_tMonW (t : ℕ → R) (N k : ℕ) (e : ℤ) : boxW t N k e ≤ tMonW R t k e := by
  rw [boxW, Submodule.span_le]
  rintro _ ⟨l, hl, he, -, rfl⟩
  exact Submodule.subset_span ⟨l, hl, he, rfl⟩

end Box

/-- **Structural half**: a `T`-polynomial passing the test only involves `T_0, …, T_{N-1}`. -/
def BoxInclusion (n r : ℕ) : Prop :=
  ∀ (d : ℤ) (N : ℕ), N < r →
    tMonW (Rn n) (tn n) (r - N) (d - r) ⊓ testSp n r N ≤ boxW (tn n) N (r - N) (d - r)

/-- **Counting half**: the image in `R_n` of the polynomials in `T_0, …, T_{N-1}` of degree `r - N`
and weight `d - r` has dimension at most the socle-word count. -/
def BoxCount (n r : ℕ) : Prop :=
  ∀ (d : ℤ) (N : ℕ), N < r → Module.rank ℂ ↥(boxW (tn n) N (r - N) (d - r)) ≤ socleCount n r d N

/-- The reduced input from its two halves. -/
theorem testBound_of_box {n r : ℕ} (hI : BoxInclusion n r) (hC : BoxCount n r) :
    TestBound n r := fun d N hN =>
  (Submodule.rank_mono (hI d N hN)).trans (hC d N hN)

/-! ### `T`-degree one -/

/-- The socle word with a single letter `1` at position `p` (all other letters `0`). -/
def singleWord {n : ℕ} (hn : 2 ≤ n) (N : ℕ) (p : Fin N) : Fin N → Fin n :=
  fun j => if j = p then ⟨1, hn⟩ else ⟨0, by omega⟩

theorem singleWord_sum {n : ℕ} (hn : 2 ≤ n) (N : ℕ) (p : Fin N) :
    ∑ j, (((singleWord hn N p j : Fin n) : ℕ) + 1) = N + 1 := by
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    mul_one, add_comm]
  congr 1
  rw [Finset.sum_eq_single p]
  · simp [singleWord]
  · intro j _ hj; simp [singleWord, hj]
  · simp

theorem clusterAtLeast_singleWord {n : ℕ} (hn : 2 ≤ n) (N : ℕ) (p : Fin N) (t : ℕ) (ht : 1 ≤ t) :
    clusterAtLeast (singleWord hn N p) t = if t = 1 then 1 else 0 := by
  rw [clusterAtLeast]
  split_ifs with h1
  · subst h1
    rw [Finset.card_eq_one]
    refine ⟨p, ?_⟩
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, singleWord]
    split_ifs with hj <;> simp [hj]
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro j _
    simp only [singleWord]
    split_ifs <;> simp <;> omega

theorem inversions_singleWord {n : ℕ} (hn : 2 ≤ n) (N : ℕ) (p : Fin N) :
    inversions (singleWord hn N p) = N - 1 - p := by
  rw [inversions, ← Fin.card_Ioi p]
  have : (Finset.univ.filter fun q : Fin N × Fin N =>
      q.1 < q.2 ∧ singleWord hn N p q.2 < singleWord hn N p q.1) =
      (Finset.Ioi p).map ⟨fun j => (p, j), fun a b h => (Prod.mk.inj h).2⟩ := by
    ext ⟨i, j⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Finset.mem_Ioi, Function.Embedding.coeFn_mk, Prod.mk.injEq, singleWord]
    constructor
    · rintro ⟨hij, h⟩
      by_cases hi : i = p
      · subst hi
        exact ⟨j, hij, rfl, rfl⟩
      · rw [if_neg hi] at h
        split_ifs at h <;> simp [Fin.lt_def] at h
    · rintro ⟨k, hk, rfl, rfl⟩
      refine ⟨hk, ?_⟩
      rw [if_neg (ne_of_gt hk), if_pos rfl]
      simp [Fin.lt_def]
  rw [this, Finset.card_map]

theorem socleDegree_singleWord {n : ℕ} (hn : 2 ≤ n) (N : ℕ) (p : Fin N) :
    socleDegree (singleWord hn N p) = N + 2 + (N - 1 - p) := by
  unfold socleDegree
  rw [inversions_singleWord]
  congr 2
  rw [Finset.sum_eq_single 1]
  · rw [clusterAtLeast_singleWord hn N p 1 le_rfl, if_pos rfl]; rfl
  · intro t ht ht1
    rw [clusterAtLeast_singleWord hn N p t (Finset.mem_Ico.mp ht).1, if_neg ht1]; rfl
  · intro h
    exact absurd (Finset.mem_Ico.mpr ⟨le_rfl, hn⟩) h

/-- **`BoxCount` in `T`-degree one** (`r = N + 1`), for every `n ≥ 2`: the box is spanned by
the single jet `T_{e-1}` with `e - 1 < N`, and the word with one letter `1` at position `N - e`
has the matching degree. -/
theorem boxCount_single {n : ℕ} (hn : 2 ≤ n) (d : ℤ) (N : ℕ) :
    Module.rank ℂ ↥(boxW (tn n) N 1 (d - (N + 1 : ℕ))) ≤ socleCount n (N + 1) d N := by
  by_cases he : ∃ m : ℕ, m < N ∧ ((m + 1 : ℕ) : ℤ) = d - (N + 1 : ℕ)
  · obtain ⟨m, hmN, hme⟩ := he
    have hle : boxW (tn n) N 1 (d - (N + 1 : ℕ)) ≤ Submodule.span ℂ {tn n m} := by
      rw [boxW, Submodule.span_le]
      rintro _ ⟨l, hl, hle, -, rfl⟩
      obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp hl
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at hle
      have ham : a = m := by omega
      subst ham
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      exact Submodule.subset_span rfl
    refine (Submodule.rank_mono hle).trans ((rank_span_le _).trans ?_)
    rw [Cardinal.mk_singleton]
    have hpos : 0 < socleCount n (N + 1) d N := by
      let p : Fin N := ⟨N - 1 - m, by omega⟩
      haveI : Nonempty {i : SocleIndex n (N + 1) //
          ((socleDegree i.2.1 : ℕ) : ℤ) = d ∧ (i.1 : ℕ) = N} :=
        ⟨⟨⟨⟨N, by omega⟩, ⟨singleWord hn N p, singleWord_sum hn N p⟩⟩, by
          change ((socleDegree (singleWord hn N p) : ℕ) : ℤ) = d
          rw [socleDegree_singleWord]
          have hp : (p : ℕ) = N - 1 - m := rfl
          rw [hp]
          push_cast at hme ⊢
          have h1 : ((N - 1 - (N - 1 - m) : ℕ) : ℤ) = m := by
            rw [show N - 1 - (N - 1 - m) = m by omega]
          rw [h1]
          linarith, rfl⟩⟩
      exact Nat.card_pos
    exact_mod_cast hpos
  · push Not at he
    have hbot : boxW (tn n) N 1 (d - (N + 1 : ℕ)) = ⊥ := by
      rw [eq_bot_iff, boxW, Submodule.span_le]
      rintro _ ⟨l, hl, hle, hlN, rfl⟩
      obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp hl
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at hle
      exact absurd hle (he a (hlN a (by simp)))
    rw [hbot, rank_bot]
    exact zero_le

/-! ### The endpoints -/

/-- **Affine GU ⇒ GU of `M(2, 2n+3)`**, `#print axioms`-clean, conditional on `hA`,
detection `det`, and the reduced input `TestBound n r` for every `r`. -/
theorem twoSeries_gradedUnitary_of_strictModel_testBound (n : ℕ) (hn : 1 ≤ n)
    (hA : GradedUnitary (affineForm (twoSeriesLevels n)) (affineRealStructure (twoSeriesLevels n))
      (affineFlag (twoSeriesLevels n)))
    (det : TwoSeriesModelDetects n) (tb : ∀ r, TestBound n r) :
    VirGradedUnitary (twoSeriesLevels n).c (targetRealStructure (twoSeriesLevels n)) :=
  twoSeries_gradedUnitary_of_strictModel_membership n hn hA det fun r =>
    modelSocleMembership_of_testBound hn (tb r)

/-- **Affine GU ⇒ GU of `M(2, 2n+3)`**, `#print axioms`-clean, conditional on `hA`,
detection `det`, the structural half `BoxInclusion` and the counting half `BoxCount`. -/
theorem twoSeries_gradedUnitary_of_strictModel_box (n : ℕ) (hn : 1 ≤ n)
    (hA : GradedUnitary (affineForm (twoSeriesLevels n)) (affineRealStructure (twoSeriesLevels n))
      (affineFlag (twoSeriesLevels n)))
    (det : TwoSeriesModelDetects n) (incl : ∀ r, BoxInclusion n r) (cnt : ∀ r, BoxCount n r) :
    VirGradedUnitary (twoSeriesLevels n).c (targetRealStructure (twoSeriesLevels n)) :=
  twoSeries_gradedUnitary_of_strictModel_testBound n hn hA det fun r =>
    testBound_of_box (incl r) (cnt r)

end

end VOA.TwoSeries.StrictModel
