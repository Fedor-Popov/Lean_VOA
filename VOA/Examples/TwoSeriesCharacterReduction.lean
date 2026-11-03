/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.TwoSeriesCharacterSpanning

/-!
# The Andrews–Gordon coefficient and the reduction of the refined PBW character

For the `(2, 2n+3)` minimal model the natural length-refined coefficient is the
**Andrews–Gordon count**

`gordonCoeff n N r = #{sorted words u of length r and energy N with u_i ≥ u_{i+n} + 2}`
`             = #{partitions of N into r parts ≥ 2 with f_m + f_{m+1} ≤ n}`

(`f_m` the multiplicity of the part `m`).  With the proved Gordon spanning
(`goodFil_eq_gordonSpan`) this file proves:

* `finrank_pieceIn_le_gordon` — **the refined upper bound**
  `dim G_p L(c)_N ≤ Σ_{r ≤ p} gordonCoeff n N r`, given `HasJetRelations c n`;
* `hpbw_of_gordonLowerBound` — the refined **lower** bound (the `hpbw` input of the coset
  transfer theorem), from the jet relations and the *unrefined* total lower bound
  `GordonLowerBound c n : ∀ N, Σ_r gordonCoeff n N r ≤ dim L(c)_N`
  (the squeeze: spanning + total count force the Gordon-good words to be a basis adapted to the
  length flag);
* `gordonLowerBound_of_hpbw`, `hpbw_iff_gordonLowerBound` — conversely, so the refined
  statement is *equivalent* to the total one.

The total lower bound is **not** proved here; it is the Rocha-Caridi / Feigin–Fuchs vacuum
character of `M(2,2n+3)` combined with the Andrews–Gordon identity.  It is kept here as the explicit
named hypothesis `GordonLowerBound`, and is proved downstream for every `n` at `c = c_{2,2n+3}`:
`TwoSeries.gordonLowerBound_twoSeries` (`TwoSeriesCharacterAGIdentity.lean`).
-/

namespace VOA.TwoSeriesCharacter

open VOA.VirModule VOA.VirGoodFil VOA.VirSimple VOA.LeeYangCharacter
open scoped BigOperators

noncomputable section

/-! ## §1  The Andrews–Gordon words and their count -/

/-- The word of a tuple. -/
def tupleList {N r : ℕ} (a : Fin r → Fin (N + 1)) : List ℕ := List.ofFn fun j => (a j : ℕ)

/-- Gordon-good sorted words of energy `N` and length exactly `r`. -/
def gordonWords (n N r : ℕ) : Finset (List ℕ) :=
  ((Finset.univ : Finset (Fin r → Fin (N + 1))).image tupleList).filter
    (fun u => SortedWord u ∧ GordonGood n u ∧ energyVir u = N)

theorem le_energyVir : ∀ (u : List ℕ), ∀ x ∈ u, x + 2 ≤ energyVir u
  | [], x, hx => by simp at hx
  | a :: u, x, hx => by
      rw [energyVir_cons]
      rcases List.mem_cons.mp hx with rfl | hx
      · omega
      · have := le_energyVir u x hx; omega

theorem mem_gordonWords {n N r : ℕ} {u : List ℕ} :
    u ∈ gordonWords n N r ↔ SortedWord u ∧ GordonGood n u ∧ energyVir u = N ∧ u.length = r := by
  simp only [gordonWords, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨a, rfl⟩, hs, hg, hE⟩
    exact ⟨hs, hg, hE, by simp [tupleList]⟩
  · rintro ⟨hs, hg, hE, hl⟩
    refine ⟨⟨fun j => ⟨u[j.val]'(by omega), ?_⟩, ?_⟩, hs, hg, hE⟩
    · have hj : j.val < u.length := by omega
      have := le_energyVir u _ (List.getElem_mem hj)
      omega
    · apply List.ext_getElem (by simp [tupleList, hl])
      intro i h1 h2
      simp [tupleList]

/-- **The Andrews–Gordon coefficient**: the number of partitions of `N` into exactly `r`
parts `≥ 2` with `f_m + f_{m+1} ≤ n` (zero for `N < 0`). -/
def gordonCoeff (n : ℕ) (N : ℤ) (r : ℕ) : ℕ :=
  if 0 ≤ N then (gordonWords n N.toNat r).card else 0

theorem gordonCoeff_natCast (n N r : ℕ) : gordonCoeff n (N : ℤ) r = (gordonWords n N r).card := by
  simp [gordonCoeff]

theorem gordonCoeff_neg (n : ℕ) {N : ℤ} (hN : N < 0) (r : ℕ) : gordonCoeff n N r = 0 := by
  simp [gordonCoeff, not_le.mpr hN]

/-- Gordon-good words of energy `N` and length `≤ p`. -/
def gordonWordsLe (n N p : ℕ) : Finset (List ℕ) :=
  (Finset.range (p + 1)).biUnion (gordonWords n N)

theorem mem_gordonWordsLe {n N p : ℕ} {u : List ℕ} :
    u ∈ gordonWordsLe n N p ↔
      SortedWord u ∧ GordonGood n u ∧ energyVir u = N ∧ u.length ≤ p := by
  simp only [gordonWordsLe, Finset.mem_biUnion, Finset.mem_range, mem_gordonWords]
  constructor
  · rintro ⟨r, hr, hs, hg, hE, hl⟩; exact ⟨hs, hg, hE, by omega⟩
  · rintro ⟨hs, hg, hE, hl⟩; exact ⟨u.length, by omega, hs, hg, hE, rfl⟩

theorem card_gordonWordsLe (n N p : ℕ) :
    (gordonWordsLe n N p).card = ∑ r ∈ Finset.range (p + 1), gordonCoeff n (N : ℤ) r := by
  rw [gordonWordsLe, Finset.card_biUnion]
  · exact Finset.sum_congr rfl fun r _ => (gordonCoeff_natCast n N r).symm
  · intro r _ s _ hrs
    rw [Function.onFun, Finset.disjoint_left]
    intro u hu hs
    rw [mem_gordonWords] at hu hs
    exact hrs (hu.2.2.2.symm.trans hs.2.2.2)

theorem gordonWordsLe_subset (n N p : ℕ) : gordonWordsLe n N p ⊆ gordonWordsLe n N N := by
  intro u hu
  rw [mem_gordonWordsLe] at hu ⊢
  refine ⟨hu.1, hu.2.1, hu.2.2.1, ?_⟩
  rw [← hu.2.2.1]
  exact length_le_energyVir u

/-! ## §2  The family of Gordon-good words in `L(c,0)` -/

variable (c : ℂ) (n : ℕ)

/-- The class of a creation word in `L(c,0)`. -/
def gWord (u : List ℕ) : VirUniv c ⧸ maxIdealVir c := (maxIdealVir c).mkQ (negWordVir c u)

/-- The Gordon-good family of energy `N` and length `≤ p`. -/
def gFamily (N p : ℕ) : (gordonWordsLe n N p) → VirUniv c ⧸ maxIdealVir c :=
  fun u => gWord c u.1

theorem goodFil_eq_span_gFamily (hJ : HasJetRelations c n) (p N : ℕ) :
    goodFil c p (N : ℤ) = Submodule.span ℂ (Set.range (gFamily c n N p)) := by
  rw [goodFil_eq_gordonSpan c n hJ]
  apply le_antisymm
  · rw [gordonSpan, Submodule.map_span_le]
    rintro _ ⟨u, hs, hg, hE, hl, rfl⟩
    exact Submodule.subset_span ⟨⟨u, mem_gordonWordsLe.mpr ⟨hs, hg, hE, hl⟩⟩, rfl⟩
  · rw [Submodule.span_le]
    rintro _ ⟨⟨u, hu⟩, rfl⟩
    obtain ⟨hs, hg, hE, hl⟩ := mem_gordonWordsLe.mp hu
    exact Submodule.mem_map_of_mem (Submodule.subset_span ⟨u, hs, hg, hE, hl, rfl⟩)

theorem finrank_pieceIn_eq_goodFil (p : ℕ) (N : ℤ) :
    Module.finrank ℂ ((virGradedFlag c).pieceIn p N) = Module.finrank ℂ (goodFil c p N) :=
  (Submodule.comapSubtypeEquivOfLe (goodFil_le_grading c p N)).finrank_eq

theorem virFil_neg' {p : ℕ} {N : ℤ} (hN : N < 0) : virFil c p N = ⊥ := by
  rw [virFil, Submodule.span_eq_bot]
  rintro _ ⟨w, -, hen, -, rfl⟩
  have : (0 : ℤ) ≤ (energyVir w : ℤ) := Int.natCast_nonneg _
  omega

theorem finrank_pieceIn_neg' {p : ℕ} {N : ℤ} (hN : N < 0) :
    Module.finrank ℂ ((virGradedFlag c).pieceIn p N) = 0 := by
  rw [finrank_pieceIn_eq_goodFil, goodFil, virFil_neg' c hN, Submodule.map_bot, finrank_bot]

/-- **The refined upper bound.** -/
theorem finrank_pieceIn_le_gordon (hJ : HasJetRelations c n) (N : ℤ) (p : ℕ) :
    Module.finrank ℂ ((virGradedFlag c).pieceIn p N) ≤
      ∑ r ∈ Finset.range (p + 1), gordonCoeff n N r := by
  rcases lt_or_ge N 0 with hN | hN
  · rw [finrank_pieceIn_neg' c hN]; exact Nat.zero_le _
  · obtain ⟨N, rfl⟩ := Int.eq_ofNat_of_zero_le hN
    rw [finrank_pieceIn_eq_goodFil, goodFil_eq_span_gFamily c n hJ, ← card_gordonWordsLe]
    have := finrank_range_le_card (R := ℂ) (gFamily c n N p)
    simpa [Set.finrank] using this

/-! ## §3  The named total lower bound and the squeeze -/

/-- Proved for every `n` at `c = c_{2,2n+3}` by `TwoSeries.gordonLowerBound_twoSeries`
(`TwoSeriesCharacterAGIdentity.lean`); not proved in this file.  The **total** Andrews–Gordon lower
bound for the vacuum module — at every weight `N`, the number of partitions of `N` into parts
`≥ 2` with `f_m + f_{m+1} ≤ n` is at most `dim L(c,0)_N`.  For `c = c_{2,2n+3}` this is the
Rocha-Caridi (Feigin–Fuchs) vacuum character of `M(2,2n+3)` combined with the Andrews–Gordon
identity. -/
def GordonLowerBound (c : ℂ) (n : ℕ) : Prop :=
  ∀ N : ℕ, (∑ r ∈ Finset.range (N + 1), gordonCoeff n (N : ℤ) r) ≤
    Module.finrank ℂ ((virasoroSimple c).grading (N : ℤ))

/-- The refined PBW lower bound, in the exact shape of the `hpbw` input of the coset transfer. -/
def GordonPBWLower (c : ℂ) (n : ℕ) : Prop :=
  ∀ (N : ℤ) (p : ℕ), ∑ r ∈ Finset.range (p + 1), gordonCoeff n N r ≤
    Module.finrank ℂ ((virGradedFlag c).pieceIn p N)

theorem goodFil_top' (N : ℕ) : goodFil c N (N : ℤ) = (virasoroSimple c).grading (N : ℤ) :=
  goodFil_eq_grading_of_le c le_rfl

theorem finrank_span_gFamily_top (hJ : HasJetRelations c n) (N : ℕ) :
    Module.finrank ℂ (Submodule.span ℂ (Set.range (gFamily c n N N))) =
      Module.finrank ℂ ((virasoroSimple c).grading (N : ℤ)) := by
  rw [← goodFil_eq_span_gFamily c n hJ, goodFil_top']

/-- The total lower bound makes the spanning Gordon family independent. -/
theorem gFamily_linearIndependent (hJ : HasJetRelations c n) (h : GordonLowerBound c n)
    (N : ℕ) : LinearIndependent ℂ (gFamily c n N N) := by
  rw [linearIndependent_iff_card_eq_finrank_span]
  apply le_antisymm
  · rw [Fintype.card_coe, card_gordonWordsLe, Set.finrank, finrank_span_gFamily_top c n hJ]
    exact h N
  · exact finrank_range_le_card (R := ℂ) (gFamily c n N N)

/-- **The refined PBW lower bound from the total one** (the squeeze). -/
theorem hpbw_of_gordonLowerBound (hJ : HasJetRelations c n) (h : GordonLowerBound c n) :
    GordonPBWLower c n := by
  intro N p
  rcases lt_or_ge N 0 with hN | hN
  · rw [finrank_pieceIn_neg' c hN]
    exact (Finset.sum_eq_zero fun r _ => gordonCoeff_neg n hN r).le
  · obtain ⟨N, rfl⟩ := Int.eq_ofNat_of_zero_le hN
    rw [finrank_pieceIn_eq_goodFil, goodFil_eq_span_gFamily c n hJ, ← card_gordonWordsLe,
      ← Fintype.card_coe]
    have hsub := gordonWordsLe_subset n N p
    let incl : (gordonWordsLe n N p) → (gordonWordsLe n N N) := fun u => ⟨u.1, hsub u.2⟩
    have hincl : Function.Injective incl := fun u v huv => by
      have h1 : (incl u).1 = (incl v).1 := congrArg Subtype.val huv
      exact Subtype.ext h1
    have hcomp : gFamily c n N p = gFamily c n N N ∘ incl := rfl
    have hind : LinearIndependent ℂ (gFamily c n N p) := by
      rw [hcomp]; exact (gFamily_linearIndependent c n hJ h N).comp incl hincl
    exact (finrank_span_eq_card hind).ge

theorem gordonLowerBound_of_hpbw (h : GordonPBWLower c n) : GordonLowerBound c n := by
  intro N
  have hc := h (N : ℤ) N
  rwa [finrank_pieceIn_eq_goodFil, goodFil_top'] at hc

/-- **The refined PBW lower bound is equivalent to the total lower bound** (given the jet
relations). -/
theorem hpbw_iff_gordonLowerBound (hJ : HasJetRelations c n) :
    GordonPBWLower c n ↔ GordonLowerBound c n :=
  ⟨gordonLowerBound_of_hpbw c n, hpbw_of_gordonLowerBound c n hJ⟩

/-- The total-dimension upper bound `dim L(c)_N ≤ Σ_r gordonCoeff n N r`, proved outright from
the jet relations. -/
theorem finrank_grading_le_gordon (hJ : HasJetRelations c n) (N : ℕ) :
    Module.finrank ℂ ((virasoroSimple c).grading (N : ℤ)) ≤
      ∑ r ∈ Finset.range (N + 1), gordonCoeff n (N : ℤ) r := by
  have := finrank_pieceIn_le_gordon c n hJ (N : ℤ) N
  rwa [finrank_pieceIn_eq_goodFil, goodFil_top'] at this

end

end VOA.TwoSeriesCharacter
