/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Data.Complex.Basic

/-!
# Rational echelon bases for finite families of power series

For the Anderson–Moore rationality argument we need: the `ℂ`-span of finitely many power series
with rational coefficients has a spanning family of power series with rational coefficients and
pairwise distinct orders (an "echelon" family), each of which lies in the span.

The construction is Gaussian elimination by leading terms. A new series is reduced against the
current echelon family by repeatedly subtracting a rational multiple of the member having the
same order; leading coefficients are rational and nonzero, so the multiplier is rational, and the
order strictly increases. Termination is by strong induction on the number of members whose
order is at least the order of the current remainder.

## Main definitions and results

* `RatCoeffs F` : every coefficient of `F` is (the image of) a rational number.
* `RatCoeffs.add`, `.neg`, `.sub`, `.smul_rat`, `.mul`, `.zero` : closure properties.
* `RatCoeffs.map_eq` : a series with rational coefficients is fixed by every `σ : ℂ →+* ℂ`
  acting on coefficients.
* `exists_echelon` : the echelon family for a finite family with rational coefficients.
-/

namespace VOA.Huang.AndersonMoore

open PowerSeries

/-- All coefficients of the power series `F` are rational. -/
def RatCoeffs (F : PowerSeries ℂ) : Prop := ∀ m : ℕ, ∃ r : ℚ, PowerSeries.coeff m F = (r : ℂ)

namespace RatCoeffs

theorem zero : RatCoeffs 0 := fun _ => ⟨0, by simp⟩

theorem add {F G : PowerSeries ℂ} (hF : RatCoeffs F) (hG : RatCoeffs G) :
    RatCoeffs (F + G) := by
  intro m
  obtain ⟨r, hr⟩ := hF m
  obtain ⟨s, hs⟩ := hG m
  exact ⟨r + s, by simp [hr, hs]⟩

theorem neg {F : PowerSeries ℂ} (hF : RatCoeffs F) : RatCoeffs (-F) := by
  intro m
  obtain ⟨r, hr⟩ := hF m
  exact ⟨-r, by simp [hr]⟩

theorem sub {F G : PowerSeries ℂ} (hF : RatCoeffs F) (hG : RatCoeffs G) :
    RatCoeffs (F - G) := by
  intro m
  obtain ⟨r, hr⟩ := hF m
  obtain ⟨s, hs⟩ := hG m
  exact ⟨r - s, by simp [hr, hs]⟩

theorem smul_rat {F : PowerSeries ℂ} (hF : RatCoeffs F) (q : ℚ) :
    RatCoeffs ((q : ℂ) • F) := by
  intro m
  obtain ⟨r, hr⟩ := hF m
  exact ⟨q * r, by simp [hr]⟩

theorem mul {F G : PowerSeries ℂ} (hF : RatCoeffs F) (hG : RatCoeffs G) :
    RatCoeffs (F * G) := by
  intro m
  choose r hr using hF
  choose s hs using hG
  exact ⟨∑ p ∈ Finset.antidiagonal m, r p.1 * s p.2, by simp [PowerSeries.coeff_mul, hr, hs]⟩

/-- A power series with rational coefficients is fixed by every ring endomorphism of `ℂ`
applied coefficientwise. -/
theorem map_eq {F : PowerSeries ℂ} (hF : RatCoeffs F) (σ : ℂ →+* ℂ) :
    PowerSeries.map σ F = F := by
  ext m
  obtain ⟨r, hr⟩ := hF m
  simp [PowerSeries.coeff_map, hr]

end RatCoeffs

/-- A finite set of power series is *echelon* if its members have rational coefficients, are
nonzero, and have pairwise distinct orders. -/
def IsEchelon (S : Finset (PowerSeries ℂ)) : Prop :=
  (∀ e ∈ S, RatCoeffs e ∧ e ≠ 0) ∧ ∀ e ∈ S, ∀ e' ∈ S, e.order = e'.order → e = e'

/-- Reduction of a series with rational coefficients against an echelon set: the remainder `g`
has rational coefficients, differs from `f` by an element of the span, and is either zero or of
an order not attained by the echelon set. Stated with an explicit termination measure `k`. -/
theorem exists_reduce_aux (S : Finset (PowerSeries ℂ)) (hS : IsEchelon S) :
    ∀ (k : ℕ) (f : PowerSeries ℂ), RatCoeffs f →
      (S.filter (fun e => f.order ≤ e.order)).card = k →
      ∃ g, RatCoeffs g ∧ f - g ∈ Submodule.span ℂ (S : Set (PowerSeries ℂ)) ∧
        (g = 0 ∨ ∀ e ∈ S, e.order ≠ g.order) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro f hf hk
  by_cases hex : ∃ e ∈ S, e.order = f.order
  swap
  · push Not at hex
    exact ⟨f, hf, by simp, Or.inr hex⟩
  obtain ⟨e, heS, heo⟩ := hex
  by_cases hf0 : f = 0
  · exact ⟨0, RatCoeffs.zero, by simp [hf0], Or.inl rfl⟩
  obtain ⟨he, he0⟩ := hS.1 e heS
  set n := f.order.toNat with hn
  have hfn : f.order = n :=
    (ENat.coe_toNat (by simpa [PowerSeries.order_eq_top] using hf0)).symm
  have hen : e.order = n := heo.trans hfn
  obtain ⟨r, hr⟩ := hf n
  obtain ⟨s, hs⟩ := he n
  have hs0 : (s : ℂ) ≠ 0 := by
    rw [← hs]
    have := PowerSeries.coeff_order he0
    rwa [hen, ENat.toNat_coe] at this
  set f' := f - ((r / s : ℚ) : ℂ) • e with hf'def
  have hf' : RatCoeffs f' := hf.sub (he.smul_rat _)
  have hlt : (n : ℕ∞) < f'.order := by
    have hle : ((n + 1 : ℕ) : ℕ∞) ≤ f'.order := by
      apply PowerSeries.le_order
      intro i hi
      have hi' : i < n + 1 := by exact_mod_cast hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi' with hi'' | rfl
      · have h1 : PowerSeries.coeff i f = 0 :=
          PowerSeries.coeff_of_lt_order i (by rw [hfn]; exact_mod_cast hi'')
        have h2 : PowerSeries.coeff i e = 0 :=
          PowerSeries.coeff_of_lt_order i (by rw [hen]; exact_mod_cast hi'')
        simp [hf'def, h1, h2]
      · simp only [hf'def, map_sub, map_smul, hr, hs, smul_eq_mul]
        push_cast
        rw [div_mul_cancel₀ _ hs0, sub_self]
    exact lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self n) hle
  have hsub : S.filter (fun e' => f'.order ≤ e'.order) ⊂
      S.filter (fun e' => f.order ≤ e'.order) := by
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨e, by simp [heS, heo], ?_⟩
      simp only [Finset.mem_filter, not_and, not_le]
      intro _
      rw [hen]
      exact hlt
    · intro e' he'
      simp only [Finset.mem_filter] at he' ⊢
      exact ⟨he'.1, hfn ▸ (hlt.le.trans he'.2)⟩
  obtain ⟨g, hg, hfg, hg'⟩ := ih _ (hk ▸ Finset.card_lt_card hsub) f' hf' rfl
  refine ⟨g, hg, ?_, hg'⟩
  have : f - g = (f' - g) + ((r / s : ℚ) : ℂ) • e := by
    rw [hf'def]
    abel
  rw [this]
  exact add_mem hfg (Submodule.smul_mem _ _ (Submodule.subset_span heS))

/-- Finset form of `exists_echelon`, by induction on the index set. -/
theorem exists_echelon_finset {ι : Type*} (H : ι → PowerSeries ℂ) (hH : ∀ i, RatCoeffs (H i))
    (s : Finset ι) :
    ∃ S : Finset (PowerSeries ℂ), IsEchelon S ∧
      (S : Set (PowerSeries ℂ)) ⊆ Submodule.span ℂ (H '' s) ∧
      ∀ i ∈ s, H i ∈ Submodule.span ℂ (S : Set (PowerSeries ℂ)) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨∅, ⟨by simp, by simp⟩, by simp, by simp⟩
  | insert i s hi ih =>
    obtain ⟨S, hS, hSs, hsS⟩ := ih
    obtain ⟨g, hg, hfg, hg'⟩ := exists_reduce_aux S hS _ (H i) (hH i) rfl
    have hmono : Submodule.span ℂ (H '' (s : Set ι)) ≤
        Submodule.span ℂ (H '' ((insert i s : Finset ι) : Set ι)) :=
      Submodule.span_mono (Set.image_mono (by simp))
    have hSle : Submodule.span ℂ (S : Set (PowerSeries ℂ)) ≤
        Submodule.span ℂ (H '' ((insert i s : Finset ι) : Set ι)) :=
      Submodule.span_le.mpr (hSs.trans hmono)
    have hHi : H i ∈ Submodule.span ℂ (H '' ((insert i s : Finset ι) : Set ι)) :=
      Submodule.subset_span ⟨i, by simp, rfl⟩
    by_cases hg0 : g = 0
    · subst hg0
      refine ⟨S, hS, hSs.trans hmono, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · simpa using hfg
      · exact hsS j hj
    have hg'' : ∀ e ∈ S, e.order ≠ g.order := hg'.resolve_left hg0
    have hSg : Submodule.span ℂ (S : Set (PowerSeries ℂ)) ≤
        Submodule.span ℂ ((insert g S : Finset (PowerSeries ℂ)) : Set (PowerSeries ℂ)) :=
      Submodule.span_mono (by simp)
    refine ⟨insert g S, ⟨?_, ?_⟩, ?_, ?_⟩
    · intro e he
      rcases Finset.mem_insert.mp he with rfl | he
      · exact ⟨hg, hg0⟩
      · exact hS.1 e he
    · intro e he e' he' h
      rcases Finset.mem_insert.mp he with rfl | heS
      · rcases Finset.mem_insert.mp he' with rfl | he'S
        · rfl
        · exact absurd h.symm (hg'' e' he'S)
      · rcases Finset.mem_insert.mp he' with rfl | he'S
        · exact absurd h (hg'' e heS)
        · exact hS.2 e heS e' he'S h
    · rw [Finset.coe_insert, Set.insert_subset_iff]
      refine ⟨?_, hSs.trans hmono⟩
      have : g = H i - (H i - g) := by abel
      rw [this]
      exact sub_mem hHi (hSle hfg)
    · intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · have : H j = (H j - g) + g := by abel
        rw [this]
        exact add_mem (hSg hfg) (Submodule.subset_span (by simp))
      · exact hSg (hsS j hj)

/-- **Rational echelon form.** A finite family of power series with rational coefficients has a
spanning family of nonzero power series with rational coefficients and pairwise distinct orders,
each lying in the span of the original family. -/
theorem exists_echelon {ι : Type*} [Finite ι] (H : ι → PowerSeries ℂ)
    (hH : ∀ i, RatCoeffs (H i)) :
    ∃ (d : ℕ) (E : Fin d → PowerSeries ℂ), (∀ l, RatCoeffs (E l)) ∧ (∀ l, E l ≠ 0) ∧
      Function.Injective (fun l => (E l).order) ∧
      (∀ l, E l ∈ Submodule.span ℂ (Set.range H)) ∧
      (∀ i, H i ∈ Submodule.span ℂ (Set.range E)) := by
  classical
  haveI := Fintype.ofFinite ι
  obtain ⟨S, hS, hSs, hsS⟩ := exists_echelon_finset H hH Finset.univ
  let e := S.equivFin.symm
  refine ⟨S.card, fun l => (e l : PowerSeries ℂ), fun l => (hS.1 _ (e l).2).1,
    fun l => (hS.1 _ (e l).2).2, ?_, ?_, ?_⟩
  · intro l l' h
    exact e.injective (Subtype.ext (hS.2 _ (e l).2 _ (e l').2 h))
  · intro l
    have := hSs (e l).2
    simpa [Set.image_univ] using this
  · intro i
    have hrange : Set.range (fun l => (e l : PowerSeries ℂ)) = (S : Set (PowerSeries ℂ)) := by
      ext y
      constructor
      · rintro ⟨l, rfl⟩
        exact (e l).2
      · intro hy
        exact ⟨e.symm ⟨y, hy⟩, by simp⟩
    rw [hrange]
    exact hsS i (Finset.mem_univ i)

end VOA.Huang.AndersonMoore
