/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.GNInduction

/-!
# Gaberdiel–Neitzke Prop. 8, layer 3: the induction statement `GNReach`

`Modularity.GNWords` gives the words and the filtration; `Modularity.GNInduction` gives the
lexicographic recursion and the base cases.  This file names the predicate that the recursion
proves, and records its two monotonicity properties — the ones the induction steps consume.

**The statement GN proves at `(gr, N)`** is, in the paper's own description, that `ℋ^{(gr)}` is
spanned by words over the `C₂`-representatives with ordered modes and *no repeated mode index at or
below `N`*.  That is `GNReach` below.  Prop. 8 is the case `N ≥ every index occurring`, at which
`gnStrictDec_of_noRepeat` upgrades "no repeats below `N`" to strict decrease.

## Main results

* `gnSpan`, `GNReach` — the induction statement;
* `gnSpan_antitone` — a larger `N` is a *stronger* constraint, so the span shrinks;
* `GNReach_mono_grade`, `GNReach_mono_index` — the two directions the induction uses.

## Status
Proved, axiom-clean, `pbw`-free, no `sorry`.  Layer 3 of Prop. 8.  The induction steps themselves
(`N = 0` base, and the `(s, m)` split for `N > 0`) are **not** here.
-/

namespace VOA

open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- A word is **over the generators** `gen` with declared weights `wt`. -/
def OverGens {g : ℕ} (gen : Fin g → 𝒱) (wt : Fin g → ℕ) (l : List (GNLetter 𝒱)) : Prop :=
  ∀ p ∈ l, ∃ i : Fin g, p.1 = gen i ∧ p.2.1 = wt i

theorem OverGens.tail {g : ℕ} {gen : Fin g → 𝒱} {wt : Fin g → ℕ} {p : GNLetter 𝒱}
    {l : List (GNLetter 𝒱)} (h : OverGens gen wt (p :: l)) : OverGens gen wt l :=
  fun q hq => h q (List.mem_cons_of_mem _ hq)

/-- The span of admissible generator words that are weakly decreasing with no repeated mode index
at or below `N`. -/
noncomputable def gnSpan (W : VertexOperatorAlgebra 𝒱) {g : ℕ} (gen : Fin g → 𝒱) (wt : Fin g → ℕ)
    (N : ℕ) : Submodule ℂ 𝒱 :=
  Submodule.span ℂ {x | ∃ l : List (GNLetter 𝒱),
    GNWordOK W l ∧ GNWeakDec l ∧ GNNoRepeatLE N l ∧ OverGens gen wt l ∧
    x = gnWord W l W.vacuum}

/-- **GN's induction statement at `(gr, N)`.** -/
def GNReach (W : VertexOperatorAlgebra 𝒱) {g : ℕ} (gen : Fin g → 𝒱) (wt : Fin g → ℕ)
    (gr N : ℕ) : Prop :=
  gnGradeFil W gr ≤ gnSpan W gen wt N

/-- No repeats below `N'` implies no repeats below any `N ≤ N'`. -/
theorem gnNoRepeatLE_of_le {N N' : ℕ} (h : N ≤ N') {l : List (GNLetter 𝒱)}
    (hl : GNNoRepeatLE N' l) : GNNoRepeatLE N l := by
  rw [GNNoRepeatLE, List.pairwise_iff_forall_sublist] at hl ⊢
  intro a b hab ha hb
  exact hl hab (le_trans ha h) (le_trans hb h)

/-- **A larger `N` is a stronger constraint**, so the admissible span shrinks. -/
theorem gnSpan_antitone (W : VertexOperatorAlgebra 𝒱) {g : ℕ} (gen : Fin g → 𝒱) (wt : Fin g → ℕ)
    {N N' : ℕ} (h : N ≤ N') : gnSpan W gen wt N' ≤ gnSpan W gen wt N := by
  rw [gnSpan, Submodule.span_le]
  rintro x ⟨l, hOK, hwd, hnr, hog, rfl⟩
  exact Submodule.subset_span ⟨l, hOK, hwd, gnNoRepeatLE_of_le h hnr, hog, rfl⟩

/-- Reaching at a larger grade implies reaching at a smaller one. -/
theorem GNReach_mono_grade (W : VertexOperatorAlgebra 𝒱) {g : ℕ} {gen : Fin g → 𝒱}
    {wt : Fin g → ℕ} {gr gr' N : ℕ} (h : gr ≤ gr') (hR : GNReach W gen wt gr' N) :
    GNReach W gen wt gr N :=
  le_trans (gnGradeFil_mono W h) hR

/-- Reaching with a stronger index bound implies reaching with a weaker one. -/
theorem GNReach_mono_index (W : VertexOperatorAlgebra 𝒱) {g : ℕ} {gen : Fin g → 𝒱}
    {wt : Fin g → ℕ} {gr N N' : ℕ} (h : N ≤ N') (hR : GNReach W gen wt gr N') :
    GNReach W gen wt gr N :=
  le_trans hR (gnSpan_antitone W gen wt h)

/-! ## The closure ingredient: a word's degree bounds its mode indices -/

/-- The conformal degree of a word: `∑ᵢ (hᵢ + nᵢ − 1)`. -/
def gnWordDeg (l : List (GNLetter 𝒱)) : ℤ :=
  (l.map (fun p : GNLetter 𝒱 => (p.2.1 : ℤ) + (p.2.2 : ℤ) - 1)).sum

@[simp] theorem gnWordDeg_nil : gnWordDeg ([] : List (GNLetter 𝒱)) = 0 := rfl

@[simp] theorem gnWordDeg_cons (p : GNLetter 𝒱) (l : List (GNLetter 𝒱)) :
    gnWordDeg (p :: l) = ((p.2.1 : ℤ) + (p.2.2 : ℤ) - 1) + gnWordDeg l := rfl

/-- **A word on the vacuum sits in the degree its letters predict.** -/
theorem gnWord_mem_grading (W : VertexOperatorAlgebra 𝒱) :
    ∀ (l : List (GNLetter 𝒱)), GNWordOK W l →
      gnWord W l W.vacuum ∈ W.grading (gnWordDeg l) := by
  intro l
  induction l with
  | nil => intro _; exact W.vacuum_mem_grading_zero
  | cons p l ih =>
      intro h
      have hstep := step_mem_grading W (m := (p.2.2 : ℤ)) h.head_mem (ih h.tail)
      rw [gnWordDeg_cons]
      have hrw : (p.2.1 : ℤ) + gnWordDeg l + (p.2.2 : ℤ) - 1
          = ((p.2.1 : ℤ) + (p.2.2 : ℤ) - 1) + gnWordDeg l := by ring
      rwa [hrw] at hstep

/-- **The closure bound.**  In a word whose letters all have *positive* conformal weight and
positive mode index, every mode index is at most the word's degree.  This is what makes GN's
parameter `N` large enough at a fixed conformal weight: `ℋ_d` only involves indices `≤ d`. -/
theorem gnWordDeg_idx_le :
    ∀ (l : List (GNLetter 𝒱)), (∀ p ∈ l, 1 ≤ p.2.1) → (∀ p ∈ l, 1 ≤ p.2.2) →
      ∀ p ∈ l, (p.2.2 : ℤ) ≤ gnWordDeg l := by
  intro l
  induction l with
  | nil => intro _ _ p hp; exact absurd hp (List.not_mem_nil)
  | cons q l ih =>
      intro hwt hidx p hp
      have hrest : (0 : ℤ) ≤ gnWordDeg l := by
        clear hp ih
        induction l with
        | nil => simp
        | cons r l' ihl =>
            rw [gnWordDeg_cons]
            have h1 : (1 : ℤ) ≤ (r.2.1 : ℤ) := by
              exact_mod_cast hwt r (List.mem_cons_of_mem _ (List.mem_cons_self ..))
            have h2 : (1 : ℤ) ≤ (r.2.2 : ℤ) := by
              exact_mod_cast hidx r (List.mem_cons_of_mem _ (List.mem_cons_self ..))
            have := ihl (fun s hs => hwt s (by
                rcases List.mem_cons.mp hs with rfl | hs' ;
                · exact List.mem_cons_self ..
                · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hs')))
              (fun s hs => hidx s (by
                rcases List.mem_cons.mp hs with rfl | hs' ;
                · exact List.mem_cons_self ..
                · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hs')))
            omega
      have hq1 : (1 : ℤ) ≤ (q.2.1 : ℤ) := by
        exact_mod_cast hwt q (List.mem_cons_self ..)
      rcases List.mem_cons.mp hp with rfl | hp'
      · rw [gnWordDeg_cons]; omega
      · have hle := ih (fun s hs => hwt s (List.mem_cons_of_mem _ hs))
          (fun s hs => hidx s (List.mem_cons_of_mem _ hs)) p hp'
        have hq2 : (1 : ℤ) ≤ (q.2.2 : ℤ) := by
          exact_mod_cast hidx q (List.mem_cons_self ..)
        rw [gnWordDeg_cons]
        omega

end VOA
