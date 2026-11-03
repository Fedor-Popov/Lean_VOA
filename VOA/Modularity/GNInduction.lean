/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.GNWords

/-!
# Gaberdiel–Neitzke Prop. 8, layer 2: the `(g, N)` induction principle and the base cases

`Modularity.GNWords` supplies the words, the grade filtration `ℋ^{(g)}` and the two order
predicates.  This file supplies the *shape* of GN's induction — the lexicographic recursion on
`(g, N)` — and the two base cases.

**The lexicographic order needs no `Prod.Lex` plumbing.**  GN's induction allows, at `(g, N)`,
appeals to *any* `(g', N')` with `g' < g`, and to `(g, N')` with `N' < N`.  That is exactly a strong
induction on `g` with a strong induction on `N` inside it, so `gnLexInduction` below is the
well-founded recursion in directly usable form.

**The `g = 0` base case is sharp.**  A word of total conformal weight `0` has every letter in
`𝒱₀ = ℂ𝟙` (`VacuumGradeZero`), and the vacuum field axiom `𝟙₍ₙ₎v = δ_{n,−1}·v` collapses every such
word on the vacuum to `𝟙` or `0`.  Hence `ℋ^{(0)} = ℂ𝟙` — `gnGradeFil_zero`.

## Main results

* `gnLexInduction` — the `(g, N)` lexicographic induction principle;
* `gnGradeFil_zero` — `ℋ^{(0)} = ℂ·𝟙`, the grade base case;
* `gnNoRepeatLE_zero` — the `N = 0` base case of the order layer: *every* word has no repeats
  at or below `0`, since all mode indices are positive.

## Status
Proved, axiom-clean, `pbw`-free, no `sorry`.  Layer 2 of Prop. 8; the `(s, m)` case split is not
here.
-/

namespace VOA

open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The lexicographic induction principle -/

/-- **GN's lexicographic induction on `(g, N)`.**  At `(g, N)` one may appeal to every `(g', N')`
with `g' < g`, and to every `(g, N')` with `N' < N`. -/
theorem gnLexInduction {P : ℕ → ℕ → Prop}
    (step : ∀ g N : ℕ, (∀ g' N' : ℕ, g' < g → P g' N') → (∀ N' : ℕ, N' < N → P g N') → P g N) :
    ∀ g N : ℕ, P g N := by
  intro g
  induction g using Nat.strong_induction_on with
  | _ g ihg =>
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ihN => exact step g N (fun g' N' hg' => ihg g' hg' N') ihN

/-! ## The `N = 0` base case -/

/-- **`N = 0` is vacuous**: mode indices are positive, so no word has a repeat at or below `0`. -/
theorem gnNoRepeatLE_zero {W : VertexOperatorAlgebra 𝒱} {l : List (GNLetter 𝒱)}
    (h : GNWordOK W l) : GNNoRepeatLE 0 l := by
  rw [GNNoRepeatLE, List.pairwise_iff_forall_sublist]
  intro a b hab
  intro ha0 _
  exact absurd ha0 (by
    have := h.2 a (hab.subset (by simp))
    omega)

/-! ## The `g = 0` base case -/

/-- A grade-`0` admissible word has every letter of weight `0`. -/
theorem gnWordGrade_zero_wt {l : List (GNLetter 𝒱)} (hg : gnWordGrade l = 0) :
    ∀ p ∈ l, p.2.1 = 0 := by
  intro p hp
  by_contra hne
  have hmem : p.2.1 ∈ l.map (fun q : GNLetter 𝒱 => q.2.1) := List.mem_map_of_mem hp
  have hpos : 0 < p.2.1 := Nat.pos_of_ne_zero hne
  have hle : p.2.1 ≤ (l.map (fun q : GNLetter 𝒱 => q.2.1)).sum :=
    List.single_le_sum (fun _ _ => Nat.zero_le _) _ hmem
  rw [← gnWordGrade, hg] at hle
  omega

/-- A word all of whose letters are scalar multiples of the vacuum collapses: on the vacuum it is
either `𝟙` or `0`. -/
theorem gnWord_vacuumLetters {W : VertexOperatorAlgebra 𝒱} :
    ∀ (l : List (GNLetter 𝒱)), (∀ p ∈ l, ∃ c : ℂ, p.1 = c • W.vacuum) →
      gnWord W l W.vacuum ∈ Submodule.span ℂ ({W.vacuum} : Set 𝒱) := by
  intro l
  induction l with
  | nil =>
      intro _
      exact Submodule.mem_span_singleton_self W.vacuum
  | cons p l ih =>
      intro hall
      obtain ⟨c, hc⟩ := hall p (List.mem_cons_self ..)
      have hrest := ih (fun q hq => hall q (List.mem_cons_of_mem _ hq))
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hrest
      rw [gnWord_cons, hc, ← ha, W.smul_smul_left, W.smul_smul_right,
        W.toPreVertexAlgebra.smul_vacuum_left]
      by_cases hn : (-(p.2.2 : ℤ)) = -1
      · rw [if_pos hn]
        exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _
          (Submodule.mem_span_singleton_self W.vacuum))
      · rw [if_neg hn, smul_zero, smul_zero]
        exact Submodule.zero_mem _

/-- **The grade base case**: `ℋ^{(0)} = ℂ·𝟙`. -/
theorem gnGradeFil_zero {W : VertexOperatorAlgebra 𝒱} (hzero : VacuumGradeZero W) :
    gnGradeFil W 0 = Submodule.span ℂ ({W.vacuum} : Set 𝒱) := by
  refine le_antisymm ?_ ?_
  · rw [gnGradeFil, Submodule.span_le]
    rintro x ⟨l, hOK, hg, rfl⟩
    refine gnWord_vacuumLetters l (fun p hp => ?_)
    have hw : p.2.1 = 0 := gnWordGrade_zero_wt (Nat.le_zero.mp hg) p hp
    have hmem : p.1 ∈ W.grading (0 : ℤ) := by
      have := hOK.1 p hp
      rwa [hw, Nat.cast_zero] at this
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hzero hmem)
    exact ⟨c, hc.symm⟩
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact vacuum_mem_gnGradeFil W 0

end VOA
