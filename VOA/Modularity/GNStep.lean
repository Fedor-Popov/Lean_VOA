/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.GNBlock

/-!
# Gaberdiel–Neitzke Prop. 8, layer 5: the induction step `(gr, N) → (gr, N+1)`

`Modularity.GNBlock` proves GN's `s < 2` sub-case at the level of a single word.  This file lifts
it to the level the induction actually consumes, and applies the banked Lemma 7 to the `m = 0`
configuration.

**The `s < 2` sub-case is discharged outright.**  `gnSpan_succ_of_repeatCase` says: the whole
step `gnSpan … N ≤ gnSpan … (N+1)` follows from handling **only** the words with `s ≥ 2`.  Every
other word already lies in the `(N+1)`-span, by `gnNoRepeatLE_succ_of_count`.  Hence
`GNReach_succ_of_repeatCase` — GN's induction step, reduced to the repeated-block words.

**The `m = 0` configuration is Lemma 7 verbatim.**  A word whose two outermost letters share the
mode index `n` is rewritten by `gnWord_repeatedHead` into terms whose leading mode index is `2n − 1`
or `> n` — the banked `Modularity.GNLemma7.gn_lemma7`, with `x` the sub-word.

## Main results

* `gnSpan_succ_of_repeatCase`, `GNReach_succ_of_repeatCase` — **the `s < 2` sub-case, at span
  level**: the induction step reduces to the words with `s ≥ 2`;
* `gnWord_repeatedHead` — **the `m = 0` rewrite**, Lemma 7 applied to a word.

## Status
Proved, axiom-clean, `pbw`-free, no `sorry`.  Layer 5 of Prop. 8.  The two surviving sub-cases
(`m ≠ 0`, and the re-normalisation of Lemma 7's output) are not treated here.
-/

namespace VOA

open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The `s < 2` sub-case, at span level -/

/-- **GN's induction step reduces to the repeated-block words.**  Every word with at most one
letter at mode index `N+1` already lies in the `(N+1)`-span, so only `s ≥ 2` needs work. -/
theorem gnSpan_succ_of_repeatCase {W : VertexOperatorAlgebra 𝒱} {g : ℕ} {gen : Fin g → 𝒱}
    {wt : Fin g → ℕ} {N : ℕ}
    (hrep : ∀ l : List (GNLetter 𝒱), GNWordOK W l → GNWeakDec l → GNNoRepeatLE N l →
      OverGens gen wt l → 2 ≤ gnCountAt (N + 1) l →
      gnWord W l W.vacuum ∈ gnSpan W gen wt (N + 1)) :
    gnSpan W gen wt N ≤ gnSpan W gen wt (N + 1) := by
  classical
  rw [gnSpan, Submodule.span_le]
  rintro x ⟨l, hOK, hwd, hnr, hog, rfl⟩
  by_cases hs : 2 ≤ gnCountAt (N + 1) l
  · exact hrep l hOK hwd hnr hog hs
  · exact Submodule.subset_span
      ⟨l, hOK, hwd, gnNoRepeatLE_succ_of_count hwd hnr (by omega), hog, rfl⟩

/-- **GN's induction step**, reduced to the repeated-block words. -/
theorem GNReach_succ_of_repeatCase {W : VertexOperatorAlgebra 𝒱} {g : ℕ} {gen : Fin g → 𝒱}
    {wt : Fin g → ℕ} {gr N : ℕ} (hR : GNReach W gen wt gr N)
    (hrep : ∀ l : List (GNLetter 𝒱), GNWordOK W l → GNWeakDec l → GNNoRepeatLE N l →
      OverGens gen wt l → 2 ≤ gnCountAt (N + 1) l →
      gnWord W l W.vacuum ∈ gnSpan W gen wt (N + 1)) :
    GNReach W gen wt gr (N + 1) :=
  le_trans hR (gnSpan_succ_of_repeatCase hrep)

/-! ## The `m = 0` configuration -/

/-- **Lemma 7 applied to a word.**  A word whose two outermost letters share the mode index `n`
is rewritten so that every leading mode index is `2n − 1` or `> n` — strictly above the repeat. -/
theorem gnWord_repeatedHead (W : VertexOperatorAlgebra 𝒱) (a b : 𝒱) (wa wb n : ℕ) (hn : 1 ≤ n)
    (rest : List (GNLetter 𝒱)) :
    gnWord W ((a, wa, n) :: (b, wb, n) :: rest) W.vacuum
      = W.smul (W.smul a (-1) b) (-2 * (n : ℤ) + 1) (gnWord W rest W.vacuum)
        - (∑ᶠ i : ℕ, if i = n - 1 then 0
            else W.smul a (-1 - (i : ℤ))
              (W.smul b (-2 * (n : ℤ) + 1 + (i : ℤ)) (gnWord W rest W.vacuum)))
        - ∑ᶠ i : ℕ, W.smul b (-2 * (n : ℤ) - (i : ℤ))
            (W.smul a (i : ℤ) (gnWord W rest W.vacuum)) := by
  rw [gnWord_cons, gnWord_cons]
  exact gn_lemma7 W a b (gnWord W rest W.vacuum) n hn

end VOA
