/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.GNReach

/-!
# Gaberdiel–Neitzke Prop. 8, layer 4: the `(s, m)` block structure at level `N`

GN's induction step from `(gr, N)` to `(gr, N+1)` splits on two numbers: `s`, the multiplicity of
the mode index `N+1` in the word, and `m`, the number of letters preceding that block.  This file
supplies the list-level facts those numbers rest on.

**The block is contiguous.**  In a weakly decreasing word the letters with a *fixed* mode index
form a contiguous segment, so every word splits canonically as `pre ++ mid ++ post` with indices
`> N`, `= N`, `< N` — `gnWeakDec_split`.  Then `m = pre.length` and `s = mid.length`.

**The `s < 2` sub-case is a pure counting fact.**  If the index `N+1` occurs at most once, a word
with no repeats at or below `N` automatically has none at or below `N+1`
(`gnNoRepeatLE_succ_of_count`).  Weak decrease is what rules out a repeat straddling the levels.

## Main results

* `gnCountAt` — the multiplicity `s` of a mode index;
* `gnNoRepeatLE_succ_of_count` — **GN's `s < 2` sub-case**, proved;
* `gnWeakDec_split` — **the `(s, m)` decomposition**, proved;
* `gnWeakDec_split_lengths` — `m` and `s` read off the decomposition.

## Status
Proved, axiom-clean, `pbw`-free, no `sorry`.  Layer 4 of Prop. 8.
-/

namespace VOA

open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- The multiplicity of the mode index `N` in a word — GN's `s`. -/
def gnCountAt (N : ℕ) (l : List (GNLetter 𝒱)) : ℕ :=
  (l.filter (fun p : GNLetter 𝒱 => decide (p.2.2 = N))).length

/-! ## GN's `s < 2` sub-case -/

/-- **The `s < 2` sub-case of GN's induction step.**  If the mode index `N+1` occurs at most once,
then no repeats at or below `N` upgrades to no repeats at or below `N+1`.  Weak decrease is what
excludes a repeat straddling the two levels. -/
theorem gnNoRepeatLE_succ_of_count {N : ℕ} {l : List (GNLetter 𝒱)}
    (hwd : GNWeakDec l) (hnr : GNNoRepeatLE N l)
    (hs : gnCountAt (N + 1) l ≤ 1) : GNNoRepeatLE (N + 1) l := by
  classical
  rw [GNNoRepeatLE, List.pairwise_iff_forall_sublist]
  intro a b hab ha hb
  have hba : b.2.2 ≤ a.2.2 := by
    have := List.pairwise_iff_forall_sublist.mp hwd hab
    exact this
  intro hEq
  by_cases hlt : a.2.2 ≤ N
  · -- both indices are `≤ N`: the `N`-hypothesis applies
    have hnr' := List.pairwise_iff_forall_sublist.mp hnr hab
    exact hnr' hlt (by omega) hEq
  · -- both indices are exactly `N+1`: that is two occurrences, contradicting `s ≤ 1`
    have haN : a.2.2 = N + 1 := by omega
    have hbN : b.2.2 = N + 1 := by omega
    have hsub : List.Sublist
        (([a, b] : List (GNLetter 𝒱)).filter
          (fun p : GNLetter 𝒱 => decide (p.2.2 = N + 1)))
        (l.filter (fun p : GNLetter 𝒱 => decide (p.2.2 = N + 1))) :=
      List.Sublist.filter _ hab
    have hfil : ([a, b] : List (GNLetter 𝒱)).filter
        (fun p : GNLetter 𝒱 => decide (p.2.2 = N + 1)) = [a, b] := by
      rw [List.filter_cons_of_pos (by simpa using haN),
        List.filter_cons_of_pos (by simpa using hbN), List.filter_nil]
    rw [hfil] at hsub
    have := hsub.length_le
    rw [gnCountAt] at hs
    simp only [List.length_cons, List.length_nil] at this
    omega

/-! ## The `(s, m)` decomposition -/

/-- **The block at a fixed mode index is contiguous.**  A weakly decreasing word splits as
`pre ++ mid ++ post` with mode indices `> N`, `= N`, `< N`.  GN's `m` is `pre.length` and his `s` is
`mid.length`. -/
theorem gnWeakDec_split (N : ℕ) :
    ∀ (l : List (GNLetter 𝒱)), GNWeakDec l →
      ∃ pre mid post : List (GNLetter 𝒱),
        l = pre ++ mid ++ post ∧
        (∀ p ∈ pre, N < p.2.2) ∧ (∀ p ∈ mid, p.2.2 = N) ∧ (∀ p ∈ post, p.2.2 < N) := by
  intro l
  induction l with
  | nil => intro _; exact ⟨[], [], [], rfl, by simp, by simp, by simp⟩
  | cons q l ih =>
      intro hwd
      obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hwd
      obtain ⟨pre, mid, post, hEq, hpre, hmid, hpost⟩ := ih htail
      rcases lt_trichotomy q.2.2 N with h | h | h
      · -- `q` is already below the block: everything after it is too
        refine ⟨[], [], q :: l, by simp, by simp, by simp, ?_⟩
        intro p hp
        rcases List.mem_cons.mp hp with rfl | hp'
        · exact h
        · exact lt_of_le_of_lt (hhead p hp') h
      · -- `q` starts the block; the tail has no letters above `N`, so its `pre` is empty
        have hpre_nil : pre = [] := by
          rw [List.eq_nil_iff_forall_not_mem]
          intro p hp
          have hmem : p ∈ l := by
            rw [hEq]
            exact List.mem_append_left post (List.mem_append_left mid hp)
          have := hhead p hmem
          have := hpre p hp
          omega
        refine ⟨[], q :: mid, post, ?_, by simp, ?_, hpost⟩
        · rw [hEq, hpre_nil]
          simp
        · intro p hp
          rcases List.mem_cons.mp hp with rfl | hp'
          · exact h
          · exact hmid p hp'
      · -- `q` is above the block: prepend it to `pre`
        refine ⟨q :: pre, mid, post, ?_, ?_, hmid, hpost⟩
        · rw [hEq]; simp
        · intro p hp
          rcases List.mem_cons.mp hp with rfl | hp'
          · exact h
          · exact hpre p hp'

/-- `m` and `s` read off the decomposition. -/
theorem gnWeakDec_split_lengths {N : ℕ} {l pre mid post : List (GNLetter 𝒱)}
    (hEq : l = pre ++ mid ++ post) (hmid : ∀ p ∈ mid, p.2.2 = N)
    (hpre : ∀ p ∈ pre, N < p.2.2) (hpost : ∀ p ∈ post, p.2.2 < N) :
    gnCountAt N l = mid.length := by
  classical
  have hfp : pre.filter (fun p : GNLetter 𝒱 => decide (p.2.2 = N)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro p hp
    have := hpre p hp
    simp only [decide_eq_true_eq]
    omega
  have hfm : mid.filter (fun p : GNLetter 𝒱 => decide (p.2.2 = N)) = mid := by
    rw [List.filter_eq_self]
    intro p hp
    simpa using hmid p hp
  have hfq : post.filter (fun p : GNLetter 𝒱 => decide (p.2.2 = N)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro p hp
    have := hpost p hp
    simp only [decide_eq_true_eq]
    omega
  rw [gnCountAt, hEq, List.filter_append, List.filter_append, hfp, hfm, hfq]
  simp

end VOA
