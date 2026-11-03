/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.TwoSeriesCharacterReduction

/-!
# Gordon partitions: the frequency form and the Andrews recursion

Lists `l` of naturals stand for partitions with parts `e + 1` (`e ∈ l`).  For a sorted list,
the index condition `GordonGood n l` ("difference two at distance `n`") is equivalent to the
frequency condition of Gordon's theorem (`gordonGood_iff_freq`):

`GordonGood n l ↔ ∀ v, count v l + count (v+1) l ≤ n`.

`gC n i m N` counts sorted Gordon-good lists of length `m`, weight `Σ (e+1) = N`, with fewer
than `i` parts equal to `1` (`count 0 l < i`).  Removing the `a` ones and lowering every other
part by one gives Andrews' recursion (`gC_succ`): for `a ≤ n`,

`gC n (a+1) m N = gC n a m N + [a ≤ m ≤ N] · gC n (n+1-a) (m-a) (N-m)`.

Finally `gordonCoeff n N r = gC n 1 r N` (`gordonCoeff_eq_gC`).  All proved.
-/

namespace VOA.TwoSeriesCharacter

open VOA.VirModule VOA.LeeYangCharacter
open scoped BigOperators

/-! ## §1  The frequency form of the Gordon condition -/

theorem gordonGood_tail {n x : ℕ} {t : List ℕ} (h : GordonGood n (x :: t)) : GordonGood n t := by
  intro i hi
  have := h (i + 1) (by simp; omega)
  simpa [show i + 1 + n = (i + n) + 1 by ring, List.getD_cons_succ] using this

theorem count_add_count_le {v w : ℕ} (hvw : v ≠ w) :
    ∀ l : List ℕ, l.count v + l.count w ≤ l.length
  | [] => by simp
  | x :: l => by
      have := count_add_count_le hvw l
      simp only [List.count_cons, beq_iff_eq, List.length_cons]
      split_ifs <;> omega

theorem freq_of_gordonGood (n : ℕ) : ∀ l : List ℕ, SortedWord l → GordonGood n l →
    ∀ v, l.count v + l.count (v + 1) ≤ n
  | [], _, _, v => by simp
  | x :: t, hs, hg, v => by
      have ih := freq_of_gordonGood n t hs.tail (gordonGood_tail hg) v
      by_cases hx : x = v ∨ x = v + 1
      · have key : t.count v + t.count (v + 1) + 1 ≤ n := by
          rcases lt_or_ge n (t.length + 1) with hlen | hlen
          · have h0 := hg 0 (by simp; omega)
            rcases Nat.eq_zero_or_pos n with hn0 | hnpos
            · subst hn0; simp at h0
            have hn1 : n - 1 < t.length := by omega
            rw [show 0 + n = (n - 1) + 1 by omega, List.getD_cons_succ,
              List.getD_eq_getElem _ _ hn1, List.getD_cons_zero] at h0
            -- every entry from position `n-1` on is below `v`
            have hsplit := (List.take_append_drop (n - 1) t).symm
            have hdrop : ∀ z ∈ t.drop (n - 1), z < v := by
              intro z hz
              obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hz
              rw [List.getElem_drop]
              have := sorted_getElem_le hs.tail (a := n - 1) (b := n - 1 + k) (by omega)
                (by simp at hk; omega)
              omega
            have hc1 : (t.drop (n - 1)).count v = 0 :=
              List.count_eq_zero.mpr fun hm => by have := hdrop v hm; omega
            have hc2 : (t.drop (n - 1)).count (v + 1) = 0 :=
              List.count_eq_zero.mpr fun hm => by have := hdrop (v + 1) hm; omega
            have htake := count_add_count_le (show v ≠ v + 1 by omega) (t.take (n - 1))
            rw [hsplit, List.count_append, List.count_append, hc1, hc2]
            simp only [List.length_take] at htake
            omega
          · have := count_add_count_le (show v ≠ v + 1 by omega) t
            omega
        simp only [List.count_cons, beq_iff_eq]
        rcases hx with rfl | rfl
        · simp only [if_true, show ¬ (x = x + 1) by omega, if_false]; omega
        · simp only [if_true, show ¬ (v + 1 = v) by omega, if_false]; omega
      · push_neg at hx
        simp only [List.count_cons, beq_iff_eq, if_neg hx.1, if_neg hx.2]
        omega

theorem gordonGood_of_freq (n : ℕ) {l : List ℕ} (hs : SortedWord l)
    (hf : ∀ v, l.count v + l.count (v + 1) ≤ n) : GordonGood n l := by
  by_contra hg
  obtain ⟨l₁, W, l₂, b, rfl, hWl, hWb⟩ := exists_window hs hg
  have hsub : W.Sublist (l₁ ++ W ++ l₂) :=
    ((List.sublist_append_right l₁ W).trans (List.sublist_append_left _ l₂))
  have h1 := hsub.count_le b
  have h2 := hsub.count_le (b + 1)
  have hw := (window_counts b W hWb).2
  have := hf b
  omega

/-- **The frequency form of the Gordon condition** for sorted lists. -/
theorem gordonGood_iff_freq (n : ℕ) {l : List ℕ} (hs : SortedWord l) :
    GordonGood n l ↔ ∀ v, l.count v + l.count (v + 1) ≤ n :=
  ⟨freq_of_gordonGood n l hs, gordonGood_of_freq n hs⟩

/-! ## §2  Shifting parts -/

theorem sorted_map_succ {μ : List ℕ} (h : SortedWord μ) : SortedWord (μ.map Nat.succ) := by
  unfold SortedWord at *
  rw [List.pairwise_map]
  exact h.imp fun hab => by simpa using hab

theorem sorted_shift {μ : List ℕ} (h : SortedWord μ) (a : ℕ) :
    SortedWord (μ.map Nat.succ ++ List.replicate a 0) := by
  unfold SortedWord
  rw [List.pairwise_append]
  refine ⟨sorted_map_succ h, ?_, ?_⟩
  · exact List.pairwise_replicate.mpr (Or.inr le_rfl)
  · intro x _ y hy
    rw [List.eq_of_mem_replicate hy]
    exact Nat.zero_le _

theorem count_map_succ_zero (μ : List ℕ) : (μ.map Nat.succ).count 0 = 0 :=
  List.count_eq_zero.mpr fun h => by
    obtain ⟨x, -, hx⟩ := List.mem_map.mp h
    exact Nat.succ_ne_zero x hx

theorem count_map_succ_succ (μ : List ℕ) (v : ℕ) : (μ.map Nat.succ).count (v + 1) = μ.count v :=
  List.count_map_of_injective μ Nat.succ Nat.succ_injective v

theorem count_shift_zero (μ : List ℕ) (a : ℕ) :
    (μ.map Nat.succ ++ List.replicate a 0).count 0 = a := by
  rw [List.count_append, count_map_succ_zero, List.count_replicate_self, zero_add]

theorem count_shift_succ (μ : List ℕ) (a v : ℕ) :
    (μ.map Nat.succ ++ List.replicate a 0).count (v + 1) = μ.count v := by
  rw [List.count_append, count_map_succ_succ, List.count_replicate]
  simp

/-- **The Gordon condition after removing the ones.** -/
theorem gordonGood_shift_iff (n : ℕ) {μ : List ℕ} (hμ : SortedWord μ) (a : ℕ) :
    GordonGood n (μ.map Nat.succ ++ List.replicate a 0) ↔
      GordonGood n μ ∧ μ.count 0 + a ≤ n := by
  rw [gordonGood_iff_freq n (sorted_shift hμ a), gordonGood_iff_freq n hμ]
  constructor
  · intro h
    refine ⟨fun v => ?_, ?_⟩
    · have := h (v + 1)
      rwa [count_shift_succ, count_shift_succ] at this
    · have := h 0
      rw [count_shift_zero, count_shift_succ] at this
      omega
  · rintro ⟨h, h0⟩ v
    rcases v with _ | v
    · rw [count_shift_zero, count_shift_succ]; omega
    · rw [count_shift_succ, count_shift_succ]; exact h v

theorem gordonGood_map_succ_iff (n : ℕ) {u : List ℕ} (hu : SortedWord u) :
    GordonGood n (u.map Nat.succ) ↔ GordonGood n u := by
  have := gordonGood_shift_iff n hu 0
  simp only [List.replicate_zero, List.append_nil, add_zero] at this
  rw [this]
  constructor
  · exact fun h => h.1
  · intro h
    refine ⟨h, ?_⟩
    have := (gordonGood_iff_freq n hu).mp h 0
    omega

/-- A sorted list with exactly `a` zeros is `μ.map succ ++ replicate a 0`. -/
theorem sorted_eq_shift {l : List ℕ} (hs : SortedWord l) :
    l = ((l.filter (· ≠ 0)).map Nat.pred).map Nat.succ ++ List.replicate (l.count 0) 0 := by
  have hmap : ((l.filter (· ≠ 0)).map Nat.pred).map Nat.succ = l.filter (· ≠ 0) := by
    rw [List.map_map]
    conv_rhs => rw [← List.map_id (l.filter (· ≠ 0))]
    apply List.map_congr_left
    intro x hx
    have := (List.mem_filter.mp hx).2
    simp only [ne_eq, decide_eq_true_eq] at this
    simp only [Function.comp_apply, id_eq]
    exact Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero this)
  rw [hmap]
  have hperm : l.Perm (l.filter (· ≠ 0) ++ List.replicate (l.count 0) 0) := by
    rw [List.perm_iff_count]
    intro x
    rw [List.count_append]
    by_cases hx : x = 0
    · subst hx
      have h1 : (l.filter (· ≠ 0)).count 0 = 0 :=
        List.count_eq_zero.mpr (fun h => by simp [List.mem_filter] at h)
      rw [h1, List.count_replicate_self, zero_add]
    · have h1 : (l.filter (· ≠ 0)).count x = l.count x := List.count_filter (by simpa using hx)
      have h2 : (List.replicate (l.count 0) 0).count x = 0 :=
        List.count_eq_zero.mpr (fun h => hx (List.eq_of_mem_replicate h))
      rw [h1, h2, add_zero]
  refine List.Perm.eq_of_pairwise (fun x y _ _ h1 h2 => le_antisymm h2 h1) hs ?_ hperm
  rw [List.pairwise_append]
  refine ⟨hs.sublist List.filter_sublist, ?_, ?_⟩
  · exact List.pairwise_replicate.mpr (Or.inr le_rfl)
  · intro x _ y hy
    rw [List.eq_of_mem_replicate hy]
    exact Nat.zero_le _

/-! ## §3  The counts `gC` and Andrews' recursion -/

/-- Sorted Gordon-good lists of length `m`, weight `Σ(e+1) = N`, fewer than `i` zeros. -/
def gordonList (n i m N : ℕ) : Finset (List ℕ) :=
  ((Finset.univ : Finset (Fin m → Fin (N + 1))).image tupleList).filter
    (fun l => SortedWord l ∧ GordonGood n l ∧ l.sum + l.length = N ∧ l.count 0 < i)

theorem mem_GL {n i m N : ℕ} {l : List ℕ} :
    l ∈ gordonList n i m N ↔ SortedWord l ∧ GordonGood n l ∧ l.sum + l.length = N ∧ l.count 0 < i ∧
      l.length = m := by
  simp only [gordonList, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨a, rfl⟩, hs, hg, hN, hc⟩
    exact ⟨hs, hg, hN, hc, by simp [tupleList]⟩
  · rintro ⟨hs, hg, hN, hc, hl⟩
    refine ⟨⟨fun j => ⟨l[j.val]'(by omega), ?_⟩, ?_⟩, hs, hg, hN, hc⟩
    · have hj : j.val < l.length := by omega
      have := List.le_sum_of_mem (List.getElem_mem hj)
      omega
    · apply List.ext_getElem (by simp [tupleList, hl])
      intro i h1 h2
      simp [tupleList]

/-- The Gordon count with at most `i - 1` parts equal to one. -/
def gC (n i m N : ℕ) : ℕ := (gordonList n i m N).card

theorem gC_zero (n m N : ℕ) : gC n 0 m N = 0 := by
  rw [gC, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro l hl
  have := (mem_GL.mp hl).2.2.2.1
  omega

theorem gC_zero_length (n i N : ℕ) (hi : 1 ≤ i) : gC n i 0 N = if N = 0 then 1 else 0 := by
  rw [gC]
  split_ifs with hN
  · subst hN
    rw [Finset.card_eq_one]
    refine ⟨[], ?_⟩
    ext l
    rw [mem_GL, Finset.mem_singleton]
    constructor
    · rintro ⟨-, -, -, -, hl⟩; exact List.eq_nil_of_length_eq_zero hl
    · rintro rfl
      refine ⟨sortedWord_nil, fun i hi => by simp at hi, by simp, by simp; omega, rfl⟩
  · rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro l hl
    obtain ⟨-, -, hs, -, hlen⟩ := mem_GL.mp hl
    rw [List.eq_nil_of_length_eq_zero hlen] at hs
    simp at hs; omega

/-- The shift map `μ ↦ μ.map succ ++ replicate a 0`. -/
def shiftList (a : ℕ) (μ : List ℕ) : List ℕ := μ.map Nat.succ ++ List.replicate a 0

theorem shiftList_injective (a : ℕ) : Function.Injective (shiftList a) := by
  intro μ ν h
  have h1 := congrArg (List.take μ.length) h
  unfold shiftList at h h1
  have hl : μ.length = ν.length := by
    have := congrArg List.length h
    simpa using this
  rw [List.take_left' (by simp), hl, List.take_left' (by simp)] at h1
  exact List.map_injective_iff.mpr Nat.succ_injective h1

theorem sum_shiftList (a : ℕ) (μ : List ℕ) :
    (shiftList a μ).sum = μ.sum + μ.length := by
  unfold shiftList
  rw [List.sum_append, List.sum_replicate, smul_zero, add_zero]
  induction μ with
  | nil => simp
  | cons x μ ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; omega

theorem length_shiftList (a : ℕ) (μ : List ℕ) : (shiftList a μ).length = μ.length + a := by
  simp [shiftList]

/-- **The lists with exactly `a` ones.** -/
theorem filter_count_eq_image (n a m N : ℕ) (ha : a ≤ n) (ham : a ≤ m) (hmN : m ≤ N) :
    (gordonList n (a + 1) m N).filter (fun l => l.count 0 = a) =
      (gordonList n (n + 1 - a) (m - a) (N - m)).image (shiftList a) := by
  ext l
  rw [Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨hl, hc⟩
    obtain ⟨hs, hg, hN, -, hlen⟩ := mem_GL.mp hl
    set μ := (l.filter (· ≠ 0)).map Nat.pred with hμ
    have heq : l = shiftList a μ := by
      rw [shiftList, ← hc]; exact sorted_eq_shift hs
    have hμs : SortedWord μ := by
      have h := hs
      rw [heq, shiftList] at h
      unfold SortedWord at h
      rw [List.pairwise_append, List.pairwise_map] at h
      exact h.1.imp fun hab => by simpa using hab
    rw [heq, shiftList] at hg
    obtain ⟨hgμ, hcμ⟩ := (gordonGood_shift_iff n hμs a).mp hg
    have hlenμ : μ.length + a = m := by rw [← hlen, heq, length_shiftList]
    have hsumμ : μ.sum + μ.length + μ.length + a = N := by
      rw [← hN, heq, sum_shiftList, length_shiftList]; ring
    refine ⟨μ, mem_GL.mpr ⟨hμs, hgμ, by omega, by omega, by omega⟩, heq.symm⟩
  · rintro ⟨μ, hμ, rfl⟩
    obtain ⟨hs, hg, hN, hc, hlen⟩ := mem_GL.mp hμ
    refine ⟨mem_GL.mpr ⟨sorted_shift hs a, (gordonGood_shift_iff n hs a).mpr ⟨hg, by omega⟩,
      ?_, ?_, ?_⟩, count_shift_zero μ a⟩
    · rw [sum_shiftList, length_shiftList]; omega
    · rw [shiftList, count_shift_zero]; omega
    · rw [length_shiftList]; omega

/-- **Andrews' recursion for the Gordon counts.** For `a ≤ n`,
`gC n (a+1) m N = gC n a m N + [a ≤ m ≤ N] gC n (n+1-a) (m-a) (N-m)`. -/
theorem gC_succ (n a m N : ℕ) (ha : a ≤ n) :
    gC n (a + 1) m N = gC n a m N +
      (if a ≤ m ∧ m ≤ N then gC n (n + 1 - a) (m - a) (N - m) else 0) := by
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := gordonList n (a + 1) m N) (fun l => l.count 0 = a)
  have hneg : (gordonList n (a + 1) m N).filter (fun l => ¬ l.count 0 = a) = gordonList n a m N := by
    ext l
    rw [Finset.mem_filter, mem_GL, mem_GL]
    constructor
    · rintro ⟨⟨h1, h2, h3, h4, h5⟩, h6⟩; exact ⟨h1, h2, h3, by omega, h5⟩
    · rintro ⟨h1, h2, h3, h4, h5⟩; exact ⟨⟨h1, h2, h3, by omega, h5⟩, by omega⟩
  rw [hneg] at hsplit
  unfold gC
  rw [← hsplit, add_comm]
  congr 1
  split_ifs with h
  · rw [filter_count_eq_image n a m N ha h.1 h.2,
      Finset.card_image_of_injective _ (shiftList_injective a)]
  · rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro l hl
    rw [Finset.mem_filter, mem_GL] at hl
    obtain ⟨⟨-, -, hN, -, hlen⟩, hc⟩ := hl
    apply h
    have h1 := List.count_le_length (a := 0) (l := l)
    exact ⟨by omega, by omega⟩

/-! ## §4  The Andrews–Gordon coefficient is the count with no ones -/

theorem gordonCoeff_eq_gC (n N r : ℕ) : gordonCoeff n (N : ℤ) r = gC n 1 r N := by
  rw [gordonCoeff_natCast, gC]
  refine Finset.card_bij (fun u _ => u.map Nat.succ) ?_ ?_ ?_
  · intro u hu
    obtain ⟨hs, hg, hE, hl⟩ := mem_gordonWords.mp hu
    refine mem_GL.mpr ⟨sorted_map_succ hs, (gordonGood_map_succ_iff n hs).mpr hg, ?_, ?_, ?_⟩
    · have := sum_shiftList 0 u
      simp only [shiftList, List.replicate_zero, List.append_nil] at this
      rw [this, List.length_map, ← hE, energyVir_eq_sum]; ring
    · rw [count_map_succ_zero]; omega
    · rw [List.length_map, hl]
  · intro u _ v _ h
    exact List.map_injective_iff.mpr Nat.succ_injective h
  · intro l hl
    obtain ⟨hs, hg, hN, hc, hlen⟩ := mem_GL.mp hl
    have hc0 : l.count 0 = 0 := by omega
    have heq := sorted_eq_shift hs
    rw [hc0, List.replicate_zero, List.append_nil] at heq
    set u := (l.filter (· ≠ 0)).map Nat.pred with hu
    clear_value u
    have hus : SortedWord u := by
      have h := hs
      rw [heq] at h
      unfold SortedWord at h ⊢
      rw [List.pairwise_map] at h
      exact h.imp fun hab => by simpa using hab
    refine ⟨u, mem_gordonWords.mpr ⟨hus, ?_, ?_, ?_⟩, heq.symm⟩
    · rw [← gordonGood_map_succ_iff n hus, ← heq]; exact hg
    · have := sum_shiftList 0 u
      simp only [shiftList, List.replicate_zero, List.append_nil] at this
      rw [energyVir_eq_sum, ← hN, heq, this, List.length_map]; ring
    · rw [← hlen, heq, List.length_map]

end VOA.TwoSeriesCharacter
