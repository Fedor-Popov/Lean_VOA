/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.GNSortingLink1
import VOA.Modularity.GNLink2Representatives
import VOA.Modularity.GNLink3Migration

/-!
# Gaberdiel--Neitzke Prop. 8, Link 4: the repeated-head output

This file packages the bookkeeping needed after `gnWord_repeatedHead`.  At repetition level
`n = N + 1`, its right hand side consists of three pieces.

* The composite term has mode index `2n - 1`.  For `N > 0` this is strictly above `n`.
* In the first finsum, the omitted term is exactly `i = N`.  If the inner mode is negative,
  the two positive mode indices are `i + 1` and `2n - 1 - i`; one of them is strictly above
  `n`.  Sorting exposes it at the head, modulo grade `G - 1`.  If the inner mode is
  nonnegative, the whole summand is already in grade `G - 1`.
* Every term of the second finsum is in grade `G - 1`, because its inner mode is nonnegative.

Both an ordinary-span API and the induction-safe `gnSpanBounded` API are recorded.  In the
bounded route, a completely unsorted admissible positive-weight word containing an index above
`n` is sorted, its exposed head is replaced by generator representatives, and every lower-grade
error is absorbed by the outer induction.  This is crucial because bare `gnSpan` forgets witness
grades and therefore cannot serve as the induction invariant.

For `N > 0` the file closes the bounded successor step by composing directly with Link 3, without
assuming that its migrated repeated-head word is ordered.  The case `N = 0` is not hidden: then
`2(N+1)-1 = N+1 = 1`, so the composite is not a high-mode term and the all-mode-`1` branch needs
the separate strong length/count induction.  Its two finsum families are lower-grade, as
recorded below.
-/

namespace VOA

open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## Small list and `finsum` bricks -/

/-- A weakly decreasing nonempty word which contains an index above `n` has head index above
`n`. -/
theorem gnLink4_head_idx_gt_of_weakDec {n : ℕ} {l : List (GNLetter 𝒱)}
    (hwd : GNWeakDec l) (hhi : ∃ p ∈ l, n < p.2.2) :
    ∃ p : GNLetter 𝒱, ∃ tail : List (GNLetter 𝒱), l = p :: tail ∧ n < p.2.2 := by
  rcases hhi with ⟨q, hq, hqn⟩
  cases l with
  | nil => simp at hq
  | cons p tail =>
      refine ⟨p, tail, rfl, ?_⟩
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hqn
      · have hpq := (List.pairwise_cons.mp hwd).1 q hq
        omega

/-- Membership in a submodule passes to a `finsum` once its actual support is known to be
finite.  Link 4 uses the concrete truncation support supplied by Lemma 7 rather than relying on
the infinite-support fallback in the definition of `finsum`. -/
theorem gnLink4_finsum_mem_of_support_finite {ι : Type*} (p : Submodule ℂ 𝒱) (F : ι → 𝒱)
    (hfin : (Function.support F).Finite) (hF : ∀ i, F i ∈ p) : (∑ᶠ i, F i) ∈ p := by
  classical
  rw [finsum_eq_finsetSum_of_support_subset F (s := hfin.toFinset)
    (fun i hi => hfin.mem_toFinset.mpr hi)]
  exact Submodule.sum_mem _ (fun i _ => hF i)

/-- The masked first family in `gnWord_repeatedHead` has finite support. -/
theorem gnLink4_familyA_support_finite (W : VertexOperatorAlgebra 𝒱) (a b x : 𝒱) (N : ℕ) :
    (Function.support (fun i : ℕ => if i = N then 0
      else W.smul a (-1 - (i : ℤ))
        (W.smul b (-2 * ((N + 1 : ℕ) : ℤ) + 1 + (i : ℤ)) x))).Finite := by
  classical
  refine (gn7_supportA_finite W a b x (-2 * ((N + 1 : ℕ) : ℤ) + 1)).subset ?_
  intro i hi
  rw [Function.mem_support] at hi ⊢
  by_cases hiN : i = N
  · simp [hiN] at hi
  · simpa [hiN] using hi

/-- The second family in `gnWord_repeatedHead` has finite support. -/
theorem gnLink4_familyB_support_finite (W : VertexOperatorAlgebra 𝒱) (a b x : 𝒱) (N : ℕ) :
    (Function.support (fun i : ℕ =>
      W.smul b (-2 * ((N + 1 : ℕ) : ℤ) - (i : ℤ))
        (W.smul a (i : ℤ) x))).Finite := by
  simpa using gn7_supportB_finite W a b x (-2 * ((N + 1 : ℕ) : ℤ))

/-! ## The repeated-index count carried by the three shapes -/

/-- The exact repeated-head input contributes two occurrences at its displayed mode index. -/
theorem gnLink4_repeatedHead_count (n : ℕ) (a b : 𝒱) (wa wb : ℕ)
    (rest : List (GNLetter 𝒱)) :
    gnCountAt n ((a, wa, n) :: (b, wb, n) :: rest) = gnCountAt n rest + 2 := by
  classical
  simp only [gnCountAt]
  rw [List.filter_cons_of_pos (by simp), List.filter_cons_of_pos (by simp)]
  simp only [List.length_cons]

/-- Above target level `1`, the composite letter contributes no new occurrence at `N+1`; the
two repeated head occurrences have both disappeared. -/
theorem gnLink4_composite_count (N : ℕ) (hN : 1 ≤ N) (c : 𝒱) (wc : ℕ)
    (rest : List (GNLetter 𝒱)) :
    gnCountAt (N + 1) ((c, wc, 2 * (N + 1) - 1) :: rest) =
      gnCountAt (N + 1) rest := by
  classical
  have hne : 2 * (N + 1) - 1 ≠ N + 1 := by omega
  simp [gnCountAt, hne]

/-- A negative-inner, non-omitted first-family term contributes no occurrence at `N+1`.
The omitted value `i=N` is exactly the unique value at which either displayed index could be
`N+1`. -/
theorem gnLink4_familyA_negative_count (N i : ℕ) (hiN : i ≠ N) (hi : i ≤ 2 * N)
    (a b : 𝒱) (wa wb : ℕ) (rest : List (GNLetter 𝒱)) :
    gnCountAt (N + 1)
        ((a, wa, i + 1) :: (b, wb, 2 * N + 1 - i) :: rest) =
      gnCountAt (N + 1) rest := by
  classical
  have houter : i + 1 ≠ N + 1 := by omega
  have hinner : 2 * N + 1 - i ≠ N + 1 := by omega
  simp only [gnCountAt]
  rw [List.filter_cons_of_neg (by simpa using houter),
    List.filter_cons_of_neg (by simpa using hinner)]

/-! ## The grade-bounded target needed by the outer induction -/

/-- `GNNoRepeatLE` is invariant under permutation because its pair relation is symmetric. -/
theorem gnLink4_noRepeat_of_perm {N : ℕ} {l l' : List (GNLetter 𝒱)}
    (hperm : l.Perm l') (hnr : GNNoRepeatLE N l) : GNNoRepeatLE N l' := by
  unfold GNNoRepeatLE at hnr ⊢
  exact (hperm.pairwise_iff (by
    intro p q hpq hq hp
    exact (hpq hp hq).symm)).mp hnr

/-- `OverGens` is invariant under permutation. -/
theorem gnLink4_overGens_of_perm {g : ℕ} {gen : Fin g → 𝒱} {wt : Fin g → ℕ}
    {l l' : List (GNLetter 𝒱)} (hperm : l.Perm l') (hgens : OverGens gen wt l) :
    OverGens gen wt l' :=
  fun p hp => hgens p (hperm.mem_iff.mpr hp)

/-- Prepending a generator at an index above `N` to a grade-bounded target combination returns
to `gnSpan ... N`.  A basis word may need sorting after the prepend; the sorting error is in
`gnGradeFil (G-1)`, while the sorted permutation preserves generators and no-repeats. -/
theorem gnLink4_prepend_high_gen_bounded_mem_span (W : VertexOperatorAlgebra 𝒱)
    {g : ℕ} {gen : Fin g → 𝒱} {wt : Fin g → ℕ}
    (hgen : ∀ i, gen i ∈ W.grading (wt i : ℤ))
    (hgenPos : ∀ i, 1 ≤ wt i) (i : Fin g) {N k H G : ℕ}
    (hk : N < k) (hgrade : wt i + H ≤ G)
    (hlower : gnGradeFil W (G - 1) ≤ gnSpan W gen wt N) {x : 𝒱}
    (hx : x ∈ gnSpanBounded W gen wt H N) :
    W.smul (gen i) (-(k : ℤ)) x ∈ gnSpan W gen wt N := by
  classical
  refine Submodule.span_induction
    (p := fun x _ => W.smul (gen i) (-(k : ℤ)) x ∈ gnSpan W gen wt N) ?_ ?_ ?_ ?_ hx
  · rintro y ⟨l, hlOK, hlGrade, hlWD, hlNR, hlGens, rfl⟩
    let p : GNLetter 𝒱 := (gen i, wt i, k)
    let raw : List (GNLetter 𝒱) := p :: l
    have hrawOK : GNWordOK W raw := by
      refine ⟨?_, ?_⟩
      · intro q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · exact hgen i
        · exact hlOK.1 q hq
      · intro q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · dsimp [p]
          omega
        · exact hlOK.2 q hq
    have hrawWt : ∀ q ∈ raw, 1 ≤ q.2.1 := by
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hgenPos i
      · obtain ⟨j, -, hjwt⟩ := hlGens q hq
        rw [hjwt]
        exact hgenPos j
    have hrawNR : GNNoRepeatLE N raw := by
      apply List.pairwise_cons.mpr
      refine ⟨?_, hlNR⟩
      intro q hq hkle _
      exact absurd hkle (by dsimp [p]; omega)
    have hrawGens : OverGens gen wt raw := by
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact ⟨i, rfl, rfl⟩
      · exact hlGens q hq
    have hrawGrade : gnWordGrade raw ≤ G := by
      simp only [raw, p, gnWordGrade_cons]
      omega
    obtain ⟨sorted, hperm, hsortedWD⟩ := exists_weakDec_perm raw
    have hsortedOK := gnWordOK_of_perm W hperm hrawOK
    have hsortedNR := gnLink4_noRepeat_of_perm hperm hrawNR
    have hsortedGens := gnLink4_overGens_of_perm hperm hrawGens
    have hsortedMem : gnWord W sorted W.vacuum ∈ gnSpan W gen wt N :=
      Submodule.subset_span ⟨sorted, hsortedOK, hsortedWD, hsortedNR, hsortedGens, rfl⟩
    have herr := gnWord_perm_sub_mem_grade W hperm hrawOK hrawWt
    have herrMem : gnWord W raw W.vacuum - gnWord W sorted W.vacuum ∈
        gnSpan W gen wt N := by
      apply hlower
      apply gnGradeFil_mono W (show gnWordGrade raw - 1 ≤ G - 1 by omega)
      exact herr
    have hadd := (gnSpan W gen wt N).add_mem herrMem hsortedMem
    change gnWord W raw W.vacuum ∈ gnSpan W gen wt N
    convert hadd using 1 <;> abel
  · change W.smul (gen i) (-(k : ℤ)) 0 ∈ gnSpan W gen wt N
    rw [W.smul_zero_right]
    exact Submodule.zero_mem _
  · intro y z _ _ hy hz
    rw [W.smul_add_right]
    exact Submodule.add_mem _ hy hz
  · intro c y _ hy
    rw [W.smul_smul_right]
    exact Submodule.smul_mem _ _ hy

/-- A sorted high-head word is in the target span from a genuinely grade-bounded outer
induction hypothesis.  This is the concrete interface consumed by the three Lemma 7 families.
It does not follow from bare `GNReach`, because bare `gnSpan` forgets witness grades. -/
theorem gnLink4_highHead_mem_span_of_bounded_outer (W : VertexOperatorAlgebra 𝒱)
    {g : ℕ} {gen : Fin g → 𝒱} {wt : Fin g → ℕ}
    (hgen : ∀ i, gen i ∈ W.grading (wt i : ℤ))
    (hgenPos : ∀ i, 1 ≤ wt i)
    (hdec : (⊤ : Submodule ℂ 𝒱) =
      Submodule.span ℂ (Set.range gen ∪ {W.vacuum}) ⊔ O₂ W)
    {N G : ℕ} (houter : ∀ H < G, GNReachBounded W gen wt H N)
    (hlower : gnGradeFil W (G - 1) ≤ gnSpan W gen wt N)
    (p : GNLetter 𝒱) (tail : List (GNLetter 𝒱))
    (hOK : GNWordOK W (p :: tail)) (_hwd : GNWeakDec (p :: tail))
    (hpidx : N < p.2.2) (hwtPos : ∀ q ∈ p :: tail, 1 ≤ q.2.1)
    (hgrade : gnWordGrade (p :: tail) ≤ G) :
    gnWord W (p :: tail) W.vacuum ∈ gnSpan W gen wt N := by
  classical
  have hpwt : 1 ≤ p.2.1 := hwtPos p (List.mem_cons_self ..)
  have htailLt : gnWordGrade tail < G := by
    rw [gnWordGrade_cons] at hgrade
    omega
  have htailFil : gnWord W tail W.vacuum ∈ gnGradeFil W (gnWordGrade tail) :=
    word_mem_gnGradeFil W hOK.tail (le_refl _)
  have htailBound := houter (gnWordGrade tail) htailLt htailFil
  have hpdec := gnLink2_homog_mem_repSpan_sup_O₂ W gen wt hgen hdec hOK.head_mem
  rw [Submodule.mem_sup] at hpdec
  obtain ⟨a, ha, b, hb, hab⟩ := hpdec
  rw [gnWord_cons, ← hab, W.smul_add_left]
  refine (gnSpan W gen wt N).add_mem ?_ ?_
  · refine Submodule.span_induction
      (p := fun a _ => W.smul a (-(p.2.2 : ℤ)) (gnWord W tail W.vacuum) ∈
        gnSpan W gen wt N) ?_ ?_ ?_ ?_ ha
    · intro y hy
      rcases hy with ⟨i, hiwt, rfl⟩ | ⟨hpzero, rfl⟩
      · apply gnLink4_prepend_high_gen_bounded_mem_span W hgen hgenPos i hpidx
          (H := gnWordGrade tail) (G := G) ?_ hlower htailBound
        rw [hiwt]
        simpa only [gnWordGrade_cons] using hgrade
      · exact absurd hpzero (by omega)
    · change W.smul 0 (-(p.2.2 : ℤ)) (gnWord W tail W.vacuum) ∈
        gnSpan W gen wt N
      rw [W.smul_zero_left]
      exact Submodule.zero_mem _
    · intro y z _ _ hy hz
      rw [W.smul_add_left]
      exact (gnSpan W gen wt N).add_mem hy hz
    · intro c y _ hy
      rw [W.smul_smul_left]
      exact (gnSpan W gen wt N).smul_mem c hy
  · have hgrade' : p.2.1 + gnWordGrade tail ≤ G := by
      simpa only [gnWordGrade_cons] using hgrade
    apply hlower
    apply gnGradeFil_mono W (show p.2.1 + gnWordGrade tail - 1 ≤ G - 1 by omega)
    exact gnLink2_O₂_word_mem W hb.1 hb.2 (by omega) hOK.tail

/-- Bounded-target version of `gnLink4_prepend_high_gen_bounded_mem_span`.  In addition to
sorting the prepended generator, this retains the common outer grade bound `G` on every target
witness. -/
theorem gnLink4_prepend_high_gen_bounded_mem_spanBounded (W : VertexOperatorAlgebra 𝒱)
    {g : ℕ} {gen : Fin g → 𝒱} {wt : Fin g → ℕ}
    (hgen : ∀ i, gen i ∈ W.grading (wt i : ℤ))
    (hgenPos : ∀ i, 1 ≤ wt i) (i : Fin g) {N k H G : ℕ}
    (hk : N < k) (hgrade : wt i + H ≤ G)
    (hlower : gnGradeFil W (G - 1) ≤ gnSpanBounded W gen wt G N) {x : 𝒱}
    (hx : x ∈ gnSpanBounded W gen wt H N) :
    W.smul (gen i) (-(k : ℤ)) x ∈ gnSpanBounded W gen wt G N := by
  classical
  refine Submodule.span_induction
    (p := fun x _ => W.smul (gen i) (-(k : ℤ)) x ∈ gnSpanBounded W gen wt G N)
      ?_ ?_ ?_ ?_ hx
  · rintro y ⟨l, hlOK, hlGrade, hlWD, hlNR, hlGens, rfl⟩
    let p : GNLetter 𝒱 := (gen i, wt i, k)
    let raw : List (GNLetter 𝒱) := p :: l
    have hrawOK : GNWordOK W raw := by
      refine ⟨?_, ?_⟩
      · intro q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · exact hgen i
        · exact hlOK.1 q hq
      · intro q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · dsimp [p]
          omega
        · exact hlOK.2 q hq
    have hrawWt : ∀ q ∈ raw, 1 ≤ q.2.1 := by
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hgenPos i
      · obtain ⟨j, -, hjwt⟩ := hlGens q hq
        rw [hjwt]
        exact hgenPos j
    have hrawNR : GNNoRepeatLE N raw := by
      apply List.pairwise_cons.mpr
      refine ⟨?_, hlNR⟩
      intro q hq hkle _
      exact absurd hkle (by dsimp [p]; omega)
    have hrawGens : OverGens gen wt raw := by
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact ⟨i, rfl, rfl⟩
      · exact hlGens q hq
    have hrawGrade : gnWordGrade raw ≤ G := by
      simp only [raw, p, gnWordGrade_cons]
      omega
    obtain ⟨sorted, hperm, hsortedWD⟩ := exists_weakDec_perm raw
    have hsortedOK := gnWordOK_of_perm W hperm hrawOK
    have hsortedGrade : gnWordGrade sorted ≤ G := by
      rw [← gnWordGrade_eq_of_perm hperm]
      exact hrawGrade
    have hsortedNR := gnLink4_noRepeat_of_perm hperm hrawNR
    have hsortedGens := gnLink4_overGens_of_perm hperm hrawGens
    have hsortedMem : gnWord W sorted W.vacuum ∈ gnSpanBounded W gen wt G N :=
      Submodule.subset_span
        ⟨sorted, hsortedOK, hsortedGrade, hsortedWD, hsortedNR, hsortedGens, rfl⟩
    have herr := gnWord_perm_sub_mem_grade W hperm hrawOK hrawWt
    have herrMem : gnWord W raw W.vacuum - gnWord W sorted W.vacuum ∈
        gnSpanBounded W gen wt G N := by
      apply hlower
      apply gnGradeFil_mono W (show gnWordGrade raw - 1 ≤ G - 1 by omega)
      exact herr
    have hadd := (gnSpanBounded W gen wt G N).add_mem herrMem hsortedMem
    change gnWord W raw W.vacuum ∈ gnSpanBounded W gen wt G N
    convert hadd using 1 <;> abel
  · change W.smul (gen i) (-(k : ℤ)) 0 ∈ gnSpanBounded W gen wt G N
    rw [W.smul_zero_right]
    exact Submodule.zero_mem _
  · intro y z _ _ hy hz
    rw [W.smul_add_right]
    exact Submodule.add_mem _ hy hz
  · intro c y _ hy
    rw [W.smul_smul_right]
    exact Submodule.smul_mem _ _ hy

/-- A positive admissible word with an index above `N` belongs to the bounded target after it
has been sorted.  Representative replacement is applied only to its head; the tail is handled
at its strictly smaller grade, and the final prepend/sort retains the outer bound `G`.

The weak-decrease proof is intentionally not an input here: callers may sort first (as the
first family does), while the composite family starts from an unsorted migrated tail. -/
theorem gnLink4_highHead_mem_bounded_of_outer (W : VertexOperatorAlgebra 𝒱)
    {g : ℕ} {gen : Fin g → 𝒱} {wt : Fin g → ℕ}
    (hgen : ∀ i, gen i ∈ W.grading (wt i : ℤ))
    (hgenPos : ∀ i, 1 ≤ wt i)
    (hdec : (⊤ : Submodule ℂ 𝒱) =
      Submodule.span ℂ (Set.range gen ∪ {W.vacuum}) ⊔ O₂ W)
    {N G : ℕ} (houter : ∀ H < G, GNReachBounded W gen wt H N)
    (hlower : gnGradeFil W (G - 1) ≤ gnSpanBounded W gen wt G N)
    (p : GNLetter 𝒱) (tail : List (GNLetter 𝒱))
    (hOK : GNWordOK W (p :: tail)) (hpidx : N < p.2.2)
    (hwtPos : ∀ q ∈ p :: tail, 1 ≤ q.2.1)
    (hgrade : gnWordGrade (p :: tail) ≤ G) :
    gnWord W (p :: tail) W.vacuum ∈ gnSpanBounded W gen wt G N := by
  classical
  have hpwt : 1 ≤ p.2.1 := hwtPos p (List.mem_cons_self ..)
  have htailLt : gnWordGrade tail < G := by
    rw [gnWordGrade_cons] at hgrade
    omega
  have htailFil : gnWord W tail W.vacuum ∈ gnGradeFil W (gnWordGrade tail) :=
    word_mem_gnGradeFil W hOK.tail (le_refl _)
  have htailBound := houter (gnWordGrade tail) htailLt htailFil
  have hpdec := gnLink2_homog_mem_repSpan_sup_O₂ W gen wt hgen hdec hOK.head_mem
  rw [Submodule.mem_sup] at hpdec
  obtain ⟨a, ha, b, hb, hab⟩ := hpdec
  rw [gnWord_cons, ← hab, W.smul_add_left]
  refine (gnSpanBounded W gen wt G N).add_mem ?_ ?_
  · refine Submodule.span_induction
      (p := fun a _ => W.smul a (-(p.2.2 : ℤ)) (gnWord W tail W.vacuum) ∈
        gnSpanBounded W gen wt G N) ?_ ?_ ?_ ?_ ha
    · intro y hy
      rcases hy with ⟨i, hiwt, rfl⟩ | ⟨hpzero, rfl⟩
      · apply gnLink4_prepend_high_gen_bounded_mem_spanBounded W hgen hgenPos i hpidx
          (H := gnWordGrade tail) (G := G) ?_ hlower htailBound
        rw [hiwt]
        simpa only [gnWordGrade_cons] using hgrade
      · exact absurd hpzero (by omega)
    · change W.smul 0 (-(p.2.2 : ℤ)) (gnWord W tail W.vacuum) ∈
          gnSpanBounded W gen wt G N
      rw [W.smul_zero_left]
      exact Submodule.zero_mem _
    · intro y z _ _ hy hz
      rw [W.smul_add_left]
      exact (gnSpanBounded W gen wt G N).add_mem hy hz
    · intro c y _ hy
      rw [W.smul_smul_left]
      exact (gnSpanBounded W gen wt G N).smul_mem c hy
  · have hgrade' : p.2.1 + gnWordGrade tail ≤ G := by
      simpa only [gnWordGrade_cons] using hgrade
    apply hlower
    apply gnGradeFil_mono W (show p.2.1 + gnWordGrade tail - 1 ≤ G - 1 by omega)
    exact gnLink2_O₂_word_mem W hb.1 hb.2 (by omega) hOK.tail

/-- Sorting wrapper for the bounded high-head lemma.  It is phrased for an arbitrary admissible
word containing a high mode, which is the form shared by the composite term and the negative
branch of the first family. -/
theorem gnLink4_word_mem_bounded_of_contains_high (W : VertexOperatorAlgebra 𝒱)
    {g : ℕ} {gen : Fin g → 𝒱} {wt : Fin g → ℕ}
    (hgen : ∀ i, gen i ∈ W.grading (wt i : ℤ))
    (hgenPos : ∀ i, 1 ≤ wt i)
    (hdec : (⊤ : Submodule ℂ 𝒱) =
      Submodule.span ℂ (Set.range gen ∪ {W.vacuum}) ⊔ O₂ W)
    {N G : ℕ} (houter : ∀ H < G, GNReachBounded W gen wt H N)
    (hlower : gnGradeFil W (G - 1) ≤ gnSpanBounded W gen wt G N)
    (l : List (GNLetter 𝒱)) (hOK : GNWordOK W l)
    (hwtPos : ∀ q ∈ l, 1 ≤ q.2.1) (hgrade : gnWordGrade l ≤ G)
    (hhi : ∃ q ∈ l, N < q.2.2) :
    gnWord W l W.vacuum ∈ gnSpanBounded W gen wt G N := by
  classical
  obtain ⟨sorted, hperm, hwd⟩ := exists_weakDec_perm l
  have hsortedOK := gnWordOK_of_perm W hperm hOK
  have hsortedWt : ∀ q ∈ sorted, 1 ≤ q.2.1 :=
    fun q hq => hwtPos q (hperm.mem_iff.mpr hq)
  have hsortedHi : ∃ q ∈ sorted, N < q.2.2 := by
    obtain ⟨q, hq, hqidx⟩ := hhi
    exact ⟨q, hperm.mem_iff.mp hq, hqidx⟩
  obtain ⟨p, tail, rfl, hpidx⟩ := gnLink4_head_idx_gt_of_weakDec hwd hsortedHi
  have hsortedGrade : gnWordGrade (p :: tail) ≤ G := by
    rw [← gnWordGrade_eq_of_perm hperm]
    exact hgrade
  have hmain := gnLink4_highHead_mem_bounded_of_outer W hgen hgenPos hdec houter hlower
    p tail hsortedOK hpidx hsortedWt hsortedGrade
  have herr := gnWord_perm_sub_mem_grade W hperm hOK hwtPos
  have herrMem : gnWord W l W.vacuum - gnWord W (p :: tail) W.vacuum ∈
      gnSpanBounded W gen wt G N := by
    apply hlower
    apply gnGradeFil_mono W (show gnWordGrade l - 1 ≤ G - 1 by omega)
    exact herr
  have hadd := (gnSpanBounded W gen wt G N).add_mem herrMem hmain
  convert hadd using 1 <;> abel

/-! ## Grade-drop families -/

/-- Every term of Lemma 7's second family is one lower GN grade. -/
theorem gnLink4_familyB_term_mem_lower (W : VertexOperatorAlgebra 𝒱)
    {a b : 𝒱} {wa wb N G : ℕ} (ha : a ∈ W.grading (wa : ℤ))
    (hb : b ∈ W.grading (wb : ℤ)) (hwa : 1 ≤ wa) (hwb : 1 ≤ wb)
    {rest : List (GNLetter 𝒱)} (hrestOK : GNWordOK W rest)
    (hgrade : wa + wb + gnWordGrade rest ≤ G) (i : ℕ) :
    W.smul b (-2 * ((N + 1 : ℕ) : ℤ) - (i : ℤ))
        (W.smul a (i : ℤ) (gnWord W rest W.vacuum)) ∈ gnGradeFil W (G - 1) := by
  have hinner := gnLink2_nonneg_mode_word_mem W rest hrestOK a wa ha i
  have houter := gnLink2_prepend_mem W hb (by omega : 1 ≤ 2 * (N + 1) + i) hinner
  have hidx : -2 * ((N + 1 : ℕ) : ℤ) - (i : ℤ) =
      -((2 * (N + 1) + i : ℕ) : ℤ) := by
    push_cast
    ring
  rw [hidx]
  exact gnGradeFil_mono W (by omega) houter

/-- Lemma 7's whole second family lies in the target span as soon as the outer grade induction
puts `gnGradeFil (G-1)` there. -/
theorem gnLink4_familyB_mem_span (W : VertexOperatorAlgebra 𝒱)
    {g : ℕ} {gen : Fin g → 𝒱} {wt : Fin g → ℕ}
    {a b : 𝒱} {wa wb N G : ℕ} (ha : a ∈ W.grading (wa : ℤ))
    (hb : b ∈ W.grading (wb : ℤ)) (hwa : 1 ≤ wa) (hwb : 1 ≤ wb)
    {rest : List (GNLetter 𝒱)} (hrestOK : GNWordOK W rest)
    (hgrade : wa + wb + gnWordGrade rest ≤ G)
    (hlower : gnGradeFil W (G - 1) ≤ gnSpan W gen wt (N + 1)) :
    (∑ᶠ i : ℕ, W.smul b (-2 * ((N + 1 : ℕ) : ℤ) - (i : ℤ))
      (W.smul a (i : ℤ) (gnWord W rest W.vacuum))) ∈ gnSpan W gen wt (N + 1) := by
  apply gnLink4_finsum_mem_of_support_finite _ _
    (gnLink4_familyB_support_finite W a b (gnWord W rest W.vacuum) N)
  intro i
  exact hlower (gnLink4_familyB_term_mem_lower W ha hb hwa hwb hrestOK hgrade i)

/-! ## The first family: lower grade or a sortable high mode -/

/-- A non-omitted term in the first Lemma 7 family lies in the target span.  In its negative-inner
branch, sorting preserves the two indices and exposes the one strictly above `N+1`; the sorting
error is one lower grade.  In its nonnegative-inner branch, the term itself is one lower grade. -/
theorem gnLink4_familyA_term_mem_span (W : VertexOperatorAlgebra 𝒱)
    {g : ℕ} {gen : Fin g → 𝒱} {wt : Fin g → ℕ}
    {a b : 𝒱} {wa wb N G : ℕ} (ha : a ∈ W.grading (wa : ℤ))
    (hb : b ∈ W.grading (wb : ℤ)) (hwa : 1 ≤ wa) (hwb : 1 ≤ wb)
    {rest : List (GNLetter 𝒱)} (hrestOK : GNWordOK W rest)
    (hrestWt : ∀ p ∈ rest, 1 ≤ p.2.1)
    (hgrade : wa + wb + gnWordGrade rest ≤ G)
    (hlower : gnGradeFil W (G - 1) ≤ gnSpan W gen wt (N + 1))
    (hhigh : ∀ (p : GNLetter 𝒱) (tail : List (GNLetter 𝒱)),
      GNWordOK W (p :: tail) → GNWeakDec (p :: tail) → N + 1 < p.2.2 →
      (∀ q ∈ p :: tail, 1 ≤ q.2.1) → gnWordGrade (p :: tail) ≤ G →
      gnWord W (p :: tail) W.vacuum ∈ gnSpan W gen wt (N + 1))
    (i : ℕ) :
    (if i = N then 0 else W.smul a (-1 - (i : ℤ))
      (W.smul b (-2 * ((N + 1 : ℕ) : ℤ) + 1 + (i : ℤ))
        (gnWord W rest W.vacuum))) ∈ gnSpan W gen wt (N + 1) := by
  classical
  by_cases hiN : i = N
  · simp [hiN]
  · rw [if_neg hiN]
    by_cases hneg : -2 * ((N + 1 : ℕ) : ℤ) + 1 + (i : ℤ) < 0
    · have hiBound : i ≤ 2 * N := by omega
      let k : ℕ := 2 * N + 1 - i
      have hkpos : 1 ≤ k := by dsimp [k]; omega
      have hinner : -2 * ((N + 1 : ℕ) : ℤ) + 1 + (i : ℤ) = -(k : ℤ) := by
        have hkcast : (k : ℤ) = 2 * (N : ℤ) + 1 - (i : ℤ) := by
          dsimp [k]
          rw [Nat.cast_sub (by omega : i ≤ 2 * N + 1)]
          push_cast
          ring
        rw [hkcast]
        push_cast
        ring
      let l : List (GNLetter 𝒱) := (a, wa, i + 1) :: (b, wb, k) :: rest
      have hlOK : GNWordOK W l := by
        refine ⟨?_, ?_⟩
        · intro p hp
          rcases List.mem_cons.mp hp with rfl | hp
          · exact ha
          · rcases List.mem_cons.mp hp with rfl | hp
            · exact hb
            · exact hrestOK.1 p hp
        · intro p hp
          rcases List.mem_cons.mp hp with rfl | hp
          · change 1 ≤ i + 1
            omega
          · rcases List.mem_cons.mp hp with rfl | hp
            · exact hkpos
            · exact hrestOK.2 p hp
      have hlWt : ∀ p ∈ l, 1 ≤ p.2.1 := by
        intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact hwa
        · rcases List.mem_cons.mp hp with rfl | hp
          · exact hwb
          · exact hrestWt p hp
      have hlGrade : gnWordGrade l = wa + wb + gnWordGrade rest := by
        simp only [l, gnWordGrade_cons]
        omega
      have hlHigh : ∃ p ∈ l, N + 1 < p.2.2 := by
        by_cases hiLt : i < N
        · refine ⟨(b, wb, k), by simp [l], ?_⟩
          dsimp [k]
          omega
        · refine ⟨(a, wa, i + 1), by simp [l], ?_⟩
          change N + 1 < i + 1
          omega
      obtain ⟨l', hperm, hwd⟩ := exists_weakDec_perm l
      have hlOK' := gnWordOK_of_perm W hperm hlOK
      have hlWt' : ∀ p ∈ l', 1 ≤ p.2.1 :=
        fun p hp => hlWt p (hperm.mem_iff.mpr hp)
      have hlHigh' : ∃ p ∈ l', N + 1 < p.2.2 := by
        obtain ⟨p, hp, hpidx⟩ := hlHigh
        exact ⟨p, hperm.mem_iff.mp hp, hpidx⟩
      obtain ⟨p, tail, rfl, hpidx⟩ := gnLink4_head_idx_gt_of_weakDec hwd hlHigh'
      have hgrade' : gnWordGrade (p :: tail) ≤ G := by
        rw [← gnWordGrade_eq_of_perm hperm, hlGrade]
        exact hgrade
      have hsorted := hhigh p tail hlOK' hwd hpidx hlWt' hgrade'
      have herr := gnWord_perm_sub_mem_grade W hperm hlOK hlWt
      have herr' : gnWord W l W.vacuum - gnWord W (p :: tail) W.vacuum ∈
          gnSpan W gen wt (N + 1) := by
        apply hlower
        apply gnGradeFil_mono W (show gnWordGrade l - 1 ≤ G - 1 by omega)
        exact herr
      have hadd := (gnSpan W gen wt (N + 1)).add_mem herr' hsorted
      have hword : W.smul a (-1 - (i : ℤ))
          (W.smul b (-2 * ((N + 1 : ℕ) : ℤ) + 1 + (i : ℤ))
            (gnWord W rest W.vacuum)) = gnWord W l W.vacuum := by
        rw [show -1 - (i : ℤ) = -((i + 1 : ℕ) : ℤ) by push_cast; ring, hinner]
        rfl
      rw [hword]
      convert hadd using 1 <;> abel
    · have hnonneg : 0 ≤ -2 * ((N + 1 : ℕ) : ℤ) + 1 + (i : ℤ) := le_of_not_gt hneg
      obtain ⟨m, hm⟩ : ∃ m : ℕ,
          -2 * ((N + 1 : ℕ) : ℤ) + 1 + (i : ℤ) = (m : ℤ) :=
        ⟨(-2 * ((N + 1 : ℕ) : ℤ) + 1 + (i : ℤ)).toNat,
          (Int.toNat_of_nonneg hnonneg).symm⟩
      have hinner := gnLink2_nonneg_mode_word_mem W rest hrestOK b wb hb m
      have houter := gnLink2_prepend_mem W ha (by omega : 1 ≤ i + 1) hinner
      have hidx : -1 - (i : ℤ) = -((i + 1 : ℕ) : ℤ) := by
        push_cast
        ring
      rw [hm, hidx]
      apply hlower
      exact gnGradeFil_mono W (by omega) houter

/-- Lemma 7's whole first family lies in the target span under the same high-head normalization
hypothesis. -/
theorem gnLink4_familyA_mem_span (W : VertexOperatorAlgebra 𝒱)
    {g : ℕ} {gen : Fin g → 𝒱} {wt : Fin g → ℕ}
    {a b : 𝒱} {wa wb N G : ℕ} (ha : a ∈ W.grading (wa : ℤ))
    (hb : b ∈ W.grading (wb : ℤ)) (hwa : 1 ≤ wa) (hwb : 1 ≤ wb)
    {rest : List (GNLetter 𝒱)} (hrestOK : GNWordOK W rest)
    (hrestWt : ∀ p ∈ rest, 1 ≤ p.2.1)
    (hgrade : wa + wb + gnWordGrade rest ≤ G)
    (hlower : gnGradeFil W (G - 1) ≤ gnSpan W gen wt (N + 1))
    (hhigh : ∀ (p : GNLetter 𝒱) (tail : List (GNLetter 𝒱)),
      GNWordOK W (p :: tail) → GNWeakDec (p :: tail) → N + 1 < p.2.2 →
      (∀ q ∈ p :: tail, 1 ≤ q.2.1) → gnWordGrade (p :: tail) ≤ G →
      gnWord W (p :: tail) W.vacuum ∈ gnSpan W gen wt (N + 1)) :
    (∑ᶠ i : ℕ, if i = N then 0 else W.smul a (-1 - (i : ℤ))
      (W.smul b (-2 * ((N + 1 : ℕ) : ℤ) + 1 + (i : ℤ))
        (gnWord W rest W.vacuum))) ∈ gnSpan W gen wt (N + 1) := by
  apply gnLink4_finsum_mem_of_support_finite _ _
    (gnLink4_familyA_support_finite W a b (gnWord W rest W.vacuum) N)
  intro i
  exact gnLink4_familyA_term_mem_span W ha hb hwa hwb hrestOK hrestWt hgrade hlower hhigh i

/-! ## The composite family and the repeated head -/

/-- The composite letter `a₍₋₁₎b` has declared GN weight `wa + wb`. -/
theorem gnLink4_composite_mem_grading (W : VertexOperatorAlgebra 𝒱)
    {a b : 𝒱} {wa wb : ℕ} (ha : a ∈ W.grading (wa : ℤ))
    (hb : b ∈ W.grading (wb : ℤ)) :
    W.smul a (-1) b ∈ W.grading ((wa + wb : ℕ) : ℤ) := by
  have h := W.smul_mem_grading ha hb (-1)
  have heq : (wa : ℤ) + (wb : ℤ) - (-1) - 1 = ((wa + wb : ℕ) : ℤ) := by
    push_cast
    ring
  rwa [heq] at h

/-! The next four lemmas isolate the algebraic three-family argument from its eventual target
submodule.  This avoids smuggling an unbounded `gnSpan` witness into the bounded outer
induction. -/

/-- Target-polymorphic form of the second family. -/
theorem gnLink4_familyB_mem_submodule (W : VertexOperatorAlgebra 𝒱)
    (P : Submodule ℂ 𝒱) {a b : 𝒱} {wa wb N G : ℕ}
    (ha : a ∈ W.grading (wa : ℤ)) (hb : b ∈ W.grading (wb : ℤ))
    (hwa : 1 ≤ wa) (hwb : 1 ≤ wb) {rest : List (GNLetter 𝒱)}
    (hrestOK : GNWordOK W rest) (hgrade : wa + wb + gnWordGrade rest ≤ G)
    (hlower : gnGradeFil W (G - 1) ≤ P) :
    (∑ᶠ i : ℕ, W.smul b (-2 * ((N + 1 : ℕ) : ℤ) - (i : ℤ))
      (W.smul a (i : ℤ) (gnWord W rest W.vacuum))) ∈ P := by
  apply gnLink4_finsum_mem_of_support_finite _ _
    (gnLink4_familyB_support_finite W a b (gnWord W rest W.vacuum) N)
  intro i
  exact hlower (gnLink4_familyB_term_mem_lower W ha hb hwa hwb hrestOK hgrade i)

/-- Target-polymorphic form of a first-family summand.  A negative inner mode produces an
explicit positive-mode word with one index above `N+1`; a nonnegative inner mode is lower
grade. -/
theorem gnLink4_familyA_term_mem_submodule (W : VertexOperatorAlgebra 𝒱)
    (P : Submodule ℂ 𝒱) {a b : 𝒱} {wa wb N G : ℕ}
    (ha : a ∈ W.grading (wa : ℤ)) (hb : b ∈ W.grading (wb : ℤ))
    (hwa : 1 ≤ wa) (hwb : 1 ≤ wb) {rest : List (GNLetter 𝒱)}
    (hrestOK : GNWordOK W rest) (hrestWt : ∀ p ∈ rest, 1 ≤ p.2.1)
    (hgrade : wa + wb + gnWordGrade rest ≤ G)
    (hlower : gnGradeFil W (G - 1) ≤ P)
    (hhigh : ∀ l : List (GNLetter 𝒱), GNWordOK W l →
      (∀ q ∈ l, 1 ≤ q.2.1) → gnWordGrade l ≤ G →
      (∃ q ∈ l, N + 1 < q.2.2) → gnWord W l W.vacuum ∈ P)
    (i : ℕ) :
    (if i = N then 0 else W.smul a (-1 - (i : ℤ))
      (W.smul b (-2 * ((N + 1 : ℕ) : ℤ) + 1 + (i : ℤ))
        (gnWord W rest W.vacuum))) ∈ P := by
  classical
  by_cases hiN : i = N
  · simp [hiN]
  · rw [if_neg hiN]
    by_cases hneg : -2 * ((N + 1 : ℕ) : ℤ) + 1 + (i : ℤ) < 0
    · have hiBound : i ≤ 2 * N := by omega
      let k : ℕ := 2 * N + 1 - i
      have hkpos : 1 ≤ k := by dsimp [k]; omega
      have hinner : -2 * ((N + 1 : ℕ) : ℤ) + 1 + (i : ℤ) = -(k : ℤ) := by
        have hkcast : (k : ℤ) = 2 * (N : ℤ) + 1 - (i : ℤ) := by
          dsimp [k]
          rw [Nat.cast_sub (by omega : i ≤ 2 * N + 1)]
          push_cast
          ring
        rw [hkcast]
        push_cast
        ring
      let l : List (GNLetter 𝒱) := (a, wa, i + 1) :: (b, wb, k) :: rest
      have hlOK : GNWordOK W l := by
        refine ⟨?_, ?_⟩
        · intro p hp
          rcases List.mem_cons.mp hp with rfl | hp
          · exact ha
          · rcases List.mem_cons.mp hp with rfl | hp
            · exact hb
            · exact hrestOK.1 p hp
        · intro p hp
          rcases List.mem_cons.mp hp with rfl | hp
          · change 1 ≤ i + 1
            omega
          · rcases List.mem_cons.mp hp with rfl | hp
            · exact hkpos
            · exact hrestOK.2 p hp
      have hlWt : ∀ p ∈ l, 1 ≤ p.2.1 := by
        intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact hwa
        · rcases List.mem_cons.mp hp with rfl | hp
          · exact hwb
          · exact hrestWt p hp
      have hlGrade : gnWordGrade l = wa + wb + gnWordGrade rest := by
        simp only [l, gnWordGrade_cons]
        omega
      have hlHigh : ∃ p ∈ l, N + 1 < p.2.2 := by
        by_cases hiLt : i < N
        · refine ⟨(b, wb, k), by simp [l], ?_⟩
          dsimp [k]
          omega
        · refine ⟨(a, wa, i + 1), by simp [l], ?_⟩
          change N + 1 < i + 1
          omega
      have hword : W.smul a (-1 - (i : ℤ))
          (W.smul b (-2 * ((N + 1 : ℕ) : ℤ) + 1 + (i : ℤ))
            (gnWord W rest W.vacuum)) = gnWord W l W.vacuum := by
        rw [show -1 - (i : ℤ) = -((i + 1 : ℕ) : ℤ) by push_cast; ring, hinner]
        rfl
      rw [hword]
      exact hhigh l hlOK hlWt (by rw [hlGrade]; exact hgrade) hlHigh
    · have hnonneg : 0 ≤ -2 * ((N + 1 : ℕ) : ℤ) + 1 + (i : ℤ) := le_of_not_gt hneg
      obtain ⟨m, hm⟩ : ∃ m : ℕ,
          -2 * ((N + 1 : ℕ) : ℤ) + 1 + (i : ℤ) = (m : ℤ) :=
        ⟨(-2 * ((N + 1 : ℕ) : ℤ) + 1 + (i : ℤ)).toNat,
          (Int.toNat_of_nonneg hnonneg).symm⟩
      have hinner := gnLink2_nonneg_mode_word_mem W rest hrestOK b wb hb m
      have houter := gnLink2_prepend_mem W ha (by omega : 1 ≤ i + 1) hinner
      have hidx : -1 - (i : ℤ) = -((i + 1 : ℕ) : ℤ) := by
        push_cast
        ring
      rw [hm, hidx]
      apply hlower
      exact gnGradeFil_mono W (by omega) houter

/-- Target-polymorphic form of the whole first family. -/
theorem gnLink4_familyA_mem_submodule (W : VertexOperatorAlgebra 𝒱)
    (P : Submodule ℂ 𝒱) {a b : 𝒱} {wa wb N G : ℕ}
    (ha : a ∈ W.grading (wa : ℤ)) (hb : b ∈ W.grading (wb : ℤ))
    (hwa : 1 ≤ wa) (hwb : 1 ≤ wb) {rest : List (GNLetter 𝒱)}
    (hrestOK : GNWordOK W rest) (hrestWt : ∀ p ∈ rest, 1 ≤ p.2.1)
    (hgrade : wa + wb + gnWordGrade rest ≤ G)
    (hlower : gnGradeFil W (G - 1) ≤ P)
    (hhigh : ∀ l : List (GNLetter 𝒱), GNWordOK W l →
      (∀ q ∈ l, 1 ≤ q.2.1) → gnWordGrade l ≤ G →
      (∃ q ∈ l, N + 1 < q.2.2) → gnWord W l W.vacuum ∈ P) :
    (∑ᶠ i : ℕ, if i = N then 0 else W.smul a (-1 - (i : ℤ))
      (W.smul b (-2 * ((N + 1 : ℕ) : ℤ) + 1 + (i : ℤ))
        (gnWord W rest W.vacuum))) ∈ P := by
  apply gnLink4_finsum_mem_of_support_finite _ _
    (gnLink4_familyA_support_finite W a b (gnWord W rest W.vacuum) N)
  intro i
  exact gnLink4_familyA_term_mem_submodule W P ha hb hwa hwb hrestOK hrestWt hgrade
    hlower hhigh i

/-- Target-polymorphic composite branch.  Unlike the older sorted-head convenience lemma, this
form makes no order assumption on `rest`; it records the composite as an arbitrary word
containing the high index `2(N+1)-1`. -/
theorem gnLink4_composite_mem_submodule (W : VertexOperatorAlgebra 𝒱)
    (P : Submodule ℂ 𝒱) {a b : 𝒱} {wa wb N G : ℕ} (hN : 1 ≤ N)
    (ha : a ∈ W.grading (wa : ℤ)) (hb : b ∈ W.grading (wb : ℤ))
    (hwa : 1 ≤ wa) (hwb : 1 ≤ wb) {rest : List (GNLetter 𝒱)}
    (hrestOK : GNWordOK W rest) (hrestWt : ∀ p ∈ rest, 1 ≤ p.2.1)
    (hgrade : wa + wb + gnWordGrade rest ≤ G)
    (hhigh : ∀ l : List (GNLetter 𝒱), GNWordOK W l →
      (∀ q ∈ l, 1 ≤ q.2.1) → gnWordGrade l ≤ G →
      (∃ q ∈ l, N + 1 < q.2.2) → gnWord W l W.vacuum ∈ P) :
    W.smul (W.smul a (-1) b) (-2 * ((N + 1 : ℕ) : ℤ) + 1)
      (gnWord W rest W.vacuum) ∈ P := by
  let c : 𝒱 := W.smul a (-1) b
  let p : GNLetter 𝒱 := (c, wa + wb, 2 * (N + 1) - 1)
  let l : List (GNLetter 𝒱) := p :: rest
  have hlOK : GNWordOK W l := by
    refine ⟨?_, ?_⟩
    · intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact gnLink4_composite_mem_grading W ha hb
      · exact hrestOK.1 q hq
    · intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · dsimp [p]
        omega
      · exact hrestOK.2 q hq
  have hlWt : ∀ q ∈ l, 1 ≤ q.2.1 := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · dsimp [p]
      omega
    · exact hrestWt q hq
  have hlGrade : gnWordGrade l ≤ G := by
    simpa [l, p, gnWordGrade] using hgrade
  have hlHigh : ∃ q ∈ l, N + 1 < q.2.2 := by
    refine ⟨p, by simp [l], ?_⟩
    dsimp [p]
    omega
  have hmem := hhigh l hlOK hlWt hlGrade hlHigh
  have hmode : -2 * ((N + 1 : ℕ) : ℤ) + 1 =
      -((2 * (N + 1) - 1 : ℕ) : ℤ) := by
    push_cast [Nat.cast_sub (by omega : 1 ≤ 2 * (N + 1))]
    ring
  rw [hmode]
  exact hmem

/-- The complete repeated-head identity, targeting an arbitrary submodule.  It needs no weak
decrease and imposes no upper bound on indices in `rest`; all order restoration is delegated to
the high-word callback. -/
theorem gnLink4_repeatedHead_mem_submodule (W : VertexOperatorAlgebra 𝒱)
    (P : Submodule ℂ 𝒱) {a b : 𝒱} {wa wb N G : ℕ}
    {rest : List (GNLetter 𝒱)} (hN : 1 ≤ N)
    (hOK : GNWordOK W ((a, wa, N + 1) :: (b, wb, N + 1) :: rest))
    (hwtPos : ∀ p ∈ (a, wa, N + 1) :: (b, wb, N + 1) :: rest, 1 ≤ p.2.1)
    (hgrade : gnWordGrade ((a, wa, N + 1) :: (b, wb, N + 1) :: rest) ≤ G)
    (hlower : gnGradeFil W (G - 1) ≤ P)
    (hhigh : ∀ l : List (GNLetter 𝒱), GNWordOK W l →
      (∀ q ∈ l, 1 ≤ q.2.1) → gnWordGrade l ≤ G →
      (∃ q ∈ l, N + 1 < q.2.2) → gnWord W l W.vacuum ∈ P) :
    gnWord W ((a, wa, N + 1) :: (b, wb, N + 1) :: rest) W.vacuum ∈ P := by
  have ha : a ∈ W.grading (wa : ℤ) := hOK.head_mem
  have hb : b ∈ W.grading (wb : ℤ) := hOK.tail.head_mem
  have hrestOK : GNWordOK W rest := hOK.tail.tail
  have hwa : 1 ≤ wa := hwtPos _ (List.mem_cons_self ..)
  have hwb : 1 ≤ wb := hwtPos _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have hrestWt : ∀ p ∈ rest, 1 ≤ p.2.1 :=
    fun p hp => hwtPos p (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hp))
  have hgrade' : wa + wb + gnWordGrade rest ≤ G := by
    simpa only [gnWordGrade_cons, Nat.add_assoc] using hgrade
  have hcomp := gnLink4_composite_mem_submodule W P hN ha hb hwa hwb hrestOK hrestWt
    hgrade' hhigh
  have hA := gnLink4_familyA_mem_submodule W P ha hb hwa hwb hrestOK hrestWt hgrade'
    hlower hhigh
  have hB := gnLink4_familyB_mem_submodule W P (N := N) ha hb hwa hwb hrestOK hgrade'
    hlower
  rw [gnWord_repeatedHead W a b wa wb (N + 1) (by omega) rest]
  exact P.sub_mem (P.sub_mem hcomp hA) hB

/-- Bounded Link 4 above target level `1`.  This is the form required by Link 3: the input
repeated head may be unsorted and its tail may contain arbitrarily high modes. -/
theorem gnLink4_repeatedHead_mem_bounded_of_outer (W : VertexOperatorAlgebra 𝒱)
    {g : ℕ} {gen : Fin g → 𝒱} {wt : Fin g → ℕ}
    (hgen : ∀ i, gen i ∈ W.grading (wt i : ℤ))
    (hgenPos : ∀ i, 1 ≤ wt i)
    (hdec : (⊤ : Submodule ℂ 𝒱) =
      Submodule.span ℂ (Set.range gen ∪ {W.vacuum}) ⊔ O₂ W)
    {a b : 𝒱} {wa wb N G : ℕ} {rest : List (GNLetter 𝒱)} (hN : 1 ≤ N)
    (hOK : GNWordOK W ((a, wa, N + 1) :: (b, wb, N + 1) :: rest))
    (hwtPos : ∀ p ∈ (a, wa, N + 1) :: (b, wb, N + 1) :: rest, 1 ≤ p.2.1)
    (hgrade : gnWordGrade ((a, wa, N + 1) :: (b, wb, N + 1) :: rest) ≤ G)
    (houter : ∀ H < G, GNReachBounded W gen wt H (N + 1)) :
    gnWord W ((a, wa, N + 1) :: (b, wb, N + 1) :: rest) W.vacuum ∈
      gnSpanBounded W gen wt G (N + 1) := by
  have hwa : 1 ≤ wa := hwtPos _ (List.mem_cons_self ..)
  have hwb : 1 ≤ wb := hwtPos _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have hG : 1 ≤ G := by
    have hgrade' : wa + wb + gnWordGrade rest ≤ G := by
      simpa only [gnWordGrade_cons, Nat.add_assoc] using hgrade
    omega
  have hlower : gnGradeFil W (G - 1) ≤ gnSpanBounded W gen wt G (N + 1) :=
    le_trans (houter (G - 1) (by omega))
      (gnSpanBounded_mono_grade W gen wt (by omega))
  apply gnLink4_repeatedHead_mem_submodule W (gnSpanBounded W gen wt G (N + 1)) hN
    hOK hwtPos hgrade hlower
  intro l hlOK hlWt hlGrade hlHigh
  exact gnLink4_word_mem_bounded_of_contains_high W hgen hgenPos hdec houter hlower
    l hlOK hlWt hlGrade hlHigh

/-- At retained grade zero, a bounded generator word with positive generator weights is empty;
hence increasing the no-repeat cutoff does not remove any witness. -/
theorem gnLink4_gnSpanBounded_zero_mono_index (W : VertexOperatorAlgebra 𝒱)
    {g : ℕ} (gen : Fin g → 𝒱) (wt : Fin g → ℕ)
    (hwt : ∀ i, 1 ≤ wt i) (N : ℕ) :
    gnSpanBounded W gen wt 0 N ≤ gnSpanBounded W gen wt 0 (N + 1) := by
  rw [gnSpanBounded, gnSpanBounded, Submodule.span_le]
  rintro x ⟨l, hOK, hgrade, hwd, _hnr, hover, rfl⟩
  have hl : l = [] := by
    cases l with
    | nil => rfl
    | cons p tail =>
        obtain ⟨i, -, hpwt⟩ := hover p (List.mem_cons_self ..)
        have hpPos : 1 ≤ p.2.1 := by
          rw [hpwt]
          exact hwt i
        simp only [gnWordGrade_cons] at hgrade
        omega
  subst l
  exact Submodule.subset_span
    ⟨[], GNWordOK.nil W, by simp [gnWordGrade], by simp [GNWeakDec],
      by simp [GNNoRepeatLE], by simp [OverGens], rfl⟩

/-- Link 3 plus bounded Link 4 closes the successor step at every positive repetition level.
The grade-zero branch is discharged separately by positivity of generator weights. -/
theorem gnLink4_GNReachBounded_succ_of_repeatedHead_pos (W : VertexOperatorAlgebra 𝒱)
    {g : ℕ} {gen : Fin g → 𝒱} {wt : Fin g → ℕ}
    (hgen : ∀ i, gen i ∈ W.grading (wt i : ℤ))
    (hwt : ∀ i, 1 ≤ wt i)
    (hdec : (⊤ : Submodule ℂ 𝒱) =
      Submodule.span ℂ (Set.range gen ∪ {W.vacuum}) ⊔ O₂ W)
    {G N : ℕ} (hN : 1 ≤ N) (hR : GNReachBounded W gen wt G N)
    (hLower : ∀ G' < G, GNReachBounded W gen wt G' (N + 1)) :
    GNReachBounded W gen wt G (N + 1) := by
  by_cases hG0 : G = 0
  · subst G
    exact le_trans hR (gnLink4_gnSpanBounded_zero_mono_index W gen wt hwt N)
  · have hG : 1 ≤ G := Nat.one_le_iff_ne_zero.mpr hG0
    apply GNReachBounded_succ_of_repeatedHead hwt hR (hLower (G - 1) (by omega))
    intro A B rest hOK hgrade _hnr hover hAidx hBidx
    have hpos : ∀ p ∈ A :: B :: rest, 1 ≤ p.2.1 := by
      intro p hp
      obtain ⟨i, -, hpwt⟩ := hover p hp
      rw [hpwt]
      exact hwt i
    rcases A with ⟨a, wa, ka⟩
    rcases B with ⟨b, wb, kb⟩
    dsimp at hAidx hBidx
    subst ka
    subst kb
    exact gnLink4_repeatedHead_mem_bounded_of_outer W hgen hwt hdec hN hOK hpos hgrade
      hLower

/-- For `N > 0`, the composite term has the exact high-head index `2(N+1)-1`. -/
theorem gnLink4_composite_mem_span (W : VertexOperatorAlgebra 𝒱)
    {g : ℕ} {gen : Fin g → 𝒱} {wt : Fin g → ℕ}
    {a b : 𝒱} {wa wb N G : ℕ} (hN : 1 ≤ N)
    (ha : a ∈ W.grading (wa : ℤ)) (hb : b ∈ W.grading (wb : ℤ))
    (hwa : 1 ≤ wa) (hwb : 1 ≤ wb)
    {rest : List (GNLetter 𝒱)} (hrestOK : GNWordOK W rest)
    (hrestWt : ∀ p ∈ rest, 1 ≤ p.2.1) (hrestWD : GNWeakDec rest)
    (hrestIdx : ∀ p ∈ rest, p.2.2 ≤ N + 1)
    (hgrade : wa + wb + gnWordGrade rest ≤ G)
    (hhigh : ∀ (p : GNLetter 𝒱) (tail : List (GNLetter 𝒱)),
      GNWordOK W (p :: tail) → GNWeakDec (p :: tail) → N + 1 < p.2.2 →
      (∀ q ∈ p :: tail, 1 ≤ q.2.1) → gnWordGrade (p :: tail) ≤ G →
      gnWord W (p :: tail) W.vacuum ∈ gnSpan W gen wt (N + 1)) :
    W.smul (W.smul a (-1) b) (-2 * ((N + 1 : ℕ) : ℤ) + 1)
      (gnWord W rest W.vacuum) ∈ gnSpan W gen wt (N + 1) := by
  let c : 𝒱 := W.smul a (-1) b
  let p : GNLetter 𝒱 := (c, wa + wb, 2 * (N + 1) - 1)
  have hpidx : N + 1 < p.2.2 := by dsimp [p]; omega
  have hpOK : GNWordOK W (p :: rest) := by
    refine ⟨?_, ?_⟩
    · intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact gnLink4_composite_mem_grading W ha hb
      · exact hrestOK.1 q hq
    · intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · dsimp [p]
        omega
      · exact hrestOK.2 q hq
  have hpWD : GNWeakDec (p :: rest) := by
    apply List.pairwise_cons.mpr
    refine ⟨?_, hrestWD⟩
    intro q hq
    dsimp [p]
    exact le_trans (hrestIdx q hq) (by omega)
  have hpWt : ∀ q ∈ p :: rest, 1 ≤ q.2.1 := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · dsimp [p]
      omega
    · exact hrestWt q hq
  have hpGrade : gnWordGrade (p :: rest) ≤ G := by
    simpa [p, gnWordGrade] using hgrade
  have hmem := hhigh p rest hpOK hpWD hpidx hpWt hpGrade
  have hmode : -2 * ((N + 1 : ℕ) : ℤ) + 1 =
      -((2 * (N + 1) - 1 : ℕ) : ℤ) := by
    push_cast [Nat.cast_sub (by omega : 1 ≤ 2 * (N + 1))]
    ring
  rw [hmode]
  exact hmem

/-- Link 4 for repetition level `N+1 ≥ 2`, with its exact repeated-head input shape.  The three
right-hand families of `gnWord_repeatedHead` are put in `gnSpan ... (N+1)` separately. -/
theorem gnLink4_repeatedHead_mem_span (W : VertexOperatorAlgebra 𝒱)
    {g : ℕ} {gen : Fin g → 𝒱} {wt : Fin g → ℕ}
    {a b : 𝒱} {wa wb N G : ℕ} {rest : List (GNLetter 𝒱)} (hN : 1 ≤ N)
    (hOK : GNWordOK W ((a, wa, N + 1) :: (b, wb, N + 1) :: rest))
    (hwtPos : ∀ p ∈ (a, wa, N + 1) :: (b, wb, N + 1) :: rest, 1 ≤ p.2.1)
    (hwd : GNWeakDec ((a, wa, N + 1) :: (b, wb, N + 1) :: rest))
    (hgrade : gnWordGrade ((a, wa, N + 1) :: (b, wb, N + 1) :: rest) ≤ G)
    (hlower : gnGradeFil W (G - 1) ≤ gnSpan W gen wt (N + 1))
    (hhigh : ∀ (p : GNLetter 𝒱) (tail : List (GNLetter 𝒱)),
      GNWordOK W (p :: tail) → GNWeakDec (p :: tail) → N + 1 < p.2.2 →
      (∀ q ∈ p :: tail, 1 ≤ q.2.1) → gnWordGrade (p :: tail) ≤ G →
      gnWord W (p :: tail) W.vacuum ∈ gnSpan W gen wt (N + 1)) :
    gnWord W ((a, wa, N + 1) :: (b, wb, N + 1) :: rest) W.vacuum ∈
      gnSpan W gen wt (N + 1) := by
  have ha : a ∈ W.grading (wa : ℤ) := hOK.head_mem
  have hb : b ∈ W.grading (wb : ℤ) := hOK.tail.head_mem
  have hrestOK : GNWordOK W rest := hOK.tail.tail
  have hwa : 1 ≤ wa := hwtPos _ (List.mem_cons_self ..)
  have hwb : 1 ≤ wb := hwtPos _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have hrestWt : ∀ p ∈ rest, 1 ≤ p.2.1 :=
    fun p hp => hwtPos p (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hp))
  have hrestWD : GNWeakDec rest := hwd.tail.tail
  have hrestIdx : ∀ p ∈ rest, p.2.2 ≤ N + 1 := by
    intro p hp
    exact (List.pairwise_cons.mp hwd.tail).1 p hp
  have hgrade' : wa + wb + gnWordGrade rest ≤ G := by
    simpa only [gnWordGrade_cons, Nat.add_assoc] using hgrade
  have hcomp := gnLink4_composite_mem_span W hN ha hb hwa hwb hrestOK hrestWt
    hrestWD hrestIdx hgrade' hhigh
  have hA := gnLink4_familyA_mem_span W ha hb hwa hwb hrestOK hrestWt hgrade'
    hlower hhigh
  have hB := gnLink4_familyB_mem_span W ha hb hwa hwb hrestOK hgrade' hlower
  rw [gnWord_repeatedHead W a b wa wb (N + 1) (by omega) rest]
  exact (gnSpan W gen wt (N + 1)).sub_mem
    ((gnSpan W gen wt (N + 1)).sub_mem hcomp hA) hB

/-- Link 4 above level `1`, discharged from the grade-bounded form of the outer induction and
the representative decomposition.  This corollary constructs the high-head hypothesis used by
`gnLink4_repeatedHead_mem_span`; no unbounded `GNReach` witness is used as though it retained a
grade cap. -/
theorem gnLink4_repeatedHead_mem_span_of_bounded_outer (W : VertexOperatorAlgebra 𝒱)
    {g : ℕ} {gen : Fin g → 𝒱} {wt : Fin g → ℕ}
    (hgen : ∀ i, gen i ∈ W.grading (wt i : ℤ))
    (hgenPos : ∀ i, 1 ≤ wt i)
    (hdec : (⊤ : Submodule ℂ 𝒱) =
      Submodule.span ℂ (Set.range gen ∪ {W.vacuum}) ⊔ O₂ W)
    {a b : 𝒱} {wa wb N G : ℕ} {rest : List (GNLetter 𝒱)} (hN : 1 ≤ N)
    (hOK : GNWordOK W ((a, wa, N + 1) :: (b, wb, N + 1) :: rest))
    (hwtPos : ∀ p ∈ (a, wa, N + 1) :: (b, wb, N + 1) :: rest, 1 ≤ p.2.1)
    (hwd : GNWeakDec ((a, wa, N + 1) :: (b, wb, N + 1) :: rest))
    (hgrade : gnWordGrade ((a, wa, N + 1) :: (b, wb, N + 1) :: rest) ≤ G)
    (houter : ∀ H < G, GNReachBounded W gen wt H (N + 1)) :
    gnWord W ((a, wa, N + 1) :: (b, wb, N + 1) :: rest) W.vacuum ∈
      gnSpan W gen wt (N + 1) := by
  have hwa : 1 ≤ wa := hwtPos _ (List.mem_cons_self ..)
  have hwb : 1 ≤ wb := hwtPos _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have hgrade' : wa + (wb + gnWordGrade rest) ≤ G := by
    simpa only [gnWordGrade_cons] using hgrade
  have hG : 1 ≤ G := by
    omega
  have hlower : gnGradeFil W (G - 1) ≤ gnSpan W gen wt (N + 1) :=
    le_trans (houter (G - 1) (by omega))
      (gnSpanBounded_le_gnSpan W gen wt (G - 1) (N + 1))
  apply gnLink4_repeatedHead_mem_span W hN hOK hwtPos hwd hgrade hlower
  intro p tail hpOK hpWD hpidx hpWt hpGrade
  exact gnLink4_highHead_mem_span_of_bounded_outer W hgen hgenPos hdec houter hlower
    p tail hpOK hpWD hpidx hpWt hpGrade

/-! ## The special target level `1` -/

/-- If an admissible positive-mode word has no index above `1`, every index is exactly `1`.
This is the shape split used for Link 3's unsorted level-one repeated-head output. -/
theorem gnLink4_all_indices_one_of_no_high (W : VertexOperatorAlgebra 𝒱)
    {l : List (GNLetter 𝒱)} (hOK : GNWordOK W l)
    (hnoHigh : ¬ ∃ p ∈ l, 1 < p.2.2) : ∀ p ∈ l, p.2.2 = 1 := by
  intro p hp
  have hpos : 1 ≤ p.2.2 := hOK.2 p hp
  have hle : p.2.2 ≤ 1 := by
    by_contra h
    exact hnoHigh ⟨p, hp, by omega⟩
  omega

/-- The exact shape forced by a weakly decreasing admissible repeated head at level `1`: every
letter in the remaining tail also has mode index `1`. -/
theorem gnLink4_levelOne_rest_index_eq_one (W : VertexOperatorAlgebra 𝒱)
    {a b : 𝒱} {wa wb : ℕ} {rest : List (GNLetter 𝒱)}
    (hOK : GNWordOK W ((a, wa, 1) :: (b, wb, 1) :: rest))
    (hwd : GNWeakDec ((a, wa, 1) :: (b, wb, 1) :: rest)) :
    ∀ p ∈ rest, p.2.2 = 1 := by
  intro p hp
  have hpos : 1 ≤ p.2.2 := hOK.tail.tail.2 p hp
  have hle : p.2.2 ≤ 1 := (List.pairwise_cons.mp hwd.tail).1 p hp
  omega

/-- At target level `1`, the composite replaces the two repeated head occurrences by exactly one
new occurrence.  This is the strict count decrease used by the exceptional length/count
induction. -/
theorem gnLink4_levelOne_composite_count (c : 𝒱) (wc : ℕ)
    (rest : List (GNLetter 𝒱)) :
    gnCountAt 1 ((c, wc, 1) :: rest) = gnCountAt 1 rest + 1 := by
  classical
  simp [gnCountAt]

/-- At target level `1`, every non-omitted first-family term is lower-grade.  This isolates the
only remaining same-grade term there: the composite mode has index exactly `1`, not a high
index. -/
theorem gnLink4_familyA_levelOne_term_mem_lower (W : VertexOperatorAlgebra 𝒱)
    {a b : 𝒱} {wa wb G : ℕ} (ha : a ∈ W.grading (wa : ℤ))
    (hb : b ∈ W.grading (wb : ℤ)) (hwa : 1 ≤ wa) (hwb : 1 ≤ wb)
    {rest : List (GNLetter 𝒱)} (hrestOK : GNWordOK W rest)
    (hgrade : wa + wb + gnWordGrade rest ≤ G) (i : ℕ) :
    (if i = 0 then 0 else W.smul a (-1 - (i : ℤ))
      (W.smul b (-2 * (1 : ℤ) + 1 + (i : ℤ))
        (gnWord W rest W.vacuum))) ∈ gnGradeFil W (G - 1) := by
  by_cases hi : i = 0
  · simp [hi]
  · rw [if_neg hi]
    have hnonneg : 0 ≤ -2 * (1 : ℤ) + 1 + (i : ℤ) := by omega
    obtain ⟨m, hm⟩ : ∃ m : ℕ, -2 * (1 : ℤ) + 1 + (i : ℤ) = (m : ℤ) :=
      ⟨(-2 * (1 : ℤ) + 1 + (i : ℤ)).toNat, (Int.toNat_of_nonneg hnonneg).symm⟩
    have hinner := gnLink2_nonneg_mode_word_mem W rest hrestOK b wb hb m
    have houter := gnLink2_prepend_mem W ha (by omega : 1 ≤ i + 1) hinner
    have hidx : -1 - (i : ℤ) = -((i + 1 : ℕ) : ℤ) := by
      push_cast
      ring
    rw [hm, hidx]
    exact gnGradeFil_mono W (by omega) houter

/-- The entire first Lemma 7 family is lower-grade at target level `1`. -/
theorem gnLink4_familyA_levelOne_mem_lower (W : VertexOperatorAlgebra 𝒱)
    {a b : 𝒱} {wa wb G : ℕ} (ha : a ∈ W.grading (wa : ℤ))
    (hb : b ∈ W.grading (wb : ℤ)) (hwa : 1 ≤ wa) (hwb : 1 ≤ wb)
    {rest : List (GNLetter 𝒱)} (hrestOK : GNWordOK W rest)
    (hgrade : wa + wb + gnWordGrade rest ≤ G) :
    (∑ᶠ i : ℕ, if i = 0 then 0 else W.smul a (-1 - (i : ℤ))
      (W.smul b (-2 * (1 : ℤ) + 1 + (i : ℤ))
        (gnWord W rest W.vacuum))) ∈ gnGradeFil W (G - 1) := by
  apply gnLink4_finsum_mem_of_support_finite _ _
    (gnLink4_familyA_support_finite W a b (gnWord W rest W.vacuum) 0)
  intro i
  exact gnLink4_familyA_levelOne_term_mem_lower W ha hb hwa hwb hrestOK hgrade i

/-- The arithmetic shape-gate for the exceptional target level `1`: the composite index is
exactly the repeated index. -/
theorem gnLink4_levelOne_composite_index : 2 * (0 + 1) - 1 = 0 + 1 := by omega

end VOA
