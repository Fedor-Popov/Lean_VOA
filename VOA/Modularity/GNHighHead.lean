/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.GNLink2Representatives
import VOA.Modularity.GNLink3Migration

/-!
# Bounded normalization of words with a high mode index

This file packages the high-index case of the outer GN grade induction.  A generator word with
some mode index above the target bound is first sorted.  Its high head is peeled off, its
strictly lower-grade tail is normalized by the outer induction hypothesis, and the head is
reattached and sorted once more.  Representative replacement then extends the result to an
arbitrary positive-weight admissible word while retaining its exact mode-index skeleton.
-/

namespace VOA

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- A weakly decreasing word containing an index above `B` has a high head. -/
theorem gnHighHead_exists_high_head {B : ℕ} {l : List (GNLetter 𝒱)}
    (hwd : GNWeakDec l) (hhigh : ∃ p ∈ l, B < p.2.2) :
    ∃ p : GNLetter 𝒱, ∃ tail : List (GNLetter 𝒱), l = p :: tail ∧ B < p.2.2 := by
  rcases hhigh with ⟨q, hq, hqB⟩
  cases l with
  | nil => simp at hq
  | cons p tail =>
      refine ⟨p, tail, rfl, ?_⟩
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hqB
      · have hpq := (List.pairwise_cons.mp hwd).1 q hq
        omega

/-- Existence of a high mode index is determined by the exact Link-2 skeleton. -/
theorem gnHighHead_exists_of_link2Skeleton_eq {B : ℕ} {l l' : List (GNLetter 𝒱)}
    (hsk : gnLink2Skeleton l' = gnLink2Skeleton l)
    (hhigh : ∃ p ∈ l, B < p.2.2) : ∃ p ∈ l', B < p.2.2 := by
  obtain ⟨p, hp, hpB⟩ := hhigh
  have hpSk : p.2.2 ∈ gnLink2Skeleton l := by
    exact List.mem_map.mpr ⟨p, hp, rfl⟩
  have hpSk' : p.2.2 ∈ gnLink2Skeleton l' := by
    rw [hsk]
    exact hpSk
  obtain ⟨q, hq, hqidx⟩ := List.mem_map.mp hpSk'
  exact ⟨q, hq, by simpa only [hqidx] using hpB⟩

/-- Reattach a generator at a mode index above `B` to a boundedly normalized tail.  Sorting the
result preserves `GNNoRepeatLE B`; its permutation error is handled at its exact lower grade. -/
theorem gnHighHead_prepend_generator_mem_bounded (W : VertexOperatorAlgebra 𝒱)
    {g : ℕ} {gen : Fin g → 𝒱} {wt : Fin g → ℕ}
    (hgen : ∀ i, gen i ∈ W.grading (wt i : ℤ))
    (hgenPos : ∀ i, 1 ≤ wt i) {G B : ℕ}
    (hLower : ∀ G' < G, GNReachBounded W gen wt G' B)
    (i : Fin g) {k H : ℕ} (hk : B < k) (hgrade : wt i + H ≤ G)
    {x : 𝒱} (hx : x ∈ gnSpanBounded W gen wt H B) :
    W.smul (gen i) (-(k : ℤ)) x ∈ gnSpanBounded W gen wt G B := by
  classical
  refine Submodule.span_induction
    (p := fun x _ => W.smul (gen i) (-(k : ℤ)) x ∈
      gnSpanBounded W gen wt G B) ?_ ?_ ?_ ?_ hx
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
    have hrawPos : ∀ q ∈ raw, 1 ≤ q.2.1 := by
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hgenPos i
      · obtain ⟨j, -, hjwt⟩ := hlGens q hq
        rw [hjwt]
        exact hgenPos j
    have hrawNR : GNNoRepeatLE B raw := by
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
    have hrawGradePos : 1 ≤ gnWordGrade raw := by
      simp only [raw, p, gnWordGrade_cons]
      have hiPos := hgenPos i
      omega
    obtain ⟨sorted, hperm, hsortedWD⟩ := exists_weakDec_perm raw
    have hsortedOK := gnWordOK_of_perm W hperm hrawOK
    have hsortedNR := hrawNR.perm hperm
    have hsortedGens := hrawGens.perm hperm
    have hsortedGrade : gnWordGrade sorted ≤ G := by
      rw [← gnWordGrade_eq_of_perm hperm]
      exact hrawGrade
    have hsortedMem : gnWord W sorted W.vacuum ∈ gnSpanBounded W gen wt G B :=
      Submodule.subset_span
        ⟨sorted, hsortedOK, hsortedGrade, hsortedWD, hsortedNR, hsortedGens, rfl⟩
    have herr := gnWord_perm_sub_mem_grade W hperm hrawOK hrawPos
    have herrGradeLt : gnWordGrade raw - 1 < G := by omega
    have herrSmall :
        gnWord W raw W.vacuum - gnWord W sorted W.vacuum ∈
          gnSpanBounded W gen wt (gnWordGrade raw - 1) B :=
      hLower (gnWordGrade raw - 1) herrGradeLt herr
    have herrMem :
        gnWord W raw W.vacuum - gnWord W sorted W.vacuum ∈
          gnSpanBounded W gen wt G B :=
      gnSpanBounded_mono_grade W gen wt (Nat.le_of_lt herrGradeLt) herrSmall
    have hadd := (gnSpanBounded W gen wt G B).add_mem herrMem hsortedMem
    change gnWord W raw W.vacuum ∈ gnSpanBounded W gen wt G B
    convert hadd using 1 <;> abel
  · change W.smul (gen i) (-(k : ℤ)) 0 ∈ gnSpanBounded W gen wt G B
    rw [W.smul_zero_right]
    exact Submodule.zero_mem _
  · intro y z _ _ hy hz
    rw [W.smul_add_right]
    exact Submodule.add_mem _ hy hz
  · intro c y _ hy
    rw [W.smul_smul_right]
    exact Submodule.smul_mem _ _ hy

/-- A grade-bounded generator word containing an index above `B` normalizes into the bounded
target.  No order assumption is made on the input word. -/
theorem gnHighHead_generator_word_mem_bounded (W : VertexOperatorAlgebra 𝒱)
    {g : ℕ} {gen : Fin g → 𝒱} {wt : Fin g → ℕ}
    (hgen : ∀ i, gen i ∈ W.grading (wt i : ℤ))
    (hgenPos : ∀ i, 1 ≤ wt i) {G B : ℕ}
    (hLower : ∀ G' < G, GNReachBounded W gen wt G' B)
    {l : List (GNLetter 𝒱)} (hOK : GNWordOK W l)
    (hgens : OverGens gen wt l) (hgrade : gnWordGrade l ≤ G)
    (hhigh : ∃ p ∈ l, B < p.2.2) :
    gnWord W l W.vacuum ∈ gnSpanBounded W gen wt G B := by
  classical
  have hpos : ∀ p ∈ l, 1 ≤ p.2.1 := by
    intro p hp
    obtain ⟨i, -, hiwt⟩ := hgens p hp
    rw [hiwt]
    exact hgenPos i
  have hgradePos : 1 ≤ gnWordGrade l := by
    obtain ⟨p, hp, -⟩ := hhigh
    have hpPos := hpos p hp
    rw [gnWordGrade]
    exact le_trans hpPos (List.single_le_sum (fun _ _ => Nat.zero_le _) p.2.1
      (List.mem_map_of_mem hp))
  obtain ⟨sorted, hperm, hsortedWD⟩ := exists_weakDec_perm l
  have hsortedOK := gnWordOK_of_perm W hperm hOK
  have hsortedGens := hgens.perm hperm
  have hsortedPos : ∀ p ∈ sorted, 1 ≤ p.2.1 :=
    gnForall_mem_perm hperm hpos
  have hsortedHigh : ∃ p ∈ sorted, B < p.2.2 := by
    obtain ⟨p, hp, hpidx⟩ := hhigh
    exact ⟨p, hperm.mem_iff.mp hp, hpidx⟩
  have hsortedGrade : gnWordGrade sorted ≤ G := by
    rw [← gnWordGrade_eq_of_perm hperm]
    exact hgrade
  obtain ⟨p, tail, rfl, hpidx⟩ :=
    gnHighHead_exists_high_head hsortedWD hsortedHigh
  have hpPos : 1 ≤ p.2.1 := hsortedPos p (List.mem_cons_self ..)
  have htailGradeLt : gnWordGrade tail < G := by
    rw [gnWordGrade_cons] at hsortedGrade
    omega
  have htailFil : gnWord W tail W.vacuum ∈ gnGradeFil W (gnWordGrade tail) :=
    word_mem_gnGradeFil W hsortedOK.tail (le_refl _)
  have htailBound : gnWord W tail W.vacuum ∈
      gnSpanBounded W gen wt (gnWordGrade tail) B :=
    hLower (gnWordGrade tail) htailGradeLt htailFil
  obtain ⟨i, hpgen, hpwt⟩ := hsortedGens p (List.mem_cons_self ..)
  have hmain : gnWord W (p :: tail) W.vacuum ∈ gnSpanBounded W gen wt G B := by
    rw [gnWord_cons, hpgen]
    apply gnHighHead_prepend_generator_mem_bounded W hgen hgenPos hLower i hpidx
      (H := gnWordGrade tail) (G := G) (B := B) ?_ htailBound
    rw [← hpwt]
    simpa only [gnWordGrade_cons] using hsortedGrade
  have herr := gnWord_perm_sub_mem_grade W hperm hOK hpos
  have herrGradeLt : gnWordGrade l - 1 < G := by omega
  have herrSmall :
      gnWord W l W.vacuum - gnWord W (p :: tail) W.vacuum ∈
        gnSpanBounded W gen wt (gnWordGrade l - 1) B :=
    hLower (gnWordGrade l - 1) herrGradeLt herr
  have herrMem :
      gnWord W l W.vacuum - gnWord W (p :: tail) W.vacuum ∈
        gnSpanBounded W gen wt G B :=
    gnSpanBounded_mono_grade W gen wt (Nat.le_of_lt herrGradeLt) herrSmall
  have hadd := (gnSpanBounded W gen wt G B).add_mem herrMem hmain
  convert hadd using 1 <;> abel

/-- An arbitrary positive-weight admissible word containing an index above `B` normalizes into
the grade-bounded target.  Link 2 preserves its exact index skeleton in all same-grade generator
branches, so the high index survives representative replacement.  No order assumption is made. -/
theorem gnHighHead_word_mem_bounded (W : VertexOperatorAlgebra 𝒱)
    {g : ℕ} {gen : Fin g → 𝒱} {wt : Fin g → ℕ}
    (hgen : ∀ i, gen i ∈ W.grading (wt i : ℤ))
    (hgenPos : ∀ i, 1 ≤ wt i)
    (hdec : (⊤ : Submodule ℂ 𝒱) =
      Submodule.span ℂ (Set.range gen ∪ {W.vacuum}) ⊔ O₂ W)
    {G B : ℕ} (hLower : ∀ G' < G, GNReachBounded W gen wt G' B)
    {l : List (GNLetter 𝒱)} (hOK : GNWordOK W l)
    (hpos : ∀ p ∈ l, 1 ≤ p.2.1) (hgrade : gnWordGrade l ≤ G)
    (hhigh : ∃ p ∈ l, B < p.2.2) :
    gnWord W l W.vacuum ∈ gnSpanBounded W gen wt G B := by
  classical
  have hgradePos : 1 ≤ gnWordGrade l := by
    obtain ⟨p, hp, -⟩ := hhigh
    have hpPos := hpos p hp
    rw [gnWordGrade]
    exact le_trans hpPos (List.single_le_sum (fun _ _ => Nat.zero_le _) p.2.1
      (List.mem_map_of_mem hp))
  have hnorm := gnLink2_word_mem_rawSkeletonSpan_sup_lower
    W gen wt hgen hdec l hOK hpos
  rw [Submodule.mem_sup] at hnorm
  obtain ⟨a, ha, b, hb, hab⟩ := hnorm
  have hraw : a ∈ gnSpanBounded W gen wt G B := by
    refine Submodule.span_induction
      (p := fun x _ => x ∈ gnSpanBounded W gen wt G B) ?_ ?_ ?_ ?_ ha
    · rintro x ⟨l', hlOK, hlGens, hlGrade, hlSk, rfl⟩
      apply gnHighHead_generator_word_mem_bounded W hgen hgenPos hLower hlOK hlGens
        (le_trans hlGrade hgrade)
      exact gnHighHead_exists_of_link2Skeleton_eq hlSk hhigh
    · exact Submodule.zero_mem _
    · intro x y _ _ hx hy
      exact Submodule.add_mem _ hx hy
    · intro c x _ hx
      exact Submodule.smul_mem _ c hx
  have hbFil : b ∈ gnGradeFil W (gnWordGrade l - 1) := by
    simpa [gnLink2LowerFil, Nat.ne_of_gt (show 0 < gnWordGrade l by omega)] using hb
  have hbGradeLt : gnWordGrade l - 1 < G := by omega
  have hbSmall : b ∈ gnSpanBounded W gen wt (gnWordGrade l - 1) B :=
    hLower (gnWordGrade l - 1) hbGradeLt hbFil
  have hbBig : b ∈ gnSpanBounded W gen wt G B :=
    gnSpanBounded_mono_grade W gen wt (Nat.le_of_lt hbGradeLt) hbSmall
  rw [← hab]
  exact Submodule.add_mem _ hraw hbBig

end VOA
