/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.GNLink4RepeatedHead

/-!
# The exceptional repeated mode at level one

At target mode `1`, Lemma 7's composite mode is again `1`, rather than a high mode.  Nevertheless
the composite replaces two leading mode-`1` letters by one.  Strong induction on word length,
together with exact-skeleton representative normalisation, therefore closes this exceptional case.
-/

namespace VOA

open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- Exact-skeleton replacement preserves the property that every mode index is `1`. -/
theorem gnLevelOne_allOne_of_skeleton_eq {l l₀ : List (GNLetter 𝒱)}
    (hsk : gnLink2Skeleton l = gnLink2Skeleton l₀)
    (hall : ∀ p ∈ l₀, p.2.2 = 1) : ∀ p ∈ l, p.2.2 = 1 := by
  intro p hp
  have hpSk : p.2.2 ∈ gnLink2Skeleton l := by
    exact List.mem_map_of_mem hp
  rw [hsk] at hpSk
  rcases List.mem_map.mp hpSk with ⟨q, hq, hqp⟩
  have hqOne := hall q hq
  omega

/-- The second Lemma 7 family is lower-grade at target mode `1`. -/
theorem gnLevelOne_familyB_mem_lower (W : VertexOperatorAlgebra 𝒱)
    {a b : 𝒱} {wa wb G : ℕ} (ha : a ∈ W.grading (wa : ℤ))
    (hb : b ∈ W.grading (wb : ℤ)) (hwa : 1 ≤ wa) (hwb : 1 ≤ wb)
    {rest : List (GNLetter 𝒱)} (hrestOK : GNWordOK W rest)
    (hgrade : wa + wb + gnWordGrade rest ≤ G) :
    (∑ᶠ i : ℕ, W.smul b (-2 * (1 : ℤ) - (i : ℤ))
      (W.smul a (i : ℤ) (gnWord W rest W.vacuum))) ∈ gnGradeFil W (G - 1) := by
  apply gnLink4_finsum_mem_of_support_finite _ _
    (gnLink4_familyB_support_finite W a b (gnWord W rest W.vacuum) 0)
  intro i
  exact gnLink4_familyB_term_mem_lower (N := 0) W ha hb hwa hwb hrestOK hgrade i

/-- Every positive generator word whose mode indices are all `1` belongs to the grade-bounded
target at cutoff `1`.  The induction decreases the length of Lemma 7's same-grade composite;
both infinite families and every representative-normalisation error are absorbed by the strict
outer-grade hypothesis. -/
theorem gnLevelOne_generator_word_mem_bounded (W : VertexOperatorAlgebra 𝒱) {g : ℕ}
    (gen : Fin g → 𝒱) (wt : Fin g → ℕ)
    (hgen : ∀ i, gen i ∈ W.grading (wt i : ℤ)) (hwt : ∀ i, 1 ≤ wt i)
    (hdec : (⊤ : Submodule ℂ 𝒱) =
      Submodule.span ℂ (Set.range gen ∪ {W.vacuum}) ⊔ O₂ W)
    {G : ℕ} (hLower : ∀ G' < G, GNReachBounded W gen wt G' 1)
    {l : List (GNLetter 𝒱)} (hOK : GNWordOK W l) (hover : OverGens gen wt l)
    (hgrade : gnWordGrade l ≤ G) (hallOne : ∀ p ∈ l, p.2.2 = 1) :
    gnWord W l W.vacuum ∈ gnSpanBounded W gen wt G 1 := by
  let P : ℕ → Prop := fun n => ∀ l : List (GNLetter 𝒱), l.length = n →
    GNWordOK W l → OverGens gen wt l → gnWordGrade l ≤ G →
      (∀ p ∈ l, p.2.2 = 1) →
        gnWord W l W.vacuum ∈ gnSpanBounded W gen wt G 1
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      dsimp only [P]
      intro l hlen hOK hover hgrade hallOne
      cases l with
      | nil =>
          exact Submodule.subset_span
            ⟨[], hOK, hgrade, by simp [GNWeakDec], by simp [GNNoRepeatLE], hover, rfl⟩
      | cons p tail =>
        cases tail with
        | nil =>
            exact Submodule.subset_span
              ⟨[p], hOK, hgrade, by simp [GNWeakDec], by simp [GNNoRepeatLE], hover, rfl⟩
        | cons q rest =>
          rcases p with ⟨a, wa, ka⟩
          rcases q with ⟨b, wb, kb⟩
          have hka : ka = 1 := hallOne (a, wa, ka) (by simp)
          have hkb : kb = 1 := hallOne (b, wb, kb) (by simp)
          subst ka
          subst kb
          have ha : a ∈ W.grading (wa : ℤ) := hOK.head_mem
          have hb : b ∈ W.grading (wb : ℤ) := hOK.tail.head_mem
          have hrestOK : GNWordOK W rest := hOK.tail.tail
          have hrestOne : ∀ p ∈ rest, p.2.2 = 1 := by
            intro r hr
            exact hallOne r (by simp [hr])
          have hwa : 1 ≤ wa := by
            obtain ⟨i, _, hiwt⟩ := hover (a, wa, 1) (by simp)
            change wa = wt i at hiwt
            rw [hiwt]
            exact hwt i
          have hwb : 1 ≤ wb := by
            obtain ⟨i, _, hiwt⟩ := hover (b, wb, 1) (by simp)
            change wb = wt i at hiwt
            rw [hiwt]
            exact hwt i
          have hrestPos : ∀ p ∈ rest, 1 ≤ p.2.1 := by
            intro r hr
            obtain ⟨i, _, hiwt⟩ := hover r (by simp [hr])
            rw [hiwt]
            exact hwt i
          have hgrade' : wa + wb + gnWordGrade rest ≤ G := by
            simpa only [gnWordGrade_cons, Nat.add_assoc] using hgrade
          have hG : 1 ≤ G := by omega
          have hlower : gnGradeFil W (G - 1) ≤ gnSpanBounded W gen wt G 1 :=
            le_trans (hLower (G - 1) (by omega))
              (gnSpanBounded_mono_grade W gen wt (by omega))
          let c : 𝒱 := W.smul a (-1) b
          let lc : List (GNLetter 𝒱) := (c, wa + wb, 1) :: rest
          have hlcOK : GNWordOK W lc := by
            refine ⟨?_, ?_⟩
            · intro r hr
              rcases List.mem_cons.mp hr with rfl | hr
              · exact gnLink4_composite_mem_grading W ha hb
              · exact hrestOK.1 r hr
            · intro r hr
              rcases List.mem_cons.mp hr with rfl | hr
              · simp
              · exact hrestOK.2 r hr
          have hlcPos : ∀ r ∈ lc, 1 ≤ r.2.1 := by
            intro r hr
            rcases List.mem_cons.mp hr with rfl | hr
            · dsimp [lc]
              omega
            · exact hrestPos r hr
          have hlcGrade : gnWordGrade lc ≤ G := by
            simpa only [lc, gnWordGrade_cons] using hgrade'
          have hlcOne : ∀ r ∈ lc, r.2.2 = 1 := by
            intro r hr
            rcases List.mem_cons.mp hr with rfl | hr
            · rfl
            · exact hrestOne r hr
          have hnorm := gnLink2_word_mem_rawSkeletonSpan_sup_lower
            W gen wt hgen hdec lc hlcOK hlcPos
          rw [Submodule.mem_sup] at hnorm
          obtain ⟨x, hx, y, hy, hxy⟩ := hnorm
          have hxTarget : x ∈ gnSpanBounded W gen wt G 1 := by
            refine Submodule.span_induction
              (p := fun x _ => x ∈ gnSpanBounded W gen wt G 1) ?_ ?_ ?_ ?_ hx
            · rintro z ⟨l', hl'OK, hl'Over, hl'Grade, hl'Sk, rfl⟩
              have hl'Len : l'.length = lc.length := by
                have h := congrArg List.length hl'Sk
                simpa [gnLink2Skeleton] using h
              have hl'One : ∀ r ∈ l', r.2.2 = 1 :=
                gnLevelOne_allOne_of_skeleton_eq hl'Sk hlcOne
              have hl'GradeG : gnWordGrade l' ≤ G := le_trans hl'Grade hlcGrade
              have hnShape : n = rest.length + 2 := by
                simpa using hlen.symm
              have hl'Lt : l'.length < n := by
                rw [hl'Len]
                simp only [lc, List.length_cons]
                omega
              exact ih l'.length hl'Lt l' rfl hl'OK hl'Over hl'GradeG hl'One
            · exact Submodule.zero_mem _
            · intro u v _ _ hu hv
              exact Submodule.add_mem _ hu hv
            · intro r u _ hu
              exact Submodule.smul_mem _ r hu
          have hyTarget : y ∈ gnSpanBounded W gen wt G 1 := by
            have hlcGradePos : 1 ≤ gnWordGrade lc := by
              simp only [lc, gnWordGrade_cons]
              omega
            have hyFil : y ∈ gnGradeFil W (gnWordGrade lc - 1) := by
              simpa [gnLink2LowerFil, Nat.ne_of_gt hlcGradePos] using hy
            have hySmall : y ∈ gnSpanBounded W gen wt (gnWordGrade lc - 1) 1 :=
              hLower (gnWordGrade lc - 1) (by omega) hyFil
            exact gnSpanBounded_mono_grade W gen wt (by omega) hySmall
          have hcompWord : gnWord W lc W.vacuum ∈ gnSpanBounded W gen wt G 1 := by
            rw [← hxy]
            exact Submodule.add_mem _ hxTarget hyTarget
          have hcomp : W.smul (W.smul a (-1) b) (-2 * (1 : ℤ) + 1)
              (gnWord W rest W.vacuum) ∈ gnSpanBounded W gen wt G 1 := by
            simpa [lc, c] using hcompWord
          have hA := hlower
            (gnLink4_familyA_levelOne_mem_lower W ha hb hwa hwb hrestOK hgrade')
          have hB := hlower
            (gnLevelOne_familyB_mem_lower W ha hb hwa hwb hrestOK hgrade')
          rw [gnWord_repeatedHead W a b wa wb 1 (by omega) rest]
          exact (gnSpanBounded W gen wt G 1).sub_mem
            ((gnSpanBounded W gen wt G 1).sub_mem hcomp hA) hB
  exact hP l.length l rfl hOK hover hgrade hallOne

/-- The exceptional bounded successor from repetition cutoff `0` to cutoff `1`.  Link 3 moves
the repeated pair to the head.  If the resulting word still contains a mode above `1`, bounded
high-mode normalisation applies; otherwise every mode is `1`, and the strong length induction
above closes the word. -/
theorem gnLevelOne_GNReachBounded_succ (W : VertexOperatorAlgebra 𝒱)
    {g : ℕ} {gen : Fin g → 𝒱} {wt : Fin g → ℕ}
    (hgen : ∀ i, gen i ∈ W.grading (wt i : ℤ))
    (hwt : ∀ i, 1 ≤ wt i)
    (hdec : (⊤ : Submodule ℂ 𝒱) =
      Submodule.span ℂ (Set.range gen ∪ {W.vacuum}) ⊔ O₂ W)
    {G : ℕ} (hR : GNReachBounded W gen wt G 0)
    (hLower : ∀ G' < G, GNReachBounded W gen wt G' 1) :
    GNReachBounded W gen wt G 1 := by
  by_cases hG0 : G = 0
  · subst G
    exact le_trans hR (gnLink4_gnSpanBounded_zero_mono_index W gen wt hwt 0)
  · have hG : 1 ≤ G := Nat.one_le_iff_ne_zero.mpr hG0
    have hlower : gnGradeFil W (G - 1) ≤ gnSpanBounded W gen wt G 1 :=
      le_trans (hLower (G - 1) (by omega))
        (gnSpanBounded_mono_grade W gen wt (by omega))
    apply GNReachBounded_succ_of_repeatedHead hwt hR
      (hLower (G - 1) (by omega))
    intro A B rest hOK hgrade _hnr hover _hAidx _hBidx
    have hpos : ∀ p ∈ A :: B :: rest, 1 ≤ p.2.1 := by
      intro p hp
      obtain ⟨i, _, hiwt⟩ := hover p hp
      change p.2.1 = wt i at hiwt
      rw [hiwt]
      exact hwt i
    by_cases hhigh : ∃ p ∈ A :: B :: rest, 1 < p.2.2
    · exact gnLink4_word_mem_bounded_of_contains_high W hgen hwt hdec hLower hlower
        (A :: B :: rest) hOK hpos hgrade hhigh
    · have hallOne : ∀ p ∈ A :: B :: rest, p.2.2 = 1 :=
        gnLink4_all_indices_one_of_no_high W hOK hhigh
      exact gnLevelOne_generator_word_mem_bounded W gen wt hgen hwt hdec hLower
        hOK hover hgrade hallOne

end VOA
