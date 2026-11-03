/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.GNBoundedReach
import VOA.Modularity.GNSortingLink1

/-!
# Gaberdiel--Neitzke Prop. 8, Link 3: permutation and block-migration bookkeeping

This file packages the repeated use of `gnWord_swap_sub_mem_ctx`: any permutation of a
positive-weight admissible word changes its value only by the next lower GN grade.  In particular,
the repeated block at mode `N + 1` may be migrated to the head before applying GN Lemma 7.
-/

namespace VOA

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- `GNWordOK` is invariant under permutation. -/
theorem GNWordOK.perm {W : VertexOperatorAlgebra 𝒱} {l₁ l₂ : List (GNLetter 𝒱)}
    (h : GNWordOK W l₁) (hp : l₁.Perm l₂) : GNWordOK W l₂ := by
  refine ⟨fun p hp₂ => h.1 p (hp.mem_iff.mpr hp₂), fun p hp₂ => h.2 p (hp.mem_iff.mpr hp₂)⟩

/-- The GN word grade is invariant under permutation. -/
theorem gnWordGrade_perm {l₁ l₂ : List (GNLetter 𝒱)} (hp : l₁.Perm l₂) :
    gnWordGrade l₁ = gnWordGrade l₂ := by
  exact (hp.map (fun p : GNLetter 𝒱 => p.2.1)).sum_nat

/-- A pointwise predicate is transported along a permutation. -/
theorem gnForall_mem_perm {P : GNLetter 𝒱 → Prop} {l₁ l₂ : List (GNLetter 𝒱)}
    (hp : l₁.Perm l₂) (h : ∀ p ∈ l₁, P p) : ∀ p ∈ l₂, P p :=
  fun p hp₂ => h p (hp.mem_iff.mpr hp₂)

/-- Being over the chosen generators is invariant under permutation. -/
theorem OverGens.perm {g : ℕ} {gen : Fin g → 𝒱} {wt : Fin g → ℕ}
    {l₁ l₂ : List (GNLetter 𝒱)} (h : OverGens gen wt l₁) (hp : l₁.Perm l₂) :
    OverGens gen wt l₂ :=
  fun p hp₂ => h p (hp.mem_iff.mpr hp₂)

/-- The no-repeat predicate is invariant under permutation. -/
theorem GNNoRepeatLE.perm {N : ℕ} {l₁ l₂ : List (GNLetter 𝒱)}
    (h : GNNoRepeatLE N l₁) (hp : l₁.Perm l₂) : GNNoRepeatLE N l₂ := by
  exact (hp.pairwise_iff (fun {a b} hab hb ha => (hab ha hb).symm)).mp h

/-- Exchanging letters by an arbitrary permutation costs one GN grade.  This is the telescoped
form of GN Lemma 5 used by the sorting and block-migration arguments. -/
theorem gnWord_perm_sub_mem (W : VertexOperatorAlgebra 𝒱) {l₁ l₂ : List (GNLetter 𝒱)}
    (hp : l₁.Perm l₂) (hOK : GNWordOK W l₁) (hwt : ∀ p ∈ l₁, 1 ≤ p.2.1)
    (G : ℕ) (hle : gnWordGrade l₁ ≤ G + 1) :
    gnWord W l₁ W.vacuum - gnWord W l₂ W.vacuum ∈ gnGradeFil W G := by
  induction hp generalizing G with
  | nil =>
      simp
  | @cons a t₁ t₂ hp ih =>
      have hOKt : GNWordOK W t₁ := hOK.tail
      have hwta : 1 ≤ a.2.1 := hwt a (List.mem_cons_self ..)
      have hwtt : ∀ p ∈ t₁, 1 ≤ p.2.1 :=
        fun p hp => hwt p (List.mem_cons_of_mem _ hp)
      by_cases haG : a.2.1 ≤ G
      · have hlet : gnWordGrade t₁ ≤ (G - a.2.1) + 1 := by
          rw [gnWordGrade_cons] at hle
          omega
        have hi := ih hOKt hwtt (G := G - a.2.1) hlet
        have hhead : GNWordOK W ([a] : List (GNLetter 𝒱)) := by
          refine ⟨?_, ?_⟩
          · intro p hp
            rw [List.mem_singleton] at hp
            subst p
            exact hOK.head_mem
          · intro p hp
            rw [List.mem_singleton] at hp
            subst p
            exact hOK.2 a (List.mem_cons_self ..)
        have hpre := gnGradeFil_prepend W hhead hi
        have hpre' :
            gnWord W (a :: t₁) W.vacuum - gnWord W (a :: t₂) W.vacuum
              ∈ gnGradeFil W (a.2.1 + (G - a.2.1)) := by
          simpa [gnWordGrade, gnWord_append, gnWord_sub] using hpre
        exact gnGradeFil_mono W (by omega) hpre'
      · have htzero : gnWordGrade t₁ = 0 := by
          rw [gnWordGrade_cons] at hle
          omega
        have ht₁ : t₁ = [] := by
          rw [List.eq_nil_iff_forall_not_mem]
          intro p hp
          have hp0 := gnWordGrade_zero_wt htzero p hp
          have hp1 := hwtt p hp
          omega
        have ht₂ : t₂ = [] := by
          subst t₁
          exact hp.symm.eq_nil
        subst t₁
        subst t₂
        simp
  | @swap a b t =>
      exact gnWord_swap_sub_mem W b a t hOK G (by
        rw [gnWordGrade_cons, gnWordGrade_cons] at hle
        omega)
  | @trans t₁ t₂ t₃ hp₁ hp₂ ih₁ ih₂ =>
      have hOK₂ : GNWordOK W t₂ := hOK.perm hp₁
      have hwt₂ : ∀ p ∈ t₂, 1 ≤ p.2.1 := gnForall_mem_perm hp₁ hwt
      have hle₂ : gnWordGrade t₂ ≤ G + 1 := by
        rw [← gnWordGrade_perm hp₁]
        exact hle
      have h₁ := ih₁ hOK hwt (G := G) hle
      have h₂ := ih₂ hOK₂ hwt₂ (G := G) hle₂
      have hadd := (gnGradeFil W G).add_mem h₁ h₂
      convert hadd using 1 <;> abel

/-- Moving a repeated pair through a prefix is a special case of the permutation congruence. -/
theorem gnWord_migratePair_sub_mem (W : VertexOperatorAlgebra 𝒱)
    (pre : List (GNLetter 𝒱)) (a b : GNLetter 𝒱) (rest : List (GNLetter 𝒱))
    (hOK : GNWordOK W (pre ++ a :: b :: rest))
    (hwt : ∀ p ∈ pre ++ a :: b :: rest, 1 ≤ p.2.1)
    (G : ℕ) (hle : gnWordGrade (pre ++ a :: b :: rest) ≤ G + 1) :
    gnWord W (pre ++ a :: b :: rest) W.vacuum
        - gnWord W (a :: b :: pre ++ rest) W.vacuum ∈ gnGradeFil W G := by
  have hp : (pre ++ a :: b :: rest).Perm (a :: b :: pre ++ rest) := by
    simpa only [List.append_assoc] using
      (List.perm_append_comm_assoc pre ([a, b] : List (GNLetter 𝒱)) rest)
  have hbase := gnWord_perm_sub_mem_grade W hp hOK hwt
  exact gnGradeFil_mono W (by omega) hbase

/-! ## The grade-bounded successor reduction -/

/-- In the strengthened invariant, the successor step reduces to grade-bounded words containing a
repeated `N + 1` block. -/
theorem gnSpanBounded_succ_of_repeatCase {W : VertexOperatorAlgebra 𝒱} {g : ℕ}
    {gen : Fin g → 𝒱} {wt : Fin g → ℕ} {gr N : ℕ}
    (hrep : ∀ l : List (GNLetter 𝒱), GNWordOK W l → gnWordGrade l ≤ gr →
      GNWeakDec l → GNNoRepeatLE N l → OverGens gen wt l → 2 ≤ gnCountAt (N + 1) l →
      gnWord W l W.vacuum ∈ gnSpanBounded W gen wt gr (N + 1)) :
    gnSpanBounded W gen wt gr N ≤ gnSpanBounded W gen wt gr (N + 1) := by
  classical
  rw [gnSpanBounded, Submodule.span_le]
  rintro x ⟨l, hOK, hgrade, hweak, hrepeat, hover, rfl⟩
  by_cases hs : 2 ≤ gnCountAt (N + 1) l
  · exact hrep l hOK hgrade hweak hrepeat hover hs
  · exact Submodule.subset_span
      ⟨l, hOK, hgrade, hweak, gnNoRepeatLE_succ_of_count hweak hrepeat (by omega), hover, rfl⟩

/-- Bounded reach at `(gr,N)` advances once all repeated-block words of grade at most `gr` are
handled. -/
theorem GNReachBounded_succ_of_repeatCase {W : VertexOperatorAlgebra 𝒱} {g : ℕ}
    {gen : Fin g → 𝒱} {wt : Fin g → ℕ} {gr N : ℕ}
    (hR : GNReachBounded W gen wt gr N)
    (hrep : ∀ l : List (GNLetter 𝒱), GNWordOK W l → gnWordGrade l ≤ gr →
      GNWeakDec l → GNNoRepeatLE N l → OverGens gen wt l → 2 ≤ gnCountAt (N + 1) l →
      gnWord W l W.vacuum ∈ gnSpanBounded W gen wt gr (N + 1)) :
    GNReachBounded W gen wt gr (N + 1) :=
  le_trans hR (gnSpanBounded_succ_of_repeatCase hrep)

/-- **Link 3, block migration.**  Assuming lower-grade bounded reach, the whole successor step
reduces to words whose repeated pair is already at the head.  The migration itself is the
permutation congruence above; its error is absorbed at grade `gr - 1`. -/
theorem GNReachBounded_succ_of_repeatedHead {W : VertexOperatorAlgebra 𝒱} {g : ℕ}
    {gen : Fin g → 𝒱} {wt : Fin g → ℕ} {gr N : ℕ}
    (hwt : ∀ i, 1 ≤ wt i)
    (hR : GNReachBounded W gen wt gr N)
    (hLower : GNReachBounded W gen wt (gr - 1) (N + 1))
    (hhead : ∀ (a b : GNLetter 𝒱) (rest : List (GNLetter 𝒱)),
      GNWordOK W (a :: b :: rest) → gnWordGrade (a :: b :: rest) ≤ gr →
      GNNoRepeatLE N (a :: b :: rest) → OverGens gen wt (a :: b :: rest) →
      a.2.2 = N + 1 → b.2.2 = N + 1 →
      gnWord W (a :: b :: rest) W.vacuum ∈ gnSpanBounded W gen wt gr (N + 1)) :
    GNReachBounded W gen wt gr (N + 1) := by
  apply GNReachBounded_succ_of_repeatCase hR
  intro l hOK hgrade hweak hrepeat hover hs
  obtain ⟨pre, mid, post, hEq, hpre, hmid, hpost⟩ := gnWeakDec_split (N + 1) l hweak
  have hlen : 2 ≤ mid.length := by
    rw [← gnWeakDec_split_lengths hEq hmid hpre hpost]
    exact hs
  obtain _ | ⟨a, mid⟩ := mid
  · simp at hlen
  obtain _ | ⟨b, tail⟩ := mid
  · simp at hlen
  let rest : List (GNLetter 𝒱) := tail ++ post
  have hlform : l = pre ++ a :: b :: rest := by
    rw [hEq]
    simp only [rest, List.append_assoc, List.cons_append]
  have hp : (pre ++ a :: b :: rest).Perm (a :: b :: pre ++ rest) := by
    simpa only [List.append_assoc] using
      (List.perm_append_comm_assoc pre ([a, b] : List (GNLetter 𝒱)) rest)
  have hOKsrc : GNWordOK W (pre ++ a :: b :: rest) := by simpa [hlform] using hOK
  have hgradesrc : gnWordGrade (pre ++ a :: b :: rest) ≤ gr := by simpa [hlform] using hgrade
  have hrepsrc : GNNoRepeatLE N (pre ++ a :: b :: rest) := by simpa [hlform] using hrepeat
  have hoversrc : OverGens gen wt (pre ++ a :: b :: rest) := by simpa [hlform] using hover
  have hwtsrc : ∀ p ∈ pre ++ a :: b :: rest, 1 ≤ p.2.1 := by
    intro p hpMem
    obtain ⟨i, _, hi⟩ := hoversrc p hpMem
    rw [hi]
    exact hwt i
  have haidx : a.2.2 = N + 1 := hmid a (by simp)
  have hbidx : b.2.2 = N + 1 := hmid b (by simp)
  have haMem : a ∈ pre ++ a :: b :: rest := List.mem_append_right _ (by simp)
  have hapos : 1 ≤ a.2.1 := hwtsrc a haMem
  have hale : a.2.1 ≤ gnWordGrade (pre ++ a :: b :: rest) := by
    rw [gnWordGrade]
    exact List.single_le_sum (fun _ _ => Nat.zero_le _) a.2.1
      (List.mem_map_of_mem haMem)
  have hgrpos : 1 ≤ gr := le_trans hapos (le_trans hale hgradesrc)
  have hmig := gnWord_migratePair_sub_mem W pre a b rest hOKsrc hwtsrc (gr - 1) (by omega)
  have herrSmall :
      gnWord W (pre ++ a :: b :: rest) W.vacuum
          - gnWord W (a :: b :: pre ++ rest) W.vacuum
        ∈ gnSpanBounded W gen wt (gr - 1) (N + 1) := hLower hmig
  have herr :
      gnWord W (pre ++ a :: b :: rest) W.vacuum
          - gnWord W (a :: b :: pre ++ rest) W.vacuum
        ∈ gnSpanBounded W gen wt gr (N + 1) :=
    gnSpanBounded_mono_grade W gen wt (by omega) herrSmall
  have hmain : gnWord W (a :: b :: pre ++ rest) W.vacuum
      ∈ gnSpanBounded W gen wt gr (N + 1) := by
    apply hhead a b (pre ++ rest)
    · exact hOKsrc.perm hp
    · rw [gnWordGrade_cons, gnWordGrade_cons, gnWordGrade_append]
      rw [gnWordGrade_append, gnWordGrade_cons, gnWordGrade_cons] at hgradesrc
      omega
    · exact hrepsrc.perm hp
    · exact hoversrc.perm hp
    · exact haidx
    · exact hbidx
  rw [hlform]
  have hadd := (gnSpanBounded W gen wt gr (N + 1)).add_mem herr hmain
  convert hadd using 1 <;> abel

end VOA
