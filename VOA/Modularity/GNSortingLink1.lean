/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.GNSwap

/-!
# Gaberdiel--Neitzke Prop. 8, Link 1: sorting mode words

This file supplies the combinatorial termination argument needed to iterate
`gnWord_swap_sub_mem_ctx`.  An inversion is a pair of letters whose mode indices occur in
strictly increasing order.  Swapping an adjacent inversion lowers the inversion count by exactly
one.  The resulting well-founded induction sorts a word into weakly decreasing order, and the
VOA-level corollary records that the sorting error has strictly smaller GN grade.

The VOA-level result assumes positive conformal weight for every letter.  This is the precise
hypothesis needed by the context swap lemma to bound the grade of the prefix, and it is supplied
downstream by the positive-weight `C₂` representatives.
-/

namespace VOA

universe u

variable {𝒱 : Type u}

/-! ## The inversion measure -/

/-- The number of pairs occurring in the wrong order for `GNWeakDec`. -/
def gnInversions : List (GNLetter 𝒱) → ℕ
  | [] => 0
  | p :: l => (l.filter fun q => p.2.2 < q.2.2).length + gnInversions l

@[simp] theorem gnInversions_nil : gnInversions ([] : List (GNLetter 𝒱)) = 0 := rfl

@[simp] theorem gnInversions_cons (p : GNLetter 𝒱) (l : List (GNLetter 𝒱)) :
    gnInversions (p :: l) = (l.filter fun q => p.2.2 < q.2.2).length + gnInversions l := rfl

private theorem filter_length_swap (r : GNLetter 𝒱 → Prop) [DecidablePred r]
    (pre : List (GNLetter 𝒱)) (p q : GNLetter 𝒱) (rest : List (GNLetter 𝒱)) :
    ((pre ++ p :: q :: rest).filter r).length =
      ((pre ++ q :: p :: rest).filter r).length := by
  simp only [List.filter_append, List.length_append, List.filter_cons]
  by_cases hp : r p <;> by_cases hq : r q <;> simp [hp, hq, Nat.add_comm, Nat.add_left_comm]

/-- Swapping an adjacent inversion lowers `gnInversions` by exactly one, in any context. -/
theorem gnInversions_swap_adjacent (pre : List (GNLetter 𝒱)) (p q : GNLetter 𝒱)
    (rest : List (GNLetter 𝒱)) (hpq : p.2.2 < q.2.2) :
    gnInversions (pre ++ p :: q :: rest) =
      gnInversions (pre ++ q :: p :: rest) + 1 := by
  induction pre with
  | nil =>
      simp only [List.nil_append, gnInversions_cons, List.filter_cons]
      have hqp : ¬q.2.2 < p.2.2 := Nat.not_lt_of_ge (Nat.le_of_lt hpq)
      simp [hpq, hqp]
      omega
  | cons r pre ih =>
      simp only [List.cons_append, gnInversions_cons]
      rw [filter_length_swap]
      omega

/-- The strict-decrease form of `gnInversions_swap_adjacent`, used as the recursive call guard. -/
theorem gnInversions_swap_adjacent_lt (pre : List (GNLetter 𝒱)) (p q : GNLetter 𝒱)
    (rest : List (GNLetter 𝒱)) (hpq : p.2.2 < q.2.2) :
    gnInversions (pre ++ q :: p :: rest) < gnInversions (pre ++ p :: q :: rest) := by
  rw [gnInversions_swap_adjacent pre p q rest hpq]
  exact Nat.lt_succ_self _

/-- A word which is not weakly decreasing contains an adjacent inversion. -/
theorem exists_adjacent_inversion_of_not_weakDec {l : List (GNLetter 𝒱)}
    (h : ¬GNWeakDec l) :
    ∃ pre : List (GNLetter 𝒱), ∃ p q : GNLetter 𝒱, ∃ rest : List (GNLetter 𝒱),
      l = pre ++ p :: q :: rest ∧ p.2.2 < q.2.2 := by
  let R : GNLetter 𝒱 → GNLetter 𝒱 → Prop := fun a b => b.2.2 ≤ a.2.2
  letI : Trans R R R := ⟨fun hab hbc => le_trans hbc hab⟩
  have hchain : ¬List.IsChain R l := by
    intro hl
    exact h (List.isChain_iff_pairwise.mp hl)
  rw [List.isChain_iff_forall_rel_of_append_cons_cons] at hchain
  push Not at hchain
  obtain ⟨p, q, pre, rest, heq, hpq⟩ := hchain
  exact ⟨pre, p, q, rest, heq, Nat.lt_of_not_ge hpq⟩

/-! ## Well-founded adjacent-swap recursion -/

/-- Well-founded induction for sorting GN words by adjacent inversions.  The step receives the
already-proved result for the word after swapping one adjacent inversion. -/
theorem gnSortingInduction {P : List (GNLetter 𝒱) → Prop}
    (sorted : ∀ l, GNWeakDec l → P l)
    (swap : ∀ (pre : List (GNLetter 𝒱)) (p q : GNLetter 𝒱)
      (rest : List (GNLetter 𝒱)), p.2.2 < q.2.2 →
        P (pre ++ q :: p :: rest) → P (pre ++ p :: q :: rest)) :
    ∀ l, P l := by
  intro l
  induction l using (measure gnInversions).wf.induction with
  | h l ih =>
      by_cases hwd : GNWeakDec l
      · exact sorted l hwd
      · obtain ⟨pre, p, q, rest, rfl, hpq⟩ :=
          exists_adjacent_inversion_of_not_weakDec hwd
        apply swap pre p q rest hpq
        apply ih (pre ++ q :: p :: rest)
        change gnInversions (pre ++ q :: p :: rest) <
          gnInversions (pre ++ p :: q :: rest)
        exact gnInversions_swap_adjacent_lt pre p q rest hpq

/-- Every GN word can be sorted into weakly decreasing order using adjacent inversion swaps. -/
theorem exists_weakDec_perm (l : List (GNLetter 𝒱)) :
    ∃ l' : List (GNLetter 𝒱), l.Perm l' ∧ GNWeakDec l' := by
  refine gnSortingInduction
    (P := fun l => ∃ l' : List (GNLetter 𝒱), l.Perm l' ∧ GNWeakDec l') ?_ ?_ l
  · intro l hwd
    exact ⟨l, List.Perm.refl l, hwd⟩
  · intro pre p q rest _ ih
    obtain ⟨l', hperm, hwd⟩ := ih
    refine ⟨l', ?_, hwd⟩
    exact (List.Perm.append_left pre (List.Perm.swap p q rest).symm).trans hperm

/-! ## Sorting modulo lower GN grade -/

section VOA

variable [AddCommGroup 𝒱] [Module ℂ 𝒱]

private theorem eq_nil_of_gnWordGrade_eq_zero_of_pos {l : List (GNLetter 𝒱)}
    (hwt : ∀ p ∈ l, 1 ≤ p.2.1) (hgrade : gnWordGrade l = 0) : l = [] := by
  cases l with
  | nil => rfl
  | cons p rest =>
      have hp := hwt p (List.mem_cons_self ..)
      rw [gnWordGrade_cons] at hgrade
      omega

omit [AddCommGroup 𝒱] [Module ℂ 𝒱] in
/-- The GN grade is invariant under permutation of the letters. -/
theorem gnWordGrade_eq_of_perm {l₁ l₂ : List (GNLetter 𝒱)} (hperm : l₁.Perm l₂) :
    gnWordGrade l₁ = gnWordGrade l₂ := by
  unfold gnWordGrade
  exact List.Perm.sum_eq (hperm.map fun p : GNLetter 𝒱 => p.2.1)

/-- Admissibility is invariant under permutation of the letters. -/
theorem gnWordOK_of_perm (W : VertexOperatorAlgebra 𝒱) {l₁ l₂ : List (GNLetter 𝒱)}
    (hperm : l₁.Perm l₂) (hOK : VOA.GNWordOK W l₁) :
    VOA.GNWordOK W l₂ :=
  ⟨fun p hp => hOK.1 p (hperm.mem_iff.mpr hp),
    fun p hp => hOK.2 p (hperm.mem_iff.mpr hp)⟩

/-- Permuting an admissible positive-weight word changes its value by a vector of grade at most
`gnWordGrade l₁ - 1`.  This stronger permutation brick is independent of the sorting algorithm. -/
theorem gnWord_perm_sub_mem_grade (W : VertexOperatorAlgebra 𝒱)
    {l₁ l₂ : List (GNLetter 𝒱)} (hperm : l₁.Perm l₂) :
    VOA.GNWordOK W l₁ → (∀ p ∈ l₁, 1 ≤ p.2.1) →
      gnWord W l₁ W.vacuum - gnWord W l₂ W.vacuum ∈
        gnGradeFil W (gnWordGrade l₁ - 1) := by
  induction hperm with
  | nil =>
      intro _ _
      simp
  | @cons p l₁ l₂ hperm ih =>
      intro hOK hwt
      have hOKtail : VOA.GNWordOK W l₁ := hOK.tail
      have hwttail : ∀ q ∈ l₁, 1 ≤ q.2.1 :=
        fun q hq => hwt q (List.mem_cons_of_mem _ hq)
      by_cases hzero : gnWordGrade l₁ = 0
      · have hl₁ : l₁ = [] := eq_nil_of_gnWordGrade_eq_zero_of_pos hwttail hzero
        subst l₁
        have hl₂ : l₂ = [] := hperm.symm.eq_nil
        subst l₂
        simp
      · have htail := ih hOKtail hwttail
        have hpOK : VOA.GNWordOK W [p] := by
          refine ⟨?_, ?_⟩
          · intro q hq
            rw [List.mem_singleton] at hq
            subst q
            exact hOK.head_mem
          · intro q hq
            rw [List.mem_singleton] at hq
            subst q
            exact hOK.2 p (List.mem_cons_self ..)
        have hpre := gnGradeFil_prepend W hpOK htail
        have hword : gnWord W [p]
            (gnWord W l₁ W.vacuum - gnWord W l₂ W.vacuum) =
            gnWord W (p :: l₁) W.vacuum - gnWord W (p :: l₂) W.vacuum := by
          rw [gnWord_sub]
          rfl
        rw [hword] at hpre
        have hidx : p.2.1 + (gnWordGrade l₁ - 1) = gnWordGrade (p :: l₁) - 1 := by
          rw [gnWordGrade_cons]
          omega
        have hpgrade : gnWordGrade ([p] : List (GNLetter 𝒱)) = p.2.1 := by simp
        rw [hpgrade, hidx] at hpre
        exact hpre
  | @swap p q rest =>
      intro hOK hwt
      have hpwt : 1 ≤ p.2.1 := hwt p (by simp)
      have hqwt : 1 ≤ q.2.1 := hwt q (by simp)
      apply gnWord_swap_sub_mem W q p rest hOK (gnWordGrade (q :: p :: rest) - 1)
      rw [gnWordGrade_cons, gnWordGrade_cons]
      omega
  | @trans l₁ l₂ l₃ hperm₁ hperm₂ ih₁ ih₂ =>
      intro hOK hwt
      have hOK₂ := gnWordOK_of_perm W hperm₁ hOK
      have hwt₂ : ∀ p ∈ l₂, 1 ≤ p.2.1 :=
        fun p hp => hwt p (hperm₁.mem_iff.mpr hp)
      have h₁ := ih₁ hOK hwt
      have h₂ := ih₂ hOK₂ hwt₂
      have hgrade := gnWordGrade_eq_of_perm hperm₁
      rw [← hgrade] at h₂
      have hadd := Submodule.add_mem (gnGradeFil W (gnWordGrade l₁ - 1)) h₁ h₂
      convert hadd using 1
      all_goals abel

/-- Sorting an admissible positive-weight word changes its value only by a vector of one lower GN
grade.  The sorted word is a permutation of the original, so all pointwise letter properties are
preserved. -/
theorem gnWord_sort_mod_lower (W : VertexOperatorAlgebra 𝒱) (l : List (GNLetter 𝒱))
    (hOK : VOA.GNWordOK W l) (hwt : ∀ p ∈ l, 1 ≤ p.2.1) (G : ℕ)
    (hgrade : gnWordGrade l ≤ G + 1) :
    ∃ l' : List (GNLetter 𝒱), l.Perm l' ∧ VOA.GNWordOK W l' ∧ GNWeakDec l' ∧
      gnWord W l W.vacuum - gnWord W l' W.vacuum ∈ gnGradeFil W G := by
  obtain ⟨l', hperm, hwd⟩ := exists_weakDec_perm l
  exact ⟨l', hperm, gnWordOK_of_perm W hperm hOK, hwd,
    gnGradeFil_mono W (by omega) (gnWord_perm_sub_mem_grade W hperm hOK hwt)⟩

end VOA

end VOA
