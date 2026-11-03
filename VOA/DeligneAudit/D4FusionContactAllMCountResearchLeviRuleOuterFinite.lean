import VOA.DeligneAudit.D4FusionContactAllMCountResearchLeviRuleCutoffs
import VOA.DeligneAudit.D4FusionContactAllMCountResearchLeviRuleReorder
import Mathlib.Data.Set.Finite.List

/-! Actual finite outer-current source families, from the proved source-power
bounds. No outer-word finiteness or dimension premise is assumed. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.LeviRules
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.D4FusionContact.Polynomial
noncomputable section

/-- Every word containing an out-of-cutoff current operator kills the whole input. -/
theorem outer_word_high_zero (K : Type*) [Field K] (m : ℕ)
    (l : List (Fin 18 × ℕ)) (p : Ring K m) (hl : ∃ x ∈ l, m ≤ x.2) :
    wordOp (representation K m) l p = 0 := by
  induction l with
  | nil =>
      obtain ⟨x,hx,_⟩ := hl
      simp only [List.not_mem_nil] at hx
  | cons x l ih =>
      obtain ⟨y,hy,hh⟩ := hl
      rcases List.mem_cons.mp hy with hy | hy
      · subst y
        change deriv K m x.1 x.2 (wordOp (representation K m) l p) = 0
        rw [deriv_high K m x.1 x.2 hh,Derivation.zero_apply]
      · change deriv K m x.1 x.2 (wordOp (representation K m) l p) = 0
        rw [ih ⟨y,hy,hh⟩,map_zero]

theorem sourceWord_outer_modes_lt (m : ℕ) (j : AllM.SeedIndex m) (modes : List ℕ)
    (l : List (Fin 18 × ℕ)) (hne : sourceWord m j modes l ≠ 0) :
    ∀ x ∈ l, x.2 < m := by
  intro x hx
  by_contra hh
  exact hne (outer_word_high_zero ℂ m l _ ⟨x,hx,Nat.le_of_not_gt hh⟩)

/-- Every surviving C outer word has at most its original number of C factors. -/
theorem c_sourceWord_length_le (m : ℕ) (j : AllM.SeedIndex m) (hj : j.val.1 = true)
    (modes : List ℕ) (l : List (Fin 18 × ℕ)) (hl : ∀ x ∈ l, category x.1 = 0)
    (hne : sourceWord m j modes l ≠ 0) : l.length ≤ j.val.2.1 := by
  apply Nat.le_of_not_gt
  intro hh
  exact hne (c_sourceWord_too_many_contacts m j hj modes l hl hh)

/-- The three negative-root axes partition every actual category-one letter. -/
theorem negative_axis_partition : ∀ a : Fin 18, category a = 1 →
    axisIncrement 0 a+axisIncrement 1 a+axisIncrement 2 a = 1 := by decide +kernel

theorem negative_word_axis_partition (l : List (Fin 18 × ℕ))
    (hl : ∀ x ∈ l, category x.1 = 1) :
    wordGrade (axisIncrement 0) 0 l+wordGrade (axisIncrement 1) 0 l+
      wordGrade (axisIncrement 2) 0 l = (l.length : ℤ) := by
  induction l with
  | nil => simp only [wordGrade,List.map_nil,List.sum_nil,add_zero,List.length_nil,Nat.cast_zero]
  | cons x l ih =>
      have hx := negative_axis_partition x.1 (hl x (List.mem_cons_self))
      have ht := ih (fun y hy => hl y (List.mem_cons_of_mem _ hy))
      simp only [wordGrade,List.map_cons,List.sum_cons,zero_mul,add_zero,
        List.length_cons,Nat.cast_add,Nat.cast_one] at ht ⊢
      omega

/-- Every surviving U word uses each negative-root direction at most r times. -/
theorem u_sourceWord_axis_le (m : ℕ) (j : AllM.SeedIndex m) (hj : j.val.1 = false)
    (modes : List ℕ) (l : List (Fin 18 × ℕ)) (hl : ∀ x ∈ l, category x.1 = 1)
    (hne : sourceWord m j modes l ≠ 0) (d : Fin 3) :
    wordGrade (axisIncrement d) 0 l ≤ j.val.2.1 := by
  apply le_of_not_gt
  intro hh
  exact hne (u_sourceWord_too_many_axis m j hj modes l hl d hh)

/-- In total, a surviving U outer word has length at most three times its power. -/
theorem u_sourceWord_length_le (m : ℕ) (j : AllM.SeedIndex m) (hj : j.val.1 = false)
    (modes : List ℕ) (l : List (Fin 18 × ℕ)) (hl : ∀ x ∈ l, category x.1 = 1)
    (hne : sourceWord m j modes l ≠ 0) : l.length ≤ 3*j.val.2.1 := by
  have h0 := u_sourceWord_axis_le m j hj modes l hl hne 0
  have h1 := u_sourceWord_axis_le m j hj modes l hl hne 1
  have h2 := u_sourceWord_axis_le m j hj modes l hl hne 2
  have hp := negative_word_axis_partition l hl
  have hh : (l.length : ℤ) ≤ 3*(j.val.2.1 : ℤ) := by omega
  exact_mod_cast hh

theorem sourceWord_outer_length_le (m : ℕ) (j : AllM.SeedIndex m) (modes : List ℕ)
    (l : List (Fin 18 × ℕ)) (hl : ∀ x ∈ l, category x.1 = branchCategory j.val.1)
    (hne : sourceWord m j modes l ≠ 0) : l.length ≤ 3*j.val.2.1 := by
  cases hj : j.val.1 with
  | false =>
      apply u_sourceWord_length_le m j hj modes l _ hne
      simpa only [branchCategory,hj,Bool.false_eq_true,if_false] using hl
  | true =>
      have hc : ∀ x ∈ l, category x.1 = 0 := by
        simpa only [branchCategory,hj,if_true] using hl
      have hh := c_sourceWord_length_le m j hj modes l hc hne
      omega

/-- Actual bounded outer words over the finite alphabet of original current modes. -/
def boundedOuterLists (m r : ℕ) (b : Bool) : Set (List (Fin 18 × ℕ)) :=
  {l | l.length ≤ 3*r ∧ ∀ x ∈ l, x.2 < m ∧ category x.1 = branchCategory b}

theorem boundedOuterLists_finite (m r : ℕ) (b : Bool) : (boundedOuterLists m r b).Finite := by
  have hf := (List.finite_length_le (Fin 18 × Fin m) (3*r)).image
    (fun l : List (Fin 18 × Fin m) => l.map (fun x => (x.1,x.2.val)))
  apply hf.subset
  intro l hl
  let v : List (Fin 18 × Fin m) :=
    l.attach.map (fun x => (x.val.1,⟨x.val.2,(hl.2 x.val x.property).1⟩))
  refine ⟨v,?_,?_⟩
  · change v.length ≤ 3*r
    simpa only [v,List.length_map,List.length_attach] using hl.1
  · change (v.map (fun x => (x.1,x.2.val))) = l
    simp only [v,List.map_map,Function.comp_def]
    exact List.attach_map_subtype_val l

/-- Every nonzero original branch source uses an index from this actual finite set. -/
theorem sourceWord_outer_mem_bounded (m : ℕ) (j : AllM.SeedIndex m) (modes : List ℕ)
    (l : List (Fin 18 × ℕ)) (hl : ∀ x ∈ l, category x.1 = branchCategory j.val.1)
    (hne : sourceWord m j modes l ≠ 0) : l ∈ boundedOuterLists m j.val.2.1 j.val.1 := by
  exact ⟨sourceWord_outer_length_le m j modes l hl hne,
    fun x hx => ⟨sourceWord_outer_modes_lt m j modes l hne x hx,hl x hx⟩⟩

def boundedOuterSeedRows (m : ℕ) (j : AllM.SeedIndex m) (modes : List ℕ) : Set (Ring ℂ m) :=
  sourceWord m j modes '' boundedOuterLists m j.val.2.1 j.val.1

theorem boundedOuterSeedRows_finite (m : ℕ) (j : AllM.SeedIndex m) (modes : List ℕ) :
    (boundedOuterSeedRows m j modes).Finite :=
  (boundedOuterLists_finite m j.val.2.1 j.val.1).image _

/-- Exact finite spanning for all original outer words, at each fixed shifted seed. -/
theorem source_outer_span_eq_bounded (m : ℕ) (j : AllM.SeedIndex m) (modes : List ℕ) :
    Submodule.span ℂ {p | ∃ l : List (Fin 18 × ℕ),
      (∀ x ∈ l, category x.1 = branchCategory j.val.1) ∧ p = sourceWord m j modes l} =
      Submodule.span ℂ (boundedOuterSeedRows m j modes) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro p ⟨l,hl,rfl⟩
    by_cases hz : sourceWord m j modes l = 0
    · rw [hz]
      exact Submodule.zero_mem _
    · exact Submodule.subset_span ⟨l,sourceWord_outer_mem_bounded m j modes l hl hz,rfl⟩
  · apply Submodule.span_le.mpr
    rintro p ⟨l,hl,rfl⟩
    exact Submodule.subset_span ⟨l,fun x hx => (hl.2 x hx).2,rfl⟩

end
#print axioms outer_word_high_zero
#print axioms c_sourceWord_length_le
#print axioms u_sourceWord_length_le
#print axioms boundedOuterLists_finite
#print axioms source_outer_span_eq_bounded
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.LeviRules
