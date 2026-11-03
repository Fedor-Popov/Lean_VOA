import VOA.DeligneAudit.D4FusionContactAllMCountResearchLeviRulePBW
import VOA.DeligneAudit.D4FusionContactAllMCountResearchLeviRuleMono

/-! The positive block of a sorted source word kills the original whole
highest-color coefficient. Removing it is a proved source-ideal equality. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.LeviRules
open VOA.DeligneAudit.D4FusionContact.Polynomial
open VOA.DeligneAudit.SectorWeyl
noncomputable section

theorem category_le_three (a : Fin 18) : category a ≤ 3 := by
  unfold category
  split_ifs <;> omega

theorem positive_seed_actual (m : ℕ) (e : Fin 3) (k : ℕ) (j : AllM.SeedIndex m) :
    deriv ℂ m (positive e) k (AllM.seedPoly m j) = 0 := by
  exact positive_seed ℂ m e j.val.1 k j.val.2.1 j.val.2.2

theorem category_three_seed (m : ℕ) (a : Fin 18) (k : ℕ) (j : AllM.SeedIndex m)
    (ha : category a = 3) : deriv ℂ m a k (AllM.seedPoly m j) = 0 := by
  have hb : 4 ≤ a.val ∧ a.val < 7 := by
    unfold category at ha
    split_ifs at ha <;> omega
  let e : Fin 3 := ⟨a.val-4,by omega⟩
  have he : positive e = a := by
    apply Fin.ext
    change 4+(a.val-4) = a.val
    omega
  rw [← he]
  exact positive_seed_actual m e k j

/-- A positive letter in a sorted word forces a killed innermost positive letter. -/
theorem sorted_positive_zero (m : ℕ) (j : AllM.SeedIndex m) :
    ∀ (l : List (Fin 18 × ℕ)), l.IsChain (fun x y => key x ≤ key y) →
      (∃ x ∈ l, category x.1 = 3) →
      wordOp (representation ℂ m) l (AllM.seedPoly m j) = 0 := by
  intro l
  induction l with
  | nil =>
      intro _ h
      obtain ⟨x,hx,_⟩ := h
      simp at hx
  | cons x l ih =>
      intro hl hp
      by_cases ht : ∃ y ∈ l, category y.1 = 3
      · change deriv ℂ m x.1 x.2 (wordOp (representation ℂ m) l (AllM.seedPoly m j)) = 0
        rw [ih hl.tail ht,map_zero]
      · have hx : category x.1 = 3 := by
          obtain ⟨y,hy,hc⟩ := hp
          rcases List.mem_cons.mp hy with hy | hy
          · subst y; exact hc
          · exact (ht ⟨y,hy,hc⟩).elim
        cases l with
        | nil => exact category_three_seed m x.1 x.2 j hx
        | cons y ys =>
            have hxy := (List.isChain_cons_cons.mp hl).1
            have hy : category y.1 = 3 := by
              have hb := category_le_three y.1
              change category x.1 ≤ category y.1 at hxy
              omega
            exact (ht ⟨y,List.mem_cons_self,hy⟩).elim

def noPositiveSeeds (m : ℕ) : Set (MvPolynomial (Vars m) ℂ) :=
  {p | ∃ (j : AllM.SeedIndex m) (l : List (Fin 18 × ℕ)),
    l.IsChain (fun x y => key x ≤ key y) ∧
      (∀ x ∈ l, category x.1 < 3) ∧ p = wordOp (representation ℂ m) l (AllM.seedPoly m j)}

def noPositiveIdeal (m : ℕ) : Ideal (MvPolynomial (Vars m) ℂ) := Ideal.span (noPositiveSeeds m)

theorem triangular_le_noPositive (m : ℕ) : triangularIdeal m ≤ noPositiveIdeal m := by
  apply Ideal.span_le.mpr
  rintro p ⟨j,l,hs,rfl⟩
  by_cases hp : ∃ x ∈ l, category x.1 = 3
  · rw [sorted_positive_zero m j l hs hp]
    exact Ideal.zero_mem _
  · apply Ideal.subset_span
    refine ⟨j,l,hs,?_,rfl⟩
    intro x hx
    have hb := category_le_three x.1
    have hn : category x.1 ≠ 3 := fun he => hp ⟨x,hx,he⟩
    omega

theorem noPositive_le_candidate (m : ℕ) : noPositiveIdeal m ≤ AllM.candidateIdeal m := by
  apply Ideal.span_le.mpr
  rintro p ⟨j,l,_,_,rfl⟩
  exact word_mem_candidate m l (AllM.seed_mem_candidate m j)

theorem candidateIdeal_eq_noPositiveIdeal (m : ℕ) :
    AllM.candidateIdeal m = noPositiveIdeal m := by
  apply le_antisymm
  · exact (candidate_le_triangular m).trans (triangular_le_noPositive m)
  · exact noPositive_le_candidate m

end
#print axioms positive_seed_actual
#print axioms sorted_positive_zero
#print axioms candidateIdeal_eq_noPositiveIdeal
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.LeviRules
