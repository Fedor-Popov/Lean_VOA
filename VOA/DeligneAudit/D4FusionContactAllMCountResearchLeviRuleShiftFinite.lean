import VOA.DeligneAudit.D4FusionContactAllMCountResearchLeviRuleShiftsActual
import Mathlib.Data.Set.Finite.List

/-! An actual finite index family for single-color shifts of every original seed.
Its finiteness follows from proved pruning, cutoff and mode-sum bounds. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.LeviRules
open VOA.DeligneAudit.D4FusionContact.Polynomial
noncomputable section

/-- Positive shift lists inside the actual cutoff and current budget. -/
def boundedShiftLists (m T : ℕ) : Set (List ℕ) :=
  {l | l.length ≤ T ∧ l.sum ≤ T ∧ ∀ k ∈ l, 1 ≤ k ∧ k < m}

/-- This is a genuine finite set, without a source-finiteness premise. -/
theorem boundedShiftLists_finite (m T : ℕ) : (boundedShiftLists m T).Finite := by
  have hf := (List.finite_length_le (Fin m) T).image (fun l => l.map Fin.val)
  apply hf.subset
  intro l hl
  let v : List (Fin m) := l.attach.map (fun x => ⟨x.val,(hl.2.2 x.val x.property).2⟩)
  refine ⟨v,?_,?_⟩
  · change v.length ≤ T
    simpa only [v,List.length_map,List.length_attach] using hl.1
  · change v.map Fin.val=l
    simp only [v,List.map_map,Function.comp_def]
    exact List.attach_map_subtype_val l

/-- Filtering zero modes preserves the entire nonnegative current budget. -/
theorem prune_zero_sum (l : List ℕ) : (l.filter (· ≠ 0)).sum=l.sum := by
  induction l with
  | nil => rfl
  | cons k l ih =>
      by_cases hk : k=0
      · subst k
        simpa only [List.filter_cons,ne_eq,not_true_eq_false,decide_false,
          Bool.false_eq_true,if_false,List.sum_cons,zero_add] using ih
      · simpa only [List.filter_cons,ne_eq,hk,not_false_eq_true,decide_true,if_true,
          List.sum_cons] using congrArg (fun n => k+n) ih

/-- Every surviving pruned original seed word belongs to the finite index set. -/
theorem pruned_shift_mem_bounded (m T : ℕ) (j : AllM.SeedIndex m) (l : List ℕ)
    (hsum : l.sum ≤ T) (hne : shiftWord m l (monoSeed m j) ≠ 0) :
    l.filter (· ≠ 0) ∈ boundedShiftLists m T := by
  refine ⟨(pruned_modes_length_le_sum l).trans hsum,?_,?_⟩
  · rw [prune_zero_sum]
    exact hsum
  · intro k hk
    have hmem := (List.mem_filter.mp hk).1
    have hk0 : k ≠ 0 := by simpa using (List.mem_filter.mp hk).2
    exact ⟨Nat.one_le_iff_ne_zero.mpr hk0,shiftWord_seed_modes_lt m j l hne k hmem⟩

/-- A surviving whole shift row is a scalar multiple of an explicitly bounded row. -/
theorem shift_seed_bounded_coverage (m T : ℕ) (j : AllM.SeedIndex m) (l : List ℕ)
    (hsum : l.sum ≤ T) (hne : shiftWord m l (monoSeed m j) ≠ 0) :
    ∃ (z : ℂ) (v : List ℕ), v ∈ boundedShiftLists m T ∧ v.sum=l.sum ∧
      shiftWord m l (monoSeed m j)=z • shiftWord m v (monoSeed m j) := by
  obtain ⟨z,hz⟩ := shiftWord_seed_prune_zero m j l
  exact ⟨z,l.filter (· ≠ 0),pruned_shift_mem_bounded m T j l hsum hne,prune_zero_sum l,hz⟩

/-- The actual finite set of original shifted whole seed polynomials. -/
def boundedShiftSeedRows (m T : ℕ) (j : AllM.SeedIndex m) : Set (MonoRing ℂ m) :=
  (fun l => shiftWord m l (monoSeed m j)) '' boundedShiftLists m T

theorem boundedShiftSeedRows_finite (m T : ℕ) (j : AllM.SeedIndex m) :
    (boundedShiftSeedRows m T j).Finite :=
  (boundedShiftLists_finite m T).image _

/-- Every original word inside the current budget lies in this finite row span. -/
theorem shift_seed_mem_bounded_span (m T : ℕ) (j : AllM.SeedIndex m) (l : List ℕ)
    (hsum : l.sum ≤ T) :
    shiftWord m l (monoSeed m j) ∈ Submodule.span ℂ (boundedShiftSeedRows m T j) := by
  by_cases hz : shiftWord m l (monoSeed m j)=0
  · rw [hz]
    exact Submodule.zero_mem _
  · obtain ⟨z,v,hv,_,he⟩ := shift_seed_bounded_coverage m T j l hsum hz
    rw [he]
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨v,hv,rfl⟩

/-- Exact finite spanning for the original shift family at every current budget. -/
theorem shift_seed_span_eq_bounded (m T : ℕ) (j : AllM.SeedIndex m) :
    Submodule.span ℂ {p | ∃ l : List ℕ, l.sum ≤ T ∧ p=shiftWord m l (monoSeed m j)} =
      Submodule.span ℂ (boundedShiftSeedRows m T j) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro p ⟨l,hsum,rfl⟩
    exact shift_seed_mem_bounded_span m T j l hsum
  · apply Submodule.span_le.mpr
    rintro p ⟨l,hl,rfl⟩
    exact Submodule.subset_span ⟨l,hl.2.1,rfl⟩

end
#print axioms boundedShiftLists_finite
#print axioms shift_seed_bounded_coverage
#print axioms boundedShiftSeedRows_finite
#print axioms shift_seed_span_eq_bounded
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.LeviRules
