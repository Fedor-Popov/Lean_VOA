import VOA.DeligneAudit.D4FusionContactAllMCountResearchLeviRuleShifts
import VOA.DeligneAudit.D4FusionContactAllMCountResearchLeviRuleSeedWords

/-! Shift pruning for the original source words used by the actual D4 ideal. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.LeviRules
open VOA.DeligneAudit.D4FusionContact.Polynomial
noncomputable section

theorem shiftWord_eq_monoShiftWord (m : ℕ) (l : List ℕ) (p : MonoRing ℂ m) :
    shiftWord m l p=monoShiftWord ℂ m l p := by
  induction l with
  | nil => rfl
  | cons k l ih =>
      change monoShift ℂ m k (shiftWord m l p)=monoShift ℂ m k (monoShiftWord ℂ m l p)
      rw [ih]

theorem monoSeed_homogeneous (m : ℕ) (j : AllM.SeedIndex m) :
    (monoSeed m j).IsHomogeneous j.val.2.1 :=
  monoCoefficient_homogeneous ℂ m j.val.2.1 j.val.2.2

/-- Out-of-cutoff modes kill the original whole single-color seed word. -/
theorem shiftWord_seed_high_zero (m : ℕ) (j : AllM.SeedIndex m) (l : List ℕ)
    (hl : ∃ k ∈ l, m ≤ k) : shiftWord m l (monoSeed m j)=0 := by
  rw [shiftWord_eq_monoShiftWord]
  exact monoShiftWord_high_zero ℂ m l _ hl

/-- Every mode in a nonzero whole seed word lies inside the actual cutoff. -/
theorem shiftWord_seed_modes_lt (m : ℕ) (j : AllM.SeedIndex m) (l : List ℕ)
    (hne : shiftWord m l (monoSeed m j) ≠ 0) : ∀ k ∈ l,k < m := by
  intro k hk
  by_contra h
  exact hne (shiftWord_seed_high_zero m j l ⟨k,hk,Nat.le_of_not_gt h⟩)

/-- Every original seed word is a scalar multiple of its positive-mode pruning. -/
theorem shiftWord_seed_prune_zero (m : ℕ) (j : AllM.SeedIndex m) (l : List ℕ) :
    ∃ z : ℂ, shiftWord m l (monoSeed m j)=z • shiftWord m (l.filter (· ≠ 0)) (monoSeed m j) := by
  simp only [shiftWord_eq_monoShiftWord]
  exact monoShiftWord_prune_zero ℂ m j.val.2.1 l (monoSeed_homogeneous m j)

end
#print axioms monoSeed_homogeneous
#print axioms shiftWord_seed_high_zero
#print axioms shiftWord_seed_modes_lt
#print axioms shiftWord_seed_prune_zero
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.LeviRules
