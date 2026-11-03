import VOA.DeligneAudit.LeviTypeA3CountCutoff

/-! One finite key box, independent of radical depth. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.LeviTypeA

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : VOA.DeligneAudit.SectorWeyl.CurrentModule bracketTable V) (w : V)

/-- Each radical colour has its root-weight count bound. -/
theorem a3KeyLayer_eq_bot_of_count (a b c : ℕ) (k : A3RadicalKey)
    (h : LocalWeylRel ρ w (weightABC a b c))
    (hk : a < k.d₁ ∨ a + b < k.d₂ ∨ a + b + c < k.d₃) :
    a3KeyLayer ρ w k = ⊥ := by
  rw [a3KeyLayer, eq_bot_iff, Submodule.span_le]
  intro z hz
  obtain ⟨l, hd₁, hd₂, hd₃, _, _, rfl⟩ := hz
  rcases hk with hk | hk | hk
  · rw [a3_radicalWord_zero_of_count ρ w a b c h 0 l
      (by simpa [hd₁] using hk)]
    exact Submodule.zero_mem _
  · rw [a3_radicalWord_zero_of_count ρ w a b c h 1 l
      (by simpa [hd₂] using hk)]
    exact Submodule.zero_mem _
  · rw [a3_radicalWord_zero_of_count ρ w a b c h 2 l
      (by simpa [hd₃] using hk)]
    exact Submodule.zero_mem _

/-- Search keys with the three sharp count limits and a uniform mode-degree limit. -/
def a3KeyBox (a b c : ℕ) : Finset A3RadicalKey :=
  (Finset.range (a + 1)).biUnion fun d₁ =>
    (Finset.range (a + b + 1)).biUnion fun d₂ =>
      (Finset.range (a + b + c + 1)).biUnion fun d₃ =>
        (Finset.range ((a + b + c) * (3 * a + 2 * b + c) + 1)).image
          fun degree => ⟨d₁, d₂, d₃, degree⟩

theorem mem_a3KeyBox (a b c : ℕ) (k : A3RadicalKey)
    (h₁ : k.d₁ ≤ a) (h₂ : k.d₂ ≤ a + b) (h₃ : k.d₃ ≤ a + b + c)
    (hdeg : k.degree ≤ (a + b + c) * (3 * a + 2 * b + c)) :
    k ∈ a3KeyBox a b c := by
  unfold a3KeyBox
  apply Finset.mem_biUnion.mpr
  refine ⟨k.d₁, Finset.mem_range.mpr (by omega), ?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨k.d₂, Finset.mem_range.mpr (by omega), ?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨k.d₃, Finset.mem_range.mpr (by omega), ?_⟩
  apply Finset.mem_image.mpr
  exact ⟨k.degree, Finset.mem_range.mpr (by omega), by cases k; rfl⟩

/-- Every nonzero radical key layer lies in the all-depth box. -/
theorem a3KeyBox_contains_nonzero_global (a b c : ℕ)
    (h : LocalWeylRel ρ w (weightABC a b c))
    (k : A3RadicalKey) (hk : a3KeyLayer ρ w k ≠ ⊥) :
    k ∈ a3KeyBox a b c := by
  have h₁ : k.d₁ ≤ a := by
    by_contra hn
    exact hk (a3KeyLayer_eq_bot_of_count ρ w a b c k h
      (Or.inl (by omega)))
  have h₂ : k.d₂ ≤ a + b := by
    by_contra hn
    exact hk (a3KeyLayer_eq_bot_of_count ρ w a b c k h
      (Or.inr (Or.inl (by omega))))
  have h₃ : k.d₃ ≤ a + b + c := by
    by_contra hn
    exact hk (a3KeyLayer_eq_bot_of_count ρ w a b c k h
      (Or.inr (Or.inr (by omega))))
  have hsum : k.d₁ + k.d₂ + k.d₃ ≤ 3 * a + 2 * b + c := by omega
  have hmul : (a + b + c) * (k.d₁ + k.d₂ + k.d₃) ≤
      (a + b + c) * (3 * a + 2 * b + c) :=
    Nat.mul_le_mul_left _ hsum
  have hdeg : k.degree ≤ (a + b + c) * (3 * a + 2 * b + c) := by
    by_contra hn
    exact hk (a3KeyLayer_eq_bot_of_degree_gt ρ w a b c k h (by omega))
  exact mem_a3KeyBox a b c k h₁ h₂ h₃ hdeg

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a3KeyLayer_eq_bot_of_count
#print axioms VOA.DeligneAudit.A3Sector.mem_a3KeyBox
#print axioms VOA.DeligneAudit.A3Sector.a3KeyBox_contains_nonzero_global
