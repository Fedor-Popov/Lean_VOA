import VOA.DeligneAudit.D4LevelReductionGradeSymmetry
import VOA.DeligneAudit.D4LevelReductionGradeFiltration

/-! The symmetric grade count and the nonnegative-grade contribution to the D4 bound. -/

namespace VOA.DeligneAudit.D4LevelReduction

/-- The four-colour target summed over the possible Levi levels at one grade. -/
noncomputable def gradeTarget (m : ℕ) (κ : ℤ) : ℕ :=
  ∑ p ∈ Finset.Icc (0 : ℤ) (2 * (m : ℤ)), levelTarget m κ p

/-- The target count has equal opposite-grade contributions. -/
theorem gradeTarget_neg (m : ℕ) (κ : ℤ) : gradeTarget m (-κ) = gradeTarget m κ := by
  simp only [gradeTarget, levelTarget_neg_grade]

/-- A symmetric integer-interval sum is its nonnegative part plus its positive part. -/
theorem symmetricGrade_sum (m : ℕ) (f : ℤ → ℕ) (hf : ∀ κ, f (-κ) = f κ) :
    (∑ κ ∈ Finset.Icc (-(m : ℤ)) m, f κ) =
      (∑ κ ∈ Finset.Icc (0 : ℤ) m, f κ) + ∑ κ ∈ Finset.Icc (1 : ℤ) m, f κ := by
  have hpos : (Finset.Icc (-(m : ℤ)) m).filter (fun κ => 0 ≤ κ) =
      Finset.Icc (0 : ℤ) m := by
    ext κ
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  have hneg : (∑ κ ∈ (Finset.Icc (-(m : ℤ)) m).filter (fun κ => ¬0 ≤ κ), f κ) =
      ∑ κ ∈ Finset.Icc (1 : ℤ) m, f κ := by
    apply Finset.sum_bij (fun κ _ => -κ)
    · intro κ hκ
      simp only [Finset.mem_filter, Finset.mem_Icc] at hκ ⊢
      omega
    · intro κ _ ν _ he
      omega
    · intro κ hκ
      refine ⟨-κ, ?_, neg_neg κ⟩
      simp only [Finset.mem_filter, Finset.mem_Icc] at hκ ⊢
      omega
    · intro κ _
      exact (hf κ).symm
  have hs := Finset.sum_filter_add_sum_filter_not (Finset.Icc (-(m : ℤ)) m)
    (fun κ => 0 ≤ κ) f
  rw [hpos, hneg] at hs
  exact hs.symm

/-- Nonnegative grades together with a second copy of positive grades count exactly 28^m. -/
theorem gradeTarget_nonnegative_sum (m : ℕ) :
    (∑ κ ∈ Finset.Icc (0 : ℤ) m, gradeTarget m κ) +
      (∑ κ ∈ Finset.Icc (1 : ℤ) m, gradeTarget m κ) = 28 ^ m := by
  rw [← symmetricGrade_sum m (gradeTarget m) (gradeTarget_neg m)]
  exact levelTarget_double_sum m

/-- The finite key levels at one grade contribute at most the full target of that grade. -/
theorem levelTarget_grade_sum_le (m : ℕ) (κ : ℤ) :
    (∑ i ∈ gradeLevelIndices m κ, levelTarget m i.1 i.2) ≤ gradeTarget m κ := by
  classical
  let s := gradeLevelIndices m κ
  let t := ({κ} : Finset ℤ) ×ˢ Finset.Icc (0 : ℤ) (2 * (m : ℤ))
  have he : (∑ i ∈ s, levelTarget m i.1 i.2) =
      ∑ i ∈ s ∩ t, levelTarget m i.1 i.2 := by
    symm
    apply Finset.sum_subset Finset.inter_subset_left
    intro i hi hn
    have hiκ := (Finset.mem_filter.mp hi).2
    apply levelTarget_zero_of_outside
    intro hmem
    have hp := (Finset.mem_product.mp hmem).2
    exact hn (Finset.mem_inter.mpr ⟨hi, Finset.mem_product.mpr
      ⟨Finset.mem_singleton.mpr hiκ, hp⟩⟩)
  calc
    _ = ∑ i ∈ s ∩ t, levelTarget m i.1 i.2 := he
    _ ≤ ∑ i ∈ t, levelTarget m i.1 i.2 :=
      Finset.sum_le_sum_of_subset Finset.inter_subset_right
    _ = gradeTarget m κ := by simp [t, gradeTarget]

end VOA.DeligneAudit.D4LevelReduction

#print axioms VOA.DeligneAudit.D4LevelReduction.gradeTarget_neg
#print axioms VOA.DeligneAudit.D4LevelReduction.symmetricGrade_sum
#print axioms VOA.DeligneAudit.D4LevelReduction.gradeTarget_nonnegative_sum
#print axioms VOA.DeligneAudit.D4LevelReduction.levelTarget_grade_sum_le
