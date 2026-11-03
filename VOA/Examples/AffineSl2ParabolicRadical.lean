import VOA.Examples.AffineSl2ParabolicForm
import VOA.Examples.AffineSl2ParabolicFirstBlock

/-! # Genuine quotient radical states from the parabolic determinant -/
namespace VOA.AffineVOA.HighestModule
noncomputable section

/-- The finite matrix really is the descended form in the actual quotient basis. -/
theorem parabolicQuotientGram_pairing (k : ℂ) (d n : ℕ) (c : ℤ)
    (i j : Fin (Module.finrank ℂ (parabolicJointSpace 1 d n c))) :
    parabolicQuotientGram k d n c i j =
      parabolicForm k d (parabolicQuotientBasis k d n c i)
        (parabolicQuotientBasis k d n c j) := by
  rw [parabolicQuotientBasis_apply,parabolicQuotientBasis_apply]
  change _ = parabolicForm k d (parabolicProjection k d _) (parabolicProjection k d _)
  rw [parabolicForm_projection]
  rfl

/-- The actual joint quotient vector with prescribed finite coordinates. -/
def parabolicJointState (k : ℂ) (d n : ℕ) (c : ℤ)
    (a : Fin (Module.finrank ℂ (parabolicJointSpace 1 d n c))→ℂ) :
    parabolicJointSpace k d n c :=
  ∑ i,a i • parabolicQuotientBasis k d n c i

theorem parabolicJointState_eq_zero_iff (k : ℂ) (d n : ℕ) (c : ℤ)
    (a : Fin (Module.finrank ℂ (parabolicJointSpace 1 d n c))→ℂ) :
    parabolicJointState k d n c a=0 ↔ a=0 := by
  constructor
  · intro h
    exact funext (Fintype.linearIndependent_iff.mp
      (parabolicQuotientBasis k d n c).linearIndependent a h)
  · rintro rfl
    simp [parabolicJointState]

theorem parabolicQuotientGram_mulVec (k : ℂ) (d n : ℕ) (c : ℤ)
    (a : Fin (Module.finrank ℂ (parabolicJointSpace 1 d n c))→ℂ)
    (i : Fin (Module.finrank ℂ (parabolicJointSpace 1 d n c))) :
    (parabolicQuotientGram k d n c).mulVec a i =
      parabolicForm k d (parabolicQuotientBasis k d n c i)
        (parabolicJointState k d n c a) := by
  simp only [Matrix.mulVec,dotProduct,parabolicJointState,Submodule.coe_sum,
    Submodule.coe_smul,map_sum,map_smul,smul_eq_mul,parabolicQuotientGram_pairing]
  exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)

/-- A null finite quotient Gram vector lies in the full genuine radical. -/
theorem parabolicQuotientGram_kernel_iff_radical (k : ℂ) (d n : ℕ) (c : ℤ)
    (a : Fin (Module.finrank ℂ (parabolicJointSpace 1 d n c))→ℂ) :
    (parabolicQuotientGram k d n c).mulVec a=0 ↔
      parabolicForm k d (parabolicJointState k d n c a)=0 := by
  constructor
  · intro ha
    apply (parabolic_joint_radical_iff k d n c _ (parabolicJointState k d n c a).2).mpr
    have hz : (parabolicForm k d (parabolicJointState k d n c a)).comp
        (parabolicJointSpace k d n c).subtype=0 := by
      apply (parabolicQuotientBasis k d n c).ext
      intro i
      have hh := congrFun ha i
      rw [parabolicQuotientGram_mulVec,parabolicForm_symm] at hh
      exact hh
    intro v hv
    exact LinearMap.congr_fun hz ⟨v,hv⟩
  · intro h
    funext i
    rw [parabolicQuotientGram_mulVec,parabolicForm_symm,h]
    rfl

/-- Any root of the actual quotient determinant gives a nonzero state in the
full descended radical, without assuming a singular vector exists. -/
theorem parabolic_nonzero_radical_of_gram_root (k : ℂ) (d n : ℕ) (c : ℤ)
    (hroot : (parabolicQuotientGram k d n c).det=0) :
    ∃ v : Parabolic k d, v≠0 ∧ v∈parabolicJointSpace k d n c ∧ parabolicForm k d v=0 := by
  obtain ⟨a,hne,ha⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hroot
  refine ⟨parabolicJointState k d n c a,?_,(parabolicJointState k d n c a).2,
    (parabolicQuotientGram_kernel_iff_radical k d n c a).mp ha⟩
  intro h
  exact hne ((parabolicJointState_eq_zero_iff k d n c a).mp (Subtype.ext h))

end
end VOA.AffineVOA.HighestModule
