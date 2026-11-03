import VOA.Huang.LogAssocCoefficientL0Ward

/-! The genuine collision Jordan defect on the full tensor dual, including
both source nilpotent actions. Its powers pair with actual tensor modes. -/
set_option maxSynthPendingDepth 3
namespace VOA.Huang.LogAssocCoefficientL0
open VOA VOA.LogTensor VOA.LogTensor.Pz
open Module (End)
noncomputable section
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable {M₁ M₂ : Type u} [AddCommGroup M₁] [Module ℂ M₁]
  [AddCommGroup M₂] [Module ℂ M₂]

/-- The actual full generalized collision defect. -/
def coefficientDefect (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (γ : ℂ) :
    End ℂ (BilinearDual (M₁ := M₁) (M₂ := M₂)) :=
  dualL0 N₁ N₂-γ • 1-preFirst N₁.L0nil-preSecond N₂.L0nil

/-- The actual source first Jordan action commutes with the collision defect. -/
theorem coefficientDefect_comm_first (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (γ : ℂ) :
    Commute (coefficientDefect N₁ N₂ γ) (preFirst N₁.L0nil) := by
  have h := (dualL0_commute_firstNil N₁ N₂).sub_left ((Commute.one_left _).smul_left γ)
  exact (h.sub_left (Commute.refl _)).sub_left (preFirstSecond_commute N₁.L0nil N₂.L0nil).symm

/-- The second genuine Jordan action commutes as well. -/
theorem coefficientDefect_comm_second (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (γ : ℂ) :
    Commute (coefficientDefect N₁ N₂ γ) (preSecond N₂.L0nil) := by
  have h := (dualL0_commute_secondNil N₁ N₂).sub_left ((Commute.one_left _).smul_left γ)
  exact (h.sub_left (preFirstSecond_commute N₁.L0nil N₂.L0nil)).sub_left (Commute.refl _)

/-- Its next power is the full target defect minus the genuine source nilpotent terms. -/
theorem coefficientDefect_pow_step (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (γ : ℂ)
    (k : ℕ) (F : BilinearDual (M₁ := M₁) (M₂ := M₂)) (x : M₁) (y : M₂) :
    ((coefficientDefect N₁ N₂ γ)^(k+1)) F x y =
      ((coefficientDefect N₁ N₂ γ)^k) ((dualL0 N₁ N₂-γ • 1) F) x y -
      ((coefficientDefect N₁ N₂ γ)^k) F (N₁.L0nil x) y -
      ((coefficientDefect N₁ N₂ γ)^k) F x (N₂.L0nil y) := by
  let D := coefficientDefect N₁ N₂ γ
  have hA := (coefficientDefect_comm_first N₁ N₂ γ).pow_left k
  have hB := (coefficientDefect_comm_second N₁ N₂ γ).pow_left k
  change ((D^(k+1)) F) x y= _
  rw [pow_succ,Module.End.mul_apply]
  change ((D^k) ((dualL0 N₁ N₂-γ • 1) F-preFirst N₁.L0nil F-preSecond N₂.L0nil F)) x y=_
  simp only [map_sub,LinearMap.sub_apply]
  have hAx := congrArg (fun E : End ℂ (BilinearDual (M₁ := M₁) (M₂ := M₂)) => E F x y) hA.eq
  have hBx := congrArg (fun E : End ℂ (BilinearDual (M₁ := M₁) (M₂ := M₂)) => E F x y) hB.eq
  simp only [Module.End.mul_apply,preFirst_apply,preSecond_apply] at hAx hBx
  rw [hAx,hBx]

end
end VOA.Huang.LogAssocCoefficientL0
