import VOA.Huang.LogAssocTensorOuterFactor
import VOA.Huang.LogAssocChosenPoints
import VOA.Huang.LogAssocCompletedPostcompose

/-! A concrete analytic characterization of the actual canonical tensor
associator. It sends the genuine completed iterate to the genuine product,
with all logarithmic coefficients and the chosen branches retained. -/
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 1200000
namespace VOA.C2Rigid.LocalInjective
open VOA.LogTensor VOA.LogTensor.Pz VOA.Huang.LogAssocTensorOuterModes
open VOA.Huang.LogAssocExpansion VOA.Huang.LogAssocTensorCoefficientMatching
open VOA.Huang.AssocExpansion
universe u
variable {V M₁ M₂ M₃ : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] {W : VertexOperatorAlgebra V}
variable (hC2 : C2Cofinite W)
  (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
  (h₁ : FinGen N₁.toWeakModule) (h₂ : FinGen N₂.toWeakModule) (h₃ : FinGen N₃.toWeakModule)

/-- The actual associator carries completed canonical iterates to completed
canonical products on every scaled overlap and every chosen branch. -/
theorem tensorAssociatorHom_completed_shift
    {a b c β : ℂ} {x : M₁} {y : M₂} {z : M₃}
    (hx : x∈N₁.weight a) (hy : y∈N₂.weight b) (hz : z∈N₃.weight c)
    (f : RestrictedDual (rightTripleDual hC2 N₁ N₂ h₁ h₂ N₃ h₃).toGW →ₗ[ℂ] ℂ)
    {t : ℂ} (ht : t∈overlapDomain) (s : ℂ) :
    completedLogProduct N₁ N₂ N₃ (rightTripleModule hC2 N₁ N₂ h₁ h₂ N₃ h₃)
      (tensorModule hC2 N₂ N₃ h₂ h₃)
      (tensorIntertwiner hC2 N₁ (tensorModule hC2 N₂ N₃ h₂ h₃)
        h₁ (tensorModule_finGen hC2 N₂ N₃ h₂ h₃))
      (tensorIntertwiner hC2 N₂ N₃ h₂ h₃)
      (Complex.log (1+Complex.exp t)+s) s a β f ⟨x,hx⟩ y z=
    completedLogIterate N₁ N₂ N₃ (leftTripleModule hC2 N₁ N₂ h₁ h₂ N₃ h₃)
      (tensorModule hC2 N₁ N₂ h₁ h₂)
      (tensorIntertwiner hC2 (tensorModule hC2 N₁ N₂ h₁ h₂) N₃
        (tensorModule_finGen hC2 N₁ N₂ h₁ h₂) h₃)
      (tensorIntertwiner hC2 N₁ N₂ h₁ h₂)
      (t+s) s c β (f ∘ₗ (tensorAssociatorHom hC2 N₁ N₂ N₃ h₁ h₂ h₃).toLinearMap)
      x y ⟨z,hz⟩ := by
  let T := tensorModule hC2 N₂ N₃ h₂ h₃
  let R := rightTripleModule hC2 N₁ N₂ h₁ h₂ N₃ h₃
  have hfgT : FinGen T.toWeakModule := tensorModule_finGen hC2 N₂ N₃ h₂ h₃
  have hfgR : FinGen R.toWeakModule := tensorModule_finGen hC2 N₁ T h₁ hfgT
  have he := completedLogProduct_eq_canonical_iterate_shift (β := β) hC2 N₁ N₂ N₃ R T
    h₁ h₂ h₃ hfgR hfgT
    (tensorIntertwiner hC2 N₁ T h₁ hfgT)
    (tensorIntertwiner hC2 N₂ N₃ h₂ h₃) hx hy hz f ht s
  change _=completedLogIterate N₁ N₂ N₃ R (tensorModule hC2 N₁ N₂ h₁ h₂)
    (tensorAssociatorOuter hC2 N₁ N₂ N₃ h₁ h₂ h₃)
    (tensorIntertwiner hC2 N₁ N₂ h₁ h₂) (t+s) s c β f x y ⟨z,hz⟩ at he
  rw [← tensorAssociatorHom_comp_intertwiner hC2 N₁ N₂ N₃ h₁ h₂ h₃,
    completedLogIterate_postcompose] at he
  exact he

/-- At the literal positive insertion points 3,2,1, the actual associator
identifies the true completed canonical product and iterate. -/
theorem tensorAssociatorHom_completed_three_two_one
    {a b c β : ℂ} {x : M₁} {y : M₂} {z : M₃}
    (hx : x∈N₁.weight a) (hy : y∈N₂.weight b) (hz : z∈N₃.weight c)
    (f : RestrictedDual (rightTripleDual hC2 N₁ N₂ h₁ h₂ N₃ h₃).toGW →ₗ[ℂ] ℂ) :
    completedLogProduct N₁ N₂ N₃ (rightTripleModule hC2 N₁ N₂ h₁ h₂ N₃ h₃)
      (tensorModule hC2 N₂ N₃ h₂ h₃)
      (tensorIntertwiner hC2 N₁ (tensorModule hC2 N₂ N₃ h₂ h₃)
        h₁ (tensorModule_finGen hC2 N₂ N₃ h₂ h₃))
      (tensorIntertwiner hC2 N₂ N₃ h₂ h₃)
      (Complex.log 3) (Complex.log 2) a β f ⟨x,hx⟩ y z=
    completedLogIterate N₁ N₂ N₃ (leftTripleModule hC2 N₁ N₂ h₁ h₂ N₃ h₃)
      (tensorModule hC2 N₁ N₂ h₁ h₂)
      (tensorIntertwiner hC2 (tensorModule hC2 N₁ N₂ h₁ h₂) N₃
        (tensorModule_finGen hC2 N₁ N₂ h₁ h₂) h₃)
      (tensorIntertwiner hC2 N₁ N₂ h₁ h₂)
      0 (Complex.log 2) c β
      (f ∘ₗ (tensorAssociatorHom hC2 N₁ N₂ N₃ h₁ h₂ h₃).toLinearMap) x y ⟨z,hz⟩ := by
  let T := tensorModule hC2 N₂ N₃ h₂ h₃
  let R := rightTripleModule hC2 N₁ N₂ h₁ h₂ N₃ h₃
  have hfgT : FinGen T.toWeakModule := tensorModule_finGen hC2 N₂ N₃ h₂ h₃
  have hfgR : FinGen R.toWeakModule := tensorModule_finGen hC2 N₁ T h₁ hfgT
  have he := completedLogProduct_eq_canonical_iterate_three_two_one (β := β) hC2 N₁ N₂ N₃ R T
    h₁ h₂ h₃ hfgR hfgT
    (tensorIntertwiner hC2 N₁ T h₁ hfgT)
    (tensorIntertwiner hC2 N₂ N₃ h₂ h₃) hx hy hz f
  change _=completedLogIterate N₁ N₂ N₃ R (tensorModule hC2 N₁ N₂ h₁ h₂)
    (tensorAssociatorOuter hC2 N₁ N₂ N₃ h₁ h₂ h₃)
    (tensorIntertwiner hC2 N₁ N₂ h₁ h₂) 0 (Complex.log 2) c β f x y ⟨z,hz⟩ at he
  rw [← tensorAssociatorHom_comp_intertwiner hC2 N₁ N₂ N₃ h₁ h₂ h₃,
    completedLogIterate_postcompose] at he
  exact he

end VOA.C2Rigid.LocalInjective
