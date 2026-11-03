import VOA.Huang.LogAssocTensorAssociatorEvaluation

/-! Canonical sewing fibers obtained by freezing a true point-evaluation
component in any of the three associator inputs. The component is an actual
generalized-weight vector, with all logarithmic modes retained. -/
set_option maxSynthPendingDepth 3
namespace VOA.C2Rigid.LocalInjective
open VOA VOA.LogTensor VOA.LogTensor.Pz
open VOA.Huang.LogAssocExpansion VOA.Huang.AssocExpansion
universe u
variable {V M₁ M₂ M₃ X Y : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] [AddCommGroup X] [Module ℂ X]
  [AddCommGroup Y] [Module ℂ Y] {W : VertexOperatorAlgebra V}
variable (hC2 : C2Cofinite W)
  (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
  (h₁ : FinGen N₁.toWeakModule) (h₂ : FinGen N₂.toWeakModule) (h₃ : FinGen N₃.toWeakModule)
  (Q : LogVModule W X) (R : LogVModule W Y)

-- Actual triple tensor point-component types require a larger elaboration budget.
set_option maxHeartbeats 2000000 in
/-- The genuine completed associator identity with an actual point component
frozen in its first input. -/
theorem pointInputFiber_first_completed
    (J : LogIntertwiningOperator Q.toWeakModule R.toWeakModule N₁.toWeakModule)
    (ell : ℂ) (i : X) (j : Y) {a b c β : ℂ} {y : M₂} {z : M₃}
    (hy : y∈N₂.weight b) (hz : z∈N₃.weight c)
    (f : RestrictedDual (rightTripleDual hC2 N₁ N₂ h₁ h₂ N₃ h₃).toGW →ₗ[ℂ] ℂ)
    {t : ℂ} (ht : t∈overlapDomain) (s : ℂ) :
    let ξ := evaluatePoint Q R N₁ J ell i j a
    completedLogProduct N₁ N₂ N₃
      (rightTripleModule hC2 N₁ N₂ h₁ h₂ N₃ h₃)
      (tensorModule hC2 N₂ N₃ h₂ h₃)
      (tensorIntertwiner hC2 N₁ (tensorModule hC2 N₂ N₃ h₂ h₃)
        h₁ (tensorModule_finGen hC2 N₂ N₃ h₂ h₃))
      (tensorIntertwiner hC2 N₂ N₃ h₂ h₃)
      (Complex.log (1+Complex.exp t)+s) s a β f ξ y z=
    completedLogIterate N₁ N₂ N₃
      (leftTripleModule hC2 N₁ N₂ h₁ h₂ N₃ h₃)
      (tensorModule hC2 N₁ N₂ h₁ h₂)
      (tensorIntertwiner hC2 (tensorModule hC2 N₁ N₂ h₁ h₂) N₃
        (tensorModule_finGen hC2 N₁ N₂ h₁ h₂) h₃)
      (tensorIntertwiner hC2 N₁ N₂ h₁ h₂) (t+s) s c β
      (f ∘ₗ (tensorAssociatorHom hC2 N₁ N₂ N₃ h₁ h₂ h₃).toLinearMap) ξ y ⟨z,hz⟩ := by
  let ξ := evaluatePoint Q R N₁ J ell i j a
  exact tensorAssociatorHom_completed_shift (β := β) hC2 N₁ N₂ N₃ h₁ h₂ h₃
    ξ.2 hy hz f ht s

-- Actual triple tensor point-component types require a larger elaboration budget.
set_option maxHeartbeats 2000000 in
/-- The genuine completed associator identity with an actual point component
frozen in its second input. -/
theorem pointInputFiber_second_completed
    (J : LogIntertwiningOperator Q.toWeakModule R.toWeakModule N₂.toWeakModule)
    (ell : ℂ) (i : X) (j : Y) {a b c β : ℂ} {x : M₁} {z : M₃}
    (hx : x∈N₁.weight a) (hz : z∈N₃.weight c)
    (f : RestrictedDual (rightTripleDual hC2 N₁ N₂ h₁ h₂ N₃ h₃).toGW →ₗ[ℂ] ℂ)
    {t : ℂ} (ht : t∈overlapDomain) (s : ℂ) :
    let ξ := evaluatePoint Q R N₂ J ell i j b
    completedLogProduct N₁ N₂ N₃
      (rightTripleModule hC2 N₁ N₂ h₁ h₂ N₃ h₃)
      (tensorModule hC2 N₂ N₃ h₂ h₃)
      (tensorIntertwiner hC2 N₁ (tensorModule hC2 N₂ N₃ h₂ h₃)
        h₁ (tensorModule_finGen hC2 N₂ N₃ h₂ h₃))
      (tensorIntertwiner hC2 N₂ N₃ h₂ h₃)
      (Complex.log (1+Complex.exp t)+s) s a β f ⟨x,hx⟩ ξ z=
    completedLogIterate N₁ N₂ N₃
      (leftTripleModule hC2 N₁ N₂ h₁ h₂ N₃ h₃)
      (tensorModule hC2 N₁ N₂ h₁ h₂)
      (tensorIntertwiner hC2 (tensorModule hC2 N₁ N₂ h₁ h₂) N₃
        (tensorModule_finGen hC2 N₁ N₂ h₁ h₂) h₃)
      (tensorIntertwiner hC2 N₁ N₂ h₁ h₂) (t+s) s c β
      (f ∘ₗ (tensorAssociatorHom hC2 N₁ N₂ N₃ h₁ h₂ h₃).toLinearMap) x ξ ⟨z,hz⟩ := by
  let ξ := evaluatePoint Q R N₂ J ell i j b
  exact tensorAssociatorHom_completed_shift (β := β) hC2 N₁ N₂ N₃ h₁ h₂ h₃
    hx ξ.2 hz f ht s

-- Actual triple tensor point-component types require a larger elaboration budget.
set_option maxHeartbeats 2000000 in
/-- The genuine completed associator identity with an actual point component
frozen in its third input. -/
theorem pointInputFiber_third_completed
    (J : LogIntertwiningOperator Q.toWeakModule R.toWeakModule N₃.toWeakModule)
    (ell : ℂ) (i : X) (j : Y) {a b c β : ℂ} {x : M₁} {y : M₂}
    (hx : x∈N₁.weight a) (hy : y∈N₂.weight b)
    (f : RestrictedDual (rightTripleDual hC2 N₁ N₂ h₁ h₂ N₃ h₃).toGW →ₗ[ℂ] ℂ)
    {t : ℂ} (ht : t∈overlapDomain) (s : ℂ) :
    let ξ := evaluatePoint Q R N₃ J ell i j c
    completedLogProduct N₁ N₂ N₃
      (rightTripleModule hC2 N₁ N₂ h₁ h₂ N₃ h₃)
      (tensorModule hC2 N₂ N₃ h₂ h₃)
      (tensorIntertwiner hC2 N₁ (tensorModule hC2 N₂ N₃ h₂ h₃)
        h₁ (tensorModule_finGen hC2 N₂ N₃ h₂ h₃))
      (tensorIntertwiner hC2 N₂ N₃ h₂ h₃)
      (Complex.log (1+Complex.exp t)+s) s a β f ⟨x,hx⟩ y ξ=
    completedLogIterate N₁ N₂ N₃
      (leftTripleModule hC2 N₁ N₂ h₁ h₂ N₃ h₃)
      (tensorModule hC2 N₁ N₂ h₁ h₂)
      (tensorIntertwiner hC2 (tensorModule hC2 N₁ N₂ h₁ h₂) N₃
        (tensorModule_finGen hC2 N₁ N₂ h₁ h₂) h₃)
      (tensorIntertwiner hC2 N₁ N₂ h₁ h₂) (t+s) s c β
      (f ∘ₗ (tensorAssociatorHom hC2 N₁ N₂ N₃ h₁ h₂ h₃).toLinearMap) x y ξ := by
  let ξ := evaluatePoint Q R N₃ J ell i j c
  exact tensorAssociatorHom_completed_shift (β := β) hC2 N₁ N₂ N₃ h₁ h₂ h₃
    hx hy ξ.2 f ht s

end VOA.C2Rigid.LocalInjective
