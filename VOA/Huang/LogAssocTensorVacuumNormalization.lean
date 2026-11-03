import VOA.Huang.LogAssocTensorVacuumMaps
import VOA.Huang.LogAssocTensorVacuumLimit

/-! Genuine vacuum normalization for the constructed logarithmic
associator. Its true completed product–iterate identity and actual unit
creation coefficients determine the constant coefficient by convergence. -/
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 1200000
namespace VOA.C2Rigid.LocalInjective
open VOA.LogTensor VOA.LogTensor.Pz VOA.Huang.LogAssocExpansion
open VOA.Huang.AssocExpansion
universe u
variable {V M N : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
  {W : VertexOperatorAlgebra V}
variable (hC2 : C2Cofinite W)
  (X : LogVModule W M) (Y : LogVModule W N)
  (hX : FinGen X.toWeakModule) (hY : FinGen Y.toWeakModule)

/-- The actual long triangle path has the genuine vacuum constant
coefficient of the canonical tensor operator, with all other logs retained. -/
theorem tensorTriangleLong_vacuum_constant
    {a b : ℂ} {x : M} {y : N} (hx : x∈X.weight a) (hy : y∈Y.weight b)
    (β : ℂ) (f : RestrictedDual (tensorDual hC2 X Y hX hY).toGW →ₗ[ℂ] ℂ) :
    f ((tensorTriangleLongHom hC2 X Y hX hY).toLinearMap
      ((tensorIntertwiner hC2 (rightUnitTensor hC2 X hX) Y
        (tensorModule_finGen hC2 X (adjointModule W).toLog hX finGen_adjoint) hY).1
        (a+b-β-1) 0
        ((tensorIntertwiner hC2 X (adjointModule W).toLog hX finGen_adjoint).1 (-1) 0 x W.vacuum) y))=
      f ((tensorIntertwiner hC2 X Y hX hY).1 (a+b-β-1) 0 x y) := by
  let U := (adjointModule W).toLog
  let T := rightUnitTensor hC2 X hX
  let L := leftTripleModule hC2 X U hX finGen_adjoint Y hY
  let Q := tensorModule hC2 X Y hX hY
  let F := tensorTriangleLongHom hC2 X Y hX hY
  let g := tensorVacuumCollapseHom hC2 X Y hX hY
  have hT : FinGen T.toWeakModule := tensorModule_finGen hC2 X U hX finGen_adjoint
  have hQ : FinGen Q.toWeakModule := tensorModule_finGen hC2 X Y hX hY
  let ηL := tensorIntertwiner hC2 T Y hT hY
  let ηR := tensorIntertwiner hC2 X U hX finGen_adjoint
  let η := tensorIntertwiner hC2 X Y hX hY
  have hlog : ∀ n k,1≤k → ηR.1 n k x W.vacuum=0 := by
    intro n k hk
    exact tensorRightUnit_vacuum_positive_log_zero hC2 X hX n k (by omega) x
  have hcreation : ∀ (n : ℂ),(∀ j : ℕ,n≠-1-j) → ηR.1 n 0 x W.vacuum=0 := by
    intro n hn
    exact tensorRightUnit_vacuum_zero_of_no_index hC2 X hX n hn x
  apply creation_constant_of_completed_point_identity hC2 X U Y Q T
    hX finGen_adjoint hY hQ hT (postcompose F ηL) ηR η
    hx adjoint_log_vacuum_mem_weight hy hlog hcreation f β
  intro r hr0 hr1
  have hlogr : (Real.log r : ℂ)=Complex.log r := Complex.ofReal_log hr0.le
  have ht : Complex.log (r : ℂ)∈overlapDomain :=
    hlogr ▸ log_mem_overlapDomain (u := r) hr0 hr1
  have hα := tensorAssociatorHom_completed_shift (β := β) hC2 X U Y hX finGen_adjoint hY
    hx adjoint_log_vacuum_mem_weight hy (f ∘ₗ g.toLinearMap) ht 0
  simp only [add_zero] at hα
  let R := rightTripleModule hC2 X U hX finGen_adjoint Y hY
  let T₀ := leftUnitTensor hC2 Y hY
  let η₁ := tensorIntertwiner hC2 X T₀ hX
    (tensorModule_finGen hC2 U Y finGen_adjoint hY)
  let η₂ := tensorIntertwiner hC2 U Y finGen_adjoint hY
  let P : ℂ → ℂ := fun ell => completedLogProduct X U Y R T₀ η₁ η₂ ell 0 a β
    (f ∘ₗ g.toLinearMap) ⟨x,hx⟩ W.vacuum y
  let I : ℂ → ℂ := fun ell => completedLogIterate X U Y L T ηL ηR ell 0 b β
    (f ∘ₗ F.toLinearMap) x W.vacuum ⟨y,hy⟩
  change P (Complex.log (1+Complex.exp (Complex.log r)))=I (Complex.log r) at hα
  rw [Complex.exp_log (by exact_mod_cast hr0.ne')] at hα
  have hpost := completedLogIterate_postcompose X U Y L T Q F ηL ηR
    (Complex.log r) 0 b β f x W.vacuum ⟨y,hy⟩
  exact hpost.trans (hα.symm.trans
    (tensorVacuumCollapse_completed_product hC2 X Y hX hY hx hy
      (Complex.log (1+(r : ℂ))) β f))

end VOA.C2Rigid.LocalInjective
