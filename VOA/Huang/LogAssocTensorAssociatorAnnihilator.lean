import VOA.Huang.LogAssocTensorOuterFactor
import VOA.Huang.LogAssocProductIterateIdentity
import VOA.Huang.LogAssocEvaluationAnnihilator

/-! A genuine scalar annihilator of the actual canonical associator
annihilates the actual canonical completed product on its convergence
overlap. This is the analytic range test for actual surjectivity. -/
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 1200000
namespace VOA.C2Rigid.LocalInjective
open VOA.LogTensor VOA.LogTensor.Pz VOA.Huang.LogAssocTensorOuterModes
open VOA.Huang.LogAssocExpansion VOA.Huang.LogAssocTensorCoefficientMatching
open VOA.Huang.LogAssocCoefficientCompatibility
open VOA.Huang.AssocExpansion
universe u
variable {V M₁ M₂ M₃ : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] {W : VertexOperatorAlgebra V}
variable (hC2 : C2Cofinite W)
  (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
  (h₁ : FinGen N₁.toWeakModule) (h₂ : FinGen N₂.toWeakModule) (h₃ : FinGen N₃.toWeakModule)

/-- An actual associator-range annihilator kills every genuine outer log mode. -/
theorem tensorAssociatorOuter_zero_of_comp
    (f : RestrictedDual (rightTripleDual hC2 N₁ N₂ h₁ h₂ N₃ h₃).toGW →ₗ[ℂ] ℂ)
    (hcomp : f ∘ₗ (tensorAssociatorHom hC2 N₁ N₂ N₃ h₁ h₂ h₃).toLinearMap=0)
    (n : ℂ) (k : ℕ) (ξ : RestrictedDual (tensorDual hC2 N₁ N₂ h₁ h₂).toGW) (z : M₃) :
    f ((tensorAssociatorOuter hC2 N₁ N₂ N₃ h₁ h₂ h₃).1 n k ξ z)=0 := by
  rw [← tensorAssociatorHom_apply hC2 N₁ N₂ N₃ h₁ h₂ h₃ n k ξ z]
  exact LinearMap.congr_fun hcomp _

/-- The annihilator of the actual canonical associator range kills the
literal canonical completed product everywhere on its true overlap. -/
theorem tensorAssociator_product_zero_of_comp
    (f : RestrictedDual (rightTripleDual hC2 N₁ N₂ h₁ h₂ N₃ h₃).toGW →ₗ[ℂ] ℂ)
    (hcomp : f ∘ₗ (tensorAssociatorHom hC2 N₁ N₂ N₃ h₁ h₂ h₃).toLinearMap=0)
    {a b c β : ℂ} {x : M₁} {y : M₂} {z : M₃}
    (hx : x∈N₁.weight a) (hy : y∈N₂.weight b) (hz : z∈N₃.weight c)
    {t : ℂ} (ht : t∈overlapDomain) :
    completedLogProduct N₁ N₂ N₃ (rightTripleModule hC2 N₁ N₂ h₁ h₂ N₃ h₃)
      (tensorModule hC2 N₂ N₃ h₂ h₃)
      (tensorIntertwiner hC2 N₁ (tensorModule hC2 N₂ N₃ h₂ h₃)
        h₁ (tensorModule_finGen hC2 N₂ N₃ h₂ h₃))
      (tensorIntertwiner hC2 N₂ N₃ h₂ h₃)
      (Complex.log (1+Complex.exp t)) 0 a β f ⟨x,hx⟩ y z=0 := by
  let T := tensorModule hC2 N₂ N₃ h₂ h₃
  let R := rightTripleModule hC2 N₁ N₂ h₁ h₂ N₃ h₃
  let η₂ := tensorIntertwiner hC2 N₂ N₃ h₂ h₃
  let η₁ := tensorIntertwiner hC2 N₁ T h₁ (tensorModule_finGen hC2 N₂ N₃ h₂ h₃)
  have hfgT : FinGen T.toWeakModule := tensorModule_finGen hC2 N₂ N₃ h₂ h₃
  have hfgR : FinGen R.toWeakModule := tensorModule_finGen hC2 N₁ T h₁ hfgT
  have he := completedLogProduct_eq_canonical_iterate (β := β) hC2 N₁ N₂ N₃ R T
    h₁ h₂ h₃ hfgR hfgT η₁ η₂ hx hy hz f ht
  have hzI := completedLogIterate_zero_of_modes N₁ N₂ N₃ R
    (tensorModule hC2 N₁ N₂ h₁ h₂)
    (tensorAssociatorOuter hC2 N₁ N₂ N₃ h₁ h₂ h₃)
    (tensorIntertwiner hC2 N₁ N₂ h₁ h₂) f
    (fun n k ξ z => tensorAssociatorOuter_zero_of_comp hC2 N₁ N₂ N₃ h₁ h₂ h₃ f hcomp n k ξ z)
    t 0 c β x y ⟨z,hz⟩
  exact he.trans hzI

/-- Genuine supported functionals on the right-associated tensor vanish
when all their actual homogeneous nested canonical zeroth modes vanish. -/
theorem supported_functional_eq_zero_of_nested_modes
    (β : ℂ) (f : RestrictedDual (rightTripleDual hC2 N₁ N₂ h₁ h₂ N₃ h₃).toGW →ₗ[ℂ] ℂ)
    (hf : SupportedAt (rightTripleModule hC2 N₁ N₂ h₁ h₂ N₃ h₃) f β)
    (hdet : ∀ (a b c : ℂ) (x : M₁) (y : M₂) (z : M₃),
      x∈N₁.weight a → y∈N₂.weight b → z∈N₃.weight c → ∀ γ : ℂ,
      f ((tensorIntertwiner hC2 N₁ (tensorModule hC2 N₂ N₃ h₂ h₃)
          h₁ (tensorModule_finGen hC2 N₂ N₃ h₂ h₃)).1 (a+γ-β-1) 0 x
        ((tensorIntertwiner hC2 N₂ N₃ h₂ h₃).1 (b+c-γ-1) 0 y z))=0) : f=0 := by
  let T := tensorModule hC2 N₂ N₃ h₂ h₃
  let η₂ := tensorIntertwiner hC2 N₂ N₃ h₂ h₃
  have hfgT : FinGen T.toWeakModule := tensorModule_finGen hC2 N₂ N₃ h₂ h₃
  let η₁ := tensorIntertwiner hC2 N₁ T h₁ hfgT
  apply tensor_linearMap_ext_homogeneous hC2 N₁ T h₁ hfgT
  intro n a γ x w hx hw
  simp only [LinearMap.zero_apply]
  let g := f ∘ₗ (η₁.1 n 0 x)
  have hg : g=0 := by
    apply tensor_linearMap_ext_homogeneous hC2 N₂ N₃ h₂ h₃
    intro m b c y z hy hz
    simp only [LinearMap.zero_apply]
    let δ := b+c-m-1
    have hξ : η₂.1 m 0 y z∈T.weight δ := η₂.2.mem_weight hy hz m 0
    have hOut := η₁.2.mem_weight hx hξ n 0
    by_cases he : a+δ-n-1=β
    · have hn : n=a+δ-β-1 := by linear_combination -he
      have hm : m=b+c-δ-1 := by dsimp only [δ]; ring
      have hh := hdet a b c x y z hx hy hz δ
      change f (η₁.1 (a+δ-β-1) 0 x (η₂.1 (b+c-δ-1) 0 y z))=0 at hh
      change f (η₁.1 n 0 x (η₂.1 m 0 y z))=0
      exact (congrArg f ((congrArg (fun q : ℂ => η₁.1 q 0 x (η₂.1 m 0 y z)) hn).trans
        (congrArg (fun q : ℂ => η₁.1 (a+δ-β-1) 0 x (η₂.1 q 0 y z)) hm))).trans hh
    · exact hf (a+δ-n-1) he _ hOut
  exact LinearMap.congr_fun hg w

end VOA.C2Rigid.LocalInjective
