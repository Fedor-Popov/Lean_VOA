import VOA.Huang.LogAssocTensorOuterJacobi
import VOA.Huang.LogAssocTensorCoefficientMatching
import VOA.Classification.COne.McRaeM2TensorClosure

/-! Genuine logarithmic associativity at the collision overlap. Actual
canonical tensor modes, literal reconstructed outer modes, and unique
convergent logarithmic coefficients identify the completed product with
its completed iterate. No associativity witness is assumed. -/
set_option maxSynthPendingDepth 3
namespace VOA.Huang.LogAssocTensorCoefficientMatching
open VOA VOA.LogTensor VOA.LogTensor.Pz
open VOA.Huang.LogAssocCoefficients VOA.Huang.LogAssocCoefficientCompatibility
open VOA.Huang.LogAssocTensorOuterModes VOA.Huang.LogAssocExpansion
open VOA.Huang.LogRemovalCoeff VOA.Huang.AssocExpansion
open VOA.C2Rigid.LocalInjective VOA.VHat VOA.VHat.DLM3
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable {M₁ M₂ M₃ M₄ M₅ : Type u}
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] [AddCommGroup M₄] [Module ℂ M₄]
  [AddCommGroup M₅] [Module ℂ M₅]
variable (hC2 : C2Cofinite W)
  (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
  (N₄ : LogVModule W M₄) (N₅ : LogVModule W M₅)
  (hfg₁ : FinGen N₁.toWeakModule) (hfg₂ : FinGen N₂.toWeakModule)
  (hfg₃ : FinGen N₃.toWeakModule) (hfg₄ : FinGen N₄.toWeakModule)
  (hfg₅ : FinGen N₅.toWeakModule)
  (Y₁ : LogIntertwiningOperator N₁.toWeakModule N₅.toWeakModule N₄.toWeakModule)
  (Y₂ : LogIntertwiningOperator N₂.toWeakModule N₃.toWeakModule N₅.toWeakModule)

/-- The literal completed true logarithmic product equals the actual
canonical tensor iterate, for supported outside generalized-weight data. -/
theorem completedLogProduct_eq_canonical_iterate_supported
    {a b c β : ℂ} {x : M₁} {y : M₂} {z : M₃}
    (hx : x∈N₁.weight a) (hy : y∈N₂.weight b) (hz : z∈N₃.weight c)
    (f : M₄ →ₗ[ℂ] ℂ) (hf : SupportedAt N₄ f β) {t : ℂ} (ht : t∈overlapDomain) :
    completedLogProduct N₁ N₂ N₃ N₄ N₅ Y₁ Y₂ (Complex.log (1+Complex.exp t)) 0 a β f ⟨x,hx⟩ y z=
      completedLogIterate N₁ N₂ N₃ N₄ (tensorModule hC2 N₁ N₂ hfg₁ hfg₂)
        (tensorOuterIntertwiner hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂)
        (tensorIntertwiner hC2 N₁ N₂ hfg₁ hfg₂) t 0 c β f x y ⟨z,hz⟩ := by
  let T := tensorModule hC2 N₁ N₂ hfg₁ hfg₂
  let η := tensorIntertwiner hC2 N₁ N₂ hfg₁ hfg₂
  let Υ := tensorOuterIntertwiner hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂
  have hfgT : FinGen T.toWeakModule := tensorModule_finGen hC2 N₁ N₂ hfg₁ hfg₂
  let P := logProductSpectrumFun hC2 N₅ hfg₅ Y₁.1 Y₂.1 f x y z a b c β
  let I := logIterateSpectrumFun hC2 T hfgT Υ.1 η.1 f x y z a b c β
  have hP : HasLogExp overlapDomain P := log_product_spectrum_hasLogExp
    hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f x y z a b c β
  have hI : HasLogExp overlapDomain I := log_iterate_spectrum_hasLogExp
    hC2 N₁ N₂ N₃ N₄ T hfg₁ hfg₂ hfg₃ hfg₄ hfgT Υ η f x y z a b c β
  have hcoeff (μ : ℂ) (k : ℕ) : logCoeff overlapDomain P μ k=logCoeff overlapDomain I μ k := by
    let γ := μ+a+b
    have hγ : γ-a-b=μ := by dsimp only [γ]; ring
    have hpc := coefficient_homogeneous hC2 N₁ N₂ N₃ N₄ N₅
      hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ k hx hy
    have hic := logCoeff_iterateSpectrum hC2 N₁ N₂ N₃ N₄ T
      hfg₁ hfg₂ hfg₃ hfg₄ hfgT Υ η hx hy f z c β γ k
    have hm : f (Υ.1 (γ+c-β-1) 0 (η.1 (a+b-γ-1) k x y) z)=
        coefficient hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ f z c β γ k x y := by
      simpa only [Υ,η,tensorOuterIntertwiner_zero] using
        tensorOuterModes_innerPair hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅
          Y₁ Y₂ hx hy hz f hf γ k
    have he := hpc.symm.trans (hm.symm.trans hic.symm)
    simpa only [P,I,hγ] using he
  have hfun := eqOn_of_logCoeff_eq isOpen_overlapDomain overlapDomain_subset overlapDomain_nonempty hP hI hcoeff t ht
  have heP := completedLogProduct_eq_spectrum hC2 N₁ N₂ N₃ N₄ N₅
    hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ hx hy hz f β ht
  have heI := completedLogIterate_eq_lowerSpectrum hC2 N₁ N₂ N₃ N₄ T
    hfg₁ hfg₂ hfg₃ hfg₄ hfgT Υ η hx hy hz f β ht
  exact heP.trans (hfun.trans heI.symm)

/-- Every outside scalar functional gives the same actual completed identity:
point-evaluation blocks already land in the stated genuine output weight. -/
theorem completedLogProduct_eq_canonical_iterate
    {a b c β : ℂ} {x : M₁} {y : M₂} {z : M₃}
    (hx : x∈N₁.weight a) (hy : y∈N₂.weight b) (hz : z∈N₃.weight c)
    (f : M₄ →ₗ[ℂ] ℂ) {t : ℂ} (ht : t∈overlapDomain) :
    completedLogProduct N₁ N₂ N₃ N₄ N₅ Y₁ Y₂ (Complex.log (1+Complex.exp t)) 0 a β f ⟨x,hx⟩ y z=
      completedLogIterate N₁ N₂ N₃ N₄ (tensorModule hC2 N₁ N₂ hfg₁ hfg₂)
        (tensorOuterIntertwiner hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂)
        (tensorIntertwiner hC2 N₁ N₂ hfg₁ hfg₂) t 0 c β f x y ⟨z,hz⟩ := by
  let g := extendedFunctional N₄ β (f.domRestrict (N₄.weight β))
  have hg := extendedFunctional_supported N₄ β (f.domRestrict (N₄.weight β))
  have he := completedLogProduct_eq_canonical_iterate_supported hC2 N₁ N₂ N₃ N₄ N₅
    hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂ hx hy hz g hg ht
  have heP : completedLogProduct N₁ N₂ N₃ N₄ N₅ Y₁ Y₂ (Complex.log (1+Complex.exp t)) 0 a β f ⟨x,hx⟩ y z=
      completedLogProduct N₁ N₂ N₃ N₄ N₅ Y₁ Y₂ (Complex.log (1+Complex.exp t)) 0 a β g ⟨x,hx⟩ y z := by
    apply tsum_congr
    intro γ
    exact (extendedFunctional_of_mem N₄ (f.domRestrict (N₄.weight β))
      (pointEvaluationBlock N₁ N₅ N₄ Y₁ (Complex.log (1+Complex.exp t)) a γ β ⟨x,hx⟩
        (evaluatePoint N₂ N₃ N₅ Y₂ 0 y z γ)).2).symm
  have heI : completedLogIterate N₁ N₂ N₃ N₄ (tensorModule hC2 N₁ N₂ hfg₁ hfg₂)
        (tensorOuterIntertwiner hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂)
        (tensorIntertwiner hC2 N₁ N₂ hfg₁ hfg₂) t 0 c β g x y ⟨z,hz⟩=
      completedLogIterate N₁ N₂ N₃ N₄ (tensorModule hC2 N₁ N₂ hfg₁ hfg₂)
        (tensorOuterIntertwiner hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂)
        (tensorIntertwiner hC2 N₁ N₂ hfg₁ hfg₂) t 0 c β f x y ⟨z,hz⟩ := by
    apply tsum_congr
    intro γ
    exact extendedFunctional_of_mem N₄ (f.domRestrict (N₄.weight β))
      (pointEvaluationBlock (tensorModule hC2 N₁ N₂ hfg₁ hfg₂) N₃ N₄
        (tensorOuterIntertwiner hC2 N₁ N₂ N₃ N₄ N₅ hfg₁ hfg₂ hfg₃ hfg₄ hfg₅ Y₁ Y₂)
        0 γ c β (evaluatePoint N₁ N₂ (tensorModule hC2 N₁ N₂ hfg₁ hfg₂)
          (tensorIntertwiner hC2 N₁ N₂ hfg₁ hfg₂) t x y γ) ⟨z,hz⟩).2
  exact heP.trans (he.trans heI)

end VOA.Huang.LogAssocTensorCoefficientMatching
