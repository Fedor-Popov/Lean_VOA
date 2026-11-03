import VOA.Huang.LogAssocIterateDetection
import VOA.Classification.COne.McRaeM2TensorHomogeneousTripleGeneration

/-! Literal completed canonical logarithmic iterates detect linear maps
on the actual left triple tensor carrier. No abstract analytic associativity
witness is used in this uniqueness principle. -/
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 1200000
namespace VOA.C2Rigid.LocalInjective
open VOA.LogTensor VOA.LogTensor.Pz VOA.Huang.LogAssocExpansion VOA.Huang.AssocExpansion
universe u
variable {V M₁ M₂ M₃ : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] {W : VertexOperatorAlgebra V}
variable (hC2 : C2Cofinite W)
  (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂) (N₃ : LogVModule W M₃)
  (h₁ : FinGen N₁.toWeakModule) (h₂ : FinGen N₂.toWeakModule) (h₃ : FinGen N₃.toWeakModule)

/-- Vanishing of every genuine completed canonical iterate scalar pairing
forces the actual carrier linear map to vanish. -/
theorem leftTriple_linearMap_eq_zero_of_completed_iterate
    {X : Type*} [AddCommGroup X] [Module ℂ X]
    (F : RestrictedDual (leftTripleDual hC2 N₁ N₂ h₁ h₂ N₃ h₃).toGW →ₗ[ℂ] X)
    (hzero : ∀ (f : X →ₗ[ℂ] ℂ) (a b c β : ℂ) (x : M₁) (y : M₂) (z : M₃)
      (hx : x∈N₁.weight a) (hy : y∈N₂.weight b) (hz : z∈N₃.weight c),
      ∀ t∈overlapDomain,
      completedLogIterate N₁ N₂ N₃ (leftTripleModule hC2 N₁ N₂ h₁ h₂ N₃ h₃)
        (tensorModule hC2 N₁ N₂ h₁ h₂)
        (tensorIntertwiner hC2 (tensorModule hC2 N₁ N₂ h₁ h₂) N₃
          (tensorModule_finGen hC2 N₁ N₂ h₁ h₂) h₃)
        (tensorIntertwiner hC2 N₁ N₂ h₁ h₂)
        t 0 c β (f ∘ₗ F) x y ⟨z,hz⟩=0) : F=0 := by
  let T := tensorModule hC2 N₁ N₂ h₁ h₂
  let L := leftTripleModule hC2 N₁ N₂ h₁ h₂ N₃ h₃
  have hfgT : FinGen T.toWeakModule := tensorModule_finGen hC2 N₁ N₂ h₁ h₂
  have hfgL : FinGen L.toWeakModule := tensorModule_finGen hC2 T N₃ hfgT h₃
  let η := tensorIntertwiner hC2 T N₃ hfgT h₃
  let θ := tensorIntertwiner hC2 N₁ N₂ h₁ h₂
  apply leftTriple_linearMap_ext_homogeneous hC2 N₁ N₂ N₃ h₁ h₂ h₃
  intro n m a b c x y z hx hy hz
  simp only [LinearMap.zero_apply]
  apply (Module.forall_dual_apply_eq_zero_iff ℂ _).mp
  intro f
  let γ := a+b-m-1
  let β := γ+c-n-1
  have hdet := iterate_mode_zero_of_completed_zero hC2 N₁ N₂ N₃ L T
    h₁ h₂ h₃ hfgL hfgT η θ hx hy hz (f ∘ₗ F) β
    (hzero f a b c β x y z hx hy hz) γ 0
  have hn : γ+c-β-1=n := by dsimp only [β]; ring
  have hm : a+b-γ-1=m := by dsimp only [γ]; ring
  change f (F (η.1 (γ+c-β-1) 0 (θ.1 (a+b-γ-1) 0 x y) z))=0 at hdet
  exact (congrArg (f ∘ₗ F) ((congrArg (fun q : ℂ => η.1 q 0 (θ.1 m 0 x y) z) hn.symm).trans
    (congrArg (fun q : ℂ => η.1 (γ+c-β-1) 0 (θ.1 q 0 x y) z) hm.symm))).trans hdet

/-- Equality of every literal completed canonical iterate scalar pairing
forces equality of the actual carrier linear maps. -/
theorem leftTriple_linearMap_ext_of_completed_iterate
    {X : Type*} [AddCommGroup X] [Module ℂ X]
    (F G : RestrictedDual (leftTripleDual hC2 N₁ N₂ h₁ h₂ N₃ h₃).toGW →ₗ[ℂ] X)
    (heq : ∀ (f : X →ₗ[ℂ] ℂ) (a b c β : ℂ) (x : M₁) (y : M₂) (z : M₃)
      (hx : x∈N₁.weight a) (hy : y∈N₂.weight b) (hz : z∈N₃.weight c),
      ∀ t∈overlapDomain,
      completedLogIterate N₁ N₂ N₃ (leftTripleModule hC2 N₁ N₂ h₁ h₂ N₃ h₃)
        (tensorModule hC2 N₁ N₂ h₁ h₂)
        (tensorIntertwiner hC2 (tensorModule hC2 N₁ N₂ h₁ h₂) N₃
          (tensorModule_finGen hC2 N₁ N₂ h₁ h₂) h₃)
        (tensorIntertwiner hC2 N₁ N₂ h₁ h₂)
        t 0 c β (f ∘ₗ F) x y ⟨z,hz⟩=
      completedLogIterate N₁ N₂ N₃ (leftTripleModule hC2 N₁ N₂ h₁ h₂ N₃ h₃)
        (tensorModule hC2 N₁ N₂ h₁ h₂)
        (tensorIntertwiner hC2 (tensorModule hC2 N₁ N₂ h₁ h₂) N₃
          (tensorModule_finGen hC2 N₁ N₂ h₁ h₂) h₃)
        (tensorIntertwiner hC2 N₁ N₂ h₁ h₂)
        t 0 c β (f ∘ₗ G) x y ⟨z,hz⟩) : F=G := by
  let T := tensorModule hC2 N₁ N₂ h₁ h₂
  let L := leftTripleModule hC2 N₁ N₂ h₁ h₂ N₃ h₃
  have hfgT : FinGen T.toWeakModule := tensorModule_finGen hC2 N₁ N₂ h₁ h₂
  have hfgL : FinGen L.toWeakModule := tensorModule_finGen hC2 T N₃ hfgT h₃
  let η := tensorIntertwiner hC2 T N₃ hfgT h₃
  let θ := tensorIntertwiner hC2 N₁ N₂ h₁ h₂
  apply leftTriple_linearMap_ext_homogeneous hC2 N₁ N₂ N₃ h₁ h₂ h₃
  intro n m a b c x y z hx hy hz
  apply sub_eq_zero.mp
  apply (Module.forall_dual_apply_eq_zero_iff ℂ _).mp
  intro f
  rw [map_sub]
  apply sub_eq_zero.mpr
  let γ := a+b-m-1
  let β := γ+c-n-1
  have hdet := iterate_mode_eq_of_completed_eq hC2 N₁ N₂ N₃ L T
    h₁ h₂ h₃ hfgL hfgT η θ hx hy hz (f ∘ₗ F) (f ∘ₗ G) β
    (heq f a b c β x y z hx hy hz) γ 0
  have hn : γ+c-β-1=n := by dsimp only [β]; ring
  have hm : a+b-γ-1=m := by dsimp only [γ]; ring
  let v := η.1 (γ+c-β-1) 0 (θ.1 (a+b-γ-1) 0 x y) z
  have hv : η.1 n 0 (θ.1 m 0 x y) z=v :=
    (congrArg (fun q : ℂ => η.1 q 0 (θ.1 m 0 x y) z) hn.symm).trans
      (congrArg (fun q : ℂ => η.1 (γ+c-β-1) 0 (θ.1 q 0 x y) z) hm.symm)
  exact (congrArg (f ∘ₗ F) hv).trans (hdet.trans (congrArg (f ∘ₗ G) hv).symm)

end VOA.C2Rigid.LocalInjective
