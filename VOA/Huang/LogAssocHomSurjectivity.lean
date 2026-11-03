import VOA.Huang.LogAssocOutsideBlocks
import VOA.Modules.LogTensorTwist

/-! Actual generalized-weight supported functionals detect the range of
any genuine module homomorphism. This is linear algebra in the actual
carriers, using their proved internal generalized-weight decompositions. -/
set_option maxSynthPendingDepth 3
namespace VOA.Huang.LogAssocExpansion
open VOA VOA.LogTensor VOA.LogTensor.Pz VOA.LogTensor.Contra
open VOA.Huang.LogAssocCoefficients VOA.Huang.LogAssocCoefficientCompatibility
open Module (Dual)
universe u
variable {V M P : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] [AddCommGroup P] [Module ℂ P]
  {W : VertexOperatorAlgebra V}

/-- If every genuine supported annihilator of a module map is zero,
its actual carrier map is surjective. -/
theorem surjective_of_supported_annihilators (N : LogVModule W M) (Q : LogVModule W P)
    (F : N.toWeakModule.Hom Q.toWeakModule)
    (h : ∀ β : ℂ,∀ f : Dual ℂ P,SupportedAt Q f β → f ∘ₗ F.toLinearMap=0 → f=0) :
    Function.Surjective F.toLinearMap := by
  have hRange : LinearMap.range F.toLinearMap=⊤ := by
    apply top_unique
    rw [← LogFin.iSup_weight_eq_top Q]
    apply iSup_le
    intro β
    let B := (LinearMap.range F.toLinearMap).comap (Q.weight β).subtype
    have hB : B=⊤ := by
      apply (Submodule.dualAnnihilator_eq_bot_iff).mp
      rw [Submodule.eq_bot_iff]
      intro g hg
      let f := extendedFunctional Q β g
      have hf : SupportedAt Q f β := extendedFunctional_supported Q β g
      have hcomp : f ∘ₗ F.toLinearMap=0 := by
        apply LinearMap.ext
        intro x
        refine LogFin.induction_on N (C := fun x => f (F.toLinearMap x)=0) x ?_ ?_ ?_
        · intro a x hx
          have hFx := hom_mem_weight N Q F hx
          by_cases ha : a=β
          · subst a
            rw [extendedFunctional_of_mem Q g hFx]
            apply (Submodule.mem_dualAnnihilator g).mp hg
            change F.toLinearMap x∈LinearMap.range F.toLinearMap
            exact ⟨x,rfl⟩
          · exact hf a ha _ hFx
        · simp
        · intro x y hx hy
          rw [map_add,map_add,hx,hy,add_zero]
      have hf0 : f=0 := h β f hf hcomp
      apply LinearMap.ext
      intro q
      have he := congrArg (fun f : Dual ℂ P => f (q : P)) hf0
      dsimp only [f] at he
      rw [extendedFunctional_of_mem Q g q.2] at he
      exact he
    intro q hq
    have hm : (⟨q,hq⟩ : Q.weight β)∈B := hB ▸ Submodule.mem_top
    exact hm
  exact LinearMap.range_eq_top.mp hRange

end VOA.Huang.LogAssocExpansion
