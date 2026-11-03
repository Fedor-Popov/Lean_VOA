import VOA.Huang.LogAssocOutsideBlocks

/-! Finite-dimensional duality converts actual homogeneous outside
coefficient blocks into genuine outer mode blocks. Every value remains
in its stated generalized output-weight space. -/
set_option maxSynthPendingDepth 3
namespace VOA.Huang.LogAssocCoefficients
open VOA VOA.LogTensor VOA.LogTensor.Pz
open Module (Dual)
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable {R M₃ M₄ : Type u}
  [AddCommGroup R] [Module ℂ R] [AddCommGroup M₃] [Module ℂ M₃]
  [AddCommGroup M₄] [Module ℂ M₄]

/-- Actual evaluation against the homogeneous outside dual, as a functional
on that dual. There is no completion or formal vector in this construction. -/
noncomputable def outsideDoubleDual (N : LogVModule W R) (N₃ : LogVModule W M₃)
    (N₄ : LogVModule W M₄) (β c : ℂ)
    (A : Dual ℂ (N₄.weight β) →ₗ[ℂ] N₃.weight c →ₗ[ℂ] R)
    (ξ : C2Rigid.RestrictedDual N.toGW) (z : N₃.weight c) : Dual ℂ (Dual ℂ (N₄.weight β)) :=
  (C2Rigid.dualPairingFlip N.toGW ξ) ∘ₗ (A.flip z)

/-- The actual finite output block recovered by ordinary vector-space
reflexivity, retaining the genuine generalized module grading. -/
noncomputable def outerEvaluationBlock (N : LogVModule W R) (N₃ : LogVModule W M₃)
    (N₄ : LogVModule W M₄) (β c : ℂ)
    (A : Dual ℂ (N₄.weight β) →ₗ[ℂ] N₃.weight c →ₗ[ℂ] R) :
    C2Rigid.RestrictedDual N.toGW →ₗ[ℂ] N₃.weight c →ₗ[ℂ] N₄.weight β := by
  letI := N₄.finrank β
  refine LinearMap.mk₂ ℂ
    (fun ξ z => (Module.evalEquiv ℂ (N₄.weight β)).symm (outsideDoubleDual N N₃ N₄ β c A ξ z))
    ?_ ?_ ?_ ?_
  · intro ξ η z
    have he : outsideDoubleDual N N₃ N₄ β c A (ξ+η) z=
        outsideDoubleDual N N₃ N₄ β c A ξ z+outsideDoubleDual N N₃ N₄ β c A η z := by
      ext g
      exact (C2Rigid.dualPairing N.toGW (A g z)).map_add ξ η
    dsimp only
    rw [he,map_add]
  · intro s ξ z
    have he : outsideDoubleDual N N₃ N₄ β c A (s•ξ) z=
        s•outsideDoubleDual N N₃ N₄ β c A ξ z := by
      ext g
      exact (C2Rigid.dualPairing N.toGW (A g z)).map_smul s ξ
    dsimp only
    rw [he,map_smul]
  · intro ξ z z'
    have he : outsideDoubleDual N N₃ N₄ β c A ξ (z+z')=
        outsideDoubleDual N N₃ N₄ β c A ξ z+outsideDoubleDual N N₃ N₄ β c A ξ z' := by
      ext g
      change C2Rigid.dualPairingFlip N.toGW ξ (A g (z+z'))=_
      rw [map_add,map_add]
      rfl
    dsimp only
    rw [he,map_add]
  · intro s ξ z
    have he : outsideDoubleDual N N₃ N₄ β c A ξ (s•z)=
        s•outsideDoubleDual N N₃ N₄ β c A ξ z := by
      ext g
      change C2Rigid.dualPairingFlip N.toGW ξ (A g (s•z))=_
      rw [map_smul,map_smul]
      rfl
    dsimp only
    rw [he,map_smul]

/-- The outer output vector represents exactly the original outside block. -/
theorem outerEvaluationBlock_pair (N : LogVModule W R) (N₃ : LogVModule W M₃)
    (N₄ : LogVModule W M₄) (β c : ℂ)
    (A : Dual ℂ (N₄.weight β) →ₗ[ℂ] N₃.weight c →ₗ[ℂ] R)
    (ξ : C2Rigid.RestrictedDual N.toGW) (z : N₃.weight c) (g : Dual ℂ (N₄.weight β)) :
    g (outerEvaluationBlock N N₃ N₄ β c A ξ z)=C2Rigid.dualPairing N.toGW (A g z) ξ := by
  letI := N₄.finrank β
  exact Module.apply_evalEquiv_symm_apply ℂ (N₄.weight β) g
    (outsideDoubleDual N N₃ N₄ β c A ξ z)

/-- Pairing the recovered output with any actual supported functional gives
exactly its corresponding original outside coefficient. -/
theorem outerEvaluationBlock_supported_pair (N : LogVModule W R) (N₃ : LogVModule W M₃)
    (N₄ : LogVModule W M₄) (β c : ℂ)
    (A : Dual ℂ (N₄.weight β) →ₗ[ℂ] N₃.weight c →ₗ[ℂ] R)
    (ξ : C2Rigid.RestrictedDual N.toGW) (z : N₃.weight c) (f : Dual ℂ M₄) :
    f (outerEvaluationBlock N N₃ N₄ β c A ξ z : M₄)=
      C2Rigid.dualPairing N.toGW (A (f.domRestrict (N₄.weight β)) z) ξ :=
  outerEvaluationBlock_pair N N₃ N₄ β c A ξ z (f.domRestrict (N₄.weight β))

end VOA.Huang.LogAssocCoefficients
