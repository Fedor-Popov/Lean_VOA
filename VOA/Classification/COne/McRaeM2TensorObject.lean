import VOA.Classification.COne.McRaeM2TensorFiniteLength

/-! # The actual candidate logarithmic tensor object and its canonical operator

The contragredient of the genuine maximal compatible module is an actual
grading-restricted generalized module. Its compatible inclusion reconstructs
a genuine logarithmic intertwining operator. The universal property is a
separate theorem; it is not part of this construction's hypotheses.
-/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.C2Rigid.LocalInjective
open VOA.Classification.COne VOA.LogTensor VOA.LogTensor.Pz

universe u
variable {V M₁ M₂ : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  {W : VertexOperatorAlgebra V}
variable (hC2 : C2Cofinite W)
  (N₁ : LogVModule W M₁) (N₂ : LogVModule W M₂)
  (h₁ : FinGen N₁.toWeakModule) (h₂ : FinGen N₂.toWeakModule)

abbrev tensorDual := maximalLogModule hC2 N₁ N₂ h₁ h₂

/-- The genuine grading-restricted generalized tensor candidate. -/
def tensorModule : LogVModule W (RestrictedDual (tensorDual hC2 N₁ N₂ h₁ h₂).toGW) :=
  contraLog (tensorDual hC2 N₁ N₂ h₁ h₂)

/-- The actual compatible inclusion of the maximal module in the tensor dual. -/
def tensorInclusion : compatibleMaps N₁ N₂ (tensorDual hC2 N₁ N₂ h₁ h₂) :=
  homToCompatible N₁ N₂ (tensorDual hC2 N₁ N₂ h₁ h₂)
    (maximalCompatibleSpace N₁.toWeakModule N₂.toWeakModule)
    ⟨LinearMap.id,fun _ _ _ => rfl⟩

/-- Its underlying map is exactly the inclusion of the actual compatible carrier. -/
theorem tensorInclusion_apply (b : maximalCarrier N₁.toWeakModule N₂.toWeakModule) :
    (tensorInclusion hC2 N₁ N₂ h₁ h₂).1 b = b.1 := rfl

/-- The canonical genuine logarithmic operator, with full Jacobi and derivative. -/
def tensorIntertwiner : LogIntertwiningOperator N₁.toWeakModule N₂.toWeakModule
    (tensorModule hC2 N₁ N₂ h₁ h₂).toWeakModule :=
  reconstruction N₁ N₂ (tensorDual hC2 N₁ N₂ h₁ h₂)
    (tensorInclusion hC2 N₁ N₂ h₁ h₂)

/-- A nonzero actual compatible space gives a nonzero canonical logarithmic operator. -/
theorem tensorIntertwiner_ne_zero
    (hne : maximalCarrier N₁.toWeakModule N₂.toWeakModule ≠ ⊥) :
    tensorIntertwiner hC2 N₁ N₂ h₁ h₂ ≠ 0 := by
  intro h
  have hi : tensorInclusion hC2 N₁ N₂ h₁ h₂ = 0 :=
    reconstruction_injective N₁ N₂ (tensorDual hC2 N₁ N₂ h₁ h₂)
      (h.trans (map_zero _).symm)
  obtain ⟨b,hb,hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have he := congrArg
    (fun p : compatibleMaps N₁ N₂ (tensorDual hC2 N₁ N₂ h₁ h₂) => p.1 ⟨b,hb⟩) hi
  exact hb0 he

end VOA.C2Rigid.LocalInjective
