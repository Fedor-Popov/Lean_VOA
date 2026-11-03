import VOA.Classification.COne.ABDWeakAdmissibleNormal
import VOA.Modules.OrdSubmodule

/-! Restricting an arbitrary weak action to its cyclic submodule. -/
namespace VOA.Classification.COne.ABDWeakAdmissible
open PlusRational VOA.Huang.LogRemovalAdmissible

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
  {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- The seed still generates after restricting the weak action to its cyclic submodule. -/
theorem cyclic_restriction_eq_top (A : WeakModule W M) (x : M) :
    let P := ofR A (cyclic A x)
    let B := WeakModule.submodule A P
    cyclic B (⟨x, Submodule.mem_span_singleton_self x⟩ : P.carrier) = ⊤ := by
  let P := ofR A (cyclic A x)
  let B := WeakModule.submodule A P
  let z : P.carrier := ⟨x, Submodule.mem_span_singleton_self x⟩
  let Q := ofR B (cyclic B z)
  let R : WeakModule.Submodule' A :=
    { carrier := Q.carrier.map P.carrier.subtype
      act_mem := by
        intro a n y hy
        obtain ⟨v, hv, rfl⟩ := hy
        exact ⟨B.act a n v, Q.act_mem a n hv, rfl⟩ }
  have hle : cyclic A x ≤ toR A R := by
    apply Submodule.span_le.mpr
    rw [Set.singleton_subset_iff]
    exact ⟨z, Submodule.mem_span_singleton_self z, rfl⟩
  apply top_unique
  intro y _
  obtain ⟨v, hv, he⟩ := hle y.property
  have hvy : v = y := Subtype.ext he
  exact hvy ▸ hv

/-- Every nonzero maximal generalized eigenspace contains an actual eigenvector. -/
theorem exists_eigenvector_of_maxGenEigenspace_ne_bot (A : WeakModule W M) (α : ℂ)
    (hα : (L0 A).maxGenEigenspace α ≠ ⊥) :
    ∃ x : M, x ≠ 0 ∧ L0 A x = α • x := by
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hα
  obtain ⟨k, hk⟩ := Module.End.mem_genEigenspace_top.mp hx
  have hgen : (L0 A).HasGenEigenvalue α k := by
    intro h
    rw [Module.End.genEigenspace_nat] at h
    rw [h] at hk
    exact hx0 hk
  obtain ⟨y, hy⟩ := (Module.End.hasEigenvalue_of_hasGenEigenvalue hgen).exists_hasEigenvector
  exact ⟨y, hy.2, hy.apply_eq_smul⟩

end VOA.Classification.COne.ABDWeakAdmissible
