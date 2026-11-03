import VOA.Modules.PoissonDescent
import VOA.Modularity.Twisted
import Mathlib.RingTheory.Finiteness.Finsupp

/-!
# The intrinsic C₂ obstruction for a subVOA

The inclusion of a subVOA induces a map of C₂ quotients, but need not induce
an injection. For a C₂-cofinite ambient VOA, precisely its kernel must be
controlled. This prevents an invalid inference from finite-dimensional
ambient invariants to the intrinsic orbifold quotient.
-/

noncomputable section
namespace VOA.Classification.COne.OrbC2
open VOA VertexOperatorAlgebra
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V]
  {W : VertexOperatorAlgebra V}

/-- Intrinsic `C₂(S)` maps into ambient `C₂(W)`. The reverse inclusion is not asserted. -/
theorem subalgebra_c2_le (S : VOASubalgebra W) :
    O₂ S.toVOA ≤ (O₂ W).comap S.carrier.subtype := by
  apply Submodule.span_le.mpr
  rintro _ ⟨a, b, rfl⟩
  exact Submodule.subset_span ⟨a.val, b.val, rfl⟩

/-- The actual inclusion-induced map on C₂ quotients. -/
def inclusionC2 (S : VOASubalgebra W) : A₂ S.toVOA →ₗ[ℂ] A₂ W :=
  (O₂ S.toVOA).liftQ ((mk₂ W).comp S.carrier.subtype) (by
    intro x hx
    exact (mk₂_eq_zero_iff W).mpr (subalgebra_c2_le S hx))

@[simp] theorem inclusionC2_mk (S : VOASubalgebra W) (v : S.carrier) :
    inclusionC2 S (mk₂ S.toVOA v) = mk₂ W v.val := rfl

/-- Kernel membership is exactly ambient C₂ membership of a fixed representative. -/
theorem mk_mem_ker_inclusionC2 (S : VOASubalgebra W) (v : S.carrier) :
    mk₂ S.toVOA v ∈ LinearMap.ker (inclusionC2 S) ↔ v.val ∈ O₂ W := by
  rw [LinearMap.mem_ker, inclusionC2_mk, mk₂_eq_zero_iff]

/-- The ambient quotient controls only the image; the kernel is the missing part. -/
theorem c2Cofinite_iff_finite_kernel (S : VOASubalgebra W) (hW : C2Cofinite W) :
    C2Cofinite S.toVOA ↔ FiniteDimensional ℂ (LinearMap.ker (inclusionC2 S)) := by
  constructor
  · intro hS
    letI : FiniteDimensional ℂ (A₂ S.toVOA) := hS
    infer_instance
  · intro hK
    letI : FiniteDimensional ℂ (A₂ W) := hW
    letI : FiniteDimensional ℂ (LinearMap.ker (inclusionC2 S)) := hK
    letI : FiniteDimensional ℂ
        (A₂ S.toVOA ⧸ LinearMap.ker (inclusionC2 S)) :=
      LinearEquiv.finiteDimensional (inclusionC2 S).quotKerEquivRange.symm
    exact Module.Finite.of_submodule_quotient (LinearMap.ker (inclusionC2 S))

/-- Concrete spanning criterion: control the classes of ambient C₂ elements
that lie in the subVOA, not only the images in the ambient quotient. -/
theorem c2Cofinite_of_ambient_c2_span (S : VOASubalgebra W) (hW : C2Cofinite W)
    (s : Finset (A₂ S.toVOA))
    (hspan : ∀ v : S.carrier, v.val ∈ O₂ W →
      mk₂ S.toVOA v ∈ Submodule.span ℂ (s : Set (A₂ S.toVOA))) :
    C2Cofinite S.toVOA := by
  apply (c2Cofinite_iff_finite_kernel S hW).mpr
  have hle : LinearMap.ker (inclusionC2 S) ≤ Submodule.span ℂ (s : Set (A₂ S.toVOA)) := by
    intro x hx
    obtain ⟨v, rfl⟩ := mk₂_surjective S.toVOA x
    exact hspan v ((mk_mem_ker_inclusionC2 S v).mp hx)
  letI : FiniteDimensional ℂ (Submodule.span ℂ (s : Set (A₂ S.toVOA))) :=
    Module.Finite.of_fg (Submodule.fg_span s.finite_toSet)
  exact FiniteDimensional.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)

end VOA.Classification.COne.OrbC2
