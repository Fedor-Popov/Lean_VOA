import VOA.Huang.LiFusionVacuum
import VOA.Huang.GenusOneWeightRealization

/-! # Li reconstruction at the genus-one interface

The scalar extension problem gives the existing `InsertionTopSurjectivity`,
and is proved in the vacuum-insertion sector. The general scalar extension
and `InsertionTopBimoduleExists` are independent remaining obligations: none
of the theorems below infer quotient actions from scalar reconstruction.
-/
namespace VOA.Huang.GenusOne
open VOA VOA.FZ FusionTop LiFusion
open scoped BigOperators
universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}
  {A : OrdVModule W M} {ι : Type u}

theorem insertionTopSurjectivity_of_scalarTopExtension (P : ι → LWModule W)
    (hext : ∀ i, ScalarTopExtension A (P i) (P i)) : InsertionTopSurjectivity A P :=
  fun i => topMapFZ_surjective_of_scalarTopExtension (hext i)

/-- An unconditional, nonzero insertion sector of the original interface. -/
theorem insertionTopSurjectivity_adjoint (P : ι → LWModule W)
    (hP : ∀ i, (P i).IsIrreducibleLW) :
    InsertionTopSurjectivity (adjointModule W) P :=
  fun i => topMapFZ_surjective_adjoint_self (P i) (hP i)

variable [Fintype ι]

/-- The scalar construction feeds the existing weight-selective trace
realization. The quotient bimodule is still an explicit, separate hypothesis. -/
theorem functional_realized_at_weight_of_scalarTopExtension (P : ι → LWModule W)
    (B : InsertionTopBimodule A P) (hext : ∀ i, ScalarTopExtension A (P i) (P i))
    (b : ℂ) (f : M →ₗ[ℂ] ℂ)
    (hO : fzO A.toWeakModule ≤ LinearMap.ker f)
    (hbal : ∀ (p : ℕ) (a : V), a ∈ W.grading (p : ℤ) → ∀ w,
      f (fzLeft A.toWeakModule p a w) = f (fzRight A.toWeakModule p a w))
    (homega : ∀ w, f (fzLeft A.toWeakModule 2 W.conformalVector w) =
      (b + W.centralCharge / 24) * f w) :
    ∃ Y : ∀ i, IntertwiningOperator A (P i).isMod (P i).isMod,
      (∀ i, (P i).h ≠ b + W.centralCharge / 24 → Y i = 0) ∧
      ∀ w, f w = ∑ i, trace (Y i) w b :=
  functional_realized_at_weight P B
    (insertionTopSurjectivity_of_scalarTopExtension P hext) b f hO hbal homega

end VOA.Huang.GenusOne
