import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Linear separation for the rectangular polynomial recursion

The shift image in the FJKLM recursion is a linear subspace, not an ideal.
Algebraic dual separation turns a functional argument for every ideal
consequence into the required inclusion modulo that subspace. No finite
dimensionality of the polynomial algebra is needed.

The polynomial primitive and the actual coefficient-ideal preservation are
separate obligations. The lemmas here do not assert those polynomial facts.
-/

namespace VOA.DeligneAudit.CVRectSeparation

noncomputable section

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Vanishing against every functional annihilating both subspaces proves
membership in their sum, even in an infinite-dimensional ambient space. -/
theorem mem_sup_of_functional (J U : Submodule K V) (v : V)
    (h : ∀ ℓ : Module.Dual K V, J ≤ LinearMap.ker ℓ →
      U ≤ LinearMap.ker ℓ → ℓ v = 0) : v ∈ J ⊔ U := by
  apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff (J ⊔ U) v).mp
  intro ℓ hℓ
  have hker : J ⊔ U ≤ LinearMap.ker ℓ := by
    intro x hx
    exact (Submodule.mem_dualAnnihilator ℓ).mp hℓ x hx
  exact h ℓ (le_trans le_sup_left hker) (le_trans le_sup_right hker)

/-- A functional proof for all elements of the target ideal gives actual
primitive preservation modulo the shift image. No ideal-invariance property
of the shift image is assumed. -/
theorem primitive_preserves_of_functional (J U L : Submodule K V) (I : V →ₗ[K] V)
    (h : ∀ ℓ : Module.Dual K V, J ≤ LinearMap.ker ℓ →
      U ≤ LinearMap.ker ℓ → L ≤ LinearMap.ker (ℓ.comp I)) :
    L ≤ (J ⊔ U).comap I := by
  intro p hp
  exact mem_sup_of_functional J U (I p) fun ℓ hJ hU => h ℓ hJ hU hp

/-- Integration induces a surjection after quotienting by the shift image:
`I(Dp)` differs from `p` by a member of that image. The descent hypothesis
must be established for the whole source submodule. -/
theorem primitive_quotient_surjective (J U L : Submodule K V)
    (I D : V →ₗ[K] V) (hdesc : L ≤ (J ⊔ U).comap I)
    (hprimitive : ∀ p, p - I (D p) ∈ U) :
    Function.Surjective (L.mapQ (J ⊔ U) I hdesc) := by
  intro q
  obtain ⟨p, rfl⟩ := (J ⊔ U).mkQ_surjective q
  refine ⟨L.mkQ (D p), ?_⟩
  change Submodule.Quotient.mk (I (D p)) = Submodule.Quotient.mk p
  apply (Submodule.Quotient.eq (J ⊔ U)).mpr
  apply (show U ≤ J ⊔ U from le_sup_right)
  simpa only [neg_sub] using U.neg_mem (hprimitive p)

/-- The actual primitive quotient has a finite-dimensional target whenever
its source is finite-dimensional. This is the upper-bound direction. -/
theorem primitive_quotient_bound (J U L : Submodule K V)
    (I D : V →ₗ[K] V) (hdesc : L ≤ (J ⊔ U).comap I)
    (hprimitive : ∀ p, p - I (D p) ∈ U)
    [FiniteDimensional K (V ⧸ L)] :
    FiniteDimensional K (V ⧸ (J ⊔ U)) ∧
      Module.finrank K (V ⧸ (J ⊔ U)) ≤ Module.finrank K (V ⧸ L) := by
  have hs := primitive_quotient_surjective J U L I D hdesc hprimitive
  exact ⟨Module.Finite.of_surjective _ hs,
    LinearMap.finrank_le_finrank_of_surjective hs⟩

/-- Two successive polynomial quotient pieces give the total upper bound.
The image equality is an exact statement about the actual maps, not a
dimension recurrence supplied as a premise. -/
theorem finite_dimensional_two_term
    {T A : Type*} [AddCommGroup T] [Module K T]
    [AddCommGroup A] [Module K A]
    (π : V →ₗ[K] T) (f : A →ₗ[K] V)
    (hπ : Function.Surjective π) (hf : LinearMap.range f = LinearMap.ker π)
    [FiniteDimensional K T] [FiniteDimensional K A] :
    FiniteDimensional K V ∧
      Module.finrank K V ≤ Module.finrank K T + Module.finrank K A := by
  haveI : FiniteDimensional K V := Module.Finite.of_exact (f := f) (g := π)
    (LinearMap.exact_iff.mpr hf.symm) hπ
  refine ⟨inferInstance, ?_⟩
  have he := π.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hπ, finrank_top, ← hf] at he
  have hb := LinearMap.finrank_range_le f
  exact he.symm.trans_le (Nat.add_le_add_left hb _)

end

end VOA.DeligneAudit.CVRectSeparation

#print axioms VOA.DeligneAudit.CVRectSeparation.primitive_preserves_of_functional
#print axioms VOA.DeligneAudit.CVRectSeparation.primitive_quotient_surjective
#print axioms VOA.DeligneAudit.CVRectSeparation.primitive_quotient_bound
#print axioms VOA.DeligneAudit.CVRectSeparation.finite_dimensional_two_term
