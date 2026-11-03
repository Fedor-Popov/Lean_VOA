import VOA.Modularity.ZhuAlgebraFinite
import VOA.Modules.ZhuRingInstance
import Mathlib.LinearAlgebra.Eigenspace.Minpoly

/-!
# A finite bound on Zhu conformal eigenvalues without semisimplicity

The conformal element of the finite-dimensional Zhu algebra has a nonzero
annihilating polynomial. Its roots bound its eigenvalues in every representation,
including infinite-dimensional and nonsemisimple representations.

This supplies a spectral bound, not the missing construction of a detecting
subspace in an arbitrary weak subquotient of an admissible module.
-/

namespace VOA.Classification.COne.C2WindowDetects

open Polynomial

attribute [local instance] instRingA instAlgebraA

universe u v

/-- A polynomial relation in an algebra bounds eigenvalues in every representation.
There is no finite-dimensionality assumption on the representation. -/
theorem isRoot_of_aeval_eq_zero
    {B : Type u} [Ring B] [Algebra ℂ B] {a : B} {p : ℂ[X]}
    (hp : aeval a p = 0)
    {U : Type v} [AddCommGroup U] [Module ℂ U] [Module B U] [IsScalarTower ℂ B U]
    {μ : ℂ} {y : U} (hy : y ≠ 0) (he : a • y = μ • y) : p.IsRoot μ := by
  let f : B →ₐ[ℂ] Module.End ℂ U := Algebra.lsmul ℂ ℂ U
  have hf : aeval (f a) p = 0 := by
    rw [aeval_algHom_apply, hp, map_zero]
  have hz : p.eval μ • y = 0 := by
    rw [← Module.End.aeval_apply_of_mem_apply_eq_smul (f := f a) he, hf]
    rfl
  exact (smul_eq_zero.mp hz).resolve_right hy

/-- A single monic polynomial annihilates the Zhu conformal element. -/
theorem exists_zhu_conformal_polynomial
    {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
    (W : VertexOperatorAlgebra 𝒱) (hC2 : C2Cofinite W) :
    ∃ p : ℂ[X], p.Monic ∧ aeval (mk W W.conformalVector) p = 0 := by
  letI := finiteDimensional_A_of_C2Cofinite W hC2
  exact IsIntegral.of_finite ℂ (mk W W.conformalVector)

/-- All eigenvalues of the Zhu conformal element, in all representations, lie
in one finite set. No Zhu semisimplicity or PBW datum is used. -/
theorem exists_finite_zhu_conformal_spectrum
    {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
    (W : VertexOperatorAlgebra 𝒱) (hC2 : C2Cofinite W) :
    ∃ s : Finset ℂ, ∀ {U : Type v} [AddCommGroup U] [Module ℂ U]
      [Module (A W) U] [IsScalarTower ℂ (A W) U] (μ : ℂ) (y : U),
      y ≠ 0 → (mk W W.conformalVector) • y = μ • y → μ ∈ s := by
  classical
  obtain ⟨p, hp, hpa⟩ := exists_zhu_conformal_polynomial W hC2
  refine ⟨p.roots.toFinset, ?_⟩
  intro U _ _ _ _ μ y hy he
  exact Multiset.mem_toFinset.mpr ((mem_roots hp.ne_zero).mpr
    (isRoot_of_aeval_eq_zero hpa hy he))

/-- In particular their real parts admit a uniform upper bound. -/
theorem exists_zhu_conformal_real_bound
    {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
    (W : VertexOperatorAlgebra 𝒱) (hC2 : C2Cofinite W) :
    ∃ B : ℝ, ∀ {U : Type v} [AddCommGroup U] [Module ℂ U]
      [Module (A W) U] [IsScalarTower ℂ (A W) U] (μ : ℂ) (y : U),
      y ≠ 0 → (mk W W.conformalVector) • y = μ • y → μ.re ≤ B := by
  obtain ⟨s, hs⟩ := exists_finite_zhu_conformal_spectrum.{u, v} W hC2
  obtain ⟨B, hB⟩ := (s.finite_toSet.image Complex.re).bddAbove
  refine ⟨B, ?_⟩
  intro U _ _ _ _ μ y hy he
  exact hB ⟨μ, hs μ y hy he, rfl⟩

end VOA.Classification.COne.C2WindowDetects
