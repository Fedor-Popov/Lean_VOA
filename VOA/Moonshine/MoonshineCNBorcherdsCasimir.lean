import VOA.Moonshine.MoonshineCNBorcherdsRootCutoff
import VOA.Moonshine.MoonshineCNBorcherdsRootDuality
import Mathlib.Algebra.Algebra.Bilinear

/-! The locally finite Casimir operator and its lowest-weight evaluation.
Centrality for non-Cartan root operators is not assumed by this construction. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace VOA.Moonshine.ConwayNorton
open Module
variable {g M : Type*} [LieRing g] [LieAlgebra ℂ g] [AddCommGroup M] [Module ℂ M]

def rootActionContraction (ρ : g →ₗ⁅ℂ⁆ End ℂ M) : g →ₗ[ℂ] g →ₗ[ℂ] End ℂ M :=
  (LinearMap.mul ℂ (End ℂ M)).compl₁₂ ρ.toLinearMap ρ.toLinearMap

namespace BorcherdsData
variable (D : BorcherdsData g) (ρ : g →ₗ⁅ℂ⁆ End ℂ M)

def rootCasimirTerm (α : ℤ × ℤ) : End ℂ M :=
  ∑ i, rootActionContraction ρ (D.rootFiniteBasis α i)
    (D.rootOppositeBasis (D.rootFiniteBasis α) i)

theorem rootCasimirTerm_eq_basis {ι : Type*} [Fintype ι] (α : ℤ × ℤ)
    (b : Basis ι ℂ (D.weightSpace α)) :
    D.rootCasimirTerm ρ α = ∑ i, ρ (b i) * ρ (D.rootOppositeBasis b i) :=
  D.rootContraction_basis_independent (rootActionContraction ρ) (D.rootFiniteBasis α) b

theorem rootCasimirTerm_apply (α : ℤ × ℤ) (v : M) :
    D.rootCasimirTerm ρ α v =
      ∑ i, ρ (D.rootFiniteBasis α i) (ρ (D.rootOppositeBasis (D.rootFiniteBasis α) i) v) := by
  rw [D.rootCasimirTerm_eq_basis ρ α (D.rootFiniteBasis α)]
  simp only [LinearMap.sum_apply, Module.End.mul_apply]

theorem rootCasimirTerm_zero_of_lowering (α : ℤ × ℤ) (v : M)
    (hv : ∀ x ∈ D.weightSpace (-α), ρ x v = 0) :
    D.rootCasimirTerm ρ α v = 0 := by
  rw [D.rootCasimirTerm_apply]
  apply Finset.sum_eq_zero
  intro i _
  rw [hv _ (D.rootOppositeBasis (D.rootFiniteBasis α) i).property, map_zero]

/-- Cartan contraction in the coordinate basis, followed by the Weyl correction ρ = (1,0). -/
def cartanCasimirOperator : End ℂ M :=
  -(ρ (D.cartanMap (1, 0)) * ρ (D.cartanMap (0, 1))) -
    ρ (D.cartanMap (0, 1)) * ρ (D.cartanMap (1, 0)) -
      (2 : ℂ) • ρ (D.cartanMap (1, 0))

end BorcherdsData

namespace BorcherdsAdmissible
variable {D : BorcherdsData g} {ρ : g →ₗ⁅ℂ⁆ End ℂ M} (A : BorcherdsAdmissible D ρ)

theorem rootCasimirTerm_height_vanishes {μ α : ℤ × ℤ} {v : M}
    (hv : v ∈ A.weightSpace μ)
    (hh : borcherdsRootHeight μ - A.lowerHeight < borcherdsRootHeight α) :
    D.rootCasimirTerm ρ α v = 0 :=
  D.rootCasimirTerm_zero_of_lowering ρ α v
    (fun _ hx => A.lowering_eq_zero_of_height hv hx hh)

theorem rootCasimirTerm_preserves_weight {μ : ℤ × ℤ} {v : M}
    (hv : v ∈ A.weightSpace μ) (α : ℤ × ℤ) :
    D.rootCasimirTerm ρ α v ∈ A.weightSpace μ := by
  rw [D.rootCasimirTerm_apply]
  apply Submodule.sum_mem
  intro i _
  have h := A.action_weight (D.rootFiniteBasis α i).property
    (A.action_weight (D.rootOppositeBasis (D.rootFiniteBasis α) i).property hv)
  simpa only [neg_add_cancel_right] using h

include A in
theorem rootCasimirTerms_finiteSupport (v : M) :
    Function.HasFiniteSupport
      (fun α => if borcherdsPositiveRoot α then D.rootCasimirTerm ρ α v else 0) := by
  classical
  apply borcherdsRootTerms_finiteSupport
  obtain ⟨h, hh⟩ := A.exists_lowering_height_bound v
  exact ⟨h, fun α _ hα => D.rootCasimirTerm_zero_of_lowering ρ α v
    (fun x hx => hh α x hx hα)⟩

def positiveCasimirOperator : End ℂ M :=
  borcherdsLocallyFiniteRootSum (D.rootCasimirTerm ρ) A.rootCasimirTerms_finiteSupport

/-- Ω is an actual linear endomorphism, with pointwise finite positive-root summation. -/
def casimirOperator : End ℂ M :=
  D.cartanCasimirOperator ρ + (2 : ℂ) • A.positiveCasimirOperator

theorem positiveCasimirOperator_eq_cutoff {μ : ℤ × ℤ} {v : M}
    (hv : v ∈ A.weightSpace μ) (h : ℤ)
    (hh : borcherdsRootHeight μ - A.lowerHeight ≤ h) :
    A.positiveCasimirOperator v = ∑ α ∈ borcherdsRootCutoff h, D.rootCasimirTerm ρ α v :=
  borcherdsLocallyFiniteRootSum_eq_cutoff _ _ v h
    (fun _ _ hα => A.rootCasimirTerm_height_vanishes hv (lt_of_le_of_lt hh hα))

theorem positiveCasimirOperator_preserves_weight {μ : ℤ × ℤ} {v : M}
    (hv : v ∈ A.weightSpace μ) :
    A.positiveCasimirOperator v ∈ A.weightSpace μ := by
  rw [A.positiveCasimirOperator_eq_cutoff hv _ le_rfl]
  exact Submodule.sum_mem _ (fun α _ => A.rootCasimirTerm_preserves_weight hv α)

theorem cartanCasimirOperator_on_weight {μ : ℤ × ℤ} {v : M}
    (hv : v ∈ A.weightSpace μ) :
    D.cartanCasimirOperator ρ v = borcherdsCasimirScalar μ • v := by
  have h₁ := A.cartan_action (1, 0) hv
  have h₂ := A.cartan_action (0, 1) hv
  simp only [BorcherdsData.cartanCasimirOperator, LinearMap.sub_apply, LinearMap.neg_apply,
    LinearMap.smul_apply, Module.End.mul_apply]
  rw [h₂, h₁]
  simp only [map_smul, h₁, h₂, borcherdsCasimirScalar, borcherdsCartanPairing,
    borcherdsWeightVector]
  module

theorem casimirOperator_preserves_weight {μ : ℤ × ℤ} {v : M}
    (hv : v ∈ A.weightSpace μ) :
    A.casimirOperator v ∈ A.weightSpace μ := by
  change D.cartanCasimirOperator ρ v + (2 : ℂ) • A.positiveCasimirOperator v ∈ _
  rw [A.cartanCasimirOperator_on_weight hv]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ hv)
    (Submodule.smul_mem _ _ (A.positiveCasimirOperator_preserves_weight hv))

theorem casimirOperator_commutes_cartan (ξ : ℂ × ℂ) (v : M) :
    A.casimirOperator (ρ (D.cartanMap ξ) v) = ρ (D.cartanMap ξ) (A.casimirOperator v) := by
  have hv : v ∈ ⨆ μ, A.weightSpace μ := by
    rw [A.weight_internal.submodule_iSup_eq_top]
    trivial
  induction hv using Submodule.iSup_induction' with
  | mem μ v hv =>
      rw [A.cartan_action ξ hv, map_smul,
        A.cartan_action ξ (A.casimirOperator_preserves_weight hv)]
  | zero => simp
  | add v w _ _ hv hw => simp only [map_add, hv, hw]

/-- Lowest vectors have eigenvalue (μ,μ) - 2(ρ,μ), with no centrality hypothesis. -/
theorem casimirOperator_lowest_vector {μ : ℤ × ℤ} {v : M}
    (hv : v ∈ A.weightSpace μ)
    (hlow : ∀ α, borcherdsPositiveRoot α → ∀ x ∈ D.weightSpace (-α), ρ x v = 0) :
    A.casimirOperator v = borcherdsCasimirScalar μ • v := by
  change D.cartanCasimirOperator ρ v + (2 : ℂ) • A.positiveCasimirOperator v = _
  rw [A.cartanCasimirOperator_on_weight hv,
    A.positiveCasimirOperator_eq_cutoff hv _ le_rfl]
  have hz : ∑ α ∈ borcherdsRootCutoff (borcherdsRootHeight μ - A.lowerHeight),
      D.rootCasimirTerm ρ α v = 0 := by
    apply Finset.sum_eq_zero
    intro α hα
    exact D.rootCasimirTerm_zero_of_lowering ρ α v
      (hlow α ((mem_borcherdsRootCutoff _ _).mp hα).1)
  rw [hz, smul_zero, add_zero]

/-- The numerical obstruction used by the later kernel argument. -/
theorem lowest_casimir_zero_first_coordinate {μ : ℤ × ℤ} {v : M}
    (hv : v ∈ A.weightSpace μ) (hv0 : v ≠ 0) (hμ : borcherdsPositiveCone μ)
    (hlow : ∀ α, borcherdsPositiveRoot α → ∀ x ∈ D.weightSpace (-α), ρ x v = 0)
    (hΩ : A.casimirOperator v = 0) : μ.1 = 1 := by
  rw [A.casimirOperator_lowest_vector hv hlow] at hΩ
  exact (borcherdsCasimirScalar_zero_iff hμ).mp ((smul_eq_zero.mp hΩ).resolve_right hv0)

end BorcherdsAdmissible
end VOA.Moonshine.ConwayNorton

