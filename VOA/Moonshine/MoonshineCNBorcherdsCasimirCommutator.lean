import VOA.Moonshine.MoonshineCNBorcherdsCasimir
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-! Invariant dual-basis cancellation and finite, simultaneous-cutoff commutators. -/
noncomputable section
open scoped BigOperators TensorProduct
namespace VOA.Moonshine.ConwayNorton
open Module
variable {g M : Type*} [LieRing g] [LieAlgebra ℂ g] [AddCommGroup M] [Module ℂ M]

namespace BorcherdsData
variable (D : BorcherdsData g)

/-- The invariant dual-basis identity after any bilinear map, including the tensor map. -/
theorem rootBracketContraction {V : Type*} [AddCommGroup V] [Module ℂ V]
    (B : g →ₗ[ℂ] g →ₗ[ℂ] V) (α γ : ℤ × ℤ) (z : g) (hz : z ∈ D.weightSpace γ) :
    ∑ i, B ⁅(D.rootFiniteBasis α i : g), z⁆
        (D.rootOppositeBasis (D.rootFiniteBasis α) i) =
      -∑ j, B (D.rootFiniteBasis (α + γ) j)
        ⁅(D.rootOppositeBasis (D.rootFiniteBasis (α + γ)) j : g), z⁆ := by
  classical
  let b := D.rootFiniteBasis α
  let c := D.rootFiniteBasis (α + γ)
  have hm (i) : ⁅(b i : g), z⁆ ∈ D.weightSpace (α + γ) :=
    D.bracket_weight (b i).property hz
  have hn (j) : ⁅(D.rootOppositeBasis c j : g), z⁆ ∈ D.weightSpace (-α) := by
    have h := D.bracket_weight (D.rootOppositeBasis c j).property hz
    simpa only [neg_add, add_assoc, neg_add_cancel, add_zero] using h
  have hc (i j) : D.form ⁅(b i : g), z⁆ (D.rootOppositeBasis c j) =
      -D.form (b i) ⁅(D.rootOppositeBasis c j : g), z⁆ := by
    rw [D.form_invariant, ← lie_skew z (D.rootOppositeBasis c j), map_neg]
  change ∑ i, B ⁅(b i : g), z⁆ (D.rootOppositeBasis b i) =
    -∑ j, B (c j) ⁅(D.rootOppositeBasis c j : g), z⁆
  calc
    _ = ∑ i, ∑ j, D.form ⁅(b i : g), z⁆ (D.rootOppositeBasis c j) •
        B (c j) (D.rootOppositeBasis b i) := by
      apply Finset.sum_congr rfl
      intro i _
      have hexp := D.rootBasis_expansion c ⟨_, hm i⟩
      change (∑ j, D.form ⁅(b i : g), z⁆ (D.rootOppositeBasis c j) •
        (c j : g)) = ⁅(b i : g), z⁆ at hexp
      conv_lhs => rw [← hexp]
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
    _ = -∑ j, B (c j) (∑ i, D.form (b i)
        ⁅(D.rootOppositeBasis c j : g), z⁆ • (D.rootOppositeBasis b i : g)) := by
      simp_rw [hc, neg_smul, Finset.sum_neg_distrib]
      rw [Finset.sum_comm]
      simp only [map_sum, map_smul]
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      rw [D.rootOppositeBasis_expansion b ⟨_, hn j⟩]

theorem rootDualTensor_bracket_identity (α γ : ℤ × ℤ) (z : g)
    (hz : z ∈ D.weightSpace γ) :
    ∑ i, ⁅(D.rootFiniteBasis α i : g), z⁆ ⊗ₜ[ℂ]
        (D.rootOppositeBasis (D.rootFiniteBasis α) i : g) =
      -∑ j, (D.rootFiniteBasis (α + γ) j : g) ⊗ₜ[ℂ]
        ⁅(D.rootOppositeBasis (D.rootFiniteBasis (α + γ)) j : g), z⁆ :=
  D.rootBracketContraction (TensorProduct.mk ℂ g g) α γ z hz

variable (ρ : g →ₗ⁅ℂ⁆ End ℂ M)

def rootCasimirBoundaryTerm (z : g) (β : ℤ × ℤ) : End ℂ M :=
  ∑ i, ρ (D.rootFiniteBasis β i) *
    ρ ⁅(D.rootOppositeBasis (D.rootFiniteBasis β) i : g), z⁆

theorem rootCasimirTerm_commutator (α γ : ℤ × ℤ) (z : g)
    (hz : z ∈ D.weightSpace γ) :
    D.rootCasimirTerm ρ α * ρ z - ρ z * D.rootCasimirTerm ρ α =
      D.rootCasimirBoundaryTerm ρ z α - D.rootCasimirBoundaryTerm ρ z (α + γ) := by
  classical
  have hp (x y : g) :
      (ρ x * ρ y) * ρ z - ρ z * (ρ x * ρ y) =
        ρ ⁅x, z⁆ * ρ y + ρ x * ρ ⁅y, z⁆ := by
    rw [ρ.map_lie, ρ.map_lie]
    simp only [Ring.lie_def]
    noncomm_ring
  rw [D.rootCasimirTerm_eq_basis ρ α (D.rootFiniteBasis α),
    Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  simp_rw [hp]
  rw [Finset.sum_add_distrib]
  have hc := D.rootBracketContraction (rootActionContraction ρ) α γ z hz
  change (∑ i, ρ ⁅(D.rootFiniteBasis α i : g), z⁆ *
    ρ (D.rootOppositeBasis (D.rootFiniteBasis α) i)) =
      -D.rootCasimirBoundaryTerm ρ z (α + γ) at hc
  rw [hc]
  change -D.rootCasimirBoundaryTerm ρ z (α + γ) +
    D.rootCasimirBoundaryTerm ρ z α = _
  abel

end BorcherdsData

namespace BorcherdsAdmissible
variable {D : BorcherdsData g} {ρ : g →ₗ⁅ℂ⁆ End ℂ M} (A : BorcherdsAdmissible D ρ)

/-- The shifted boundary terms need the bound at μ + γ, not merely at μ. -/
theorem rootCasimirBoundaryTerm_height_vanishes {μ γ β : ℤ × ℤ} {v : M} {z : g}
    (hv : v ∈ A.weightSpace μ) (hz : z ∈ D.weightSpace γ)
    (hh : borcherdsRootHeight (μ + γ) - A.lowerHeight < borcherdsRootHeight β) :
    D.rootCasimirBoundaryTerm ρ z β v = 0 := by
  change (∑ i, ρ (D.rootFiniteBasis β i) *
    ρ ⁅(D.rootOppositeBasis (D.rootFiniteBasis β) i : g), z⁆) v = 0
  rw [LinearMap.sum_apply]
  apply Finset.sum_eq_zero
  intro i _
  have hm := A.action_weight
    (D.bracket_weight (D.rootOppositeBasis (D.rootFiniteBasis β) i).property hz) hv
  rw [A.below_eq_bot (μ + (-β + γ))] at hm
  · change ρ (D.rootFiniteBasis β i) _ = 0
    rw [show ρ ⁅(D.rootOppositeBasis (D.rootFiniteBasis β) i : g), z⁆ v = 0 from hm,
      map_zero]
  · simp only [borcherdsRootHeight, Prod.fst_add, Prod.snd_add,
      Prod.fst_neg, Prod.snd_neg] at *
    omega

/-- The full finite commutator calculation with a cutoff valid on both inputs. -/
theorem positiveCasimirOperator_commutator_cutoff {μ γ : ℤ × ℤ} {v : M} {z : g}
    (hv : v ∈ A.weightSpace μ) (hz : z ∈ D.weightSpace γ) (h : ℤ)
    (hμ : borcherdsRootHeight μ - A.lowerHeight ≤ h)
    (hγ : borcherdsRootHeight (μ + γ) - A.lowerHeight ≤ h) :
    A.positiveCasimirOperator (ρ z v) - ρ z (A.positiveCasimirOperator v) =
      ∑ α ∈ borcherdsRootCutoff h,
        (D.rootCasimirBoundaryTerm ρ z α v - D.rootCasimirBoundaryTerm ρ z (α + γ) v) := by
  rw [A.positiveCasimirOperator_eq_cutoff (A.action_weight hz hv) h hγ,
    A.positiveCasimirOperator_eq_cutoff hv h hμ, map_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro α _
  exact LinearMap.congr_fun (D.rootCasimirTerm_commutator ρ α γ z hz) v

end BorcherdsAdmissible
end VOA.Moonshine.ConwayNorton

