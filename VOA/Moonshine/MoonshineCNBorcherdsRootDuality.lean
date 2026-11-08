import VOA.Moonshine.MoonshineCNBorcherdsData
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Dimension.Finrank

/-! Opposite-root perfect pairings and basis-independent finite contractions. -/
noncomputable section
open scoped BigOperators
namespace VOA.Moonshine.ConwayNorton
namespace BorcherdsData
open Module
variable {g : Type*} [LieRing g] [LieAlgebra ℂ g] (D : BorcherdsData g)

def rootPairingToDual (α : ℤ × ℤ) :
    D.weightSpace (-α) →ₗ[ℂ] Dual ℂ (D.weightSpace α) :=
  D.form.flip.compl₁₂ (D.weightSpace (-α)).subtype (D.weightSpace α).subtype

theorem rootPairingToDual_injective (α : ℤ × ℤ) :
    Function.Injective (D.rootPairingToDual α) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro y hy
  apply Subtype.ext
  apply D.form_nondegenerate (-α) y y.property
  intro x hx
  rw [neg_neg] at hx
  have h := LinearMap.congr_fun hy (⟨x, hx⟩ : D.weightSpace α)
  change D.form x y = 0 at h
  rw [D.form_symmetric]
  exact h

theorem rootPairingToDual_flip_injective (α : ℤ × ℤ) :
    Function.Injective (D.rootPairingToDual α).flip := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  apply Subtype.ext
  apply D.form_nondegenerate α x x.property
  intro y hy
  exact LinearMap.congr_fun hx (⟨y, hy⟩ : D.weightSpace (-α))

theorem rootPairingToDual_bijective (α : ℤ × ℤ) :
    Function.Bijective (D.rootPairingToDual α) := by
  letI := D.weight_finite (-α)
  exact ⟨D.rootPairingToDual_injective α,
    LinearMap.flip_injective_iff₁.mp (D.rootPairingToDual_flip_injective α)⟩

def rootPairingEquiv (α : ℤ × ℤ) :
    D.weightSpace (-α) ≃ₗ[ℂ] Dual ℂ (D.weightSpace α) :=
  LinearEquiv.ofBijective (D.rootPairingToDual α) (D.rootPairingToDual_bijective α)

variable {ι κ : Type*} [Fintype ι] [Fintype κ] {α : ℤ × ℤ}

def rootOppositeBasis (b : Basis ι ℂ (D.weightSpace α)) :
    Basis ι ℂ (D.weightSpace (-α)) := by
  classical
  exact b.dualBasis.map (D.rootPairingEquiv α).symm

theorem rootOppositeBasis_pairing (b : Basis ι ℂ (D.weightSpace α))
    (i : ι) (x : D.weightSpace α) :
    D.form x (D.rootOppositeBasis b i) = b.repr x i := by
  classical
  change D.rootPairingEquiv α ((D.rootPairingEquiv α).symm (b.dualBasis i)) x = _
  rw [LinearEquiv.apply_symm_apply, Basis.dualBasis_apply]

theorem rootOppositeBasis_repr (b : Basis ι ℂ (D.weightSpace α))
    (y : D.weightSpace (-α)) (i : ι) :
    (D.rootOppositeBasis b).repr y i = D.form (b i) y := by
  classical
  simp only [rootOppositeBasis, Basis.map_repr, LinearEquiv.symm_symm,
    LinearEquiv.trans_apply, Basis.dualBasis_repr]
  rfl

theorem rootBasis_expansion (b : Basis ι ℂ (D.weightSpace α))
    (x : D.weightSpace α) :
    ∑ i, D.form x (D.rootOppositeBasis b i) • (b i : g) = (x : g) := by
  simp_rw [D.rootOppositeBasis_pairing]
  exact (map_sum (D.weightSpace α).subtype _ _).symm.trans
    (congrArg (D.weightSpace α).subtype (b.sum_repr x))

theorem rootOppositeBasis_expansion (b : Basis ι ℂ (D.weightSpace α))
    (y : D.weightSpace (-α)) :
    ∑ i, D.form (b i) y • (D.rootOppositeBasis b i : g) = (y : g) := by
  simp_rw [← D.rootOppositeBasis_repr b y]
  exact (map_sum (D.weightSpace (-α)).subtype _ _).symm.trans
    (congrArg (D.weightSpace (-α)).subtype ((D.rootOppositeBasis b).sum_repr y))

/-- Any bilinear contraction of the canonical opposite-root tensor is independent of basis. -/
theorem rootContraction_basis_independent {V : Type*} [AddCommGroup V] [Module ℂ V]
    (B : g →ₗ[ℂ] g →ₗ[ℂ] V)
    (b : Basis ι ℂ (D.weightSpace α)) (c : Basis κ ℂ (D.weightSpace α)) :
    ∑ i, B (b i) (D.rootOppositeBasis b i) =
      ∑ j, B (c j) (D.rootOppositeBasis c j) := by
  classical
  calc
    _ = ∑ i, ∑ j, D.form (b i) (D.rootOppositeBasis c j) •
        B (c j) (D.rootOppositeBasis b i) := by
      apply Finset.sum_congr rfl
      intro i _
      conv_lhs => rw [← D.rootBasis_expansion c (b i)]
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
    _ = ∑ j, B (c j) (∑ i, D.form (b i) (D.rootOppositeBasis c j) •
        (D.rootOppositeBasis b i : g)) := by
      rw [Finset.sum_comm]
      simp only [map_sum, map_smul]
    _ = _ := by simp_rw [D.rootOppositeBasis_expansion]

/-- A fixed finite basis used only to implement basis-independent contractions. -/
def rootFiniteBasis (α : ℤ × ℤ) :
    Basis (Fin (Module.finrank ℂ (D.weightSpace α))) ℂ (D.weightSpace α) := by
  letI := D.weight_finite α
  exact Module.finBasis ℂ (D.weightSpace α)

end BorcherdsData
end VOA.Moonshine.ConwayNorton

