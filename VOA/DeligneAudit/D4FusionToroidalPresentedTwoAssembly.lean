import VOA.DeligneAudit.D4FusionToroidalPresentedTwoZeroRank
import VOA.DeligneAudit.D4FusionToroidalPresentedEigRank
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! Conditional final assembly from the two positive-u-degree layers. -/

namespace VOA.DeligneAudit.Toroidal

noncomputable section

def twoN2inN1 : Submodule ℂ (twoN 1) :=
  (twoN 2).comap (twoN 1).subtype

def TwoPositiveLayerBounds : Prop :=
  (FiniteDimensional ℂ ((twoN 1) ⧸ twoN2inN1) ∧
    Module.finrank ℂ ((twoN 1) ⧸ twoN2inN1) ≤ 56) ∧
  (FiniteDimensional ℂ twoN2inN1 ∧
    Module.finrank ℂ twoN2inN1 ≤ 1)

theorem presentedRankBoundE_two_of (h : TwoPositiveLayerBounds) :
    PresentedRankBoundE 2 (by norm_num) := by
  letI : FiniteDimensional ℂ ((twoN 1) ⧸ twoN2inN1) := h.1.1
  letI : FiniteDimensional ℂ twoN2inN1 := h.2.1
  letI : FiniteDimensional ℂ (twoN 1) :=
    Module.Finite.equiv (quotient_prod_linearEquiv twoN2inN1).some
  letI : FiniteDimensional ℂ twoZeroQuot := two_zero_rank_bound.1
  letI : FiniteDimensional ℂ (PTE 2) :=
    Module.Finite.equiv (quotient_prod_linearEquiv (twoN 1)).some
  have hpos : Module.finrank ℂ (twoN 1) ≤ 57 := by
    calc
      Module.finrank ℂ (twoN 1) =
          Module.finrank ℂ ((twoN 1) ⧸ twoN2inN1) +
            Module.finrank ℂ twoN2inN1 :=
        (twoN2inN1.finrank_quotient_add_finrank).symm
      _ ≤ 56 + 1 := Nat.add_le_add h.1.2 h.2.2
      _ = 57 := by norm_num
  change FiniteDimensional ℂ (PTE 2) ∧ Module.finrank ℂ (PTE 2) ≤ 29 ^ 2
  refine ⟨inferInstance, ?_⟩
  calc
    Module.finrank ℂ (PTE 2) =
        Module.finrank ℂ ((PTE 2) ⧸ twoN 1) + Module.finrank ℂ (twoN 1) :=
      ((twoN 1).finrank_quotient_add_finrank).symm
    _ ≤ 784 + 57 := Nat.add_le_add two_zero_rank_bound.2 hpos
    _ = 29 ^ 2 := by norm_num

end

end VOA.DeligneAudit.Toroidal

#print axioms VOA.DeligneAudit.Toroidal.presentedRankBoundE_two_of
