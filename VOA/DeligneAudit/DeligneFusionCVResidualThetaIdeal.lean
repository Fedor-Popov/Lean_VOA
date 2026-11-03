import VOA.DeligneAudit.DeligneFusionCVResidualThetaRelations
import VOA.DeligneAudit.DeligneFusionCVRectFilteredRegion
import VOA.DeligneAudit.DeligneFusionCVRectAdjointFamily

/-!
# The actual residual theta source and adjoint polynomial coefficient ideal

The adjoint reversal has one fewer theta variable than the weaker pair of
fundamental sites. Its low coefficient j corresponds to weak index j+q.
The comparison is derived arithmetically and used only with proved actual
source relations in the PBW quotient.
-/

namespace VOA.DeligneAudit.A2.CVResidualThetaRelations

open VOA.AffineSl3 VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.A2.CVFamily VOA.DeligneAudit.A2.CVRectCommutative
open VOA.DeligneAudit.A2.CVRectFiltered VOA.DeligneAudit.A2.CVRectIntegrationOrder
open VOA.DeligneAudit.A2.CVRectStarIdeal VOA.DeligneAudit.A2.CVRectAdjointOrder
open VOA.DeligneAudit.A2.CVRectStarBase VOA.DeligneAudit.A2.CVRectAdjointFamily

/-- The adjoint site together with the actual level-three rectangle sites. -/
def residualOrder (ϱ : Weight) : ℕ → ℕ → ℕ → ℕ :=
  adjointOrder (List.replicate ϱ.1 3) (List.replicate ϱ.2 3) []

/-- No coefficient relation is demanded in total multiplicity at most one. -/
theorem residualOrder_low (ϱ : Weight) (p q r : ℕ) (hd : p + q + r ≤ 1) :
    residualOrder ϱ p q r = 0 := by
  simp only [residualOrder, adjointOrder, background, excess, List.map_replicate,
    List.sum_replicate, List.map_nil, List.sum_nil, nsmul_eq_mul, Nat.add_zero, adjOrder]
  have hL : p + q - 3 = 0 := by omega
  have hR : q + r - 3 = 0 := by omega
  rw [hL, hR]
  simp only [Nat.mul_zero, Nat.zero_add]
  omega

/-- In total multiplicity at least two, the two fundamental-site order is
exactly the adjoint-site order plus the number of theta factors. -/
theorem weakOrder_eq (ϱ : Weight) (p q r : ℕ) (hd : 2 ≤ p + q + r) :
    starOrder (parts ϱ.1 0 1) (parts ϱ.2 0 1) [] p q r =
      residualOrder ϱ p q r + q := by
  have ha : (p + q - 1) + (q + r - 1) = adjOrder p q r + q := by
    unfold adjOrder
    omega
  simp only [starOrder, residualOrder, adjointOrder, background, excess,
    parts, List.map_append, List.map_replicate, List.sum_append, List.sum_replicate,
    List.map_nil, List.sum_nil, nsmul_eq_mul, Nat.add_zero]
  omega

/-- The theta reversal degrees differ by precisely q. -/
theorem weakReverseDegree_eq (ϱ : Weight) (p q r : ℕ) :
    reverseDegree (parts ϱ.1 0 1).length
      ((parts ϱ.1 0 1).length + (parts ϱ.2 0 1).length + ([] : List ℕ).length)
      (parts ϱ.2 0 1).length p q r =
      reverseDegree (ϱ.1 + 1) (ϱ.1 + ϱ.2 + 1) (ϱ.2 + 1) p q r + q := by
  have hNy : (parts ϱ.1 0 1).length + (parts ϱ.2 0 1).length +
      ([] : List ℕ).length - 1 = ϱ.1 + ϱ.2 + 1 := by
    simp only [parts_length, List.length_nil]
    omega
  unfold reverseDegree
  rw [hNy]
  simp only [parts_length, Nat.add_zero, Nat.add_sub_cancel_right]
  ring

/-- Every low reversed adjoint coefficient is in the checked weak source
clipped region, with the same actual forward current degree. -/
theorem residual_reverse_region (ϱ : Weight) (p q r j : ℕ)
    (hj : j < residualOrder ϱ p q r)
    (hD : j ≤ reverseDegree (ϱ.1 + 1) (ϱ.1 + ϱ.2 + 1) (ϱ.2 + 1) p q r) :
    clippedSum (parts ϱ.1 0 1) (p + q) + clippedSum (parts ϱ.2 0 1) (q + r) <
      (reverseDegree (ϱ.1 + 1) (ϱ.1 + ϱ.2 + 1) (ϱ.2 + 1) p q r - j) +
        (p + q + r) := by
  have hd : 2 ≤ p + q + r := by
    by_contra hn
    rw [residualOrder_low ϱ p q r (by omega)] at hj
    omega
  have hμ := weakOrder_eq ϱ p q r hd
  have hdeg := weakReverseDegree_eq ϱ p q r
  have hreg := star_reverse_region (parts ϱ.1 0 1) (parts ϱ.2 0 1) []
    p q r (j + q) (by simp only [parts_length]; omega)
    (by simp only [parts_length, List.length_nil]; omega)
    (by simp only [parts_length]; omega) (by omega) (by omega)
  rw [hdeg, Nat.add_sub_add_right] at hreg
  simpa only [clippedSum, List.map_nil, List.sum_nil, Nat.add_zero] using hreg

end VOA.DeligneAudit.A2.CVResidualThetaRelations

#print axioms VOA.DeligneAudit.A2.CVResidualThetaRelations.residual_reverse_region
