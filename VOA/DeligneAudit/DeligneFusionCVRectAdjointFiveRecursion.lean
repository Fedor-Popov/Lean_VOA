import VOA.DeligneAudit.DeligneFusionCVRectAdjointFiveFamily
import VOA.DeligneAudit.DeligneFusionCVRectAdjointFiveMaps
import VOA.DeligneAudit.DeligneFusionCVRectAdjointModelDimension

/-! # Actual canonical quotient recursions for the five-monomial tail -/

namespace VOA.DeligneAudit.A2.CVRectAdjointFiveRecursion

open VOA.DeligneAudit.A2.CVRectStarBase
open VOA.DeligneAudit.A2.CVRectAdjointFamily
open VOA.DeligneAudit.A2.CVRectAdjointFiveOrder
open VOA.DeligneAudit.A2.CVRectAdjointFiveFamily

noncomputable section

theorem special_tail_dimension_step (active center : List ℕ)
    (hactive : ∀ k ∈ active, k ≤ 1)
    [FiniteDimensional ℂ (ThreeTailFamily active center)]
    [FiniteDimensional ℂ (TwoTailFamily active center)] :
    FiniteDimensional ℂ (FiveTailFamily active center) ∧
      Module.finrank ℂ (FiveTailFamily active center) ≤
        Module.finrank ℂ (ThreeTailFamily active center) +
        Module.finrank ℂ (TwoTailFamily active center) := by
  let N := active.length + center.length + 1
  exact CVRectAdjointModelDimension.model_dimension_step active.length N 0
    (fiveTailOrder active center) (threeTailOrder active center) (twoTailOrder active center)
    (CVRectAdjointFiveMaps.five_special_shift _ _ _ active center)
    (CVRectAdjointFiveMaps.five_special_primitive _ _ _ active center hactive)

theorem ordinary_tail_dimension_step (active center : List ℕ) (K : ℕ)
    (hK : 2 ≤ K) (hmax : ∀ k ∈ active, k ≤ K)
    [FiniteDimensional ℂ (FiveTailFamily active (K :: center))]
    [FiniteDimensional ℂ (FiveTailFamily ((K - 1) :: active) center)] :
    FiniteDimensional ℂ (FiveTailFamily (K :: active) center) ∧
      Module.finrank ℂ (FiveTailFamily (K :: active) center) ≤
        Module.finrank ℂ (FiveTailFamily ((K - 1) :: active) center) +
        Module.finrank ℂ (FiveTailFamily active (K :: center)) := by
  let N := active.length + center.length + 2
  have hN : active.length + 1 + center.length + 1 = N := by dsimp [N]; omega
  have hN' : active.length + (center.length + 1) + 1 = N := by dsimp [N]; omega
  haveI : FiniteDimensional ℂ (Model (active.length + 1) N 0
      (fiveTailOrder active (K :: center))) := by
    have hf := (inferInstance : FiniteDimensional ℂ (FiveTailFamily active (K :: center)))
    unfold FiveTailFamily at hf
    rw [List.length_cons, hN'] at hf
    exact hf
  haveI : FiniteDimensional ℂ (Model (active.length + 1 + 1) N 0
      (fiveTailOrder ((K - 1) :: active) center)) := by
    have hf := (inferInstance :
      FiniteDimensional ℂ (FiveTailFamily ((K - 1) :: active) center))
    unfold FiveTailFamily at hf
    rw [List.length_cons, hN] at hf
    exact hf
  have hb := CVRectAdjointModelDimension.model_dimension_step (active.length + 1) N 0
    (fiveTailOrder (K :: active) center) (fiveTailOrder ((K - 1) :: active) center)
    (fiveTailOrder active (K :: center))
    (CVRectAdjointFiveMaps.five_ordinary_shift _ _ _ active center K)
    (CVRectAdjointFiveMaps.five_ordinary_primitive _ _ _ active center K hK hmax)
  let P : ℕ → ℕ → Prop := fun n n' =>
    FiniteDimensional ℂ (Model (active.length + 1 + 1) n 0 (fiveTailOrder (K :: active) center)) ∧
      Module.finrank ℂ (Model (active.length + 1 + 1) n 0 (fiveTailOrder (K :: active) center)) ≤
        Module.finrank ℂ (Model (active.length + 1 + 1) n 0
          (fiveTailOrder ((K - 1) :: active) center)) +
        Module.finrank ℂ (Model (active.length + 1) n' 0 (fiveTailOrder active (K :: center)))
  have he : P (active.length + 1 + center.length + 1)
      (active.length + (center.length + 1) + 1) = P N N := congrArg₂ P hN hN'
  exact he.mpr hb

end
end VOA.DeligneAudit.A2.CVRectAdjointFiveRecursion

#print axioms VOA.DeligneAudit.A2.CVRectAdjointFiveRecursion.special_tail_dimension_step
#print axioms VOA.DeligneAudit.A2.CVRectAdjointFiveRecursion.ordinary_tail_dimension_step
