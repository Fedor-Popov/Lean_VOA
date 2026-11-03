import VOA.DeligneAudit.DeligneFusionCVRectAdjointFiveLeftIdeal
import VOA.DeligneAudit.DeligneFusionCVRectAdjointModelDimension
import VOA.DeligneAudit.DeligneFusionCVRectAdjointEliminate

/-!
# Actual finite-dimensional ordinary left-leaf recursion for FiveFamily

The source quotient is bounded using the constructed constant-branch shift
and actual primitive branch. Only the smaller modules' finiteness is used;
no dimension inequality, recurrence, or coefficient-ideal premise is assumed.
-/

namespace VOA.DeligneAudit.A2.CVRectAdjointFiveLeft

open VOA.DeligneAudit.A2.CVRectAdjointOrder
open VOA.DeligneAudit.A2.CVRectAdjointFamily
open VOA.DeligneAudit.A2.CVRectStarBase

noncomputable section

theorem left_dimension_step (left right center : List ℕ) (K : ℕ)
    (hK : 1 ≤ K) (hmax : ∀ k ∈ left, k ≤ K)
    [FiniteDimensional ℂ (FiveFamily left right (K :: center))]
    [FiniteDimensional ℂ (FiveFamily ((K - 1) :: left) right center)] :
    FiniteDimensional ℂ (FiveFamily (K :: left) right center) ∧
      Module.finrank ℂ (FiveFamily (K :: left) right center) ≤
        Module.finrank ℂ (FiveFamily ((K - 1) :: left) right center) +
        Module.finrank ℂ (FiveFamily left right (K :: center)) := by
  let N := left.length + right.length + center.length + 2
  let R := right.length + 1
  have hN : left.length + 1 + right.length + center.length + 1 = N := by dsimp [N]; omega
  have hN' : left.length + right.length + (center.length + 1) + 1 = N := by
    dsimp [N]
    omega
  haveI : FiniteDimensional ℂ (Model left.length N R
      (fiveSiteOrder left right (K :: center))) := by
    have hf := (inferInstance : FiniteDimensional ℂ (FiveFamily left right (K :: center)))
    unfold FiveFamily at hf
    rw [List.length_cons, hN'] at hf
    exact hf
  haveI : FiniteDimensional ℂ (Model (left.length + 1) N R
      (fiveSiteOrder ((K - 1) :: left) right center)) := by
    have hf := (inferInstance :
      FiniteDimensional ℂ (FiveFamily ((K - 1) :: left) right center))
    unfold FiveFamily at hf
    rw [List.length_cons, hN] at hf
    exact hf
  have hb := CVRectAdjointModelDimension.model_dimension_step left.length N R
    (fiveSiteOrder (K :: left) right center) (fiveSiteOrder ((K - 1) :: left) right center)
    (fiveSiteOrder left right (K :: center))
    (left_shift _ _ _ left right center K)
    (chosen_left_primitive _ _ _ left right center K hK hmax)
  let P : ℕ → ℕ → Prop := fun n n' =>
    FiniteDimensional ℂ (Model (left.length + 1) n R (fiveSiteOrder (K :: left) right center)) ∧
      Module.finrank ℂ (Model (left.length + 1) n R (fiveSiteOrder (K :: left) right center)) ≤
        Module.finrank ℂ (Model (left.length + 1) n R
          (fiveSiteOrder ((K - 1) :: left) right center)) +
        Module.finrank ℂ (Model left.length n' R (fiveSiteOrder left right (K :: center)))
  have he : P (left.length + 1 + right.length + center.length + 1)
      (left.length + right.length + (center.length + 1) + 1) = P N N := congrArg₂ P hN hN'
  exact he.mpr hb

/-- A zero-capacity ordinary left site is removed by the actual zero-xy
quotient map, with no source dimension premise. -/
theorem left_zero_bound (left right center : List ℕ)
    [FiniteDimensional ℂ (FiveFamily left right center)] :
    FiniteDimensional ℂ (FiveFamily (0 :: left) right center) ∧
      Module.finrank ℂ (FiveFamily (0 :: left) right center) ≤
        Module.finrank ℂ (FiveFamily left right center) := by
  let N := left.length + right.length + center.length + 1
  let R := right.length + 1
  have hN : left.length + 1 + right.length + center.length + 1 = N + 1 := by
    dsimp [N]
    omega
  have hb := CVRectAdjointEliminate.zeroXY_model_bound left.length N R
    (fiveSiteOrder left right center)
  let P : ℕ → (ℕ → ℕ → ℕ → ℕ) → Prop := fun n μ =>
    FiniteDimensional ℂ (Model (left.length + 1) n R μ) ∧
      Module.finrank ℂ (Model (left.length + 1) n R μ) ≤
        Module.finrank ℂ (Model left.length N R (fiveSiteOrder left right center))
  have he : P (left.length + 1 + right.length + center.length + 1)
      (fiveSiteOrder (0 :: left) right center) =
        P (N + 1) (fun p q r => fiveSiteOrder left right center p q r + p + q) :=
    congrArg₂ P hN (left_zero_order left right center)
  exact he.mpr hb

theorem finiteDimensional_left_perm {left left' : List ℕ} (hp : left.Perm left')
    (right center : List ℕ) [FiniteDimensional ℂ (FiveFamily left right center)] :
    FiniteDimensional ℂ (FiveFamily left' right center) := by
  have hf := (inferInstance : FiniteDimensional ℂ (FiveFamily left right center))
  unfold FiveFamily at hf ⊢
  rw [hp.length_eq, left_perm_order hp] at hf
  exact hf

theorem finrank_left_perm {left left' : List ℕ} (hp : left.Perm left')
    (right center : List ℕ) :
    Module.finrank ℂ (FiveFamily left right center) =
      Module.finrank ℂ (FiveFamily left' right center) := by
  unfold FiveFamily
  rw [hp.length_eq, left_perm_order hp]

end

end VOA.DeligneAudit.A2.CVRectAdjointFiveLeft

#print axioms VOA.DeligneAudit.A2.CVRectAdjointFiveLeft.left_dimension_step
#print axioms VOA.DeligneAudit.A2.CVRectAdjointFiveLeft.left_zero_bound
