import VOA.DeligneAudit.DeligneFusionCVRectAdjointFiveRecursion
import VOA.DeligneAudit.DeligneFusionCVRectAdjointBase
import VOA.DeligneAudit.DeligneFusionCVRectStarBound

/-! # The actual three- and two-dimensional branches of the five-shape tail -/

namespace VOA.DeligneAudit.A2.CVRectAdjointFiveBase

open VOA.DeligneAudit.A2.CVRectIntegrationOrder
open VOA.DeligneAudit.A2.CVRectStarIdeal
open VOA.DeligneAudit.A2.CVRectStarCount
open VOA.DeligneAudit.A2.CVRectAdjointFamily
open VOA.DeligneAudit.A2.CVRectAdjointFiveOrder
open VOA.DeligneAudit.A2.CVRectAdjointFiveFamily

noncomputable section

theorem three_tail_order (active center : List ℕ) :
    threeTailOrder active center =
      fun p q r => p + starOrder active [] (1 :: center) p q r := by
  funext p q r
  simp only [threeTailOrder, tailBackground, starOrder, excess, List.map_cons,
    List.sum_cons, List.map_nil, List.sum_nil]
  omega

theorem two_tail_order (active center : List ℕ) :
    twoTailOrder active center = starOrder active [] (2 :: center) := by
  funext p q r
  simp only [twoTailOrder, tailBackground, starOrder, excess, List.map_cons,
    List.sum_cons, List.map_nil, List.sum_nil]
  omega

theorem three_tail_bound (active center : List ℕ) :
    FiniteDimensional ℂ (ThreeTailFamily active center) ∧
      Module.finrank ℂ (ThreeTailFamily active center) ≤ 2 * starWeight active [] center := by
  let N := active.length + center.length + 1
  let μ := starOrder active [] (1 :: center)
  have hb := CVRectStarBound.family_bound active [] (1 :: center)
  haveI : FiniteDimensional ℂ (Model active.length N 0 μ) := by
    have hf := hb.1
    unfold CVRectStarFamily.Family at hf
    simpa only [List.length_nil, List.length_cons, N, Nat.add_zero,
      Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hf
  have hr := CVRectAdjointBase.phantom_model_bound active.length N 0 μ
  have hweight : starWeight active [] (1 :: center) = 2 * starWeight active [] center := by
    simp only [starWeight, List.map_cons, List.prod_cons]
    ring
  have hsource : Module.finrank ℂ (Model active.length N 0 μ) ≤
      2 * starWeight active [] center := by
    have hh := hb.2.trans_eq hweight
    unfold CVRectStarFamily.Family at hh
    simpa only [List.length_nil, List.length_cons, N, Nat.add_zero,
      Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hh
  unfold ThreeTailFamily
  rw [three_tail_order]
  exact ⟨hr.1, hr.2.trans hsource⟩

theorem two_tail_bound (active center : List ℕ) :
    FiniteDimensional ℂ (TwoTailFamily active center) ∧
      Module.finrank ℂ (TwoTailFamily active center) ≤ 3 * starWeight active [] center := by
  have hb := CVRectStarBound.family_bound active [] (2 :: center)
  have hweight : starWeight active [] (2 :: center) = 3 * starWeight active [] center := by
    simp only [starWeight, List.map_cons, List.prod_cons]
    ring
  unfold TwoTailFamily
  rw [two_tail_order]
  refine ⟨?_, ?_⟩
  · have hf := hb.1
    unfold CVRectStarFamily.Family at hf
    simpa only [List.length_nil, List.length_cons, Nat.add_zero, Nat.add_assoc,
      Nat.add_left_comm, Nat.add_comm] using hf
  · have hh := hb.2.trans_eq hweight
    unfold CVRectStarFamily.Family at hh
    simpa only [List.length_nil, List.length_cons, Nat.add_zero, Nat.add_assoc,
      Nat.add_left_comm, Nat.add_comm] using hh

theorem five_tail_small_bound (active center : List ℕ)
    (hactive : ∀ k ∈ active, k ≤ 1) :
    FiniteDimensional ℂ (FiveTailFamily active center) ∧
      Module.finrank ℂ (FiveTailFamily active center) ≤ 5 * starWeight active [] center := by
  have hthree := three_tail_bound active center
  have htwo := two_tail_bound active center
  haveI := hthree.1
  haveI := htwo.1
  have hs := CVRectAdjointFiveRecursion.special_tail_dimension_step active center hactive
  refine ⟨hs.1, hs.2.trans ?_⟩
  omega

end
end VOA.DeligneAudit.A2.CVRectAdjointFiveBase

#print axioms VOA.DeligneAudit.A2.CVRectAdjointFiveBase.three_tail_bound
#print axioms VOA.DeligneAudit.A2.CVRectAdjointFiveBase.two_tail_bound
#print axioms VOA.DeligneAudit.A2.CVRectAdjointFiveBase.five_tail_small_bound
