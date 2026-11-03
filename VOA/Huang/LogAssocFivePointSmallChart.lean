import VOA.Huang.LogAssocFivePointEvaluation

/-! A genuine nonempty common real sewing subchart is sufficient for the
pentagon. It provides the stricter middle-tree separation while retaining
an interval in both real coordinates for coefficient faithfulness. -/
namespace VOA.Huang.LogAssocFivePoint

/-- The common open real sewing subchart used by actual joint convergence. -/
def FivePointSmallDomain (r s : ℝ) : Prop := 0<r ∧ r<s ∧ s<1/3

/-- The small convergence chart lies in the actual five-point sewing domain. -/
theorem smallDomain_full {r s : ℝ} (h : FivePointSmallDomain r s) :
    FivePointDomain r s := by
  refine ⟨h.1,h.2.1,?_⟩
  linarith [h.2.1,h.2.2]

/-- The stricter middle-tree geometric separation holds throughout this chart. -/
theorem smallDomain_mid {r s : ℝ} (h : FivePointSmallDomain r s) : 2*s+r<1 := by
  linarith [h.2.1,h.2.2]

/-- Each fixed positive small second coordinate leaves a genuine first-coordinate interval. -/
theorem smallDomain_of_fixed {r s : ℝ} (hs : 0<s) (hs' : s<1/3) (hr : 0<r) (hrs : r<s) :
    FivePointSmallDomain r s := ⟨hr,hrs,hs'⟩

/-- The small sewing region is genuinely nonempty. -/
theorem smallDomain_nonempty : ∃ r s : ℝ,FivePointSmallDomain r s := by
  refine ⟨1/16,1/8,?_⟩
  norm_num [FivePointSmallDomain]

end VOA.Huang.LogAssocFivePoint
