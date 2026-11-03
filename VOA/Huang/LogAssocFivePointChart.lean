import VOA.Huang.AssocExpansion

/-! The literal principal logarithm coordinates for genuine real five-point
sewing. Positive rescaling remains in the proved logarithmic overlap chart. -/
namespace VOA.Huang.LogAssocFivePointChart
open VOA.Huang.AssocExpansion

/-- Exact chosen-branch logarithmic coordinates after positive rescaling. -/
theorem positive_ratio_chart {r s : ℝ} (hr : 0<r) (hs : 0<s) :
    let t : ℂ := (Real.log (r/s) : ℝ)
    t+Complex.log (s : ℂ)=Complex.log (r : ℂ) ∧
      Complex.log (1+Complex.exp t)+Complex.log (s : ℂ)=Complex.log ((s+r : ℝ) : ℂ) := by
  have hratio : 0<r/s := div_pos hr hs
  have hExp : Complex.exp ((Real.log (r/s) : ℝ) : ℂ)=((r/s : ℝ) : ℂ) := by
    rw [← Complex.ofReal_exp,Real.exp_log hratio]
  have hsumPositive : 0 < 1+r/s := by linarith
  have hsr : 0 < s+r := add_pos hs hr
  constructor
  · rw [← Complex.ofReal_log hs.le,← Complex.ofReal_log hr.le,← Complex.ofReal_add,
      ← Real.log_mul (ne_of_gt hratio) (ne_of_gt hs)]
    congr 1
    congr 1
    field_simp
  · rw [hExp]
    have hadd : (1 : ℂ)+((r/s : ℝ) : ℂ)=((1+r/s : ℝ) : ℂ) := by push_cast; rfl
    rw [hadd,← Complex.ofReal_log hsumPositive.le,
      ← Complex.ofReal_log hs.le,← Complex.ofReal_log hsr.le,
      ← Complex.ofReal_add,← Real.log_mul (ne_of_gt hsumPositive) (ne_of_gt hs)]
    congr 1
    congr 1
    field_simp

/-- The genuine logarithmic overlap condition for every positive ratio below one. -/
theorem positive_ratio_mem_overlap {r s : ℝ} (hr : 0<r) (hs : 0<s) (hrs : r<s) :
    ((Real.log (r/s) : ℝ) : ℂ)∈overlapDomain :=
  log_mem_overlapDomain (div_pos hr hs) ((div_lt_one hs).mpr hrs)

end VOA.Huang.LogAssocFivePointChart
