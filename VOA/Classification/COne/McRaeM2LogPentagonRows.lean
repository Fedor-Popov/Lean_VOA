import VOA.Huang.LogAssocFivePointPentagonEvaluation
import VOA.Huang.LogAssocFivePointPairPointPolynomial
import VOA.Huang.LogAssocFivePointProductConvergence
import VOA.Huang.LogAssocFivePointWeightSum
import VOA.Huang.LogAssocFivePointBlockFiber

/-! Elementary transfer lemmas for the logarithmic pentagon arrays: a natural
progression row that is a fixed multiple of an injectively reindexed absolutely
summable array is absolutely summable, and the exponential coordinate ratios of
the common pentagon chart have norm below one. -/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Huang.LogAssocFivePoint
open scoped BigOperators

/-- A progression row equal to a constant multiple of an injectively
reindexed absolutely summable array is absolutely summable. -/
theorem summable_row_of_reindex {F : ℂ → ℂ → ℂ} {G : ℕ × ℕ → ℂ} (h h' K : ℂ)
    (σ : ℕ × ℕ → ℕ × ℕ) (hσ : Function.Injective σ) (hG : Summable fun q => ‖G q‖)
    (hF : ∀ p : ℕ × ℕ, F (h+p.1) (h'+p.2)=K*G (σ p)) :
    Summable fun p : ℕ × ℕ => ‖F (h+p.1) (h'+p.2)‖ := by
  have hs := (hG.comp_injective hσ).mul_left ‖K‖
  refine hs.congr fun p => ?_
  simp only [Function.comp_apply, hF p, norm_mul]

/-- Natural powers of a complex exponential. -/
theorem exp_mul_nat (e : ℂ) (n : ℕ) : Complex.exp (e*n)=Complex.exp e^n := by
  rw [mul_comm, Complex.exp_nat_mul]

/-- The norm of the exponential of a real number. -/
theorem norm_exp_ofReal_lt_one {x : ℝ} (hx : x<0) : ‖Complex.exp (x : ℂ)‖<1 := by
  rw [Complex.norm_exp_ofReal]
  exact Real.exp_lt_one_iff.mpr hx

/-- A principal logarithm of a positive real number is real. -/
theorem log_ofReal_pos {x : ℝ} (hx : 0<x) : Complex.log (x : ℂ)=(Real.log x : ℂ) :=
  (Complex.ofReal_log hx.le).symm

/-- The norm of a ratio of exponentials of real logarithms. -/
theorem norm_exp_log_sub_log_lt_one {x y : ℝ} (hx : 0<x) (hxy : x<y) :
    ‖Complex.exp (Complex.log (x : ℂ)-Complex.log (y : ℂ))‖<1 := by
  rw [log_ofReal_pos hx, log_ofReal_pos (hx.trans hxy), ← Complex.ofReal_sub]
  apply norm_exp_ofReal_lt_one
  have := Real.log_lt_log hx hxy
  linarith

/-- The norm of the reciprocal exponential of a logarithm above zero. -/
theorem norm_exp_neg_log_lt_one {y : ℝ} (hy : 1<y) :
    ‖Complex.exp (-Complex.log (y : ℂ))‖<1 := by
  rw [log_ofReal_pos (zero_lt_one.trans hy), ← Complex.ofReal_neg]
  apply norm_exp_ofReal_lt_one
  have := Real.log_pos hy
  linarith

/-- The norm of the exponential of a logarithm. -/
theorem norm_exp_log {x : ℝ} (hx : 0<x) : ‖Complex.exp (Complex.log (x : ℂ))‖=x := by
  rw [Complex.exp_log (by exact_mod_cast hx.ne')]
  simp [abs_of_pos hx]

end VOA.Huang.LogAssocFivePoint
