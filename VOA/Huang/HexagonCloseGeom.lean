import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Complex.Convex

/-! # Hexagon closure: plane geometry for the gluing argument

Elementary facts about `arg`, `log` and the regions used by the hexagon gluing
(`HexagonCloseGlue`).  The sign `s = ±1` selects the half plane `{s · Im r > 0}`; the phase is
`κ = s π i` (`s = -1` is FHL's `Ω₀`, `s = 1` its inverse).  VOA-free.
-/

noncomputable section
namespace VOA.Huang.TensorCat.HexagonClose
open Complex

/-- The phase constant `κ = s π i`. -/
def kap (s : ℝ) : ℂ := (s : ℂ) * (Real.pi * Complex.I)

theorem sign_cases {s : ℝ} (hs : s = 1 ∨ s = -1) : s * s = 1 := by
  rcases hs with rfl | rfl <;> norm_num

theorem exp_kap {s : ℝ} (hs : s = 1 ∨ s = -1) : Complex.exp (kap s) = -1 := by
  rcases hs with rfl | rfl
  · simp [kap, Complex.exp_pi_mul_I]
  · rw [kap, show ((-1 : ℝ) : ℂ) * (↑Real.pi * Complex.I) = -(↑Real.pi * Complex.I) by
      push_cast; ring, Complex.exp_neg, Complex.exp_pi_mul_I]
    norm_num

theorem kap_re (s : ℝ) : (kap s).re = 0 := by simp [kap]

theorem kap_im (s : ℝ) : (kap s).im = s * Real.pi := by simp [kap]

/-- `s · arg z ∈ (0, π)` on the half plane `s · Im z > 0`. -/
theorem sign_arg_mem {s : ℝ} (hs : s = 1 ∨ s = -1) {z : ℂ} (hz : 0 < s * z.im) :
    0 < s * Complex.arg z ∧ s * Complex.arg z < Real.pi := by
  have hlt := Complex.arg_le_pi z
  have hgt := Complex.neg_pi_lt_arg z
  rcases hs with rfl | rfl
  · have him : 0 < z.im := by linarith
    have h0 : 0 ≤ Complex.arg z := Complex.arg_nonneg_iff.2 him.le
    have hne : Complex.arg z ≠ 0 := by
      intro h; rw [Complex.arg_eq_zero_iff] at h; linarith [h.2]
    have hpi : Complex.arg z < Real.pi := Complex.arg_lt_pi_iff.2 (Or.inr him.ne')
    refine ⟨?_, by linarith⟩
    rw [one_mul]
    exact lt_of_le_of_ne h0 (Ne.symm hne)
  · have him : z.im < 0 := by linarith
    have h0 : Complex.arg z < 0 := Complex.arg_neg_iff.2 him
    constructor <;> nlinarith

/-- On the half plane with negative real part, `s · arg z ∈ (π/2, π)`. -/
theorem sign_arg_mem_of_re_neg {s : ℝ} (hs : s = 1 ∨ s = -1) {z : ℂ} (hz : 0 < s * z.im)
    (hre : z.re < 0) : Real.pi / 2 < s * Complex.arg z := by
  have h := sign_arg_mem hs hz
  have habs : Real.pi / 2 < |Complex.arg z| := by
    by_contra hle
    push Not at hle
    exact absurd (Complex.abs_arg_le_pi_div_two_iff.1 hle) (not_le.2 hre)
  rcases hs with rfl | rfl
  · rw [abs_of_pos (by linarith [h.1])] at habs; linarith
  · rw [abs_of_neg (by linarith [h.1])] at habs; linarith

/-- On the half plane with positive real part, `s · arg z ∈ (0, π/2)`. -/
theorem sign_arg_lt_of_re_pos {s : ℝ} (hs : s = 1 ∨ s = -1) {z : ℂ} (hre : 0 < z.re) :
    s * Complex.arg z < Real.pi / 2 := by
  have habs : |Complex.arg z| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl hre)
  rcases hs with rfl | rfl
  · linarith [le_abs_self (Complex.arg z)]
  · linarith [neg_abs_le (Complex.arg z)]

/-- A logarithm with `|Im| < π` of a number with positive real part has `|Im| < π/2`. -/
theorem abs_im_lt_of_exp_re_pos {ℓ : ℂ} (h1 : -Real.pi < ℓ.im) (h2 : ℓ.im < Real.pi)
    (hre : 0 < (Complex.exp ℓ).re) : |ℓ.im| < Real.pi / 2 := by
  rw [Complex.exp_re] at hre
  have hcos : 0 < Real.cos ℓ.im := by
    by_contra h
    push Not at h
    have := mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos ℓ.re).le h
    linarith
  rw [abs_lt]
  constructor
  · by_contra h
    push Not at h
    have := Real.cos_nonpos_of_pi_div_two_le_of_le (x := -ℓ.im) (by linarith) (by linarith)
    rw [Real.cos_neg] at this
    linarith
  · by_contra h
    push Not at h
    have := Real.cos_nonpos_of_pi_div_two_le_of_le (x := ℓ.im) h (by linarith)
    linarith

/-- `log(-w) = log w + κ` on the half plane `s · Im w < 0`. -/
theorem log_neg_eq {s : ℝ} (hs : s = 1 ∨ s = -1) {w : ℂ} (hw : s * w.im < 0) :
    Complex.log (-w) = Complex.log w + kap s := by
  rcases hs with rfl | rfl
  · have him : w.im < 0 := by linarith
    rw [Complex.log, Complex.log, norm_neg, Complex.arg_neg_eq_arg_add_pi_of_im_neg him, kap]
    push_cast; ring
  · have him : 0 < w.im := by linarith
    rw [Complex.log, Complex.log, norm_neg, Complex.arg_neg_eq_arg_sub_pi_of_im_pos him, kap]
    push_cast; ring

/-! ## The two continued coordinates -/

/-- The continued `K`-coordinate `ℓ_K(r) = κ - log(1+r)`. -/
def ellK (s : ℝ) (r : ℂ) : ℂ := kap s - Complex.log (1 + r)

/-- The continued `M`-coordinate `ℓ_M(r) = log r - log(1+r) - κ`. -/
def ellM (s : ℝ) (r : ℂ) : ℂ := Complex.log r - Complex.log (1 + r) - kap s

theorem exp_ellK {s : ℝ} (hs : s = 1 ∨ s = -1) {r : ℂ} (h1 : 1 + r ≠ 0) :
    Complex.exp (ellK s r) = -1 / (1 + r) := by
  rw [ellK, Complex.exp_sub, exp_kap hs, Complex.exp_log h1]

theorem exp_ellM {s : ℝ} (hs : s = 1 ∨ s = -1) {r : ℂ} (h0 : r ≠ 0) (h1 : 1 + r ≠ 0) :
    Complex.exp (ellM s r) = -(r / (1 + r)) := by
  rw [ellM, Complex.exp_sub, Complex.exp_sub, exp_kap hs, Complex.exp_log h0,
    Complex.exp_log h1]
  field_simp

theorem one_add_exp_ellK {s : ℝ} (hs : s = 1 ∨ s = -1) {r : ℂ} (h1 : 1 + r ≠ 0) :
    1 + Complex.exp (ellK s r) = r / (1 + r) := by
  rw [exp_ellK hs h1]
  field_simp
  ring

theorem one_add_exp_ellM {s : ℝ} (hs : s = 1 ∨ s = -1) {r : ℂ} (h0 : r ≠ 0) (h1 : 1 + r ≠ 0) :
    1 + Complex.exp (ellM s r) = 1 / (1 + r) := by
  rw [exp_ellM hs h0 h1]
  field_simp
  ring

theorem ellK_re (s : ℝ) (r : ℂ) : (ellK s r).re = -Real.log ‖1 + r‖ := by
  simp [ellK, kap, Complex.log_re]

theorem ellK_im (s : ℝ) (r : ℂ) : (ellK s r).im = s * Real.pi - Complex.arg (1 + r) := by
  simp [ellK, kap, Complex.log_im]

theorem ellM_re (s : ℝ) (r : ℂ) : (ellM s r).re = Real.log ‖r‖ - Real.log ‖1 + r‖ := by
  simp [ellM, kap, Complex.log_re]

theorem ellM_im (s : ℝ) (r : ℂ) :
    (ellM s r).im = Complex.arg r - Complex.arg (1 + r) - s * Real.pi := by
  simp [ellM, kap, Complex.log_im]

/-! ## Quotient computations -/

theorem re_div_one_add (r : ℂ) :
    (r / (1 + r)).re = (r.re + Complex.normSq r) / Complex.normSq (1 + r) := by
  rw [Complex.div_re]
  simp only [Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im, zero_add,
    Complex.normSq_apply]
  ring

theorem im_div_one_add (r : ℂ) : (r / (1 + r)).im = r.im / Complex.normSq (1 + r) := by
  rw [Complex.div_im]
  simp only [Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im, zero_add]
  ring

theorem im_one_div (u : ℂ) : (1 / u).im = -u.im / Complex.normSq u := by
  rw [one_div, Complex.inv_im]

theorem re_one_div (u : ℂ) : (1 / u).re = u.re / Complex.normSq u := by
  rw [one_div, Complex.inv_re]

end VOA.Huang.TensorCat.HexagonClose
