import VOA.Huang.GenusOneODE

/-! # The Eisenstein evaluation algebra homomorphism

Absolute convergence makes evaluation multiplicative on the upper half-plane.
This permits one module of simultaneous values of all insertion blocks, with
formal Eisenstein coefficients acting through their actual analytic values.
-/
namespace VOA.Huang.GenusOne
open VOA Complex
open scoped BigOperators

@[simp] theorem eisensteinEval_add (f g : ↥GSeries) {z : ℂ} (hz : z ∈ imGT 0) :
    eisensteinEval (f + g) z = eisensteinEval f z + eisensteinEval g z := by
  unfold eisensteinEval
  rw [← (summable_norm_eisenstein f hz).of_norm.tsum_add
    (summable_norm_eisenstein g hz).of_norm]
  apply tsum_congr
  intro n
  simp [add_mul]

@[simp] theorem eisensteinEval_smul (c : ℂ) (f : ↥GSeries) (z : ℂ) :
    eisensteinEval (c • f) z = c * eisensteinEval f z := by
  unfold eisensteinEval
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  simp [mul_assoc]

@[simp] theorem eisensteinEval_one (z : ℂ) : eisensteinEval 1 z = 1 := by
  unfold eisensteinEval
  rw [tsum_eq_single 0]
  · simp
  · intro n hn
    simp [PowerSeries.coeff_one, hn]

theorem eisensteinEval_mul (f g : ↥GSeries) {z : ℂ} (hz : z ∈ imGT 0) :
    eisensteinEval (f * g) z = eisensteinEval f z * eisensteinEval g z := by
  unfold eisensteinEval
  rw [tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm
    (summable_norm_eisenstein f hz) (summable_norm_eisenstein g hz)]
  refine tsum_congr fun n => ?_
  rw [show ((f * g : ↥GSeries) : PowerSeries ℂ) = (f : PowerSeries ℂ) * g from rfl,
    coeff_mul_range, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmn : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
  have he : exp (2 * (Real.pi : ℂ) * I * (n : ℂ) * z) =
      exp (2 * (Real.pi : ℂ) * I * (m : ℂ) * z) *
        exp (2 * (Real.pi : ℂ) * I * ((n - m : ℕ) : ℂ) * z) := by
    rw [← Complex.exp_add, Nat.cast_sub hmn]
    congr 1
    ring
  rw [he]
  ring

/-- Evaluation as an algebra homomorphism, restricted to its convergence domain. -/
noncomputable def eisensteinEvalHom : ↥GSeries →ₐ[ℂ] (UpperHalfPlane → ℂ) where
  toFun f τ := eisensteinEval f τ
  map_zero' := by ext τ; simp [eisensteinEval]
  map_one' := by ext τ; exact eisensteinEval_one τ
  map_add' f g := by ext τ; exact eisensteinEval_add f g τ.im_pos
  map_mul' f g := by ext τ; exact eisensteinEval_mul f g τ.im_pos
  commutes' c := by
    ext τ
    change eisensteinEval (algebraMap ℂ ↥GSeries c) τ = c
    rw [Algebra.algebraMap_eq_smul_one, eisensteinEval_smul, eisensteinEval_one, mul_one]

@[simp] theorem eisensteinEvalHom_apply (f : ↥GSeries) (τ : UpperHalfPlane) :
    eisensteinEvalHom f τ = eisensteinEval f τ := rfl

/-- The named generator evaluates to the Eisenstein coefficient of block recursion. -/
theorem eisensteinEval_zhuG (m : ℕ) (hm : 1 ≤ m) (z : ℂ) :
    eisensteinEval ⟨PowerSeries.mk (zhuG m), mk_zhuG_mem_GSeries hm⟩ z = zhuGC m z := by
  simp only [eisensteinEval, PowerSeries.coeff_mk]
  rfl

end VOA.Huang.GenusOne
