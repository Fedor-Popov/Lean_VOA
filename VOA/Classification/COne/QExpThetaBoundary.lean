import VOA.Classification.COne.QExpThetaLambert

/-! # The zeroth Lambert term and the boundary constant -/

open Complex
open scoped UpperHalfPlane

noncomputable section
namespace VOA.Classification.COne.SSHecke

/-- The zeroth Lambert term must be separated when the parameter has norm one. -/
theorem thetaLambert_shift {r : ℂ} (hr : ‖r‖ < 1) (u : ℂ) :
    thetaLambert r u = u / (1 - u) + thetaLambert r (u * r) := by
  have h := (thetaLambert_summable hr u).tsum_eq_zero_add
  change thetaLambert r u = _ at h
  simpa only [pow_zero, mul_one, pow_succ, thetaLambert,
    mul_assoc, mul_comm, mul_left_comm] using h

/-- Correct boundary constant, with the positive-index tail kept explicit. -/
theorem thetaLambert_boundary {r u : ℂ} (hr : ‖r‖ < 1) (hu : u ≠ 1) :
    1 / 2 + thetaLambert r u =
      (1 + u) / (2 * (1 - u)) + thetaLambert r (u * r) := by
  rw [thetaLambert_shift hr]
  have hn : 1 - u ≠ 0 := sub_ne_zero.mpr (Ne.symm hu)
  field_simp
  ring

/-- Each Lambert summand admits its geometric expansion in the open unit disk. -/
theorem thetaLambert_summand_geometric {v : ℂ} (hv : ‖v‖ < 1) :
    v / (1 - v) = ∑' k : ℕ, v ^ (k + 1) := by
  simp_rw [pow_succ, tsum_mul_right, tsum_geometric_of_norm_lt_one hv]
  ring

/-- On the open disk, both indices of the Lambert expansion are explicit.
This does not yet regroup the two indices into divisor sums. -/
theorem thetaLambert_eq_double_tsum {r u : ℂ} (hr : ‖r‖ < 1) (hu : ‖u‖ < 1) :
    thetaLambert r u = ∑' n : ℕ, ∑' k : ℕ, (u * r ^ n) ^ (k + 1) := by
  apply tsum_congr
  intro n
  apply thetaLambert_summand_geometric
  rw [norm_mul, norm_pow]
  calc
    ‖u‖ * ‖r‖ ^ n ≤ ‖u‖ * 1 :=
      mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg r) hr.le) (norm_nonneg u)
    _ < 1 := by simpa using hu

/-- The standard primitive-root parameter at the boundary. -/
theorem thetaExp_div_nat (N b : ℕ) :
    thetaExp ((b : ℂ) / N) = weightOneStandardRoot N ^ b := by
  rw [weightOneStandardRoot, ← Complex.exp_nat_mul, thetaExp]
  congr 1
  ring

/-- The normalized existing constant coefficient agrees with the boundary value. -/
theorem weightOne_boundary_constant {N : ℕ} (hN : 0 < N) (a b : Fin N)
    (ha : a.val = 0) (hb : b.val ≠ 0) :
    weightOneIntegralCoeff N (weightOneStandardRoot N) a b 0 /
      weightOneScale N (weightOneStandardRoot N) a b =
        (1 + thetaExp ((b.val : ℂ) / N)) / (2 * (1 - thetaExp ((b.val : ℂ) / N))) := by
  have hn : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  rw [thetaExp_div_nat]
  simp [weightOneIntegralCoeff, weightOneScale, ha, hb]
  field_simp

end VOA.Classification.COne.SSHecke
