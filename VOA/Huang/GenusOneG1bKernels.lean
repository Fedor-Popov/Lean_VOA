import VOA.Huang.GenusOneG1bContraction

/-!
# Transported kernels: from `t`-rational rows to Laurent kernels in `x`

Under `t = 1/(1+x)` a row `P(t)/(1−t)^E` becomes `(1+x)^E P(1/(1+x)) / x^E`. For a polynomial
`P` of degree `≤ m`, `transPoly P m = Σ_i P_i (X+1)^{m−i}` is the polynomial
`(1+x)^m P(1/(1+x))` (`eval_transPoly`). The transported kernel with a negative power of
`1 + x` is `transKer P m N = transPoly P m · (1+X)^{−N}` as a formal power series; clearing
`(1+X)^L` recovers `transPoly P (m + L − N)` (`one_add_X_pow_mul_transKer`). Its weighted
`ℓ¹` norm is `≤ (Σ‖P_i‖)(1+r)^m (1−r)^{−N}` (`normLe_transKer`).
-/
noncomputable section
namespace VOA.Huang.GenusOneG1b
open scoped BigOperators
open VOA.Huang.GenusOneWard (pc coeff_pc omt)

/-- `(1+x)^m P(1/(1+x))` as a polynomial in `x` (requires `deg P ≤ m`). -/
def transPoly (P : Polynomial ℂ) (m : ℕ) : Polynomial ℂ :=
  ∑ i ∈ Finset.range (P.natDegree + 1), Polynomial.C (P.coeff i) * (Polynomial.X + 1) ^ (m - i)

theorem eval_transPoly (P : Polynomial ℂ) {m : ℕ} (hm : P.natDegree ≤ m) {x : ℂ}
    (hx : 1 + x ≠ 0) :
    (transPoly P m).eval x = P.eval (1 + x)⁻¹ * (1 + x) ^ m := by
  rw [transPoly, Polynomial.eval_finset_sum, Polynomial.eval_eq_sum_range, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_one]
  have hm' : (1 + x) ^ m = (1 + x) ^ (m - i) * (1 + x) ^ i := by
    rw [← pow_add]; congr 1; omega
  rw [hm', inv_pow, add_comm x 1]
  field_simp

theorem X_add_one_pow_mul_transPoly (P : Polynomial ℂ) {m : ℕ} (hm : P.natDegree ≤ m) (e : ℕ) :
    (Polynomial.X + 1) ^ e * transPoly P m = transPoly P (m + e) := by
  rw [transPoly, transPoly, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [mul_left_comm, ← pow_add]
  congr 2
  omega

theorem pc_X_add_one : pc (Polynomial.X + 1) = 1 + PowerSeries.X := by
  simp [pc, add_comm]

/-- The transported kernel `(1+x)^{m−N} P(1/(1+x))` as a power series. -/
def transKer (P : Polynomial ℂ) (m N : ℕ) : PowerSeries ℂ :=
  pc (transPoly P m) * invOnePlusX ^ N

theorem one_add_X_pow_mul_transKer (P : Polynomial ℂ) {m N L : ℕ} (hm : P.natDegree ≤ m)
    (hNL : N ≤ L) :
    (1 + PowerSeries.X) ^ L * transKer P m N = pc (transPoly P (m + (L - N))) := by
  rw [transKer, ← X_add_one_pow_mul_transPoly P hm, map_mul, map_pow, pc_X_add_one]
  have hL : (1 + PowerSeries.X : PowerSeries ℂ) ^ L =
      (1 + PowerSeries.X) ^ (L - N) * (1 + PowerSeries.X) ^ N := by
    rw [← pow_add]; congr 1; omega
  rw [hL]
  have hinv : (1 + PowerSeries.X : PowerSeries ℂ) ^ N * invOnePlusX ^ N = 1 := by
    rw [← mul_pow, one_add_X_mul_inv, one_pow]
  calc (1 + PowerSeries.X) ^ (L - N) * (1 + PowerSeries.X) ^ N *
        (pc (transPoly P m) * invOnePlusX ^ N)
      = (1 + PowerSeries.X) ^ (L - N) * pc (transPoly P m) *
          ((1 + PowerSeries.X) ^ N * invOnePlusX ^ N) := by ring
    _ = _ := by rw [hinv, mul_one]

/-! ## Norm bounds -/

theorem pc_transPoly_eq (P : Polynomial ℂ) (m : ℕ) :
    pc (transPoly P m) = ∑ i ∈ Finset.range (P.natDegree + 1),
      P.coeff i • (1 + PowerSeries.X) ^ (m - i) := by
  rw [transPoly, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, map_pow, pc_X_add_one, PowerSeries.smul_eq_C_mul]
  simp [pc]

theorem normLe_pc_transPoly (P : Polynomial ℂ) (m : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    NormLe r (pc (transPoly P m))
      ((∑ i ∈ Finset.range (P.natDegree + 1), ‖P.coeff i‖) * (1 + r) ^ m) := by
  rw [pc_transPoly_eq, Finset.sum_mul]
  refine NormLe.sum _ hr fun i _ => ?_
  refine ((NormLe.pow hr (normLe_one_add_X hr) (m - i)).smul (P.coeff i)).mono ?_
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by linarith) (Nat.sub_le m i))
    (norm_nonneg _)

theorem normLe_transKer (P : Polynomial ℂ) (m N : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    NormLe r (transKer P m N)
      ((∑ i ∈ Finset.range (P.natDegree + 1), ‖P.coeff i‖) * (1 + r) ^ m * ((1 - r)⁻¹) ^ N) :=
  (normLe_pc_transPoly P m hr0).mul hr0 (NormLe.pow hr0 (normLe_inv hr0 hr1) N)

/-- The weighted norm of a polynomial. -/
theorem normLe_pc (P : Polynomial ℂ) {r : ℝ} (hr : 0 ≤ r) :
    NormLe r (pc P) (∑ i ∈ Finset.range (P.natDegree + 1), ‖P.coeff i‖ * r ^ i) := by
  intro N
  rw [show (∑ i ∈ Finset.range N, ‖PowerSeries.coeff i (pc P)‖ * r ^ i) =
      ∑ i ∈ (Finset.range N).filter (· ≤ P.natDegree), ‖P.coeff i‖ * r ^ i by
    rw [Finset.sum_filter_of_ne]
    · exact Finset.sum_congr rfl fun i _ => by rw [coeff_pc]
    · intro i _ hne
      by_contra h
      push Not at h
      apply hne
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt h, norm_zero, zero_mul]]
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun i hi => ?_) fun i _ _ => by positivity
  rw [Finset.mem_filter] at hi
  exact Finset.mem_range.mpr (by omega)

theorem normLe_omt {r : ℝ} (hr : 0 ≤ r) : NormLe r omt (1 + r) := by
  intro N
  calc ∑ i ∈ Finset.range N, ‖PowerSeries.coeff i omt‖ * r ^ i
      ≤ ∑ i ∈ Finset.range (N + 2), ‖PowerSeries.coeff i omt‖ * r ^ i :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
          fun i _ _ => by positivity
    _ = 1 + r := by
        rw [Finset.sum_range_succ', Finset.sum_range_succ']
        rw [Finset.sum_eq_zero fun i _ => by
          simp [omt, PowerSeries.coeff_one, PowerSeries.coeff_X]]
        simp [omt, PowerSeries.coeff_one, PowerSeries.coeff_X]
        ring

/-- Coefficient bound for the numerator `P = (1−t)^E F`. -/
theorem coeff_numerator_le {P : Polynomial ℂ} {E : ℕ} {F : PowerSeries ℂ} {w β : ℝ}
    (hw0 : 0 < w) (hw1 : w ≤ 1) (hP : omt ^ E * F = pc P)
    (hF : ∀ k, ‖PowerSeries.coeff k F‖ * w ^ k ≤ β) (i : ℕ) :
    ‖P.coeff i‖ * w ^ i ≤ 2 ^ E * β := by
  have h := coeff_mul_le hw0.le (NormLe.pow hw0.le (normLe_omt hw0.le) E) hF i
  rw [hP, coeff_pc] at h
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (le_trans (by positivity) (hF 0)))
  exact pow_le_pow_left₀ (by linarith) (by linarith) E

end VOA.Huang.GenusOneG1b
