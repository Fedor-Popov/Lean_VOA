import VOA.Huang.GenusOneG1bTransport
import VOA.Huang.GenusOneG1IterateConverse
import VOA.Huang.GenusOneG1ProductGrowth

/-!
# Product and iterate rows on the real segment

At fixed traced level `n`, with `z₂ = 1` and positive real `z₁ = 1 + s`, `z₀ = s`:

* `productCoeff_eq_evS`: the product coefficient is `(1+s)^{−α₁+h_N−h_Q+n}` times the row
  `coeff n (Phi Y₁ Y₂ x y)` evaluated at `t = 1/(1+s)`;
* `iterateCoeff_eq_evS`: the iterate coefficient is `s^{h_Q−α₁−α₂}` times the iterate row
  `iterRow … n = Σ_k iterateLevelCoeff … n k · X^k` evaluated at `s`;
* `iterRow_bound`: every iterate row is bounded in the weighted sup norm at every radius
  `r < 1` (genus-zero convergence of the iterate);
* `phiRow_sumAt`: every product row converges at every `0 < t < 1`.
-/
noncomputable section
namespace VOA.Huang.GenusOneG1b
open VOA
open scoped BigOperators
open VOA.Huang.GenusOneWard (Phi c2 productLevelCoeff_eq_c2 conv_Phi)
open VOA.Huang.GenusTwoPoint (productCoeff iterateCoeff productTerm iterateTerm
  productLevelCoeff iterateLevelCoeff cpow_add_nat_sub_nat summable_iterateTerm)
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  {P₁ P₂ N Q : LWModule W}

/-- The iterate row at traced level `n` as a power series in `x = z₀/z₂`. -/
def iterRow (Y₃ : IntertwiningOperator Q.isMod N.isMod N.isMod)
    (Y₄ : IntertwiningOperator P₁.isMod P₂.isMod Q.isMod)
    (w₁ : P₁.carrier) (w₂ : P₂.carrier) (α₁ α₂ : ℂ) (n : ℕ) : PowerSeries ℂ :=
  PowerSeries.mk fun k => iterateLevelCoeff Y₃ Y₄ w₁ w₂ α₁ α₂ n k

theorem coeff_iterRow (Y₃ : IntertwiningOperator Q.isMod N.isMod N.isMod)
    (Y₄ : IntertwiningOperator P₁.isMod P₂.isMod Q.isMod)
    (w₁ : P₁.carrier) (w₂ : P₂.carrier) (α₁ α₂ : ℂ) (n k : ℕ) :
    PowerSeries.coeff k (iterRow Y₃ Y₄ w₁ w₂ α₁ α₂ n) = iterateLevelCoeff Y₃ Y₄ w₁ w₂ α₁ α₂ n k := by
  simp [iterRow]

theorem iterateTerm_eq (Y₃ : IntertwiningOperator Q.isMod N.isMod N.isMod)
    (Y₄ : IntertwiningOperator P₁.isMod P₂.isMod Q.isMod)
    (w₁ : P₁.carrier) (w₂ : P₂.carrier) (α₁ α₂ : ℂ) (n : ℕ) {s : ℂ} (hs : s ≠ 0) (k : ℕ) :
    iterateTerm Y₃ Y₄ w₁ w₂ α₁ α₂ (N.h + n) s 1 k =
      s ^ (Q.h - α₁ - α₂) * (iterateLevelCoeff Y₃ Y₄ w₁ w₂ α₁ α₂ n k * s ^ k) := by
  unfold iterateTerm iterateLevelCoeff
  rw [Complex.one_cpow, mul_one,
    show -((α₁ + α₂ - 1 - Q.h) - (k : ℂ)) - 1 = (Q.h - α₁ - α₂) + (k : ℂ) by ring,
    Complex.cpow_add _ _ hs, Complex.cpow_natCast]
  ring

/-- The iterate coefficient on the real segment is a row evaluation. -/
theorem iterateCoeff_eq_evS (Y₃ : IntertwiningOperator Q.isMod N.isMod N.isMod)
    (Y₄ : IntertwiningOperator P₁.isMod P₂.isMod Q.isMod)
    (w₁ : P₁.carrier) (w₂ : P₂.carrier) (α₁ α₂ : ℂ) (n : ℕ) {s : ℂ} (hs : s ≠ 0) :
    iterateCoeff Y₃ Y₄ w₁ w₂ α₁ α₂ (N.h + n) s 1 =
      s ^ (Q.h - α₁ - α₂) * evS (iterRow Y₃ Y₄ w₁ w₂ α₁ α₂ n) s := by
  unfold iterateCoeff evS
  simp only [iterateTerm_eq Y₃ Y₄ w₁ w₂ α₁ α₂ n hs, coeff_iterRow]
  exact tsum_mul_left

theorem productTerm_eq (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod) {α₁ α₂ : ℂ} {x : P₁.carrier}
    {y : P₂.carrier} (hx : x ∈ P₁.isMod.weight α₁) (hy : y ∈ P₂.isMod.weight α₂)
    (n : ℕ) {z : ℂ} (hz : z ≠ 0) (k : ℕ) :
    productTerm Y₁ Y₂ x y α₁ α₂ (N.h + n) z 1 k =
      z ^ (-α₁ + N.h - Q.h + n) * (c2 (Phi Y₁ Y₂ x y) n k * z⁻¹ ^ k) := by
  rw [← productLevelCoeff_eq_c2 Y₁ Y₂ hx hy]
  unfold productTerm productLevelCoeff
  rw [Complex.one_cpow, mul_one,
    show α₂ + (N.h + (n : ℂ)) - 1 - Q.h = α₂ + N.h + n - 1 - Q.h by ring,
    show -((α₁ + α₂ - 2) - (α₂ + N.h + (n : ℂ) - 1 - Q.h) + k) - 1 =
      (-α₁ + N.h - Q.h) + n - k by ring,
    cpow_add_nat_sub_nat hz, Complex.cpow_add _ _ hz, Complex.cpow_natCast, inv_pow]
  ring

/-- The product coefficient on the real segment is a row evaluation. -/
theorem productCoeff_eq_evS (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod) {α₁ α₂ : ℂ} {x : P₁.carrier}
    {y : P₂.carrier} (hx : x ∈ P₁.isMod.weight α₁) (hy : y ∈ P₂.isMod.weight α₂)
    (n : ℕ) {z : ℂ} (hz : z ≠ 0) :
    productCoeff Y₁ Y₂ x y α₁ α₂ (N.h + n) z 1 =
      z ^ (-α₁ + N.h - Q.h + n) * evS (PowerSeries.coeff n (Phi Y₁ Y₂ x y)) z⁻¹ := by
  unfold productCoeff evS
  simp only [productTerm_eq Y₁ Y₂ hx hy n hz]
  rw [tsum_mul_left]
  rfl

/-- Product rows converge on `0 < t < 1`. -/
theorem phiRow_sumAt (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod) (hV : StronglyRational W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW) (iN : N.IsIrreducibleLW)
    (x : P₁.carrier) (y : P₂.carrier) (n : ℕ) {t : ℂ} (ht0 : t ≠ 0) (ht : ‖t‖ < 1) :
    SumAt (PowerSeries.coeff n (Phi Y₁ Y₂ x y)) t := by
  have hc := conv_Phi Y₁ Y₂ hV i₁ i₂ iN (z₁ := 1) ht0 (by rw [norm_one]; exact ht) x y n
  rw [div_one] at hc
  exact hc.of_norm

/-- Every iterate row is bounded in the weighted sup norm at every radius `r < 1`. -/
theorem iterRow_bound (hV : StronglyRational W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW) (iN : N.IsIrreducibleLW)
    (Y₃ : IntertwiningOperator Q.isMod N.isMod N.isMod)
    (Y₄ : IntertwiningOperator P₁.isMod P₂.isMod Q.isMod)
    {α₁ α₂ : ℂ} {w₁ : P₁.carrier} {w₂ : P₂.carrier}
    (h₁ : w₁ ∈ P₁.isMod.weight α₁) (h₂ : w₂ ∈ P₂.isMod.weight α₂) (n : ℕ)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∃ B : ℝ, ∀ k, ‖PowerSeries.coeff k (iterRow Y₃ Y₄ w₁ w₂ α₁ α₂ n)‖ * r ^ k ≤ B := by
  set r' : ℝ := (1 + r) / 2 with hr'
  have hr'0 : 0 < r' := by rw [hr']; linarith
  have hr'1 : r' < 1 := by rw [hr']; linarith
  have hrr : r ≤ r' := by rw [hr']; linarith
  have hz0 : ((r' : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr'0.ne'
  have hz : ‖((r' : ℝ) : ℂ)‖ < ‖(1 : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_of_nonneg hr'0.le, norm_one]; exact hr'1
  have hs := summable_iterateTerm hV i₁ i₂ iN Y₃ Y₄ h₁ h₂ (N.h + n) hz0 hz
  have hsn := (summable_norm_iff (E := ℂ)).mpr hs
  set S := ∑' k, ‖iterateTerm Y₃ Y₄ w₁ w₂ α₁ α₂ (N.h + n) (r' : ℂ) 1 k‖
  set c := ‖((r' : ℝ) : ℂ) ^ (Q.h - α₁ - α₂)‖ with hc
  have hc0 : 0 < c := by
    rw [hc, norm_pos_iff]
    exact Complex.cpow_ne_zero_iff.mpr (Or.inl hz0)
  refine ⟨S / c, fun k => ?_⟩
  have hle := hsn.le_tsum k (fun j _ => norm_nonneg _)
  rw [iterateTerm_eq Y₃ Y₄ w₁ w₂ α₁ α₂ n hz0 k, norm_mul, norm_mul, norm_pow,
    Complex.norm_real, Real.norm_of_nonneg hr'0.le, ← coeff_iterRow Y₃ Y₄ w₁ w₂ α₁ α₂ n k]
    at hle
  rw [le_div_iff₀ hc0]
  calc ‖PowerSeries.coeff k (iterRow Y₃ Y₄ w₁ w₂ α₁ α₂ n)‖ * r ^ k * c
      ≤ ‖PowerSeries.coeff k (iterRow Y₃ Y₄ w₁ w₂ α₁ α₂ n)‖ * r' ^ k * c := by
        gcongr
    _ = c * (‖PowerSeries.coeff k (iterRow Y₃ Y₄ w₁ w₂ α₁ α₂ n)‖ * r' ^ k) := by ring
    _ ≤ S := hle

end VOA.Huang.GenusOneG1b
