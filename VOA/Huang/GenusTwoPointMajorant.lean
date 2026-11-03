import VOA.Huang.GenusTwoPointSewing

/-!
# Two-level coefficient bounds and absolute sewing

This file isolates coefficient estimates BEFORE either coordinate series is summed.
The implications to sewing below are proved; existence of the uniform estimates
for general intertwiners is not asserted. Separate one-index estimates do not
provide them. The product variables are `q z₁/z₂` and `z₂/z₁`; this also records
the scale-invariant raw-coordinate sewing region.
-/
namespace VOA.Huang.GenusTwoPoint
open VOA
open scoped BigOperators
universe u

/-- A geometric estimate on individual coefficients, with both levels independent. -/
def TwoLevelBound (c : ℕ → ℕ → ℂ) (C a b : ℝ) : Prop :=
  ∀ n k, ‖c n k‖ ≤ C * a ^ n * b ^ k

/-- A coefficient bound with a strict margin in both variables gives joint, hence
absolute, summability. No interchange of conditionally convergent sums is used. -/
theorem summable_twoLevel_of_bound {c : ℕ → ℕ → ℂ} {C a b : ℝ}
    (_hC : 0 ≤ C) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : TwoLevelBound c C a b)
    {x y : ℂ} (hx : a * ‖x‖ < 1) (hy : b * ‖y‖ < 1) :
    Summable (fun p : ℕ × ℕ => c p.1 p.2 * x ^ p.1 * y ^ p.2) := by
  have hs := summable_mul_of_summable_norm
    (summable_geometric_of_lt_one (mul_nonneg ha (norm_nonneg x)) hx).norm
    (summable_geometric_of_lt_one (mul_nonneg hb (norm_nonneg y)) hy).norm
  apply (hs.mul_left C).of_norm_bounded
  intro p
  simp only [norm_mul, norm_pow]
  calc
    ‖c p.1 p.2‖ * ‖x‖ ^ p.1 * ‖y‖ ^ p.2 ≤
        (C * a ^ p.1 * b ^ p.2) * ‖x‖ ^ p.1 * ‖y‖ ^ p.2 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hc p.1 p.2) (pow_nonneg (norm_nonneg x) _))
        (pow_nonneg (norm_nonneg y) _)
    _ = C * ((a * ‖x‖) ^ p.1 * (b * ‖y‖) ^ p.2) := by ring

variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  {P₁ P₂ N Q : LWModule W}

/-- The product coefficient stripped of coordinate and conformal q factors. -/
noncomputable def productLevelCoeff
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    (w₁ : P₁.carrier) (w₂ : P₂.carrier) (α₁ α₂ : ℂ) (n k : ℕ) : ℂ :=
  productModeTrace Y₁ Y₂ w₁ w₂
    ((α₁ + α₂ - 2) - (α₂ + N.h + n - 1 - Q.h) + k)
    ((α₂ + N.h + n - 1 - Q.h) - k)
    (N.h + n - W.centralCharge / 24)

/-- The iterate coefficient stripped of coordinate and conformal q factors. -/
noncomputable def iterateLevelCoeff
    (Y₃ : IntertwiningOperator Q.isMod N.isMod N.isMod)
    (Y₄ : IntertwiningOperator P₁.isMod P₂.isMod Q.isMod)
    (w₁ : P₁.carrier) (w₂ : P₂.carrier) (α₁ α₂ : ℂ) (n k : ℕ) : ℂ :=
  iterateModeTrace Y₃ Y₄ w₁ w₂ ((α₁ + α₂ - 1 - Q.h) - k)
    ((α₁ + α₂ - 2) - (α₁ + α₂ - 1 - Q.h) + k)
    (N.h + n - W.centralCharge / 24)

/-- Separating integer shifts requires no multiplication rule for principal
complex powers of different bases. -/
theorem cpow_add_nat_sub_nat {z : ℂ} (hz : z ≠ 0) (s : ℂ) (n k : ℕ) :
    z ^ (s + n - k) = z ^ s * z ^ n / z ^ k := by
  rw [Complex.cpow_sub _ _ hz, Complex.cpow_add _ _ hz,
    Complex.cpow_natCast, Complex.cpow_natCast]

theorem productTerm_qFactor_eq
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    (w₁ : P₁.carrier) (w₂ : P₂.carrier) (α₁ α₂ : ℂ)
    {z₁ z₂ : ℂ} (hz₁ : z₁ ≠ 0) (hz₂ : z₂ ≠ 0) (τ : UpperHalfPlane) (n k : ℕ) :
    productTerm Y₁ Y₂ w₁ w₂ α₁ α₂ (N.h + n) z₁ z₂ k * qFactor N τ n =
      (z₁ ^ (-α₁ + N.h - Q.h) * z₂ ^ (-α₂ - N.h + Q.h) * qFactor N τ 0) *
        (productLevelCoeff Y₁ Y₂ w₁ w₂ α₁ α₂ n k *
          (qParam τ * z₁ / z₂) ^ n * (z₂ / z₁) ^ k) := by
  unfold productTerm productLevelCoeff qFactor
  simp only [pow_zero, mul_one]
  rw [show α₂ + (N.h + (n : ℂ)) - 1 - Q.h = α₂ + N.h + n - 1 - Q.h by ring]
  rw [show -((α₁ + α₂ - 2) - (α₂ + N.h + (n : ℂ) - 1 - Q.h) + k) - 1 =
      (-α₁ + N.h - Q.h) + n - k by ring,
    show -((α₂ + N.h + (n : ℂ) - 1 - Q.h) - k) - 1 =
      (-α₂ - N.h + Q.h) + k - n by ring]
  rw [cpow_add_nat_sub_nat hz₁, cpow_add_nat_sub_nat hz₂]
  simp only [div_pow, mul_pow]
  ring

theorem iterateTerm_qFactor_eq
    (Y₃ : IntertwiningOperator Q.isMod N.isMod N.isMod)
    (Y₄ : IntertwiningOperator P₁.isMod P₂.isMod Q.isMod)
    (w₁ : P₁.carrier) (w₂ : P₂.carrier) (α₁ α₂ : ℂ)
    {z₀ z₂ : ℂ} (hz₀ : z₀ ≠ 0) (hz₂ : z₂ ≠ 0) (τ : UpperHalfPlane) (n k : ℕ) :
    iterateTerm Y₃ Y₄ w₁ w₂ α₁ α₂ (N.h + n) z₀ z₂ k * qFactor N τ n =
      (z₂ ^ (-Q.h) * z₀ ^ (-α₁ - α₂ + Q.h) * qFactor N τ 0) *
        (iterateLevelCoeff Y₃ Y₄ w₁ w₂ α₁ α₂ n k *
          qParam τ ^ n * (z₀ / z₂) ^ k) := by
  unfold iterateTerm iterateLevelCoeff qFactor
  simp only [pow_zero, mul_one]
  rw [show -((α₁ + α₂ - 2) - (α₁ + α₂ - 1 - Q.h) + (k : ℂ)) - 1 =
      -Q.h + (0 : ℕ) - k by ring,
    show -((α₁ + α₂ - 1 - Q.h) - (k : ℂ)) - 1 =
      (-α₁ - α₂ + Q.h) + k - (0 : ℕ) by ring]
  rw [cpow_add_nat_sub_nat hz₂, cpow_add_nat_sub_nat hz₀]
  simp only [pow_zero, mul_one, div_one, div_pow]
  ring

/-- Product sewing from a concrete bound on the raw rectangular-mode traces. -/
theorem productSewingSummable_of_modeBound
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    (w₁ : P₁.carrier) (w₂ : P₂.carrier) (α₁ α₂ : ℂ)
    {C a b : ℝ} (hC : 0 ≤ C) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hbound : TwoLevelBound (productLevelCoeff Y₁ Y₂ w₁ w₂ α₁ α₂) C a b)
    {z₁ z₂ : ℂ} (hz₁ : z₁ ≠ 0) (hz₂ : z₂ ≠ 0) (τ : UpperHalfPlane)
    (hq : a * ‖qParam τ * z₁ / z₂‖ < 1) (hz : b * ‖z₂ / z₁‖ < 1) :
    ProductSewingSummable Y₁ Y₂ w₁ w₂ α₁ α₂ z₁ z₂ τ := by
  have hs := (summable_twoLevel_of_bound hC ha hb hbound hq hz).mul_left
    (z₁ ^ (-α₁ + N.h - Q.h) * z₂ ^ (-α₂ - N.h + Q.h) * qFactor N τ 0)
  exact hs.congr fun p => (productTerm_qFactor_eq Y₁ Y₂ w₁ w₂ α₁ α₂ hz₁ hz₂ τ p.1 p.2).symm

/-- Iterate sewing from a concrete bound on the raw iterate-mode traces. -/
theorem iterateSewingSummable_of_modeBound
    (Y₃ : IntertwiningOperator Q.isMod N.isMod N.isMod)
    (Y₄ : IntertwiningOperator P₁.isMod P₂.isMod Q.isMod)
    (w₁ : P₁.carrier) (w₂ : P₂.carrier) (α₁ α₂ : ℂ)
    {C a b : ℝ} (hC : 0 ≤ C) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hbound : TwoLevelBound (iterateLevelCoeff Y₃ Y₄ w₁ w₂ α₁ α₂) C a b)
    {z₀ z₂ : ℂ} (hz₀ : z₀ ≠ 0) (hz₂ : z₂ ≠ 0) (τ : UpperHalfPlane)
    (hq : a * ‖qParam τ‖ < 1) (hz : b * ‖z₀ / z₂‖ < 1) :
    IterateSewingSummable Y₃ Y₄ w₁ w₂ α₁ α₂ z₀ z₂ τ := by
  have hs := (summable_twoLevel_of_bound hC ha hb hbound hq hz).mul_left
    (z₂ ^ (-Q.h) * z₀ ^ (-α₁ - α₂ + Q.h) * qFactor N τ 0)
  exact hs.congr fun p => (iterateTerm_qFactor_eq Y₃ Y₄ w₁ w₂ α₁ α₂ hz₀ hz₂ τ p.1 p.2).symm

end VOA.Huang.GenusTwoPoint
