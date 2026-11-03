import VOA.Huang.GenusTwoPointAssociativity
import VOA.Huang.GenusOneC2Convergence

/-!
# The analytic sewing obligation and reduction to one-point traces

The raw plane-coordinate iterate is an infinite sum of ordinary one-point traces.
One-point convergence supplies each fixed intermediate-level row. Joint summability
is kept explicit: convergence of rows and columns alone cannot justify Fubini.
No geometric modification, elliptic ODE, or modular-invariance claim is made here.
-/
namespace VOA.Huang.GenusTwoPoint
open VOA
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  {P₁ P₂ N Q : LWModule W}

/-- The conformal q-factor, with its branch fixed by τ in the upper half-plane. -/
noncomputable def qFactor (N : LWModule W) (τ : UpperHalfPlane) (n : ℕ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (τ : ℂ) *
    (N.h - W.centralCharge / 24)) * qParam τ ^ n

/-- q-evaluation of coefficients indexed by the actual traced weight. -/
noncomputable def qTrace (N : LWModule W) (F : ℂ → ℂ) (τ : UpperHalfPlane) : ℂ :=
  ∑' n : ℕ, F (N.h + n) * qFactor N τ n

/-- Remaining outer q-summability for a product. Intended region:
`1 > ‖z₁‖ > ‖z₂‖ > ‖qParam τ‖ > 0`. This is a predicate, not an assumed theorem. -/
def ProductQSummable (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    (w₁ : P₁.carrier) (w₂ : P₂.carrier) (α₁ α₂ z₁ z₂ : ℂ) (τ : UpperHalfPlane) : Prop :=
  Summable (fun n : ℕ => productCoeff Y₁ Y₂ w₁ w₂ α₁ α₂ (N.h + n) z₁ z₂ *
    qFactor N τ n)

/-- Full double-series product convergence, stronger than outer q-convergence.
For homogeneous insertions over a strongly rational VOA the intended target is
Huang's region `1 > ‖z₁‖ > ‖z₂‖ > ‖qParam τ‖ > 0`. -/
def ProductSewingSummable (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    (w₁ : P₁.carrier) (w₂ : P₂.carrier) (α₁ α₂ z₁ z₂ : ℂ) (τ : UpperHalfPlane) : Prop :=
  Summable (fun p : ℕ × ℕ =>
    productTerm Y₁ Y₂ w₁ w₂ α₁ α₂ (N.h + p.1) z₁ z₂ p.2 * qFactor N τ p.1)

/-- Joint product convergence implies convergence of the actual q-series. -/
theorem productQSummable_of_sewing
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    (w₁ : P₁.carrier) (w₂ : P₂.carrier) (α₁ α₂ z₁ z₂ : ℂ) (τ : UpperHalfPlane)
    (hs : ProductSewingSummable Y₁ Y₂ w₁ w₂ α₁ α₂ z₁ z₂ τ) :
    ProductQSummable Y₁ Y₂ w₁ w₂ α₁ α₂ z₁ z₂ τ := by
  simpa only [ProductQSummable, productCoeff, tsum_mul_right] using hs.prod

/-- Joint sewing estimate for the actual iterate terms, indexed by traced and
intermediate levels. Intended local sewing region: `‖qParam τ‖ < ‖z₂‖ < 1`
and sufficiently small nonzero `z₀`, as in Huang's local associativity chart.
No assertion for every `‖z₀‖ < ‖z₂‖` is made. -/
def IterateSewingSummable (Y₃ : IntertwiningOperator Q.isMod N.isMod N.isMod)
    (Y₄ : IntertwiningOperator P₁.isMod P₂.isMod Q.isMod)
    (w₁ : P₁.carrier) (w₂ : P₂.carrier) (α₁ α₂ z₀ z₂ : ℂ) (τ : UpperHalfPlane) : Prop :=
  Summable (fun p : ℕ × ℕ =>
    iterateTerm Y₃ Y₄ w₁ w₂ α₁ α₂ (N.h + p.1) z₀ z₂ p.2 * qFactor N τ p.1)

/-- Every fixed intermediate-level row already converges by the one-point theorem. -/
theorem hasSum_iterate_row (hC2 : C2Cofinite W) (iQ : Q.IsIrreducibleLW)
    (Y₃ : IntertwiningOperator Q.isMod N.isMod N.isMod)
    (Y₄ : IntertwiningOperator P₁.isMod P₂.isMod Q.isMod)
    {α₁ α₂ : ℂ} {w₁ : P₁.carrier} {w₂ : P₂.carrier}
    (h₁ : w₁ ∈ P₁.isMod.weight α₁) (h₂ : w₂ ∈ P₂.isMod.weight α₂)
    (z₀ z₂ : ℂ) (τ : UpperHalfPlane) (k : ℕ) :
    HasSum (fun n : ℕ => iterateTerm Y₃ Y₄ w₁ w₂ α₁ α₂ (N.h + n) z₀ z₂ k *
      qFactor N τ n)
      (GenusOne.traceFunction Y₃ N.h
        (Y₄.val ((α₁ + α₂ - 1 - Q.h) - k) w₁ w₂) τ *
        z₂ ^ (-((α₁ + α₂ - 2) - (α₁ + α₂ - 1 - Q.h) + k) - 1) *
        z₀ ^ (-((α₁ + α₂ - 1 - Q.h) - k) - 1)) := by
  have hs := GenusOne.hasSum_trace_of_irreducible hC2 iQ Y₃
    ⟨N.realized, N.isLow⟩ (Y₄.val ((α₁ + α₂ - 1 - Q.h) - k) w₁ w₂) τ
  refine ((hs.mul_right _).mul_right _).congr_fun (fun n => ?_)
  rw [iterateTerm_eq_onePoint Y₃ Y₄ h₁ h₂]
  unfold qFactor
  rw [show N.h + (n : ℂ) - W.centralCharge / 24 =
    N.h - W.centralCharge / 24 + n by ring]
  ring

/-- Joint sewing supplies genuine convergence of the outer iterate q-series. -/
theorem summable_iterate_q_of_sewing
    (Y₃ : IntertwiningOperator Q.isMod N.isMod N.isMod)
    (Y₄ : IntertwiningOperator P₁.isMod P₂.isMod Q.isMod)
    (w₁ : P₁.carrier) (w₂ : P₂.carrier) (α₁ α₂ z₀ z₂ : ℂ) (τ : UpperHalfPlane)
    (hs : IterateSewingSummable Y₃ Y₄ w₁ w₂ α₁ α₂ z₀ z₂ τ) :
    Summable (fun n : ℕ => iterateCoeff Y₃ Y₄ w₁ w₂ α₁ α₂ (N.h + n) z₀ z₂ *
      qFactor N τ n) := by
  simpa only [iterateCoeff, tsum_mul_right] using hs.prod

/-- Fubini reduction to one-point traces, with the sole sewing hypothesis explicit. -/
theorem iterateTrace_eq_tsum_onePoint (hC2 : C2Cofinite W) (iQ : Q.IsIrreducibleLW)
    (Y₃ : IntertwiningOperator Q.isMod N.isMod N.isMod)
    (Y₄ : IntertwiningOperator P₁.isMod P₂.isMod Q.isMod)
    {α₁ α₂ : ℂ} {w₁ : P₁.carrier} {w₂ : P₂.carrier}
    (h₁ : w₁ ∈ P₁.isMod.weight α₁) (h₂ : w₂ ∈ P₂.isMod.weight α₂)
    (z₀ z₂ : ℂ) (τ : UpperHalfPlane)
    (hs : IterateSewingSummable Y₃ Y₄ w₁ w₂ α₁ α₂ z₀ z₂ τ) :
    qTrace N (fun β => iterateCoeff Y₃ Y₄ w₁ w₂ α₁ α₂ β z₀ z₂) τ =
      ∑' k : ℕ, GenusOne.traceFunction Y₃ N.h
        (Y₄.val ((α₁ + α₂ - 1 - Q.h) - k) w₁ w₂) τ *
        z₂ ^ (-((α₁ + α₂ - 2) - (α₁ + α₂ - 1 - Q.h) + k) - 1) *
        z₀ ^ (-((α₁ + α₂ - 1 - Q.h) - k) - 1) := by
  unfold qTrace iterateCoeff
  simp only [← tsum_mul_right]
  rw [← Summable.tsum_comm (f := fun (n k : ℕ) =>
    iterateTerm Y₃ Y₄ w₁ w₂ α₁ α₂ (N.h + n) z₀ z₂ k * qFactor N τ n) hs]
  exact tsum_congr (fun k => (hasSum_iterate_row hC2 iQ Y₃ Y₄ h₁ h₂ z₀ z₂ τ k).tsum_eq)

/-- The one-point expansion on the preceding right-hand side is also summable. -/
theorem summable_onePoint_expansion (hC2 : C2Cofinite W) (iQ : Q.IsIrreducibleLW)
    (Y₃ : IntertwiningOperator Q.isMod N.isMod N.isMod)
    (Y₄ : IntertwiningOperator P₁.isMod P₂.isMod Q.isMod)
    {α₁ α₂ : ℂ} {w₁ : P₁.carrier} {w₂ : P₂.carrier}
    (h₁ : w₁ ∈ P₁.isMod.weight α₁) (h₂ : w₂ ∈ P₂.isMod.weight α₂)
    (z₀ z₂ : ℂ) (τ : UpperHalfPlane)
    (hs : IterateSewingSummable Y₃ Y₄ w₁ w₂ α₁ α₂ z₀ z₂ τ) :
    Summable (fun k : ℕ => GenusOne.traceFunction Y₃ N.h
        (Y₄.val ((α₁ + α₂ - 1 - Q.h) - k) w₁ w₂) τ *
        z₂ ^ (-((α₁ + α₂ - 2) - (α₁ + α₂ - 1 - Q.h) + k) - 1) *
        z₀ ^ (-((α₁ + α₂ - 1 - Q.h) - k) - 1)) :=
  hs.prod_symm.prod.congr (fun k =>
    (hasSum_iterate_row hC2 iQ Y₃ Y₄ h₁ h₂ z₀ z₂ τ k).tsum_eq)

/-- Coefficientwise associativity passes to convergent q-traces as soon as the
finite iterate channels satisfy the joint sewing estimate. -/
theorem product_qTrace_eq_of_coefficients {r : ℕ} (R : Fin r → LWModule W)
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    (Y₃ : ∀ j, IntertwiningOperator (R j).isMod N.isMod N.isMod)
    (Y₄ : ∀ j, IntertwiningOperator P₁.isMod P₂.isMod (R j).isMod)
    (w₁ : P₁.carrier) (w₂ : P₂.carrier) (α₁ α₂ z₁ z₂ : ℂ) (τ : UpperHalfPlane)
    (heq : ∀ β, productCoeff Y₁ Y₂ w₁ w₂ α₁ α₂ β z₁ z₂ =
      ∑ j, iterateCoeff (Y₃ j) (Y₄ j) w₁ w₂ α₁ α₂ β (z₁ - z₂) z₂)
    (hs : ∀ j, IterateSewingSummable (Y₃ j) (Y₄ j) w₁ w₂ α₁ α₂ (z₁ - z₂) z₂ τ) :
    ProductQSummable Y₁ Y₂ w₁ w₂ α₁ α₂ z₁ z₂ τ ∧
    qTrace N (fun β => productCoeff Y₁ Y₂ w₁ w₂ α₁ α₂ β z₁ z₂) τ =
      ∑ j, qTrace N (fun β => iterateCoeff (Y₃ j) (Y₄ j) w₁ w₂ α₁ α₂ β (z₁ - z₂) z₂) τ := by
  have ht := fun j => summable_iterate_q_of_sewing (Y₃ j) (Y₄ j) w₁ w₂
    α₁ α₂ (z₁ - z₂) z₂ τ (hs j)
  constructor
  · unfold ProductQSummable
    simp only [heq, Finset.sum_mul]
    exact summable_sum (fun j _ => ht j)
  · simp only [qTrace, heq, Finset.sum_mul]
    exact Summable.tsum_finsetSum (fun j _ => ht j)

end VOA.Huang.GenusTwoPoint
