import VOA.Huang.GenusOneIntCoordSquareTrace

/-!
# Scalar logarithmic re-expansion of the vacuum trace

The explicit coefficients expand `(exp y - 1)^k`. Their scalar series converge
everywhere. The joint square-component estimate is kept as a separate analytic
obligation; pointwise finite square decomposition alone does not prove it.
-/

noncomputable section
namespace VOA.Huang.GenusOne.IntCoord
open VOA GenusTwoPoint GenusOneG1c VerlindeFusion VerlindeTransport TensorCat Complex
open scoped BigOperators

/-- Taylor coefficients of the scalar entire function `(exp y - 1)^k`. -/
def expSubOneCoeff (k r : ℕ) : ℂ :=
  ∑ i ∈ Finset.range (k + 1),
    (-1 : ℂ) ^ (k - i) * (k.choose i : ℂ) * (i : ℂ) ^ r / (r.factorial : ℂ)

theorem hasSum_expSubOneCoeff (k : ℕ) (y : ℂ) :
    HasSum (fun r : ℕ => expSubOneCoeff k r * y ^ r) ((exp y - 1) ^ k) := by
  have hs := hasSum_sum (s := Finset.range (k + 1)) (fun i _ =>
    (NormedSpace.expSeries_div_hasSum_exp ((i : ℂ) * y)).mul_left
      ((-1 : ℂ) ^ (k - i) * (k.choose i : ℂ)))
  have he : (∑ i ∈ Finset.range (k + 1),
      (-1 : ℂ) ^ (k - i) * (k.choose i : ℂ) * NormedSpace.exp ((i : ℂ) * y)) =
      (exp y - 1) ^ k := by
    simp only [← Complex.exp_eq_exp_ℂ, Complex.exp_nat_mul]
    rw [sub_eq_add_neg, add_pow]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [he] at hs
  refine hs.congr_fun fun r => ?_
  simp only [expSubOneCoeff, Finset.sum_mul, mul_pow]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem hasSum_expSubOneCoeff_log (k : ℕ) {z : ℂ} (hz : 1 + z ≠ 0) :
    HasSum (fun r : ℕ => expSubOneCoeff k r * log (1 + z) ^ r) (z ^ k) := by
  simpa only [Complex.exp_log hz, add_sub_cancel_left] using
    hasSum_expSubOneCoeff k (log (1 + z))

universe u w
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  {ι : Type w} [Fintype ι] [DecidableEq ι] (D : VOA.ModularData W ι)
  {P Q : LWModule W}

/-- The actual triple series, before flattening its countable index. -/
def logSquareTerm
    (Y : IntertwiningOperator P.isMod Q.isMod (adjointModule W))
    (wa : P.carrier) (wb : Q.carrier) (α β : ℂ)
    (x : ι) (τ : UpperHalfPlane) (z : ℂ) (p : ℕ × (ℕ × ℕ)) : ℂ :=
  expSubOneCoeff p.1 p.2.2 * log (1 + z) ^ p.2.2 *
    traceFun D.Mfam D.h x
      (squarePart (W := W) (vacuumInnerCoeff Y wa wb α β p.1) p.2.1) τ

/-- A concrete remaining analytic estimate, on explicit coefficients and states.
No coordinate identity, modular covariance, or intertwiner substitution is
assumed here. The assertion is joint absolute convergence, uniform in the finite
traced family on a τ-dependent half-disc. -/
def LogSquareTraceSummable
    (Y : IntertwiningOperator P.isMod Q.isMod (adjointModule W))
    (wa : P.carrier) (wb : Q.carrier) (α β : ℂ) : Prop :=
  ∀ τ : UpperHalfPlane, ∃ δ : ℝ, 0 < δ ∧ ∀ (x : ι) (z : ℂ),
    0 < z.re → ‖z‖ < δ → Summable (logSquareTerm D Y wa wb α β x τ z)

/-- Summing the scalar Taylor index recovers the original plane monomial. -/
theorem logSquareTerm_scalar_sum
    (Y : IntertwiningOperator P.isMod Q.isMod (adjointModule W))
    (wa : P.carrier) (wb : Q.carrier) (α β : ℂ)
    (x : ι) (τ : UpperHalfPlane) {z : ℂ} (hz : 1 + z ≠ 0) (k n : ℕ) :
    (∑' r : ℕ, logSquareTerm D Y wa wb α β x τ z (k, n, r)) =
      z ^ k * traceFun D.Mfam D.h x
        (squarePart (W := W) (vacuumInnerCoeff Y wa wb α β k) n) τ := by
  exact ((hasSum_expSubOneCoeff_log k hz).mul_right
    (traceFun D.Mfam D.h x
      (squarePart (W := W) (vacuumInnerCoeff Y wa wb α β k) n) τ)).tsum_eq

/-- Joint convergence permits both regroupings, yielding the original
coefficient sequence after removing its common complex-power prefactor. -/
theorem logSquareTerm_tsum (hC2 : C2Cofinite W)
    (Y : IntertwiningOperator P.isMod Q.isMod (adjointModule W))
    (wa : P.carrier) (wb : Q.carrier) (α β : ℂ)
    (x : ι) (τ : UpperHalfPlane) {z : ℂ} (hz : 1 + z ≠ 0)
    (hs : Summable (logSquareTerm D Y wa wb α β x τ z)) :
    (∑' p : ℕ × (ℕ × ℕ), logSquareTerm D Y wa wb α β x τ z p) =
      ∑' k : ℕ, z ^ k * traceFun D.Mfam D.h x (vacuumInnerCoeff Y wa wb α β k) τ := by
  rw [hs.tsum_prod]
  apply tsum_congr
  intro k
  rw [(hs.prod_factor k).tsum_prod]
  simp_rw [logSquareTerm_scalar_sum D Y wa wb α β x τ hz]
  rw [tsum_mul_left]
  congr 1
  rw [traceFun_eq_sum_squarePart D hC2]
  apply tsum_eq_sum
  intro n hn
  rw [squarePart_eq_zero_of_not_mem hn]
  exact (traceFunStateLinear D hC2 x τ).map_zero

/-- The complex power factored out of the plane expansion. -/
theorem planePower_eq (α β z : ℂ) (hz : z ≠ 0) (k : ℕ) :
    z ^ ((k : ℂ) - α - β) = z ^ (-α - β) * z ^ k := by
  rw [show (k : ℂ) - α - β = (-α - β) + k by ring,
    Complex.cpow_add _ _ hz, Complex.cpow_natCast]

/-- A fixed-point logarithmic identity follows solely from the explicit joint
estimate and the already-proved plane sewing estimate. -/
theorem vacuum_iterF_eq_logSquare (hC2 : C2Cofinite W) (hv : W.vacuum ≠ 0)
    (Y : IntertwiningOperator P.isMod Q.isMod (adjointModule W))
    {wa : P.carrier} {wb : Q.carrier} {α β : ℂ}
    (hwa : wa ∈ P.isMod.weight α) (hwb : wb ∈ Q.isMod.weight β)
    (x : ι) (τ : UpperHalfPlane) {z : ℂ} (hz : z ≠ 0) (hz1 : 1 + z ≠ 0)
    (hplane : IterateSewingSummable (Q := vacuumLW W hv) (N := lwOf D x)
      (moduleIntertwiner (lwOf D x).isMod) Y wa wb α β z 1 τ)
    (hlog : Summable (logSquareTerm D Y wa wb α β x τ z)) :
    iterF (Q := vacuumLW W hv) (N := lwOf D x)
        (moduleIntertwiner (lwOf D x).isMod) Y wa wb α β τ z =
      z ^ (-α - β) * ∑' p : ℕ × (ℕ × ℕ), logSquareTerm D Y wa wb α β x τ z p := by
  rw [logSquareTerm_tsum D hC2 Y wa wb α β x τ hz1 hlog, ← tsum_mul_left]
  exact (vacuum_iterF_eq_tsum_traceFun D hv Y hwa hwb x τ z hplane).tsum_eq.symm.trans
    (tsum_congr fun k => by rw [planePower_eq α β z hz]; ring)

end VOA.Huang.GenusOne.IntCoord
