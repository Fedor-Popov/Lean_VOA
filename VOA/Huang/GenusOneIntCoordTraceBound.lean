import VOA.Huang.GenusOneIntCoordMajorant

/-!
# The precise positive majorant needed for square traces

The scalar logarithmic expansion is completely eliminated from the convergence
question. What remains is positive radius for the sum of absolute square traces.
No uniform bound in the inserted state's degree is inferred from pointwise
one-point convergence.
-/

noncomputable section
namespace VOA.Huang.GenusOne.IntCoord
open VOA GenusTwoPoint GenusOneG1c VerlindeFusion VerlindeTransport TensorCat
open scoped BigOperators
universe u w
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  {ι : Type w} [Fintype ι] [DecidableEq ι] (D : VOA.ModularData W ι)
  {P Q : LWModule W}

/-- Absolute mass of the canonical square components of one inner coefficient. -/
def squareTraceMass
    (Y : IntertwiningOperator P.isMod Q.isMod (adjointModule W))
    (wa : P.carrier) (wb : Q.carrier) (α β : ℂ)
    (x : ι) (τ : UpperHalfPlane) (k : ℕ) : ℝ :=
  ∑' n : ℕ, ‖traceFun D.Mfam D.h x
    (squarePart (W := W) (vacuumInnerCoeff Y wa wb α β k) n) τ‖

theorem squareTraceMass_nonneg
    (Y : IntertwiningOperator P.isMod Q.isMod (adjointModule W))
    (wa : P.carrier) (wb : Q.carrier) (α β : ℂ)
    (x : ι) (τ : UpperHalfPlane) (k : ℕ) :
    0 ≤ squareTraceMass D Y wa wb α β x τ k :=
  tsum_nonneg fun _ => norm_nonneg _

theorem summable_norm_squareTrace (hC2 : C2Cofinite W)
    (x : ι) (τ : UpperHalfPlane) (v : V) :
    Summable (fun n : ℕ => ‖traceFun D.Mfam D.h x (squarePart (W := W) v n) τ‖) := by
  apply summable_of_ne_finset_zero (s := squareSupport (W := W) v)
  intro n hn
  rw [squarePart_eq_zero_of_not_mem hn]
  change ‖traceFunStateLinear D hC2 x τ 0‖ = 0
  rw [map_zero, norm_zero]

/-- The total sum in `squareTraceMass` is a finite sum with its canonical support. -/
theorem squareTraceMass_eq_sum (hC2 : C2Cofinite W)
    (Y : IntertwiningOperator P.isMod Q.isMod (adjointModule W))
    (wa : P.carrier) (wb : Q.carrier) (α β : ℂ)
    (x : ι) (τ : UpperHalfPlane) (k : ℕ) :
    squareTraceMass D Y wa wb α β x τ k =
      ∑ n ∈ squareSupport (W := W) (vacuumInnerCoeff Y wa wb α β k),
        ‖traceFun D.Mfam D.h x
          (squarePart (W := W) (vacuumInnerCoeff Y wa wb α β k) n) τ‖ := by
  apply tsum_eq_sum
  intro n hn
  rw [squarePart_eq_zero_of_not_mem hn]
  change ‖traceFunStateLinear D hC2 x τ 0‖ = 0
  rw [map_zero, norm_zero]

/-- An exact equivalence, including absolute convergence, at every complex point. -/
theorem logSquareTerm_summable_iff (hC2 : C2Cofinite W)
    (Y : IntertwiningOperator P.isMod Q.isMod (adjointModule W))
    (wa : P.carrier) (wb : Q.carrier) (α β : ℂ)
    (x : ι) (τ : UpperHalfPlane) (z : ℂ) :
    Summable (logSquareTerm D Y wa wb α β x τ z) ↔
      Summable (fun k : ℕ => (Real.exp ‖Complex.log (1 + z)‖ - 1) ^ k *
        squareTraceMass D Y wa wb α β x τ k) :=
  summable_expSubOneCoeff_mul_iff _
    (fun k => summable_norm_squareTrace D hC2 x τ (vacuumInnerCoeff Y wa wb α β k)) _

/-- A quantitative bound on the square-component masses suffices. All scalar
re-expansion and all infinite regrouping are proved in this implication. -/
theorem logSquareTraceSummable_of_squareTraceMass_bound (hC2 : C2Cofinite W)
    (Y : IntertwiningOperator P.isMod Q.isMod (adjointModule W))
    (wa : P.carrier) (wb : Q.carrier) (α β : ℂ)
    (hbound : ∀ τ : UpperHalfPlane, ∃ C B : ℝ, 0 ≤ C ∧ 0 ≤ B ∧
      ∀ (x : ι) (k : ℕ), squareTraceMass D Y wa wb α β x τ k ≤ C * B ^ k) :
    LogSquareTraceSummable D Y wa wb α β := by
  intro τ
  obtain ⟨C, B, hC, hB, hb⟩ := hbound τ
  have hBp : 0 < B + 1 := by linarith
  obtain ⟨δ, hδ, hd⟩ := exists_logMajorant_radius (inv_pos.mpr hBp)
  refine ⟨δ, hδ, fun x z _ hz => ?_⟩
  rw [logSquareTerm_summable_iff D hC2]
  set R := Real.exp ‖Complex.log (1 + z)‖ - 1
  have hR : 0 ≤ R := sub_nonneg.mpr (Real.one_le_exp (norm_nonneg _))
  have hsmall : R * B < 1 := calc
    R * B ≤ R * (B + 1) := mul_le_mul_of_nonneg_left (by linarith) hR
    _ < 1 := (lt_div_iff₀ hBp).mp (by simpa only [one_div] using hd z hz)
  have hs := (summable_geometric_of_lt_one (mul_nonneg hR hB) hsmall).mul_left C
  apply hs.of_nonneg_of_le
  · intro k
    exact mul_nonneg (pow_nonneg hR _) (squareTraceMass_nonneg D Y wa wb α β x τ k)
  · intro k
    calc
      R ^ k * squareTraceMass D Y wa wb α β x τ k ≤ R ^ k * (C * B ^ k) :=
        mul_le_mul_of_nonneg_left (hb x k) (pow_nonneg hR _)
      _ = C * (R * B) ^ k := by rw [mul_pow]; ring

/-- Conversely the requested half-disc convergence forces the same exponential
bound. Thus the quantitative obligation above is necessary as well as sufficient. -/
theorem squareTraceMass_bound_of_logSquareTraceSummable (hC2 : C2Cofinite W)
    (Y : IntertwiningOperator P.isMod Q.isMod (adjointModule W))
    (wa : P.carrier) (wb : Q.carrier) (α β : ℂ)
    (hs : LogSquareTraceSummable D Y wa wb α β) :
    ∀ τ : UpperHalfPlane, ∃ C B : ℝ, 0 ≤ C ∧ 0 ≤ B ∧
      ∀ (x : ι) (k : ℕ), squareTraceMass D Y wa wb α β x τ k ≤ C * B ^ k := by
  classical
  intro τ
  obtain ⟨δ, hδ, hd⟩ := hs τ
  let z : ℂ := (δ / 2 : ℝ)
  have hz : 0 < z.re := by change 0 < δ / 2; positivity
  have hnz : ‖z‖ < δ := by
    change ‖((δ / 2 : ℝ) : ℂ)‖ < δ
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    linarith
  let R : ℝ := Real.exp ‖Complex.log (1 + z)‖ - 1
  have hR : 0 < R := sub_pos.mpr (Real.one_lt_exp_iff.mpr
    (norm_pos_iff.mpr (log_coordinate_nonzero hz).2.2))
  have hsum (x : ι) : Summable (fun k : ℕ => R ^ k *
      squareTraceMass D Y wa wb α β x τ k) :=
    (logSquareTerm_summable_iff D hC2 Y wa wb α β x τ z).mp (hd x z hz hnz)
  let C : ℝ := ∑ x : ι, ∑' k : ℕ, R ^ k * squareTraceMass D Y wa wb α β x τ k
  have hterm (x : ι) (k : ℕ) : 0 ≤ R ^ k * squareTraceMass D Y wa wb α β x τ k :=
    mul_nonneg (pow_nonneg hR.le _) (squareTraceMass_nonneg D Y wa wb α β x τ k)
  refine ⟨C, R⁻¹, Finset.sum_nonneg (fun x _ => tsum_nonneg (hterm x)),
    inv_nonneg.mpr hR.le, fun x k => ?_⟩
  have hle : R ^ k * squareTraceMass D Y wa wb α β x τ k ≤ C :=
    ((hsum x).le_tsum k (fun j _ => hterm x j)).trans
      (Finset.single_le_sum (fun j _ => tsum_nonneg (hterm j)) (Finset.mem_univ x))
  rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ (pow_pos hR k)]
  simpa only [mul_comm] using hle

/-- Exact characterization of the remaining analytic input by exponential growth
of the absolute square-component masses. -/
theorem logSquareTraceSummable_iff_squareTraceMass_bound (hC2 : C2Cofinite W)
    (Y : IntertwiningOperator P.isMod Q.isMod (adjointModule W))
    (wa : P.carrier) (wb : Q.carrier) (α β : ℂ) :
    LogSquareTraceSummable D Y wa wb α β ↔
      ∀ τ : UpperHalfPlane, ∃ C B : ℝ, 0 ≤ C ∧ 0 ≤ B ∧
        ∀ (x : ι) (k : ℕ), squareTraceMass D Y wa wb α β x τ k ≤ C * B ^ k :=
  ⟨squareTraceMass_bound_of_logSquareTraceSummable D hC2 Y wa wb α β,
    logSquareTraceSummable_of_squareTraceMass_bound D hC2 Y wa wb α β⟩

end VOA.Huang.GenusOne.IntCoord
