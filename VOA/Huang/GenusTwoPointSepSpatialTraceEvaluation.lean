import VOA.Huang.GenusTwoPointSepFormalTrace

/-!
# Evaluating the actual raw spatial trace, with q still formal

The intermediate-level power series is factored from the two principal complex
powers. Only integer shifts of exponents are split; no multiplication law for
principal powers of different bases is used. Genus-zero convergence puts this
actual power series in `spatialConvergent (z₂/z₁)` at every traced grade.
-/
noncomputable section
namespace VOA.Huang.GenusTwoPoint.Separate
open VOA
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  {P₁ P₂ N Q : LWModule W}

/-- The normalized spatial series at one traced grade, before spatial evaluation. -/
def rawLevelSeries
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    (x : P₁.carrier) (y : P₂.carrier) (α₁ α₂ β : ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun k => productModeTrace Y₁ Y₂ x y
    ((α₁ + α₂ - 2) - (α₂ + β - 1 - Q.h) + k)
    ((α₂ + β - 1 - Q.h) - k) (β - W.centralCharge / 24)

/-- The principal-branch prefactor, kept separate from the integral spatial powers. -/
def rawSpatialPrefactor (Q : LWModule W) (α₁ α₂ β z₁ z₂ : ℂ) : ℂ :=
  z₁ ^ (β - Q.h - α₁) * z₂ ^ (Q.h - β - α₂)

theorem productTerm_eq_spatialTerm
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    (x : P₁.carrier) (y : P₂.carrier) (α₁ α₂ β : ℂ)
    {z₁ z₂ : ℂ} (hz₁ : z₁ ≠ 0) (hz₂ : z₂ ≠ 0) (k : ℕ) :
    productTerm Y₁ Y₂ x y α₁ α₂ β z₁ z₂ k =
      rawSpatialPrefactor Q α₁ α₂ β z₁ z₂ *
        (PowerSeries.coeff k (rawLevelSeries Y₁ Y₂ x y α₁ α₂ β) * (z₂ / z₁) ^ k) := by
  simp only [productTerm, rawLevelSeries, PowerSeries.coeff_mk, rawSpatialPrefactor]
  rw [show -((α₁ + α₂ - 2) - (α₂ + β - 1 - Q.h) + (k : ℂ)) - 1 =
      (β - Q.h - α₁) - k by ring,
    show -((α₂ + β - 1 - Q.h) - (k : ℂ)) - 1 = (Q.h - β - α₂) + k by ring,
    Complex.cpow_sub _ _ hz₁, Complex.cpow_add _ _ hz₂,
    Complex.cpow_natCast, Complex.cpow_natCast, div_pow]
  ring

/-- The formal monomial coefficient and the normalized spatial coefficient agree. -/
theorem coeff_rawLevelSeries
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    (x : P₁.carrier) (y : P₂.carrier) (α₁ α₂ : ℂ) (n k : ℕ) :
    PowerSeries.coeff k (rawLevelSeries Y₁ Y₂ x y α₁ α₂ (N.h + n)) =
      PowerSeries.coeff n (rawSpatialTrace Y₁ Y₂ x y (-α₁ - α₂)
        (Q.h - N.h - α₂ + k - n)) := by
  simp only [rawLevelSeries, PowerSeries.coeff_mk, coeff_rawSpatialTrace]
  congr 1 <;> ring

theorem rawSpatialPrefactor_ne_zero (Q : LWModule W) (α₁ α₂ β : ℂ)
    {z₁ z₂ : ℂ} (hz₁ : z₁ ≠ 0) (hz₂ : z₂ ≠ 0) :
    rawSpatialPrefactor Q α₁ α₂ β z₁ z₂ ≠ 0 :=
  mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl hz₁))
    (Complex.cpow_ne_zero_iff.mpr (Or.inl hz₂))

/-- Genus-zero convergence supplies absolute convergence of every actual
spatial coefficient series; no genus-one Ward hypothesis occurs. -/
theorem rawLevelSeries_spatialSummable (hV : StronglyRational W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW) (iN : N.IsIrreducibleLW)
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    {α₁ α₂ : ℂ} {x : P₁.carrier} {y : P₂.carrier}
    (hx : x ∈ P₁.isMod.weight α₁) (hy : y ∈ P₂.isMod.weight α₂)
    (β : ℂ) {z₁ z₂ : ℂ} (hz₂ : z₂ ≠ 0) (hz : ‖z₂‖ < ‖z₁‖) :
    SpatialSummable (z₂ / z₁) (rawLevelSeries Y₁ Y₂ x y α₁ α₂ β) := by
  have hz₁ : z₁ ≠ 0 := norm_pos_iff.mp ((norm_nonneg _).trans_lt hz)
  have hc := rawSpatialPrefactor_ne_zero Q α₁ α₂ β hz₁ hz₂
  have hs := (summable_productTerm hV i₁ i₂ iN Y₁ Y₂ hx hy β hz₂ hz).norm
  have ht := hs.mul_left ‖(rawSpatialPrefactor Q α₁ α₂ β z₁ z₂)⁻¹‖
  apply ht.congr
  intro k
  rw [productTerm_eq_spatialTerm Y₁ Y₂ x y α₁ α₂ β hz₁ hz₂,
    ← norm_mul, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]

/-- Evaluation of the actual series is exactly the existing spatial trace. -/
theorem productCoeff_eq_spatialEval (hV : StronglyRational W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW) (iN : N.IsIrreducibleLW)
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    {α₁ α₂ : ℂ} {x : P₁.carrier} {y : P₂.carrier}
    (hx : x ∈ P₁.isMod.weight α₁) (hy : y ∈ P₂.isMod.weight α₂)
    (β : ℂ) {z₁ z₂ : ℂ} (hz₂ : z₂ ≠ 0) (hz : ‖z₂‖ < ‖z₁‖) :
    productCoeff Y₁ Y₂ x y α₁ α₂ β z₁ z₂ =
      rawSpatialPrefactor Q α₁ α₂ β z₁ z₂ * spatialEval (z₂ / z₁)
        ⟨rawLevelSeries Y₁ Y₂ x y α₁ α₂ β,
          rawLevelSeries_spatialSummable hV i₁ i₂ iN Y₁ Y₂ hx hy β hz₂ hz⟩ := by
  have hz₁ : z₁ ≠ 0 := norm_pos_iff.mp ((norm_nonneg _).trans_lt hz)
  simp only [productCoeff, productTerm_eq_spatialTerm Y₁ Y₂ x y α₁ α₂ β hz₁ hz₂,
    tsum_mul_left]
  rfl

/-- Spatial specialization at every q coefficient, valid also at rho=z₂/z₁. -/
theorem coeff_productCuspSeries_spatialEval (hV : StronglyRational W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW) (iN : N.IsIrreducibleLW)
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    {α₁ α₂ : ℂ} {x : P₁.carrier} {y : P₂.carrier}
    (hx : x ∈ P₁.isMod.weight α₁) (hy : y ∈ P₂.isMod.weight α₂)
    {z₁ z₂ : ℂ} (hz₂ : z₂ ≠ 0) (hz : ‖z₂‖ < ‖z₁‖) (rho : ℂ) (n : ℕ) :
    PowerSeries.coeff n (productCuspSeries hV i₁ i₂ iN Y₁ Y₂ hz₂ hz rho x y) =
      rho ^ n * (rawSpatialPrefactor Q α₁ α₂ (N.h + n) z₁ z₂ * spatialEval (z₂ / z₁)
        ⟨rawLevelSeries Y₁ Y₂ x y α₁ α₂ (N.h + n),
          rawLevelSeries_spatialSummable hV i₁ i₂ iN Y₁ Y₂ hx hy (N.h + n) hz₂ hz⟩) := by
  rw [coeff_productCuspSeries hV i₁ i₂ iN Y₁ Y₂ hx hy,
    productCoeff_eq_spatialEval hV i₁ i₂ iN Y₁ Y₂ hx hy (N.h + n) hz₂ hz]

/-- Integer grade shifts create exactly the Laurent factor t⁻ⁿ, with no
complex-power multiplication across different bases. -/
theorem rawSpatialPrefactor_add_nat (Q : LWModule W) (α₁ α₂ β : ℂ)
    {z₁ z₂ : ℂ} (hz₁ : z₁ ≠ 0) (hz₂ : z₂ ≠ 0) (n : ℕ) :
    rawSpatialPrefactor Q α₁ α₂ (β + n) z₁ z₂ =
      rawSpatialPrefactor Q α₁ α₂ β z₁ z₂ * ((z₂ / z₁)⁻¹) ^ n := by
  unfold rawSpatialPrefactor
  rw [show β + (n : ℂ) - Q.h - α₁ = (β - Q.h - α₁) + n by ring,
    show Q.h - (β + (n : ℂ)) - α₂ = (Q.h - β - α₂) - n by ring,
    Complex.cpow_add _ _ hz₁, Complex.cpow_sub _ _ hz₂,
    Complex.cpow_natCast, Complex.cpow_natCast, inv_div, div_pow]
  ring

/-- The actual homogeneous raw trace, with its common nonintegral prefactor
removed, as a q-power series of convergent Laurent expressions in t.
The coefficient's negative spatial order is allowed to grow with n. -/
def rawLaurentQTrace (hV : StronglyRational W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW) (iN : N.IsIrreducibleLW)
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    {α₁ α₂ : ℂ} {x : P₁.carrier} {y : P₂.carrier}
    (hx : x ∈ P₁.isMod.weight α₁) (hy : y ∈ P₂.isMod.weight α₂)
    {z₁ z₂ : ℂ} (hz₂ : z₂ ≠ 0) (hz : ‖z₂‖ < ‖z₁‖) (rho : ℂ) :
    PowerSeries (SpatialLaurent (z₂ / z₁)) :=
  PowerSeries.mk fun n =>
    algebraMap (spatialConvergent (z₂ / z₁)) (SpatialLaurent (z₂ / z₁))
      (algebraMap ℂ (spatialConvergent (z₂ / z₁)) (rho ^ n)) *
    (IsLocalization.Away.invSelf (S := SpatialLaurent (z₂ / z₁)) (spatialX (z₂ / z₁))) ^ n *
    algebraMap (spatialConvergent (z₂ / z₁)) (SpatialLaurent (z₂ / z₁))
      ⟨rawLevelSeries Y₁ Y₂ x y α₁ α₂ (N.h + n),
        rawLevelSeries_spatialSummable hV i₁ i₂ iN Y₁ Y₂ hx hy (N.h + n) hz₂ hz⟩

/-- Full formal-q evaluation bridge for an actual homogeneous product trace.
This does not assume, or assert, summability of the outer q-series. -/
theorem productCuspSeries_eq_laurentQEval (hV : StronglyRational W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW) (iN : N.IsIrreducibleLW)
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    {α₁ α₂ : ℂ} {x : P₁.carrier} {y : P₂.carrier}
    (hx : x ∈ P₁.isMod.weight α₁) (hy : y ∈ P₂.isMod.weight α₂)
    {z₁ z₂ : ℂ} (hz₁ : z₁ ≠ 0) (hz₂ : z₂ ≠ 0) (hz : ‖z₂‖ < ‖z₁‖) (rho : ℂ) :
    productCuspSeries hV i₁ i₂ iN Y₁ Y₂ hz₂ hz rho x y =
      rawSpatialPrefactor Q α₁ α₂ N.h z₁ z₂ •
        spatialLaurentQEval (div_ne_zero hz₂ hz₁)
          (rawLaurentQTrace hV i₁ i₂ iN Y₁ Y₂ hx hy hz₂ hz rho) := by
  ext n
  rw [coeff_productCuspSeries_spatialEval hV i₁ i₂ iN Y₁ Y₂ hx hy,
    rawSpatialPrefactor_add_nat Q α₁ α₂ N.h hz₁ hz₂]
  simp only [PowerSeries.coeff_smul, spatialLaurentQEval, PowerSeries.coeff_map,
    rawLaurentQTrace, PowerSeries.coeff_mk, map_mul, map_pow, spatialLaurentEval_of,
    AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply,
    spatialLaurentEval_invX, smul_eq_mul]
  ring

end VOA.Huang.GenusTwoPoint.Separate
