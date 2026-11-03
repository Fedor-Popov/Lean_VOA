import VOA.Huang.GenusTwoPointSewing
import VOA.Huang.GenusTwoPointSepHuangU
import VOA.Huang.GenusTwoPointModifiedTrace
import VOA.Huang.PzTensorY4

/-!
# Actual two-point traces as formal q-series with evaluated spatial coefficients

Every q coefficient is the convergent genus-zero intermediate-level sum.
Weight decomposition extends these coefficients bilinearly to arbitrary
insertions. The outer q-series is formal throughout this construction.
The parameter rho rescales q so that a local coefficient disc can be used.
-/
noncomputable section
namespace VOA.Huang.GenusTwoPoint.Separate
open VOA
open scoped BigOperators

/-- Pointwise summation of scalar bilinear maps when every scalar series converges. -/
def bilinearTsum {E F : Type*} [AddCommGroup E] [Module ℂ E]
    [AddCommGroup F] [Module ℂ F] (f : ℕ → E →ₗ[ℂ] F →ₗ[ℂ] ℂ)
    (hf : ∀ x y, Summable (fun k => f k x y)) : E →ₗ[ℂ] F →ₗ[ℂ] ℂ where
  toFun x :=
    { toFun := fun y => ∑' k, f k x y
      map_add' := fun y z => by
        simp only [map_add]
        exact (hf x y).tsum_add (hf x z)
      map_smul' := fun c y => by
        simp only [map_smul, RingHom.id_apply]
        simpa only [smul_eq_mul] using tsum_mul_left }
  map_add' := by
    intro x y
    ext z
    simp only [map_add, LinearMap.add_apply]
    exact (hf x z).tsum_add (hf y z)
  map_smul' := by
    intro c x
    ext y
    simp only [map_smul, LinearMap.smul_apply, RingHom.id_apply]
    simpa only [smul_eq_mul] using tsum_mul_left

/-- Coefficientwise assembly involves no q convergence assumption. -/
def bilinearSeries {E F : Type*} [AddCommGroup E] [Module ℂ E]
    [AddCommGroup F] [Module ℂ F] (f : ℕ → E →ₗ[ℂ] F →ₗ[ℂ] ℂ) :
    E →ₗ[ℂ] F →ₗ[ℂ] PowerSeries ℂ where
  toFun x :=
    { toFun := fun y => PowerSeries.mk (fun n => f n x y)
      map_add' := fun y z => by ext n; simp
      map_smul' := fun c y => by ext n; simp }
  map_add' := by intro x y; ext z n; simp
  map_smul' := by intro c x; ext y n; simp

@[simp] theorem coeff_bilinearSeries {E F : Type*} [AddCommGroup E] [Module ℂ E]
    [AddCommGroup F] [Module ℂ F] (f : ℕ → E →ₗ[ℂ] F →ₗ[ℂ] ℂ)
    (x : E) (y : F) (n : ℕ) :
    PowerSeries.coeff n (bilinearSeries f x y) = f n x y := by simp [bilinearSeries]

universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  {P₁ P₂ N Q : LWModule W}

/-- A homogeneous spatial summand as a bilinear map on the two weight spaces. -/
def productWeightTermPair
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    (α₁ α₂ β z₁ z₂ : ℂ) (k : ℕ) :
    P₁.isMod.weight α₁ →ₗ[ℂ] P₂.isMod.weight α₂ →ₗ[ℂ] ℂ :=
  let n₁ := (α₁ + α₂ - 2) - (α₂ + β - 1 - Q.h) + k
  let n₂ := (α₂ + β - 1 - Q.h) - k
  (z₁ ^ (-n₁ - 1) * z₂ ^ (-n₂ - 1)) •
    ((productTracePair Y₁ Y₂ n₁ n₂ (β - W.centralCharge / 24)).comp
      (P₁.isMod.weight α₁).subtype).compl₂ (P₂.isMod.weight α₂).subtype

theorem productWeightTermPair_apply
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    (α₁ α₂ β z₁ z₂ : ℂ) (k : ℕ)
    (x : P₁.isMod.weight α₁) (y : P₂.isMod.weight α₂) :
    productWeightTermPair Y₁ Y₂ α₁ α₂ β z₁ z₂ k x y =
      productTerm Y₁ Y₂ x.val y.val α₁ α₂ β z₁ z₂ k := by
  dsimp [productWeightTermPair, productTracePair, productTerm]
  ring

/-- The actual genus-zero-summed coefficient, extended using finite weight
support. Only the inner spatial sums have been evaluated. -/
def productCoeffPair (hV : StronglyRational W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW) (iN : N.IsIrreducibleLW)
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    (β : ℂ) {z₁ z₂ : ℂ} (hz₂ : z₂ ≠ 0) (hz : ‖z₂‖ < ‖z₁‖) :
    P₁.carrier →ₗ[ℂ] P₂.carrier →ₗ[ℂ] ℂ :=
  PzTensorY4.biHat fun α₁ α₂ => bilinearTsum
    (productWeightTermPair Y₁ Y₂ α₁ α₂ β z₁ z₂)
    (fun x y => (summable_productTerm hV i₁ i₂ iN Y₁ Y₂ x.property y.property
      β hz₂ hz).congr (fun k => (productWeightTermPair_apply _ _ _ _ _ _ _ k x y).symm))

/-- No arbitrary scalar series has been substituted for the actual trace. -/
theorem productCoeffPair_of_mem (hV : StronglyRational W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW) (iN : N.IsIrreducibleLW)
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    {α₁ α₂ : ℂ} {x : P₁.carrier} {y : P₂.carrier}
    (hx : x ∈ P₁.isMod.weight α₁) (hy : y ∈ P₂.isMod.weight α₂)
    (β : ℂ) {z₁ z₂ : ℂ} (hz₂ : z₂ ≠ 0) (hz : ‖z₂‖ < ‖z₁‖) :
    productCoeffPair hV i₁ i₂ iN Y₁ Y₂ β hz₂ hz x y =
      productCoeff Y₁ Y₂ x y α₁ α₂ β z₁ z₂ := by
  rw [productCoeffPair, PzTensorY4.biHat_homog _ hx hy]
  change (∑' k, productWeightTermPair Y₁ Y₂ α₁ α₂ β z₁ z₂ k ⟨x, hx⟩ ⟨y, hy⟩) = _
  simp only [productWeightTermPair_apply, productCoeff]

/-- Formal series in q/rho, with coefficients equal to rho^n times the
convergent spatial traces. The conformal power is handled by thetaShift. -/
def productCuspSeries (hV : StronglyRational W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW) (iN : N.IsIrreducibleLW)
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    {z₁ z₂ : ℂ} (hz₂ : z₂ ≠ 0) (hz : ‖z₂‖ < ‖z₁‖) (rho : ℂ) :
    P₁.carrier →ₗ[ℂ] P₂.carrier →ₗ[ℂ] PowerSeries ℂ :=
  bilinearSeries fun n => rho ^ n • productCoeffPair hV i₁ i₂ iN Y₁ Y₂ (N.h + n) hz₂ hz

theorem coeff_productCuspSeries (hV : StronglyRational W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW) (iN : N.IsIrreducibleLW)
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    {α₁ α₂ : ℂ} {x : P₁.carrier} {y : P₂.carrier}
    (hx : x ∈ P₁.isMod.weight α₁) (hy : y ∈ P₂.isMod.weight α₂)
    {z₁ z₂ : ℂ} (hz₂ : z₂ ≠ 0) (hz : ‖z₂‖ < ‖z₁‖) (rho : ℂ) (n : ℕ) :
    PowerSeries.coeff n (productCuspSeries hV i₁ i₂ iN Y₁ Y₂ hz₂ hz rho x y) =
      rho ^ n * productCoeff Y₁ Y₂ x y α₁ α₂ (N.h + n) z₁ z₂ := by
  simp only [productCuspSeries, coeff_bilinearSeries, LinearMap.smul_apply, smul_eq_mul,
    productCoeffPair_of_mem hV i₁ i₂ iN Y₁ Y₂ hx hy]

/-- Geometric modification is applied to actual insertion vectors. It is
invertible and finite on every vector; no completed module is introduced. -/
def modifiedProductCuspSeries (hV : StronglyRational W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW) (iN : N.IsIrreducibleLW)
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    {z₁ z₂ : ℂ} (hz₂ : z₂ ≠ 0) (hz : ‖z₂‖ < ‖z₁‖) (rho : ℂ) :
    P₁.carrier →ₗ[ℂ] P₂.carrier →ₗ[ℂ] PowerSeries ℂ :=
  ((productCuspSeries hV i₁ i₂ iN Y₁ Y₂ hz₂ hz rho).comp
    (huangU P₁ (Complex.log z₁)).toLinearMap).compl₂
      (huangU P₂ (Complex.log z₂)).toLinearMap

theorem modifiedProductCuspSeries_inverse (hV : StronglyRational W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW) (iN : N.IsIrreducibleLW)
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    {z₁ z₂ : ℂ} (hz₂ : z₂ ≠ 0) (hz : ‖z₂‖ < ‖z₁‖) (rho : ℂ)
    (x : P₁.carrier) (y : P₂.carrier) :
    modifiedProductCuspSeries hV i₁ i₂ iN Y₁ Y₂ hz₂ hz rho
      ((huangU P₁ (Complex.log z₁)).symm x) ((huangU P₂ (Complex.log z₂)).symm y) =
      productCuspSeries hV i₁ i₂ iN Y₁ Y₂ hz₂ hz rho x y := by
  simp [modifiedProductCuspSeries]

end VOA.Huang.GenusTwoPoint.Separate
