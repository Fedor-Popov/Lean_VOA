import VOA.Huang.GenusTwoPointSepCoordinateFlow
import VOA.Huang.GenusTwoPointSepQTransport

/-!
# Huang's U with its uniquely determined coefficients

The logarithmic argument t represents x=exp(t). This retains Huang's
(2*pi*i)^L(0) convention, including its specified logarithm. The normalized
coordinate exponential is related to U by an actual operator conjugation.
The vertex/intertwiner coordinate substitution law is a further obligation.
-/
noncomputable section
namespace VOA.Huang.GenusTwoPoint.Separate
open VOA
open scoped BigOperators
universe u

/-- Naturality of the locally finite exponential for an intertwining linear map. -/
theorem expFun_intertwine {M N : Type*} [AddCommGroup M] [Module ℂ M]
    [AddCommGroup N] [Module ℂ N] (f : M →ₗ[ℂ] N)
    {D : Module.End ℂ M} {E : Module.End ℂ N} (hD : IsLocNilp D) (hE : IsLocNilp E)
    (h : ∀ x, f (D x) = E (f x)) (x : M) :
    f (expFun hD x) = expFun hE (f x) := by
  have hp : ∀ n, f ((D ^ n) x) = (E ^ n) (f x) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [VOA.pow_succ'_apply, VOA.pow_succ'_apply, h, ih]
  obtain ⟨n, hn⟩ := hD x
  have he : (E ^ n) (f x) = 0 := by rw [← hp, hn, map_zero]
  rw [expFun_eq_expSum hD hn, expFun_eq_expSum hE he, expSum, expSum, map_sum]
  simp only [map_smul, hp]

variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}

/-- Conjugating the positive Virasoro generator by ordinary weight scaling. -/
theorem moduleCoordGen_scale (P : LWModule W) (a : ℕ → ℂ) (t : ℂ) (x : P.carrier) :
    moduleWeightExp P.isMod t (moduleCoordGen P (scaleGenerator (Complex.exp t) a) x) =
      moduleCoordGen P a (moduleWeightExp P.isMod t x) := by
  refine FusionTop.induction_weight P.isMod x (by simp) ?_ ?_
  · intro x y hx hy
    simp only [map_add, hx, hy]
  · intro α x hx
    rw [moduleWeightExp_of_weight P.isMod t hx, map_smul]
    change moduleWeightExp P.isMod t (∑ᶠ k : ℕ, _) =
      Complex.exp (t * α) • ∑ᶠ k : ℕ, _
    rw [map_finsum _ (moduleCoordGen_support_finite P _ x),
      smul_finsum' _ (moduleCoordGen_support_finite P a x)]
    apply finsum_congr
    intro k
    rw [map_smul, moduleWeightExp_of_weight P.isMod t
      (mode_mem_weight P.isMod W.conformal_mem hx ((k : ℤ) + 2))]
    simp only [scaleGenerator, smul_smul, ← Complex.exp_nat_mul]
    have he : ((k + 1 : ℕ) : ℂ) * t +
        t * (α + (2 : ℤ) - (((k : ℤ) + 2 : ℤ) : ℂ) - 1) = t * α := by
      push_cast
      ring
    rw [mul_right_comm, ← Complex.exp_add, he]

/-- Huang (1.8), for arbitrary coordinate coefficients and logarithmic scale. -/
theorem moduleCoordinateChange_scale (P : LWModule W) (a : ℕ → ℂ) (t : ℂ)
    (x : P.carrier) :
    moduleWeightExp P.isMod t
        (moduleCoordinateChange P (scaleGenerator (Complex.exp t) a) x) =
      moduleCoordinateChange P a (moduleWeightExp P.isMod t x) := by
  apply expFun_intertwine (moduleWeightExp P.isMod t)
    (moduleCoordGen_isLocNilp P _).neg (moduleCoordGen_isLocNilp P a).neg
  intro y
  simpa only [LinearMap.neg_apply, map_neg] using congrArg Neg.neg (moduleCoordGen_scale P a t y)

/-- The chosen logarithm really exponentiates to 2*pi*i. -/
theorem exp_logTwoPiI : Complex.exp logTwoPiI = 2 * (Real.pi : ℂ) * Complex.I := by
  rw [logTwoPiI, Complex.exp_add]
  have hr : Complex.exp (Real.log (2 * Real.pi) : ℂ) = (2 * Real.pi : ℝ) := by
    rw [← Complex.ofReal_exp, Real.exp_log (by positivity)]
  rw [hr]
  have hi : Complex.exp (Complex.I * ((Real.pi : ℂ) / 2)) = Complex.I := by
    rw [mul_comm, Complex.exp_mul_I]
    simp
  rw [hi]
  push_cast
  rfl

/-- Huang U(exp t)=(2*pi*i*exp t)^L(0) exp(-sum A_j L(j)), on its log cover. -/
def huangU (P : LWModule W) (t : ℂ) : P.carrier ≃ₗ[ℂ] P.carrier :=
  coordinateModification P huangA t

/-- The normalized logarithmic coordinate uses B_j, without a free coefficient family. -/
def normalizedCoordinateChange (P : LWModule W) : P.carrier ≃ₗ[ℂ] P.carrier :=
  moduleCoordinateChange P (iterativeLog (logarithmicCoordinate 1))

/-- Exact normalization bridge to Zhu's coordinate exponential. -/
theorem huangU_eq_normalized (P : LWModule W) (t : ℂ) (x : P.carrier) :
    huangU P t x = moduleWeightExp P.isMod t
      (normalizedCoordinateChange P (moduleWeightExp P.isMod logTwoPiI x)) := by
  change moduleWeightExp P.isMod (logTwoPiI + t) (moduleCoordinateChange P huangA x) = _
  rw [add_comm logTwoPiI, moduleWeightExp_add, huangA_scale, ← exp_logTwoPiI,
    moduleCoordinateChange_scale]
  rfl

/-- Huang (1.4), with no principal-power multiplication assumption. -/
theorem huangU_add (P : LWModule W) (s t : ℂ) (x : P.carrier) :
    huangU P (s + t) x = moduleWeightExp P.isMod s (huangU P t x) :=
  coordinateModification_add P huangA s t x

/-- Primary insertions have exactly the expected geometric factor. -/
theorem huangU_of_primary (P : LWModule W) (t : ℂ) {α : ℂ} {x : P.carrier}
    (hx : x ∈ P.isMod.weight α)
    (hp : ∀ k : ℕ, mode (P.isMod.YM W.conformalVector) ((k : ℤ) + 2) x = 0) :
    huangU P t x = Complex.exp ((logTwoPiI + t) * α) • x :=
  coordinateModification_of_primary P huangA t hx hp

end VOA.Huang.GenusTwoPoint.Separate
