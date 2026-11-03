/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Commutative.P3ResidualConeBridge

/-!
# The precise quadratic-cone carrier interface at `p = 3`

The conductor argument produces a pair of residual polynomials in two different source rings.
Their typed diagonal restrictions agree.  To turn that fact into the published Hilbert bound one
still needs a representation theorem identifying the appropriate finite, separately symmetric,
fixed-degree window of such pairs with the quadratic-Veronese carrier of Dumanski--Feigin.

This file isolates the remaining inputs; the final bound `finrank_le_expectedDim` takes three
(`D`, `I`, `H` below).  A `P3ResidualWindow` records the two finite graded windows.  Its
`compatibleResidualSpace` is the honest kernel of the typed diagonal difference,
not the range of a desired coefficient map.  `P3QuadraticConeCarrierIdentification` states the
functional-model identification with the cone carrier, while
`DumanskiFeiginP3GradedDimensionHypothesis` states only the external fixed-piece dimension input.

The remaining results are internal.  A linear residualization with the two explicit conductor
factorizations maps injectively to the compatible residual space, hence to the carrier, and yields
the required coefficient-space dimension bound, given three hypotheses: a
`P3LinearResidualization` (whose window-membership fields are model-specific; `ofDivisibility`
reduces it to pointwise conductor divisibility plus membership), the identification
`P3QuadraticConeCarrierIdentification`, and `DumanskiFeiginP3GradedDimensionHypothesis`.  None of
the three is asserted here.
-/

namespace VOA.P3ConeCarrierInterface

open VOA.BoundaryTypedSubstitution
open VOA.P3RestrictedDualCommonFactor
open VOA.P3ResidualConeBridge

noncomputable section

universe u v

variable {K : Type u} [Field K]

/-- A pair of linear windows in the two residual polynomial rings.  In the application these are
the separately symmetric, fixed particle-number and fixed derivative-degree pieces. -/
structure P3ResidualWindow (a b c d : ℕ) where
  xz : Submodule K (MvPolynomial (XZLabel a b c d) K)
  yy : Submodule K (MvPolynomial (YYLabel a b c d) K)

namespace P3ResidualWindow

variable {a b c d : ℕ} (W : P3ResidualWindow (K := K) a b c d)

/-- Typed diagonal difference on a prescribed pair of residual windows. -/
def diagonalDifference :
    W.xz × W.yy →ₗ[K] MvPolynomial (BoundaryDiagonalLabel a b c d) K where
  toFun q :=
    xzDiagonalSubstitution (K := K) a b c d q.1.1 -
      yyDiagonalSubstitution (K := K) a b c d q.2.1
  map_add' q r := by
    simp
    abel
  map_smul' k q := by
    simp [smul_sub]

/-- The finite-window restricted dual of the quadratic relation, expressed as the kernel of the
typed `XZ-YY` diagonal difference. -/
def compatibleResidualSpace : Submodule K (W.xz × W.yy) :=
  LinearMap.ker W.diagonalDifference

/-- Construct a compatible residual from window membership and literal typed compatibility. -/
def compatibleResidualMk
    (qXZ : MvPolynomial (XZLabel a b c d) K)
    (qYY : MvPolynomial (YYLabel a b c d) K)
    (hXZ : qXZ ∈ W.xz) (hYY : qYY ∈ W.yy)
    (hcompat : xzDiagonalSubstitution (K := K) a b c d qXZ =
      yyDiagonalSubstitution (K := K) a b c d qYY) :
    W.compatibleResidualSpace :=
  ⟨(⟨qXZ, hXZ⟩, ⟨qYY, hYY⟩), by
    simp [compatibleResidualSpace, diagonalDifference, hcompat]⟩

@[simp] theorem compatibleResidualMk_xz
    (qXZ : MvPolynomial (XZLabel a b c d) K)
    (qYY : MvPolynomial (YYLabel a b c d) K)
    (hXZ : qXZ ∈ W.xz) (hYY : qYY ∈ W.yy)
    (hcompat : xzDiagonalSubstitution (K := K) a b c d qXZ =
      yyDiagonalSubstitution (K := K) a b c d qYY) :
    (W.compatibleResidualMk qXZ qYY hXZ hYY hcompat).1.1.1 = qXZ := rfl

@[simp] theorem compatibleResidualMk_yy
    (qXZ : MvPolynomial (XZLabel a b c d) K)
    (qYY : MvPolynomial (YYLabel a b c d) K)
    (hXZ : qXZ ∈ W.xz) (hYY : qYY ∈ W.yy)
    (hcompat : xzDiagonalSubstitution (K := K) a b c d qXZ =
      yyDiagonalSubstitution (K := K) a b c d qYY) :
    (W.compatibleResidualMk qXZ qYY hXZ hYY hcompat).1.2.1 = qYY := rfl

end P3ResidualWindow

/-- The exact functional-model identification still required after conductor cancellation: the
finite compatible residual window is the matching quadratic-Veronese cone carrier piece.

This statement is logically separate from the Dumanski--Feigin freeness/dimension theorem. -/
structure P3QuadraticConeCarrierIdentification
    {a b c d : ℕ} (W : P3ResidualWindow (K := K) a b c d)
    (Carrier : Type v) [AddCommGroup Carrier] [Module K Carrier] where
  residualEquiv : W.compatibleResidualSpace ≃ₗ[K] Carrier

/-- The precise external Dumanski--Feigin input for one fixed graded carrier piece.  Their
finite-freeness theorem and graded-rank formula supply this statement on paper. -/
structure DumanskiFeiginP3GradedDimensionHypothesis
    (Carrier : Type v) [AddCommGroup Carrier] [Module K Carrier]
    (expectedDim : ℕ) where
  finite_carrier : FiniteDimensional K Carrier
  finrank_eq_expected : Module.finrank K Carrier = expectedDim

namespace P3QuadraticConeCarrierIdentification

variable {a b c d : ℕ} {W : P3ResidualWindow (K := K) a b c d}
variable {Carrier : Type v} [AddCommGroup Carrier] [Module K Carrier]
variable {expectedDim : ℕ}

/-- The functional-model identification and external dimension theorem together compute the
dimension of the compatible residual window. -/
theorem compatibleResidualSpace_finrank_eq
    (I : P3QuadraticConeCarrierIdentification W Carrier)
    (H : DumanskiFeiginP3GradedDimensionHypothesis (K := K) Carrier expectedDim) :
    Module.finrank K W.compatibleResidualSpace = expectedDim := by
  letI : FiniteDimensional K Carrier := H.finite_carrier
  rw [LinearEquiv.finrank_eq I.residualEquiv, H.finrank_eq_expected]

end P3QuadraticConeCarrierIdentification

namespace FixedPolynomialFactor

variable {I : Type*}

/-- Multiplication by one fixed polynomial, regarded as a linear endomorphism. -/
def multiplication (C : MvPolynomial I K) :
    MvPolynomial I K →ₗ[K] MvPolynomial I K where
  toFun q := C * q
  map_add' q r := by simp [mul_add]
  map_smul' k q := by simp

@[simp] theorem multiplication_apply (C q : MvPolynomial I K) :
    multiplication (K := K) C q = C * q := rfl

/-- Multiplication by a nonzero polynomial is injective. -/
theorem multiplication_injective {C : MvPolynomial I K} (hC : C ≠ 0) :
    Function.Injective (multiplication (K := K) C) := by
  intro q r h
  exact mul_left_cancel₀ hC h

/-- Linear division on the range of multiplication by a fixed nonzero polynomial. -/
def divideRange (C : MvPolynomial I K) (hC : C ≠ 0) :
    LinearMap.range (multiplication (K := K) C) →ₗ[K] MvPolynomial I K :=
  (LinearEquiv.ofInjective
    (multiplication (K := K) C) (multiplication_injective hC)).symm.toLinearMap

/-- Multiplying the range quotient restores the original polynomial. -/
theorem multiplication_divideRange (C : MvPolynomial I K) (hC : C ≠ 0)
    (p : LinearMap.range (multiplication (K := K) C)) :
    C * divideRange C hC p = p.1 := by
  have h := (LinearEquiv.ofInjective
    (multiplication (K := K) C) (multiplication_injective hC)).apply_symm_apply p
  exact congrArg Subtype.val h

/-- A linear polynomial family whose values are all divisible by `C`, with codomain restricted to
the multiplication range. -/
def codRestrictToMultiplicationRange
    {E : Type*} [AddCommGroup E] [Module K E]
    (C : MvPolynomial I K) (f : E →ₗ[K] MvPolynomial I K)
    (hdiv : ∀ e, C ∣ f e) :
    E →ₗ[K] LinearMap.range (multiplication (K := K) C) :=
  f.codRestrict (LinearMap.range (multiplication (K := K) C)) (fun e ↦ by
    rcases hdiv e with ⟨q, hq⟩
    exact ⟨q, by simpa using hq.symm⟩)

/-- Canonical linear residualization of a pointwise divisible linear polynomial family. -/
def residualOfDivisibility
    {E : Type*} [AddCommGroup E] [Module K E]
    (C : MvPolynomial I K) (hC : C ≠ 0)
    (f : E →ₗ[K] MvPolynomial I K) (hdiv : ∀ e, C ∣ f e) :
    E →ₗ[K] MvPolynomial I K :=
  (divideRange C hC).comp (codRestrictToMultiplicationRange C f hdiv)

/-- The canonical residual map has the required factorization. -/
theorem factor_residualOfDivisibility
    {E : Type*} [AddCommGroup E] [Module K E]
    (C : MvPolynomial I K) (hC : C ≠ 0)
    (f : E →ₗ[K] MvPolynomial I K) (hdiv : ∀ e, C ∣ f e) (e : E) :
    f e = C * residualOfDivisibility C hC f hdiv e := by
  symm
  exact multiplication_divideRange C hC
    (codRestrictToMultiplicationRange C f hdiv e)

end FixedPolynomialFactor

/-- Internal data needed to divide a finite coefficient model by the two sector conductors.

The residual maps are required to be linear.  Their displayed factorizations are exactly what
one obtains by restricting multiplication by a fixed nonzero conductor to its range.  Keeping
linearity explicit prevents a pointwise choice of quotients from being used in a Hilbert bound. -/
structure P3LinearResidualization
    {a b c d : ℕ} (W : P3ResidualWindow (K := K) a b c d)
    (E : Type v) [AddCommGroup E] [Module K E] where
  fullXZ : E →ₗ[K] MvPolynomial (XZLabel a b c d) K
  fullYY : E →ₗ[K] MvPolynomial (YYLabel a b c d) K
  residualXZ : E →ₗ[K] MvPolynomial (XZLabel a b c d) K
  residualYY : E →ₗ[K] MvPolynomial (YYLabel a b c d) K
  factorXZ : ∀ e, fullXZ e =
    p3CommonFactor (K := K) (a + 1) b (c + 1) d * residualXZ e
  factorYY : ∀ e, fullYY e =
    p3CommonFactor (K := K) a (b + 2) c d * residualYY e
  full_compatible : ∀ e,
    IsPolarizedDiagonalCompatible (K := K) a b c d (fullXZ e, fullYY e)
  residualXZ_mem : ∀ e, residualXZ e ∈ W.xz
  residualYY_mem : ∀ e, residualYY e ∈ W.yy
  full_pair_injective : Function.Injective (fun e ↦ (fullXZ e, fullYY e))

namespace P3LinearResidualization

variable {a b c d : ℕ} {W : P3ResidualWindow (K := K) a b c d}
variable {E : Type v} [AddCommGroup E] [Module K E]

/-- Build a linear residualization directly from pointwise conductor divisibility.  The only
remaining model-specific algebraic input is that the canonical quotients lie in the two chosen
finite windows. -/
def ofDivisibility
    (fullXZ : E →ₗ[K] MvPolynomial (XZLabel a b c d) K)
    (fullYY : E →ₗ[K] MvPolynomial (YYLabel a b c d) K)
    (hdivXZ : ∀ e,
      p3CommonFactor (K := K) (a + 1) b (c + 1) d ∣ fullXZ e)
    (hdivYY : ∀ e,
      p3CommonFactor (K := K) a (b + 2) c d ∣ fullYY e)
    (hcompatible : ∀ e,
      IsPolarizedDiagonalCompatible (K := K) a b c d (fullXZ e, fullYY e))
    (hmemXZ : ∀ e,
      FixedPolynomialFactor.residualOfDivisibility
          (p3CommonFactor (K := K) (a + 1) b (c + 1) d)
          (p3CommonFactor_ne_zero (K := K) (a + 1) b (c + 1) d)
          fullXZ hdivXZ e ∈ W.xz)
    (hmemYY : ∀ e,
      FixedPolynomialFactor.residualOfDivisibility
          (p3CommonFactor (K := K) a (b + 2) c d)
          (p3CommonFactor_ne_zero (K := K) a (b + 2) c d)
          fullYY hdivYY e ∈ W.yy)
    (hinjective : Function.Injective (fun e ↦ (fullXZ e, fullYY e))) :
    P3LinearResidualization W E where
  fullXZ := fullXZ
  fullYY := fullYY
  residualXZ := FixedPolynomialFactor.residualOfDivisibility
    (p3CommonFactor (K := K) (a + 1) b (c + 1) d)
    (p3CommonFactor_ne_zero (K := K) (a + 1) b (c + 1) d) fullXZ hdivXZ
  residualYY := FixedPolynomialFactor.residualOfDivisibility
    (p3CommonFactor (K := K) a (b + 2) c d)
    (p3CommonFactor_ne_zero (K := K) a (b + 2) c d) fullYY hdivYY
  factorXZ := FixedPolynomialFactor.factor_residualOfDivisibility _ _ _ _
  factorYY := FixedPolynomialFactor.factor_residualOfDivisibility _ _ _ _
  full_compatible := hcompatible
  residualXZ_mem := hmemXZ
  residualYY_mem := hmemYY
  full_pair_injective := hinjective

/-- Cancellation of the common target conductor makes every residualized coefficient vector a
member of the compatible residual space. -/
theorem residual_compatible (D : P3LinearResidualization W E) (e : E) :
    xzDiagonalSubstitution (K := K) a b c d (D.residualXZ e) =
      yyDiagonalSubstitution (K := K) a b c d (D.residualYY e) := by
  exact (polarized_compatibility_iff_residual_diagonal_compatibility
    a b c d (D.fullXZ e) (D.residualXZ e) (D.fullYY e) (D.residualYY e)
      (D.factorXZ e) (D.factorYY e)).mp (D.full_compatible e)

/-- The residualization map into the honest quadratic-cone equalizer. -/
def toCompatibleResidual (D : P3LinearResidualization W E) :
    E →ₗ[K] W.compatibleResidualSpace where
  toFun e := W.compatibleResidualMk
    (D.residualXZ e) (D.residualYY e)
    (D.residualXZ_mem e) (D.residualYY_mem e) (D.residual_compatible e)
  map_add' e f := by
    apply Subtype.ext
    apply Prod.ext <;> apply Subtype.ext <;> simp
  map_smul' k e := by
    apply Subtype.ext
    apply Prod.ext <;> apply Subtype.ext <;> simp

@[simp] theorem toCompatibleResidual_xz
    (D : P3LinearResidualization W E) (e : E) :
    (D.toCompatibleResidual e).1.1.1 = D.residualXZ e := rfl

@[simp] theorem toCompatibleResidual_yy
    (D : P3LinearResidualization W E) (e : E) :
    (D.toCompatibleResidual e).1.2.1 = D.residualYY e := rfl

/-- Injectivity survives conductor division: equality of residuals restores equality of the full
polynomial pair, where the original realization is injective. -/
theorem toCompatibleResidual_injective (D : P3LinearResidualization W E) :
    Function.Injective D.toCompatibleResidual := by
  intro e f hef
  apply D.full_pair_injective
  have hx : D.residualXZ e = D.residualXZ f := by
    have h := congrArg (fun q : W.compatibleResidualSpace ↦ q.1.1.1) hef
    simpa using h
  have hy : D.residualYY e = D.residualYY f := by
    have h := congrArg (fun q : W.compatibleResidualSpace ↦ q.1.2.1) hef
    simpa using h
  apply Prod.ext
  · change D.fullXZ e = D.fullXZ f
    rw [D.factorXZ e, D.factorXZ f, hx]
  · change D.fullYY e = D.fullYY f
    rw [D.factorYY e, D.factorYY f, hy]

/-- Compose the internal residualization with the externally identified quadratic-Veronese
carrier. -/
def toDumanskiFeiginCarrier
    {Carrier : Type*} [AddCommGroup Carrier] [Module K Carrier]
    (D : P3LinearResidualization W E)
    (I : P3QuadraticConeCarrierIdentification W Carrier) :
    E →ₗ[K] Carrier :=
  I.residualEquiv.toLinearMap.comp D.toCompatibleResidual

theorem toDumanskiFeiginCarrier_injective
    {Carrier : Type*} [AddCommGroup Carrier] [Module K Carrier]
    (D : P3LinearResidualization W E)
    (I : P3QuadraticConeCarrierIdentification W Carrier) :
    Function.Injective (D.toDumanskiFeiginCarrier I) :=
  I.residualEquiv.injective.comp D.toCompatibleResidual_injective

/-- The fixed-graded coefficient-space Hilbert bound, from three hypotheses: the linear
residualization `D`, and the two named structures `I` and `H`, which expose separately the
remaining functional-model identification and the external representation-theoretic input. -/
theorem finrank_le_expectedDim
    {Carrier : Type*} [AddCommGroup Carrier] [Module K Carrier]
    {expectedDim : ℕ}
    (D : P3LinearResidualization W E)
    (I : P3QuadraticConeCarrierIdentification W Carrier)
    (H : DumanskiFeiginP3GradedDimensionHypothesis (K := K) Carrier expectedDim) :
    Module.finrank K E ≤ expectedDim := by
  letI : FiniteDimensional K Carrier := H.finite_carrier
  calc
    Module.finrank K E ≤ Module.finrank K Carrier :=
      LinearMap.finrank_le_finrank_of_injective
        (D.toDumanskiFeiginCarrier_injective I)
    _ = expectedDim := H.finrank_eq_expected

end P3LinearResidualization

end

end VOA.P3ConeCarrierInterface
