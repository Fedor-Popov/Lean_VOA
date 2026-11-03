import VOA.Huang.VerlindeRhoCoefficients
import VOA.Huang.VerlindeRhoPairing

/-!
# The central modular matrix is charge conjugation

Square-bracket reflection is proved for every VOA, by the ordinary Virasoro
conjugation calculation and a scalar binomial identity. FHL nonvanishing
identifies the labels of any supplied vacuum delta rule. The PBW-relative
theorem has PBW as an explicit hypothesis; the `_pbw` suffix marks the corollary in which the
explicit PBW datum is discharged by the theorem `VOA.pbw`; it
adds no axiom.
-/

namespace VOA.Huang.VerlindeRho

open VOA VOA.Huang.VerlindeEigen VOA.Huang.ZhuModData

universe u w

/-- Coordinate reflection on states, with no niceness assumption. -/
theorem squareBracketReflection (V : Type u) [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) : SquareBracketReflection W :=
  squareBracketReflection_of_binomial reflectionBinomialIdentity

/-- The exact reflection input of the existing rho reduction. -/
theorem squareBracketReflectionInput : SquareBracketReflectionInput.{u} :=
  fun V _ _ W _ => squareBracketReflection V W

/-- The contragredient trace identity at every square-bracket weight. -/
theorem squareBracketTraceParity (V : Type u) [AddCommGroup V] [Module ℂ V]
    (W : VertexOperatorAlgebra V) : SquareBracketTraceParity W :=
  squareBracketTraceParity_of_reflection (squareBracketReflection V W)

/-- The unchanged rho input, with the only remaining project input explicit. -/
theorem rhoNegOneInput (hPBW : ZhuPBWBottomInput.{u}) : RhoNegOneInput.{u, w} :=
  rhoNegOneInput_of_reflection hPBW squareBracketReflectionInput
    contragredientVacuumNonzeroInput

/-- The central modular matrix is charge conjugation, using the project's PBW datum. -/
theorem rhoNegOneInput_pbw : RhoNegOneInput.{u, w} :=
  rhoNegOneInput zhuPBWBottomInput_of_pbw

end VOA.Huang.VerlindeRho
