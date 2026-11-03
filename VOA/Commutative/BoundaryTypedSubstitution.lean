/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Commutative.MultispeciesParticlePolynomial

/-!
# Typed diagonal substitutions for the boundary auxiliary algebra

The labelled particle rings for the two terms of `Q = X Z - Y^2` do not have the
same variable type: the `XZ` term lives in multidegree `(a+1,b,c+1,d)`, whereas
the `YY` term lives in `(a,b+2,c,d)`.  This file makes that distinction literal.
It maps the two polynomial rings separately to the common collision-coordinate ring

`K[t, x_1,..,x_a, y_1,..,y_b, z_1,..,z_c, s_1,..,s_d]`.

The binary product of the two source rings is the typed direct-sum coordinate space
for the polarized relation.  The maps identify precisely the two active variables,
and preserve every passive spectator variable.  On the coefficient side, slicing a
four-species coefficient family at an arbitrary `S` spectator gives the exact
three-current polarized orthogonality theorem already proved in
`ModeParticlePairing.lean`.

This is an interface theorem only.  It does not prove that the two substituted
polynomials arise from a common carrier, does not turn coefficient diagonal sums into
an all-weight common-factor theorem, and does not assert classical freeness.
-/

namespace VOA.BoundaryTypedSubstitution

open VOA.ModeParticlePairing
open VOA.MultispeciesParticlePolynomial

noncomputable section

universe u

variable {K : Type u} [Field K]

section TypedPolynomialMaps

/-- Labels after one polarized collision: one collision variable together with the passive
four-species labels in multidegree `(a,b,c,d)`. -/
abbrev BoundaryDiagonalLabel (a b c d : ℕ) :=
  Unit ⊕ SpeciesLabel (boundaryMultiplicity a b c d)

/-- The `XZ` source label type. -/
abbrev XZLabel (a b c d : ℕ) :=
  SpeciesLabel (boundaryMultiplicity (a + 1) b (c + 1) d)

/-- The `YY` source label type. -/
abbrev YYLabel (a b c d : ℕ) :=
  SpeciesLabel (boundaryMultiplicity a (b + 2) c d)

/-- Embed a passive label in the `XZ` source.  The extra `X` and `Z` variables occupy the
zeroth slots. -/
def liftXZPassiveLabel (a b c d : ℕ) :
    SpeciesLabel (boundaryMultiplicity a b c d) → XZLabel a b c d
  | ⟨.X, i⟩ => ⟨.X, i.succ⟩
  | ⟨.Y, i⟩ => ⟨.Y, i⟩
  | ⟨.Z, i⟩ => ⟨.Z, i.succ⟩
  | ⟨.S, i⟩ => ⟨.S, i⟩

/-- Embed a passive label in the `YY` source.  The two extra `Y` variables occupy the first
two slots. -/
def liftYYPassiveLabel (a b c d : ℕ) :
    SpeciesLabel (boundaryMultiplicity a b c d) → YYLabel a b c d
  | ⟨.X, i⟩ => ⟨.X, i⟩
  | ⟨.Y, i⟩ => ⟨.Y, i.succ.succ⟩
  | ⟨.Z, i⟩ => ⟨.Z, i⟩
  | ⟨.S, i⟩ => ⟨.S, i⟩

/-- The typed `XZ` collision substitution.  It sends the new `X` and new `Z` labels to the
common collision coordinate and leaves passive labels in their own species. -/
def xzToDiagonalLabel (a b c d : ℕ) : XZLabel a b c d → BoundaryDiagonalLabel a b c d
  | ⟨.X, i⟩ => Fin.cases (Sum.inl ()) (fun j => Sum.inr ⟨.X, j⟩) i
  | ⟨.Y, i⟩ => Sum.inr ⟨.Y, i⟩
  | ⟨.Z, i⟩ => Fin.cases (Sum.inl ()) (fun j => Sum.inr ⟨.Z, j⟩) i
  | ⟨.S, i⟩ => Sum.inr ⟨.S, i⟩

/-- The typed `YY` collision substitution.  It sends both new `Y` labels to the common
collision coordinate and leaves passive labels in their own species. -/
def yyToDiagonalLabel (a b c d : ℕ) : YYLabel a b c d → BoundaryDiagonalLabel a b c d
  | ⟨.X, i⟩ => Sum.inr ⟨.X, i⟩
  | ⟨.Y, i⟩ =>
      Fin.cases (Sum.inl ())
        (fun j => Fin.cases (Sum.inl ()) (fun k => Sum.inr ⟨.Y, k⟩) j) i
  | ⟨.Z, i⟩ => Sum.inr ⟨.Z, i⟩
  | ⟨.S, i⟩ => Sum.inr ⟨.S, i⟩

/-- The newly inserted `X` label in the `XZ` summand. -/
def newXZLabelX (a b c d : ℕ) : XZLabel a b c d :=
  ⟨.X, (0 : Fin (a + 1))⟩

/-- The newly inserted `Z` label in the `XZ` summand. -/
def newXZLabelZ (a b c d : ℕ) : XZLabel a b c d :=
  ⟨.Z, (0 : Fin (c + 1))⟩

/-- The first newly inserted `Y` label in the `YY` summand. -/
def newYYLabelZero (a b c d : ℕ) : YYLabel a b c d :=
  ⟨.Y, (0 : Fin (b + 2))⟩

/-- The second newly inserted `Y` label in the `YY` summand. -/
def newYYLabelOne (a b c d : ℕ) : YYLabel a b c d :=
  ⟨.Y, (1 : Fin (b + 2))⟩

/-- Literal `XZ` diagonal substitution on the appropriate labelled polynomial ring. -/
def xzDiagonalSubstitution (a b c d : ℕ) :
    MvPolynomial (XZLabel a b c d) K →ₐ[K]
      MvPolynomial (BoundaryDiagonalLabel a b c d) K :=
  MvPolynomial.rename (xzToDiagonalLabel a b c d)

/-- Literal `YY` diagonal substitution on its *different* labelled polynomial ring. -/
def yyDiagonalSubstitution (a b c d : ℕ) :
    MvPolynomial (YYLabel a b c d) K →ₐ[K]
      MvPolynomial (BoundaryDiagonalLabel a b c d) K :=
  MvPolynomial.rename (yyToDiagonalLabel a b c d)

/-- The typed binary direct-sum coordinate space for the two multidegrees coupled by `Q`.
The product is the binary direct sum in coordinates; neither summand is coerced into the other. -/
abbrev PolarizedPolynomialSource (a b c d : ℕ) :=
  MvPolynomial (XZLabel a b c d) K × MvPolynomial (YYLabel a b c d) K

/-- Apply the two typed substitutions componentwise to the polarized direct sum. -/
def polarizedDiagonalSubstitution (a b c d : ℕ) :
    PolarizedPolynomialSource (K := K) a b c d →
      MvPolynomial (BoundaryDiagonalLabel a b c d) K ×
        MvPolynomial (BoundaryDiagonalLabel a b c d) K
  | (pXZ, pYY) =>
      (xzDiagonalSubstitution (K := K) a b c d pXZ,
        yyDiagonalSubstitution (K := K) a b c d pYY)

/-- The common-target form of the polarized cone condition. -/
def IsPolarizedDiagonalCompatible (a b c d : ℕ)
    (p : PolarizedPolynomialSource (K := K) a b c d) : Prop :=
  xzDiagonalSubstitution (K := K) a b c d p.1 =
    yyDiagonalSubstitution (K := K) a b c d p.2

/-- Equivalently, the componentwise direct-sum substitution lands on the diagonal of the common
target product. -/
theorem isPolarizedDiagonalCompatible_iff_componentwise_eq (a b c d : ℕ)
    (p : PolarizedPolynomialSource (K := K) a b c d) :
    IsPolarizedDiagonalCompatible (K := K) a b c d p ↔
      (polarizedDiagonalSubstitution (K := K) a b c d p).1 =
        (polarizedDiagonalSubstitution (K := K) a b c d p).2 := by
  rfl

@[simp]
theorem xzToDiagonalLabel_passive (a b c d : ℕ)
    (i : SpeciesLabel (boundaryMultiplicity a b c d)) :
    xzToDiagonalLabel a b c d (liftXZPassiveLabel a b c d i) = Sum.inr i := by
  rcases i with ⟨A, i⟩
  cases A <;> rfl

@[simp]
theorem yyToDiagonalLabel_passive (a b c d : ℕ)
    (i : SpeciesLabel (boundaryMultiplicity a b c d)) :
    yyToDiagonalLabel a b c d (liftYYPassiveLabel a b c d i) = Sum.inr i := by
  rcases i with ⟨A, i⟩
  cases A <;> rfl

@[simp]
theorem xzToDiagonalLabel_newX (a b c d : ℕ) :
    xzToDiagonalLabel a b c d (newXZLabelX a b c d) = Sum.inl () := by
  rfl

@[simp]
theorem xzToDiagonalLabel_newZ (a b c d : ℕ) :
    xzToDiagonalLabel a b c d (newXZLabelZ a b c d) = Sum.inl () := by
  rfl

@[simp]
theorem yyToDiagonalLabel_newY_zero (a b c d : ℕ) :
    yyToDiagonalLabel a b c d (newYYLabelZero a b c d) = Sum.inl () := by
  rfl

@[simp]
theorem yyToDiagonalLabel_newY_one (a b c d : ℕ) :
    yyToDiagonalLabel a b c d (newYYLabelOne a b c d) = Sum.inl () := by
  rfl

/-- The `XZ` substitution preserves every passive spectator variable literally. -/
@[simp]
theorem xzDiagonalSubstitution_X_passive (a b c d : ℕ)
    (i : SpeciesLabel (boundaryMultiplicity a b c d)) :
    xzDiagonalSubstitution (K := K) a b c d (MvPolynomial.X (liftXZPassiveLabel a b c d i)) =
      MvPolynomial.X (Sum.inr i) := by
  simp [xzDiagonalSubstitution]

/-- The `YY` substitution preserves every passive spectator variable literally. -/
@[simp]
theorem yyDiagonalSubstitution_X_passive (a b c d : ℕ)
    (i : SpeciesLabel (boundaryMultiplicity a b c d)) :
    yyDiagonalSubstitution (K := K) a b c d (MvPolynomial.X (liftYYPassiveLabel a b c d i)) =
      MvPolynomial.X (Sum.inr i) := by
  simp [yyDiagonalSubstitution]

/-- The active `X` and `Z` variables have the same literal diagonal image. -/
theorem xzDiagonalSubstitution_active_agree (a b c d : ℕ) :
    xzDiagonalSubstitution (K := K) a b c d (MvPolynomial.X (newXZLabelX a b c d)) =
      xzDiagonalSubstitution (K := K) a b c d (MvPolynomial.X (newXZLabelZ a b c d)) := by
  simp [xzDiagonalSubstitution]

/-- The two active `Y` variables have the same literal diagonal image. -/
theorem yyDiagonalSubstitution_active_agree (a b c d : ℕ) :
    yyDiagonalSubstitution (K := K) a b c d (MvPolynomial.X (newYYLabelZero a b c d)) =
      yyDiagonalSubstitution (K := K) a b c d (MvPolynomial.X (newYYLabelOne a b c d)) := by
  simp [yyDiagonalSubstitution]

end TypedPolynomialMaps

section CoefficientSlices

/-- The two four-species coefficient sectors coupled by `Q`, now retaining `d` passive `S`
particles in both components. -/
abbrev BoundaryPolarizedCoefficientSpace (jetOrder a b c d : ℕ) :=
  MultispeciesJetParticleSpace K jetOrder (boundaryMultiplicity (a + 1) b (c + 1) d) ×
    MultispeciesJetParticleSpace K jetOrder (boundaryMultiplicity a (b + 2) c d)

/-- Slice an `XZ` four-species coefficient family at a fixed passive `S` configuration. -/
def sliceXZAtS {jetOrder a b c d : ℕ}
    (F : MultispeciesJetParticleSpace K jetOrder
      (boundaryMultiplicity (a + 1) b (c + 1) d))
    (s : ModeConfiguration jetOrder d) :
    CurrentCoefficientSpace K jetOrder (a + 1) b (c + 1) :=
  fun q ↦ F fun
    | .X => q.xModes
    | .Y => q.yModes
    | .Z => q.zModes
    | .S => s

/-- Slice a `YY` four-species coefficient family at a fixed passive `S` configuration. -/
def sliceYYAtS {jetOrder a b c d : ℕ}
    (F : MultispeciesJetParticleSpace K jetOrder
      (boundaryMultiplicity a (b + 2) c d))
    (s : ModeConfiguration jetOrder d) :
    CurrentCoefficientSpace K jetOrder a (b + 2) c :=
  fun q ↦ F fun
    | .X => q.xModes
    | .Y => q.yModes
    | .Z => q.zModes
    | .S => s

/-- The active three-current polarized pair obtained after fixing all passive `S` spectators. -/
def slicePolarizedAtS {jetOrder a b c d : ℕ}
    (F : BoundaryPolarizedCoefficientSpace (K := K) jetOrder a b c d)
    (s : ModeConfiguration jetOrder d) :
    PolarizedConeCoefficients K jetOrder a b c :=
  (sliceXZAtS F.1 s, sliceYYAtS F.2 s)

/-- Four-species polarized orthogonality, tested after every choice of passive `S` spectator.
This is deliberately a predicate on the typed direct sum, not a coerced common multidegree. -/
def IsBoundaryPolarizedOrthogonal {jetOrder a b c d : ℕ}
    (F : BoundaryPolarizedCoefficientSpace (K := K) jetOrder a b c d) : Prop :=
  ∀ s q bx byy bz,
    polarizedConePairing
      (polarizedConeRelationMode (K := K) q bx byy bz)
      (slicePolarizedAtS F s) = 0

/-- The corresponding four-species equality of active collision-diagonal coefficient sums. -/
def IsBoundaryPolarizedDiagonalCompatible {jetOrder a b c d : ℕ}
    (F : BoundaryPolarizedCoefficientSpace (K := K) jetOrder a b c d) : Prop :=
  ∀ s q bx byy bz,
    polarizedXZDiagonalCoefficient q bx byy bz (slicePolarizedAtS F s) =
      polarizedYYDiagonalCoefficient q bx byy bz (slicePolarizedAtS F s)

/-- Existing active-species orthogonality is stable under every passive `S` spectator.  This is
the coefficient-level substitution square needed before one supplies a polynomial/carrier
description of the common target. -/
theorem boundaryPolarized_orthogonal_iff_diagonal
    {jetOrder a b c d : ℕ}
    (F : BoundaryPolarizedCoefficientSpace (K := K) jetOrder a b c d) :
    IsBoundaryPolarizedOrthogonal F ↔ IsBoundaryPolarizedDiagonalCompatible F := by
  constructor
  · intro h s
    exact (polarizedCone_orthogonal_iff_diagonal (slicePolarizedAtS F s)).1 (h s)
  · intro h s
    exact (polarizedCone_orthogonal_iff_diagonal (slicePolarizedAtS F s)).2 (h s)

end CoefficientSlices

end

end VOA.BoundaryTypedSubstitution
