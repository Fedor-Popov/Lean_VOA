/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Commutative.P3AuxiliaryCollisionBridge

/-!
# The common conductor in the polarized `p = 3` channel

This file compares the conductor factors in the two particle sectors coupled by
`XZ - Y^2`.  It also isolates the elementary cancellation step which passes from equality of
the full diagonal restrictions to equality of the residual diagonal restrictions.

No identification of the residual polynomials with a representation-theoretic carrier is made.
-/

namespace VOA.P3ResidualConeBridge

open MvPolynomial
open VOA.CollisionCommonFactors
open VOA.MultispeciesParticlePolynomial
open VOA.BoundaryTypedSubstitution
open VOA.BoundaryCoefficientFiber
open VOA.P3RestrictedDualCommonFactor
open VOA.P3AuxiliaryCollisionBridge

noncomputable section

universe u

variable {K : Type u} [Field K]

/-- A target `S` label after the active current variables have collided. -/
def targetSLabel (a b c d : ℕ) (s : Fin d) : BoundaryDiagonalLabel a b c d :=
  Sum.inr ⟨BoundarySpecies.S, s⟩

/-- The collision coordinate shared by the active `XZ` and `YY` variables. -/
def targetCollisionLabel (a b c d : ℕ) : BoundaryDiagonalLabel a b c d :=
  Sum.inl ()

/-- The extra factor created by collapsing two active current variables against every `S`
variable.  Its multiplicity is two for each labelled `S` variable, hence `2d` in total. -/
def activeCurrentSCollisionProduct (a b c d : ℕ) :
    MvPolynomial (BoundaryDiagonalLabel a b c d) K :=
  ∏ s : Fin d,
    collisionFactor (K := K) (targetSLabel a b c d s) (targetCollisionLabel a b c d) ^ 2

/-- Equivalently, the active contribution is the square of the product of the `d` individual
collision factors.  This records total collision-coordinate multiplicity `2d`. -/
theorem activeCurrentSCollisionProduct_eq_sq (a b c d : ℕ) :
    activeCurrentSCollisionProduct (K := K) a b c d =
      (∏ s : Fin d,
        collisionFactor (K := K)
          (targetSLabel a b c d s) (targetCollisionLabel a b c d)) ^ 2 := by
  classical
  rw [activeCurrentSCollisionProduct, Finset.prod_pow]

/-- Relabel a polynomial in the passive sector into the common diagonal target. -/
def passiveDiagonalSubstitution (a b c d : ℕ) :
    MvPolynomial (SpeciesLabel (boundaryMultiplicity a b c d)) K →ₐ[K]
      MvPolynomial (BoundaryDiagonalLabel a b c d) K :=
  MvPolynomial.rename Sum.inr

/-- The common target conductor: the passive-sector conductor, followed by the two active
current--`S` factors at each `S` label. -/
def commonTargetConductor (a b c d : ℕ) :
    MvPolynomial (BoundaryDiagonalLabel a b c d) K :=
  passiveDiagonalSubstitution (K := K) a b c d
      (p3CommonFactor (K := K) a b c d) *
    activeCurrentSCollisionProduct (K := K) a b c d

private theorem xz_sRootFactor_image (a b c d : ℕ) :
    xzDiagonalSubstitution (K := K) a b c d
        (sRootFactor (K := K) (a + 1) b (c + 1) d) =
      passiveDiagonalSubstitution (K := K) a b c d
        (sRootFactor (K := K) a b c d) := by
  classical
  simp only [xzDiagonalSubstitution, passiveDiagonalSubstitution, sRootFactor,
    MvPolynomial.rename_monomial]
  have hexp :
      Finsupp.mapDomain (xzToDiagonalLabel a b c d)
          (speciesShiftExponent (boundaryMultiplicity (a + 1) b (c + 1) d)
            boundarySpeciesShift) =
        Finsupp.mapDomain Sum.inr
          (speciesShiftExponent (boundaryMultiplicity a b c d) boundarySpeciesShift) := by
    ext i
    rcases i with u | j
    · rcases u with ⟨⟩
      have hzero :
          Finsupp.mapDomain Sum.inr
              (speciesShiftExponent (boundaryMultiplicity a b c d) boundarySpeciesShift)
              (Sum.inl () : BoundaryDiagonalLabel a b c d) = 0 :=
        Finsupp.mapDomain_notin_range _ _ (by simp)
      rw [hzero]
      simp [speciesShiftExponent, newXZLabelX, newXZLabelZ, boundarySpeciesShift]
    · simp only [mapDomain_xzToDiagonalLabel_apply_passive,
        Finsupp.mapDomain_apply Sum.inr_injective]
      rcases j with ⟨A, j⟩
      cases A <;>
        simp [speciesShiftExponent, liftXZPassiveLabel, boundarySpeciesShift]
  rw [hexp]

private theorem yy_sRootFactor_image (a b c d : ℕ) :
    yyDiagonalSubstitution (K := K) a b c d
        (sRootFactor (K := K) a (b + 2) c d) =
      passiveDiagonalSubstitution (K := K) a b c d
        (sRootFactor (K := K) a b c d) := by
  classical
  simp only [yyDiagonalSubstitution, passiveDiagonalSubstitution, sRootFactor,
    MvPolynomial.rename_monomial]
  have hexp :
      Finsupp.mapDomain (yyToDiagonalLabel a b c d)
          (speciesShiftExponent (boundaryMultiplicity a (b + 2) c d)
            boundarySpeciesShift) =
        Finsupp.mapDomain Sum.inr
          (speciesShiftExponent (boundaryMultiplicity a b c d) boundarySpeciesShift) := by
    ext i
    rcases i with u | j
    · rcases u with ⟨⟩
      have hzero :
          Finsupp.mapDomain Sum.inr
              (speciesShiftExponent (boundaryMultiplicity a b c d) boundarySpeciesShift)
              (Sum.inl () : BoundaryDiagonalLabel a b c d) = 0 :=
        Finsupp.mapDomain_notin_range _ _ (by simp)
      rw [hzero]
      simp [speciesShiftExponent, newYYLabelZero, newYYLabelOne, boundarySpeciesShift]
    · simp only [mapDomain_yyToDiagonalLabel_apply_passive,
        Finsupp.mapDomain_apply Sum.inr_injective]
      rcases j with ⟨A, j⟩
      cases A <;>
        simp [speciesShiftExponent, liftYYPassiveLabel, boundarySpeciesShift]
  rw [hexp]

/-- The same-`S` part of the conductor, before adjoining current--`S` factors. -/
def sameSCollisionProduct (a b c d : ℕ) :
    MvPolynomial (SpeciesLabel (boundaryMultiplicity a b c d)) K :=
  ∏ ij : IncreasingPair (Fin d),
    collisionFactor (K := K)
      (boundarySLabel a b c d ij.1.1) (boundarySLabel a b c d ij.1.2) ^ 2

/-- The current--`S` part of the conductor. -/
def currentSCollisionProduct (a b c d : ℕ) :
    MvPolynomial (SpeciesLabel (boundaryMultiplicity a b c d)) K :=
  ∏ is : BoundaryCurrentLabel a b c × Fin d,
    collisionFactor (K := K)
      (boundarySLabel a b c d is.2) (boundaryCurrentLabel a b c d is.1)

theorem conductorCollisionProduct_eq (a b c d : ℕ) :
    conductorCollisionProduct (K := K) a b c d =
      sameSCollisionProduct (K := K) a b c d *
        currentSCollisionProduct (K := K) a b c d := by
  classical
  simp [conductorCollisionProduct, sameSCollisionProduct, currentSCollisionProduct,
    conductorCollisionFactor, conductorCollisionMultiplicity, Fintype.prod_sum_type]

private theorem xz_sameSCollisionProduct_image (a b c d : ℕ) :
    xzDiagonalSubstitution (K := K) a b c d
        (sameSCollisionProduct (K := K) (a + 1) b (c + 1) d) =
      passiveDiagonalSubstitution (K := K) a b c d
        (sameSCollisionProduct (K := K) a b c d) := by
  classical
  simp only [sameSCollisionProduct, map_prod, map_pow]
  apply Finset.prod_congr rfl
  intro ij _
  simp [xzDiagonalSubstitution, passiveDiagonalSubstitution,
    collisionFactor, boundarySLabel, xzToDiagonalLabel]

private theorem yy_sameSCollisionProduct_image (a b c d : ℕ) :
    yyDiagonalSubstitution (K := K) a b c d
        (sameSCollisionProduct (K := K) a (b + 2) c d) =
      passiveDiagonalSubstitution (K := K) a b c d
        (sameSCollisionProduct (K := K) a b c d) := by
  classical
  simp only [sameSCollisionProduct, map_prod, map_pow]
  apply Finset.prod_congr rfl
  intro ij _
  simp [yyDiagonalSubstitution, passiveDiagonalSubstitution,
    collisionFactor, boundarySLabel, yyToDiagonalLabel]

private theorem xz_currentSCollisionProduct_image (a b c d : ℕ) :
    xzDiagonalSubstitution (K := K) a b c d
        (currentSCollisionProduct (K := K) (a + 1) b (c + 1) d) =
      passiveDiagonalSubstitution (K := K) a b c d
          (currentSCollisionProduct (K := K) a b c d) *
        activeCurrentSCollisionProduct (K := K) a b c d := by
  classical
  simp [currentSCollisionProduct, activeCurrentSCollisionProduct,
    xzDiagonalSubstitution, passiveDiagonalSubstitution, collisionFactor,
    boundarySLabel, boundaryCurrentLabel, xzToDiagonalLabel,
    targetSLabel, targetCollisionLabel, Fintype.prod_sum_type,
    Fintype.prod_prod_type, Fin.prod_univ_succ]
  rw [Finset.prod_pow]
  ring

private theorem yy_currentSCollisionProduct_image (a b c d : ℕ) :
    yyDiagonalSubstitution (K := K) a b c d
        (currentSCollisionProduct (K := K) a (b + 2) c d) =
      passiveDiagonalSubstitution (K := K) a b c d
          (currentSCollisionProduct (K := K) a b c d) *
        activeCurrentSCollisionProduct (K := K) a b c d := by
  classical
  have hone :
      yyToDiagonalLabel a b c d
          ⟨BoundarySpecies.Y, (1 : Fin (b + 2))⟩ =
        (Sum.inl () : BoundaryDiagonalLabel a b c d) := by
    simpa [newYYLabelOne] using yyToDiagonalLabel_newY_one a b c d
  have hzero :
      yyToDiagonalLabel a b c d
          ⟨BoundarySpecies.Y, (0 : Fin (b + 2))⟩ =
        (Sum.inl () : BoundaryDiagonalLabel a b c d) := by
    rfl
  have hX (i : Fin a) :
      yyToDiagonalLabel a b c d
          ⟨BoundarySpecies.X, i⟩ =
        (Sum.inr ⟨BoundarySpecies.X, i⟩ : BoundaryDiagonalLabel a b c d) := by
    rfl
  have hY (i : Fin b) :
      yyToDiagonalLabel a b c d
          ⟨BoundarySpecies.Y, i.succ.succ⟩ =
        (Sum.inr ⟨BoundarySpecies.Y, i⟩ : BoundaryDiagonalLabel a b c d) := by
    rfl
  have hZ (i : Fin c) :
      yyToDiagonalLabel a b c d
          ⟨BoundarySpecies.Z, i⟩ =
        (Sum.inr ⟨BoundarySpecies.Z, i⟩ : BoundaryDiagonalLabel a b c d) := by
    rfl
  have hS (i : Fin d) :
      yyToDiagonalLabel a b c d
          ⟨BoundarySpecies.S, i⟩ =
        (Sum.inr ⟨BoundarySpecies.S, i⟩ : BoundaryDiagonalLabel a b c d) := by
    rfl
  simp [hone, hzero, hX, hY, hZ, hS,
    currentSCollisionProduct, activeCurrentSCollisionProduct,
    yyDiagonalSubstitution, passiveDiagonalSubstitution, collisionFactor,
    boundarySLabel, boundaryCurrentLabel,
    targetSLabel, targetCollisionLabel, Fintype.prod_sum_type,
    Fintype.prod_prod_type, Fin.prod_univ_succ]
  rw [Finset.prod_pow]
  ring

/-- The `XZ`-sector conductor has the common target image.  In particular, each labelled `S`
coordinate receives two active current--`S` factors. -/
theorem xz_p3CommonFactor_image (a b c d : ℕ) :
    xzDiagonalSubstitution (K := K) a b c d
        (p3CommonFactor (K := K) (a + 1) b (c + 1) d) =
      commonTargetConductor (K := K) a b c d := by
  classical
  simp only [commonTargetConductor, p3CommonFactor, conductorCollisionProduct_eq,
    map_mul, xz_sRootFactor_image, xz_sameSCollisionProduct_image,
    xz_currentSCollisionProduct_image]
  ring

/-- The `YY`-sector conductor has the same common target image as the `XZ`-sector conductor. -/
theorem yy_p3CommonFactor_image (a b c d : ℕ) :
    yyDiagonalSubstitution (K := K) a b c d
        (p3CommonFactor (K := K) a (b + 2) c d) =
      commonTargetConductor (K := K) a b c d := by
  classical
  simp only [commonTargetConductor, p3CommonFactor, conductorCollisionProduct_eq,
    map_mul, yy_sRootFactor_image, yy_sameSCollisionProduct_image,
    yy_currentSCollisionProduct_image]
  ring

/-- The two conductor factors coupled by `XZ - Y^2` have exactly the same typed diagonal
restriction. -/
theorem p3CommonFactor_typed_diagonal_images_agree (a b c d : ℕ) :
    xzDiagonalSubstitution (K := K) a b c d
        (p3CommonFactor (K := K) (a + 1) b (c + 1) d) =
      yyDiagonalSubstitution (K := K) a b c d
        (p3CommonFactor (K := K) a (b + 2) c d) := by
  rw [xz_p3CommonFactor_image, yy_p3CommonFactor_image]

/-- The labelled conductor is nonzero. -/
theorem p3CommonFactor_ne_zero (a b c d : ℕ) :
    p3CommonFactor (K := K) a b c d ≠ 0 := by
  classical
  rw [p3CommonFactor]
  apply mul_ne_zero
  · simp [sRootFactor]
  · rw [conductorCollisionProduct]
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    rcases i with ij | is
    · apply pow_ne_zero
      exact (collisionFactor_prime (K := K) _ _
        ((boundarySLabel_injective a b c d).ne (ne_of_gt ij.2))).ne_zero
    · apply pow_ne_zero
      exact (collisionFactor_prime (K := K) _ _
        (boundarySLabel_ne_boundaryCurrentLabel a b c d is.2 is.1).symm).ne_zero

/-- The common target conductor is nonzero.  This is the exact cancellation input used below. -/
theorem commonTargetConductor_ne_zero (a b c d : ℕ) :
    commonTargetConductor (K := K) a b c d ≠ 0 := by
  classical
  rw [commonTargetConductor]
  apply mul_ne_zero
  · exact (MvPolynomial.rename_injective Sum.inr Sum.inr_injective).ne
      (p3CommonFactor_ne_zero (K := K) a b c d)
  · rw [activeCurrentSCollisionProduct]
    apply Finset.prod_ne_zero_iff.mpr
    intro s _
    apply pow_ne_zero
    exact (collisionFactor_prime _ _ (by
      simp [targetSLabel, targetCollisionLabel])).ne_zero

section Cancellation

variable {R : Type*} [CommRing R] [IsDomain R]

/-- Cancelling a nonzero common factor is equivalent to comparing the two residuals. -/
theorem common_factor_mul_eq_iff {C PX PY RX RY : R}
    (hC : C ≠ 0) (hX : PX = C * RX) (hY : PY = C * RY) :
    PX = PY ↔ RX = RY := by
  constructor
  · intro h
    apply mul_left_cancel₀ hC
    calc
      C * RX = PX := hX.symm
      _ = PY := h
      _ = C * RY := hY
  · intro h
    rw [hX, hY, h]

end Cancellation

/-- If the two source polynomials factor by their sector conductors, then the full polarized
diagonal condition is equivalent to equality of the two residual diagonal restrictions. -/
theorem polarized_compatibility_iff_residual_diagonal_compatibility
    (a b c d : ℕ)
    (pXZ qXZ : MvPolynomial (XZLabel a b c d) K)
    (pYY qYY : MvPolynomial (YYLabel a b c d) K)
    (hXZ : pXZ = p3CommonFactor (K := K) (a + 1) b (c + 1) d * qXZ)
    (hYY : pYY = p3CommonFactor (K := K) a (b + 2) c d * qYY) :
    IsPolarizedDiagonalCompatible (K := K) a b c d (pXZ, pYY) ↔
      xzDiagonalSubstitution (K := K) a b c d qXZ =
        yyDiagonalSubstitution (K := K) a b c d qYY := by
  apply common_factor_mul_eq_iff
    (commonTargetConductor_ne_zero (K := K) a b c d)
  · rw [hXZ, map_mul, xz_p3CommonFactor_image]
  · rw [hYY, map_mul, yy_p3CommonFactor_image]

/-- Auxiliary orthogonality in both polarized sectors supplies conductor residuals, and
polarized orthogonality forces their typed diagonal restrictions to agree.  This is a
state-counting/algebraic interface only: it does not identify which residual pairs occur. -/
theorem exists_compatible_residuals_of_auxiliary_and_polarized_orthogonal [CharZero K]
    {jetOrder a b c d : ℕ}
    (F : BoundaryPolarizedCoefficientSpace (K := K) jetOrder a b c d)
    (hPolarized : IsBoundaryPolarizedOrthogonal F)
    (hXZSS : HasBoundaryS2Orthogonality F.1)
    (hXZXS : HasBoundaryXSOrthogonality F.1)
    (hXZYS : HasBoundaryYSOrthogonality F.1)
    (hXZZS : HasBoundaryZSOrthogonality F.1)
    (hYYSS : HasBoundaryS2Orthogonality F.2)
    (hYYXS : HasBoundaryXSOrthogonality F.2)
    (hYYYS : HasBoundaryYSOrthogonality F.2)
    (hYYZS : HasBoundaryZSOrthogonality F.2) :
    ∃ qXZ : MvPolynomial (XZLabel a b c d) K,
      ∃ qYY : MvPolynomial (YYLabel a b c d) K,
        shiftedMultispeciesParticlePolynomial boundarySpeciesShift F.1 =
            p3CommonFactor (K := K) (a + 1) b (c + 1) d * qXZ ∧
          shiftedMultispeciesParticlePolynomial boundarySpeciesShift F.2 =
            p3CommonFactor (K := K) a (b + 2) c d * qYY ∧
          xzDiagonalSubstitution (K := K) a b c d qXZ =
            yyDiagonalSubstitution (K := K) a b c d qYY := by
  rcases p3CommonFactor_dvd_of_auxiliaryOrthogonal F.1
      hXZSS hXZXS hXZYS hXZZS with ⟨qXZ, hXZ⟩
  rcases p3CommonFactor_dvd_of_auxiliaryOrthogonal F.2
      hYYSS hYYXS hYYYS hYYZS with ⟨qYY, hYY⟩
  refine ⟨qXZ, qYY, hXZ, hYY, ?_⟩
  apply (polarized_compatibility_iff_residual_diagonal_compatibility
    a b c d _ qXZ _ qYY hXZ hYY).mp
  exact boundaryPolarizedOrthogonal_typedPolynomial_eq F hPolarized

end

end VOA.P3ResidualConeBridge
