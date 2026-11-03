/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Commutative.P3ConeCarrierInterface
import VOA.Commutative.P3CommonFactorSourceInvariant
import VOA.Commutative.MvPolynomialFiniteHomogeneous
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
# Weighted and symmetric residual windows at `p = 3`

This file isolates the formal fact behind the finite residual windows used after conductor
division.  Over a domain, division by a fixed nonzero weighted-homogeneous polynomial subtracts
its weighted degree.  If the dividend and divisor are invariant under the same source action,
the quotient is invariant as well.

The results here concern only finite graded windows and conductor cancellation.  They do not
assert the external identification of a compatible residual window with the
Dumanski--Feigin quadratic-cone carrier.
-/

namespace VOA.P3ResidualWindowPreservation

open VOA.MultispeciesParticlePolynomial
open VOA.P3ConeCarrierInterface
open VOA.P3CommonFactorInvariant
open VOA.P3RestrictedDualCommonFactor
open VOA.CollisionCommonFactors
open VOA.ModeParticlePairing
open VOA.BoundaryTypedSubstitution
open VOA.BoundaryCollisionDivisibility
open VOA.P3ResidualConeBridge
open VOA.P3BoundaryRootEquiv
open VOA.P3FunctionalModel
open VOA.RootedMatching
open VOA.P3CommonFactorSourceInvariant
open VOA.MvPolynomialFiniteHomogeneous

noncomputable section

universe u

variable {K : Type u} [Field K]

section WeightedCancellation

variable {I : Type*}

/-- Multiplication by a weighted-homogeneous left factor commutes with extracting the component
whose degree is the sum of the factor degree and the requested residual degree. -/
theorem weightedHomogeneousComponent_mul_left
    (w : I → ℕ) {C q : MvPolynomial I K} {c r : ℕ}
    (hC : C.IsWeightedHomogeneous w c) :
    MvPolynomial.weightedHomogeneousComponent w (c + r) (C * q) =
      C * MvPolynomial.weightedHomogeneousComponent w r q := by
  letI : GradedAlgebra (MvPolynomial.weightedHomogeneousSubmodule K w) :=
    MvPolynomial.weightedGradedAlgebra K w
  have h :=
    (DirectSum.coe_decompose_mul_add_of_left_mem
      (MvPolynomial.weightedHomogeneousSubmodule K w) hC :
      ((DirectSum.decompose (MvPolynomial.weightedHomogeneousSubmodule K w) (C * q)
        (c + r) : MvPolynomial I K) =
        C * DirectSum.decompose (MvPolynomial.weightedHomogeneousSubmodule K w) q r))
  change
    (((MvPolynomial.weightedDecomposition K w).decompose' (C * q) (c + r) :
        MvPolynomial I K) =
      C * ((MvPolynomial.weightedDecomposition K w).decompose' q r :
        MvPolynomial I K)) at h
  simpa only [MvPolynomial.weightedDecomposition.decompose'_apply] using h

/-- A nonzero weighted-homogeneous factor can be cancelled from a weighted-homogeneous product;
the quotient has the residual weighted degree. -/
theorem quotient_weightedHomogeneous_of_factorization
    (w : I → ℕ) (C p q : MvPolynomial I K) (c r : ℕ)
    (hC0 : C ≠ 0) (hC : C.IsWeightedHomogeneous w c)
    (hp : p.IsWeightedHomogeneous w (c + r)) (hfac : p = C * q) :
    q.IsWeightedHomogeneous w r := by
  intro d hd
  by_contra hdegree
  have hcomponentQ :
      MvPolynomial.weightedHomogeneousComponent w (Finsupp.weight w d) q ≠ 0 := by
    intro hzero
    have hcoeff := congrArg (MvPolynomial.coeff d) hzero
    simp [MvPolynomial.coeff_weightedHomogeneousComponent] at hcoeff
    exact hd hcoeff
  have hcomponentProduct :
      MvPolynomial.weightedHomogeneousComponent w
          (c + Finsupp.weight w d) (C * q) ≠ 0 := by
    rw [weightedHomogeneousComponent_mul_left w hC]
    exact mul_ne_zero hC0 hcomponentQ
  have hne : c + Finsupp.weight w d ≠ c + r :=
    Nat.add_left_cancel_iff.not.mpr hdegree
  have hzero :
      MvPolynomial.weightedHomogeneousComponent w
          (c + Finsupp.weight w d) p = 0 :=
    hp.weightedHomogeneousComponent_ne (c + Finsupp.weight w d) hne
  rw [hfac] at hzero
  exact hcomponentProduct hzero

/-- Subtraction form of weighted-degree cancellation.  The inequality is exactly what turns the
computable natural-number difference into an additive degree decomposition. -/
theorem quotient_weightedHomogeneous_of_factorization_sub
    (w : I → ℕ) (C p q : MvPolynomial I K) (c n : ℕ)
    (hcn : c ≤ n) (hC0 : C ≠ 0) (hC : C.IsWeightedHomogeneous w c)
    (hp : p.IsWeightedHomogeneous w n) (hfac : p = C * q) :
    q.IsWeightedHomogeneous w (n - c) := by
  apply quotient_weightedHomogeneous_of_factorization w C p q c (n - c)
    hC0 hC
  · simpa [Nat.add_sub_of_le hcn] using hp
  · exact hfac

end WeightedCancellation

section InvariantWindows

variable {G I : Type*}

/-- Polynomials fixed by every permutation in a specified family form a linear subspace.  No
group laws are needed for this elementary fixed-point construction. -/
def invariantPolynomialSubmodule (action : G → Equiv.Perm I) :
    Submodule K (MvPolynomial I K) where
  carrier := {p | ∀ g, MvPolynomial.rename (action g) p = p}
  zero_mem' := by intro g; simp
  add_mem' := by
    intro p q hp hq g
    rw [map_add, hp g, hq g]
  smul_mem' := by
    intro k p hp g
    simpa using congrArg (fun q : MvPolynomial I K ↦ k • q) (hp g)

@[simp] theorem mem_invariantPolynomialSubmodule
    (action : G → Equiv.Perm I) (p : MvPolynomial I K) :
    p ∈ invariantPolynomialSubmodule (K := K) action ↔
      ∀ g, MvPolynomial.rename (action g) p = p :=
  Iff.rfl

/-- The separately invariant, fixed-weight residual window. -/
def symmetricWeightedWindow (action : G → Equiv.Perm I)
    (w : I → ℕ) (r : ℕ) : Submodule K (MvPolynomial I K) :=
  invariantPolynomialSubmodule (K := K) action ⊓
    MvPolynomial.weightedHomogeneousSubmodule K w r

/-- A symmetric fixed-weight window is finite dimensional when there are finitely many variables
and every variable has positive weight. -/
theorem finiteDimensional_symmetricWeightedWindow [Finite I]
    (action : G → Equiv.Perm I) (w : I → ℕ)
    (hw : ∀ i, w i ≠ 0) (r : ℕ) :
    FiniteDimensional K (symmetricWeightedWindow (K := K) action w r) := by
  letI : FiniteDimensional K
      (MvPolynomial.weightedHomogeneousSubmodule K w r) :=
    finiteDimensional_weightedHomogeneousSubmodule w hw r
  exact FiniteDimensional.of_injective
    (Submodule.inclusion inf_le_right) (Submodule.inclusion_injective _)

@[simp] theorem mem_symmetricWeightedWindow
    (action : G → Equiv.Perm I) (w : I → ℕ) (r : ℕ)
    (p : MvPolynomial I K) :
    p ∈ symmetricWeightedWindow (K := K) action w r ↔
      (∀ g, MvPolynomial.rename (action g) p = p) ∧
        p.IsWeightedHomogeneous w r :=
  Iff.rfl

/-- Division by a fixed nonzero homogeneous invariant conductor lands in the symmetric residual
window of the degree difference. -/
theorem quotient_mem_symmetricWeightedWindow_of_factorization
    (action : G → Equiv.Perm I) (w : I → ℕ)
    (C p q : MvPolynomial I K) (c r : ℕ)
    (hC0 : C ≠ 0)
    (hCinv : ∀ g, MvPolynomial.rename (action g) C = C)
    (hpInv : ∀ g, MvPolynomial.rename (action g) p = p)
    (hC : C.IsWeightedHomogeneous w c)
    (hp : p.IsWeightedHomogeneous w (c + r))
    (hfac : p = C * q) :
    q ∈ symmetricWeightedWindow (K := K) action w r := by
  constructor
  · exact quotient_source_invariant_of_factorization action C p q
      hC0 hCinv hpInv hfac
  · exact quotient_weightedHomogeneous_of_factorization w C p q c r
      hC0 hC hp hfac

/-- Symmetric-window form with the residual degree computed as `n - c`. -/
theorem quotient_mem_symmetricWeightedWindow_of_factorization_sub
    (action : G → Equiv.Perm I) (w : I → ℕ)
    (C p q : MvPolynomial I K) (c n : ℕ)
    (hcn : c ≤ n) (hC0 : C ≠ 0)
    (hCinv : ∀ g, MvPolynomial.rename (action g) C = C)
    (hpInv : ∀ g, MvPolynomial.rename (action g) p = p)
    (hC : C.IsWeightedHomogeneous w c)
    (hp : p.IsWeightedHomogeneous w n) (hfac : p = C * q) :
    q ∈ symmetricWeightedWindow (K := K) action w (n - c) := by
  constructor
  · exact quotient_source_invariant_of_factorization action C p q
      hC0 hCinv hpInv hfac
  · exact quotient_weightedHomogeneous_of_factorization_sub w C p q c n
      hcn hC0 hC hp hfac

/-- The canonical linear quotient from `FixedPolynomialFactor.residualOfDivisibility` satisfies
the same window theorem. -/
theorem residualOfDivisibility_mem_symmetricWeightedWindow
    {E : Type*} [AddCommGroup E] [Module K E]
    (action : G → Equiv.Perm I) (w : I → ℕ)
    (C : MvPolynomial I K) (f : E →ₗ[K] MvPolynomial I K)
    (hdiv : ∀ e, C ∣ f e) (c r : ℕ)
    (hC0 : C ≠ 0)
    (hCinv : ∀ g, MvPolynomial.rename (action g) C = C)
    (hC : C.IsWeightedHomogeneous w c)
    (hpInv : ∀ e g, MvPolynomial.rename (action g) (f e) = f e)
    (hp : ∀ e, (f e).IsWeightedHomogeneous w (c + r)) (e : E) :
    FixedPolynomialFactor.residualOfDivisibility C hC0 f hdiv e ∈
      symmetricWeightedWindow (K := K) action w r := by
  apply quotient_mem_symmetricWeightedWindow_of_factorization
    action w C (f e)
    (FixedPolynomialFactor.residualOfDivisibility C hC0 f hdiv e) c r
    hC0 hCinv (hpInv e) hC (hp e)
  exact FixedPolynomialFactor.factor_residualOfDivisibility C hC0 f hdiv e

end InvariantWindows

section P3ConductorDegree

/-- The current part of an arbitrary four-species permutation, assembled as a permutation of
the sigma type of `X`, `Y`, and `Z` current labels. -/
def boundarySpeciesPermutationCurrentEquiv (a b c d : ℕ)
    (g : SpeciesPermutation (boundaryMultiplicity a b c d)) :
    Equiv.Perm (CurrentLabels (p3CurrentMultiplicity a b c)) :=
  Equiv.sigmaCongrRight fun A ↦
    match A with
    | .X => g .X
    | .Y => g .Y
    | .Z => g .Z

/-- Every independent permutation of the four boundary species determines a source relabeling
of the current-plus-`S` formulation. -/
def boundarySpeciesPermutationToSourceRelabeling (a b c d : ℕ)
    (g : SpeciesPermutation (boundaryMultiplicity a b c d)) :
    SourceRelabeling (S := Fin d)
      (currentSpecies (p3CurrentMultiplicity a b c)) :=
  (⟨boundarySpeciesPermutationCurrentEquiv a b c d g, by
      rintro ⟨A, i⟩
      cases A <;> rfl⟩,
    g .S)

/-- Conjugating the lifted source relabeling back to four-species labels recovers the original
four independent permutations. -/
theorem p3BoundarySpeciesPermutation_toSourceRelabeling
    (a b c d : ℕ)
    (g : SpeciesPermutation (boundaryMultiplicity a b c d)) :
    p3BoundarySpeciesPermutation a b c d
        (boundarySpeciesPermutationToSourceRelabeling a b c d g) = g := by
  funext A
  apply Equiv.ext
  intro i
  have h := p3BoundarySpeciesPermutation_naturality a b c d
    (boundarySpeciesPermutationToSourceRelabeling a b c d g)
    (⟨A, i⟩ : SpeciesLabel (boundaryMultiplicity a b c d))
  cases A <;>
    simpa [boundarySpeciesPermutationToSourceRelabeling,
      boundarySpeciesPermutationCurrentEquiv, speciesLabelEquiv,
      SourceRelabeling.sumEquiv, currentSpecies, p3BoundaryRootEquiv] using h

/-- Ordinary total polynomial degree, presented as the constant-one weight. -/
def particleWeightOne {I : Type*} : I → ℕ := fun _ ↦ 1

theorem modeDegree_unorderedModeBlock {jetOrder arity : ℕ}
    (r : Fin arity → Fin (jetOrder + 1)) :
    modeDegree (unorderedModeBlock r) = ∑ i, (r i : ℕ) := by
  have hcoe :
      ((unorderedModeBlock r : ModeConfiguration jetOrder arity) :
          Multiset (Fin (jetOrder + 1))) =
        (List.ofFn r : Multiset (Fin (jetOrder + 1))) := by
    change (List.Vector.toList (List.Vector.ofFn r) :
      Multiset (Fin (jetOrder + 1))) = (List.ofFn r : Multiset (Fin (jetOrder + 1)))
    rw [List.Vector.toList_ofFn]
  rw [modeDegree, hcoe, Multiset.map_coe, Multiset.sum_coe]
  rw [← List.ofFn_comp']
  exact List.sum_ofFn

theorem weight_multispeciesLabelledExponent
    {Species : Type*} [Fintype Species]
    {jetOrder : ℕ} {multiplicity : Species → ℕ}
    (r : MultispeciesModeTuple jetOrder multiplicity) :
    Finsupp.weight particleWeightOne (multispeciesLabelledExponent r) =
      multispeciesModeDegree (multispeciesUnorderedModeBlock r) := by
  classical
  rw [Finsupp.weight_apply,
    Finsupp.sum_fintype _ _ (fun _ ↦ by simp [particleWeightOne])]
  simp only [nsmul_eq_mul, multispeciesLabelledExponent_apply, particleWeightOne, mul_one]
  rw [Fintype.sum_sigma]
  simp only [multispeciesModeDegree]
  apply Finset.sum_congr rfl
  intro A hA
  exact (modeDegree_unorderedModeBlock (r A)).symm

theorem weight_boundarySpeciesShift (a b c d : ℕ) :
    Finsupp.weight
        (particleWeightOne : SpeciesLabel (boundaryMultiplicity a b c d) → ℕ)
        (speciesShiftExponent (boundaryMultiplicity a b c d) boundarySpeciesShift) = d := by
  classical
  rw [Finsupp.weight_apply,
    Finsupp.sum_fintype _ _ (fun _ ↦ by simp [particleWeightOne])]
  simp only [nsmul_eq_mul, speciesShiftExponent_apply, particleWeightOne, mul_one]
  rw [Fintype.sum_sigma]
  have huniv : (Finset.univ : Finset BoundarySpecies) =
      {.X, .Y, .Z, .S} := by
    ext A
    cases A <;> simp
  rw [huniv]
  simp [boundaryMultiplicity, boundarySpeciesShift]
  exact Fintype.card_fin d

theorem weight_shiftedMultispeciesLabelledExponent
    {Species : Type*} [Fintype Species]
    {jetOrder : ℕ} {multiplicity : Species → ℕ}
    (shift : Species → ℕ) (r : MultispeciesModeTuple jetOrder multiplicity) :
    Finsupp.weight particleWeightOne
        (shiftedMultispeciesLabelledExponent shift r) =
      Finsupp.weight particleWeightOne (speciesShiftExponent multiplicity shift) +
        multispeciesModeDegree (multispeciesUnorderedModeBlock r) := by
  simp [shiftedMultispeciesLabelledExponent,
    weight_multispeciesLabelledExponent]

/-- A boundary coefficient vector of fixed derivative degree maps to a polynomial of ordinary
total degree equal to the `S` shift `d` plus that derivative degree. -/
theorem boundaryFixedParticlePolynomial_isWeightedHomogeneous
    (jetOrder derivativeDegree a b c d : ℕ)
    (F : MultispeciesParticleSector K jetOrder
      (boundaryMultiplicity a b c d) derivativeDegree) :
    (boundaryFixedParticlePolynomial jetOrder derivativeDegree a b c d F).IsWeightedHomogeneous
      particleWeightOne (d + derivativeDegree) := by
  classical
  rw [boundaryFixedParticlePolynomial, shiftedMultispeciesParticlePolynomial]
  apply MvPolynomial.IsWeightedHomogeneous.sum
  intro r hr
  by_cases hdegree :
      multispeciesModeDegree (multispeciesUnorderedModeBlock r) = derivativeDegree
  · apply MvPolynomial.isWeightedHomogeneous_monomial
    rw [weight_shiftedMultispeciesLabelledExponent,
      weight_boundarySpeciesShift, hdegree]
  · simpa [extendFixedMultispeciesSector, hdegree] using
      (MvPolynomial.isWeightedHomogeneous_zero K particleWeightOne
        (d + derivativeDegree))

/-- The exact computable weighted degree of the labelled `p = 3` conductor.  This form avoids
hiding finite collision multiplicities behind a closed cardinality formula. -/
def p3ConductorWeightedDegree (a b c d : ℕ) : ℕ :=
  Finsupp.weight
      (particleWeightOne : SpeciesLabel (boundaryMultiplicity a b c d) → ℕ)
      (speciesShiftExponent (boundaryMultiplicity a b c d) boundarySpeciesShift) +
    ∑ i : ConductorCollisionIndex a b c d, conductorCollisionMultiplicity i

/- The total ordinary particle degree of a fixed boundary sector is `d + derivativeDegree`.
The following two elementary consequences of the degree-matching equation make the natural-number
subtraction in the residual-window API explicit.  They do not assert that a factorization or a
quadratic-cone carrier identification exists. -/
theorem p3ConductorWeightedDegree_le_of_degree_eq
    (derivativeDegree a b c d residualDegree : ℕ)
    (hdegree : p3ConductorWeightedDegree a b c d + residualDegree =
      d + derivativeDegree) :
    p3ConductorWeightedDegree a b c d ≤ d + derivativeDegree := by
  omega

theorem residualDegree_eq_totalDegree_sub_p3ConductorWeightedDegree
    (derivativeDegree a b c d residualDegree : ℕ)
    (hdegree : p3ConductorWeightedDegree a b c d + residualDegree =
      d + derivativeDegree) :
    residualDegree = d + derivativeDegree - p3ConductorWeightedDegree a b c d := by
  omega

theorem collisionFactor_isWeightedHomogeneous_one
    {I : Type*} (i j : I) :
    (collisionFactor (K := K) i j).IsWeightedHomogeneous particleWeightOne 1 := by
  rw [← MvPolynomial.mem_weightedHomogeneousSubmodule]
  exact (MvPolynomial.weightedHomogeneousSubmodule K particleWeightOne 1).sub_mem
    (MvPolynomial.isWeightedHomogeneous_X K particleWeightOne i)
    (MvPolynomial.isWeightedHomogeneous_X K particleWeightOne j)

theorem sRootFactor_isWeightedHomogeneous (a b c d : ℕ) :
    (sRootFactor (K := K) a b c d).IsWeightedHomogeneous particleWeightOne
      (Finsupp.weight
        (particleWeightOne : SpeciesLabel (boundaryMultiplicity a b c d) → ℕ)
        (speciesShiftExponent (boundaryMultiplicity a b c d) boundarySpeciesShift)) := by
  exact MvPolynomial.isWeightedHomogeneous_monomial _ _ _ rfl

theorem conductorCollisionProduct_isWeightedHomogeneous (a b c d : ℕ) :
    (conductorCollisionProduct (K := K) a b c d).IsWeightedHomogeneous particleWeightOne
      (∑ i : ConductorCollisionIndex a b c d, conductorCollisionMultiplicity i) := by
  classical
  rw [conductorCollisionProduct]
  simpa using
    (MvPolynomial.IsWeightedHomogeneous.prod
      (Finset.univ : Finset (ConductorCollisionIndex a b c d))
      (fun i ↦ conductorCollisionFactor (K := K) a b c d i ^
        conductorCollisionMultiplicity i)
      (fun i ↦ conductorCollisionMultiplicity i • (1 : ℕ)) (w := particleWeightOne)
      (by
        intro i hi
        rcases i with ij | is
        · simpa [conductorCollisionFactor, conductorCollisionMultiplicity] using
            (collisionFactor_isWeightedHomogeneous_one (K := K)
              (boundarySLabel a b c d ij.1.1)
              (boundarySLabel a b c d ij.1.2)).pow 2
        · simpa [conductorCollisionFactor, conductorCollisionMultiplicity] using
            (collisionFactor_isWeightedHomogeneous_one (K := K)
              (boundarySLabel a b c d is.2)
              (boundaryCurrentLabel a b c d is.1)).pow 1))

/-- The labelled `p = 3` conductor is homogeneous of its explicit root-plus-collision degree. -/
theorem p3CommonFactor_isWeightedHomogeneous (a b c d : ℕ) :
    (p3CommonFactor (K := K) a b c d).IsWeightedHomogeneous particleWeightOne
      (p3ConductorWeightedDegree a b c d) := by
  rw [p3CommonFactor, p3ConductorWeightedDegree]
  exact (sRootFactor_isWeightedHomogeneous (K := K) a b c d).mul
    (conductorCollisionProduct_isWeightedHomogeneous (K := K) a b c d)

/-- The concrete separately symmetric, fixed-total-degree window in one boundary sector. -/
def boundarySymmetricWeightedWindow (a b c d residualDegree : ℕ) :
    Submodule K
      (MvPolynomial (SpeciesLabel (boundaryMultiplicity a b c d)) K) :=
  symmetricWeightedWindow (K := K)
    (G := SpeciesPermutation (boundaryMultiplicity a b c d))
    (fun g ↦ speciesLabelEquiv g) particleWeightOne residualDegree

/-- The two finite-dimensional separately symmetric fixed-degree polynomial windows for the
polarized `XZ` and `YY` branches. -/
def p3SymmetricResidualWindow (a b c d residualDegreeXZ residualDegreeYY : ℕ) :
    P3ResidualWindow (K := K) a b c d where
  xz := boundarySymmetricWeightedWindow (K := K)
    (a + 1) b (c + 1) d residualDegreeXZ
  yy := boundarySymmetricWeightedWindow (K := K)
    a (b + 2) c d residualDegreeYY

theorem boundarySymmetricWeightedWindow_finiteDimensional
    (a b c d residualDegree : ℕ) :
    FiniteDimensional K
      (boundarySymmetricWeightedWindow (K := K) a b c d residualDegree) := by
  exact finiteDimensional_symmetricWeightedWindow
    (K := K) (G := SpeciesPermutation (boundaryMultiplicity a b c d))
    (fun g ↦ speciesLabelEquiv g) particleWeightOne
    (fun _ ↦ one_ne_zero) residualDegree

/-- The honest compatible residual space for the two separately symmetric fixed-degree windows
is finite dimensional, before making any identification with a quadratic-cone carrier. -/
theorem p3CompatibleSymmetricResidualSpace_finiteDimensional
    (a b c d residualDegreeXZ residualDegreeYY : ℕ) :
    FiniteDimensional K
      (p3SymmetricResidualWindow (K := K) a b c d
        residualDegreeXZ residualDegreeYY).compatibleResidualSpace := by
  letI : FiniteDimensional K
      (p3SymmetricResidualWindow (K := K) a b c d
        residualDegreeXZ residualDegreeYY).xz :=
    boundarySymmetricWeightedWindow_finiteDimensional
      (K := K) (a + 1) b (c + 1) d residualDegreeXZ
  letI : FiniteDimensional K
      (p3SymmetricResidualWindow (K := K) a b c d
        residualDegreeXZ residualDegreeYY).yy :=
    boundarySymmetricWeightedWindow_finiteDimensional
      (K := K) a (b + 2) c d residualDegreeYY
  infer_instance

/-- Every quotient of an actual fixed-sector boundary particle polynomial by the labelled
conductor lies in the expected separately symmetric residual window.  Conductor invariance under
all four independent species permutations is discharged through the source-relabeling theorem. -/
theorem boundaryQuotient_mem_symmetricWeightedWindow
    (jetOrder derivativeDegree a b c d residualDegree : ℕ)
    (F : MultispeciesParticleSector K jetOrder
      (boundaryMultiplicity a b c d) derivativeDegree)
    (q : MvPolynomial (SpeciesLabel (boundaryMultiplicity a b c d)) K)
    (hdegree : p3ConductorWeightedDegree a b c d + residualDegree =
      d + derivativeDegree)
    (hfac : boundaryFixedParticlePolynomial
        jetOrder derivativeDegree a b c d F =
      p3CommonFactor (K := K) a b c d * q) :
    q ∈ boundarySymmetricWeightedWindow (K := K)
      a b c d residualDegree := by
  have hcn : p3ConductorWeightedDegree a b c d ≤ d + derivativeDegree :=
    p3ConductorWeightedDegree_le_of_degree_eq
      derivativeDegree a b c d residualDegree hdegree
  have hres : residualDegree =
      d + derivativeDegree - p3ConductorWeightedDegree a b c d :=
    residualDegree_eq_totalDegree_sub_p3ConductorWeightedDegree
      derivativeDegree a b c d residualDegree hdegree
  rw [hres]
  apply quotient_mem_symmetricWeightedWindow_of_factorization_sub
    (G := SpeciesPermutation (boundaryMultiplicity a b c d))
    (fun g ↦ speciesLabelEquiv g) particleWeightOne
    (p3CommonFactor (K := K) a b c d)
    (boundaryFixedParticlePolynomial jetOrder derivativeDegree a b c d F)
    q (p3ConductorWeightedDegree a b c d) (d + derivativeDegree)
    hcn
    (p3CommonFactor_ne_zero (K := K) a b c d)
    (by
      intro g
      simpa [p3BoundarySpeciesPermutation_toSourceRelabeling] using
        (p3CommonFactor_rename_invariant (K := K) a b c d
          (boundarySpeciesPermutationToSourceRelabeling a b c d g)))
  · intro g
    simpa [boundaryFixedParticlePolynomial] using
      (shiftedMultispeciesParticlePolynomial_rename
        (K := K) boundarySpeciesShift g (extendFixedMultispeciesSector F))
  · exact p3CommonFactor_isWeightedHomogeneous (K := K) a b c d
  · exact boundaryFixedParticlePolynomial_isWeightedHomogeneous
      (K := K) jetOrder derivativeDegree a b c d F
  · exact hfac

/-- Simultaneous `XZ`/`YY` specialization of the residual-window theorem. -/
theorem p3PolarizedQuotients_mem_symmetricResidualWindow
    (jetOrder derivativeDegreeXZ derivativeDegreeYY a b c d
      residualDegreeXZ residualDegreeYY : ℕ)
    (FXZ : MultispeciesParticleSector K jetOrder
      (boundaryMultiplicity (a + 1) b (c + 1) d) derivativeDegreeXZ)
    (FYY : MultispeciesParticleSector K jetOrder
      (boundaryMultiplicity a (b + 2) c d) derivativeDegreeYY)
    (qXZ : MvPolynomial (XZLabel a b c d) K)
    (qYY : MvPolynomial (YYLabel a b c d) K)
    (hdegreeXZ :
      p3ConductorWeightedDegree (a + 1) b (c + 1) d + residualDegreeXZ =
        d + derivativeDegreeXZ)
    (hdegreeYY :
      p3ConductorWeightedDegree a (b + 2) c d + residualDegreeYY =
        d + derivativeDegreeYY)
    (hfacXZ : boundaryFixedParticlePolynomial
        jetOrder derivativeDegreeXZ (a + 1) b (c + 1) d FXZ =
      p3CommonFactor (K := K) (a + 1) b (c + 1) d * qXZ)
    (hfacYY : boundaryFixedParticlePolynomial
        jetOrder derivativeDegreeYY a (b + 2) c d FYY =
      p3CommonFactor (K := K) a (b + 2) c d * qYY) :
    qXZ ∈ (p3SymmetricResidualWindow (K := K) a b c d
        residualDegreeXZ residualDegreeYY).xz ∧
      qYY ∈ (p3SymmetricResidualWindow (K := K) a b c d
        residualDegreeXZ residualDegreeYY).yy := by
  constructor
  · exact boundaryQuotient_mem_symmetricWeightedWindow (K := K)
      jetOrder derivativeDegreeXZ (a + 1) b (c + 1) d residualDegreeXZ
      FXZ qXZ hdegreeXZ hfacXZ
  · exact boundaryQuotient_mem_symmetricWeightedWindow (K := K)
      jetOrder derivativeDegreeYY a (b + 2) c d residualDegreeYY
      FYY qYY hdegreeYY hfacYY

end P3ConductorDegree

end

end VOA.P3ResidualWindowPreservation
