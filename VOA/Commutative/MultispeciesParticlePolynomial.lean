/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Commutative.ModeParticlePolynomial

/-!
# Multispecies labelled particle polynomials

This file assembles the one-species polynomial realization into a dependent family of species.
For a finite species type and a multiplicity function, labels have type
`Sigma fun A => Fin (multiplicity A)`.  A source mode configuration is a symmetric power in each
species, and a labelled monomial assigns one mode index to every label.

The realization is coefficientwise injective and invariant under the product of the symmetric
groups acting within each species.  A generic species-dependent initial exponent is included.  In
the boundary affine application it is `0` on `X,Y,Z` and `1` on `S`, so the resulting polynomial
has exactly the shifted `S` monomial factor.

The last definitions restrict the construction to the already formalized fixed multidegree and
fixed derivative-degree sector.  No relation, ideal, carrier, or classical-freeness theorem is
asserted here.
-/

namespace VOA.MultispeciesParticlePolynomial

open VOA.ModeParticlePairing
open VOA.ModeParticlePolynomial

noncomputable section

universe u v

variable {K : Type u} [Field K]
variable {Species : Type v} [Fintype Species]

local instance : DecidableEq Species := Classical.decEq _

/-- Labels for a fixed species multidegree. -/
abbrev SpeciesLabel (multiplicity : Species → ℕ) :=
  Σ A, Fin (multiplicity A)

/-- A labelled assignment of finite-jet mode indices, separately for every species. -/
abbrev MultispeciesModeTuple (jetOrder : ℕ) (multiplicity : Species → ℕ) :=
  ∀ A, Fin (multiplicity A) → Fin (jetOrder + 1)

/-- A coefficient family on all commutative mode configurations in one fixed species
multidegree. -/
abbrev MultispeciesJetParticleSpace (K : Type u) (jetOrder : ℕ)
    (multiplicity : Species → ℕ) :=
  MultispeciesModeConfiguration jetOrder multiplicity → K

/-- Forget the label ordering separately in every species. -/
def multispeciesUnorderedModeBlock {jetOrder : ℕ} {multiplicity : Species → ℕ}
    (r : MultispeciesModeTuple jetOrder multiplicity) :
    MultispeciesModeConfiguration jetOrder multiplicity :=
  fun A ↦ unorderedModeBlock (r A)

/-- Flatten a specieswise labelled mode tuple to the exponent vector on all particle labels. -/
def multispeciesLabelledExponent {jetOrder : ℕ} {multiplicity : Species → ℕ}
    (r : MultispeciesModeTuple jetOrder multiplicity) :
    SpeciesLabel multiplicity →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i ↦ (r i.1 i.2 : ℕ))

@[simp]
theorem multispeciesLabelledExponent_apply {jetOrder : ℕ}
    {multiplicity : Species → ℕ}
    (r : MultispeciesModeTuple jetOrder multiplicity)
    (i : SpeciesLabel multiplicity) :
    multispeciesLabelledExponent r i = (r i.1 i.2 : ℕ) := by
  simp [multispeciesLabelledExponent]

/-- The flattened exponent vector remembers every specieswise mode index. -/
theorem multispeciesLabelledExponent_injective {jetOrder : ℕ}
    {multiplicity : Species → ℕ} :
    Function.Injective
      (multispeciesLabelledExponent :
        MultispeciesModeTuple jetOrder multiplicity → SpeciesLabel multiplicity →₀ ℕ) := by
  intro r s h
  funext A i
  apply Fin.ext
  have hi := congrArg (fun e : SpeciesLabel multiplicity →₀ ℕ ↦ e ⟨A, i⟩) h
  simpa using hi

/-- Concrete polynomial realization of a multispecies coefficient family. -/
def multispeciesParticlePolynomial {jetOrder : ℕ} {multiplicity : Species → ℕ}
    (F : MultispeciesJetParticleSpace K jetOrder multiplicity) :
    MvPolynomial (SpeciesLabel multiplicity) K :=
  ∑ r : MultispeciesModeTuple jetOrder multiplicity,
    MvPolynomial.monomial (multispeciesLabelledExponent r)
      (F (multispeciesUnorderedModeBlock r))

/-- Exact coefficient recovery for the multispecies realization. -/
theorem coeff_multispeciesParticlePolynomial {jetOrder : ℕ}
    {multiplicity : Species → ℕ}
    (F : MultispeciesJetParticleSpace K jetOrder multiplicity)
    (r : MultispeciesModeTuple jetOrder multiplicity) :
    MvPolynomial.coeff (multispeciesLabelledExponent r)
        (multispeciesParticlePolynomial F) =
      F (multispeciesUnorderedModeBlock r) := by
  classical
  rw [multispeciesParticlePolynomial, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  rw [Finset.sum_eq_single r]
  · simp
  · intro s _ hs
    rw [if_neg (fun h ↦ hs (multispeciesLabelledExponent_injective h))]
  · simp

/-- Choose one ordered representative in every species. -/
def multispeciesOrderedRepresentative {jetOrder : ℕ}
    {multiplicity : Species → ℕ}
    (b : MultispeciesModeConfiguration jetOrder multiplicity) :
    MultispeciesModeTuple jetOrder multiplicity :=
  fun A ↦ orderedRepresentative (b A)

omit [Fintype Species] in
/-- Forgetting all chosen specieswise orderings recovers the source configuration. -/
theorem multispeciesUnordered_orderedRepresentative {jetOrder : ℕ}
    {multiplicity : Species → ℕ}
    (b : MultispeciesModeConfiguration jetOrder multiplicity) :
    multispeciesUnorderedModeBlock (multispeciesOrderedRepresentative b) = b := by
  funext A
  exact unorderedModeBlock_orderedRepresentative (b A)

/-- The multispecies polynomial realization is injective. -/
theorem multispeciesParticlePolynomial_injective {jetOrder : ℕ}
    {multiplicity : Species → ℕ} :
    Function.Injective
      (multispeciesParticlePolynomial :
        MultispeciesJetParticleSpace K jetOrder multiplicity →
          MvPolynomial (SpeciesLabel multiplicity) K) := by
  intro F G h
  funext b
  let r := multispeciesOrderedRepresentative b
  have hc := congrArg (MvPolynomial.coeff (multispeciesLabelledExponent r)) h
  rw [coeff_multispeciesParticlePolynomial,
    coeff_multispeciesParticlePolynomial] at hc
  have hr : multispeciesUnorderedModeBlock r = b :=
    multispeciesUnordered_orderedRepresentative b
  simpa only [hr] using hc

/-- The product of the symmetric groups which relabel particles within each species. -/
abbrev SpeciesPermutation (multiplicity : Species → ℕ) :=
  ∀ A, Equiv.Perm (Fin (multiplicity A))

/-- A species-preserving permutation of the full dependent label type. -/
def speciesLabelEquiv {multiplicity : Species → ℕ}
    (g : SpeciesPermutation multiplicity) :
    SpeciesLabel multiplicity ≃ SpeciesLabel multiplicity where
  toFun i := ⟨i.1, g i.1 i.2⟩
  invFun i := ⟨i.1, (g i.1).symm i.2⟩
  left_inv i := by simp
  right_inv i := by simp

/-- Relabel a mode tuple independently within each species. -/
def relabelMultispeciesModeTuple {jetOrder : ℕ}
    {multiplicity : Species → ℕ} (g : SpeciesPermutation multiplicity) :
    MultispeciesModeTuple jetOrder multiplicity ≃
      MultispeciesModeTuple jetOrder multiplicity where
  toFun r A i := r A ((g A).symm i)
  invFun r A i := r A (g A i)
  left_inv r := by
    funext A i
    simp
  right_inv r := by
    funext A i
    simp

/-- Relabeling particle variables agrees with relabeling the multispecies mode tuple. -/
theorem mapDomain_multispeciesLabelledExponent {jetOrder : ℕ}
    {multiplicity : Species → ℕ} (g : SpeciesPermutation multiplicity)
    (r : MultispeciesModeTuple jetOrder multiplicity) :
    Finsupp.mapDomain (speciesLabelEquiv g) (multispeciesLabelledExponent r) =
      multispeciesLabelledExponent (relabelMultispeciesModeTuple g r) := by
  rw [← Finsupp.equivMapDomain_eq_mapDomain]
  ext i
  simp [Finsupp.equivMapDomain_apply, speciesLabelEquiv,
    relabelMultispeciesModeTuple]

omit [Fintype Species] in
/-- Specieswise relabeling does not change any commutative mode configuration. -/
theorem multispeciesUnordered_relabel {jetOrder : ℕ}
    {multiplicity : Species → ℕ} (g : SpeciesPermutation multiplicity)
    (r : MultispeciesModeTuple jetOrder multiplicity) :
    multispeciesUnorderedModeBlock (relabelMultispeciesModeTuple g r) =
      multispeciesUnorderedModeBlock r := by
  funext A
  exact unorderedModeBlock_relabelModeTuple (g A) (r A)

/-- The concrete multispecies polynomial is invariant under every species-preserving label
permutation. -/
theorem multispeciesParticlePolynomial_rename {jetOrder : ℕ}
    {multiplicity : Species → ℕ} (g : SpeciesPermutation multiplicity)
    (F : MultispeciesJetParticleSpace K jetOrder multiplicity) :
    MvPolynomial.rename (speciesLabelEquiv g) (multispeciesParticlePolynomial F) =
      multispeciesParticlePolynomial F := by
  classical
  rw [multispeciesParticlePolynomial, map_sum]
  simp_rw [MvPolynomial.rename_monomial,
    mapDomain_multispeciesLabelledExponent]
  calc
    (∑ r, MvPolynomial.monomial
        (multispeciesLabelledExponent (relabelMultispeciesModeTuple g r))
        (F (multispeciesUnorderedModeBlock r))) =
      ∑ r, MvPolynomial.monomial
        (multispeciesLabelledExponent (relabelMultispeciesModeTuple g r))
        (F (multispeciesUnorderedModeBlock (relabelMultispeciesModeTuple g r))) := by
          apply Finset.sum_congr rfl
          intro r _
          rw [multispeciesUnordered_relabel]
    _ = ∑ r, MvPolynomial.monomial (multispeciesLabelledExponent r)
        (F (multispeciesUnorderedModeBlock r)) :=
      Equiv.sum_comp (relabelMultispeciesModeTuple g)
        (fun r ↦ MvPolynomial.monomial (multispeciesLabelledExponent r)
          (F (multispeciesUnorderedModeBlock r)))

section SpeciesShift

/-- The species-dependent initial exponent.  Boundary affine currents have shift zero and the
auxiliary `S` species has shift one. -/
def speciesShiftExponent (multiplicity : Species → ℕ) (shift : Species → ℕ) :
    SpeciesLabel multiplicity →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i ↦ shift i.1)

@[simp]
theorem speciesShiftExponent_apply {multiplicity : Species → ℕ}
    (shift : Species → ℕ) (i : SpeciesLabel multiplicity) :
    speciesShiftExponent multiplicity shift i = shift i.1 := by
  simp [speciesShiftExponent]

/-- The exponent vector after applying the initial shift of each species. -/
def shiftedMultispeciesLabelledExponent {jetOrder : ℕ}
    {multiplicity : Species → ℕ} (shift : Species → ℕ)
    (r : MultispeciesModeTuple jetOrder multiplicity) :
    SpeciesLabel multiplicity →₀ ℕ :=
  speciesShiftExponent multiplicity shift + multispeciesLabelledExponent r

/-- Concrete multispecies polynomial with a species-dependent initial exponent. -/
def shiftedMultispeciesParticlePolynomial {jetOrder : ℕ}
    {multiplicity : Species → ℕ} (shift : Species → ℕ)
    (F : MultispeciesJetParticleSpace K jetOrder multiplicity) :
    MvPolynomial (SpeciesLabel multiplicity) K :=
  ∑ r : MultispeciesModeTuple jetOrder multiplicity,
    MvPolynomial.monomial (shiftedMultispeciesLabelledExponent shift r)
      (F (multispeciesUnorderedModeBlock r))

/-- The initial species shifts factor as one explicit monomial. -/
theorem shiftedMultispeciesParticlePolynomial_factor {jetOrder : ℕ}
    {multiplicity : Species → ℕ} (shift : Species → ℕ)
    (F : MultispeciesJetParticleSpace K jetOrder multiplicity) :
    shiftedMultispeciesParticlePolynomial shift F =
      MvPolynomial.monomial (speciesShiftExponent multiplicity shift) 1 *
        multispeciesParticlePolynomial F := by
  classical
  rw [shiftedMultispeciesParticlePolynomial, multispeciesParticlePolynomial,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [MvPolynomial.monomial_mul]
  simp [shiftedMultispeciesLabelledExponent]

/-- Adding a fixed species-shift monomial does not destroy injectivity. -/
theorem shiftedMultispeciesParticlePolynomial_injective {jetOrder : ℕ}
    {multiplicity : Species → ℕ} (shift : Species → ℕ) :
    Function.Injective
      (shiftedMultispeciesParticlePolynomial shift :
        MultispeciesJetParticleSpace K jetOrder multiplicity →
          MvPolynomial (SpeciesLabel multiplicity) K) := by
  intro F G h
  rw [shiftedMultispeciesParticlePolynomial_factor,
    shiftedMultispeciesParticlePolynomial_factor] at h
  apply multispeciesParticlePolynomial_injective
  apply mul_left_cancel₀ (a := MvPolynomial.monomial
    (speciesShiftExponent multiplicity shift) 1)
  · simp
  · exact h

end SpeciesShift

section FixedDerivativeDegree

/-- Extend a fixed derivative-degree sector by zero to the full fixed-multidegree coefficient
space. -/
def extendFixedMultispeciesSector {jetOrder derivativeDegree : ℕ}
    {multiplicity : Species → ℕ}
    (F : MultispeciesParticleSector K jetOrder multiplicity derivativeDegree) :
    MultispeciesJetParticleSpace K jetOrder multiplicity :=
  fun b ↦ if h : multispeciesModeDegree b = derivativeDegree then F ⟨b, h⟩ else 0

@[simp]
theorem extendFixedMultispeciesSector_apply
    {jetOrder derivativeDegree : ℕ} {multiplicity : Species → ℕ}
    (F : MultispeciesParticleSector K jetOrder multiplicity derivativeDegree)
    (b : FixedMultispeciesModeConfiguration jetOrder multiplicity derivativeDegree) :
    extendFixedMultispeciesSector F b = F b := by
  simp [extendFixedMultispeciesSector, b.2]

/-- Polynomial realization of one fixed multidegree and derivative degree. -/
def fixedMultispeciesParticlePolynomial {jetOrder derivativeDegree : ℕ}
    {multiplicity : Species → ℕ}
    (F : MultispeciesParticleSector K jetOrder multiplicity derivativeDegree) :
    MvPolynomial (SpeciesLabel multiplicity) K :=
  multispeciesParticlePolynomial (extendFixedMultispeciesSector F)

/-- The fixed-multidegree, fixed-derivative-degree polynomial realization is injective. -/
theorem fixedMultispeciesParticlePolynomial_injective
    {jetOrder derivativeDegree : ℕ} {multiplicity : Species → ℕ} :
    Function.Injective
      (fixedMultispeciesParticlePolynomial :
        MultispeciesParticleSector K jetOrder multiplicity derivativeDegree →
          MvPolynomial (SpeciesLabel multiplicity) K) := by
  intro F G h
  have hext := multispeciesParticlePolynomial_injective h
  funext b
  have hb := congrFun hext b
  simpa using hb

end FixedDerivativeDegree

section BoundaryFourSpecies

/-- The four species in the boundary affine auxiliary algebra. -/
inductive BoundarySpecies
  | X
  | Y
  | Z
  | S
deriving DecidableEq

instance boundarySpeciesFintype : Fintype BoundarySpecies where
  elems := {.X, .Y, .Z, .S}
  complete A := by cases A <;> simp

/-- Multiplicity function `(a,b,c,d)` for the species `X,Y,Z,S`. -/
def boundaryMultiplicity (a b c d : ℕ) : BoundarySpecies → ℕ
  | .X => a
  | .Y => b
  | .Z => c
  | .S => d

/-- Initial field-power shift: zero for the currents and one for the shifted `S` field. -/
def boundarySpeciesShift : BoundarySpecies → ℕ
  | .X | .Y | .Z => 0
  | .S => 1

@[simp]
theorem boundarySpeciesShift_X : boundarySpeciesShift .X = 0 := rfl

@[simp]
theorem boundarySpeciesShift_Y : boundarySpeciesShift .Y = 0 := rfl

@[simp]
theorem boundarySpeciesShift_Z : boundarySpeciesShift .Z = 0 := rfl

@[simp]
theorem boundarySpeciesShift_S : boundarySpeciesShift .S = 1 := rfl

/-- Concrete labelled polynomial for the exact boundary-affine multidegree `(a,b,c,d)` and
derivative degree. -/
def boundaryFixedParticlePolynomial (jetOrder derivativeDegree a b c d : ℕ)
    (F : MultispeciesParticleSector K jetOrder
      (boundaryMultiplicity a b c d) derivativeDegree) :
    MvPolynomial (SpeciesLabel (boundaryMultiplicity a b c d)) K :=
  shiftedMultispeciesParticlePolynomial boundarySpeciesShift
    (extendFixedMultispeciesSector F)

/-- The concrete four-species realization loses no coefficient in a fixed multidegree and
derivative degree. -/
theorem boundaryFixedParticlePolynomial_injective
    (jetOrder derivativeDegree a b c d : ℕ) :
    Function.Injective
      (boundaryFixedParticlePolynomial (K := K)
        jetOrder derivativeDegree a b c d) := by
  intro F G h
  have hext := shiftedMultispeciesParticlePolynomial_injective
    (K := K) (jetOrder := jetOrder)
    (multiplicity := boundaryMultiplicity a b c d) boundarySpeciesShift
    (by simpa [boundaryFixedParticlePolynomial] using h)
  funext b
  have hb := congrFun hext b
  simpa using hb

/-- In the boundary specialization, the explicit shift exponent is one exactly on `S` labels and
zero on current labels. -/
theorem boundaryShiftExponent_apply (a b c d : ℕ)
    (i : SpeciesLabel (boundaryMultiplicity a b c d)) :
    speciesShiftExponent (boundaryMultiplicity a b c d) boundarySpeciesShift i =
      if i.1 = .S then 1 else 0 := by
  rcases i with ⟨A, i⟩
  cases A <;> simp [boundarySpeciesShift]

end BoundaryFourSpecies

end

end VOA.MultispeciesParticlePolynomial
