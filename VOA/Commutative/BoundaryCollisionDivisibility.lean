/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Commutative.BoundaryTypedSubstitution
import VOA.Commutative.CollisionCommonFactors
import Mathlib.Logic.Equiv.Fintype

/-!
# Boundary typed substitutions and collision divisibility

This file identifies the typed `XZ` and `YY` substitutions with the literal collision maps from
`CollisionCommonFactors.lean`, up to a relabeling equivalence of the residual variables.  It then
exports exact factor criteria for each typed summand.

The polarized relation is different: it asserts equality of the two typed diagonal images, not
vanishing of either image.  Accordingly no individual `XZ` or `YY` factor is deduced from cone
compatibility.  This distinction retains the ordered-square normalization of the `YY` channel.
-/

namespace VOA.BoundaryCollisionDivisibility

open MvPolynomial
open VOA.BoundaryTypedSubstitution
open VOA.CollisionCommonFactors
open VOA.ModeParticlePairing
open VOA.MultispeciesParticlePolynomial

noncomputable section

universe u

variable {K : Type u} [Field K]

section ResidualLabels

theorem newXZLabelZ_ne_newXZLabelX (a b c d : ℕ) :
    newXZLabelZ a b c d ≠ newXZLabelX a b c d := by
  simp [newXZLabelZ, newXZLabelX]

theorem newYYLabelOne_ne_newYYLabelZero (a b c d : ℕ) :
    newYYLabelOne a b c d ≠ newYYLabelZero a b c d := by
  intro h
  have hv := congrArg (fun q : YYLabel a b c d ↦ (q.2 : ℕ)) h
  change ((1 : Fin (b + 2)) : ℕ) = ((0 : Fin (b + 2)) : ℕ) at hv
  norm_num at hv

theorem liftXZPassiveLabel_ne_newXZLabelX (a b c d : ℕ)
    (i : SpeciesLabel (boundaryMultiplicity a b c d)) :
    liftXZPassiveLabel a b c d i ≠ newXZLabelX a b c d := by
  intro h
  rcases i with ⟨A, i⟩
  cases A
  · have hv := congrArg (fun q : XZLabel a b c d ↦ (q.2 : ℕ)) h
    change ((i.succ : Fin (a + 1)) : ℕ) = ((0 : Fin (a + 1)) : ℕ) at hv
    simp at hv
  · simp [liftXZPassiveLabel, newXZLabelX] at h
  · simp [liftXZPassiveLabel, newXZLabelX] at h
  · simp [liftXZPassiveLabel, newXZLabelX] at h

theorem liftYYPassiveLabel_ne_newYYLabelZero (a b c d : ℕ)
    (i : SpeciesLabel (boundaryMultiplicity a b c d)) :
    liftYYPassiveLabel a b c d i ≠ newYYLabelZero a b c d := by
  intro h
  rcases i with ⟨A, i⟩
  cases A
  · simp [liftYYPassiveLabel, newYYLabelZero] at h
  · have hv := congrArg (fun q : YYLabel a b c d ↦ (q.2 : ℕ)) h
    change ((i.succ.succ : Fin (b + 2)) : ℕ) = ((0 : Fin (b + 2)) : ℕ) at hv
    simp at hv
  · simp [liftYYPassiveLabel, newYYLabelZero] at h
  · simp [liftYYPassiveLabel, newYYLabelZero] at h

/-- The typed diagonal labels are exactly the `XZ` labels remaining after deleting the active
`X` label; the active `Z` label represents the common collision coordinate. -/
def xzResidualEquiv (a b c d : ℕ) :
    {i : XZLabel a b c d // i ≠ newXZLabelX a b c d} ≃
      BoundaryDiagonalLabel a b c d where
  toFun i := xzToDiagonalLabel a b c d i
  invFun
    | Sum.inl () => ⟨newXZLabelZ a b c d, newXZLabelZ_ne_newXZLabelX a b c d⟩
    | Sum.inr i =>
        ⟨liftXZPassiveLabel a b c d i, liftXZPassiveLabel_ne_newXZLabelX a b c d i⟩
  left_inv i := by
    rcases i with ⟨⟨A, i⟩, hi⟩
    apply Subtype.ext
    cases A
    · revert hi
      refine Fin.cases ?_ (fun _ _ ↦ ?_) i
      · intro hi
        exact False.elim (hi rfl)
      · rfl
    · rfl
    · revert hi
      refine Fin.cases (fun _ ↦ ?_) (fun _ _ ↦ ?_) i <;> rfl
    · rfl
  right_inv i := by
    rcases i with (_ | i)
    · rfl
    · rcases i with ⟨A, i⟩
      cases A <;> rfl

/-- The typed diagonal labels are exactly the `YY` labels remaining after deleting the first
active `Y` label; the second active `Y` label represents the common collision coordinate. -/
def yyResidualEquiv (a b c d : ℕ) :
    {i : YYLabel a b c d // i ≠ newYYLabelZero a b c d} ≃
      BoundaryDiagonalLabel a b c d where
  toFun i := yyToDiagonalLabel a b c d i
  invFun
    | Sum.inl () => ⟨newYYLabelOne a b c d, newYYLabelOne_ne_newYYLabelZero a b c d⟩
    | Sum.inr i =>
        ⟨liftYYPassiveLabel a b c d i, liftYYPassiveLabel_ne_newYYLabelZero a b c d i⟩
  left_inv i := by
    rcases i with ⟨⟨A, i⟩, hi⟩
    apply Subtype.ext
    cases A
    · rfl
    · revert hi
      refine Fin.cases ?_ (fun j hi ↦ ?_) i
      · intro hi
        exact False.elim (hi rfl)
      · revert hi
        refine Fin.cases (fun _ ↦ ?_) (fun _ _ ↦ ?_) j <;> rfl
    · rfl
    · rfl
  right_inv i := by
    rcases i with (_ | i)
    · rfl
    · rcases i with ⟨A, i⟩
      cases A <;> rfl

end ResidualLabels

section Factorization

theorem xzToDiagonalLabel_eq_residual_collisionIndex (a b c d : ℕ)
    (i : XZLabel a b c d) :
    xzToDiagonalLabel a b c d i =
      xzResidualEquiv a b c d
        (collisionIndex (newXZLabelX a b c d) (newXZLabelZ a b c d)
          (newXZLabelZ_ne_newXZLabelX a b c d) i) := by
  rcases i with ⟨A, i⟩
  cases A
  · refine Fin.cases ?_ (fun _ ↦ ?_) i <;>
      rfl
  · rfl
  · refine Fin.cases ?_ (fun _ ↦ ?_) i <;>
      rfl
  · rfl

theorem yyToDiagonalLabel_eq_residual_collisionIndex (a b c d : ℕ)
    (i : YYLabel a b c d) :
    yyToDiagonalLabel a b c d i =
      yyResidualEquiv a b c d
        (collisionIndex (newYYLabelZero a b c d) (newYYLabelOne a b c d)
          (newYYLabelOne_ne_newYYLabelZero a b c d) i) := by
  rcases i with ⟨A, i⟩
  cases A
  · rfl
  · refine Fin.cases ?_ (fun j ↦ ?_) i
    · rfl
    · refine Fin.cases ?_ (fun _ ↦ ?_) j <;>
        rfl
  · rfl
  · rfl

/-- The typed `XZ` substitution is the literal collision map followed by a bijective relabeling
of the residual variables. -/
theorem xzDiagonalSubstitution_eq_rename_collisionMap (a b c d : ℕ)
    (p : MvPolynomial (XZLabel a b c d) K) :
    xzDiagonalSubstitution (K := K) a b c d p =
      MvPolynomial.rename (xzResidualEquiv a b c d)
        (collisionMap (K := K) (newXZLabelX a b c d) (newXZLabelZ a b c d)
          (newXZLabelZ_ne_newXZLabelX a b c d) p) := by
  suffices hhom :
      xzDiagonalSubstitution (K := K) a b c d =
        (MvPolynomial.rename (xzResidualEquiv a b c d)).comp
          (collisionMap (K := K) (newXZLabelX a b c d) (newXZLabelZ a b c d)
            (newXZLabelZ_ne_newXZLabelX a b c d)) by
    exact DFunLike.congr_fun hhom p
  apply MvPolynomial.algHom_ext
  intro i
  simp only [xzDiagonalSubstitution, collisionMap, AlgHom.comp_apply,
    MvPolynomial.rename_X]
  rw [xzToDiagonalLabel_eq_residual_collisionIndex]

/-- The typed `YY` substitution is the literal collision map followed by a bijective relabeling
of the residual variables. -/
theorem yyDiagonalSubstitution_eq_rename_collisionMap (a b c d : ℕ)
    (p : MvPolynomial (YYLabel a b c d) K) :
    yyDiagonalSubstitution (K := K) a b c d p =
      MvPolynomial.rename (yyResidualEquiv a b c d)
        (collisionMap (K := K) (newYYLabelZero a b c d) (newYYLabelOne a b c d)
          (newYYLabelOne_ne_newYYLabelZero a b c d) p) := by
  suffices hhom :
      yyDiagonalSubstitution (K := K) a b c d =
        (MvPolynomial.rename (yyResidualEquiv a b c d)).comp
          (collisionMap (K := K) (newYYLabelZero a b c d) (newYYLabelOne a b c d)
            (newYYLabelOne_ne_newYYLabelZero a b c d)) by
    exact DFunLike.congr_fun hhom p
  apply MvPolynomial.algHom_ext
  intro i
  simp only [yyDiagonalSubstitution, collisionMap, AlgHom.comp_apply,
    MvPolynomial.rename_X]
  rw [yyToDiagonalLabel_eq_residual_collisionIndex]

/-- Exact factor criterion for the active `XZ` collision in its typed polynomial sector. -/
theorem xzCollisionFactor_dvd_iff (a b c d : ℕ)
    (p : MvPolynomial (XZLabel a b c d) K) :
    collisionFactor (K := K) (newXZLabelX a b c d) (newXZLabelZ a b c d) ∣ p ↔
      xzDiagonalSubstitution (K := K) a b c d p = 0 := by
  rw [xzDiagonalSubstitution_eq_rename_collisionMap]
  have hzero :
      MvPolynomial.rename (xzResidualEquiv a b c d)
          (collisionMap (K := K) (newXZLabelX a b c d) (newXZLabelZ a b c d)
            (newXZLabelZ_ne_newXZLabelX a b c d) p) = 0 ↔
        collisionMap (K := K) (newXZLabelX a b c d) (newXZLabelZ a b c d)
            (newXZLabelZ_ne_newXZLabelX a b c d) p = 0 := by
    constructor
    · intro h
      apply MvPolynomial.rename_injective (xzResidualEquiv a b c d)
        (xzResidualEquiv a b c d).injective
      simpa using h
    · intro h
      simp [h]
  rw [hzero]
  exact collisionFactor_dvd_iff _ _ (newXZLabelZ_ne_newXZLabelX a b c d) p

/-- Exact factor criterion for the active `YY` collision in its typed polynomial sector.  This
is a polynomial statement; the ordered-convolution multiplicities remain in the coefficient map
which supplies the diagonal hypothesis. -/
theorem yyCollisionFactor_dvd_iff (a b c d : ℕ)
    (p : MvPolynomial (YYLabel a b c d) K) :
    collisionFactor (K := K) (newYYLabelZero a b c d) (newYYLabelOne a b c d) ∣ p ↔
      yyDiagonalSubstitution (K := K) a b c d p = 0 := by
  rw [yyDiagonalSubstitution_eq_rename_collisionMap]
  have hzero :
      MvPolynomial.rename (yyResidualEquiv a b c d)
          (collisionMap (K := K) (newYYLabelZero a b c d) (newYYLabelOne a b c d)
            (newYYLabelOne_ne_newYYLabelZero a b c d) p) = 0 ↔
        collisionMap (K := K) (newYYLabelZero a b c d) (newYYLabelOne a b c d)
            (newYYLabelOne_ne_newYYLabelZero a b c d) p = 0 := by
    constructor
    · intro h
      apply MvPolynomial.rename_injective (yyResidualEquiv a b c d)
        (yyResidualEquiv a b c d).injective
      simpa using h
    · intro h
      simp [h]
  rw [hzero]
  exact collisionFactor_dvd_iff _ _ (newYYLabelOne_ne_newYYLabelZero a b c d) p

/-- Polarized compatibility is vanishing of the difference in the common typed target.  It does
not say that either typed summand vanishes separately. -/
theorem isPolarizedDiagonalCompatible_iff_sub_eq_zero (a b c d : ℕ)
    (p : PolarizedPolynomialSource (K := K) a b c d) :
    IsPolarizedDiagonalCompatible (K := K) a b c d p ↔
      xzDiagonalSubstitution (K := K) a b c d p.1 -
        yyDiagonalSubstitution (K := K) a b c d p.2 = 0 := by
  exact sub_eq_zero.symm

section YYNormalization

/-- Exponent vector supported on the two active `Y` labels. -/
def activeYYExponent (a b c d r s : ℕ) : YYLabel a b c d →₀ ℕ :=
  Finsupp.single (newYYLabelZero a b c d) r +
    Finsupp.single (newYYLabelOne a b c d) s

/-- Identifying the two active `Y` labels adds their exponents. -/
theorem mapDomain_activeYYExponent (a b c d r s : ℕ) :
    Finsupp.mapDomain (yyToDiagonalLabel a b c d) (activeYYExponent a b c d r s) =
      Finsupp.single (Sum.inl () : BoundaryDiagonalLabel a b c d) (r + s) := by
  rw [activeYYExponent, Finsupp.mapDomain_add,
    Finsupp.mapDomain_single, Finsupp.mapDomain_single,
    yyToDiagonalLabel_newY_zero, yyToDiagonalLabel_newY_one,
    Finsupp.single_add]

/-- One labelled ordered `YY` monomial maps to the common collision monomial of exponent
`r+s`. -/
theorem yyDiagonalSubstitution_monomial_active (a b c d r s : ℕ) (u : K) :
    yyDiagonalSubstitution (K := K) a b c d
        (MvPolynomial.monomial (activeYYExponent a b c d r s) u) =
      MvPolynomial.monomial
        (Finsupp.single (Sum.inl () : BoundaryDiagonalLabel a b c d) (r + s)) u := by
  rw [yyDiagonalSubstitution, MvPolynomial.rename_monomial,
    mapDomain_activeYYExponent]

/-- The two off-diagonal ordered label assignments have the same diagonal image and therefore
add with coefficient `2`.  This is the polynomial form of the `YY` normalization. -/
theorem yyDiagonalSubstitution_two_orders (a b c d r s : ℕ) (u : K) :
    yyDiagonalSubstitution (K := K) a b c d
        (MvPolynomial.monomial (activeYYExponent a b c d r s) u +
          MvPolynomial.monomial (activeYYExponent a b c d s r) u) =
      MvPolynomial.monomial
        (Finsupp.single (Sum.inl () : BoundaryDiagonalLabel a b c d) (r + s)) (2 * u) := by
  rw [map_add, yyDiagonalSubstitution_monomial_active,
    yyDiagonalSubstitution_monomial_active, add_comm s r,
    ← map_add]
  congr 1
  exact (two_mul u).symm

/-- On the exponent diagonal there is one ordered assignment, hence no extra factor `2`. -/
theorem yyDiagonalSubstitution_diagonal_order (a b c d r : ℕ) (u : K) :
    yyDiagonalSubstitution (K := K) a b c d
        (MvPolynomial.monomial (activeYYExponent a b c d r r) u) =
      MvPolynomial.monomial
        (Finsupp.single (Sum.inl () : BoundaryDiagonalLabel a b c d) (r + r)) u :=
  yyDiagonalSubstitution_monomial_active a b c d r r u

end YYNormalization

end Factorization

section SameSpeciesSymmetry

/-- Transpose two labels in one boundary species and fix every other species. -/
def boundarySpeciesTransposition (multiplicity : BoundarySpecies → ℕ)
    (A : BoundarySpecies) (i j : Fin (multiplicity A)) :
    SpeciesPermutation multiplicity :=
  fun B ↦ if h : B = A then by
    subst B
    exact Equiv.swap i j
  else Equiv.refl _

/-- The dependent species permutation is literally the transposition of the corresponding two
labels in the flattened label type. -/
theorem speciesLabelEquiv_boundarySpeciesTransposition
    (multiplicity : BoundarySpecies → ℕ)
    (A : BoundarySpecies) (i j : Fin (multiplicity A)) :
    speciesLabelEquiv (boundarySpeciesTransposition multiplicity A i j) =
      Equiv.swap (⟨A, i⟩ : SpeciesLabel multiplicity) ⟨A, j⟩ := by
  apply Equiv.ext
  intro q
  rcases q with ⟨B, k⟩
  by_cases hBA : B = A
  · subst B
    by_cases hki : k = i
    · subst k
      simp [speciesLabelEquiv, boundarySpeciesTransposition]
    · by_cases hkj : k = j
      · subst k
        simp [speciesLabelEquiv, boundarySpeciesTransposition]
      · have hqI : (⟨A, k⟩ : SpeciesLabel multiplicity) ≠ ⟨A, i⟩ := by
          intro h
          apply hki
          apply Fin.ext
          exact congrArg (fun q : SpeciesLabel multiplicity ↦ (q.2 : ℕ)) h
        have hqJ : (⟨A, k⟩ : SpeciesLabel multiplicity) ≠ ⟨A, j⟩ := by
          intro h
          apply hkj
          apply Fin.ext
          exact congrArg (fun q : SpeciesLabel multiplicity ↦ (q.2 : ℕ)) h
        simp only [speciesLabelEquiv]
        change (⟨A, (boundarySpeciesTransposition multiplicity A i j A) k⟩ :
          SpeciesLabel multiplicity) =
            (Equiv.swap (⟨A, i⟩ : SpeciesLabel multiplicity) ⟨A, j⟩) ⟨A, k⟩
        rw [show boundarySpeciesTransposition multiplicity A i j A =
          Equiv.swap i j by simp [boundarySpeciesTransposition]]
        rw [Equiv.swap_apply_of_ne_of_ne hki hkj,
          Equiv.swap_apply_of_ne_of_ne hqI hqJ]
  · have hqI : (⟨B, k⟩ : SpeciesLabel multiplicity) ≠ ⟨A, i⟩ := by
      intro h
      exact hBA (congrArg Sigma.fst h)
    have hqJ : (⟨B, k⟩ : SpeciesLabel multiplicity) ≠ ⟨A, j⟩ := by
      intro h
      exact hBA (congrArg Sigma.fst h)
    simp [speciesLabelEquiv, boundarySpeciesTransposition, hBA,
      Equiv.swap_apply_of_ne_of_ne hqI hqJ]

/-- A species-dependent initial exponent is fixed by every within-species relabeling. -/
theorem mapDomain_speciesShiftExponent_speciesLabelEquiv
    (multiplicity : BoundarySpecies → ℕ) (shift : BoundarySpecies → ℕ)
    (g : SpeciesPermutation multiplicity) :
    Finsupp.mapDomain (speciesLabelEquiv g) (speciesShiftExponent multiplicity shift) =
      speciesShiftExponent multiplicity shift := by
  rw [← Finsupp.equivMapDomain_eq_mapDomain]
  ext q
  rcases q with ⟨A, i⟩
  simp [Finsupp.equivMapDomain_apply, speciesLabelEquiv, speciesShiftExponent]

/-- The shifted multispecies particle polynomial is invariant under every within-species
permutation. -/
theorem shiftedMultispeciesParticlePolynomial_rename
    {jetOrder : ℕ} {multiplicity : BoundarySpecies → ℕ}
    (shift : BoundarySpecies → ℕ) (g : SpeciesPermutation multiplicity)
    (F : MultispeciesJetParticleSpace K jetOrder multiplicity) :
    MvPolynomial.rename (speciesLabelEquiv g)
        (shiftedMultispeciesParticlePolynomial shift F) =
      shiftedMultispeciesParticlePolynomial shift F := by
  rw [shiftedMultispeciesParticlePolynomial_factor, map_mul,
    MvPolynomial.rename_monomial,
    mapDomain_speciesShiftExponent_speciesLabelEquiv,
    multispeciesParticlePolynomial_rename]

/-- In particular, the shifted particle polynomial is invariant under transposing two labels of
one species. -/
theorem shiftedMultispeciesParticlePolynomial_swap
    {jetOrder : ℕ} {multiplicity : BoundarySpecies → ℕ}
    (shift : BoundarySpecies → ℕ) (A : BoundarySpecies)
    (i j : Fin (multiplicity A))
    (F : MultispeciesJetParticleSpace K jetOrder multiplicity) :
    swapVariables (K := K) (⟨A, i⟩ : SpeciesLabel multiplicity) ⟨A, j⟩
        (shiftedMultispeciesParticlePolynomial shift F) =
      shiftedMultispeciesParticlePolynomial shift F := by
  rw [swapVariables,
    ← speciesLabelEquiv_boundarySpeciesTransposition multiplicity A i j]
  exact shiftedMultispeciesParticlePolynomial_rename shift
    (boundarySpeciesTransposition multiplicity A i j) F

/-- Divisibility by one collision factor transports along any relabeling which fixes the
polynomial.  This elementary lemma lets separate species-symmetry move a distinguished active
collision to every pair of particle labels. -/
theorem collisionFactor_dvd_of_rename_invariant
    {I : Type*} [DecidableEq I]
    (g : Equiv.Perm I) (p : MvPolynomial I K)
    (hinvariant : MvPolynomial.rename g p = p)
    {i j : I} (hdvd : collisionFactor (K := K) i j ∣ p) :
    collisionFactor (K := K) (g i) (g j) ∣ p := by
  rcases hdvd with ⟨q, hpq⟩
  refine ⟨MvPolynomial.rename g q, ?_⟩
  rw [← hinvariant, hpq, map_mul]
  simp [collisionFactor]

/-- For the actual shifted `YY` particle polynomial, typed diagonal vanishing gives a square
factor because the two active labels belong to the same species.  The factor `2` in the
off-diagonal ordered coefficient sum is already encoded by
`yyDiagonalSubstitution_two_orders`; no division by `2` is inserted here. -/
theorem shiftedYYParticlePolynomial_collisionFactor_sq_dvd [CharZero K]
    {jetOrder a b c d : ℕ}
    (F : MultispeciesJetParticleSpace K jetOrder
      (boundaryMultiplicity a (b + 2) c d))
    (hzero : yyDiagonalSubstitution (K := K) a b c d
      (shiftedMultispeciesParticlePolynomial boundarySpeciesShift F) = 0) :
    collisionFactor (K := K) (newYYLabelZero a b c d) (newYYLabelOne a b c d) ^ 2 ∣
      shiftedMultispeciesParticlePolynomial boundarySpeciesShift F := by
  let p : MvPolynomial (YYLabel a b c d) K :=
    shiftedMultispeciesParticlePolynomial boundarySpeciesShift F
  change yyDiagonalSubstitution (K := K) a b c d p = 0 at hzero
  change collisionFactor (K := K) (newYYLabelZero a b c d)
      (newYYLabelOne a b c d) ^ 2 ∣ p
  have hrenamed : MvPolynomial.rename (yyResidualEquiv a b c d)
      (collisionMap (K := K) (newYYLabelZero a b c d) (newYYLabelOne a b c d)
        (newYYLabelOne_ne_newYYLabelZero a b c d) p) = 0 := by
    simpa [yyDiagonalSubstitution_eq_rename_collisionMap] using hzero
  have hcollision : collisionMap (K := K) (newYYLabelZero a b c d)
      (newYYLabelOne a b c d) (newYYLabelOne_ne_newYYLabelZero a b c d)
      p = 0 := by
    apply MvPolynomial.rename_injective (yyResidualEquiv a b c d)
      (yyResidualEquiv a b c d).injective
    simpa using hrenamed
  have hsymm : swapVariables (K := K) (newYYLabelZero a b c d)
      (newYYLabelOne a b c d) p = p := by
    simpa only [p, newYYLabelZero, newYYLabelOne] using
      (shiftedMultispeciesParticlePolynomial_swap boundarySpeciesShift .Y
        (0 : Fin (b + 2)) (1 : Fin (b + 2)) F)
  exact collisionFactor_sq_dvd_of_swap_invariant
    (newYYLabelZero a b c d) (newYYLabelOne a b c d)
    (newYYLabelOne_ne_newYYLabelZero a b c d) p hsymm hcollision

end SameSpeciesSymmetry

section BoundaryFactors

/-- Inclusion of the labels of one boundary species into the full dependent label type. -/
def boundarySpeciesLabel (a b c d : ℕ) (A : BoundarySpecies) :
    Fin (boundaryMultiplicity a b c d A) →
      SpeciesLabel (boundaryMultiplicity a b c d) :=
  fun i ↦ ⟨A, i⟩

theorem boundarySpeciesLabel_injective (a b c d : ℕ) (A : BoundarySpecies) :
    Function.Injective (boundarySpeciesLabel a b c d A) := by
  intro i j h
  apply Fin.ext
  exact congrArg
    (fun q : SpeciesLabel (boundaryMultiplicity a b c d) ↦ (q.2 : ℕ)) h

theorem boundarySpeciesLabel_disjoint (a b c d : ℕ)
    {A B : BoundarySpecies} (hAB : A ≠ B) (i : Fin (boundaryMultiplicity a b c d A))
    (j : Fin (boundaryMultiplicity a b c d B)) :
    boundarySpeciesLabel a b c d A i ≠ boundarySpeciesLabel a b c d B j := by
  intro h
  exact hAB (congrArg Sigma.fst h)

/-- Apply an arbitrary permutation to the `Y` labels and fix the other three species. -/
def boundaryYPermutation (a b c d : ℕ) (g : Equiv.Perm (Fin b)) :
    SpeciesPermutation (boundaryMultiplicity a b c d)
  | .X => Equiv.refl _
  | .Y => g
  | .Z => Equiv.refl _
  | .S => Equiv.refl _

@[simp]
theorem speciesLabelEquiv_boundaryYPermutation_Y (a b c d : ℕ)
    (g : Equiv.Perm (Fin b)) (i : Fin b) :
    speciesLabelEquiv (boundaryYPermutation a b c d g)
        (⟨.Y, i⟩ : SpeciesLabel (boundaryMultiplicity a b c d)) = ⟨.Y, g i⟩ := by
  rfl

/-- For a shifted multispecies polynomial in the `XZ` source sector, vanishing of the one typed
active diagonal propagates by separate `X`- and `Z`-symmetry to every cross-species collision.
Consequently the complete `X`--`Z` collision product divides the polynomial. -/
theorem shiftedXZParticlePolynomial_crossCollisionProduct_dvd
    {jetOrder a b c d : ℕ}
    (F : MultispeciesJetParticleSpace K jetOrder
      (boundaryMultiplicity (a + 1) b (c + 1) d))
    (hzero : xzDiagonalSubstitution (K := K) a b c d
      (shiftedMultispeciesParticlePolynomial boundarySpeciesShift F) = 0) :
    crossCollisionProduct (K := K)
        (boundarySpeciesLabel (a + 1) b (c + 1) d .X)
        (boundarySpeciesLabel (a + 1) b (c + 1) d .Z) ∣
      shiftedMultispeciesParticlePolynomial boundarySpeciesShift F := by
  let p := shiftedMultispeciesParticlePolynomial boundarySpeciesShift F
  have hactive : collisionFactor (K := K) (newXZLabelX a b c d)
      (newXZLabelZ a b c d) ∣ p :=
    (xzCollisionFactor_dvd_iff a b c d p).2 hzero
  apply crossCollisionProduct_dvd_of_diagonal_vanishing
    (boundarySpeciesLabel (a + 1) b (c + 1) d .X)
    (boundarySpeciesLabel (a + 1) b (c + 1) d .Z)
    (boundarySpeciesLabel_injective (a + 1) b (c + 1) d .X)
    (boundarySpeciesLabel_injective (a + 1) b (c + 1) d .Z)
    (fun i j ↦ boundarySpeciesLabel_disjoint (a + 1) b (c + 1) d
      (by decide : BoundarySpecies.X ≠ BoundarySpecies.Z) i j)
  intro i j hji
  apply (collisionFactor_dvd_iff _ _ hji p).1
  have hmoveX := collisionFactor_dvd_of_rename_invariant
    (speciesLabelEquiv
      (boundarySpeciesTransposition (boundaryMultiplicity (a + 1) b (c + 1) d)
        .X (0 : Fin (a + 1)) i)) p
    (shiftedMultispeciesParticlePolynomial_rename boundarySpeciesShift
      (boundarySpeciesTransposition (boundaryMultiplicity (a + 1) b (c + 1) d)
        .X (0 : Fin (a + 1)) i) F)
    hactive
  have hmoveZ := collisionFactor_dvd_of_rename_invariant
    (speciesLabelEquiv
      (boundarySpeciesTransposition (boundaryMultiplicity (a + 1) b (c + 1) d)
        .Z (0 : Fin (c + 1)) j)) p
    (shiftedMultispeciesParticlePolynomial_rename boundarySpeciesShift
      (boundarySpeciesTransposition (boundaryMultiplicity (a + 1) b (c + 1) d)
        .Z (0 : Fin (c + 1)) j) F)
    hmoveX
  simpa [speciesLabelEquiv_boundarySpeciesTransposition, newXZLabelX, newXZLabelZ,
    boundarySpeciesLabel] using hmoveZ

/-- For a shifted multispecies polynomial in the `YY` source sector, vanishing of the one typed
active diagonal propagates by `Y`-species symmetry to every pair of `Y` labels.  The complete
squared `Y` Vandermonde therefore divides the polynomial. -/
theorem shiftedYYParticlePolynomial_vandermondeAlong_sq_dvd [CharZero K]
    {jetOrder a b c d : ℕ}
    (F : MultispeciesJetParticleSpace K jetOrder
      (boundaryMultiplicity a (b + 2) c d))
    (hzero : yyDiagonalSubstitution (K := K) a b c d
      (shiftedMultispeciesParticlePolynomial boundarySpeciesShift F) = 0) :
    vandermondeAlong (K := K)
        (boundarySpeciesLabel a (b + 2) c d .Y) ^ 2 ∣
      shiftedMultispeciesParticlePolynomial boundarySpeciesShift F := by
  let p := shiftedMultispeciesParticlePolynomial boundarySpeciesShift F
  have hactive : collisionFactor (K := K) (newYYLabelZero a b c d)
      (newYYLabelOne a b c d) ∣ p :=
    (yyCollisionFactor_dvd_iff a b c d p).2 hzero
  apply vandermondeAlong_sq_dvd_of_symmetric_diagonal_vanishing
    (boundarySpeciesLabel a (b + 2) c d .Y)
    (boundarySpeciesLabel_injective a (b + 2) c d .Y)
  · intro i j
    exact shiftedMultispeciesParticlePolynomial_swap boundarySpeciesShift .Y i j F
  · intro i j hji
    apply (collisionFactor_dvd_iff _ _ hji p).1
    have hjiFin : j ≠ i := by
      intro hij
      subst j
      exact hji rfl
    let source : Bool → Fin (b + 2) := fun t => if t then 1 else 0
    let target : Bool → Fin (b + 2) := fun t => if t then j else i
    have hsource : Function.Injective source := by
      intro s t
      cases s <;> cases t <;> simp [source]
    have htarget : Function.Injective target := by
      intro s t hst
      cases s <;> cases t
      · rfl
      · exfalso
        exact hjiFin hst.symm
      · exfalso
        exact hjiFin hst
      · rfl
    obtain ⟨g, hg⟩ := Equiv.Perm.exists_extending_pair source target hsource htarget
    have hg0 : g (0 : Fin (b + 2)) = i := by
      simpa [source, target] using hg false
    have hg1 : g (1 : Fin (b + 2)) = j := by
      simpa [source, target] using hg true
    have hmove := collisionFactor_dvd_of_rename_invariant
      (speciesLabelEquiv (boundaryYPermutation a (b + 2) c d g)) p
      (shiftedMultispeciesParticlePolynomial_rename boundarySpeciesShift
        (boundaryYPermutation a (b + 2) c d g) F)
      hactive
    simpa [newYYLabelZero, newYYLabelOne, boundarySpeciesLabel, hg0, hg1] using hmove

/-- Every fixed boundary particle polynomial is symmetric separately in the labels of each
species. -/
theorem boundaryFixedParticlePolynomial_swap
    {jetOrder derivativeDegree a b c d : ℕ}
    (A : BoundarySpecies) (i j : Fin (boundaryMultiplicity a b c d A))
    (F : MultispeciesParticleSector K jetOrder
      (boundaryMultiplicity a b c d) derivativeDegree) :
    swapVariables (K := K) (boundarySpeciesLabel a b c d A i)
        (boundarySpeciesLabel a b c d A j)
        (boundaryFixedParticlePolynomial jetOrder derivativeDegree a b c d F) =
      boundaryFixedParticlePolynomial jetOrder derivativeDegree a b c d F := by
  exact shiftedMultispeciesParticlePolynomial_swap boundarySpeciesShift A i j
    (extendFixedMultispeciesSector F)

/-- Literal cross-species collision vanishings for a boundary particle polynomial give the full
cross-species collision product. -/
theorem boundaryFixedParticlePolynomial_crossCollisionProduct_dvd
    {jetOrder derivativeDegree a b c d : ℕ}
    {A B : BoundarySpecies} (hAB : A ≠ B)
    (F : MultispeciesParticleSector K jetOrder
      (boundaryMultiplicity a b c d) derivativeDegree)
    (hvanish : ∀ i j, ∀ hji :
      boundarySpeciesLabel a b c d B j ≠ boundarySpeciesLabel a b c d A i,
      collisionMap (K := K) (boundarySpeciesLabel a b c d A i)
        (boundarySpeciesLabel a b c d B j) hji
        (boundaryFixedParticlePolynomial jetOrder derivativeDegree a b c d F) = 0) :
    crossCollisionProduct (K := K) (boundarySpeciesLabel a b c d A)
        (boundarySpeciesLabel a b c d B) ∣
      boundaryFixedParticlePolynomial jetOrder derivativeDegree a b c d F := by
  apply crossCollisionProduct_dvd_of_diagonal_vanishing
    (boundarySpeciesLabel a b c d A) (boundarySpeciesLabel a b c d B)
    (boundarySpeciesLabel_injective a b c d A)
    (boundarySpeciesLabel_injective a b c d B)
    (fun i j ↦ boundarySpeciesLabel_disjoint a b c d hAB i j)
  exact hvanish

/-- Same-species diagonal vanishings for a boundary particle polynomial give the square of that
species' Vandermonde. -/
theorem boundaryFixedParticlePolynomial_vandermondeAlong_sq_dvd [CharZero K]
    {jetOrder derivativeDegree a b c d : ℕ}
    (A : BoundarySpecies)
    (F : MultispeciesParticleSector K jetOrder
      (boundaryMultiplicity a b c d) derivativeDegree)
    (hvanish : ∀ i j, ∀ hji :
      boundarySpeciesLabel a b c d A j ≠ boundarySpeciesLabel a b c d A i,
      collisionMap (K := K) (boundarySpeciesLabel a b c d A i)
        (boundarySpeciesLabel a b c d A j) hji
        (boundaryFixedParticlePolynomial jetOrder derivativeDegree a b c d F) = 0) :
    vandermondeAlong (K := K) (boundarySpeciesLabel a b c d A) ^ 2 ∣
      boundaryFixedParticlePolynomial jetOrder derivativeDegree a b c d F := by
  apply vandermondeAlong_sq_dvd_of_symmetric_diagonal_vanishing
    (boundarySpeciesLabel a b c d A)
    (boundarySpeciesLabel_injective a b c d A)
  · intro i j
    exact boundaryFixedParticlePolynomial_swap A i j F
  · exact hvanish

end BoundaryFactors

end


end VOA.BoundaryCollisionDivisibility
