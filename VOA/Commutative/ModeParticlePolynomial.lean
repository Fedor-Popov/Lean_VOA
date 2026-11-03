/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Data.List.FinRange
import VOA.Commutative.AuxiliaryIdealOrthogonal

/-!
# Polynomial realization of finite particle coefficients

`ModeParticlePairing.lean` constructs the exact finite coefficient model for same-species
symmetric labelled particles.  This file maps that model into an actual multivariable polynomial
ring.  A coefficient family on unordered mode configurations is repeated on every labelled
ordering of the corresponding exponent multiset.

The coefficient theorem and injectivity theorem below show that no information is lost.  For the
shifted field `S(z)=sum_(r>=1) S_r z^r`, every labelled exponent is increased by one; the resulting
polynomial factors by the monomial having exponent one in every particle coordinate.  This is the
coefficient-level content of divisibility by the product of the `S` coordinates.

The realization is invariant under arbitrary same-species relabelings.  Its image is characterized
exactly as the finite-jet-supported coefficient-symmetric polynomials.  Relating that
coefficientwise symmetry predicate to an independently defined invariant-subring API, and taking
the product over several species, are left to a later file.  No carrier or classical-freeness
claim is made here.
-/

namespace VOA.ModeParticlePolynomial

open VOA.ModeParticlePairing

noncomputable section

universe u

variable {K : Type u} [Field K]

/-- The labelled monomial exponent vector associated with a labelled tuple of divided-derivative
mode indices. -/
def labelledExponent {jetOrder n : ℕ}
    (r : Fin n → Fin (jetOrder + 1)) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i ↦ (r i : ℕ))

@[simp]
theorem labelledExponent_apply {jetOrder n : ℕ}
    (r : Fin n → Fin (jetOrder + 1)) (i : Fin n) :
    labelledExponent r i = (r i : ℕ) := by
  simp [labelledExponent]

/-- Labelled exponent tuples remember every mode index. -/
theorem labelledExponent_injective {jetOrder n : ℕ} :
    Function.Injective
      (labelledExponent : (Fin n → Fin (jetOrder + 1)) → Fin n →₀ ℕ) := by
  intro r s h
  funext i
  apply Fin.ext
  have hi := congrArg (fun e : Fin n →₀ ℕ ↦ e i) h
  simpa using hi

/-- The polynomial obtained by repeating an unordered coefficient on every labelled ordering of
its exponent multiset. -/
def labelledParticlePolynomial {jetOrder n : ℕ}
    (F : JetParticleSpace K jetOrder n) : MvPolynomial (Fin n) K :=
  ∑ r : Fin n → Fin (jetOrder + 1),
    MvPolynomial.monomial (labelledExponent r) (F (unorderedModeBlock r))

/-- Coefficient recovery at every labelled exponent tuple. -/
theorem coeff_labelledParticlePolynomial {jetOrder n : ℕ}
    (F : JetParticleSpace K jetOrder n)
    (r : Fin n → Fin (jetOrder + 1)) :
    MvPolynomial.coeff (labelledExponent r) (labelledParticlePolynomial F) =
      F (unorderedModeBlock r) := by
  classical
  rw [labelledParticlePolynomial, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  rw [Finset.sum_eq_single r]
  · simp
  · intro s _ hs
    rw [if_neg (fun h ↦ hs (labelledExponent_injective h))]
  · simp

/-- Choose one labelled ordering of an unordered finite mode configuration. -/
def orderedRepresentative {jetOrder n : ℕ} (b : ModeConfiguration jetOrder n) :
    Fin n → Fin (jetOrder + 1) :=
  (Quotient.out (Sym.symEquivSym' b)).get

/-- Forgetting the order of the chosen representative recovers the original configuration. -/
theorem unorderedModeBlock_orderedRepresentative {jetOrder n : ℕ}
    (b : ModeConfiguration jetOrder n) :
    unorderedModeBlock (orderedRepresentative b) = b := by
  apply Sym.symEquivSym'.injective
  change Quotient.mk'' (List.Vector.ofFn (orderedRepresentative b)) = Sym.symEquivSym' b
  rw [show List.Vector.ofFn (orderedRepresentative b) =
      Quotient.out (Sym.symEquivSym' b) by
    apply List.Vector.ext
    intro i
    simp [orderedRepresentative]]
  exact Quotient.out_eq _

/-- The labelled polynomial realization is injective.  Thus the coefficient model in
`ModeParticlePairing.lean` is a concrete polynomial model, not merely a dimension count. -/
theorem labelledParticlePolynomial_injective {jetOrder n : ℕ} :
    Function.Injective
      (labelledParticlePolynomial :
        JetParticleSpace K jetOrder n → MvPolynomial (Fin n) K) := by
  intro F G h
  funext b
  let r := orderedRepresentative b
  have hc := congrArg (MvPolynomial.coeff (labelledExponent r)) h
  rw [coeff_labelledParticlePolynomial, coeff_labelledParticlePolynomial] at hc
  have hr : unorderedModeBlock r = b := unorderedModeBlock_orderedRepresentative b
  simpa only [hr] using hc

/-- Relabel a tuple of particle modes by a permutation of the particle labels. -/
def relabelModeTuple {jetOrder n : ℕ} (g : Equiv.Perm (Fin n)) :
    (Fin n → Fin (jetOrder + 1)) ≃ (Fin n → Fin (jetOrder + 1)) :=
  Equiv.arrowCongr g (Equiv.refl _)

@[simp]
theorem relabelModeTuple_apply {jetOrder n : ℕ} (g : Equiv.Perm (Fin n))
    (r : Fin n → Fin (jetOrder + 1)) (i : Fin n) :
    relabelModeTuple g r i = r (g.symm i) :=
  rfl

/-- Relabeling an exponent vector agrees with relabeling its tuple of mode indices. -/
theorem mapDomain_labelledExponent {jetOrder n : ℕ} (g : Equiv.Perm (Fin n))
    (r : Fin n → Fin (jetOrder + 1)) :
    Finsupp.mapDomain g (labelledExponent r) =
      labelledExponent (relabelModeTuple g r) := by
  rw [← Finsupp.equivMapDomain_eq_mapDomain]
  ext i
  simp [Finsupp.equivMapDomain_apply]

/-- Relabeling particles does not change the underlying commutative mode configuration. -/
theorem unorderedModeBlock_relabelModeTuple {jetOrder n : ℕ}
    (g : Equiv.Perm (Fin n)) (r : Fin n → Fin (jetOrder + 1)) :
    unorderedModeBlock (relabelModeTuple g r) = unorderedModeBlock r := by
  apply Sym.sound
  have hr : relabelModeTuple g r = r ∘ g.symm := by
    funext i
    rfl
  change (List.Vector.toList (List.Vector.ofFn (relabelModeTuple g r))).Perm
    (List.Vector.toList (List.Vector.ofFn r))
  rw [List.Vector.toList_ofFn, List.Vector.toList_ofFn, hr]
  exact Equiv.Perm.ofFn_comp_perm g.symm r

/-- Concatenating labelled tuples and then forgetting their order agrees with appending their
unordered mode configurations. -/
theorem unorderedModeBlock_append {jetOrder n m : ℕ}
    (r : Fin n → Fin (jetOrder + 1)) (s : Fin m → Fin (jetOrder + 1)) :
    unorderedModeBlock (Fin.append r s) =
      (unorderedModeBlock r).append (unorderedModeBlock s) := by
  apply Sym.ext
  change
    (↑(List.Vector.toList (List.Vector.ofFn (Fin.append r s))) :
      Multiset (Fin (jetOrder + 1))) =
      ↑(List.Vector.toList (List.Vector.ofFn r)) +
        ↑(List.Vector.toList (List.Vector.ofFn s))
  rw [List.Vector.toList_ofFn, List.Vector.toList_ofFn,
    List.Vector.toList_ofFn, List.ofFn_fin_append]
  rfl

/-- The concrete polynomial realization is invariant under every permutation of same-species
particle labels. -/
theorem labelledParticlePolynomial_rename {jetOrder n : ℕ}
    (g : Equiv.Perm (Fin n)) (F : JetParticleSpace K jetOrder n) :
    MvPolynomial.rename g (labelledParticlePolynomial F) =
      labelledParticlePolynomial F := by
  classical
  rw [labelledParticlePolynomial, map_sum]
  simp_rw [MvPolynomial.rename_monomial, mapDomain_labelledExponent]
  calc
    (∑ r, MvPolynomial.monomial (labelledExponent (relabelModeTuple g r))
        (F (unorderedModeBlock r))) =
        ∑ r, MvPolynomial.monomial (labelledExponent (relabelModeTuple g r))
          (F (unorderedModeBlock (relabelModeTuple g r))) := by
            apply Finset.sum_congr rfl
            intro r _
            rw [unorderedModeBlock_relabelModeTuple]
    _ = ∑ r, MvPolynomial.monomial (labelledExponent r)
          (F (unorderedModeBlock r)) :=
      Equiv.sum_comp (relabelModeTuple g)
        (fun r ↦ MvPolynomial.monomial (labelledExponent r)
          (F (unorderedModeBlock r)))

/-- A polynomial is supported in the finite jet box when every nonzero labelled exponent vector
comes from a tuple of modes of order at most `jetOrder`. -/
def IsSupportedOnJetTuples (jetOrder n : ℕ) (p : MvPolynomial (Fin n) K) : Prop :=
  ∀ d, MvPolynomial.coeff d p ≠ 0 →
    ∃ r : Fin n → Fin (jetOrder + 1), d = labelledExponent r

/-- Coefficient symmetry says that labelled exponent tuples with the same unordered mode
configuration have equal coefficients.  This is the coefficientwise form of same-species
particle symmetry. -/
def IsCoefficientSymmetric {jetOrder n : ℕ} (p : MvPolynomial (Fin n) K) : Prop :=
  ∀ r s : Fin n → Fin (jetOrder + 1),
    unorderedModeBlock r = unorderedModeBlock s →
      MvPolynomial.coeff (labelledExponent r) p =
        MvPolynomial.coeff (labelledExponent s) p

/-- The concrete realization is supported in the finite jet box. -/
theorem labelledParticlePolynomial_supported {jetOrder n : ℕ}
    (F : JetParticleSpace K jetOrder n) :
    IsSupportedOnJetTuples jetOrder n (labelledParticlePolynomial F) := by
  intro d hd
  classical
  rw [labelledParticlePolynomial, MvPolynomial.coeff_sum] at hd
  obtain ⟨r, _, hr⟩ := Finset.exists_ne_zero_of_sum_ne_zero hd
  rw [MvPolynomial.coeff_monomial] at hr
  split at hr
  · rename_i h
    exact ⟨r, h.symm⟩
  · simp at hr

/-- The concrete realization is coefficient-symmetric. -/
theorem labelledParticlePolynomial_coefficientSymmetric {jetOrder n : ℕ}
    (F : JetParticleSpace K jetOrder n) :
    IsCoefficientSymmetric (jetOrder := jetOrder) (labelledParticlePolynomial F) := by
  intro r s h
  rw [coeff_labelledParticlePolynomial, coeff_labelledParticlePolynomial, h]

/-- Exact image characterization of the finite labelled polynomial realization. -/
theorem mem_range_labelledParticlePolynomial_iff {jetOrder n : ℕ}
    (p : MvPolynomial (Fin n) K) :
    p ∈ Set.range
        (labelledParticlePolynomial :
          JetParticleSpace K jetOrder n → MvPolynomial (Fin n) K) ↔
      IsSupportedOnJetTuples jetOrder n p ∧
        IsCoefficientSymmetric (jetOrder := jetOrder) p := by
  constructor
  · rintro ⟨F, rfl⟩
    exact ⟨labelledParticlePolynomial_supported F,
      labelledParticlePolynomial_coefficientSymmetric F⟩
  · rintro ⟨hsupport, hsymm⟩
    let F : JetParticleSpace K jetOrder n := fun b ↦
      MvPolynomial.coeff (labelledExponent (orderedRepresentative b)) p
    refine ⟨F, ?_⟩
    apply MvPolynomial.ext
    intro d
    by_cases hd : MvPolynomial.coeff d p = 0
    · rw [hd]
      classical
      rw [labelledParticlePolynomial, MvPolynomial.coeff_sum]
      apply Finset.sum_eq_zero
      intro r _
      rw [MvPolynomial.coeff_monomial]
      split
      · rename_i hr
        simp only [F]
        have hcoeff := hsymm (orderedRepresentative (unorderedModeBlock r)) r
          (unorderedModeBlock_orderedRepresentative (unorderedModeBlock r))
        rw [hcoeff, hr, hd]
      · simp
    · obtain ⟨r, hr⟩ := hsupport d hd
      rw [hr, coeff_labelledParticlePolynomial]
      change MvPolynomial.coeff
          (labelledExponent (orderedRepresentative (unorderedModeBlock r))) p =
        MvPolynomial.coeff (labelledExponent r) p
      exact hsymm (orderedRepresentative (unorderedModeBlock r)) r
        (unorderedModeBlock_orderedRepresentative (unorderedModeBlock r))

/-- The exact coefficientwise image criterion implies the usual rename-invariance condition. -/
theorem rename_eq_self_of_supported_coefficientSymmetric {jetOrder n : ℕ}
    {p : MvPolynomial (Fin n) K}
    (hsupport : IsSupportedOnJetTuples jetOrder n p)
    (hsymm : IsCoefficientSymmetric (jetOrder := jetOrder) p)
    (g : Equiv.Perm (Fin n)) :
    MvPolynomial.rename g p = p := by
  obtain ⟨F, rfl⟩ := (mem_range_labelledParticlePolynomial_iff p).2
    ⟨hsupport, hsymm⟩
  exact labelledParticlePolynomial_rename g F

/-- Exponent one in every labelled particle coordinate.  Its monomial is the algebraic product
factor forced by the absence of `S_0`. -/
def allParticleFactorExponent (n : ℕ) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun _ ↦ 1)

@[simp]
theorem allParticleFactorExponent_apply {n : ℕ} (i : Fin n) :
    allParticleFactorExponent n i = 1 := by
  simp [allParticleFactorExponent]

/-- The shifted labelled exponent for `S_r`, whose actual field power is one larger than its
divided-derivative index. -/
def shiftedLabelledExponent {jetOrder n : ℕ}
    (r : Fin n → Fin (jetOrder + 1)) : Fin n →₀ ℕ :=
  allParticleFactorExponent n + labelledExponent r

@[simp]
theorem shiftedLabelledExponent_apply {jetOrder n : ℕ}
    (r : Fin n → Fin (jetOrder + 1)) (i : Fin n) :
    shiftedLabelledExponent r i = (r i : ℕ) + 1 := by
  simp [shiftedLabelledExponent, add_comm]

/-- Shifted labelled exponent tuples remain injective. -/
theorem shiftedLabelledExponent_injective {jetOrder n : ℕ} :
    Function.Injective
      (shiftedLabelledExponent :
        (Fin n → Fin (jetOrder + 1)) → Fin n →₀ ℕ) := by
  intro r s h
  apply labelledExponent_injective
  exact add_left_cancel h

/-- The all-particle factor is fixed by relabeling. -/
theorem mapDomain_allParticleFactorExponent {n : ℕ} (g : Equiv.Perm (Fin n)) :
    Finsupp.mapDomain g (allParticleFactorExponent n) =
      allParticleFactorExponent n := by
  rw [← Finsupp.equivMapDomain_eq_mapDomain]
  ext i
  simp [Finsupp.equivMapDomain_apply]

/-- Relabeling a shifted exponent agrees with relabeling its tuple of mode indices. -/
theorem mapDomain_shiftedLabelledExponent {jetOrder n : ℕ}
    (g : Equiv.Perm (Fin n)) (r : Fin n → Fin (jetOrder + 1)) :
    Finsupp.mapDomain g (shiftedLabelledExponent r) =
      shiftedLabelledExponent (relabelModeTuple g r) := by
  simp [shiftedLabelledExponent, Finsupp.mapDomain_add,
    mapDomain_allParticleFactorExponent, mapDomain_labelledExponent]

/-- Concrete labelled polynomial for shifted `S` particles. -/
def shiftedSParticlePolynomial {jetOrder n : ℕ}
    (F : JetParticleSpace K jetOrder n) : MvPolynomial (Fin n) K :=
  ∑ r : Fin n → Fin (jetOrder + 1),
    MvPolynomial.monomial (shiftedLabelledExponent r) (F (unorderedModeBlock r))

/-- Coefficient recovery for the shifted `S` polynomial. -/
theorem coeff_shiftedSParticlePolynomial {jetOrder n : ℕ}
    (F : JetParticleSpace K jetOrder n)
    (r : Fin n → Fin (jetOrder + 1)) :
    MvPolynomial.coeff (shiftedLabelledExponent r) (shiftedSParticlePolynomial F) =
      F (unorderedModeBlock r) := by
  classical
  rw [shiftedSParticlePolynomial, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  rw [Finset.sum_eq_single r]
  · simp
  · intro s _ hs
    rw [if_neg (fun h ↦ hs (shiftedLabelledExponent_injective h))]
  · simp

/-- The shifted `S` polynomial is also invariant under every permutation of same-species labels. -/
theorem shiftedSParticlePolynomial_rename {jetOrder n : ℕ}
    (g : Equiv.Perm (Fin n)) (F : JetParticleSpace K jetOrder n) :
    MvPolynomial.rename g (shiftedSParticlePolynomial F) =
      shiftedSParticlePolynomial F := by
  classical
  rw [shiftedSParticlePolynomial, map_sum]
  simp_rw [MvPolynomial.rename_monomial, mapDomain_shiftedLabelledExponent]
  calc
    (∑ r, MvPolynomial.monomial (shiftedLabelledExponent (relabelModeTuple g r))
        (F (unorderedModeBlock r))) =
        ∑ r, MvPolynomial.monomial (shiftedLabelledExponent (relabelModeTuple g r))
          (F (unorderedModeBlock (relabelModeTuple g r))) := by
            apply Finset.sum_congr rfl
            intro r _
            rw [unorderedModeBlock_relabelModeTuple]
    _ = ∑ r, MvPolynomial.monomial (shiftedLabelledExponent r)
          (F (unorderedModeBlock r)) :=
      Equiv.sum_comp (relabelModeTuple g)
        (fun r ↦ MvPolynomial.monomial (shiftedLabelledExponent r)
          (F (unorderedModeBlock r)))

/-- Exact factorization forced by the shifted `S` convention. -/
theorem shiftedSParticlePolynomial_factor {jetOrder n : ℕ}
    (F : JetParticleSpace K jetOrder n) :
    shiftedSParticlePolynomial F =
      MvPolynomial.monomial (allParticleFactorExponent n) 1 *
        labelledParticlePolynomial F := by
  classical
  rw [shiftedSParticlePolynomial, labelledParticlePolynomial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [MvPolynomial.monomial_mul]
  simp [shiftedLabelledExponent]

/-- Every shifted `S` polynomial is divisible by the monomial with exponent one in each particle
coordinate. -/
theorem allParticleFactor_dvd_shiftedSParticlePolynomial {jetOrder n : ℕ}
    (F : JetParticleSpace K jetOrder n) :
    MvPolynomial.monomial (allParticleFactorExponent n) 1 ∣
      shiftedSParticlePolynomial F := by
  refine ⟨labelledParticlePolynomial F, ?_⟩
  exact shiftedSParticlePolynomial_factor F

/-- The coefficient of a literal shifted `S`-particle diagonal, now expressed entirely in the
concrete labelled polynomial.  The first `arity` labels are the colliding particles and the
remaining labels are a chosen ordering of the spectator configuration. -/
def shiftedPolynomialDiagonalCoefficient {jetOrder arity spectatorCount : ℕ} (q : ℕ)
    (spectator : ModeConfiguration jetOrder spectatorCount)
    (F : JetParticleSpace K jetOrder (arity + spectatorCount)) : K :=
  ∑ r ∈ VOA.AuxiliaryIdealOrthogonal.shiftedCoefficientBlocks
      jetOrder arity q,
    MvPolynomial.coeff
      (shiftedLabelledExponent
        (Fin.append r (orderedRepresentative spectator)))
      (shiftedSParticlePolynomial F)

/-- The coefficient-model diagonal is exactly the corresponding sum of coefficients of the
concrete shifted labelled polynomial. -/
theorem shiftedPolynomialDiagonalCoefficient_eq
    {jetOrder arity spectatorCount : ℕ} (q : ℕ)
    (spectator : ModeConfiguration jetOrder spectatorCount)
    (F : JetParticleSpace K jetOrder (arity + spectatorCount)) :
    shiftedPolynomialDiagonalCoefficient q spectator F =
      VOA.AuxiliaryIdealOrthogonal.shiftedFieldPowerDiagonalCoefficient
        q spectator F := by
  simp only [shiftedPolynomialDiagonalCoefficient,
    coeff_shiftedSParticlePolynomial,
    VOA.AuxiliaryIdealOrthogonal.shiftedFieldPowerDiagonalCoefficient]
  apply Finset.sum_congr rfl
  intro r _
  rw [unorderedModeBlock_append, unorderedModeBlock_orderedRepresentative]

/-- Orthogonality to the full shifted field-power relation span can therefore be read directly
from the coefficients of the concrete same-species invariant polynomial. -/
theorem shiftedFieldPower_span_orthogonal_iff_polynomialDiagonal
    {jetOrder arity spectatorCount : ℕ}
    (F : JetParticleSpace K jetOrder (arity + spectatorCount)) :
    VOA.AuxiliaryIdealOrthogonal.AnnihilatesSpan
        (VOA.AuxiliaryIdealOrthogonal.jetPairingFunctional F)
        (VOA.AuxiliaryIdealOrthogonal.shiftedFieldPowerRelationSet
          (K := K) jetOrder arity spectatorCount) ↔
      ∀ q spectator, shiftedPolynomialDiagonalCoefficient q spectator F = 0 := by
  rw [VOA.AuxiliaryIdealOrthogonal.shiftedFieldPower_span_orthogonal_iff_diagonal]
  constructor
  · intro h q spectator
    rw [shiftedPolynomialDiagonalCoefficient_eq]
    exact h q spectator
  · intro h q spectator
    rw [← shiftedPolynomialDiagonalCoefficient_eq]
    exact h q spectator

end

end VOA.ModeParticlePolynomial
