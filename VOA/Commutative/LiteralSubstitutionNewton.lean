/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.Degree.Support

/-!
# Support-orbit Newton counting

This file isolates the finite combinatorial lemma behind the Newton-binomial dependence in a
literal diagonal substitution.  A finite family of exponent vectors is restricted by requiring
its support to lie in a chosen finite set `T`.  If every exponent vector has total degree `d`, and
the sum of the coefficients with a fixed support depends only on the cardinality of that support,
then the restricted sum is

`sum r in range (d + 1), choose T.card r • C r`.

The statement is purely combinatorial.  In particular, it does not assert that a particular VOA
coefficient extraction supplies the orbit-invariance hypothesis.
-/

namespace VOA.LiteralSubstitutionNewton

open scoped BigOperators

open Polynomial

variable {I M : Type*} [AddCommMonoid M]

/-- Total degree of a finitely supported natural-valued exponent vector. -/
def totalDegree (alpha : I →₀ ℕ) : ℕ :=
  ∑ i ∈ alpha.support, alpha i

section LiteralPolynomial

variable {R : Type*} [CommSemiring R]

/-- Substitute the single indeterminate `X` for the variables in `T`, and zero for every other
variable.  This is the literal diagonal-offset specialization used before Newton counting. -/
noncomputable def literalSubstitution [DecidableEq I] (T : Finset I) :
    MvPolynomial I R →+* R[X] :=
  MvPolynomial.eval₂Hom Polynomial.C fun i => if i ∈ T then Polynomial.X else 0

/-- Literal substitution of one multivariate monomial is either the corresponding power of `X`,
or zero when the monomial uses a variable outside `T`. -/
theorem literalSubstitution_monomial [DecidableEq I]
    (T : Finset I) (alpha : I →₀ ℕ) (c : R) :
    literalSubstitution T (MvPolynomial.monomial alpha c) =
      if alpha.support ⊆ T then Polynomial.C c * Polynomial.X ^ totalDegree alpha else 0 := by
  classical
  rw [literalSubstitution, MvPolynomial.eval₂Hom_monomial]
  split_ifs with hsupport
  · congr 1
    rw [Finsupp.prod]
    calc
      (∏ i ∈ alpha.support, (if i ∈ T then Polynomial.X else 0) ^ alpha i) =
          ∏ i ∈ alpha.support, Polynomial.X ^ alpha i := by
            apply Finset.prod_congr rfl
            intro i hi
            rw [if_pos (hsupport hi)]
      _ = Polynomial.X ^ totalDegree alpha := by
        rw [totalDegree, Finset.prod_pow_eq_pow_sum]
  · obtain ⟨i, hiSupport, hiT⟩ := Set.not_subset.mp hsupport
    have hiT' : i ∉ T := by simpa using hiT
    rw [Finsupp.prod, Finset.prod_eq_zero hiSupport]
    · simp
    · rw [if_neg hiT', zero_pow (Finsupp.mem_support_iff.mp hiSupport)]

/-- The coefficient of `X^d` after literal diagonal substitution is exactly the sum of the
multivariate coefficients of total degree `d` whose support is contained in `T`. -/
theorem coeff_literalSubstitution [DecidableEq I]
    (T : Finset I) (p : MvPolynomial I R) (d : ℕ) :
    (literalSubstitution T p).coeff d =
      ∑ alpha ∈ p.support with totalDegree alpha = d ∧ alpha.support ⊆ T,
        p.coeff alpha := by
  classical
  have hsubstitution :
      literalSubstitution T p =
        ∑ alpha ∈ p.support,
          if alpha.support ⊆ T then
            Polynomial.C (p.coeff alpha) * Polynomial.X ^ totalDegree alpha
          else 0 := by
    conv_lhs => rw [← MvPolynomial.support_sum_monomial_coeff p]
    simp only [map_sum, literalSubstitution_monomial]
  rw [hsubstitution]
  change Polynomial.lcoeff R d
      (∑ alpha ∈ p.support,
        if alpha.support ⊆ T then
          Polynomial.C (p.coeff alpha) * Polynomial.X ^ totalDegree alpha
        else 0) = _
  rw [map_sum]
  simp only [Polynomial.lcoeff_apply]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro alpha halpha
  by_cases hsupport : alpha.support ⊆ T
  · rw [if_pos hsupport, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    by_cases hdegree : totalDegree alpha = d
    · rw [if_pos hdegree.symm, if_pos ⟨hdegree, hsupport⟩, mul_one]
    · rw [if_neg (fun h => hdegree h.symm), if_neg]
      · exact mul_zero _
      · exact fun h => hdegree h.1
  · rw [if_neg hsupport, Polynomial.coeff_zero, if_neg]
    exact fun h => hsupport h.2

end LiteralPolynomial

/-- The support of an exponent vector has cardinality at most its total degree. -/
theorem card_support_le_totalDegree (alpha : I →₀ ℕ) :
    alpha.support.card ≤ totalDegree alpha := by
  classical
  rw [totalDegree, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro i hi
  exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)

/-- Sum the coefficients of the exponent vectors in `A` whose support is exactly `U`. -/
def exactSupportContribution [DecidableEq I]
    (A : Finset (I →₀ ℕ)) (coeff : (I →₀ ℕ) → M) (U : Finset I) : M :=
  ∑ alpha ∈ A with alpha.support = U, coeff alpha

/-- Sum the coefficients of the exponent vectors in `A` whose support is contained in `T`. -/
def supportRestrictedContribution [DecidableEq I]
    (A : Finset (I →₀ ℕ)) (coeff : (I →₀ ℕ) → M) (T : Finset I) : M :=
  ∑ alpha ∈ A with alpha.support ⊆ T, coeff alpha

/-- A minimal, representation-independent formulation of support-orbit symmetry: among supports
contained in `T`, the sum over each exact-support fiber depends only on support cardinality.  The
VOA application must prove this predicate from symmetry of its leaf variables; it is not built
into the combinatorial statement. -/
def ExactSupportCardinalityInvariant [DecidableEq I]
    (A : Finset (I →₀ ℕ)) (coeff : (I →₀ ℕ) → M) (T : Finset I) : Prop :=
  ∀ ⦃U V : Finset I⦄, U ⊆ T → V ⊆ T → U.card = V.card →
    exactSupportContribution A coeff U = exactSupportContribution A coeff V

/-- Exact-support cardinality invariance supplies a single coefficient function on cardinalities.
The function is defined arbitrarily at cardinalities not realized by subsets of `T`. -/
theorem exists_exactSupportContribution_eq_card [DecidableEq I]
    (A : Finset (I →₀ ℕ)) (coeff : (I →₀ ℕ) → M) (T : Finset I)
    (hsymm : ExactSupportCardinalityInvariant A coeff T) :
    ∃ C : ℕ → M, ∀ U : Finset I, U ⊆ T →
      exactSupportContribution A coeff U = C U.card := by
  classical
  let supportCoeff : ℕ → M := fun r =>
    if h : ∃ U : Finset I, U ⊆ T ∧ U.card = r then
      exactSupportContribution A coeff (Classical.choose h)
    else 0
  refine ⟨supportCoeff, ?_⟩
  intro U hUT
  have hexists : ∃ V : Finset I, V ⊆ T ∧ V.card = U.card := ⟨U, hUT, rfl⟩
  dsimp only [supportCoeff]
  rw [dif_pos hexists]
  exact hsymm hUT (Classical.choose_spec hexists).1
    (Classical.choose_spec hexists).2.symm

/-- Fixed-support fibers partition the contribution whose support lies in `T`. -/
theorem supportRestrictedContribution_eq_sum_exactSupportContribution
    [DecidableEq I]
    (A : Finset (I →₀ ℕ)) (coeff : (I →₀ ℕ) → M) (T : Finset I) :
    supportRestrictedContribution A coeff T =
      ∑ U ∈ T.powerset, exactSupportContribution A coeff U := by
  classical
  let restricted := A.filter fun alpha => alpha.support ⊆ T
  have hmap : ∀ alpha ∈ restricted, alpha.support ∈ T.powerset := by
    intro alpha halpha
    exact Finset.mem_powerset.mpr (Finset.mem_filter.mp halpha).2
  have hgroup :=
    Finset.sum_fiberwise_of_maps_to
      (s := restricted) (t := T.powerset) (g := fun alpha => alpha.support)
      hmap coeff
  rw [supportRestrictedContribution]
  change (∑ alpha ∈ restricted, coeff alpha) = _
  rw [← hgroup]
  apply Finset.sum_congr rfl
  intro U hU
  have hUT : U ⊆ T := Finset.mem_powerset.mp hU
  rw [exactSupportContribution]
  have hfiber :
      restricted.filter (fun alpha => alpha.support = U) =
        A.filter (fun alpha => alpha.support = U) := by
    ext alpha
    simp only [restricted, Finset.mem_filter]
    constructor
    · exact fun halpha => ⟨halpha.1.1, halpha.2⟩
    · rintro ⟨halphaA, hsupp⟩
      exact ⟨⟨halphaA, hsupp.trans_le hUT⟩, hsupp⟩
  rw [hfiber]

/-- The literal support-orbit counting lemma.  The hypothesis `horbit` is the exact point where
symmetry enters: after summing all exponent vectors with the same support, the answer depends only
on the support cardinality.  The total-degree hypothesis supplies the sharp truncation `r ≤ d`. -/
theorem supportRestrictedContribution_eq_binomialSum
    [DecidableEq I]
    (A : Finset (I →₀ ℕ)) (coeff : (I →₀ ℕ) → M) (T : Finset I)
    (d : ℕ) (C : ℕ → M)
    (hdegree : ∀ alpha ∈ A, totalDegree alpha = d)
    (horbit : ∀ U : Finset I, U ⊆ T → U.card ≤ d →
      exactSupportContribution A coeff U = C U.card) :
    supportRestrictedContribution A coeff T =
      ∑ r ∈ Finset.range (d + 1), T.card.choose r • C r := by
  classical
  let restricted := A.filter fun alpha => alpha.support ⊆ T
  let supports := T.powerset.filter fun U => U.card ≤ d
  have hmap : ∀ alpha ∈ restricted, alpha.support ∈ supports := by
    intro alpha halpha
    have halpha' := Finset.mem_filter.mp halpha
    refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr halpha'.2, ?_⟩
    exact (card_support_le_totalDegree alpha).trans_eq (hdegree alpha halpha'.1)
  have hsupportGroup :=
    Finset.sum_fiberwise_of_maps_to
      (s := restricted) (t := supports) (g := fun alpha => alpha.support)
      hmap coeff
  rw [supportRestrictedContribution]
  change (∑ alpha ∈ restricted, coeff alpha) = _
  rw [← hsupportGroup]
  have hfixedSupport :
      (∑ U ∈ supports,
          ∑ alpha ∈ restricted with alpha.support = U, coeff alpha) =
        ∑ U ∈ supports, C U.card := by
    apply Finset.sum_congr rfl
    intro U hU
    have hU' := Finset.mem_filter.mp hU
    have hUT : U ⊆ T := Finset.mem_powerset.mp hU'.1
    have hfiber :
        restricted.filter (fun alpha => alpha.support = U) =
          A.filter (fun alpha => alpha.support = U) := by
      ext alpha
      simp only [restricted, Finset.mem_filter]
      constructor
      · exact fun halpha => ⟨halpha.1.1, halpha.2⟩
      · rintro ⟨halphaA, hsupp⟩
        exact ⟨⟨halphaA, hsupp.trans_le hUT⟩, hsupp⟩
    rw [hfiber]
    exact horbit U hUT hU'.2
  rw [hfixedSupport]
  have hcardMap : ∀ U ∈ supports, U.card ∈ Finset.range (d + 1) := by
    intro U hU
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_filter.mp hU).2)
  have hcardGroup :=
    Finset.sum_fiberwise_of_maps_to
      (s := supports) (t := Finset.range (d + 1)) (g := Finset.card)
      hcardMap (fun U : Finset I => C U.card)
  rw [← hcardGroup]
  apply Finset.sum_congr rfl
  intro r hr
  have hrd : r ≤ d := Nat.le_of_lt_succ (Finset.mem_range.mp hr)
  have hfiber :
      supports.filter (fun U => U.card = r) = T.powersetCard r := by
    ext U
    simp only [supports, Finset.mem_filter, Finset.mem_powerset,
      Finset.mem_powersetCard]
    constructor
    · rintro ⟨⟨hUT, _hUd⟩, hcard⟩
      exact ⟨hUT, hcard⟩
    · rintro ⟨hUT, hcard⟩
      exact ⟨⟨hUT, hcard.trans_le hrd⟩, hcard⟩
  rw [hfiber]
  calc
    (∑ U ∈ T.powersetCard r, C U.card) =
        ∑ _U ∈ T.powersetCard r, C r := by
      apply Finset.sum_congr rfl
      intro U hU
      rw [(Finset.mem_powersetCard.mp hU).2]
    _ = T.card.choose r • C r := by
      rw [Finset.sum_const, Finset.card_powersetCard]

section LiteralPolynomialBridge

variable {R : Type*} [CommSemiring R]

/-- The exponent vectors of a multivariate polynomial having a prescribed total degree. -/
def fixedDegreeSupport [DecidableEq I] (p : MvPolynomial I R) (d : ℕ) :
    Finset (I →₀ ℕ) :=
  p.support.filter fun alpha => totalDegree alpha = d

/-- A permutation-invariant polynomial has exact-support contributions that only depend on the
support cardinality.  This is the combinatorial bridge needed after rewriting the labelled
polynomial into an `S`-variable polynomial with current variables in the coefficients. -/
theorem exactSupportCardinalityInvariant_of_permInvariant [Fintype I] [DecidableEq I]
    (p : MvPolynomial I R) (d : ℕ) (T : Finset I)
    (hp : ∀ σ : Equiv.Perm I, MvPolynomial.rename σ p = p) :
    ExactSupportCardinalityInvariant (fixedDegreeSupport p d) p.coeff T := by
  classical
  intro U V hUT hVT hcard
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_map_finset_eq U V hcard
  let e : (I →₀ ℕ) → (I →₀ ℕ) := Finsupp.mapDomain σ
  have he_bijective : Function.Bijective e := by
    constructor
    · exact Finsupp.mapDomain_injective σ.injective
    · exact Finsupp.mapDomain_surjective σ.surjective
  have hdeg : ∀ τ : Equiv.Perm I, ∀ α, totalDegree (Finsupp.mapDomain τ α) = totalDegree α := by
    intro τ α
    rw [totalDegree, totalDegree, Finsupp.mapDomain_support_of_injective τ.injective]
    simpa [Finsupp.mapDomain_equiv_apply] using
      (Finset.sum_image (f := fun x => α (τ.symm x)) (s := α.support) (g := τ) τ.injective)
  have hcoeff : ∀ τ : Equiv.Perm I, ∀ α, p.coeff α = p.coeff (Finsupp.mapDomain τ α) := by
    intro τ α
    rw [← MvPolynomial.coeff_rename_mapDomain τ τ.injective p α, hp τ]
  have hA_fwd : ∀ α, α ∈ fixedDegreeSupport p d → e α ∈ fixedDegreeSupport p d := by
    intro α hα
    change Finsupp.mapDomain σ α ∈ fixedDegreeSupport p d
    simpa [fixedDegreeSupport, hdeg σ α, hcoeff σ α] using hα
  have hA_bwd : ∀ α, e α ∈ fixedDegreeSupport p d → α ∈ fixedDegreeSupport p d := by
    intro α hα
    change Finsupp.mapDomain σ α ∈ fixedDegreeSupport p d at hα
    have hα' : Finsupp.mapDomain σ.symm (Finsupp.mapDomain σ α) ∈ fixedDegreeSupport p d := by
      simpa [fixedDegreeSupport, hdeg σ.symm (Finsupp.mapDomain σ α),
        hcoeff σ.symm (Finsupp.mapDomain σ α)] using hα
    have heq : Finsupp.mapDomain σ.symm (Finsupp.mapDomain σ α) = α := by
      ext i
      simp
    simpa [heq] using hα'
  have hsupport_fwd : ∀ α, α.support = U → (e α).support = V := by
    intro α hα
    rw [Finsupp.mapDomain_support_of_injective σ.injective]
    rw [hα]
    simpa [Finset.map_eq_image] using hσ
  have hsupport_bwd : ∀ α, (e α).support = V → α.support = U := by
    intro α hα
    change (Finsupp.mapDomain σ α).support = V at hα
    have hσsymm : Finset.image (⇑(Equiv.symm σ)) V = U := by
      have h := congrArg (Finset.image (⇑(Equiv.symm σ))) hσ
      simpa [Finset.map_eq_image, Finset.image_image] using h.symm
    have hα' : (Finsupp.mapDomain σ.symm (Finsupp.mapDomain σ α)).support = U := by
      rw [Finsupp.mapDomain_support_of_injective σ.symm.injective]
      rw [hα]
      simpa [Finset.map_eq_image] using hσsymm
    have heq : Finsupp.mapDomain σ.symm (Finsupp.mapDomain σ α) = α := by
      ext i
      simp
    simpa [heq] using hα'
  have hmem : ∀ α, α ∈ (fixedDegreeSupport p d).filter (fun α => α.support = U) ↔
      e α ∈ (fixedDegreeSupport p d).filter (fun α => α.support = V) := by
    intro α
    constructor
    · intro hα
      rcases Finset.mem_filter.mp hα with ⟨hαA, hαU⟩
      exact Finset.mem_filter.mpr ⟨hA_fwd α hαA, hsupport_fwd α hαU⟩
    · intro hα
      rcases Finset.mem_filter.mp hα with ⟨hαA, hαV⟩
      exact Finset.mem_filter.mpr ⟨hA_bwd α hαA, hsupport_bwd α hαV⟩
  have hfg : ∀ α ∈ (fixedDegreeSupport p d).filter (fun α => α.support = U),
      p.coeff α = p.coeff (e α) := by
    intro α hα
    exact hcoeff σ α
  rw [exactSupportContribution, exactSupportContribution]
  refine Finset.sum_bijective e he_bijective hmem ?_
  intro α hα
  exact hfg α hα

/-- The literal polynomial coefficient formula, restated in the support-restricted language used
by the combinatorial Newton theorem. -/
theorem coeff_literalSubstitution_eq_supportRestrictedContribution [DecidableEq I]
    (T : Finset I) (p : MvPolynomial I R) (d : ℕ) :
    (literalSubstitution T p).coeff d =
      supportRestrictedContribution (fixedDegreeSupport p d) p.coeff T := by
  rw [coeff_literalSubstitution, supportRestrictedContribution]
  congr 1
  ext alpha
  simp only [fixedDegreeSupport, Finset.mem_filter]
  tauto

/-- A direct instantiation of support-orbit Newton counting for the coefficient obtained by
literal substitution in a multivariate polynomial. -/
theorem coeff_literalSubstitution_eq_binomialSum [DecidableEq I]
    (T : Finset I) (p : MvPolynomial I R) (d : ℕ) (C : ℕ → R)
    (horbit : ∀ U : Finset I, U ⊆ T → U.card ≤ d →
      exactSupportContribution (fixedDegreeSupport p d) p.coeff U = C U.card) :
    (literalSubstitution T p).coeff d =
      ∑ r ∈ Finset.range (d + 1), T.card.choose r • C r := by
  rw [coeff_literalSubstitution_eq_supportRestrictedContribution]
  apply supportRestrictedContribution_eq_binomialSum
  · intro alpha halpha
    exact (Finset.mem_filter.mp halpha).2
  · exact horbit

/-- Exact-support cardinality invariance is sufficient, without choosing orbit representatives in
the theorem statement, to give the Newton-binomial formula for literal substitution. -/
theorem exists_coeff_literalSubstitution_eq_binomialSum_of_invariant [DecidableEq I]
    (T : Finset I) (p : MvPolynomial I R) (d : ℕ)
    (hsymm : ExactSupportCardinalityInvariant (fixedDegreeSupport p d) p.coeff T) :
    ∃ C : ℕ → R,
      (literalSubstitution T p).coeff d =
        ∑ r ∈ Finset.range (d + 1), T.card.choose r • C r := by
  obtain ⟨C, hC⟩ := exists_exactSupportContribution_eq_card
    (fixedDegreeSupport p d) p.coeff T hsymm
  refine ⟨C, coeff_literalSubstitution_eq_binomialSum T p d C ?_⟩
  intro U hUT _hUd
  exact hC U hUT

end LiteralPolynomialBridge

end VOA.LiteralSubstitutionNewton
