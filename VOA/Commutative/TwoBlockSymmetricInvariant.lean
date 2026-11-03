/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem

/-!
# Two-block symmetric invariants

This file isolates the reusable algebraic induction step behind the Young-parabolic invariant
presentation.  Under `MvPolynomial.sumAlgEquiv`, a polynomial in variables `sigma ⊕ tau` is a
polynomial in the `sigma` variables with coefficients in the `tau` variables.  Independent
permutations of the two blocks become outer-variable renaming and coefficient renaming.

The first results below prove that covariance and its coefficientwise consequence.  The
coefficient-lift construction then shows that a polynomial whose coefficients lie in a
subalgebra comes from a polynomial over that subalgebra.  These are the two nontrivial adapters
needed to iterate Mathlib's one-block Fundamental Theorem of Symmetric Polynomials.
-/

namespace VOA.TwoBlockSymmetricInvariant

noncomputable section

universe u v w

variable {K : Type u} [CommRing K]
variable {sigma : Type v} {tau : Type w}

/-- Independent permutations of two variable blocks, acting on their disjoint union. -/
def blockPermutation (e : Equiv.Perm sigma) (f : Equiv.Perm tau) :
    Equiv.Perm (sigma ⊕ tau) :=
  e.sumCongr f

/-- Under the sum-of-variables equivalence, a two-block permutation is outer renaming after
coefficient renaming. -/
theorem sumAlgEquiv_rename_blockPermutation
    (e : Equiv.Perm sigma) (f : Equiv.Perm tau)
    (p : MvPolynomial (sigma ⊕ tau) K) :
    MvPolynomial.sumAlgEquiv K sigma tau
        (MvPolynomial.rename (blockPermutation e f) p) =
      MvPolynomial.rename e
        (MvPolynomial.map (MvPolynomial.rename f).toRingHom
          (MvPolynomial.sumAlgEquiv K sigma tau p)) := by
  induction p using MvPolynomial.induction_on with
  | C r => simp [blockPermutation]
  | add p q hp hq => simp [map_add, hp, hq]
  | mul_X p i hp =>
      rcases i with i | i
      · simp [blockPermutation, map_mul]
        simpa [blockPermutation] using hp
      · simp [blockPermutation, map_mul]
        congr 1

/-- Invariance under the second block makes every coefficient in the first-block polynomial
symmetric in the second-block variables. -/
theorem coefficient_isSymmetric_of_rightInvariant
    (p : MvPolynomial (sigma ⊕ tau) K)
    (hp : ∀ f : Equiv.Perm tau,
      MvPolynomial.rename (blockPermutation (Equiv.refl sigma) f) p = p)
    (d : sigma →₀ ℕ) :
    (MvPolynomial.sumAlgEquiv K sigma tau p).coeff d |>.IsSymmetric := by
  intro f
  have hcov := sumAlgEquiv_rename_blockPermutation
    (K := K) (sigma := sigma) (tau := tau) (Equiv.refl sigma) f p
  rw [hp f] at hcov
  have hcoeff := congrArg (MvPolynomial.coeff d) hcov
  simpa [MvPolynomial.coeff_map] using hcoeff.symm

section CoefficientLift

variable {A : Type*} [CommRing A] [Algebra K A]
variable (S : Subalgebra K A)

/-- Lift a polynomial coefficientwise to a subalgebra, given membership of every coefficient. -/
def liftCoefficientsToSubalgebra (p : MvPolynomial sigma A)
    (hp : ∀ d, p.coeff d ∈ S) : MvPolynomial sigma S :=
  ∑ d ∈ p.support, MvPolynomial.monomial d ⟨p.coeff d, hp d⟩

/-- Mapping a coefficient lift back along the subalgebra inclusion recovers the polynomial. -/
theorem map_liftCoefficientsToSubalgebra (p : MvPolynomial sigma A)
    (hp : ∀ d, p.coeff d ∈ S) :
    MvPolynomial.map S.val
        (liftCoefficientsToSubalgebra (K := K) S p hp) = p := by
  rw [liftCoefficientsToSubalgebra, map_sum]
  simp only [MvPolynomial.map_monomial]
  exact p.as_sum.symm

/-- Coefficient inclusion from a subalgebra is injective on multivariate polynomials. -/
theorem map_subalgebraVal_injective :
    Function.Injective
      (MvPolynomial.map S.val : MvPolynomial sigma S → MvPolynomial sigma A) := by
  intro p q hpq
  apply MvPolynomial.ext
  intro d
  apply Subtype.ext
  have hcoeff := congrArg (MvPolynomial.coeff d) hpq
  simpa [MvPolynomial.coeff_map] using hcoeff

end CoefficientLift

section SymmetricCoefficientLift

/-- Regard the iterated polynomial associated to `p` as a polynomial whose coefficients are
symmetric in the right block. -/
def rightSymmetricLift (p : MvPolynomial (sigma ⊕ tau) K)
    (hp : ∀ f : Equiv.Perm tau,
      MvPolynomial.rename (blockPermutation (Equiv.refl sigma) f) p = p) :
    MvPolynomial sigma (MvPolynomial.symmetricSubalgebra tau K) :=
  liftCoefficientsToSubalgebra (K := K)
    (MvPolynomial.symmetricSubalgebra tau K)
    (MvPolynomial.sumAlgEquiv K sigma tau p)
    (coefficient_isSymmetric_of_rightInvariant
      (K := K) (sigma := sigma) (tau := tau) p hp)

/-- Forgetting the symmetric-coefficient proofs recovers the iterated form of `p`. -/
theorem map_rightSymmetricLift (p : MvPolynomial (sigma ⊕ tau) K)
    (hp : ∀ f : Equiv.Perm tau,
      MvPolynomial.rename (blockPermutation (Equiv.refl sigma) f) p = p) :
    MvPolynomial.map (MvPolynomial.symmetricSubalgebra tau K).val
        (rightSymmetricLift (K := K) (sigma := sigma) (tau := tau) p hp) =
      MvPolynomial.sumAlgEquiv K sigma tau p := by
  exact map_liftCoefficientsToSubalgebra (K := K)
    (MvPolynomial.symmetricSubalgebra tau K)
    (MvPolynomial.sumAlgEquiv K sigma tau p)
    (coefficient_isSymmetric_of_rightInvariant
      (K := K) (sigma := sigma) (tau := tau) p hp)

/-- If `p` is invariant under both blocks, its right-symmetric coefficient lift is symmetric in
the outer (left-block) variables. -/
theorem rightSymmetricLift_isSymmetric_of_blockInvariant
    (p : MvPolynomial (sigma ⊕ tau) K)
    (hp : ∀ (e : Equiv.Perm sigma) (f : Equiv.Perm tau),
      MvPolynomial.rename (blockPermutation e f) p = p) :
    (rightSymmetricLift (K := K) (sigma := sigma) (tau := tau) p
      (hp (Equiv.refl sigma))).IsSymmetric := by
  intro e
  apply map_subalgebraVal_injective (K := K)
    (MvPolynomial.symmetricSubalgebra tau K)
  rw [MvPolynomial.map_rename]
  rw [map_rightSymmetricLift]
  have hcov := sumAlgEquiv_rename_blockPermutation
    (K := K) (sigma := sigma) (tau := tau) e (Equiv.refl tau) p
  rw [hp e (Equiv.refl tau)] at hcov
  have hring : (MvPolynomial.rename (R := K) (Equiv.refl tau)).toRingHom =
      RingHom.id (MvPolynomial tau K) := by
    change (MvPolynomial.rename (R := K) id).toRingHom = _
    rw [MvPolynomial.rename_id]
    rfl
  have hright : MvPolynomial.map
      (MvPolynomial.rename (R := K) (Equiv.refl tau)).toRingHom
      (MvPolynomial.sumAlgEquiv K sigma tau p) =
        MvPolynomial.sumAlgEquiv K sigma tau p := by
    rw [hring]
    exact MvPolynomial.map_id _
  rw [hright] at hcov
  exact hcov.symm

/-- A polynomial fixed by both blocks canonically determines a nested symmetric polynomial:
symmetric in the left variables, with coefficients symmetric in the right variables. -/
def nestedSymmetricLift
    (p : MvPolynomial (sigma ⊕ tau) K)
    (hp : ∀ (e : Equiv.Perm sigma) (f : Equiv.Perm tau),
      MvPolynomial.rename (blockPermutation e f) p = p) :
    MvPolynomial.symmetricSubalgebra sigma
      (MvPolynomial.symmetricSubalgebra tau K) :=
  ⟨rightSymmetricLift (K := K) (sigma := sigma) (tau := tau) p
      (hp (Equiv.refl sigma)),
    rightSymmetricLift_isSymmetric_of_blockInvariant
      (K := K) (sigma := sigma) (tau := tau) p hp⟩

end SymmetricCoefficientLift

section TwoBlockFixedPresentation

/-- The subalgebra fixed by every independent permutation of the left and right variable
blocks. -/
def twoBlockFixedSubalgebra : Subalgebra K (MvPolynomial (sigma ⊕ tau) K) where
  carrier := {p | ∀ (e : Equiv.Perm sigma) (f : Equiv.Perm tau),
    MvPolynomial.rename (blockPermutation e f) p = p}
  algebraMap_mem' r e f := MvPolynomial.rename_C _ _
  add_mem' {p q} hp hq e f := by rw [map_add, hp e f, hq e f]
  mul_mem' {p q} hp hq e f := by rw [map_mul, hp e f, hq e f]

/-- The outer symmetric subalgebra inclusion, regarded over the original ground ring rather than
over the intermediate right-block invariant ring. -/
def nestedSymmetricVal :
    MvPolynomial.symmetricSubalgebra sigma
        (MvPolynomial.symmetricSubalgebra tau K) →ₐ[K]
      MvPolynomial sigma (MvPolynomial.symmetricSubalgebra tau K) where
  toFun q := q.1
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- Forget the two nested symmetry proofs and return to a polynomial on the disjoint union of
the two variable blocks. -/
def nestedSymmetricToTwoBlockRaw :
  MvPolynomial.symmetricSubalgebra sigma
        (MvPolynomial.symmetricSubalgebra tau K) →ₐ[K]
      MvPolynomial (sigma ⊕ tau) K :=
  (MvPolynomial.sumAlgEquiv K sigma tau).symm.toAlgHom.comp
    ((MvPolynomial.mapAlgHom (R := K) (σ := sigma)
      (MvPolynomial.symmetricSubalgebra tau K).val).comp
        (nestedSymmetricVal (K := K) (sigma := sigma) (tau := tau)))

/-- Iterating and then forgetting nested symmetry is coefficient inclusion. -/
theorem sumAlgEquiv_nestedSymmetricToTwoBlockRaw
    (q : MvPolynomial.symmetricSubalgebra sigma
      (MvPolynomial.symmetricSubalgebra tau K)) :
    MvPolynomial.sumAlgEquiv K sigma tau
        (nestedSymmetricToTwoBlockRaw (K := K) (sigma := sigma) (tau := tau) q) =
      MvPolynomial.map (MvPolynomial.symmetricSubalgebra tau K).val.toRingHom q.1 := by
  simp [nestedSymmetricToTwoBlockRaw]
  rfl

/-- The raw image of a nested symmetric polynomial is invariant under both blocks. -/
theorem nestedSymmetricToTwoBlockRaw_mem_fixed
    (q : MvPolynomial.symmetricSubalgebra sigma
      (MvPolynomial.symmetricSubalgebra tau K)) :
    nestedSymmetricToTwoBlockRaw (K := K) (sigma := sigma) (tau := tau) q ∈
      twoBlockFixedSubalgebra (K := K) (sigma := sigma) (tau := tau) := by
  intro e f
  apply (MvPolynomial.sumAlgEquiv K sigma tau).injective
  rw [sumAlgEquiv_rename_blockPermutation]
  rw [sumAlgEquiv_nestedSymmetricToTwoBlockRaw]
  have hright :
      MvPolynomial.map (MvPolynomial.rename f).toRingHom
          (MvPolynomial.map
            (MvPolynomial.symmetricSubalgebra tau K).val.toRingHom q.1) =
        MvPolynomial.map
          (MvPolynomial.symmetricSubalgebra tau K).val.toRingHom q.1 := by
    apply MvPolynomial.ext
    intro d
    simp only [MvPolynomial.coeff_map]
    exact (q.1.coeff d).2 f
  rw [hright]
  rw [← MvPolynomial.map_rename]
  exact congrArg
    (MvPolynomial.map
      (MvPolynomial.symmetricSubalgebra tau K).val.toRingHom) (q.2 e)

/-- The nested symmetric algebra maps canonically to the simultaneous two-block fixed
subalgebra. -/
def nestedSymmetricToTwoBlockFixed :
    MvPolynomial.symmetricSubalgebra sigma
        (MvPolynomial.symmetricSubalgebra tau K) →ₐ[K]
      twoBlockFixedSubalgebra (K := K) (sigma := sigma) (tau := tau) :=
  (nestedSymmetricToTwoBlockRaw (K := K) (sigma := sigma) (tau := tau)).codRestrict
    (twoBlockFixedSubalgebra (K := K) (sigma := sigma) (tau := tau))
    (nestedSymmetricToTwoBlockRaw_mem_fixed
      (K := K) (sigma := sigma) (tau := tau))

/-- The nested-symmetry presentation is injective. -/
theorem nestedSymmetricToTwoBlockFixed_injective :
    Function.Injective
      (nestedSymmetricToTwoBlockFixed (K := K) (sigma := sigma) (tau := tau)) := by
  intro p q hpq
  apply Subtype.ext
  apply map_subalgebraVal_injective (K := K)
    (MvPolynomial.symmetricSubalgebra tau K)
  have hraw := congrArg Subtype.val hpq
  change nestedSymmetricToTwoBlockRaw (K := K) (sigma := sigma) (tau := tau) p =
    nestedSymmetricToTwoBlockRaw (K := K) (sigma := sigma) (tau := tau) q at hraw
  have hiter := congrArg (MvPolynomial.sumAlgEquiv K sigma tau) hraw
  rw [sumAlgEquiv_nestedSymmetricToTwoBlockRaw,
    sumAlgEquiv_nestedSymmetricToTwoBlockRaw] at hiter
  exact hiter

/-- Every simultaneous two-block invariant has a nested symmetric preimage. -/
theorem nestedSymmetricToTwoBlockFixed_surjective :
    Function.Surjective
      (nestedSymmetricToTwoBlockFixed (K := K) (sigma := sigma) (tau := tau)) := by
  intro p
  let q := nestedSymmetricLift (K := K) (sigma := sigma) (tau := tau) p.1 p.2
  refine ⟨q, ?_⟩
  apply Subtype.ext
  apply (MvPolynomial.sumAlgEquiv K sigma tau).injective
  change MvPolynomial.sumAlgEquiv K sigma tau
      (nestedSymmetricToTwoBlockRaw (K := K) (sigma := sigma) (tau := tau) q) =
    MvPolynomial.sumAlgEquiv K sigma tau p.1
  rw [sumAlgEquiv_nestedSymmetricToTwoBlockRaw]
  exact map_rightSymmetricLift
    (K := K) (sigma := sigma) (tau := tau) p.1 (p.2 (Equiv.refl sigma))

/-- Simultaneous invariants of two blocks are exactly nested symmetric polynomials. -/
def nestedSymmetricTwoBlockFixedAlgEquiv :
    MvPolynomial.symmetricSubalgebra sigma
        (MvPolynomial.symmetricSubalgebra tau K) ≃ₐ[K]
      twoBlockFixedSubalgebra (K := K) (sigma := sigma) (tau := tau) :=
  AlgEquiv.ofBijective
    (nestedSymmetricToTwoBlockFixed (K := K) (sigma := sigma) (tau := tau))
    ⟨nestedSymmetricToTwoBlockFixed_injective
      (K := K) (sigma := sigma) (tau := tau),
     nestedSymmetricToTwoBlockFixed_surjective
      (K := K) (sigma := sigma) (tau := tau)⟩

end TwoBlockFixedPresentation

section TwoBlockFundamentalTheorem

variable [Fintype sigma] [Fintype tau]

/-- The two-block Fundamental Theorem of Symmetric Polynomials.  Its source has one elementary
coordinate for each positive elementary degree in each block, and its target is the simultaneous
fixed subalgebra. -/
def twoBlockEsymmAlgEquiv (a b : ℕ)
    (ha : Fintype.card sigma = a) (hb : Fintype.card tau = b) :
    MvPolynomial (Fin a ⊕ Fin b) K ≃ₐ[K]
      twoBlockFixedSubalgebra (K := K) (sigma := sigma) (tau := tau) :=
  (MvPolynomial.sumAlgEquiv K (Fin a) (Fin b)).trans
    ((MvPolynomial.mapAlgEquiv (Fin a)
      (MvPolynomial.esymmAlgEquiv tau K hb)).trans
        (((MvPolynomial.esymmAlgEquiv sigma
          (MvPolynomial.symmetricSubalgebra tau K) ha).restrictScalars K).trans
            (nestedSymmetricTwoBlockFixedAlgEquiv
              (K := K) (sigma := sigma) (tau := tau))))

/-- In particular, the canonical two-block elementary-symmetric map is bijective onto the
simultaneous fixed subalgebra. -/
theorem twoBlockEsymmAlgEquiv_bijective (a b : ℕ)
    (ha : Fintype.card sigma = a) (hb : Fintype.card tau = b) :
    Function.Bijective
      (twoBlockEsymmAlgEquiv (K := K) (sigma := sigma) (tau := tau) a b ha hb) :=
  (twoBlockEsymmAlgEquiv (K := K) (sigma := sigma) (tau := tau) a b ha hb).bijective

/-- The left generators of the two-block presentation are the elementary symmetric polynomials
in the left variables. -/
@[simp] theorem twoBlockEsymmAlgEquiv_X_inl (a b : ℕ)
    (ha : Fintype.card sigma = a) (hb : Fintype.card tau = b) (i : Fin a) :
    (twoBlockEsymmAlgEquiv (K := K) (sigma := sigma) (tau := tau) a b ha hb
      (MvPolynomial.X (Sum.inl i))).1 =
        MvPolynomial.rename Sum.inl
          (MvPolynomial.esymm sigma K (i.1 + 1)) := by
  simp [twoBlockEsymmAlgEquiv, nestedSymmetricTwoBlockFixedAlgEquiv,
    nestedSymmetricToTwoBlockFixed, nestedSymmetricToTwoBlockRaw,
    nestedSymmetricVal, MvPolynomial.esymmAlgEquiv_apply,
    MvPolynomial.esymmAlgHom]
  apply (MvPolynomial.sumAlgEquiv K sigma tau).injective
  simp [MvPolynomial.map_esymm]
  have h := DFunLike.congr_fun
    (MvPolynomial.sumAlgEquiv_comp_rename_inl
      (R := K) (S₁ := sigma) (S₂ := tau))
    (MvPolynomial.esymm sigma K (i.1 + 1))
  simpa [MvPolynomial.map_esymm] using h.symm

/-- The right generators of the two-block presentation are the elementary symmetric polynomials
in the right variables. -/
@[simp] theorem twoBlockEsymmAlgEquiv_X_inr (a b : ℕ)
    (ha : Fintype.card sigma = a) (hb : Fintype.card tau = b) (i : Fin b) :
    (twoBlockEsymmAlgEquiv (K := K) (sigma := sigma) (tau := tau) a b ha hb
      (MvPolynomial.X (Sum.inr i))).1 =
        MvPolynomial.rename Sum.inr
          (MvPolynomial.esymm tau K (i.1 + 1)) := by
  simp [twoBlockEsymmAlgEquiv, nestedSymmetricTwoBlockFixedAlgEquiv,
    nestedSymmetricToTwoBlockFixed, nestedSymmetricToTwoBlockRaw,
    nestedSymmetricVal, MvPolynomial.esymmAlgEquiv_apply,
    MvPolynomial.esymmAlgHom]
  apply (MvPolynomial.sumAlgEquiv K sigma tau).injective
  simp
  have h := DFunLike.congr_fun
    (MvPolynomial.sumAlgEquiv_comp_rename_inr
      (R := K) (S₁ := sigma) (S₂ := tau))
    (MvPolynomial.esymm tau K (i.1 + 1))
  simpa using h.symm

end TwoBlockFundamentalTheorem

end

end VOA.TwoBlockSymmetricInvariant

