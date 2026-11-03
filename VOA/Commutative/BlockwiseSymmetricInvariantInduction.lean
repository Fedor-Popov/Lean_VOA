/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Commutative.TwoBlockSymmetricInvariant

/-!
# Adjoining one symmetric block to an invariant presentation

This file is the induction engine for arbitrary Young-parabolic invariant rings.  The right-hand
variables may already carry an arbitrary family of permutations.  Adjoining a new left block and
requiring full symmetry in that block produces outer symmetric polynomials with coefficients in
the old fixed subalgebra.

No group laws are needed: fixedness under a family of permutations is enough.  Consequently this
applies directly to the independent colorwise relabelings of a boundary root profile.
-/

namespace VOA.BlockwiseSymmetricInvariantInduction

open VOA.TwoBlockSymmetricInvariant

noncomputable section

universe u v w x

variable {K : Type u} [CommRing K]
variable {sigma : Type v} {tau : Type w} {H : Type x}

/-- Fixed polynomials for an arbitrary family of permutations of the right variables. -/
def rightFixedSubalgebra (act : H → Equiv.Perm tau) :
    Subalgebra K (MvPolynomial tau K) where
  carrier := {p | ∀ h, MvPolynomial.rename (act h) p = p}
  algebraMap_mem' r h := MvPolynomial.rename_C _ _
  add_mem' {p q} hp hq h := by rw [map_add, hp h, hq h]
  mul_mem' {p q} hp hq h := by rw [map_mul, hp h, hq h]

/-- Simultaneous fixed polynomials after adjoining a fully symmetric left block. -/
def extendedFixedSubalgebra (act : H → Equiv.Perm tau) :
    Subalgebra K (MvPolynomial (sigma ⊕ tau) K) where
  carrier := {p | ∀ (e : Equiv.Perm sigma) (h : H),
    MvPolynomial.rename (blockPermutation e (act h)) p = p}
  algebraMap_mem' r e h := MvPolynomial.rename_C _ _
  add_mem' {p q} hp hq e h := by rw [map_add, hp e h, hq e h]
  mul_mem' {p q} hp hq e h := by rw [map_mul, hp e h, hq e h]

/-- Right-family invariance of a sum-polynomial makes every outer coefficient right-fixed. -/
theorem coefficient_mem_rightFixed_of_invariant (act : H → Equiv.Perm tau)
    (p : MvPolynomial (sigma ⊕ tau) K)
    (hp : ∀ h : H,
      MvPolynomial.rename (blockPermutation (Equiv.refl sigma) (act h)) p = p)
    (d : sigma →₀ ℕ) :
    (MvPolynomial.sumAlgEquiv K sigma tau p).coeff d ∈
      rightFixedSubalgebra (K := K) act := by
  intro h
  have hcov := sumAlgEquiv_rename_blockPermutation
    (K := K) (sigma := sigma) (tau := tau) (Equiv.refl sigma) (act h) p
  rw [hp h] at hcov
  have hcoeff := congrArg (MvPolynomial.coeff d) hcov
  simpa [MvPolynomial.coeff_map] using hcoeff.symm

/-- Lift the iterated polynomial associated to a right-invariant polynomial to coefficients in
the right fixed subalgebra. -/
def rightFixedLift (act : H → Equiv.Perm tau)
    (p : MvPolynomial (sigma ⊕ tau) K)
    (hp : ∀ h : H,
      MvPolynomial.rename (blockPermutation (Equiv.refl sigma) (act h)) p = p) :
    MvPolynomial sigma (rightFixedSubalgebra (K := K) act) :=
  liftCoefficientsToSubalgebra (K := K) (rightFixedSubalgebra (K := K) act)
    (MvPolynomial.sumAlgEquiv K sigma tau p)
    (coefficient_mem_rightFixed_of_invariant
      (K := K) (sigma := sigma) act p hp)

/-- Forgetting the fixed-coefficient proofs recovers the iterated form. -/
theorem map_rightFixedLift (act : H → Equiv.Perm tau)
    (p : MvPolynomial (sigma ⊕ tau) K)
    (hp : ∀ h : H,
      MvPolynomial.rename (blockPermutation (Equiv.refl sigma) (act h)) p = p) :
    MvPolynomial.map (rightFixedSubalgebra (K := K) act).val
        (rightFixedLift (K := K) (sigma := sigma) act p hp) =
      MvPolynomial.sumAlgEquiv K sigma tau p :=
  map_liftCoefficientsToSubalgebra (K := K)
    (rightFixedSubalgebra (K := K) act)
    (MvPolynomial.sumAlgEquiv K sigma tau p)
    (coefficient_mem_rightFixed_of_invariant
      (K := K) (sigma := sigma) act p hp)

/-- Simultaneous invariance makes the fixed-coefficient lift symmetric in the new block. -/
theorem rightFixedLift_isSymmetric (act : H → Equiv.Perm tau)
    (hId : H) (hact : act hId = Equiv.refl tau)
    (p : MvPolynomial (sigma ⊕ tau) K)
    (hp : ∀ (e : Equiv.Perm sigma) (h : H),
      MvPolynomial.rename (blockPermutation e (act h)) p = p) :
    (rightFixedLift (K := K) (sigma := sigma) act p (hp (Equiv.refl sigma))).IsSymmetric := by
  intro e
  apply map_subalgebraVal_injective (K := K) (rightFixedSubalgebra (K := K) act)
  rw [MvPolynomial.map_rename]
  rw [map_rightFixedLift]
  have hcov := sumAlgEquiv_rename_blockPermutation
    (K := K) (sigma := sigma) (tau := tau) e (Equiv.refl tau) p
  let h0 : (MvPolynomial.rename (R := K) (Equiv.refl tau)).toRingHom =
      RingHom.id (MvPolynomial tau K) := by
    change (MvPolynomial.rename (R := K) id).toRingHom = _
    rw [MvPolynomial.rename_id]
    rfl
  have hid : MvPolynomial.map
      (MvPolynomial.rename (R := K) (Equiv.refl tau)).toRingHom
      (MvPolynomial.sumAlgEquiv K sigma tau p) =
        MvPolynomial.sumAlgEquiv K sigma tau p := by
    rw [h0]
    exact MvPolynomial.map_id _
  rw [hid] at hcov
  -- The designated identity element of the right family supplies pure left invariance.
  rw [← hact] at hcov
  rw [hp e hId] at hcov
  exact hcov.symm

section PointedFamily

/-- The nested fixed/symmetric lift of a simultaneously invariant polynomial. -/
def nestedFixedLift (act : H → Equiv.Perm tau)
    (hId : H) (hact : act hId = Equiv.refl tau)
    (p : MvPolynomial (sigma ⊕ tau) K)
    (hp : ∀ (e : Equiv.Perm sigma) (h : H),
      MvPolynomial.rename (blockPermutation e (act h)) p = p) :
    MvPolynomial.symmetricSubalgebra sigma (rightFixedSubalgebra (K := K) act) :=
  ⟨rightFixedLift (K := K) (sigma := sigma) act p (hp (Equiv.refl sigma)),
    rightFixedLift_isSymmetric (K := K) (sigma := sigma) act hId hact p hp⟩

/-- Ground-ring form of the outer symmetric-subalgebra inclusion. -/
def nestedFixedVal (act : H → Equiv.Perm tau) :
    MvPolynomial.symmetricSubalgebra sigma (rightFixedSubalgebra (K := K) act) →ₐ[K]
      MvPolynomial sigma (rightFixedSubalgebra (K := K) act) where
  toFun q := q.1
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- Forget nested fixedness and symmetry, returning to the sum of variable blocks. -/
def nestedFixedToExtendedRaw (act : H → Equiv.Perm tau) :
    MvPolynomial.symmetricSubalgebra sigma (rightFixedSubalgebra (K := K) act) →ₐ[K]
      MvPolynomial (sigma ⊕ tau) K :=
  (MvPolynomial.sumAlgEquiv K sigma tau).symm.toAlgHom.comp
    ((MvPolynomial.mapAlgHom (R := K) (σ := sigma)
      (rightFixedSubalgebra (K := K) act).val).comp
        (nestedFixedVal (K := K) (sigma := sigma) act))

theorem sumAlgEquiv_nestedFixedToExtendedRaw (act : H → Equiv.Perm tau)
    (q : MvPolynomial.symmetricSubalgebra sigma
      (rightFixedSubalgebra (K := K) act)) :
    MvPolynomial.sumAlgEquiv K sigma tau
        (nestedFixedToExtendedRaw (K := K) (sigma := sigma) act q) =
      MvPolynomial.map (rightFixedSubalgebra (K := K) act).val.toRingHom q.1 := by
  simp [nestedFixedToExtendedRaw]
  rfl

theorem nestedFixedToExtendedRaw_mem (act : H → Equiv.Perm tau)
    (q : MvPolynomial.symmetricSubalgebra sigma
      (rightFixedSubalgebra (K := K) act)) :
    nestedFixedToExtendedRaw (K := K) (sigma := sigma) act q ∈
      extendedFixedSubalgebra (K := K) (sigma := sigma) act := by
  intro e h
  apply (MvPolynomial.sumAlgEquiv K sigma tau).injective
  rw [sumAlgEquiv_rename_blockPermutation]
  rw [sumAlgEquiv_nestedFixedToExtendedRaw]
  have hright :
      MvPolynomial.map (MvPolynomial.rename (act h)).toRingHom
          (MvPolynomial.map (rightFixedSubalgebra (K := K) act).val.toRingHom q.1) =
        MvPolynomial.map (rightFixedSubalgebra (K := K) act).val.toRingHom q.1 := by
    apply MvPolynomial.ext
    intro d
    simp only [MvPolynomial.coeff_map]
    exact (q.1.coeff d).2 h
  rw [hright]
  rw [← MvPolynomial.map_rename]
  exact congrArg (MvPolynomial.map
    (rightFixedSubalgebra (K := K) act).val.toRingHom) (q.2 e)

/-- Nested fixed/symmetric polynomials map to the extended fixed subalgebra. -/
def nestedFixedToExtended (act : H → Equiv.Perm tau) :
    MvPolynomial.symmetricSubalgebra sigma (rightFixedSubalgebra (K := K) act) →ₐ[K]
      extendedFixedSubalgebra (K := K) (sigma := sigma) act :=
  (nestedFixedToExtendedRaw (K := K) (sigma := sigma) act).codRestrict
    (extendedFixedSubalgebra (K := K) (sigma := sigma) act)
    (nestedFixedToExtendedRaw_mem (K := K) (sigma := sigma) act)

theorem nestedFixedToExtended_injective (act : H → Equiv.Perm tau) :
    Function.Injective (nestedFixedToExtended (K := K) (sigma := sigma) act) := by
  intro p q hpq
  apply Subtype.ext
  apply map_subalgebraVal_injective (K := K) (rightFixedSubalgebra (K := K) act)
  have hraw := congrArg Subtype.val hpq
  change nestedFixedToExtendedRaw (K := K) (sigma := sigma) act p =
    nestedFixedToExtendedRaw (K := K) (sigma := sigma) act q at hraw
  have hiter := congrArg (MvPolynomial.sumAlgEquiv K sigma tau) hraw
  rw [sumAlgEquiv_nestedFixedToExtendedRaw,
    sumAlgEquiv_nestedFixedToExtendedRaw] at hiter
  exact hiter

theorem nestedFixedToExtended_surjective (act : H → Equiv.Perm tau)
    (hId : H) (hact : act hId = Equiv.refl tau) :
    Function.Surjective (nestedFixedToExtended (K := K) (sigma := sigma) act) := by
  intro p
  let q := nestedFixedLift (K := K) (sigma := sigma) act hId hact p.1 p.2
  refine ⟨q, ?_⟩
  apply Subtype.ext
  apply (MvPolynomial.sumAlgEquiv K sigma tau).injective
  change MvPolynomial.sumAlgEquiv K sigma tau
      (nestedFixedToExtendedRaw (K := K) (sigma := sigma) act q) =
    MvPolynomial.sumAlgEquiv K sigma tau p.1
  rw [sumAlgEquiv_nestedFixedToExtendedRaw]
  exact map_rightFixedLift (K := K) (sigma := sigma) act p.1
    (p.2 (Equiv.refl sigma))

/-- Adjoining a fully symmetric block turns an old fixed-subalgebra presentation into the
nested presentation of the enlarged fixed subalgebra. -/
def nestedFixedExtendedAlgEquiv (act : H → Equiv.Perm tau)
    (hId : H) (hact : act hId = Equiv.refl tau) :
    MvPolynomial.symmetricSubalgebra sigma (rightFixedSubalgebra (K := K) act) ≃ₐ[K]
      extendedFixedSubalgebra (K := K) (sigma := sigma) act :=
  AlgEquiv.ofBijective (nestedFixedToExtended (K := K) (sigma := sigma) act)
    ⟨nestedFixedToExtended_injective (K := K) (sigma := sigma) act,
     nestedFixedToExtended_surjective (K := K) (sigma := sigma) act hId hact⟩

section FundamentalTheorem

variable [Fintype sigma]
variable {Q : Type*} [CommRing Q] [Algebra K Q]

/-- Product step for invariant presentations: if `Q` presents the old fixed subalgebra, then a
polynomial ring over `Q` in the elementary coordinates of a new block presents the enlarged
fixed subalgebra. -/
def extendFixedPresentation (act : H → Equiv.Perm tau)
    (hId : H) (hact : act hId = Equiv.refl tau)
    (a : ℕ) (ha : Fintype.card sigma = a)
    (old : Q ≃ₐ[K] rightFixedSubalgebra (K := K) act) :
    MvPolynomial (Fin a) Q ≃ₐ[K]
      extendedFixedSubalgebra (K := K) (sigma := sigma) act :=
  (MvPolynomial.mapAlgEquiv (Fin a) old).trans
        (((MvPolynomial.esymmAlgEquiv sigma
      (rightFixedSubalgebra (K := K) act) ha).restrictScalars K).trans
        (nestedFixedExtendedAlgEquiv (K := K) (sigma := sigma) act hId hact))

end FundamentalTheorem

end PointedFamily

end


end VOA.BlockwiseSymmetricInvariantInduction

