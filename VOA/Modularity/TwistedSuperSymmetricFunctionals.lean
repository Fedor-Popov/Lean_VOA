/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.SuperSymmetricFunctionals

/-!
# Sector-indexed supersymmetric functionals

This file formalizes the algebraic `h`-supersymmetry relation used by van Ekeren for a
parity-preserving finite-order automorphism.  It is independent of conformal weights,
square-bracket modes, convergence, rationality, and semisimplicity.

For parity-homogeneous eigenvectors

* `a ∈ A_p`, `h a = lambda • a`,
* `b ∈ A_q`, `h b = mu • b`,

with nonzero eigenvalues, the cyclic coefficient is

`if lambda * mu = 1 then koszul p q * lambda⁻¹ else 0`.

Thus an `h`-supersymmetric functional satisfies

`phi (a*b) = cyclicCoefficient * phi (b*a)`.

The eigenvector and nonzero-eigenvalue hypotheses are explicit in every generator and every
functional identity.  Neither diagonalizability nor existence of enough eigenvectors is hidden
in a structure.  Parity preservation and finite order are recorded as separate predicates:
they are hypotheses of the intended VOSA application, but are not needed for the formal
quotient-dual equivalence, which is valid for every algebra automorphism.

## Main results

* `twistedSuperCommSpan` and `hSupersymmetricFunctionals`;
* `hSupersymmetricFunctionalsEquivDualQuot`;
* the corresponding finrank and finite-dimensionality theorems;
* `twistedSuperCommSpan_refl` and `hSupersymmetricFunctionals_refl`: the `h = 1` sector is exactly
  the untwisted theory of `SuperSymmetricFunctionals.lean`.

## Status

Proved without `sorry`, `admit`, `native_decide`, or new axioms.
-/

namespace VOA

open Module (finrank)

universe u

variable {A : Type u} [Ring A] [Algebra ℂ A]

/-! ## Explicit hypotheses on the sector automorphism -/

/-- An algebra automorphism preserves the two parity subspaces. -/
def PreservesSuperParity (P : AssociativeSuperalgebra A) (h : A ≃ₐ[ℂ] A) : Prop :=
  ∀ (p : ZMod 2) ⦃a : A⦄, a ∈ P.parity p → h a ∈ P.parity p

/-- The automorphism has finite positive order.  This is deliberately a predicate, not a field
of the sector relation: the quotient-dual algebra works without it. -/
def IsFiniteOrderAlgAut (h : A ≃ₐ[ℂ] A) : Prop :=
  ∃ N : ℕ, 0 < N ∧ h ^ N = 1

/-- `a` is an `h`-eigenvector with explicitly specified eigenvalue `lambda`. -/
def IsAlgAutEigenvector (h : A ≃ₐ[ℂ] A) (lambda : ℂ) (a : A) : Prop :=
  h a = lambda • a

/-- Iterating an eigenvector equation raises the eigenvalue to the same power. -/
theorem algAut_pow_apply_of_isEigenvector (h : A ≃ₐ[ℂ] A) {lambda : ℂ} {a : A}
    (ha : IsAlgAutEigenvector h lambda a) (N : ℕ) :
    (h ^ N) a = lambda ^ N • a := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [pow_succ, AlgEquiv.mul_apply, ha, map_smul, ih, pow_succ, mul_smul]
      simp only [smul_smul, mul_comm]

/-- A nonzero eigenvector of a finite-order automorphism has a root-of-unity eigenvalue.
No diagonalizability assertion is used or produced. -/
theorem eigenvalue_pow_eq_one_of_pow_eq_one (h : A ≃ₐ[ℂ] A) {lambda : ℂ} {a : A}
    (ha : IsAlgAutEigenvector h lambda a) (ha0 : a ≠ 0) {N : ℕ} (hN : h ^ N = 1) :
    lambda ^ N = 1 := by
  have hp := algAut_pow_apply_of_isEigenvector h ha N
  rw [hN, AlgEquiv.one_apply] at hp
  have hz : (lambda ^ N - 1) • a = 0 := by
    rw [sub_smul, one_smul, ← hp, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_right ha0)

/-- The packaged finite-order predicate supplies a positive root-of-unity exponent for every
nonzero eigenvector. -/
theorem exists_eigenvalue_pow_eq_one_of_finiteOrder (h : A ≃ₐ[ℂ] A)
    (hfin : IsFiniteOrderAlgAut h) {lambda : ℂ} {a : A}
    (ha : IsAlgAutEigenvector h lambda a) (ha0 : a ≠ 0) :
    ∃ N : ℕ, 0 < N ∧ lambda ^ N = 1 := by
  obtain ⟨N, hNpos, hN⟩ := hfin
  exact ⟨N, hNpos, eigenvalue_pow_eq_one_of_pow_eq_one h ha ha0 hN⟩

/-! ## The sector coefficient and relation span -/

/-- The coefficient in van Ekeren's `h`-supersymmetry relation. -/
noncomputable def twistedSuperCyclicCoeff (p q : ZMod 2) (lambda mu : ℂ) : ℂ :=
  if lambda * mu = 1 then koszul p q * lambda⁻¹ else 0

@[simp] theorem twistedSuperCyclicCoeff_one_one (p q : ZMod 2) :
    twistedSuperCyclicCoeff p q 1 1 = koszul p q := by
  simp [twistedSuperCyclicCoeff]

/-- The span of the homogeneous, simultaneous parity/eigenvector sector relations. -/
def twistedSuperCommSpan (P : AssociativeSuperalgebra A) (h : A ≃ₐ[ℂ] A) :
    Submodule ℂ A :=
  Submodule.span ℂ {x : A | ∃ (p q : ZMod 2) (lambda mu : ℂ) (a b : A),
    lambda ≠ 0 ∧ mu ≠ 0 ∧
    a ∈ P.parity p ∧ b ∈ P.parity q ∧
    IsAlgAutEigenvector h lambda a ∧ IsAlgAutEigenvector h mu b ∧
    x = a * b - twistedSuperCyclicCoeff p q lambda mu • (b * a)}

/-- Each explicit homogeneous eigenvector relation belongs to its span. -/
theorem twisted_supercommutator_mem (P : AssociativeSuperalgebra A) (h : A ≃ₐ[ℂ] A)
    {p q : ZMod 2} {lambda mu : ℂ} {a b : A}
    (hlambda : lambda ≠ 0) (hmu : mu ≠ 0)
    (ha : a ∈ P.parity p) (hb : b ∈ P.parity q)
    (hala : IsAlgAutEigenvector h lambda a) (hmb : IsAlgAutEigenvector h mu b) :
    a * b - twistedSuperCyclicCoeff p q lambda mu • (b * a) ∈
      twistedSuperCommSpan P h :=
  Submodule.subset_span ⟨p, q, lambda, mu, a, b,
    hlambda, hmu, ha, hb, hala, hmb, rfl⟩

/-! ## `h`-supersymmetric functionals -/

/-- Linear functionals satisfying van Ekeren's sector cyclicity law on explicitly homogeneous
`h`-eigenvectors. -/
def hSupersymmetricFunctionals (P : AssociativeSuperalgebra A) (h : A ≃ₐ[ℂ] A) :
    Submodule ℂ (A →ₗ[ℂ] ℂ) where
  carrier := {phi : A →ₗ[ℂ] ℂ | ∀ (p q : ZMod 2) (lambda mu : ℂ) (a b : A),
    lambda ≠ 0 → mu ≠ 0 →
    a ∈ P.parity p → b ∈ P.parity q →
    IsAlgAutEigenvector h lambda a → IsAlgAutEigenvector h mu b →
    phi (a * b) = twistedSuperCyclicCoeff p q lambda mu * phi (b * a)}
  add_mem' := by
    intro phi psi hphi hpsi p q lambda mu a b hl hm ha hb hla hmb
    change phi (a * b) + psi (a * b) =
      twistedSuperCyclicCoeff p q lambda mu * (phi (b * a) + psi (b * a))
    rw [hphi p q lambda mu a b hl hm ha hb hla hmb,
      hpsi p q lambda mu a b hl hm ha hb hla hmb, mul_add]
  zero_mem' := by
    intro p q lambda mu a b hl hm ha hb hla hmb
    simp
  smul_mem' := by
    intro c phi hphi p q lambda mu a b hl hm ha hb hla hmb
    change c * phi (a * b) =
      twistedSuperCyclicCoeff p q lambda mu * (c * phi (b * a))
    rw [hphi p q lambda mu a b hl hm ha hb hla hmb]
    ring

@[simp] theorem mem_hSupersymmetricFunctionals
    {P : AssociativeSuperalgebra A} {h : A ≃ₐ[ℂ] A} {phi : A →ₗ[ℂ] ℂ} :
    phi ∈ hSupersymmetricFunctionals P h ↔
      ∀ (p q : ZMod 2) (lambda mu : ℂ) (a b : A),
        lambda ≠ 0 → mu ≠ 0 →
        a ∈ P.parity p → b ∈ P.parity q →
        IsAlgAutEigenvector h lambda a → IsAlgAutEigenvector h mu b →
        phi (a * b) = twistedSuperCyclicCoeff p q lambda mu * phi (b * a) := Iff.rfl

/-- An `h`-supersymmetric functional kills the sector relation span. -/
theorem twistedSuperCommSpan_le_ker_of_hSupersymmetric
    {P : AssociativeSuperalgebra A} {h : A ≃ₐ[ℂ] A} {phi : A →ₗ[ℂ] ℂ}
    (hphi : phi ∈ hSupersymmetricFunctionals P h) :
    twistedSuperCommSpan P h ≤ LinearMap.ker phi := by
  rw [twistedSuperCommSpan, Submodule.span_le]
  rintro _ ⟨p, q, lambda, mu, a, b, hl, hm, ha, hb, hla, hmb, rfl⟩
  change phi (a * b - twistedSuperCyclicCoeff p q lambda mu • (b * a)) = 0
  rw [map_sub, map_smul, hphi p q lambda mu a b hl hm ha hb hla hmb]
  simp

/-- Killing the relation span is sufficient for `h`-supersymmetry. -/
theorem mem_hSupersymmetricFunctionals_of_twistedSuperCommSpan_le_ker
    {P : AssociativeSuperalgebra A} {h : A ≃ₐ[ℂ] A} {phi : A →ₗ[ℂ] ℂ}
    (hphi : twistedSuperCommSpan P h ≤ LinearMap.ker phi) :
    phi ∈ hSupersymmetricFunctionals P h := by
  rw [mem_hSupersymmetricFunctionals]
  intro p q lambda mu a b hl hm ha hb hla hmb
  have hmem := hphi (twisted_supercommutator_mem P h hl hm ha hb hla hmb)
  rw [LinearMap.mem_ker, map_sub, map_smul, sub_eq_zero] at hmem
  exact hmem

/-! ## Quotient-dual equivalence -/

/-- Descent of an `h`-supersymmetric functional to the sector quotient. -/
noncomputable def hSupersymmetricLift (P : AssociativeSuperalgebra A) (h : A ≃ₐ[ℂ] A) :
    hSupersymmetricFunctionals P h →ₗ[ℂ]
      Module.Dual ℂ (A ⧸ twistedSuperCommSpan P h) where
  toFun phi := Submodule.liftQ _ phi.1 (twistedSuperCommSpan_le_ker_of_hSupersymmetric phi.2)
  map_add' phi psi := by
    refine LinearMap.ext fun q => ?_
    obtain ⟨x, rfl⟩ := (twistedSuperCommSpan P h).mkQ_surjective q
    rfl
  map_smul' c phi := by
    refine LinearMap.ext fun q => ?_
    obtain ⟨x, rfl⟩ := (twistedSuperCommSpan P h).mkQ_surjective q
    rfl

@[simp] theorem hSupersymmetricLift_apply_mk (P : AssociativeSuperalgebra A)
    (h : A ≃ₐ[ℂ] A) (phi : hSupersymmetricFunctionals P h) (a : A) :
    hSupersymmetricLift P h phi ((twistedSuperCommSpan P h).mkQ a) =
      (phi : A →ₗ[ℂ] ℂ) a := rfl

/-- Pullback from the sector quotient is `h`-supersymmetric. -/
theorem mem_hSupersymmetricFunctionals_comp_mkQ (P : AssociativeSuperalgebra A)
    (h : A ≃ₐ[ℂ] A) (psi : Module.Dual ℂ (A ⧸ twistedSuperCommSpan P h)) :
    (psi ∘ₗ (twistedSuperCommSpan P h).mkQ) ∈ hSupersymmetricFunctionals P h := by
  apply mem_hSupersymmetricFunctionals_of_twistedSuperCommSpan_le_ker
  intro x hx
  rw [LinearMap.mem_ker]
  change psi ((twistedSuperCommSpan P h).mkQ x) = 0
  have hzero : (twistedSuperCommSpan P h).mkQ x = 0 := by
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hx
  rw [hzero, map_zero]

/-- Pullback from the quotient as a linear map. -/
noncomputable def hSupersymmetricOfDualQuot (P : AssociativeSuperalgebra A)
    (h : A ≃ₐ[ℂ] A) :
    Module.Dual ℂ (A ⧸ twistedSuperCommSpan P h) →ₗ[ℂ]
      hSupersymmetricFunctionals P h where
  toFun psi := ⟨psi ∘ₗ (twistedSuperCommSpan P h).mkQ,
    mem_hSupersymmetricFunctionals_comp_mkQ P h psi⟩
  map_add' _ _ := Subtype.ext (LinearMap.ext fun _ => rfl)
  map_smul' _ _ := Subtype.ext (LinearMap.ext fun _ => rfl)

/-- Pullback is a right inverse to descent. -/
theorem hSupersymmetricLift_hSupersymmetricOfDualQuot (P : AssociativeSuperalgebra A)
    (h : A ≃ₐ[ℂ] A) (psi : Module.Dual ℂ (A ⧸ twistedSuperCommSpan P h)) :
    hSupersymmetricLift P h (hSupersymmetricOfDualQuot P h psi) = psi := by
  refine LinearMap.ext fun q => ?_
  obtain ⟨x, rfl⟩ := (twistedSuperCommSpan P h).mkQ_surjective q
  rfl

theorem hSupersymmetricLift_injective (P : AssociativeSuperalgebra A) (h : A ≃ₐ[ℂ] A) :
    Function.Injective (hSupersymmetricLift P h) := by
  intro phi psi hphi
  refine Subtype.ext (LinearMap.ext fun a => ?_)
  exact congrArg (fun f => f ((twistedSuperCommSpan P h).mkQ a)) hphi

theorem hSupersymmetricLift_surjective (P : AssociativeSuperalgebra A) (h : A ≃ₐ[ℂ] A) :
    Function.Surjective (hSupersymmetricLift P h) :=
  fun psi => ⟨hSupersymmetricOfDualQuot P h psi,
    hSupersymmetricLift_hSupersymmetricOfDualQuot P h psi⟩

/-- Canonical identification with the dual of the sector relation quotient. -/
noncomputable def hSupersymmetricFunctionalsEquivDualQuot
    (P : AssociativeSuperalgebra A) (h : A ≃ₐ[ℂ] A) :
    hSupersymmetricFunctionals P h ≃ₗ[ℂ]
      Module.Dual ℂ (A ⧸ twistedSuperCommSpan P h) :=
  LinearEquiv.ofBijective (hSupersymmetricLift P h)
    ⟨hSupersymmetricLift_injective P h, hSupersymmetricLift_surjective P h⟩

/-- Dimension equality without rationality or semisimplicity. -/
theorem finrank_hSupersymmetricFunctionals_eq_finrank_quot
    (P : AssociativeSuperalgebra A) (h : A ≃ₐ[ℂ] A) :
    finrank ℂ (hSupersymmetricFunctionals P h) =
      finrank ℂ (A ⧸ twistedSuperCommSpan P h) := by
  rw [(hSupersymmetricFunctionalsEquivDualQuot P h).finrank_eq, Subspace.dual_finrank_eq]

/-- Sharp finite-dimensionality from the quotient alone. -/
theorem finiteDimensional_hSupersymmetricFunctionals_of_quot
    (P : AssociativeSuperalgebra A) (h : A ≃ₐ[ℂ] A)
    [FiniteDimensional ℂ (A ⧸ twistedSuperCommSpan P h)] :
    FiniteDimensional ℂ (hSupersymmetricFunctionals P h) :=
  (hSupersymmetricFunctionalsEquivDualQuot P h).symm.finiteDimensional

/-- Finite-dimensionality when the underlying algebra is finite-dimensional. -/
theorem finiteDimensional_hSupersymmetricFunctionals
    (P : AssociativeSuperalgebra A) (h : A ≃ₐ[ℂ] A) [FiniteDimensional ℂ A] :
    FiniteDimensional ℂ (hSupersymmetricFunctionals P h) :=
  finiteDimensional_hSupersymmetricFunctionals_of_quot P h

/-! ## The identity sector is the untwisted supertrace theory -/

private theorem eigenvalue_eq_one_of_refl {lambda : ℂ} {a : A} (ha0 : a ≠ 0)
    (ha : IsAlgAutEigenvector (AlgEquiv.refl : A ≃ₐ[ℂ] A) lambda a) : lambda = 1 := by
  have hae : a = lambda • a := by simpa [IsAlgAutEigenvector] using ha
  have hz : (lambda - 1) • a = 0 := by
    rw [sub_smul, one_smul, ← hae, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_right ha0)

/-- In the identity sector, the twisted relation span is exactly the ordinary
supercommutator span. -/
theorem twistedSuperCommSpan_refl (P : AssociativeSuperalgebra A) :
    twistedSuperCommSpan P (AlgEquiv.refl : A ≃ₐ[ℂ] A) = superCommSpan P := by
  apply le_antisymm
  · rw [twistedSuperCommSpan, Submodule.span_le]
    rintro _ ⟨p, q, lambda, mu, a, b, hl, hm, ha, hb, hla, hmb, rfl⟩
    by_cases ha0 : a = 0
    · subst a
      simp
    by_cases hb0 : b = 0
    · subst b
      simp
    have hl1 := eigenvalue_eq_one_of_refl ha0 hla
    have hm1 := eigenvalue_eq_one_of_refl hb0 hmb
    subst lambda
    subst mu
    simpa using mul_sub_koszul_smul_mul_mem_superCommSpan P ha hb
  · rw [superCommSpan, Submodule.span_le]
    rintro _ ⟨p, q, a, b, ha, hb, rfl⟩
    simpa using twisted_supercommutator_mem P (AlgEquiv.refl : A ≃ₐ[ℂ] A)
      one_ne_zero one_ne_zero ha hb (by simp [IsAlgAutEigenvector])
        (by simp [IsAlgAutEigenvector])

/-- In the identity sector, `h`-supersymmetric functionals are exactly the untwisted
supersymmetric functionals. -/
theorem hSupersymmetricFunctionals_refl (P : AssociativeSuperalgebra A) :
    hSupersymmetricFunctionals P (AlgEquiv.refl : A ≃ₐ[ℂ] A) =
      supersymmetricFunctionals P := by
  apply le_antisymm
  · intro phi hphi
    rw [mem_supersymmetricFunctionals]
    intro p q a b ha hb
    have h := hphi p q 1 1 a b one_ne_zero one_ne_zero ha hb
      (by simp [IsAlgAutEigenvector]) (by simp [IsAlgAutEigenvector])
    simpa using h
  · intro phi hphi
    rw [mem_hSupersymmetricFunctionals]
    intro p q lambda mu a b hl hm ha hb hla hmb
    by_cases ha0 : a = 0
    · subst a
      simp
    by_cases hb0 : b = 0
    · subst b
      simp
    have hl1 := eigenvalue_eq_one_of_refl ha0 hla
    have hm1 := eigenvalue_eq_one_of_refl hb0 hmb
    subst lambda
    subst mu
    simpa using hphi p q a b ha hb

end VOA
