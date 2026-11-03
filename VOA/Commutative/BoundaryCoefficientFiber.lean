/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Commutative.BoundaryCollisionDivisibility

/-!
# Fibers of the boundary collision substitutions

This file records the exact fibers of the two typed label maps used in the polarized
`XZ - Y^2` relation.  The collision coordinate has a two-element fiber, while every passive
coordinate has a singleton fiber.  These are the finite combinatorial statements needed to
identify coefficients of substituted particle polynomials with the ordered convolution sums.
-/

namespace VOA.BoundaryCoefficientFiber

open VOA.BoundaryTypedSubstitution
open VOA.BoundaryCollisionDivisibility
open VOA.ModeParticlePairing
open VOA.ModeParticlePolynomial
open VOA.MultispeciesParticlePolynomial

noncomputable section

/-- The only `XZ` labels mapping to the collision coordinate are the inserted `X` and `Z`
labels. -/
theorem xzToDiagonalLabel_eq_collision_iff (a b c d : ℕ)
    (i : XZLabel a b c d) :
    xzToDiagonalLabel a b c d i = Sum.inl () ↔
      i = newXZLabelX a b c d ∨ i = newXZLabelZ a b c d := by
  rcases i with ⟨A, i⟩
  cases A
  · refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp [xzToDiagonalLabel, newXZLabelX, newXZLabelZ]
    · simp [xzToDiagonalLabel, newXZLabelX, newXZLabelZ]
      exact Fin.succ_ne_zero j
  · simp [xzToDiagonalLabel, newXZLabelX, newXZLabelZ]
  · refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp [xzToDiagonalLabel, newXZLabelX, newXZLabelZ]
    · simp [xzToDiagonalLabel, newXZLabelX, newXZLabelZ]
      exact Fin.succ_ne_zero j
  · simp [xzToDiagonalLabel, newXZLabelX, newXZLabelZ]

/-- Every passive `XZ` coordinate has exactly one preimage. -/
theorem xzToDiagonalLabel_eq_passive_iff (a b c d : ℕ)
    (i : XZLabel a b c d)
    (j : SpeciesLabel (boundaryMultiplicity a b c d)) :
    xzToDiagonalLabel a b c d i = Sum.inr j ↔
      i = liftXZPassiveLabel a b c d j := by
  constructor
  · intro h
    have hi : i ≠ newXZLabelX a b c d := by
      intro hi
      subst i
      simp at h
    have hcollision : xzToDiagonalLabel a b c d
        (liftXZPassiveLabel a b c d j) = Sum.inr j :=
      xzToDiagonalLabel_passive a b c d j
    have heq : (xzResidualEquiv a b c d) ⟨i, hi⟩ =
        (xzResidualEquiv a b c d)
          ⟨liftXZPassiveLabel a b c d j,
            liftXZPassiveLabel_ne_newXZLabelX a b c d j⟩ :=
      h.trans hcollision.symm
    exact congrArg Subtype.val ((xzResidualEquiv a b c d).injective heq)
  · rintro rfl
    exact xzToDiagonalLabel_passive a b c d j

/-- The only `YY` labels mapping to the collision coordinate are the two inserted `Y`
labels. -/
theorem yyToDiagonalLabel_eq_collision_iff (a b c d : ℕ)
    (i : YYLabel a b c d) :
    yyToDiagonalLabel a b c d i = Sum.inl () ↔
      i = newYYLabelZero a b c d ∨ i = newYYLabelOne a b c d := by
  rcases i with ⟨A, i⟩
  cases A
  · simp [yyToDiagonalLabel, newYYLabelZero, newYYLabelOne]
  · refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp [yyToDiagonalLabel, newYYLabelZero, newYYLabelOne]
    · refine Fin.cases ?_ (fun k ↦ ?_) j
      · simpa [newYYLabelOne] using yyToDiagonalLabel_newY_one a b c d
      · constructor
        · intro h
          simp only [yyToDiagonalLabel] at h
          contradiction
        · rintro (h | h)
          · have hv := congrArg
              (fun q : YYLabel a b c d ↦ (q.2 : ℕ)) h
            simp [newYYLabelZero] at hv
          · have hv := congrArg
              (fun q : YYLabel a b c d ↦ (q.2 : ℕ)) h
            simp [newYYLabelOne] at hv
  · simp [yyToDiagonalLabel, newYYLabelZero, newYYLabelOne]
  · simp [yyToDiagonalLabel, newYYLabelZero, newYYLabelOne]

/-- Every passive `YY` coordinate has exactly one preimage. -/
theorem yyToDiagonalLabel_eq_passive_iff (a b c d : ℕ)
    (i : YYLabel a b c d)
    (j : SpeciesLabel (boundaryMultiplicity a b c d)) :
    yyToDiagonalLabel a b c d i = Sum.inr j ↔
      i = liftYYPassiveLabel a b c d j := by
  constructor
  · intro h
    have hi : i ≠ newYYLabelZero a b c d := by
      intro hi
      subst i
      simp at h
    have hcollision : yyToDiagonalLabel a b c d
        (liftYYPassiveLabel a b c d j) = Sum.inr j :=
      yyToDiagonalLabel_passive a b c d j
    have heq : (yyResidualEquiv a b c d) ⟨i, hi⟩ =
        (yyResidualEquiv a b c d)
          ⟨liftYYPassiveLabel a b c d j,
            liftYYPassiveLabel_ne_newYYLabelZero a b c d j⟩ :=
      h.trans hcollision.symm
    exact congrArg Subtype.val ((yyResidualEquiv a b c d).injective heq)
  · rintro rfl
    exact yyToDiagonalLabel_passive a b c d j

section ExponentFibers

/-- On exponent vectors, the `XZ` collision coordinate is the sum of the two active
exponents. -/
@[simp]
theorem mapDomain_xzToDiagonalLabel_apply_collision (a b c d : ℕ)
    (e : XZLabel a b c d →₀ ℕ) :
    Finsupp.mapDomain (xzToDiagonalLabel a b c d) e
        (Sum.inl () : BoundaryDiagonalLabel a b c d) =
      e (newXZLabelX a b c d) + e (newXZLabelZ a b c d) := by
  classical
  induction e using Finsupp.induction with
  | zero => simp
  | single_add i n e hi hn ih =>
      rw [Finsupp.mapDomain_add, Finsupp.add_apply, Finsupp.add_apply,
        Finsupp.add_apply, ih, Finsupp.mapDomain_single]
      by_cases hiX : i = newXZLabelX a b c d
      · subst i
        simp [newXZLabelZ_ne_newXZLabelX]
        omega
      · by_cases hiZ : i = newXZLabelZ a b c d
        · subst i
          simp [newXZLabelZ_ne_newXZLabelX]
          omega
        · have hdiag : xzToDiagonalLabel a b c d i ≠ Sum.inl () := by
            simpa [xzToDiagonalLabel_eq_collision_iff] using
              not_or_intro hiX hiZ
          simp [hiX, hiZ, hdiag]

/-- On exponent vectors, every passive `XZ` coordinate retains precisely its unique source
exponent. -/
@[simp]
theorem mapDomain_xzToDiagonalLabel_apply_passive (a b c d : ℕ)
    (e : XZLabel a b c d →₀ ℕ)
    (j : SpeciesLabel (boundaryMultiplicity a b c d)) :
    Finsupp.mapDomain (xzToDiagonalLabel a b c d) e (Sum.inr j) =
      e (liftXZPassiveLabel a b c d j) := by
  classical
  induction e using Finsupp.induction with
  | zero => simp
  | single_add i n e hi hn ih =>
      rw [Finsupp.mapDomain_add, Finsupp.add_apply, Finsupp.add_apply,
        ih, Finsupp.mapDomain_single]
      by_cases hij : i = liftXZPassiveLabel a b c d j
      · subst i
        simp
      · have hdiag : xzToDiagonalLabel a b c d i ≠ Sum.inr j := by
          simpa [xzToDiagonalLabel_eq_passive_iff] using hij
        simp [hij, hdiag]

/-- On exponent vectors, the `YY` collision coordinate is the sum of the two active
exponents. -/
@[simp]
theorem mapDomain_yyToDiagonalLabel_apply_collision (a b c d : ℕ)
    (e : YYLabel a b c d →₀ ℕ) :
    Finsupp.mapDomain (yyToDiagonalLabel a b c d) e
        (Sum.inl () : BoundaryDiagonalLabel a b c d) =
      e (newYYLabelZero a b c d) + e (newYYLabelOne a b c d) := by
  classical
  induction e using Finsupp.induction with
  | zero => simp
  | single_add i n e hi hn ih =>
      rw [Finsupp.mapDomain_add, Finsupp.add_apply, Finsupp.add_apply,
        Finsupp.add_apply, ih, Finsupp.mapDomain_single]
      by_cases hiZero : i = newYYLabelZero a b c d
      · subst i
        simp [newYYLabelOne_ne_newYYLabelZero]
        omega
      · by_cases hiOne : i = newYYLabelOne a b c d
        · subst i
          simp [newYYLabelOne_ne_newYYLabelZero]
          omega
        · have hdiag : yyToDiagonalLabel a b c d i ≠ Sum.inl () := by
            simpa [yyToDiagonalLabel_eq_collision_iff] using
              not_or_intro hiZero hiOne
          simp [hiZero, hiOne, hdiag]

/-- On exponent vectors, every passive `YY` coordinate retains precisely its unique source
exponent. -/
@[simp]
theorem mapDomain_yyToDiagonalLabel_apply_passive (a b c d : ℕ)
    (e : YYLabel a b c d →₀ ℕ)
    (j : SpeciesLabel (boundaryMultiplicity a b c d)) :
    Finsupp.mapDomain (yyToDiagonalLabel a b c d) e (Sum.inr j) =
      e (liftYYPassiveLabel a b c d j) := by
  classical
  induction e using Finsupp.induction with
  | zero => simp
  | single_add i n e hi hn ih =>
      rw [Finsupp.mapDomain_add, Finsupp.add_apply, Finsupp.add_apply,
        ih, Finsupp.mapDomain_single]
      by_cases hij : i = liftYYPassiveLabel a b c d j
      · subst i
        simp
      · have hdiag : yyToDiagonalLabel a b c d i ≠ Sum.inr j := by
          simpa [yyToDiagonalLabel_eq_passive_iff] using hij
        simp [hij, hdiag]

/-- Complete fiber classification for the `XZ` exponent map: equality with a prescribed
diagonal exponent is equivalent to the one active sum equation and equality at every passive
label. -/
theorem mapDomain_xzToDiagonalLabel_eq_iff (a b c d q : ℕ)
    (e : XZLabel a b c d →₀ ℕ)
    (v : SpeciesLabel (boundaryMultiplicity a b c d) →₀ ℕ) :
    Finsupp.mapDomain (xzToDiagonalLabel a b c d) e =
        Finsupp.single (Sum.inl () : BoundaryDiagonalLabel a b c d) q +
          Finsupp.mapDomain Sum.inr v ↔
      e (newXZLabelX a b c d) + e (newXZLabelZ a b c d) = q ∧
        ∀ j, e (liftXZPassiveLabel a b c d j) = v j := by
  constructor
  · intro h
    constructor
    · have hc := congrArg
          (fun w : BoundaryDiagonalLabel a b c d →₀ ℕ ↦ w (Sum.inl ())) h
      have hzero : Finsupp.mapDomain Sum.inr v
          (Sum.inl () : BoundaryDiagonalLabel a b c d) = 0 :=
        Finsupp.mapDomain_notin_range v _ (by simp)
      simpa [hzero] using hc
    · intro j
      have hp := congrArg
        (fun w : BoundaryDiagonalLabel a b c d →₀ ℕ ↦ w (Sum.inr j)) h
      change Finsupp.mapDomain (xzToDiagonalLabel a b c d) e (Sum.inr j) =
        ((Finsupp.single (Sum.inl ()) q + Finsupp.mapDomain Sum.inr v :
          BoundaryDiagonalLabel a b c d →₀ ℕ) (Sum.inr j)) at hp
      rw [Finsupp.add_apply, Finsupp.single_eq_of_ne (by simp), zero_add,
        Finsupp.mapDomain_apply Sum.inr_injective v j] at hp
      simpa using hp
  · rintro ⟨hc, hp⟩
    ext i
    rcases i with (u | j)
    · rcases u with ⟨⟩
      have hzero : Finsupp.mapDomain Sum.inr v
          (Sum.inl () : BoundaryDiagonalLabel a b c d) = 0 :=
        Finsupp.mapDomain_notin_range v _ (by simp)
      simpa [hzero] using hc
    · rw [Finsupp.add_apply, Finsupp.single_eq_of_ne (by simp), zero_add,
        Finsupp.mapDomain_apply Sum.inr_injective v j]
      simpa using hp j

/-- Complete fiber classification for the `YY` exponent map. -/
theorem mapDomain_yyToDiagonalLabel_eq_iff (a b c d q : ℕ)
    (e : YYLabel a b c d →₀ ℕ)
    (v : SpeciesLabel (boundaryMultiplicity a b c d) →₀ ℕ) :
    Finsupp.mapDomain (yyToDiagonalLabel a b c d) e =
        Finsupp.single (Sum.inl () : BoundaryDiagonalLabel a b c d) q +
          Finsupp.mapDomain Sum.inr v ↔
      e (newYYLabelZero a b c d) + e (newYYLabelOne a b c d) = q ∧
        ∀ j, e (liftYYPassiveLabel a b c d j) = v j := by
  constructor
  · intro h
    constructor
    · have hc := congrArg
          (fun w : BoundaryDiagonalLabel a b c d →₀ ℕ ↦ w (Sum.inl ())) h
      have hzero : Finsupp.mapDomain Sum.inr v
          (Sum.inl () : BoundaryDiagonalLabel a b c d) = 0 :=
        Finsupp.mapDomain_notin_range v _ (by simp)
      simpa [hzero] using hc
    · intro j
      have hp := congrArg
        (fun w : BoundaryDiagonalLabel a b c d →₀ ℕ ↦ w (Sum.inr j)) h
      change Finsupp.mapDomain (yyToDiagonalLabel a b c d) e (Sum.inr j) =
        ((Finsupp.single (Sum.inl ()) q + Finsupp.mapDomain Sum.inr v :
          BoundaryDiagonalLabel a b c d →₀ ℕ) (Sum.inr j)) at hp
      rw [Finsupp.add_apply, Finsupp.single_eq_of_ne (by simp), zero_add,
        Finsupp.mapDomain_apply Sum.inr_injective v j] at hp
      simpa using hp
  · rintro ⟨hc, hp⟩
    ext i
    rcases i with (u | j)
    · rcases u with ⟨⟩
      have hzero : Finsupp.mapDomain Sum.inr v
          (Sum.inl () : BoundaryDiagonalLabel a b c d) = 0 :=
        Finsupp.mapDomain_notin_range v _ (by simp)
      simpa [hzero] using hc
    · rw [Finsupp.add_apply, Finsupp.single_eq_of_ne (by simp), zero_add,
        Finsupp.mapDomain_apply Sum.inr_injective v j]
      simpa using hp j

end ExponentFibers

section PolynomialCoefficients

universe u

variable {K : Type u} [Field K]

/-- Coefficients after the typed `XZ` substitution are exactly the finite sum over labelled mode
tuples in the corresponding exponent fiber. -/
theorem coeff_xzDiagonalSubstitution_shiftedMultispeciesParticlePolynomial
    {jetOrder a b c d : ℕ}
    (F : MultispeciesJetParticleSpace K jetOrder
      (boundaryMultiplicity (a + 1) b (c + 1) d))
    (target : BoundaryDiagonalLabel a b c d →₀ ℕ) :
    MvPolynomial.coeff target
        (xzDiagonalSubstitution (K := K) a b c d
          (shiftedMultispeciesParticlePolynomial boundarySpeciesShift F)) =
      ∑ r : MultispeciesModeTuple jetOrder
          (boundaryMultiplicity (a + 1) b (c + 1) d),
        if Finsupp.mapDomain (xzToDiagonalLabel a b c d)
              (shiftedMultispeciesLabelledExponent boundarySpeciesShift r) = target
        then F (multispeciesUnorderedModeBlock r) else 0 := by
  classical
  simp only [xzDiagonalSubstitution, shiftedMultispeciesParticlePolynomial, map_sum,
    MvPolynomial.coeff_sum, MvPolynomial.rename_monomial, MvPolynomial.coeff_monomial]
  apply Finset.sum_congr (by ext; simp)
  intro r _
  rfl

/-- Coefficients after the typed `YY` substitution are exactly the finite sum over labelled mode
tuples in its exponent fiber.  The two orders of unequal active exponents occur as two distinct
tuples in this sum. -/
theorem coeff_yyDiagonalSubstitution_shiftedMultispeciesParticlePolynomial
    {jetOrder a b c d : ℕ}
    (F : MultispeciesJetParticleSpace K jetOrder
      (boundaryMultiplicity a (b + 2) c d))
    (target : BoundaryDiagonalLabel a b c d →₀ ℕ) :
    MvPolynomial.coeff target
        (yyDiagonalSubstitution (K := K) a b c d
          (shiftedMultispeciesParticlePolynomial boundarySpeciesShift F)) =
      ∑ r : MultispeciesModeTuple jetOrder
          (boundaryMultiplicity a (b + 2) c d),
        if Finsupp.mapDomain (yyToDiagonalLabel a b c d)
              (shiftedMultispeciesLabelledExponent boundarySpeciesShift r) = target
        then F (multispeciesUnorderedModeBlock r) else 0 := by
  classical
  simp only [yyDiagonalSubstitution, shiftedMultispeciesParticlePolynomial, map_sum,
    MvPolynomial.coeff_sum, MvPolynomial.rename_monomial, MvPolynomial.coeff_monomial]
  apply Finset.sum_congr (by ext; simp)
  intro r _
  rfl

/-- Specializing the preceding formula to an explicit diagonal exponent exposes exactly the
active sum and passive-label constraints for `XZ`. -/
theorem coeff_xzDiagonalSubstitution_eq_fiberSum
    {jetOrder a b c d q : ℕ}
    (F : MultispeciesJetParticleSpace K jetOrder
      (boundaryMultiplicity (a + 1) b (c + 1) d))
    (v : SpeciesLabel (boundaryMultiplicity a b c d) →₀ ℕ) :
    MvPolynomial.coeff
        (Finsupp.single (Sum.inl () : BoundaryDiagonalLabel a b c d) q +
          Finsupp.mapDomain Sum.inr v)
        (xzDiagonalSubstitution (K := K) a b c d
          (shiftedMultispeciesParticlePolynomial boundarySpeciesShift F)) =
      ∑ r : MultispeciesModeTuple jetOrder
          (boundaryMultiplicity (a + 1) b (c + 1) d),
        if
          (shiftedMultispeciesLabelledExponent boundarySpeciesShift r)
              (newXZLabelX a b c d) +
                (shiftedMultispeciesLabelledExponent boundarySpeciesShift r)
                  (newXZLabelZ a b c d) = q ∧
            ∀ j,
              (shiftedMultispeciesLabelledExponent boundarySpeciesShift r)
                  (liftXZPassiveLabel a b c d j) = v j
        then F (multispeciesUnorderedModeBlock r) else 0 := by
  rw [coeff_xzDiagonalSubstitution_shiftedMultispeciesParticlePolynomial]
  apply Finset.sum_congr rfl
  intro r _
  simp only [mapDomain_xzToDiagonalLabel_eq_iff]

/-- The analogous exact active/passive fiber sum for `YY`. -/
theorem coeff_yyDiagonalSubstitution_eq_fiberSum
    {jetOrder a b c d q : ℕ}
    (F : MultispeciesJetParticleSpace K jetOrder
      (boundaryMultiplicity a (b + 2) c d))
    (v : SpeciesLabel (boundaryMultiplicity a b c d) →₀ ℕ) :
    MvPolynomial.coeff
        (Finsupp.single (Sum.inl () : BoundaryDiagonalLabel a b c d) q +
          Finsupp.mapDomain Sum.inr v)
        (yyDiagonalSubstitution (K := K) a b c d
          (shiftedMultispeciesParticlePolynomial boundarySpeciesShift F)) =
      ∑ r : MultispeciesModeTuple jetOrder
          (boundaryMultiplicity a (b + 2) c d),
        if
          (shiftedMultispeciesLabelledExponent boundarySpeciesShift r)
              (newYYLabelZero a b c d) +
                (shiftedMultispeciesLabelledExponent boundarySpeciesShift r)
                  (newYYLabelOne a b c d) = q ∧
            ∀ j,
              (shiftedMultispeciesLabelledExponent boundarySpeciesShift r)
                  (liftYYPassiveLabel a b c d j) = v j
        then F (multispeciesUnorderedModeBlock r) else 0 := by
  rw [coeff_yyDiagonalSubstitution_shiftedMultispeciesParticlePolynomial]
  apply Finset.sum_congr rfl
  intro r _
  simp only [mapDomain_yyToDiagonalLabel_eq_iff]

end PolynomialCoefficients

section TupleDecomposition

/-- A labelled tuple in the `XZ` source is one active `X` mode, one active `Z` mode, and a
labelled tuple on all passive particles. -/
def xzModeTupleEquiv (jetOrder a b c d : ℕ) :
    MultispeciesModeTuple jetOrder (boundaryMultiplicity (a + 1) b (c + 1) d) ≃
      (Fin (jetOrder + 1) × Fin (jetOrder + 1)) ×
        MultispeciesModeTuple jetOrder (boundaryMultiplicity a b c d) where
  toFun r :=
    ((r .X (0 : Fin (a + 1)), r .Z (0 : Fin (c + 1))), fun A ↦
      match A with
      | .X => fun i ↦ r .X i.succ
      | .Y => fun i ↦ r .Y i
      | .Z => fun i ↦ r .Z i.succ
      | .S => fun i ↦ r .S i)
  invFun z := fun A ↦
    match A with
    | .X => Fin.cons z.1.1 (z.2 .X)
    | .Y => z.2 .Y
    | .Z => Fin.cons z.1.2 (z.2 .Z)
    | .S => z.2 .S
  left_inv r := by
    funext A i
    cases A
    · refine Fin.cases ?_ (fun j ↦ ?_) i <;> rfl
    · rfl
    · refine Fin.cases ?_ (fun j ↦ ?_) i <;> rfl
    · rfl
  right_inv z := by
    rcases z with ⟨⟨rx, rz⟩, t⟩
    apply Prod.ext
    · rfl
    · funext A i
      cases A <;> rfl

/-- A labelled tuple in the `YY` source is the ordered pair of active `Y` modes and a labelled
tuple on all passive particles. -/
def yyModeTupleEquiv (jetOrder a b c d : ℕ) :
    MultispeciesModeTuple jetOrder (boundaryMultiplicity a (b + 2) c d) ≃
      (Fin (jetOrder + 1) × Fin (jetOrder + 1)) ×
        MultispeciesModeTuple jetOrder (boundaryMultiplicity a b c d) where
  toFun r :=
    ((r .Y (0 : Fin (b + 2)), r .Y (1 : Fin (b + 2))), fun A ↦
      match A with
      | .X => fun i ↦ r .X i
      | .Y => fun i ↦ r .Y i.succ.succ
      | .Z => fun i ↦ r .Z i
      | .S => fun i ↦ r .S i)
  invFun z := fun A ↦
    match A with
    | .X => z.2 .X
    | .Y => Fin.cons z.1.1 (Fin.cons z.1.2 (z.2 .Y))
    | .Z => z.2 .Z
    | .S => z.2 .S
  left_inv r := by
    funext A i
    cases A
    · rfl
    · refine Fin.cases ?_ (fun j ↦ ?_) i
      · rfl
      · refine Fin.cases ?_ (fun k ↦ ?_) j <;> rfl
    · rfl
    · rfl
  right_inv z := by
    rcases z with ⟨⟨ry₀, ry₁⟩, t⟩
    apply Prod.ext
    · rfl
    · funext A i
      cases A <;> rfl

/-- Adding a fixed species shift preserves the injectivity of labelled mode exponents. -/
theorem shiftedMultispeciesLabelledExponent_injective
    {Species : Type*} [Fintype Species]
    {jetOrder : ℕ} {multiplicity : Species → ℕ} (shift : Species → ℕ) :
    Function.Injective
      (shiftedMultispeciesLabelledExponent shift :
        MultispeciesModeTuple jetOrder multiplicity → SpeciesLabel multiplicity →₀ ℕ) := by
  intro r s h
  apply multispeciesLabelledExponent_injective
  exact add_left_cancel h

/-- Package four same-species mode configurations as one boundary multispecies
configuration. -/
def boundaryModeConfiguration {jetOrder a b c d : ℕ}
    (bx : ModeConfiguration jetOrder a)
    (byy : ModeConfiguration jetOrder b)
    (bz : ModeConfiguration jetOrder c)
    (s : ModeConfiguration jetOrder d) :
    MultispeciesModeConfiguration jetOrder (boundaryMultiplicity a b c d)
  | .X => bx
  | .Y => byy
  | .Z => bz
  | .S => s

/-- The target exponent selecting collision degree `q` and a fixed passive mode
configuration. -/
def boundaryDiagonalModeExponent {jetOrder a b c d : ℕ} (q : ℕ)
    (bmode : MultispeciesModeConfiguration jetOrder (boundaryMultiplicity a b c d)) :
    BoundaryDiagonalLabel a b c d →₀ ℕ :=
  Finsupp.single (Sum.inl ()) q +
    Finsupp.mapDomain Sum.inr
      (shiftedMultispeciesLabelledExponent boundarySpeciesShift
        (multispeciesOrderedRepresentative bmode))

/-- A diagonal target exponent retaining an arbitrary labelled passive tuple.  Unlike
`boundaryDiagonalModeExponent`, this does not choose an ordered representative. -/
def boundaryDiagonalTupleExponent {jetOrder a b c d : ℕ} (q : ℕ)
    (t : MultispeciesModeTuple jetOrder (boundaryMultiplicity a b c d)) :
    BoundaryDiagonalLabel a b c d →₀ ℕ :=
  Finsupp.single (Sum.inl ()) q +
    Finsupp.mapDomain Sum.inr
      (shiftedMultispeciesLabelledExponent boundarySpeciesShift t)

/-- Forgetting the order of a tuple with a distinguished head gives symmetric-power
cons. -/
theorem unorderedModeBlock_fin_cons {jetOrder n : ℕ}
    (r : Fin (jetOrder + 1)) (t : Fin n → Fin (jetOrder + 1)) :
    unorderedModeBlock (Fin.cons r t) = r ::ₛ unorderedModeBlock t := by
  change (↑(List.Vector.ofFn (Fin.cons r t)) : Sym (Fin (jetOrder + 1)) (n + 1)) =
    r ::ₛ unorderedModeBlock t
  rw [show List.Vector.ofFn (Fin.cons r t) =
      List.Vector.cons r (List.Vector.ofFn t) by
    apply List.Vector.ext
    intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp]
  simp [unorderedModeBlock]

@[simp]
theorem shiftedExponent_xzModeTupleEquiv_symm_activeX
    {jetOrder a b c d : ℕ} (rs : Fin (jetOrder + 1) × Fin (jetOrder + 1))
    (t : MultispeciesModeTuple jetOrder (boundaryMultiplicity a b c d)) :
    shiftedMultispeciesLabelledExponent boundarySpeciesShift
        ((xzModeTupleEquiv jetOrder a b c d).symm (rs, t))
        (newXZLabelX a b c d) = rs.1 := by
  simp [shiftedMultispeciesLabelledExponent, speciesShiftExponent,
    multispeciesLabelledExponent, xzModeTupleEquiv, newXZLabelX, boundarySpeciesShift]

@[simp]
theorem shiftedExponent_xzModeTupleEquiv_symm_activeZ
    {jetOrder a b c d : ℕ} (rs : Fin (jetOrder + 1) × Fin (jetOrder + 1))
    (t : MultispeciesModeTuple jetOrder (boundaryMultiplicity a b c d)) :
    shiftedMultispeciesLabelledExponent boundarySpeciesShift
        ((xzModeTupleEquiv jetOrder a b c d).symm (rs, t))
        (newXZLabelZ a b c d) = rs.2 := by
  simp [shiftedMultispeciesLabelledExponent, speciesShiftExponent,
    multispeciesLabelledExponent, xzModeTupleEquiv, newXZLabelZ, boundarySpeciesShift]

@[simp]
theorem shiftedExponent_xzModeTupleEquiv_symm_passive
    {jetOrder a b c d : ℕ} (rs : Fin (jetOrder + 1) × Fin (jetOrder + 1))
    (t : MultispeciesModeTuple jetOrder (boundaryMultiplicity a b c d))
    (j : SpeciesLabel (boundaryMultiplicity a b c d)) :
    shiftedMultispeciesLabelledExponent boundarySpeciesShift
        ((xzModeTupleEquiv jetOrder a b c d).symm (rs, t))
        (liftXZPassiveLabel a b c d j) =
      shiftedMultispeciesLabelledExponent boundarySpeciesShift t j := by
  rcases j with ⟨A, j⟩
  have htuple := (xzModeTupleEquiv jetOrder a b c d).apply_symm_apply (rs, t)
  have hmode := congrArg
    (fun z : (Fin (jetOrder + 1) × Fin (jetOrder + 1)) ×
        MultispeciesModeTuple jetOrder (boundaryMultiplicity a b c d) ↦ z.2 A j) htuple
  cases A <;>
    simpa [shiftedMultispeciesLabelledExponent, speciesShiftExponent,
      multispeciesLabelledExponent, xzModeTupleEquiv, liftXZPassiveLabel,
      boundarySpeciesShift] using congrArg Fin.val hmode

@[simp]
theorem shiftedExponent_yyModeTupleEquiv_symm_activeZero
    {jetOrder a b c d : ℕ} (rs : Fin (jetOrder + 1) × Fin (jetOrder + 1))
    (t : MultispeciesModeTuple jetOrder (boundaryMultiplicity a b c d)) :
    shiftedMultispeciesLabelledExponent boundarySpeciesShift
        ((yyModeTupleEquiv jetOrder a b c d).symm (rs, t))
        (newYYLabelZero a b c d) = rs.1 := by
  simp [shiftedMultispeciesLabelledExponent, speciesShiftExponent,
    multispeciesLabelledExponent, yyModeTupleEquiv, newYYLabelZero, boundarySpeciesShift]

@[simp]
theorem shiftedExponent_yyModeTupleEquiv_symm_activeOne
    {jetOrder a b c d : ℕ} (rs : Fin (jetOrder + 1) × Fin (jetOrder + 1))
    (t : MultispeciesModeTuple jetOrder (boundaryMultiplicity a b c d)) :
    shiftedMultispeciesLabelledExponent boundarySpeciesShift
        ((yyModeTupleEquiv jetOrder a b c d).symm (rs, t))
        (newYYLabelOne a b c d) = rs.2 := by
  simp [shiftedMultispeciesLabelledExponent, speciesShiftExponent,
    multispeciesLabelledExponent, yyModeTupleEquiv, newYYLabelOne, boundarySpeciesShift]

@[simp]
theorem shiftedExponent_yyModeTupleEquiv_symm_passive
    {jetOrder a b c d : ℕ} (rs : Fin (jetOrder + 1) × Fin (jetOrder + 1))
    (t : MultispeciesModeTuple jetOrder (boundaryMultiplicity a b c d))
    (j : SpeciesLabel (boundaryMultiplicity a b c d)) :
    shiftedMultispeciesLabelledExponent boundarySpeciesShift
        ((yyModeTupleEquiv jetOrder a b c d).symm (rs, t))
        (liftYYPassiveLabel a b c d j) =
      shiftedMultispeciesLabelledExponent boundarySpeciesShift t j := by
  rcases j with ⟨A, j⟩
  have htuple := (yyModeTupleEquiv jetOrder a b c d).apply_symm_apply (rs, t)
  have hmode := congrArg
    (fun z : (Fin (jetOrder + 1) × Fin (jetOrder + 1)) ×
        MultispeciesModeTuple jetOrder (boundaryMultiplicity a b c d) ↦ z.2 A j) htuple
  cases A <;>
    simpa [shiftedMultispeciesLabelledExponent, speciesShiftExponent,
      multispeciesLabelledExponent, yyModeTupleEquiv, liftYYPassiveLabel,
      boundarySpeciesShift] using congrArg Fin.val hmode

@[simp]
theorem multispeciesUnordered_xzModeTupleEquiv_symm
    {jetOrder a b c d : ℕ} (rs : Fin (jetOrder + 1) × Fin (jetOrder + 1))
    (t : MultispeciesModeTuple jetOrder (boundaryMultiplicity a b c d)) :
    multispeciesUnorderedModeBlock
        ((xzModeTupleEquiv jetOrder a b c d).symm (rs, t)) =
      boundaryModeConfiguration
        (rs.1 ::ₛ unorderedModeBlock (t .X))
        (unorderedModeBlock (t .Y))
        (rs.2 ::ₛ unorderedModeBlock (t .Z))
        (unorderedModeBlock (t .S)) := by
  funext A
  cases A
  · exact unorderedModeBlock_fin_cons rs.1 (t .X)
  · rfl
  · exact unorderedModeBlock_fin_cons rs.2 (t .Z)
  · rfl

@[simp]
theorem multispeciesUnordered_yyModeTupleEquiv_symm
    {jetOrder a b c d : ℕ} (rs : Fin (jetOrder + 1) × Fin (jetOrder + 1))
    (t : MultispeciesModeTuple jetOrder (boundaryMultiplicity a b c d)) :
    multispeciesUnorderedModeBlock
        ((yyModeTupleEquiv jetOrder a b c d).symm (rs, t)) =
      boundaryModeConfiguration
        (unorderedModeBlock (t .X))
        (rs.1 ::ₛ rs.2 ::ₛ unorderedModeBlock (t .Y))
        (unorderedModeBlock (t .Z))
        (unorderedModeBlock (t .S)) := by
  funext A
  cases A
  · rfl
  · change unorderedModeBlock
        (Fin.cons rs.1 (Fin.cons rs.2 (t .Y))) =
      rs.1 ::ₛ rs.2 ::ₛ unorderedModeBlock (t .Y)
    rw [unorderedModeBlock_fin_cons, unorderedModeBlock_fin_cons]
  · rfl
  · rfl

/-- After decomposing an `XZ` tuple, the passive exponent equations select exactly one labelled
passive tuple. -/
theorem xzModeTuple_passiveExponent_eq_iff
    {jetOrder a b c d : ℕ} (rs : Fin (jetOrder + 1) × Fin (jetOrder + 1))
    (t t₀ : MultispeciesModeTuple jetOrder (boundaryMultiplicity a b c d)) :
    (∀ j,
        shiftedMultispeciesLabelledExponent boundarySpeciesShift
            ((xzModeTupleEquiv jetOrder a b c d).symm (rs, t))
            (liftXZPassiveLabel a b c d j) =
          shiftedMultispeciesLabelledExponent boundarySpeciesShift t₀ j) ↔
      t = t₀ := by
  simp only [shiftedExponent_xzModeTupleEquiv_symm_passive]
  constructor
  · intro h
    apply shiftedMultispeciesLabelledExponent_injective boundarySpeciesShift
    ext j
    exact h j
  · rintro rfl
    simp

/-- After decomposing a `YY` tuple, the passive exponent equations likewise select exactly one
labelled passive tuple. -/
theorem yyModeTuple_passiveExponent_eq_iff
    {jetOrder a b c d : ℕ} (rs : Fin (jetOrder + 1) × Fin (jetOrder + 1))
    (t t₀ : MultispeciesModeTuple jetOrder (boundaryMultiplicity a b c d)) :
    (∀ j,
        shiftedMultispeciesLabelledExponent boundarySpeciesShift
            ((yyModeTupleEquiv jetOrder a b c d).symm (rs, t))
            (liftYYPassiveLabel a b c d j) =
          shiftedMultispeciesLabelledExponent boundarySpeciesShift t₀ j) ↔
      t = t₀ := by
  simp only [shiftedExponent_yyModeTupleEquiv_symm_passive]
  constructor
  · intro h
    apply shiftedMultispeciesLabelledExponent_injective boundarySpeciesShift
    ext j
    exact h j
  · rintro rfl
    simp

end TupleDecomposition

section PolarizedCoefficientBridge

universe u

variable {K : Type u} [Field K]

/-- The coefficient selected by a typed `XZ` collision is exactly the ordered convolution sum
from the mode--particle pairing, with every passive species fixed. -/
theorem coeff_xzDiagonalSubstitution_eq_orderedConvolution
    {jetOrder a b c d : ℕ} (q : ℕ)
    (bx : ModeConfiguration jetOrder a)
    (byy : ModeConfiguration jetOrder b)
    (bz : ModeConfiguration jetOrder c)
    (s : ModeConfiguration jetOrder d)
    (F : MultispeciesJetParticleSpace K jetOrder
      (boundaryMultiplicity (a + 1) b (c + 1) d)) :
    MvPolynomial.coeff
        (boundaryDiagonalModeExponent q (boundaryModeConfiguration bx byy bz s))
        (xzDiagonalSubstitution (K := K) a b c d
          (shiftedMultispeciesParticlePolynomial boundarySpeciesShift F)) =
      ∑ rs ∈ coefficientPairs jetOrder q,
        F (boundaryModeConfiguration
          (rs.1 ::ₛ bx) byy (rs.2 ::ₛ bz) s) := by
  classical
  let bmode := boundaryModeConfiguration bx byy bz s
  let t₀ := multispeciesOrderedRepresentative bmode
  rw [show boundaryDiagonalModeExponent q bmode =
      Finsupp.single (Sum.inl () : BoundaryDiagonalLabel a b c d) q +
        Finsupp.mapDomain Sum.inr
          (shiftedMultispeciesLabelledExponent boundarySpeciesShift t₀) from rfl]
  rw [coeff_xzDiagonalSubstitution_eq_fiberSum]
  let H := fun r : MultispeciesModeTuple jetOrder
      (boundaryMultiplicity (a + 1) b (c + 1) d) ↦
    if
      (shiftedMultispeciesLabelledExponent boundarySpeciesShift r)
          (newXZLabelX a b c d) +
            (shiftedMultispeciesLabelledExponent boundarySpeciesShift r)
              (newXZLabelZ a b c d) = q ∧
        ∀ j,
          (shiftedMultispeciesLabelledExponent boundarySpeciesShift r)
              (liftXZPassiveLabel a b c d j) =
            shiftedMultispeciesLabelledExponent boundarySpeciesShift t₀ j
    then F (multispeciesUnorderedModeBlock r) else 0
  change (∑ r, H r) = _
  calc
    (∑ r, H r) =
        ∑ z : (Fin (jetOrder + 1) × Fin (jetOrder + 1)) ×
            MultispeciesModeTuple jetOrder (boundaryMultiplicity a b c d),
          H ((xzModeTupleEquiv jetOrder a b c d).symm z) := by
      exact (Equiv.sum_comp (xzModeTupleEquiv jetOrder a b c d).symm H).symm
    _ = ∑ rs : Fin (jetOrder + 1) × Fin (jetOrder + 1),
          ∑ t : MultispeciesModeTuple jetOrder (boundaryMultiplicity a b c d),
            H ((xzModeTupleEquiv jetOrder a b c d).symm (rs, t)) := by
      rw [Fintype.sum_prod_type]
    _ = ∑ rs : Fin (jetOrder + 1) × Fin (jetOrder + 1),
          if (rs.1 : ℕ) + (rs.2 : ℕ) = q then
            F (boundaryModeConfiguration (rs.1 ::ₛ bx) byy (rs.2 ::ₛ bz) s)
          else 0 := by
      apply Fintype.sum_congr
      intro rs
      by_cases hrs : (rs.1 : ℕ) + (rs.2 : ℕ) = q
      · simp only [H, shiftedExponent_xzModeTupleEquiv_symm_activeX,
          shiftedExponent_xzModeTupleEquiv_symm_activeZ, hrs,
          true_and, xzModeTuple_passiveExponent_eq_iff, if_true]
        rw [Fintype.sum_ite_eq' t₀]
        rw [multispeciesUnordered_xzModeTupleEquiv_symm]
        have ht₀ : multispeciesUnorderedModeBlock t₀ = bmode :=
          multispeciesUnordered_orderedRepresentative bmode
        have hx := congrFun ht₀ .X
        have hy := congrFun ht₀ .Y
        have hz := congrFun ht₀ .Z
        have hs := congrFun ht₀ .S
        have hx' : unorderedModeBlock (t₀ .X) = bx := by
          simpa [multispeciesUnorderedModeBlock, bmode, boundaryModeConfiguration] using hx
        have hy' : unorderedModeBlock (t₀ .Y) = byy := by
          simpa [multispeciesUnorderedModeBlock, bmode, boundaryModeConfiguration] using hy
        have hz' : unorderedModeBlock (t₀ .Z) = bz := by
          simpa [multispeciesUnorderedModeBlock, bmode, boundaryModeConfiguration] using hz
        have hs' : unorderedModeBlock (t₀ .S) = s := by
          simpa [multispeciesUnorderedModeBlock, bmode, boundaryModeConfiguration] using hs
        rw [hx', hy', hz', hs']
        rfl
      · simp only [H, shiftedExponent_xzModeTupleEquiv_symm_activeX,
          shiftedExponent_xzModeTupleEquiv_symm_activeZ, hrs,
          false_and, if_false]
        simp
    _ = ∑ rs ∈ coefficientPairs jetOrder q,
          F (boundaryModeConfiguration (rs.1 ::ₛ bx) byy (rs.2 ::ₛ bz) s) := by
      rw [coefficientPairs, Finset.sum_filter]

/-- The typed `YY` coefficient is the same ordered convolution used by the mode--particle
pairing.  In particular, unequal active modes occur twice, once as `(r,s)` and once as `(s,r)`,
while a diagonal pair occurs once. -/
theorem coeff_yyDiagonalSubstitution_eq_orderedConvolution
    {jetOrder a b c d : ℕ} (q : ℕ)
    (bx : ModeConfiguration jetOrder a)
    (byy : ModeConfiguration jetOrder b)
    (bz : ModeConfiguration jetOrder c)
    (s : ModeConfiguration jetOrder d)
    (F : MultispeciesJetParticleSpace K jetOrder
      (boundaryMultiplicity a (b + 2) c d)) :
    MvPolynomial.coeff
        (boundaryDiagonalModeExponent q (boundaryModeConfiguration bx byy bz s))
        (yyDiagonalSubstitution (K := K) a b c d
          (shiftedMultispeciesParticlePolynomial boundarySpeciesShift F)) =
      ∑ rs ∈ coefficientPairs jetOrder q,
        F (boundaryModeConfiguration
          bx (rs.1 ::ₛ rs.2 ::ₛ byy) bz s) := by
  classical
  let bmode := boundaryModeConfiguration bx byy bz s
  let t₀ := multispeciesOrderedRepresentative bmode
  rw [show boundaryDiagonalModeExponent q bmode =
      Finsupp.single (Sum.inl () : BoundaryDiagonalLabel a b c d) q +
        Finsupp.mapDomain Sum.inr
          (shiftedMultispeciesLabelledExponent boundarySpeciesShift t₀) from rfl]
  rw [coeff_yyDiagonalSubstitution_eq_fiberSum]
  let H := fun r : MultispeciesModeTuple jetOrder
      (boundaryMultiplicity a (b + 2) c d) ↦
    if
      (shiftedMultispeciesLabelledExponent boundarySpeciesShift r)
          (newYYLabelZero a b c d) +
            (shiftedMultispeciesLabelledExponent boundarySpeciesShift r)
              (newYYLabelOne a b c d) = q ∧
        ∀ j,
          (shiftedMultispeciesLabelledExponent boundarySpeciesShift r)
              (liftYYPassiveLabel a b c d j) =
            shiftedMultispeciesLabelledExponent boundarySpeciesShift t₀ j
    then F (multispeciesUnorderedModeBlock r) else 0
  change (∑ r, H r) = _
  calc
    (∑ r, H r) =
        ∑ z : (Fin (jetOrder + 1) × Fin (jetOrder + 1)) ×
            MultispeciesModeTuple jetOrder (boundaryMultiplicity a b c d),
          H ((yyModeTupleEquiv jetOrder a b c d).symm z) := by
      exact (Equiv.sum_comp (yyModeTupleEquiv jetOrder a b c d).symm H).symm
    _ = ∑ rs : Fin (jetOrder + 1) × Fin (jetOrder + 1),
          ∑ t : MultispeciesModeTuple jetOrder (boundaryMultiplicity a b c d),
            H ((yyModeTupleEquiv jetOrder a b c d).symm (rs, t)) := by
      rw [Fintype.sum_prod_type]
    _ = ∑ rs : Fin (jetOrder + 1) × Fin (jetOrder + 1),
          if (rs.1 : ℕ) + (rs.2 : ℕ) = q then
            F (boundaryModeConfiguration bx (rs.1 ::ₛ rs.2 ::ₛ byy) bz s)
          else 0 := by
      apply Fintype.sum_congr
      intro rs
      by_cases hrs : (rs.1 : ℕ) + (rs.2 : ℕ) = q
      · simp only [H, shiftedExponent_yyModeTupleEquiv_symm_activeZero,
          shiftedExponent_yyModeTupleEquiv_symm_activeOne, hrs,
          true_and, yyModeTuple_passiveExponent_eq_iff, if_true]
        rw [Fintype.sum_ite_eq' t₀]
        rw [multispeciesUnordered_yyModeTupleEquiv_symm]
        have ht₀ : multispeciesUnorderedModeBlock t₀ = bmode :=
          multispeciesUnordered_orderedRepresentative bmode
        have hx := congrFun ht₀ .X
        have hy := congrFun ht₀ .Y
        have hz := congrFun ht₀ .Z
        have hs := congrFun ht₀ .S
        have hx' : unorderedModeBlock (t₀ .X) = bx := by
          simpa [multispeciesUnorderedModeBlock, bmode, boundaryModeConfiguration] using hx
        have hy' : unorderedModeBlock (t₀ .Y) = byy := by
          simpa [multispeciesUnorderedModeBlock, bmode, boundaryModeConfiguration] using hy
        have hz' : unorderedModeBlock (t₀ .Z) = bz := by
          simpa [multispeciesUnorderedModeBlock, bmode, boundaryModeConfiguration] using hz
        have hs' : unorderedModeBlock (t₀ .S) = s := by
          simpa [multispeciesUnorderedModeBlock, bmode, boundaryModeConfiguration] using hs
        rw [hx', hy', hz', hs']
        rfl
      · simp only [H, shiftedExponent_yyModeTupleEquiv_symm_activeZero,
          shiftedExponent_yyModeTupleEquiv_symm_activeOne, hrs,
          false_and, if_false]
        simp
    _ = ∑ rs ∈ coefficientPairs jetOrder q,
          F (boundaryModeConfiguration bx (rs.1 ::ₛ rs.2 ::ₛ byy) bz s) := by
      rw [coefficientPairs, Finset.sum_filter]

/-- Arbitrary-labelled version of the `XZ` coefficient bridge.  It is the support-compatible
form needed to upgrade equality on ordered representatives to polynomial equality. -/
theorem coeff_xzDiagonalSubstitution_tupleExponent
    {jetOrder a b c d : ℕ} (q : ℕ)
    (t₀ : MultispeciesModeTuple jetOrder (boundaryMultiplicity a b c d))
    (F : MultispeciesJetParticleSpace K jetOrder
      (boundaryMultiplicity (a + 1) b (c + 1) d)) :
    MvPolynomial.coeff (boundaryDiagonalTupleExponent q t₀)
        (xzDiagonalSubstitution (K := K) a b c d
          (shiftedMultispeciesParticlePolynomial boundarySpeciesShift F)) =
      ∑ rs ∈ coefficientPairs jetOrder q,
        F (boundaryModeConfiguration
          (rs.1 ::ₛ unorderedModeBlock (t₀ .X))
          (unorderedModeBlock (t₀ .Y))
          (rs.2 ::ₛ unorderedModeBlock (t₀ .Z))
          (unorderedModeBlock (t₀ .S))) := by
  classical
  rw [show boundaryDiagonalTupleExponent q t₀ =
      Finsupp.single (Sum.inl () : BoundaryDiagonalLabel a b c d) q +
        Finsupp.mapDomain Sum.inr
          (shiftedMultispeciesLabelledExponent boundarySpeciesShift t₀) from rfl]
  rw [coeff_xzDiagonalSubstitution_eq_fiberSum]
  let H := fun r : MultispeciesModeTuple jetOrder
      (boundaryMultiplicity (a + 1) b (c + 1) d) ↦
    if
      (shiftedMultispeciesLabelledExponent boundarySpeciesShift r)
          (newXZLabelX a b c d) +
            (shiftedMultispeciesLabelledExponent boundarySpeciesShift r)
              (newXZLabelZ a b c d) = q ∧
        ∀ j,
          (shiftedMultispeciesLabelledExponent boundarySpeciesShift r)
              (liftXZPassiveLabel a b c d j) =
            shiftedMultispeciesLabelledExponent boundarySpeciesShift t₀ j
    then F (multispeciesUnorderedModeBlock r) else 0
  change (∑ r, H r) = _
  calc
    (∑ r, H r) =
        ∑ z : (Fin (jetOrder + 1) × Fin (jetOrder + 1)) ×
            MultispeciesModeTuple jetOrder (boundaryMultiplicity a b c d),
          H ((xzModeTupleEquiv jetOrder a b c d).symm z) := by
      exact (Equiv.sum_comp (xzModeTupleEquiv jetOrder a b c d).symm H).symm
    _ = ∑ rs : Fin (jetOrder + 1) × Fin (jetOrder + 1),
          ∑ t : MultispeciesModeTuple jetOrder (boundaryMultiplicity a b c d),
            H ((xzModeTupleEquiv jetOrder a b c d).symm (rs, t)) := by
      rw [Fintype.sum_prod_type]
    _ = ∑ rs : Fin (jetOrder + 1) × Fin (jetOrder + 1),
          if (rs.1 : ℕ) + (rs.2 : ℕ) = q then
            F (boundaryModeConfiguration
              (rs.1 ::ₛ unorderedModeBlock (t₀ .X))
              (unorderedModeBlock (t₀ .Y))
              (rs.2 ::ₛ unorderedModeBlock (t₀ .Z))
              (unorderedModeBlock (t₀ .S)))
          else 0 := by
      apply Fintype.sum_congr
      intro rs
      by_cases hrs : (rs.1 : ℕ) + (rs.2 : ℕ) = q
      · simp only [H, shiftedExponent_xzModeTupleEquiv_symm_activeX,
          shiftedExponent_xzModeTupleEquiv_symm_activeZ, hrs, true_and,
          xzModeTuple_passiveExponent_eq_iff, if_true]
        rw [Fintype.sum_ite_eq' t₀]
        rw [multispeciesUnordered_xzModeTupleEquiv_symm]
        rfl
      · simp only [H, shiftedExponent_xzModeTupleEquiv_symm_activeX,
          shiftedExponent_xzModeTupleEquiv_symm_activeZ, hrs, false_and, if_false]
        simp
    _ = ∑ rs ∈ coefficientPairs jetOrder q,
          F (boundaryModeConfiguration
            (rs.1 ::ₛ unorderedModeBlock (t₀ .X))
            (unorderedModeBlock (t₀ .Y))
            (rs.2 ::ₛ unorderedModeBlock (t₀ .Z))
            (unorderedModeBlock (t₀ .S))) := by
      rw [coefficientPairs, Finset.sum_filter]

/-- Arbitrary-labelled version of the `YY` coefficient bridge. -/
theorem coeff_yyDiagonalSubstitution_tupleExponent
    {jetOrder a b c d : ℕ} (q : ℕ)
    (t₀ : MultispeciesModeTuple jetOrder (boundaryMultiplicity a b c d))
    (F : MultispeciesJetParticleSpace K jetOrder
      (boundaryMultiplicity a (b + 2) c d)) :
    MvPolynomial.coeff (boundaryDiagonalTupleExponent q t₀)
        (yyDiagonalSubstitution (K := K) a b c d
          (shiftedMultispeciesParticlePolynomial boundarySpeciesShift F)) =
      ∑ rs ∈ coefficientPairs jetOrder q,
        F (boundaryModeConfiguration
          (unorderedModeBlock (t₀ .X))
          (rs.1 ::ₛ rs.2 ::ₛ unorderedModeBlock (t₀ .Y))
          (unorderedModeBlock (t₀ .Z))
          (unorderedModeBlock (t₀ .S))) := by
  classical
  rw [show boundaryDiagonalTupleExponent q t₀ =
      Finsupp.single (Sum.inl () : BoundaryDiagonalLabel a b c d) q +
        Finsupp.mapDomain Sum.inr
          (shiftedMultispeciesLabelledExponent boundarySpeciesShift t₀) from rfl]
  rw [coeff_yyDiagonalSubstitution_eq_fiberSum]
  let H := fun r : MultispeciesModeTuple jetOrder
      (boundaryMultiplicity a (b + 2) c d) ↦
    if
      (shiftedMultispeciesLabelledExponent boundarySpeciesShift r)
          (newYYLabelZero a b c d) +
            (shiftedMultispeciesLabelledExponent boundarySpeciesShift r)
              (newYYLabelOne a b c d) = q ∧
        ∀ j,
          (shiftedMultispeciesLabelledExponent boundarySpeciesShift r)
              (liftYYPassiveLabel a b c d j) =
            shiftedMultispeciesLabelledExponent boundarySpeciesShift t₀ j
    then F (multispeciesUnorderedModeBlock r) else 0
  change (∑ r, H r) = _
  calc
    (∑ r, H r) =
        ∑ z : (Fin (jetOrder + 1) × Fin (jetOrder + 1)) ×
            MultispeciesModeTuple jetOrder (boundaryMultiplicity a b c d),
          H ((yyModeTupleEquiv jetOrder a b c d).symm z) := by
      exact (Equiv.sum_comp (yyModeTupleEquiv jetOrder a b c d).symm H).symm
    _ = ∑ rs : Fin (jetOrder + 1) × Fin (jetOrder + 1),
          ∑ t : MultispeciesModeTuple jetOrder (boundaryMultiplicity a b c d),
            H ((yyModeTupleEquiv jetOrder a b c d).symm (rs, t)) := by
      rw [Fintype.sum_prod_type]
    _ = ∑ rs : Fin (jetOrder + 1) × Fin (jetOrder + 1),
          if (rs.1 : ℕ) + (rs.2 : ℕ) = q then
            F (boundaryModeConfiguration
              (unorderedModeBlock (t₀ .X))
              (rs.1 ::ₛ rs.2 ::ₛ unorderedModeBlock (t₀ .Y))
              (unorderedModeBlock (t₀ .Z))
              (unorderedModeBlock (t₀ .S)))
          else 0 := by
      apply Fintype.sum_congr
      intro rs
      by_cases hrs : (rs.1 : ℕ) + (rs.2 : ℕ) = q
      · simp only [H, shiftedExponent_yyModeTupleEquiv_symm_activeZero,
          shiftedExponent_yyModeTupleEquiv_symm_activeOne, hrs, true_and,
          yyModeTuple_passiveExponent_eq_iff, if_true]
        rw [Fintype.sum_ite_eq' t₀]
        rw [multispeciesUnordered_yyModeTupleEquiv_symm]
        rfl
      · simp only [H, shiftedExponent_yyModeTupleEquiv_symm_activeZero,
          shiftedExponent_yyModeTupleEquiv_symm_activeOne, hrs, false_and, if_false]
        simp
    _ = ∑ rs ∈ coefficientPairs jetOrder q,
          F (boundaryModeConfiguration
            (unorderedModeBlock (t₀ .X))
            (rs.1 ::ₛ rs.2 ::ₛ unorderedModeBlock (t₀ .Y))
            (unorderedModeBlock (t₀ .Z))
            (unorderedModeBlock (t₀ .S))) := by
      rw [coefficientPairs, Finset.sum_filter]

/-- On every arbitrary-labelled diagonal exponent, equality of the two substituted polynomial
coefficients is exactly the polarized coefficient identity for the underlying passive symmetric
configurations. -/
theorem typedPolynomial_tupleCoefficient_eq_iff_polarizedDiagonalCoefficient_eq
    {jetOrder a b c d : ℕ} (q : ℕ)
    (t₀ : MultispeciesModeTuple jetOrder (boundaryMultiplicity a b c d))
    (F : BoundaryPolarizedCoefficientSpace (K := K) jetOrder a b c d) :
    MvPolynomial.coeff (boundaryDiagonalTupleExponent q t₀)
          (xzDiagonalSubstitution (K := K) a b c d
            (shiftedMultispeciesParticlePolynomial boundarySpeciesShift F.1)) =
        MvPolynomial.coeff (boundaryDiagonalTupleExponent q t₀)
          (yyDiagonalSubstitution (K := K) a b c d
            (shiftedMultispeciesParticlePolynomial boundarySpeciesShift F.2)) ↔
      polarizedXZDiagonalCoefficient q
          (unorderedModeBlock (t₀ .X)) (unorderedModeBlock (t₀ .Y))
          (unorderedModeBlock (t₀ .Z))
          (slicePolarizedAtS F (unorderedModeBlock (t₀ .S))) =
        polarizedYYDiagonalCoefficient q
          (unorderedModeBlock (t₀ .X)) (unorderedModeBlock (t₀ .Y))
          (unorderedModeBlock (t₀ .Z))
          (slicePolarizedAtS F (unorderedModeBlock (t₀ .S))) := by
  rw [coeff_xzDiagonalSubstitution_tupleExponent,
    coeff_yyDiagonalSubstitution_tupleExponent]
  rfl

/-- Every exponent in the support of a substituted `XZ` particle polynomial is a diagonal tuple
exponent for some collision degree and some arbitrary labelled passive tuple. -/
theorem exists_boundaryDiagonalTupleExponent_of_xz_coeff_ne_zero
    {jetOrder a b c d : ℕ}
    (F : MultispeciesJetParticleSpace K jetOrder
      (boundaryMultiplicity (a + 1) b (c + 1) d))
    (target : BoundaryDiagonalLabel a b c d →₀ ℕ)
    (hcoeff : MvPolynomial.coeff target
      (xzDiagonalSubstitution (K := K) a b c d
        (shiftedMultispeciesParticlePolynomial boundarySpeciesShift F)) ≠ 0) :
    ∃ q, ∃ t : MultispeciesModeTuple jetOrder (boundaryMultiplicity a b c d),
      target = boundaryDiagonalTupleExponent q t := by
  classical
  rw [coeff_xzDiagonalSubstitution_shiftedMultispeciesParticlePolynomial] at hcoeff
  obtain ⟨r, _, hr⟩ := Finset.exists_ne_zero_of_sum_ne_zero hcoeff
  split at hr
  · rename_i hmap
    let z := xzModeTupleEquiv jetOrder a b c d r
    let q : ℕ := (z.1.1 : ℕ) + (z.1.2 : ℕ)
    refine ⟨q, z.2, ?_⟩
    have hrz : r = (xzModeTupleEquiv jetOrder a b c d).symm z :=
      (xzModeTupleEquiv jetOrder a b c d).symm_apply_apply r |>.symm
    have hfiber : Finsupp.mapDomain (xzToDiagonalLabel a b c d)
          (shiftedMultispeciesLabelledExponent boundarySpeciesShift r) =
        boundaryDiagonalTupleExponent q z.2 := by
      change Finsupp.mapDomain (xzToDiagonalLabel a b c d)
          (shiftedMultispeciesLabelledExponent boundarySpeciesShift r) =
        Finsupp.single (Sum.inl ()) q + Finsupp.mapDomain Sum.inr
          (shiftedMultispeciesLabelledExponent boundarySpeciesShift z.2)
      apply (mapDomain_xzToDiagonalLabel_eq_iff a b c d q _ _).2
      constructor
      · simp [shiftedMultispeciesLabelledExponent, speciesShiftExponent,
          multispeciesLabelledExponent, newXZLabelX, newXZLabelZ,
          boundarySpeciesShift, xzModeTupleEquiv, q, z]
      · intro j
        rw [hrz]
        exact shiftedExponent_xzModeTupleEquiv_symm_passive z.1 z.2 j
    exact hmap.symm.trans hfiber
  · simp at hr

/-- Every exponent in the support of a substituted `YY` particle polynomial has the same
diagonal-tuple form. -/
theorem exists_boundaryDiagonalTupleExponent_of_yy_coeff_ne_zero
    {jetOrder a b c d : ℕ}
    (F : MultispeciesJetParticleSpace K jetOrder
      (boundaryMultiplicity a (b + 2) c d))
    (target : BoundaryDiagonalLabel a b c d →₀ ℕ)
    (hcoeff : MvPolynomial.coeff target
      (yyDiagonalSubstitution (K := K) a b c d
        (shiftedMultispeciesParticlePolynomial boundarySpeciesShift F)) ≠ 0) :
    ∃ q, ∃ t : MultispeciesModeTuple jetOrder (boundaryMultiplicity a b c d),
      target = boundaryDiagonalTupleExponent q t := by
  classical
  rw [coeff_yyDiagonalSubstitution_shiftedMultispeciesParticlePolynomial] at hcoeff
  obtain ⟨r, _, hr⟩ := Finset.exists_ne_zero_of_sum_ne_zero hcoeff
  split at hr
  · rename_i hmap
    let z := yyModeTupleEquiv jetOrder a b c d r
    let q : ℕ := (z.1.1 : ℕ) + (z.1.2 : ℕ)
    refine ⟨q, z.2, ?_⟩
    have hrz : r = (yyModeTupleEquiv jetOrder a b c d).symm z :=
      (yyModeTupleEquiv jetOrder a b c d).symm_apply_apply r |>.symm
    have hfiber : Finsupp.mapDomain (yyToDiagonalLabel a b c d)
          (shiftedMultispeciesLabelledExponent boundarySpeciesShift r) =
        boundaryDiagonalTupleExponent q z.2 := by
      change Finsupp.mapDomain (yyToDiagonalLabel a b c d)
          (shiftedMultispeciesLabelledExponent boundarySpeciesShift r) =
        Finsupp.single (Sum.inl ()) q + Finsupp.mapDomain Sum.inr
          (shiftedMultispeciesLabelledExponent boundarySpeciesShift z.2)
      apply (mapDomain_yyToDiagonalLabel_eq_iff a b c d q _ _).2
      constructor
      · simp [shiftedMultispeciesLabelledExponent, speciesShiftExponent,
          multispeciesLabelledExponent, newYYLabelZero, newYYLabelOne,
          boundarySpeciesShift, yyModeTupleEquiv, q, z]
      · intro j
        rw [hrz]
        exact shiftedExponent_yyModeTupleEquiv_symm_passive z.1 z.2 j
    exact hmap.symm.trans hfiber
  · simp at hr

/-- Boundary polarized orthogonality upgrades from coefficientwise diagonal equations to equality
of the complete typed substituted particle polynomials. -/
theorem boundaryPolarizedOrthogonal_typedPolynomial_eq
    {jetOrder a b c d : ℕ}
    (F : BoundaryPolarizedCoefficientSpace (K := K) jetOrder a b c d)
    (hF : IsBoundaryPolarizedOrthogonal F) :
    xzDiagonalSubstitution (K := K) a b c d
        (shiftedMultispeciesParticlePolynomial boundarySpeciesShift F.1) =
      yyDiagonalSubstitution (K := K) a b c d
        (shiftedMultispeciesParticlePolynomial boundarySpeciesShift F.2) := by
  apply MvPolynomial.ext
  intro target
  by_cases hx : MvPolynomial.coeff target
      (xzDiagonalSubstitution (K := K) a b c d
        (shiftedMultispeciesParticlePolynomial boundarySpeciesShift F.1)) ≠ 0
  · obtain ⟨q, t, rfl⟩ :=
      exists_boundaryDiagonalTupleExponent_of_xz_coeff_ne_zero F.1 target hx
    apply (typedPolynomial_tupleCoefficient_eq_iff_polarizedDiagonalCoefficient_eq q t F).2
    exact (boundaryPolarized_orthogonal_iff_diagonal F).1 hF
      (unorderedModeBlock (t .S)) q
      (unorderedModeBlock (t .X)) (unorderedModeBlock (t .Y))
      (unorderedModeBlock (t .Z))
  · by_cases hy : MvPolynomial.coeff target
        (yyDiagonalSubstitution (K := K) a b c d
          (shiftedMultispeciesParticlePolynomial boundarySpeciesShift F.2)) ≠ 0
    · obtain ⟨q, t, rfl⟩ :=
        exists_boundaryDiagonalTupleExponent_of_yy_coeff_ne_zero F.2 target hy
      apply (typedPolynomial_tupleCoefficient_eq_iff_polarizedDiagonalCoefficient_eq q t F).2
      exact (boundaryPolarized_orthogonal_iff_diagonal F).1 hF
        (unorderedModeBlock (t .S)) q
        (unorderedModeBlock (t .X)) (unorderedModeBlock (t .Y))
        (unorderedModeBlock (t .Z))
    · rw [not_ne_iff.mp hx, not_ne_iff.mp hy]

/-- The polynomial `XZ` coefficient is literally the coefficient-space diagonal functional. -/
theorem coeff_xzDiagonalSubstitution_eq_polarizedXZDiagonalCoefficient
    {jetOrder a b c d : ℕ} (q : ℕ)
    (bx : ModeConfiguration jetOrder a)
    (byy : ModeConfiguration jetOrder b)
    (bz : ModeConfiguration jetOrder c)
    (s : ModeConfiguration jetOrder d)
    (F : BoundaryPolarizedCoefficientSpace (K := K) jetOrder a b c d) :
    MvPolynomial.coeff
        (boundaryDiagonalModeExponent q (boundaryModeConfiguration bx byy bz s))
        (xzDiagonalSubstitution (K := K) a b c d
          (shiftedMultispeciesParticlePolynomial boundarySpeciesShift F.1)) =
      polarizedXZDiagonalCoefficient q bx byy bz (slicePolarizedAtS F s) := by
  rw [coeff_xzDiagonalSubstitution_eq_orderedConvolution]
  rfl

/-- The polynomial `YY` coefficient is literally the coefficient-space diagonal functional,
including its ordered multiplicities. -/
theorem coeff_yyDiagonalSubstitution_eq_polarizedYYDiagonalCoefficient
    {jetOrder a b c d : ℕ} (q : ℕ)
    (bx : ModeConfiguration jetOrder a)
    (byy : ModeConfiguration jetOrder b)
    (bz : ModeConfiguration jetOrder c)
    (s : ModeConfiguration jetOrder d)
    (F : BoundaryPolarizedCoefficientSpace (K := K) jetOrder a b c d) :
    MvPolynomial.coeff
        (boundaryDiagonalModeExponent q (boundaryModeConfiguration bx byy bz s))
        (yyDiagonalSubstitution (K := K) a b c d
          (shiftedMultispeciesParticlePolynomial boundarySpeciesShift F.2)) =
      polarizedYYDiagonalCoefficient q bx byy bz (slicePolarizedAtS F s) := by
  rw [coeff_yyDiagonalSubstitution_eq_orderedConvolution]
  rfl

/-- At every collision degree and passive configuration, equality of the two literal polynomial
coefficients is exactly the polarized diagonal equation from the mode--particle pairing. -/
theorem typedPolynomialCoefficient_eq_iff_polarizedDiagonalCoefficient_eq
    {jetOrder a b c d : ℕ} (q : ℕ)
    (bx : ModeConfiguration jetOrder a)
    (byy : ModeConfiguration jetOrder b)
    (bz : ModeConfiguration jetOrder c)
    (s : ModeConfiguration jetOrder d)
    (F : BoundaryPolarizedCoefficientSpace (K := K) jetOrder a b c d) :
    MvPolynomial.coeff
          (boundaryDiagonalModeExponent q (boundaryModeConfiguration bx byy bz s))
          (xzDiagonalSubstitution (K := K) a b c d
            (shiftedMultispeciesParticlePolynomial boundarySpeciesShift F.1)) =
        MvPolynomial.coeff
          (boundaryDiagonalModeExponent q (boundaryModeConfiguration bx byy bz s))
          (yyDiagonalSubstitution (K := K) a b c d
            (shiftedMultispeciesParticlePolynomial boundarySpeciesShift F.2)) ↔
      polarizedXZDiagonalCoefficient q bx byy bz (slicePolarizedAtS F s) =
        polarizedYYDiagonalCoefficient q bx byy bz (slicePolarizedAtS F s) := by
  rw [coeff_xzDiagonalSubstitution_eq_polarizedXZDiagonalCoefficient,
    coeff_yyDiagonalSubstitution_eq_polarizedYYDiagonalCoefficient]

/-- Boundary polarized orthogonality therefore gives equality of the two substituted polynomial
coefficients on every canonical finite-jet diagonal exponent. -/
theorem boundaryPolarizedOrthogonal_typedPolynomialCoefficient_eq
    {jetOrder a b c d : ℕ}
    (F : BoundaryPolarizedCoefficientSpace (K := K) jetOrder a b c d)
    (hF : IsBoundaryPolarizedOrthogonal F)
    (q : ℕ)
    (bx : ModeConfiguration jetOrder a)
    (byy : ModeConfiguration jetOrder b)
    (bz : ModeConfiguration jetOrder c)
    (s : ModeConfiguration jetOrder d) :
    MvPolynomial.coeff
        (boundaryDiagonalModeExponent q (boundaryModeConfiguration bx byy bz s))
        (xzDiagonalSubstitution (K := K) a b c d
          (shiftedMultispeciesParticlePolynomial boundarySpeciesShift F.1)) =
      MvPolynomial.coeff
        (boundaryDiagonalModeExponent q (boundaryModeConfiguration bx byy bz s))
        (yyDiagonalSubstitution (K := K) a b c d
          (shiftedMultispeciesParticlePolynomial boundarySpeciesShift F.2)) := by
  rw [typedPolynomialCoefficient_eq_iff_polarizedDiagonalCoefficient_eq]
  exact (boundaryPolarized_orthogonal_iff_diagonal F).1 hF s q bx byy bz

end PolarizedCoefficientBridge

end

end VOA.BoundaryCoefficientFiber
