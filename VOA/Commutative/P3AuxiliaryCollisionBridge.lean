/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Commutative.AuxiliaryIdealOrthogonal
import VOA.Commutative.BoundaryCoefficientFiber
import VOA.Commutative.P3RestrictedDualCommonFactor

/-!
# From auxiliary orthogonality to the labelled p=3 collisions

This file supplies the coefficient bridge deliberately left open in
`P3RestrictedDualCommonFactor.lean`.  It first treats the shifted `S^2` relation in a fixed
four-species sector.  The two active `S` labels have exponent `r+1`, so their common diagonal
degree is `2+r+s`.  All other labels are retained literally.

The proofs use arbitrary labelled passive tuples and support extraction.  They do not assume
that an arbitrary labelled exponent is the exponent of the chosen ordered representative of a
symmetric-power configuration.
-/

namespace VOA.P3AuxiliaryCollisionBridge

open MvPolynomial
open VOA.AuxiliaryIdealOrthogonal
open VOA.BoundaryCoefficientFiber
open VOA.BoundaryCollisionDivisibility
open VOA.BoundaryTypedSubstitution
open VOA.CollisionCommonFactors
open VOA.ModeParticlePairing
open VOA.MultispeciesParticlePolynomial
open VOA.P3RestrictedDualCommonFactor

noncomputable section

universe u

variable {K : Type u} [Field K]

section ShiftedSS

/-- The source label type with two distinguished `S` particles. -/
abbrev SSLabel (a b c d : ℕ) :=
  SpeciesLabel (boundaryMultiplicity a b c (d + 2))

/-- Include a passive label after reserving the first two `S` slots. -/
def liftSSPassiveLabel (a b c d : ℕ) :
    SpeciesLabel (boundaryMultiplicity a b c d) → SSLabel a b c d
  | ⟨.X, i⟩ => ⟨.X, i⟩
  | ⟨.Y, i⟩ => ⟨.Y, i⟩
  | ⟨.Z, i⟩ => ⟨.Z, i⟩
  | ⟨.S, i⟩ => ⟨.S, i.succ.succ⟩

/-- The first active `S` label. -/
def newSSLabelZero (a b c d : ℕ) : SSLabel a b c d :=
  ⟨.S, (0 : Fin (d + 2))⟩

/-- The second active `S` label. -/
def newSSLabelOne (a b c d : ℕ) : SSLabel a b c d :=
  ⟨.S, (1 : Fin (d + 2))⟩

theorem newSSLabelOne_ne_newSSLabelZero (a b c d : ℕ) :
    newSSLabelOne a b c d ≠ newSSLabelZero a b c d := by
  intro h
  have hv := congrArg (fun q : SSLabel a b c d => (q.2 : ℕ)) h
  change ((1 : Fin (d + 2)) : ℕ) = ((0 : Fin (d + 2)) : ℕ) at hv
  norm_num at hv

theorem liftSSPassiveLabel_ne_newSSLabelZero (a b c d : ℕ)
    (i : SpeciesLabel (boundaryMultiplicity a b c d)) :
    liftSSPassiveLabel a b c d i ≠ newSSLabelZero a b c d := by
  intro h
  rcases i with ⟨A, i⟩
  cases A
  · simp [liftSSPassiveLabel, newSSLabelZero] at h
  · simp [liftSSPassiveLabel, newSSLabelZero] at h
  · simp [liftSSPassiveLabel, newSSLabelZero] at h
  · have hv := congrArg (fun q : SSLabel a b c d => (q.2 : ℕ)) h
    change ((i.succ.succ : Fin (d + 2)) : ℕ) = ((0 : Fin (d + 2)) : ℕ) at hv
    simp at hv

/-- Identify the two active `S` labels and retain every passive label. -/
def ssToDiagonalLabel (a b c d : ℕ) :
    SSLabel a b c d → BoundaryDiagonalLabel a b c d
  | ⟨.X, i⟩ => Sum.inr ⟨.X, i⟩
  | ⟨.Y, i⟩ => Sum.inr ⟨.Y, i⟩
  | ⟨.Z, i⟩ => Sum.inr ⟨.Z, i⟩
  | ⟨.S, i⟩ =>
      Fin.cases (Sum.inl ())
        (fun j => Fin.cases (Sum.inl ()) (fun k => Sum.inr ⟨.S, k⟩) j) i

/-- The typed shifted `S`--`S` diagonal substitution. -/
def ssDiagonalSubstitution (a b c d : ℕ) :
    MvPolynomial (SSLabel a b c d) K →ₐ[K]
      MvPolynomial (BoundaryDiagonalLabel a b c d) K :=
  MvPolynomial.rename (ssToDiagonalLabel a b c d)

@[simp]
theorem ssToDiagonalLabel_new_zero (a b c d : ℕ) :
    ssToDiagonalLabel a b c d (newSSLabelZero a b c d) = Sum.inl () := by
  rfl

@[simp]
theorem ssToDiagonalLabel_new_one (a b c d : ℕ) :
    ssToDiagonalLabel a b c d (newSSLabelOne a b c d) = Sum.inl () := by
  rfl

@[simp]
theorem ssToDiagonalLabel_passive (a b c d : ℕ)
    (i : SpeciesLabel (boundaryMultiplicity a b c d)) :
    ssToDiagonalLabel a b c d (liftSSPassiveLabel a b c d i) = Sum.inr i := by
  rcases i with ⟨A, i⟩
  cases A <;> rfl

/-- The collision coordinate has precisely the two active `S` preimages. -/
theorem ssToDiagonalLabel_eq_collision_iff (a b c d : ℕ)
    (i : SSLabel a b c d) :
    ssToDiagonalLabel a b c d i = Sum.inl () ↔
      i = newSSLabelZero a b c d ∨ i = newSSLabelOne a b c d := by
  rcases i with ⟨A, i⟩
  cases A
  · simp [ssToDiagonalLabel, newSSLabelZero, newSSLabelOne]
  · simp [ssToDiagonalLabel, newSSLabelZero, newSSLabelOne]
  · simp [ssToDiagonalLabel, newSSLabelZero, newSSLabelOne]
  · refine Fin.cases ?_ (fun j => ?_) i
    · simp [ssToDiagonalLabel, newSSLabelZero, newSSLabelOne]
    · refine Fin.cases ?_ (fun k => ?_) j
      · constructor
        · intro _
          exact Or.inr rfl
        · intro _
          rfl
      · constructor
        · intro h
          simp only [ssToDiagonalLabel] at h
          contradiction
        · rintro (h | h)
          · have hv := congrArg (fun q : SSLabel a b c d => (q.2 : ℕ)) h
            simp [newSSLabelZero] at hv
          · have hv := congrArg (fun q : SSLabel a b c d => (q.2 : ℕ)) h
            simp [newSSLabelOne] at hv

/-- The diagonal target is the residual label type obtained after deleting the first active
`S` label. -/
def ssResidualEquiv (a b c d : ℕ) :
    {i : SSLabel a b c d // i ≠ newSSLabelZero a b c d} ≃
      BoundaryDiagonalLabel a b c d where
  toFun i := ssToDiagonalLabel a b c d i
  invFun
    | Sum.inl () =>
        ⟨newSSLabelOne a b c d, newSSLabelOne_ne_newSSLabelZero a b c d⟩
    | Sum.inr i =>
        ⟨liftSSPassiveLabel a b c d i, liftSSPassiveLabel_ne_newSSLabelZero a b c d i⟩
  left_inv i := by
    rcases i with ⟨⟨A, i⟩, hi⟩
    apply Subtype.ext
    cases A
    · rfl
    · rfl
    · rfl
    · revert hi
      refine Fin.cases ?_ (fun j hi => ?_) i
      · intro hi
        exact False.elim (hi rfl)
      · revert hi
        refine Fin.cases (fun _ => ?_) (fun _ _ => ?_) j <;> rfl
  right_inv i := by
    rcases i with (_ | i)
    · rfl
    · rcases i with ⟨A, i⟩
      cases A <;> rfl

/-- Every passive coordinate has its displayed unique preimage. -/
theorem ssToDiagonalLabel_eq_passive_iff (a b c d : ℕ)
    (i : SSLabel a b c d)
    (j : SpeciesLabel (boundaryMultiplicity a b c d)) :
    ssToDiagonalLabel a b c d i = Sum.inr j ↔
      i = liftSSPassiveLabel a b c d j := by
  constructor
  · intro h
    have hi : i ≠ newSSLabelZero a b c d := by
      intro hi
      subst i
      simp at h
    have hcollision : ssToDiagonalLabel a b c d
        (liftSSPassiveLabel a b c d j) = Sum.inr j :=
      ssToDiagonalLabel_passive a b c d j
    have heq : (ssResidualEquiv a b c d) ⟨i, hi⟩ =
        (ssResidualEquiv a b c d)
          ⟨liftSSPassiveLabel a b c d j,
            liftSSPassiveLabel_ne_newSSLabelZero a b c d j⟩ :=
      h.trans hcollision.symm
    exact congrArg Subtype.val ((ssResidualEquiv a b c d).injective heq)
  · rintro rfl
    exact ssToDiagonalLabel_passive a b c d j

@[simp]
theorem mapDomain_ssToDiagonalLabel_apply_collision (a b c d : ℕ)
    (e : SSLabel a b c d →₀ ℕ) :
    Finsupp.mapDomain (ssToDiagonalLabel a b c d) e
        (Sum.inl () : BoundaryDiagonalLabel a b c d) =
      e (newSSLabelZero a b c d) + e (newSSLabelOne a b c d) := by
  classical
  induction e using Finsupp.induction with
  | zero => simp
  | single_add i n e hi hn ih =>
      rw [Finsupp.mapDomain_add, Finsupp.add_apply, Finsupp.add_apply,
        Finsupp.add_apply, ih, Finsupp.mapDomain_single]
      by_cases hiZero : i = newSSLabelZero a b c d
      · subst i
        simp [newSSLabelOne_ne_newSSLabelZero]
        omega
      · by_cases hiOne : i = newSSLabelOne a b c d
        · subst i
          simp [newSSLabelOne_ne_newSSLabelZero]
          omega
        · have hdiag : ssToDiagonalLabel a b c d i ≠ Sum.inl () := by
            simpa [ssToDiagonalLabel_eq_collision_iff] using
              not_or_intro hiZero hiOne
          simp [hiZero, hiOne, hdiag]

@[simp]
theorem mapDomain_ssToDiagonalLabel_apply_passive (a b c d : ℕ)
    (e : SSLabel a b c d →₀ ℕ)
    (j : SpeciesLabel (boundaryMultiplicity a b c d)) :
    Finsupp.mapDomain (ssToDiagonalLabel a b c d) e (Sum.inr j) =
      e (liftSSPassiveLabel a b c d j) := by
  classical
  induction e using Finsupp.induction with
  | zero => simp
  | single_add i n e hi hn ih =>
      rw [Finsupp.mapDomain_add, Finsupp.add_apply, Finsupp.add_apply,
        ih, Finsupp.mapDomain_single]
      by_cases hij : i = liftSSPassiveLabel a b c d j
      · subst i
        simp
      · have hdiag : ssToDiagonalLabel a b c d i ≠ Sum.inr j := by
          simpa [ssToDiagonalLabel_eq_passive_iff] using hij
        simp [hij, hdiag]

/-- Exact active/passive classification of an `SS` exponent fiber. -/
theorem mapDomain_ssToDiagonalLabel_eq_iff (a b c d q : ℕ)
    (e : SSLabel a b c d →₀ ℕ)
    (v : SpeciesLabel (boundaryMultiplicity a b c d) →₀ ℕ) :
    Finsupp.mapDomain (ssToDiagonalLabel a b c d) e =
        Finsupp.single (Sum.inl () : BoundaryDiagonalLabel a b c d) q +
          Finsupp.mapDomain Sum.inr v ↔
      e (newSSLabelZero a b c d) + e (newSSLabelOne a b c d) = q ∧
        ∀ j, e (liftSSPassiveLabel a b c d j) = v j := by
  constructor
  · intro h
    constructor
    · have hc := congrArg
          (fun w : BoundaryDiagonalLabel a b c d →₀ ℕ => w (Sum.inl ())) h
      have hzero : Finsupp.mapDomain Sum.inr v
          (Sum.inl () : BoundaryDiagonalLabel a b c d) = 0 :=
        Finsupp.mapDomain_notin_range v _ (by simp)
      simpa [hzero] using hc
    · intro j
      have hp := congrArg
        (fun w : BoundaryDiagonalLabel a b c d →₀ ℕ => w (Sum.inr j)) h
      change Finsupp.mapDomain (ssToDiagonalLabel a b c d) e (Sum.inr j) =
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

/-- Decompose an `SS` tuple into the ordered active modes and an arbitrary labelled passive
tuple. -/
def ssModeTupleEquiv (jetOrder a b c d : ℕ) :
    MultispeciesModeTuple jetOrder (boundaryMultiplicity a b c (d + 2)) ≃
      (Fin (jetOrder + 1) × Fin (jetOrder + 1)) ×
        MultispeciesModeTuple jetOrder (boundaryMultiplicity a b c d) where
  toFun r :=
    ((r .S (0 : Fin (d + 2)), r .S (1 : Fin (d + 2))), fun A =>
      match A with
      | .X => fun i => r .X i
      | .Y => fun i => r .Y i
      | .Z => fun i => r .Z i
      | .S => fun i => r .S i.succ.succ)
  invFun z := fun A =>
    match A with
    | .X => z.2 .X
    | .Y => z.2 .Y
    | .Z => z.2 .Z
    | .S => Fin.cons z.1.1 (Fin.cons z.1.2 (z.2 .S))
  left_inv r := by
    funext A i
    cases A
    · rfl
    · rfl
    · rfl
    · refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · refine Fin.cases ?_ (fun k => ?_) j <;> rfl
  right_inv z := by
    rcases z with ⟨⟨rs₀, rs₁⟩, t⟩
    apply Prod.ext
    · rfl
    · funext A i
      cases A <;> rfl

@[simp]
theorem shiftedExponent_ssModeTupleEquiv_symm_activeZero
    {jetOrder a b c d : ℕ} (rs : Fin (jetOrder + 1) × Fin (jetOrder + 1))
    (t : MultispeciesModeTuple jetOrder (boundaryMultiplicity a b c d)) :
    shiftedMultispeciesLabelledExponent boundarySpeciesShift
        ((ssModeTupleEquiv jetOrder a b c d).symm (rs, t))
        (newSSLabelZero a b c d) = (rs.1 : ℕ) + 1 := by
  simp [shiftedMultispeciesLabelledExponent, speciesShiftExponent,
    multispeciesLabelledExponent, ssModeTupleEquiv, newSSLabelZero,
    boundarySpeciesShift, add_comm]

@[simp]
theorem shiftedExponent_ssModeTupleEquiv_symm_activeOne
    {jetOrder a b c d : ℕ} (rs : Fin (jetOrder + 1) × Fin (jetOrder + 1))
    (t : MultispeciesModeTuple jetOrder (boundaryMultiplicity a b c d)) :
    shiftedMultispeciesLabelledExponent boundarySpeciesShift
        ((ssModeTupleEquiv jetOrder a b c d).symm (rs, t))
        (newSSLabelOne a b c d) = (rs.2 : ℕ) + 1 := by
  simp [shiftedMultispeciesLabelledExponent, speciesShiftExponent,
    multispeciesLabelledExponent, ssModeTupleEquiv, newSSLabelOne,
    boundarySpeciesShift, add_comm]

@[simp]
theorem shiftedExponent_ssModeTupleEquiv_symm_passive
    {jetOrder a b c d : ℕ} (rs : Fin (jetOrder + 1) × Fin (jetOrder + 1))
    (t : MultispeciesModeTuple jetOrder (boundaryMultiplicity a b c d))
    (j : SpeciesLabel (boundaryMultiplicity a b c d)) :
    shiftedMultispeciesLabelledExponent boundarySpeciesShift
        ((ssModeTupleEquiv jetOrder a b c d).symm (rs, t))
        (liftSSPassiveLabel a b c d j) =
      shiftedMultispeciesLabelledExponent boundarySpeciesShift t j := by
  rcases j with ⟨A, j⟩
  have htuple := (ssModeTupleEquiv jetOrder a b c d).apply_symm_apply (rs, t)
  have hmode := congrArg
    (fun z : (Fin (jetOrder + 1) × Fin (jetOrder + 1)) ×
        MultispeciesModeTuple jetOrder (boundaryMultiplicity a b c d) => z.2 A j) htuple
  cases A <;>
    simpa [shiftedMultispeciesLabelledExponent, speciesShiftExponent,
      multispeciesLabelledExponent, ssModeTupleEquiv, liftSSPassiveLabel,
      boundarySpeciesShift] using congrArg Fin.val hmode

@[simp]
theorem multispeciesUnordered_ssModeTupleEquiv_symm
    {jetOrder a b c d : ℕ} (rs : Fin (jetOrder + 1) × Fin (jetOrder + 1))
    (t : MultispeciesModeTuple jetOrder (boundaryMultiplicity a b c d)) :
    multispeciesUnorderedModeBlock
        ((ssModeTupleEquiv jetOrder a b c d).symm (rs, t)) =
      boundaryModeConfiguration
        (unorderedModeBlock (t .X))
        (unorderedModeBlock (t .Y))
        (unorderedModeBlock (t .Z))
        (rs.1 ::ₛ rs.2 ::ₛ unorderedModeBlock (t .S)) := by
  funext A
  cases A
  · rfl
  · rfl
  · rfl
  · change unorderedModeBlock (Fin.cons rs.1 (Fin.cons rs.2 (t .S))) =
      rs.1 ::ₛ rs.2 ::ₛ unorderedModeBlock (t .S)
    rw [unorderedModeBlock_fin_cons, unorderedModeBlock_fin_cons]

theorem ssModeTuple_passiveExponent_eq_iff
    {jetOrder a b c d : ℕ} (rs : Fin (jetOrder + 1) × Fin (jetOrder + 1))
    (t t₀ : MultispeciesModeTuple jetOrder (boundaryMultiplicity a b c d)) :
    (∀ j,
        shiftedMultispeciesLabelledExponent boundarySpeciesShift
            ((ssModeTupleEquiv jetOrder a b c d).symm (rs, t))
            (liftSSPassiveLabel a b c d j) =
          shiftedMultispeciesLabelledExponent boundarySpeciesShift t₀ j) ↔
      t = t₀ := by
  simp only [shiftedExponent_ssModeTupleEquiv_symm_passive]
  constructor
  · intro h
    apply shiftedMultispeciesLabelledExponent_injective boundarySpeciesShift
    ext j
    exact h j
  · rintro rfl
    simp

/-- Ordered active pairs contributing to the coefficient of the shifted field square. -/
def shiftedS2CoefficientPairs (jetOrder q : ℕ) :
    Finset (Fin (jetOrder + 1) × Fin (jetOrder + 1)) :=
  Finset.univ.filter (fun rs => 2 + ((rs.1 : ℕ) + (rs.2 : ℕ)) = q)

/-- The shifted `S^2` diagonal functional in the convention whose total particle number is
written `d+2`. -/
def shiftedS2DiagonalCoefficient {jetOrder d : ℕ} (q : ℕ)
    (spectator : ModeConfiguration jetOrder d)
    (F : JetParticleSpace K jetOrder (d + 2)) : K :=
  ∑ rs ∈ shiftedS2CoefficientPairs jetOrder q,
    F (rs.1 ::ₛ rs.2 ::ₛ spectator)

/-- The corresponding shifted `S^2` relation coefficient in mode space. -/
def shiftedS2RelationMode {jetOrder d : ℕ} (q : ℕ)
    (spectator : ModeConfiguration jetOrder d) :
    JetModeSpace K jetOrder (d + 2) :=
  ∑ rs ∈ shiftedS2CoefficientPairs jetOrder q,
    jetDeltaMode (K := K) (rs.1 ::ₛ rs.2 ::ₛ spectator)

theorem shiftedS2Relation_adjoint_diagonal {jetOrder d : ℕ} (q : ℕ)
    (spectator : ModeConfiguration jetOrder d)
    (F : JetParticleSpace K jetOrder (d + 2)) :
    jetModeParticlePairing (shiftedS2RelationMode (K := K) q spectator) F =
      shiftedS2DiagonalCoefficient q spectator F := by
  rw [shiftedS2RelationMode, jetModeParticlePairing_sum]
  simp [shiftedS2DiagonalCoefficient]

/-- All shifted `S^2` coefficients with arbitrary same-species spectators. -/
def shiftedS2RelationSet (jetOrder d : ℕ) :
    Set (JetModeSpace K jetOrder (d + 2)) :=
  Set.range (fun i : ℕ × ModeConfiguration jetOrder d =>
    shiftedS2RelationMode (K := K) i.1 i.2)

theorem shiftedS2_span_orthogonal_iff_diagonal {jetOrder d : ℕ}
    (F : JetParticleSpace K jetOrder (d + 2)) :
    AnnihilatesSpan (jetPairingFunctional F)
        (shiftedS2RelationSet (K := K) jetOrder d) ↔
      ∀ q spectator, shiftedS2DiagonalCoefficient q spectator F = 0 := by
  rw [annihilatesSpan_iff]
  simp only [shiftedS2RelationSet, Set.forall_mem_range,
    jetPairingFunctional_apply, shiftedS2Relation_adjoint_diagonal, Prod.forall]

/-- Coefficients of the typed `SS` substitution are the exact exponent-fiber sums. -/
theorem coeff_ssDiagonalSubstitution_eq_fiberSum
    {jetOrder a b c d q : ℕ}
    (F : MultispeciesJetParticleSpace K jetOrder
      (boundaryMultiplicity a b c (d + 2)))
    (v : SpeciesLabel (boundaryMultiplicity a b c d) →₀ ℕ) :
    MvPolynomial.coeff
        (Finsupp.single (Sum.inl () : BoundaryDiagonalLabel a b c d) q +
          Finsupp.mapDomain Sum.inr v)
        (ssDiagonalSubstitution (K := K) a b c d
          (shiftedMultispeciesParticlePolynomial boundarySpeciesShift F)) =
      ∑ r : MultispeciesModeTuple jetOrder
          (boundaryMultiplicity a b c (d + 2)),
        if
          (shiftedMultispeciesLabelledExponent boundarySpeciesShift r)
              (newSSLabelZero a b c d) +
                (shiftedMultispeciesLabelledExponent boundarySpeciesShift r)
                  (newSSLabelOne a b c d) = q ∧
            ∀ j,
              (shiftedMultispeciesLabelledExponent boundarySpeciesShift r)
                  (liftSSPassiveLabel a b c d j) = v j
        then F (multispeciesUnorderedModeBlock r) else 0 := by
  classical
  simp only [ssDiagonalSubstitution, shiftedMultispeciesParticlePolynomial, map_sum,
    MvPolynomial.coeff_sum, MvPolynomial.rename_monomial, MvPolynomial.coeff_monomial]
  apply Finset.sum_congr (by ext; simp)
  intro r _
  simp only [mapDomain_ssToDiagonalLabel_eq_iff]

/-- On an arbitrary labelled passive tuple, the `SS` polynomial coefficient is exactly the
ordered shifted `S^2` diagonal coefficient, including its ordered multiplicity. -/
theorem coeff_ssDiagonalSubstitution_tupleExponent
    {jetOrder a b c d : ℕ} (q : ℕ)
    (t₀ : MultispeciesModeTuple jetOrder (boundaryMultiplicity a b c d))
    (F : MultispeciesJetParticleSpace K jetOrder
      (boundaryMultiplicity a b c (d + 2))) :
    MvPolynomial.coeff (boundaryDiagonalTupleExponent q t₀)
        (ssDiagonalSubstitution (K := K) a b c d
          (shiftedMultispeciesParticlePolynomial boundarySpeciesShift F)) =
      shiftedS2DiagonalCoefficient q (unorderedModeBlock (t₀ .S))
        (fun s => F (boundaryModeConfiguration
          (unorderedModeBlock (t₀ .X))
          (unorderedModeBlock (t₀ .Y))
          (unorderedModeBlock (t₀ .Z)) s)) := by
  classical
  rw [show boundaryDiagonalTupleExponent q t₀ =
      Finsupp.single (Sum.inl () : BoundaryDiagonalLabel a b c d) q +
        Finsupp.mapDomain Sum.inr
          (shiftedMultispeciesLabelledExponent boundarySpeciesShift t₀) from rfl]
  rw [coeff_ssDiagonalSubstitution_eq_fiberSum]
  let H := fun r : MultispeciesModeTuple jetOrder
      (boundaryMultiplicity a b c (d + 2)) =>
    if
      (shiftedMultispeciesLabelledExponent boundarySpeciesShift r)
          (newSSLabelZero a b c d) +
            (shiftedMultispeciesLabelledExponent boundarySpeciesShift r)
              (newSSLabelOne a b c d) = q ∧
        ∀ j,
          (shiftedMultispeciesLabelledExponent boundarySpeciesShift r)
              (liftSSPassiveLabel a b c d j) =
            shiftedMultispeciesLabelledExponent boundarySpeciesShift t₀ j
    then F (multispeciesUnorderedModeBlock r) else 0
  change (∑ r, H r) = _
  rw [shiftedS2DiagonalCoefficient]
  calc
    (∑ r, H r) =
        ∑ z : (Fin (jetOrder + 1) × Fin (jetOrder + 1)) ×
            MultispeciesModeTuple jetOrder (boundaryMultiplicity a b c d),
          H ((ssModeTupleEquiv jetOrder a b c d).symm z) := by
      exact (Equiv.sum_comp (ssModeTupleEquiv jetOrder a b c d).symm H).symm
    _ = ∑ rs : Fin (jetOrder + 1) × Fin (jetOrder + 1),
          if 2 + ((rs.1 : ℕ) + (rs.2 : ℕ)) = q then
            F (boundaryModeConfiguration
              (unorderedModeBlock (t₀ .X))
              (unorderedModeBlock (t₀ .Y))
              (unorderedModeBlock (t₀ .Z))
              (rs.1 ::ₛ rs.2 ::ₛ unorderedModeBlock (t₀ .S)))
          else 0 := by
      rw [Fintype.sum_prod_type]
      apply Fintype.sum_congr
      intro rs
      by_cases hrs : 2 + ((rs.1 : ℕ) + (rs.2 : ℕ)) = q
      · simp only [H, shiftedExponent_ssModeTupleEquiv_symm_activeZero,
          shiftedExponent_ssModeTupleEquiv_symm_activeOne,
          show (rs.1 : ℕ) + 1 + ((rs.2 : ℕ) + 1) = q from by omega,
          true_and, ssModeTuple_passiveExponent_eq_iff, if_true]
        rw [Fintype.sum_ite_eq' t₀]
        rw [multispeciesUnordered_ssModeTupleEquiv_symm]
        simp [hrs]
        rfl
      · have hrs' : ¬((rs.1 : ℕ) + 1 + ((rs.2 : ℕ) + 1) = q) := by omega
        simp only [H, shiftedExponent_ssModeTupleEquiv_symm_activeZero,
          shiftedExponent_ssModeTupleEquiv_symm_activeOne, hrs', false_and, if_false]
        simp [hrs]
    _ = ∑ r ∈ shiftedS2CoefficientPairs jetOrder q,
          F (boundaryModeConfiguration
            (unorderedModeBlock (t₀ .X))
            (unorderedModeBlock (t₀ .Y))
            (unorderedModeBlock (t₀ .Z))
            (r.1 ::ₛ r.2 ::ₛ unorderedModeBlock (t₀ .S))) := by
      rw [shiftedS2CoefficientPairs, Finset.sum_filter]

/-- Fixing the current configurations turns a four-species coefficient family into the
one-species coefficient family paired with `S^2`. -/
def sliceSAtCurrents {jetOrder a b c d : ℕ}
    (F : MultispeciesJetParticleSpace K jetOrder (boundaryMultiplicity a b c d))
    (bx : ModeConfiguration jetOrder a)
    (byy : ModeConfiguration jetOrder b)
    (bz : ModeConfiguration jetOrder c) : JetParticleSpace K jetOrder d :=
  fun s => F (boundaryModeConfiguration bx byy bz s)

/-- Four-species orthogonality to every coefficient of shifted `S(z)^2`, with arbitrary
current and `S` spectators. -/
def IsBoundaryS2Orthogonal {jetOrder a b c d : ℕ}
    (F : MultispeciesJetParticleSpace K jetOrder
      (boundaryMultiplicity a b c (d + 2))) : Prop :=
  ∀ bx byy bz,
    AnnihilatesSpan
      (jetPairingFunctional (sliceSAtCurrents F bx byy bz))
      (shiftedS2RelationSet (K := K) jetOrder d)

/-- `S^2` relation-span orthogonality kills the complete typed `S`--`S` diagonal polynomial. -/
theorem boundaryS2Orthogonal_ssDiagonalSubstitution_eq_zero
    {jetOrder a b c d : ℕ}
    (F : MultispeciesJetParticleSpace K jetOrder
      (boundaryMultiplicity a b c (d + 2)))
    (hF : IsBoundaryS2Orthogonal F) :
    ssDiagonalSubstitution (K := K) a b c d
        (shiftedMultispeciesParticlePolynomial boundarySpeciesShift F) = 0 := by
  apply MvPolynomial.ext
  intro target
  by_cases hcoeff : MvPolynomial.coeff target
      (ssDiagonalSubstitution (K := K) a b c d
        (shiftedMultispeciesParticlePolynomial boundarySpeciesShift F)) ≠ 0
  · classical
    simp only [ssDiagonalSubstitution, shiftedMultispeciesParticlePolynomial, map_sum,
      MvPolynomial.coeff_sum, MvPolynomial.rename_monomial,
      MvPolynomial.coeff_monomial] at hcoeff
    obtain ⟨r, _, hr⟩ := Finset.exists_ne_zero_of_sum_ne_zero hcoeff
    split at hr
    · rename_i hmap
      let z := ssModeTupleEquiv jetOrder a b c d r
      let q : ℕ :=
        ((shiftedMultispeciesLabelledExponent boundarySpeciesShift r)
          (newSSLabelZero a b c d)) +
        ((shiftedMultispeciesLabelledExponent boundarySpeciesShift r)
          (newSSLabelOne a b c d))
      have htarget : target = boundaryDiagonalTupleExponent q z.2 := by
        rw [← hmap]
        apply (mapDomain_ssToDiagonalLabel_eq_iff a b c d q _ _).2
        constructor
        · rfl
        · intro j
          have hrz : r = (ssModeTupleEquiv jetOrder a b c d).symm z :=
            (ssModeTupleEquiv jetOrder a b c d).symm_apply_apply r |>.symm
          rw [hrz]
          exact shiftedExponent_ssModeTupleEquiv_symm_passive z.1 z.2 j
      rw [htarget, coeff_ssDiagonalSubstitution_tupleExponent]
      exact (shiftedS2_span_orthogonal_iff_diagonal
        (sliceSAtCurrents F
          (unorderedModeBlock (z.2 .X))
          (unorderedModeBlock (z.2 .Y))
          (unorderedModeBlock (z.2 .Z)))).1
        (hF _ _ _) q (unorderedModeBlock (z.2 .S))
    · simp at hr
  · simpa [not_ne_iff.mp hcoeff]

theorem ssToDiagonalLabel_eq_residual_collisionIndex (a b c d : ℕ)
    (i : SSLabel a b c d) :
    ssToDiagonalLabel a b c d i =
      ssResidualEquiv a b c d
        (collisionIndex (newSSLabelZero a b c d) (newSSLabelOne a b c d)
          (newSSLabelOne_ne_newSSLabelZero a b c d) i) := by
  rcases i with ⟨A, i⟩
  cases A
  · rfl
  · rfl
  · rfl
  · refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · refine Fin.cases ?_ (fun _ => ?_) j <;> rfl

theorem ssDiagonalSubstitution_eq_rename_collisionMap (a b c d : ℕ)
    (p : MvPolynomial (SSLabel a b c d) K) :
    ssDiagonalSubstitution (K := K) a b c d p =
      MvPolynomial.rename (ssResidualEquiv a b c d)
        (collisionMap (K := K) (newSSLabelZero a b c d) (newSSLabelOne a b c d)
          (newSSLabelOne_ne_newSSLabelZero a b c d) p) := by
  suffices hhom :
      ssDiagonalSubstitution (K := K) a b c d =
        (MvPolynomial.rename (ssResidualEquiv a b c d)).comp
          (collisionMap (K := K) (newSSLabelZero a b c d) (newSSLabelOne a b c d)
            (newSSLabelOne_ne_newSSLabelZero a b c d)) by
    exact DFunLike.congr_fun hhom p
  apply MvPolynomial.algHom_ext
  intro i
  simp only [ssDiagonalSubstitution, collisionMap, AlgHom.comp_apply,
    MvPolynomial.rename_X]
  rw [ssToDiagonalLabel_eq_residual_collisionIndex]

/-- Apply an arbitrary permutation to `S` labels and fix the three current species. -/
def boundarySPermutation (a b c d : ℕ) (g : Equiv.Perm (Fin d)) :
    SpeciesPermutation (boundaryMultiplicity a b c d)
  | .X => Equiv.refl _
  | .Y => Equiv.refl _
  | .Z => Equiv.refl _
  | .S => g

@[simp]
theorem speciesLabelEquiv_boundarySPermutation_S (a b c d : ℕ)
    (g : Equiv.Perm (Fin d)) (i : Fin d) :
    speciesLabelEquiv (boundarySPermutation a b c d g)
        (⟨.S, i⟩ : SpeciesLabel (boundaryMultiplicity a b c d)) = ⟨.S, g i⟩ := by
  rfl

/-- `S^2` orthogonality implies the literal collision vanishing for every ordered pair of
distinct labelled `S` particles, not only for the two distinguished slots. -/
theorem boundaryS2Orthogonal_all_literal_collisions [CharZero K]
    {jetOrder a b c d : ℕ}
    (F : MultispeciesJetParticleSpace K jetOrder
      (boundaryMultiplicity a b c (d + 2)))
    (hF : IsBoundaryS2Orthogonal F) :
    ∀ i j : Fin (d + 2),
      ∀ hji : boundarySpeciesLabel a b c (d + 2) .S j ≠
        boundarySpeciesLabel a b c (d + 2) .S i,
      collisionMap (K := K) (boundarySpeciesLabel a b c (d + 2) .S i)
        (boundarySpeciesLabel a b c (d + 2) .S j) hji
        (shiftedMultispeciesParticlePolynomial boundarySpeciesShift F) = 0 := by
  let p := shiftedMultispeciesParticlePolynomial boundarySpeciesShift F
  have htyped := boundaryS2Orthogonal_ssDiagonalSubstitution_eq_zero F hF
  rw [ssDiagonalSubstitution_eq_rename_collisionMap] at htyped
  have hactiveZero : collisionMap (K := K) (newSSLabelZero a b c d)
      (newSSLabelOne a b c d) (newSSLabelOne_ne_newSSLabelZero a b c d) p = 0 := by
    apply MvPolynomial.rename_injective (ssResidualEquiv a b c d)
      (ssResidualEquiv a b c d).injective
    simpa only [map_zero] using htyped
  have hactive : collisionFactor (K := K) (newSSLabelZero a b c d)
      (newSSLabelOne a b c d) ∣ p :=
    (collisionFactor_dvd_iff _ _ (newSSLabelOne_ne_newSSLabelZero a b c d) p).2
      hactiveZero
  intro i j hji
  apply (collisionFactor_dvd_iff _ _ hji p).1
  have hjiFin : j ≠ i := by
    intro hij
    subst j
    exact hji rfl
  let source : Bool → Fin (d + 2) := fun t => if t then 1 else 0
  let target : Bool → Fin (d + 2) := fun t => if t then j else i
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
  have hg0 : g (0 : Fin (d + 2)) = i := by
    simpa [source, target] using hg false
  have hg1 : g (1 : Fin (d + 2)) = j := by
    simpa [source, target] using hg true
  have hmove := collisionFactor_dvd_of_rename_invariant
    (speciesLabelEquiv (boundarySPermutation a b c (d + 2) g)) p
    (shiftedMultispeciesParticlePolynomial_rename boundarySpeciesShift
      (boundarySPermutation a b c (d + 2) g) F)
    hactive
  change collisionFactor (K := K)
      (speciesLabelEquiv (boundarySPermutation a b c (d + 2) g)
        (⟨.S, (0 : Fin (d + 2))⟩ : SpeciesLabel
          (boundaryMultiplicity a b c (d + 2))))
      (speciesLabelEquiv (boundarySPermutation a b c (d + 2) g)
        (⟨.S, (1 : Fin (d + 2))⟩ : SpeciesLabel
          (boundaryMultiplicity a b c (d + 2)))) ∣ p at hmove
  rw [speciesLabelEquiv_boundarySPermutation_S,
    speciesLabelEquiv_boundarySPermutation_S, hg0, hg1] at hmove
  exact hmove

end ShiftedSS

section ShiftedCurrentS

/-- Ordered active current/`S` pairs contributing to a coefficient of `A(z)S(z)`. -/
def shiftedASCoefficientPairs (jetOrder q : ℕ) :
    Finset (Fin (jetOrder + 1) × Fin (jetOrder + 1)) :=
  Finset.univ.filter (fun rs => (rs.1 : ℕ) + 1 + (rs.2 : ℕ) = q)

/-- The shifted mixed diagonal functional, with the current mode first and the shifted `S`
mode second. -/
def shiftedASDiagonalCoefficient {jetOrder a d : ℕ} (q : ℕ)
    (aSpectator : ModeConfiguration jetOrder a)
    (sSpectator : ModeConfiguration jetOrder d)
    (F : TwoSpeciesParticleSpace K jetOrder (a + 1) (d + 1)) : K :=
  ∑ rs ∈ shiftedASCoefficientPairs jetOrder q,
    F (rs.1 ::ₛ aSpectator, rs.2 ::ₛ sSpectator)

/-- The matching coefficient of the shifted mixed relation in mode space. -/
def shiftedASRelationMode {jetOrder a d : ℕ} (q : ℕ)
    (aSpectator : ModeConfiguration jetOrder a)
    (sSpectator : ModeConfiguration jetOrder d) :
    TwoSpeciesModeSpace K jetOrder (a + 1) (d + 1) :=
  ∑ rs ∈ shiftedASCoefficientPairs jetOrder q,
    twoSpeciesDeltaMode (K := K)
      (rs.1 ::ₛ aSpectator, rs.2 ::ₛ sSpectator)

theorem shiftedASRelation_adjoint_diagonal {jetOrder a d : ℕ} (q : ℕ)
    (aSpectator : ModeConfiguration jetOrder a)
    (sSpectator : ModeConfiguration jetOrder d)
    (F : TwoSpeciesParticleSpace K jetOrder (a + 1) (d + 1)) :
    twoSpeciesPairing (shiftedASRelationMode (K := K) q aSpectator sSpectator) F =
      shiftedASDiagonalCoefficient q aSpectator sSpectator F := by
  rw [shiftedASRelationMode, twoSpeciesPairing_sum]
  simp [shiftedASDiagonalCoefficient]

/-- All shifted mixed coefficients with arbitrary spectators of the two active species. -/
def shiftedASRelationSet (jetOrder a d : ℕ) :
    Set (TwoSpeciesModeSpace K jetOrder (a + 1) (d + 1)) :=
  Set.range (fun i : ℕ ×
      (ModeConfiguration jetOrder a × ModeConfiguration jetOrder d) =>
    shiftedASRelationMode (K := K) i.1 i.2.1 i.2.2)

theorem shiftedAS_span_orthogonal_iff_diagonal {jetOrder a d : ℕ}
    (F : TwoSpeciesParticleSpace K jetOrder (a + 1) (d + 1)) :
    AnnihilatesSpan (twoSpeciesPairingFunctional F)
        (shiftedASRelationSet (K := K) jetOrder a d) ↔
      ∀ q aSpectator sSpectator,
        shiftedASDiagonalCoefficient q aSpectator sSpectator F = 0 := by
  rw [annihilatesSpan_iff]
  simp only [shiftedASRelationSet, Set.forall_mem_range,
    twoSpeciesPairingFunctional_apply, shiftedASRelation_adjoint_diagonal,
    Prod.forall]

/-- Divisibility by a collision equation is independent of its orientation. -/
theorem reverse_collisionFactor_dvd {I : Type*} [DecidableEq I]
    (i j : I) (p : MvPolynomial I K)
    (h : collisionFactor (K := K) i j ∣ p) :
    collisionFactor (K := K) j i ∣ p := by
  rw [show collisionFactor (K := K) j i =
    -collisionFactor (K := K) i j by simp [collisionFactor, neg_sub]]
  exact h.neg_left

section XS

abbrev XSLabel (a b c d : ℕ) :=
  SpeciesLabel (boundaryMultiplicity (a + 1) b c (d + 1))

def liftXSPassiveLabel (a b c d : ℕ) :
    SpeciesLabel (boundaryMultiplicity a b c d) → XSLabel a b c d
  | ⟨.X, i⟩ => ⟨.X, i.succ⟩
  | ⟨.Y, i⟩ => ⟨.Y, i⟩
  | ⟨.Z, i⟩ => ⟨.Z, i⟩
  | ⟨.S, i⟩ => ⟨.S, i.succ⟩

def newXSLabelX (a b c d : ℕ) : XSLabel a b c d :=
  ⟨.X, (0 : Fin (a + 1))⟩

def newXSLabelS (a b c d : ℕ) : XSLabel a b c d :=
  ⟨.S, (0 : Fin (d + 1))⟩

theorem newXSLabelS_ne_newXSLabelX (a b c d : ℕ) :
    newXSLabelS a b c d ≠ newXSLabelX a b c d := by
  simp [newXSLabelS, newXSLabelX]

def xsToDiagonalLabel (a b c d : ℕ) :
    XSLabel a b c d → BoundaryDiagonalLabel a b c d
  | ⟨.X, i⟩ => Fin.cases (Sum.inl ()) (fun j => Sum.inr ⟨.X, j⟩) i
  | ⟨.Y, i⟩ => Sum.inr ⟨.Y, i⟩
  | ⟨.Z, i⟩ => Sum.inr ⟨.Z, i⟩
  | ⟨.S, i⟩ => Fin.cases (Sum.inl ()) (fun j => Sum.inr ⟨.S, j⟩) i

def xsDiagonalSubstitution (a b c d : ℕ) :
    MvPolynomial (XSLabel a b c d) K →ₐ[K]
      MvPolynomial (BoundaryDiagonalLabel a b c d) K :=
  MvPolynomial.rename (xsToDiagonalLabel a b c d)

@[simp]
theorem xsToDiagonalLabel_newX (a b c d : ℕ) :
    xsToDiagonalLabel a b c d (newXSLabelX a b c d) = Sum.inl () := by rfl

@[simp]
theorem xsToDiagonalLabel_newS (a b c d : ℕ) :
    xsToDiagonalLabel a b c d (newXSLabelS a b c d) = Sum.inl () := by rfl

@[simp]
theorem xsToDiagonalLabel_passive (a b c d : ℕ)
    (i : SpeciesLabel (boundaryMultiplicity a b c d)) :
    xsToDiagonalLabel a b c d (liftXSPassiveLabel a b c d i) = Sum.inr i := by
  rcases i with ⟨A, i⟩
  cases A <;> rfl

theorem xsToDiagonalLabel_eq_collision_iff (a b c d : ℕ)
    (i : XSLabel a b c d) :
    xsToDiagonalLabel a b c d i = Sum.inl () ↔
      i = newXSLabelX a b c d ∨ i = newXSLabelS a b c d := by
  rcases i with ⟨A, i⟩
  cases A
  · refine Fin.cases ?_ (fun j => ?_) i
    · simp [xsToDiagonalLabel, newXSLabelX, newXSLabelS]
    · constructor
      · intro h
        simp only [xsToDiagonalLabel] at h
        contradiction
      · rintro (h | h)
        · have hv := congrArg (fun q : XSLabel a b c d => (q.2 : ℕ)) h
          simp [newXSLabelX] at hv
        · simp [newXSLabelS, newXSLabelX] at h
  · simp [xsToDiagonalLabel, newXSLabelX, newXSLabelS]
  · simp [xsToDiagonalLabel, newXSLabelX, newXSLabelS]
  · refine Fin.cases ?_ (fun j => ?_) i
    · simp [xsToDiagonalLabel, newXSLabelX, newXSLabelS]
    · constructor
      · intro h
        simp only [xsToDiagonalLabel] at h
        contradiction
      · rintro (h | h)
        · simp [newXSLabelS, newXSLabelX] at h
        · have hv := congrArg (fun q : XSLabel a b c d => (q.2 : ℕ)) h
          simp [newXSLabelS] at hv

theorem liftXSPassiveLabel_ne_newXSLabelX (a b c d : ℕ)
    (i : SpeciesLabel (boundaryMultiplicity a b c d)) :
    liftXSPassiveLabel a b c d i ≠ newXSLabelX a b c d := by
  intro h
  rcases i with ⟨A, i⟩
  cases A
  · have hv := congrArg (fun q : XSLabel a b c d => (q.2 : ℕ)) h
    change ((i.succ : Fin (a + 1)) : ℕ) = ((0 : Fin (a + 1)) : ℕ) at hv
    simp at hv
  · simp [liftXSPassiveLabel, newXSLabelX] at h
  · simp [liftXSPassiveLabel, newXSLabelX] at h
  · simp [liftXSPassiveLabel, newXSLabelX] at h

def xsResidualEquiv (a b c d : ℕ) :
    {i : XSLabel a b c d // i ≠ newXSLabelX a b c d} ≃
      BoundaryDiagonalLabel a b c d where
  toFun i := xsToDiagonalLabel a b c d i
  invFun
    | Sum.inl () => ⟨newXSLabelS a b c d, newXSLabelS_ne_newXSLabelX a b c d⟩
    | Sum.inr i =>
        ⟨liftXSPassiveLabel a b c d i, liftXSPassiveLabel_ne_newXSLabelX a b c d i⟩
  left_inv i := by
    rcases i with ⟨⟨A, i⟩, hi⟩
    apply Subtype.ext
    cases A
    · revert hi
      refine Fin.cases ?_ (fun _ _ => ?_) i
      · intro hi
        exact False.elim (hi rfl)
      · rfl
    · rfl
    · rfl
    · revert hi
      refine Fin.cases (fun _ => ?_) (fun _ _ => ?_) i <;> rfl
  right_inv i := by
    rcases i with (_ | i)
    · rfl
    · rcases i with ⟨A, i⟩
      cases A <;> rfl

theorem xsToDiagonalLabel_eq_passive_iff (a b c d : ℕ)
    (i : XSLabel a b c d)
    (j : SpeciesLabel (boundaryMultiplicity a b c d)) :
    xsToDiagonalLabel a b c d i = Sum.inr j ↔
      i = liftXSPassiveLabel a b c d j := by
  constructor
  · intro h
    have hi : i ≠ newXSLabelX a b c d := by
      intro hi
      subst i
      simp at h
    have heq : (xsResidualEquiv a b c d) ⟨i, hi⟩ =
        (xsResidualEquiv a b c d)
          ⟨liftXSPassiveLabel a b c d j,
            liftXSPassiveLabel_ne_newXSLabelX a b c d j⟩ :=
      h.trans (xsToDiagonalLabel_passive a b c d j).symm
    exact congrArg Subtype.val ((xsResidualEquiv a b c d).injective heq)
  · rintro rfl
    exact xsToDiagonalLabel_passive a b c d j

@[simp]
theorem mapDomain_xsToDiagonalLabel_apply_collision (a b c d : ℕ)
    (e : XSLabel a b c d →₀ ℕ) :
    Finsupp.mapDomain (xsToDiagonalLabel a b c d) e
        (Sum.inl () : BoundaryDiagonalLabel a b c d) =
      e (newXSLabelX a b c d) + e (newXSLabelS a b c d) := by
  classical
  induction e using Finsupp.induction with
  | zero => simp
  | single_add i n e hi hn ih =>
      rw [Finsupp.mapDomain_add, Finsupp.add_apply, Finsupp.add_apply,
        Finsupp.add_apply, ih, Finsupp.mapDomain_single]
      by_cases hiX : i = newXSLabelX a b c d
      · subst i
        simp [newXSLabelS_ne_newXSLabelX]
        omega
      · by_cases hiS : i = newXSLabelS a b c d
        · subst i
          simp [newXSLabelS_ne_newXSLabelX]
          omega
        · have hdiag : xsToDiagonalLabel a b c d i ≠ Sum.inl () := by
            simpa [xsToDiagonalLabel_eq_collision_iff] using not_or_intro hiX hiS
          simp [hiX, hiS, hdiag]

@[simp]
theorem mapDomain_xsToDiagonalLabel_apply_passive (a b c d : ℕ)
    (e : XSLabel a b c d →₀ ℕ)
    (j : SpeciesLabel (boundaryMultiplicity a b c d)) :
    Finsupp.mapDomain (xsToDiagonalLabel a b c d) e (Sum.inr j) =
      e (liftXSPassiveLabel a b c d j) := by
  classical
  induction e using Finsupp.induction with
  | zero => simp
  | single_add i n e hi hn ih =>
      rw [Finsupp.mapDomain_add, Finsupp.add_apply, Finsupp.add_apply,
        ih, Finsupp.mapDomain_single]
      by_cases hij : i = liftXSPassiveLabel a b c d j
      · subst i
        simp
      · have hdiag : xsToDiagonalLabel a b c d i ≠ Sum.inr j := by
          simpa [xsToDiagonalLabel_eq_passive_iff] using hij
        simp [hij, hdiag]

theorem mapDomain_xsToDiagonalLabel_eq_iff (a b c d q : ℕ)
    (e : XSLabel a b c d →₀ ℕ)
    (v : SpeciesLabel (boundaryMultiplicity a b c d) →₀ ℕ) :
    Finsupp.mapDomain (xsToDiagonalLabel a b c d) e =
        Finsupp.single (Sum.inl () : BoundaryDiagonalLabel a b c d) q +
          Finsupp.mapDomain Sum.inr v ↔
      e (newXSLabelX a b c d) + e (newXSLabelS a b c d) = q ∧
        ∀ j, e (liftXSPassiveLabel a b c d j) = v j := by
  constructor
  · intro h
    constructor
    · have hc := congrArg
          (fun w : BoundaryDiagonalLabel a b c d →₀ ℕ => w (Sum.inl ())) h
      have hzero : Finsupp.mapDomain Sum.inr v
          (Sum.inl () : BoundaryDiagonalLabel a b c d) = 0 :=
        Finsupp.mapDomain_notin_range v _ (by simp)
      simpa [hzero] using hc
    · intro j
      have hp := congrArg
        (fun w : BoundaryDiagonalLabel a b c d →₀ ℕ => w (Sum.inr j)) h
      change Finsupp.mapDomain (xsToDiagonalLabel a b c d) e (Sum.inr j) =
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

def xsModeTupleEquiv (jetOrder a b c d : ℕ) :
    MultispeciesModeTuple jetOrder (boundaryMultiplicity (a + 1) b c (d + 1)) ≃
      (Fin (jetOrder + 1) × Fin (jetOrder + 1)) ×
        MultispeciesModeTuple jetOrder (boundaryMultiplicity a b c d) where
  toFun r :=
    ((r .X (0 : Fin (a + 1)), r .S (0 : Fin (d + 1))), fun A =>
      match A with
      | .X => fun i => r .X i.succ
      | .Y => fun i => r .Y i
      | .Z => fun i => r .Z i
      | .S => fun i => r .S i.succ)
  invFun z := fun A =>
    match A with
    | .X => Fin.cons z.1.1 (z.2 .X)
    | .Y => z.2 .Y
    | .Z => z.2 .Z
    | .S => Fin.cons z.1.2 (z.2 .S)
  left_inv r := by
    funext A i
    cases A
    · refine Fin.cases ?_ (fun j => ?_) i <;> rfl
    · rfl
    · rfl
    · refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  right_inv z := by
    rcases z with ⟨⟨rx, rs⟩, t⟩
    apply Prod.ext
    · rfl
    · funext A i
      cases A <;> rfl

@[simp]
theorem shiftedExponent_xsModeTupleEquiv_symm_activeX
    {jetOrder a b c d : ℕ} (rs : Fin (jetOrder + 1) × Fin (jetOrder + 1))
    (t : MultispeciesModeTuple jetOrder (boundaryMultiplicity a b c d)) :
    shiftedMultispeciesLabelledExponent boundarySpeciesShift
        ((xsModeTupleEquiv jetOrder a b c d).symm (rs, t))
        (newXSLabelX a b c d) = rs.1 := by
  simp [shiftedMultispeciesLabelledExponent, speciesShiftExponent,
    multispeciesLabelledExponent, xsModeTupleEquiv, newXSLabelX,
    boundarySpeciesShift]

@[simp]
theorem shiftedExponent_xsModeTupleEquiv_symm_activeS
    {jetOrder a b c d : ℕ} (rs : Fin (jetOrder + 1) × Fin (jetOrder + 1))
    (t : MultispeciesModeTuple jetOrder (boundaryMultiplicity a b c d)) :
    shiftedMultispeciesLabelledExponent boundarySpeciesShift
        ((xsModeTupleEquiv jetOrder a b c d).symm (rs, t))
        (newXSLabelS a b c d) = (rs.2 : ℕ) + 1 := by
  simp [shiftedMultispeciesLabelledExponent, speciesShiftExponent,
    multispeciesLabelledExponent, xsModeTupleEquiv, newXSLabelS,
    boundarySpeciesShift, add_comm]

@[simp]
theorem shiftedExponent_xsModeTupleEquiv_symm_passive
    {jetOrder a b c d : ℕ} (rs : Fin (jetOrder + 1) × Fin (jetOrder + 1))
    (t : MultispeciesModeTuple jetOrder (boundaryMultiplicity a b c d))
    (j : SpeciesLabel (boundaryMultiplicity a b c d)) :
    shiftedMultispeciesLabelledExponent boundarySpeciesShift
        ((xsModeTupleEquiv jetOrder a b c d).symm (rs, t))
        (liftXSPassiveLabel a b c d j) =
      shiftedMultispeciesLabelledExponent boundarySpeciesShift t j := by
  rcases j with ⟨A, j⟩
  have htuple := (xsModeTupleEquiv jetOrder a b c d).apply_symm_apply (rs, t)
  have hmode := congrArg
    (fun z : (Fin (jetOrder + 1) × Fin (jetOrder + 1)) ×
        MultispeciesModeTuple jetOrder (boundaryMultiplicity a b c d) => z.2 A j) htuple
  cases A <;>
    simpa [shiftedMultispeciesLabelledExponent, speciesShiftExponent,
      multispeciesLabelledExponent, xsModeTupleEquiv, liftXSPassiveLabel,
      boundarySpeciesShift] using congrArg Fin.val hmode

@[simp]
theorem multispeciesUnordered_xsModeTupleEquiv_symm
    {jetOrder a b c d : ℕ} (rs : Fin (jetOrder + 1) × Fin (jetOrder + 1))
    (t : MultispeciesModeTuple jetOrder (boundaryMultiplicity a b c d)) :
    multispeciesUnorderedModeBlock
        ((xsModeTupleEquiv jetOrder a b c d).symm (rs, t)) =
      boundaryModeConfiguration
        (rs.1 ::ₛ unorderedModeBlock (t .X))
        (unorderedModeBlock (t .Y))
        (unorderedModeBlock (t .Z))
        (rs.2 ::ₛ unorderedModeBlock (t .S)) := by
  funext A
  cases A
  · exact unorderedModeBlock_fin_cons rs.1 (t .X)
  · rfl
  · rfl
  · exact unorderedModeBlock_fin_cons rs.2 (t .S)

theorem xsModeTuple_passiveExponent_eq_iff
    {jetOrder a b c d : ℕ} (rs : Fin (jetOrder + 1) × Fin (jetOrder + 1))
    (t t₀ : MultispeciesModeTuple jetOrder (boundaryMultiplicity a b c d)) :
    (∀ j,
        shiftedMultispeciesLabelledExponent boundarySpeciesShift
            ((xsModeTupleEquiv jetOrder a b c d).symm (rs, t))
            (liftXSPassiveLabel a b c d j) =
          shiftedMultispeciesLabelledExponent boundarySpeciesShift t₀ j) ↔
      t = t₀ := by
  simp only [shiftedExponent_xsModeTupleEquiv_symm_passive]
  constructor
  · intro h
    apply shiftedMultispeciesLabelledExponent_injective boundarySpeciesShift
    ext j
    exact h j
  · rintro rfl
    simp

theorem coeff_xsDiagonalSubstitution_eq_fiberSum
    {jetOrder a b c d q : ℕ}
    (F : MultispeciesJetParticleSpace K jetOrder
      (boundaryMultiplicity (a + 1) b c (d + 1)))
    (v : SpeciesLabel (boundaryMultiplicity a b c d) →₀ ℕ) :
    MvPolynomial.coeff
        (Finsupp.single (Sum.inl () : BoundaryDiagonalLabel a b c d) q +
          Finsupp.mapDomain Sum.inr v)
        (xsDiagonalSubstitution (K := K) a b c d
          (shiftedMultispeciesParticlePolynomial boundarySpeciesShift F)) =
      ∑ r : MultispeciesModeTuple jetOrder
          (boundaryMultiplicity (a + 1) b c (d + 1)),
        if
          (shiftedMultispeciesLabelledExponent boundarySpeciesShift r)
              (newXSLabelX a b c d) +
                (shiftedMultispeciesLabelledExponent boundarySpeciesShift r)
                  (newXSLabelS a b c d) = q ∧
            ∀ j,
              (shiftedMultispeciesLabelledExponent boundarySpeciesShift r)
                  (liftXSPassiveLabel a b c d j) = v j
        then F (multispeciesUnorderedModeBlock r) else 0 := by
  classical
  simp only [xsDiagonalSubstitution, shiftedMultispeciesParticlePolynomial, map_sum,
    MvPolynomial.coeff_sum, MvPolynomial.rename_monomial, MvPolynomial.coeff_monomial]
  apply Finset.sum_congr (by ext; simp)
  intro r _
  simp only [mapDomain_xsToDiagonalLabel_eq_iff]

theorem coeff_xsDiagonalSubstitution_tupleExponent
    {jetOrder a b c d : ℕ} (q : ℕ)
    (t₀ : MultispeciesModeTuple jetOrder (boundaryMultiplicity a b c d))
    (F : MultispeciesJetParticleSpace K jetOrder
      (boundaryMultiplicity (a + 1) b c (d + 1))) :
    MvPolynomial.coeff (boundaryDiagonalTupleExponent q t₀)
        (xsDiagonalSubstitution (K := K) a b c d
          (shiftedMultispeciesParticlePolynomial boundarySpeciesShift F)) =
      shiftedASDiagonalCoefficient q (unorderedModeBlock (t₀ .X))
        (unorderedModeBlock (t₀ .S))
        (fun z => F (boundaryModeConfiguration z.1
          (unorderedModeBlock (t₀ .Y))
          (unorderedModeBlock (t₀ .Z)) z.2)) := by
  classical
  rw [show boundaryDiagonalTupleExponent q t₀ =
      Finsupp.single (Sum.inl () : BoundaryDiagonalLabel a b c d) q +
        Finsupp.mapDomain Sum.inr
          (shiftedMultispeciesLabelledExponent boundarySpeciesShift t₀) from rfl]
  rw [coeff_xsDiagonalSubstitution_eq_fiberSum]
  let H := fun r : MultispeciesModeTuple jetOrder
      (boundaryMultiplicity (a + 1) b c (d + 1)) =>
    if
      (shiftedMultispeciesLabelledExponent boundarySpeciesShift r)
          (newXSLabelX a b c d) +
            (shiftedMultispeciesLabelledExponent boundarySpeciesShift r)
              (newXSLabelS a b c d) = q ∧
        ∀ j,
          (shiftedMultispeciesLabelledExponent boundarySpeciesShift r)
              (liftXSPassiveLabel a b c d j) =
            shiftedMultispeciesLabelledExponent boundarySpeciesShift t₀ j
    then F (multispeciesUnorderedModeBlock r) else 0
  change (∑ r, H r) = _
  rw [shiftedASDiagonalCoefficient]
  calc
    (∑ r, H r) =
        ∑ z : (Fin (jetOrder + 1) × Fin (jetOrder + 1)) ×
            MultispeciesModeTuple jetOrder (boundaryMultiplicity a b c d),
          H ((xsModeTupleEquiv jetOrder a b c d).symm z) := by
      exact (Equiv.sum_comp (xsModeTupleEquiv jetOrder a b c d).symm H).symm
    _ = ∑ rs : Fin (jetOrder + 1) × Fin (jetOrder + 1),
          if (rs.1 : ℕ) + 1 + (rs.2 : ℕ) = q then
            F (boundaryModeConfiguration
              (rs.1 ::ₛ unorderedModeBlock (t₀ .X))
              (unorderedModeBlock (t₀ .Y))
              (unorderedModeBlock (t₀ .Z))
              (rs.2 ::ₛ unorderedModeBlock (t₀ .S)))
          else 0 := by
      rw [Fintype.sum_prod_type]
      apply Fintype.sum_congr
      intro rs
      by_cases hrs : (rs.1 : ℕ) + 1 + (rs.2 : ℕ) = q
      · have hrs' : (rs.1 : ℕ) + ((rs.2 : ℕ) + 1) = q := by omega
        simp only [H, shiftedExponent_xsModeTupleEquiv_symm_activeX,
          shiftedExponent_xsModeTupleEquiv_symm_activeS, hrs',
          true_and, xsModeTuple_passiveExponent_eq_iff, if_true]
        rw [Fintype.sum_ite_eq' t₀]
        rw [multispeciesUnordered_xsModeTupleEquiv_symm]
        simp [hrs]
        rfl
      · have hrs' : ¬((rs.1 : ℕ) + ((rs.2 : ℕ) + 1) = q) := by omega
        simp only [H, shiftedExponent_xsModeTupleEquiv_symm_activeX,
          shiftedExponent_xsModeTupleEquiv_symm_activeS, hrs', false_and, if_false]
        simp [hrs]
    _ = ∑ rs ∈ shiftedASCoefficientPairs jetOrder q,
          F (boundaryModeConfiguration
            (rs.1 ::ₛ unorderedModeBlock (t₀ .X))
            (unorderedModeBlock (t₀ .Y))
            (unorderedModeBlock (t₀ .Z))
            (rs.2 ::ₛ unorderedModeBlock (t₀ .S))) := by
      rw [shiftedASCoefficientPairs, Finset.sum_filter]

def sliceXSAtYZ {jetOrder a b c d : ℕ}
    (F : MultispeciesJetParticleSpace K jetOrder
      (boundaryMultiplicity (a + 1) b c (d + 1)))
    (byy : ModeConfiguration jetOrder b)
    (bz : ModeConfiguration jetOrder c) :
    TwoSpeciesParticleSpace K jetOrder (a + 1) (d + 1) :=
  fun z => F (boundaryModeConfiguration z.1 byy bz z.2)

def IsBoundaryXSOrthogonal {jetOrder a b c d : ℕ}
    (F : MultispeciesJetParticleSpace K jetOrder
      (boundaryMultiplicity (a + 1) b c (d + 1))) : Prop :=
  ∀ byy bz,
    AnnihilatesSpan (twoSpeciesPairingFunctional (sliceXSAtYZ F byy bz))
      (shiftedASRelationSet (K := K) jetOrder a d)

theorem boundaryXSOrthogonal_xsDiagonalSubstitution_eq_zero
    {jetOrder a b c d : ℕ}
    (F : MultispeciesJetParticleSpace K jetOrder
      (boundaryMultiplicity (a + 1) b c (d + 1)))
    (hF : IsBoundaryXSOrthogonal F) :
    xsDiagonalSubstitution (K := K) a b c d
        (shiftedMultispeciesParticlePolynomial boundarySpeciesShift F) = 0 := by
  apply MvPolynomial.ext
  intro target
  by_cases hcoeff : MvPolynomial.coeff target
      (xsDiagonalSubstitution (K := K) a b c d
        (shiftedMultispeciesParticlePolynomial boundarySpeciesShift F)) ≠ 0
  · classical
    simp only [xsDiagonalSubstitution, shiftedMultispeciesParticlePolynomial, map_sum,
      MvPolynomial.coeff_sum, MvPolynomial.rename_monomial,
      MvPolynomial.coeff_monomial] at hcoeff
    obtain ⟨r, _, hr⟩ := Finset.exists_ne_zero_of_sum_ne_zero hcoeff
    split at hr
    · rename_i hmap
      let z := xsModeTupleEquiv jetOrder a b c d r
      let q : ℕ :=
        ((shiftedMultispeciesLabelledExponent boundarySpeciesShift r)
          (newXSLabelX a b c d)) +
        ((shiftedMultispeciesLabelledExponent boundarySpeciesShift r)
          (newXSLabelS a b c d))
      have htarget : target = boundaryDiagonalTupleExponent q z.2 := by
        rw [← hmap]
        apply (mapDomain_xsToDiagonalLabel_eq_iff a b c d q _ _).2
        constructor
        · rfl
        · intro j
          have hrz : r = (xsModeTupleEquiv jetOrder a b c d).symm z :=
            (xsModeTupleEquiv jetOrder a b c d).symm_apply_apply r |>.symm
          rw [hrz]
          exact shiftedExponent_xsModeTupleEquiv_symm_passive z.1 z.2 j
      rw [htarget, coeff_xsDiagonalSubstitution_tupleExponent]
      exact (shiftedAS_span_orthogonal_iff_diagonal
        (sliceXSAtYZ F
          (unorderedModeBlock (z.2 .Y))
          (unorderedModeBlock (z.2 .Z)))).1
        (hF _ _) q (unorderedModeBlock (z.2 .X))
          (unorderedModeBlock (z.2 .S))
    · simp at hr
  · simpa [not_ne_iff.mp hcoeff]

theorem xsToDiagonalLabel_eq_residual_collisionIndex (a b c d : ℕ)
    (i : XSLabel a b c d) :
    xsToDiagonalLabel a b c d i =
      xsResidualEquiv a b c d
        (collisionIndex (newXSLabelX a b c d) (newXSLabelS a b c d)
          (newXSLabelS_ne_newXSLabelX a b c d) i) := by
  rcases i with ⟨A, i⟩
  cases A
  · refine Fin.cases ?_ (fun _ => ?_) i <;> rfl
  · rfl
  · rfl
  · refine Fin.cases ?_ (fun _ => ?_) i <;> rfl

theorem xsDiagonalSubstitution_eq_rename_collisionMap (a b c d : ℕ)
    (p : MvPolynomial (XSLabel a b c d) K) :
    xsDiagonalSubstitution (K := K) a b c d p =
      MvPolynomial.rename (xsResidualEquiv a b c d)
        (collisionMap (K := K) (newXSLabelX a b c d) (newXSLabelS a b c d)
          (newXSLabelS_ne_newXSLabelX a b c d) p) := by
  suffices hhom :
      xsDiagonalSubstitution (K := K) a b c d =
        (MvPolynomial.rename (xsResidualEquiv a b c d)).comp
          (collisionMap (K := K) (newXSLabelX a b c d) (newXSLabelS a b c d)
            (newXSLabelS_ne_newXSLabelX a b c d)) by
    exact DFunLike.congr_fun hhom p
  apply MvPolynomial.algHom_ext
  intro i
  simp only [xsDiagonalSubstitution, collisionMap, AlgHom.comp_apply,
    MvPolynomial.rename_X]
  rw [xsToDiagonalLabel_eq_residual_collisionIndex]

theorem boundaryXSOrthogonal_all_literal_collisions
    {jetOrder a b c d : ℕ}
    (F : MultispeciesJetParticleSpace K jetOrder
      (boundaryMultiplicity (a + 1) b c (d + 1)))
    (hF : IsBoundaryXSOrthogonal F) :
    ∀ i : Fin (a + 1), ∀ s : Fin (d + 1),
      ∀ his : boundarySpeciesLabel (a + 1) b c (d + 1) .X i ≠
        boundarySpeciesLabel (a + 1) b c (d + 1) .S s,
      collisionMap (K := K) (boundarySpeciesLabel (a + 1) b c (d + 1) .S s)
        (boundarySpeciesLabel (a + 1) b c (d + 1) .X i) his
        (shiftedMultispeciesParticlePolynomial boundarySpeciesShift F) = 0 := by
  let p := shiftedMultispeciesParticlePolynomial boundarySpeciesShift F
  have htyped := boundaryXSOrthogonal_xsDiagonalSubstitution_eq_zero F hF
  rw [xsDiagonalSubstitution_eq_rename_collisionMap] at htyped
  have hactiveZero : collisionMap (K := K) (newXSLabelX a b c d)
      (newXSLabelS a b c d) (newXSLabelS_ne_newXSLabelX a b c d) p = 0 := by
    apply MvPolynomial.rename_injective (xsResidualEquiv a b c d)
      (xsResidualEquiv a b c d).injective
    simpa only [map_zero] using htyped
  have hactive : collisionFactor (K := K) (newXSLabelX a b c d)
      (newXSLabelS a b c d) ∣ p :=
    (collisionFactor_dvd_iff _ _ (newXSLabelS_ne_newXSLabelX a b c d) p).2
      hactiveZero
  intro i s his
  have hmoveX := collisionFactor_dvd_of_rename_invariant
    (speciesLabelEquiv
      (boundarySpeciesTransposition (boundaryMultiplicity (a + 1) b c (d + 1))
        .X (0 : Fin (a + 1)) i)) p
    (shiftedMultispeciesParticlePolynomial_rename boundarySpeciesShift
      (boundarySpeciesTransposition (boundaryMultiplicity (a + 1) b c (d + 1))
        .X (0 : Fin (a + 1)) i) F)
    hactive
  have hmoveS := collisionFactor_dvd_of_rename_invariant
    (speciesLabelEquiv
      (boundarySpeciesTransposition (boundaryMultiplicity (a + 1) b c (d + 1))
        .S (0 : Fin (d + 1)) s)) p
    (shiftedMultispeciesParticlePolynomial_rename boundarySpeciesShift
      (boundarySpeciesTransposition (boundaryMultiplicity (a + 1) b c (d + 1))
        .S (0 : Fin (d + 1)) s) F)
    hmoveX
  apply (collisionFactor_dvd_iff _ _ his p).1
  apply reverse_collisionFactor_dvd
  simpa [speciesLabelEquiv_boundarySpeciesTransposition,
    newXSLabelX, newXSLabelS, boundarySpeciesLabel] using hmoveS

end XS

section CurrentAxisTransport

/-- Relabel the `X`-axis model as the `Y`-axis model. -/
def xyLabelEquiv (a b c d : ℕ) :
    SpeciesLabel (boundaryMultiplicity (b + 1) a c (d + 1)) ≃
      SpeciesLabel (boundaryMultiplicity a (b + 1) c (d + 1)) where
  toFun i := match i with
    | ⟨.X, j⟩ => ⟨.Y, j⟩
    | ⟨.Y, j⟩ => ⟨.X, j⟩
    | ⟨.Z, j⟩ => ⟨.Z, j⟩
    | ⟨.S, j⟩ => ⟨.S, j⟩
  invFun i := match i with
    | ⟨.X, j⟩ => ⟨.Y, j⟩
    | ⟨.Y, j⟩ => ⟨.X, j⟩
    | ⟨.Z, j⟩ => ⟨.Z, j⟩
    | ⟨.S, j⟩ => ⟨.S, j⟩
  left_inv i := by rcases i with ⟨A, i⟩; cases A <;> rfl
  right_inv i := by rcases i with ⟨A, i⟩; cases A <;> rfl

def xyModeTupleEquiv (jetOrder a b c d : ℕ) :
    MultispeciesModeTuple jetOrder (boundaryMultiplicity (b + 1) a c (d + 1)) ≃
      MultispeciesModeTuple jetOrder (boundaryMultiplicity a (b + 1) c (d + 1)) where
  toFun r A := match A with
    | .X => r .Y
    | .Y => r .X
    | .Z => r .Z
    | .S => r .S
  invFun r A := match A with
    | .X => r .Y
    | .Y => r .X
    | .Z => r .Z
    | .S => r .S
  left_inv r := by funext A i; cases A <;> rfl
  right_inv r := by funext A i; cases A <;> rfl

def xyModeConfiguration (jetOrder a b c d : ℕ)
    (q : MultispeciesModeConfiguration jetOrder
      (boundaryMultiplicity (b + 1) a c (d + 1))) :
    MultispeciesModeConfiguration jetOrder
      (boundaryMultiplicity a (b + 1) c (d + 1))
  | .X => q .Y
  | .Y => q .X
  | .Z => q .Z
  | .S => q .S

@[simp]
theorem mapDomain_xyLabelEquiv_shiftedExponent
    {jetOrder a b c d : ℕ}
    (r : MultispeciesModeTuple jetOrder
      (boundaryMultiplicity (b + 1) a c (d + 1))) :
    Finsupp.mapDomain (xyLabelEquiv a b c d)
        (shiftedMultispeciesLabelledExponent boundarySpeciesShift r) =
      shiftedMultispeciesLabelledExponent boundarySpeciesShift
        (xyModeTupleEquiv jetOrder a b c d r) := by
  rw [← Finsupp.equivMapDomain_eq_mapDomain]
  ext i
  rcases i with ⟨A, i⟩
  cases A <;>
    simp [Finsupp.equivMapDomain_apply, xyLabelEquiv, xyModeTupleEquiv,
      shiftedMultispeciesLabelledExponent, speciesShiftExponent,
      multispeciesLabelledExponent, boundarySpeciesShift]

@[simp]
theorem multispeciesUnordered_xyModeTupleEquiv
    {jetOrder a b c d : ℕ}
    (r : MultispeciesModeTuple jetOrder
      (boundaryMultiplicity (b + 1) a c (d + 1))) :
    multispeciesUnorderedModeBlock (xyModeTupleEquiv jetOrder a b c d r) =
      xyModeConfiguration jetOrder a b c d (multispeciesUnorderedModeBlock r) := by
  funext A
  cases A <;> rfl

def transportXYCoefficient {jetOrder a b c d : ℕ}
    (F : MultispeciesJetParticleSpace K jetOrder
      (boundaryMultiplicity a (b + 1) c (d + 1))) :
    MultispeciesJetParticleSpace K jetOrder
      (boundaryMultiplicity (b + 1) a c (d + 1)) :=
  fun q => F (xyModeConfiguration jetOrder a b c d q)

/-- Swapping the two unshifted current axes commutes exactly with the shifted particle-polynomial
realization. -/
theorem rename_shiftedParticlePolynomial_transportXY
    {jetOrder a b c d : ℕ}
    (F : MultispeciesJetParticleSpace K jetOrder
      (boundaryMultiplicity a (b + 1) c (d + 1))) :
    MvPolynomial.rename (xyLabelEquiv a b c d)
        (shiftedMultispeciesParticlePolynomial boundarySpeciesShift
          (transportXYCoefficient F)) =
      shiftedMultispeciesParticlePolynomial boundarySpeciesShift F := by
  classical
  letI : DecidableEq BoundarySpecies :=
    VOA.MultispeciesParticlePolynomial.instDecidableEq_vOA
  rw [shiftedMultispeciesParticlePolynomial,
    shiftedMultispeciesParticlePolynomial, map_sum]
  simp_rw [MvPolynomial.rename_monomial,
    mapDomain_xyLabelEquiv_shiftedExponent]
  calc
    (∑ r, MvPolynomial.monomial
        (shiftedMultispeciesLabelledExponent boundarySpeciesShift
          (xyModeTupleEquiv jetOrder a b c d r))
        (transportXYCoefficient F (multispeciesUnorderedModeBlock r))) =
      ∑ r, MvPolynomial.monomial
        (shiftedMultispeciesLabelledExponent boundarySpeciesShift
          (xyModeTupleEquiv jetOrder a b c d r))
        (F (multispeciesUnorderedModeBlock
          (xyModeTupleEquiv jetOrder a b c d r))) := by
      apply Finset.sum_congr rfl
      intro r _
      rw [multispeciesUnordered_xyModeTupleEquiv]
      rfl
    _ = ∑ r, MvPolynomial.monomial
        (shiftedMultispeciesLabelledExponent boundarySpeciesShift r)
        (F (multispeciesUnorderedModeBlock r)) :=
      Equiv.sum_comp (xyModeTupleEquiv jetOrder a b c d)
        (fun r => MvPolynomial.monomial
          (shiftedMultispeciesLabelledExponent boundarySpeciesShift r)
          (F (multispeciesUnorderedModeBlock r)))

/-- Orthogonality to `Y(z)S(z)` is the transported two-species relation-span orthogonality;
the `X` and `Z` species remain arbitrary passive spectators. -/
def IsBoundaryYSOrthogonal {jetOrder a b c d : ℕ}
    (F : MultispeciesJetParticleSpace K jetOrder
      (boundaryMultiplicity a (b + 1) c (d + 1))) : Prop :=
  IsBoundaryXSOrthogonal (transportXYCoefficient F)

theorem boundaryYSOrthogonal_all_literal_collisions
    {jetOrder a b c d : ℕ}
    (F : MultispeciesJetParticleSpace K jetOrder
      (boundaryMultiplicity a (b + 1) c (d + 1)))
    (hF : IsBoundaryYSOrthogonal F) :
    ∀ i : Fin (b + 1), ∀ s : Fin (d + 1),
      ∀ his : boundarySpeciesLabel a (b + 1) c (d + 1) .Y i ≠
        boundarySpeciesLabel a (b + 1) c (d + 1) .S s,
      collisionMap (K := K) (boundarySpeciesLabel a (b + 1) c (d + 1) .S s)
        (boundarySpeciesLabel a (b + 1) c (d + 1) .Y i) his
        (shiftedMultispeciesParticlePolynomial boundarySpeciesShift F) = 0 := by
  intro i s his
  let G := transportXYCoefficient F
  have hzero := boundaryXSOrthogonal_all_literal_collisions G hF i s (by
    exact boundarySpeciesLabel_disjoint (b + 1) a c (d + 1)
      (by decide : BoundarySpecies.X ≠ BoundarySpecies.S) i s)
  have hdvd : collisionFactor (K := K)
      (boundarySpeciesLabel (b + 1) a c (d + 1) .S s)
      (boundarySpeciesLabel (b + 1) a c (d + 1) .X i) ∣
      shiftedMultispeciesParticlePolynomial boundarySpeciesShift G :=
    (collisionFactor_dvd_iff _ _
      (boundarySpeciesLabel_disjoint (b + 1) a c (d + 1)
        (by decide : BoundarySpecies.X ≠ BoundarySpecies.S) i s) _).2 hzero
  have hmapped := map_dvd (MvPolynomial.rename (xyLabelEquiv a b c d)) hdvd
  rw [rename_shiftedParticlePolynomial_transportXY] at hmapped
  apply (collisionFactor_dvd_iff _ _ his _).1
  simpa [collisionFactor, boundarySpeciesLabel, xyLabelEquiv] using hmapped

/-- Relabel the `X`-axis model as the `Z`-axis model. -/
def xzAxisLabelEquiv (a b c d : ℕ) :
    SpeciesLabel (boundaryMultiplicity (c + 1) b a (d + 1)) ≃
      SpeciesLabel (boundaryMultiplicity a b (c + 1) (d + 1)) where
  toFun i := match i with
    | ⟨.X, j⟩ => ⟨.Z, j⟩
    | ⟨.Y, j⟩ => ⟨.Y, j⟩
    | ⟨.Z, j⟩ => ⟨.X, j⟩
    | ⟨.S, j⟩ => ⟨.S, j⟩
  invFun i := match i with
    | ⟨.X, j⟩ => ⟨.Z, j⟩
    | ⟨.Y, j⟩ => ⟨.Y, j⟩
    | ⟨.Z, j⟩ => ⟨.X, j⟩
    | ⟨.S, j⟩ => ⟨.S, j⟩
  left_inv i := by rcases i with ⟨A, i⟩; cases A <;> rfl
  right_inv i := by rcases i with ⟨A, i⟩; cases A <;> rfl

def xzAxisModeTupleEquiv (jetOrder a b c d : ℕ) :
    MultispeciesModeTuple jetOrder (boundaryMultiplicity (c + 1) b a (d + 1)) ≃
      MultispeciesModeTuple jetOrder (boundaryMultiplicity a b (c + 1) (d + 1)) where
  toFun r A := match A with
    | .X => r .Z
    | .Y => r .Y
    | .Z => r .X
    | .S => r .S
  invFun r A := match A with
    | .X => r .Z
    | .Y => r .Y
    | .Z => r .X
    | .S => r .S
  left_inv r := by funext A i; cases A <;> rfl
  right_inv r := by funext A i; cases A <;> rfl

def xzAxisModeConfiguration (jetOrder a b c d : ℕ)
    (q : MultispeciesModeConfiguration jetOrder
      (boundaryMultiplicity (c + 1) b a (d + 1))) :
    MultispeciesModeConfiguration jetOrder
      (boundaryMultiplicity a b (c + 1) (d + 1))
  | .X => q .Z
  | .Y => q .Y
  | .Z => q .X
  | .S => q .S

@[simp]
theorem mapDomain_xzAxisLabelEquiv_shiftedExponent
    {jetOrder a b c d : ℕ}
    (r : MultispeciesModeTuple jetOrder
      (boundaryMultiplicity (c + 1) b a (d + 1))) :
    Finsupp.mapDomain (xzAxisLabelEquiv a b c d)
        (shiftedMultispeciesLabelledExponent boundarySpeciesShift r) =
      shiftedMultispeciesLabelledExponent boundarySpeciesShift
        (xzAxisModeTupleEquiv jetOrder a b c d r) := by
  rw [← Finsupp.equivMapDomain_eq_mapDomain]
  ext i
  rcases i with ⟨A, i⟩
  cases A <;>
    simp [Finsupp.equivMapDomain_apply, xzAxisLabelEquiv, xzAxisModeTupleEquiv,
      shiftedMultispeciesLabelledExponent, speciesShiftExponent,
      multispeciesLabelledExponent, boundarySpeciesShift]

@[simp]
theorem multispeciesUnordered_xzAxisModeTupleEquiv
    {jetOrder a b c d : ℕ}
    (r : MultispeciesModeTuple jetOrder
      (boundaryMultiplicity (c + 1) b a (d + 1))) :
    multispeciesUnorderedModeBlock (xzAxisModeTupleEquiv jetOrder a b c d r) =
      xzAxisModeConfiguration jetOrder a b c d (multispeciesUnorderedModeBlock r) := by
  funext A
  cases A <;> rfl

def transportXZAxisCoefficient {jetOrder a b c d : ℕ}
    (F : MultispeciesJetParticleSpace K jetOrder
      (boundaryMultiplicity a b (c + 1) (d + 1))) :
    MultispeciesJetParticleSpace K jetOrder
      (boundaryMultiplicity (c + 1) b a (d + 1)) :=
  fun q => F (xzAxisModeConfiguration jetOrder a b c d q)

theorem rename_shiftedParticlePolynomial_transportXZAxis
    {jetOrder a b c d : ℕ}
    (F : MultispeciesJetParticleSpace K jetOrder
      (boundaryMultiplicity a b (c + 1) (d + 1))) :
    MvPolynomial.rename (xzAxisLabelEquiv a b c d)
        (shiftedMultispeciesParticlePolynomial boundarySpeciesShift
          (transportXZAxisCoefficient F)) =
      shiftedMultispeciesParticlePolynomial boundarySpeciesShift F := by
  classical
  letI : DecidableEq BoundarySpecies :=
    VOA.MultispeciesParticlePolynomial.instDecidableEq_vOA
  rw [shiftedMultispeciesParticlePolynomial,
    shiftedMultispeciesParticlePolynomial, map_sum]
  simp_rw [MvPolynomial.rename_monomial,
    mapDomain_xzAxisLabelEquiv_shiftedExponent]
  calc
    (∑ r, MvPolynomial.monomial
        (shiftedMultispeciesLabelledExponent boundarySpeciesShift
          (xzAxisModeTupleEquiv jetOrder a b c d r))
        (transportXZAxisCoefficient F (multispeciesUnorderedModeBlock r))) =
      ∑ r, MvPolynomial.monomial
        (shiftedMultispeciesLabelledExponent boundarySpeciesShift
          (xzAxisModeTupleEquiv jetOrder a b c d r))
        (F (multispeciesUnorderedModeBlock
          (xzAxisModeTupleEquiv jetOrder a b c d r))) := by
      apply Finset.sum_congr rfl
      intro r _
      rw [multispeciesUnordered_xzAxisModeTupleEquiv]
      rfl
    _ = ∑ r, MvPolynomial.monomial
        (shiftedMultispeciesLabelledExponent boundarySpeciesShift r)
        (F (multispeciesUnorderedModeBlock r)) :=
      Equiv.sum_comp (xzAxisModeTupleEquiv jetOrder a b c d)
        (fun r => MvPolynomial.monomial
          (shiftedMultispeciesLabelledExponent boundarySpeciesShift r)
          (F (multispeciesUnorderedModeBlock r)))

/-- Orthogonality to `Z(z)S(z)`, transported to the common current-axis model. -/
def IsBoundaryZSOrthogonal {jetOrder a b c d : ℕ}
    (F : MultispeciesJetParticleSpace K jetOrder
      (boundaryMultiplicity a b (c + 1) (d + 1))) : Prop :=
  IsBoundaryXSOrthogonal (transportXZAxisCoefficient F)

theorem boundaryZSOrthogonal_all_literal_collisions
    {jetOrder a b c d : ℕ}
    (F : MultispeciesJetParticleSpace K jetOrder
      (boundaryMultiplicity a b (c + 1) (d + 1)))
    (hF : IsBoundaryZSOrthogonal F) :
    ∀ i : Fin (c + 1), ∀ s : Fin (d + 1),
      ∀ his : boundarySpeciesLabel a b (c + 1) (d + 1) .Z i ≠
        boundarySpeciesLabel a b (c + 1) (d + 1) .S s,
      collisionMap (K := K) (boundarySpeciesLabel a b (c + 1) (d + 1) .S s)
        (boundarySpeciesLabel a b (c + 1) (d + 1) .Z i) his
        (shiftedMultispeciesParticlePolynomial boundarySpeciesShift F) = 0 := by
  intro i s his
  let G := transportXZAxisCoefficient F
  have hzero := boundaryXSOrthogonal_all_literal_collisions G hF i s (by
    exact boundarySpeciesLabel_disjoint (c + 1) b a (d + 1)
      (by decide : BoundarySpecies.X ≠ BoundarySpecies.S) i s)
  have hdvd : collisionFactor (K := K)
      (boundarySpeciesLabel (c + 1) b a (d + 1) .S s)
      (boundarySpeciesLabel (c + 1) b a (d + 1) .X i) ∣
      shiftedMultispeciesParticlePolynomial boundarySpeciesShift G :=
    (collisionFactor_dvd_iff _ _
      (boundarySpeciesLabel_disjoint (c + 1) b a (d + 1)
        (by decide : BoundarySpecies.X ≠ BoundarySpecies.S) i s) _).2 hzero
  have hmapped := map_dvd (MvPolynomial.rename (xzAxisLabelEquiv a b c d)) hdvd
  rw [rename_shiftedParticlePolynomial_transportXZAxis] at hmapped
  apply (collisionFactor_dvd_iff _ _ his _).1
  simpa [collisionFactor, boundarySpeciesLabel, xzAxisLabelEquiv] using hmapped

end CurrentAxisTransport

end ShiftedCurrentS

section PositiveSectorAssembly

/-- In sectors with fewer than two `S` particles there is no `S`--`S` pair; otherwise require
the shifted `S^2` relation-span orthogonality with the uniquely determined spectator count. -/
def HasBoundaryS2Orthogonality {jetOrder a b c d : ℕ}
    (F : MultispeciesJetParticleSpace K jetOrder (boundaryMultiplicity a b c d)) : Prop :=
  match d, F with
  | 0, _ => True
  | 1, _ => True
  | Nat.succ (Nat.succ d), F => IsBoundaryS2Orthogonal F

/-- If either species is absent the `X`--`S` collision family is vacuous; otherwise require the
transported `XS` relation-span orthogonality. -/
def HasBoundaryXSOrthogonality {jetOrder a b c d : ℕ}
    (F : MultispeciesJetParticleSpace K jetOrder (boundaryMultiplicity a b c d)) : Prop :=
  match a, d, F with
  | Nat.succ a, Nat.succ d, F => IsBoundaryXSOrthogonal F
  | _, _, _ => True

def HasBoundaryYSOrthogonality {jetOrder a b c d : ℕ}
    (F : MultispeciesJetParticleSpace K jetOrder (boundaryMultiplicity a b c d)) : Prop :=
  match b, d, F with
  | Nat.succ b, Nat.succ d, F => IsBoundaryYSOrthogonal F
  | _, _, _ => True

def HasBoundaryZSOrthogonality {jetOrder a b c d : ℕ}
    (F : MultispeciesJetParticleSpace K jetOrder (boundaryMultiplicity a b c d)) : Prop :=
  match c, d, F with
  | Nat.succ c, Nat.succ d, F => IsBoundaryZSOrthogonal F
  | _, _, _ => True

theorem hasBoundaryS2Orthogonality_all_literal_collisions [CharZero K]
    {jetOrder a b c d : ℕ}
    (F : MultispeciesJetParticleSpace K jetOrder (boundaryMultiplicity a b c d))
    (hF : HasBoundaryS2Orthogonality F) :
    ∀ i j : Fin d, ∀ hji : boundarySpeciesLabel a b c d .S j ≠
        boundarySpeciesLabel a b c d .S i,
      collisionMap (K := K) (boundarySpeciesLabel a b c d .S i)
        (boundarySpeciesLabel a b c d .S j) hji
        (shiftedMultispeciesParticlePolynomial boundarySpeciesShift F) = 0 := by
  cases d with
  | zero => intro i; exact Fin.elim0 i
  | succ d =>
      cases d with
      | zero =>
          intro i j hji
          have hi : i = 0 := Fin.eq_zero i
          have hj : j = 0 := Fin.eq_zero j
          subst i
          subst j
          exact False.elim (hji rfl)
      | succ d =>
          exact boundaryS2Orthogonal_all_literal_collisions F
            (by simpa [HasBoundaryS2Orthogonality] using hF)

theorem hasBoundaryXSOrthogonality_all_literal_collisions
    {jetOrder a b c d : ℕ}
    (F : MultispeciesJetParticleSpace K jetOrder (boundaryMultiplicity a b c d))
    (hF : HasBoundaryXSOrthogonality F) :
    ∀ i : Fin a, ∀ s : Fin d,
      ∀ his : boundarySpeciesLabel a b c d .X i ≠ boundarySpeciesLabel a b c d .S s,
      collisionMap (K := K) (boundarySpeciesLabel a b c d .S s)
        (boundarySpeciesLabel a b c d .X i) his
        (shiftedMultispeciesParticlePolynomial boundarySpeciesShift F) = 0 := by
  cases a with
  | zero => intro i; exact Fin.elim0 i
  | succ a =>
      cases d with
      | zero => intro i s; exact Fin.elim0 s
      | succ d =>
          exact boundaryXSOrthogonal_all_literal_collisions F
            (by simpa [HasBoundaryXSOrthogonality] using hF)

theorem hasBoundaryYSOrthogonality_all_literal_collisions
    {jetOrder a b c d : ℕ}
    (F : MultispeciesJetParticleSpace K jetOrder (boundaryMultiplicity a b c d))
    (hF : HasBoundaryYSOrthogonality F) :
    ∀ i : Fin b, ∀ s : Fin d,
      ∀ his : boundarySpeciesLabel a b c d .Y i ≠ boundarySpeciesLabel a b c d .S s,
      collisionMap (K := K) (boundarySpeciesLabel a b c d .S s)
        (boundarySpeciesLabel a b c d .Y i) his
        (shiftedMultispeciesParticlePolynomial boundarySpeciesShift F) = 0 := by
  cases b with
  | zero => intro i; exact Fin.elim0 i
  | succ b =>
      cases d with
      | zero => intro i s; exact Fin.elim0 s
      | succ d =>
          exact boundaryYSOrthogonal_all_literal_collisions F
            (by simpa [HasBoundaryYSOrthogonality] using hF)

theorem hasBoundaryZSOrthogonality_all_literal_collisions
    {jetOrder a b c d : ℕ}
    (F : MultispeciesJetParticleSpace K jetOrder (boundaryMultiplicity a b c d))
    (hF : HasBoundaryZSOrthogonality F) :
    ∀ i : Fin c, ∀ s : Fin d,
      ∀ his : boundarySpeciesLabel a b c d .Z i ≠ boundarySpeciesLabel a b c d .S s,
      collisionMap (K := K) (boundarySpeciesLabel a b c d .S s)
        (boundarySpeciesLabel a b c d .Z i) his
        (shiftedMultispeciesParticlePolynomial boundarySpeciesShift F) = 0 := by
  cases c with
  | zero => intro i; exact Fin.elim0 i
  | succ c =>
      cases d with
      | zero => intro i s; exact Fin.elim0 s
      | succ d =>
          exact boundaryZSOrthogonal_all_literal_collisions F
            (by simpa [HasBoundaryZSOrthogonality] using hF)

/-- Full sector-level conductor theorem, including zero current multiplicities and the vacuous
`d=0,1` same-`S` cases. -/
theorem p3CommonFactor_dvd_of_auxiliaryOrthogonal [CharZero K]
    {jetOrder a b c d : ℕ}
    (F : MultispeciesJetParticleSpace K jetOrder (boundaryMultiplicity a b c d))
    (hSS : HasBoundaryS2Orthogonality F)
    (hXS : HasBoundaryXSOrthogonality F)
    (hYS : HasBoundaryYSOrthogonality F)
    (hZS : HasBoundaryZSOrthogonality F) :
    p3CommonFactor (K := K) a b c d ∣
      shiftedMultispeciesParticlePolynomial boundarySpeciesShift F := by
  apply p3CommonFactor_dvd F
  · simpa [boundarySLabel, boundarySpeciesLabel] using
      hasBoundaryS2Orthogonality_all_literal_collisions F hSS
  · intro i s his
    rcases i with ((i | i) | i)
    · simpa [boundaryCurrentLabel, boundarySLabel, boundarySpeciesLabel] using
        hasBoundaryXSOrthogonality_all_literal_collisions F hXS i s his
    · simpa [boundaryCurrentLabel, boundarySLabel, boundarySpeciesLabel] using
        hasBoundaryYSOrthogonality_all_literal_collisions F hYS i s his
    · simpa [boundaryCurrentLabel, boundarySLabel, boundarySpeciesLabel] using
        hasBoundaryZSOrthogonality_all_literal_collisions F hZS i s his

/-- In a sector with at least one particle of each current species and at least two `S`
particles, the four separate auxiliary orthogonality conditions supply exactly the literal
collision hypotheses of `p3CommonFactor_dvd`.  This is the conductor assembly; it makes no
claim about the remaining polarized-cone carrier. -/
theorem p3CommonFactor_dvd_of_auxiliaryOrthogonal_positive [CharZero K]
    {jetOrder a b c d : ℕ}
    (F : MultispeciesJetParticleSpace K jetOrder
      (boundaryMultiplicity (a + 1) (b + 1) (c + 1) (d + 2)))
    (hSS : IsBoundaryS2Orthogonal F)
    (hXS : IsBoundaryXSOrthogonal F)
    (hYS : IsBoundaryYSOrthogonal F)
    (hZS : IsBoundaryZSOrthogonal F) :
    p3CommonFactor (K := K) (a + 1) (b + 1) (c + 1) (d + 2) ∣
      shiftedMultispeciesParticlePolynomial boundarySpeciesShift F := by
  apply p3CommonFactor_dvd F
  · intro i j hji
    simpa [boundarySLabel, boundarySpeciesLabel] using
      boundaryS2Orthogonal_all_literal_collisions F hSS i j hji
  · intro i s his
    rcases i with ((i | i) | i)
    · simpa [boundaryCurrentLabel, boundarySLabel, boundarySpeciesLabel] using
        boundaryXSOrthogonal_all_literal_collisions F hXS i s his
    · simpa [boundaryCurrentLabel, boundarySLabel, boundarySpeciesLabel] using
        boundaryYSOrthogonal_all_literal_collisions F hYS i s his
    · simpa [boundaryCurrentLabel, boundarySLabel, boundarySpeciesLabel] using
        boundaryZSOrthogonal_all_literal_collisions F hZS i s his

end PositiveSectorAssembly

end

end VOA.P3AuxiliaryCollisionBridge
