/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modularity.SuperWedderburnTrace
import VOA.Modularity.SuperTwistedTrace
import VOA.Modularity.SuperConformalSign
import VOA.Modules.SuperTwistedZhuFinite
import VOA.Modules.SuperRelativeTwistedZhuBridge

/-!
# Conditional realization of a finite commuting super sector

This file packages, rather than derives, the representation-theoretic data needed to realize the
standard type-M and type-Q functionals of a supplied finite super-Wedderburn product by bottom
spaces of irreducible twisted modules.  The spatial twist and temporal insertion remain the
literal pair `(g,h)`.  The inverse lift of `h` is used, matching the orientation of
`hSupersymmetricFunctionals`.

The type-M functional is the inverse-inserted supertrace.  The type-Q functional descends the
actual represented queer odd trace from `TwistedQueerTraceData`; it is not extended to arbitrary
endomorphisms.  The sign-adjusted Zhu convention is exposed separately through
`SuperAut.twistedZhuSignAdjusted = parityAut * g` and is never silently substituted for `g`.

Nothing here constructs a super-Wedderburn decomposition, twisted modules, centralizer lifts, or
bottom-space realization from strong rationality.  There is no convergence or modularity claim.
-/

namespace VOA

open Module (finrank)
open scoped BigOperators

set_option autoImplicit false

universe u v

variable {VType : Type u} [AddCommGroup VType] [Module ℂ VType]
variable {W : SuperVertexOperatorAlgebra VType}
variable {g h : SuperAut W} {N : ℕ}

/-! ## Irreducible objects in one fixed `(g,h)` sector -/

namespace SuperTwistedModule

variable {M : Type v} [AddCommGroup M] [Module ℂ M]

/-- A subspace split by both carried gradings and stable under every fractional mode. -/
def IsGradedInvariant (T : SuperTwistedModule W g N M) (S : Submodule ℂ M) : Prop :=
  S = ⨆ p : ZMod 2, S ⊓ T.parity p ∧
  S = ⨆ α : ℂ, S ⊓ T.weight α ∧
  ∀ (a : VType) (k : ℤ) (x : M), x ∈ S → T.act a k x ∈ S

/-- Irreducibility among graded invariant subspaces. -/
def IsIrreducible (T : SuperTwistedModule W g N M) : Prop :=
  T.IsGradedInvariant ⊤ ∧
  ∀ S : Submodule ℂ M, T.IsGradedInvariant S → S = ⊥ ∨ S = ⊤

end SuperTwistedModule

/-- An irreducible `g`-twisted module with a chosen homogeneous lift of the commuting temporal
automorphism `h`.  The intertwiner itself contains the exact equation `h * g = g * h`. -/
structure PackagedIrreducibleSuperTwistedModule
    (W : SuperVertexOperatorAlgebra VType) (g h : SuperAut W) (N : ℕ) where
  carrier : Type v
  [addCommGroup : AddCommGroup carrier]
  [module : Module ℂ carrier]
  twistedModule : SuperTwistedModule W g N carrier
  intertwiner : SuperTwistedIntertwiner twistedModule h
  irreducible : twistedModule.IsIrreducible

attribute [instance] PackagedIrreducibleSuperTwistedModule.addCommGroup
  PackagedIrreducibleSuperTwistedModule.module

/-- Equivalence in the fixed `(g,h)` sector.  The lift may be rescaled, as is natural for a
projective centralizer action. -/
structure SuperTwistedModuleEquiv
    (X Y : PackagedIrreducibleSuperTwistedModule.{u, v} W g h N) where
  toLinearEquiv : X.carrier ≃ₗ[ℂ] Y.carrier
  map_parity : ∀ (p : ZMod 2) (x : X.carrier),
    toLinearEquiv x ∈ Y.twistedModule.parity p ↔ x ∈ X.twistedModule.parity p
  map_weight : ∀ (α : ℂ) (x : X.carrier),
    toLinearEquiv x ∈ Y.twistedModule.weight α ↔ x ∈ X.twistedModule.weight α
  intertwines_modes : ∀ (a : VType) (k : ℤ) (x : X.carrier),
    toLinearEquiv (X.twistedModule.act a k x) =
      Y.twistedModule.act a k (toLinearEquiv x)
  intertwines_lift_up_to_scalar : ∃ c : ℂ, c ≠ 0 ∧ ∀ x : X.carrier,
    toLinearEquiv (X.intertwiner x) = c • Y.intertwiner (toLinearEquiv x)

/-! ## An explicit presentation and temporal action on the twisted Zhu algebra -/

variable {A : Type u} [Ring A] [Algebra ℂ A]

/-- A parity-preserving algebra presentation of the actual `g`-twisted Zhu quotient. -/
structure TwistedZhuSuperalgebraPresentation
    (P : AssociativeSuperalgebra A)
    (hW : W.toSuperNearVOA.IntegralWeights)
    (hZ : SuperTwistedZhuRingData W hW g N)
    (hgr : W.TwistedOParityGraded hW g N) where
  toTwistedA : A ≃ₗ[ℂ] W.twistedA hW g N
  map_one : toTwistedA 1 = W.twistedOne hW g N
  map_mul : ∀ a b : A,
    toTwistedA (a * b) = hZ.twistedAmul (toTwistedA a) (toTwistedA b)
  map_parity : ∀ (p : ZMod 2) (a : A),
    a ∈ P.parity p ↔ toTwistedA a ∈ W.twistedAParity hW g N p

/-- The algebra action induced by the literal temporal automorphism `h`. -/
structure TwistedZhuCentralizerAction
    {P : AssociativeSuperalgebra A}
    {hW : W.toSuperNearVOA.IntegralWeights}
    {hZ : SuperTwistedZhuRingData W hW g N}
    {hgr : W.TwistedOParityGraded hW g N}
    (E : TwistedZhuSuperalgebraPresentation P hW hZ hgr) (h : SuperAut W) where
  algAut : A ≃ₐ[ℂ] A
  preservesParity : PreservesSuperParity P algAut
  state_compatibility : ∀ (a : A) (u : VType),
    E.toTwistedA a = W.twistedMk hW g N u →
      E.toTwistedA (algAut a) = W.twistedMk hW g N (h u)

/-! ## Actual bottom-space M/Q functionals -/

namespace PackagedIrreducibleSuperTwistedModule

variable (X : PackagedIrreducibleSuperTwistedModule.{u, v} W g h N)
  (hW : W.toSuperNearVOA.IntegralWeights) (α : ℂ)

/-- Type-M bottom functional: supertrace with the inverse temporal lift. -/
noncomputable def bottomInverseSupertrace
    (hB : SuperTwistedZhuBottomData hW X.twistedModule α) :
    W.twistedA hW g N →ₗ[ℂ] ℂ :=
  (X.twistedModule.inverseInsertedSupertraceLinear X.intertwiner α).comp hB.bottomAction

/-- Type-Q bottom functional.  Faithfulness of the represented queer block makes its state-level
preimage annihilate the twisted Zhu relation space, so the genuine queer odd trace descends. -/
noncomputable def bottomOddTrace
    (hB : SuperTwistedZhuBottomData hW X.twistedModule α)
    (Θ : SuperTwistedModule.TwistedQueerTraceData X.twistedModule X.intertwiner hW) :
    W.twistedA hW g N →ₗ[ℂ] ℂ := by
  have hker : W.twistedO hW g N ≤ LinearMap.ker (Θ.preimage α) := by
    intro u hu
    rw [LinearMap.mem_ker]
    apply (Θ.block α).faithful
    have hzero := hB.O_annihilates hu
    rw [LinearMap.mem_ker] at hzero
    rw [Θ.represents, map_zero, hzero, mul_zero]
  exact Queer.oddTrace.comp
    ((W.twistedO hW g N).liftQ (Θ.preimage α) hker)

end PackagedIrreducibleSuperTwistedModule

/-! ## Conditional finite sector realization -/

section TraceRealization

variable (hW : W.toSuperNearVOA.IntegralWeights)
  (hZ : SuperTwistedZhuRingData W hW g N)
  (hgr : W.TwistedOParityGraded hW g N)
  (P : AssociativeSuperalgebra A)
  (E : TwistedZhuSuperalgebraPresentation P hW hZ hgr)
  (D : FiniteSuperWedderburnDecomposition P)

/-- The smallest operational realization package used below.  Every classification, module,
bottom-space, Type-M/Type-Q, equivariance, and completeness assertion is supplied as data. -/
structure FiniteCompleteSectorTraceRealization where
  centralizerAction : TwistedZhuCentralizerAction E h
  object : Fin D.blockCount → PackagedIrreducibleSuperTwistedModule.{u, v} W g h N
  complete : ∀ X : PackagedIrreducibleSuperTwistedModule.{u, v} W g h N,
    ∃ i, Nonempty (SuperTwistedModuleEquiv X (object i))
  bottomWeight : Fin D.blockCount → ℂ
  bottomData : ∀ i, SuperTwistedZhuBottomData hW (object i).twistedModule (bottomWeight i)
  typeMEven : ∀ i, (D.block i).kind = .typeM → (object i).intertwiner.parityDegree = 0
  typeQData : ∀ i, (D.block i).kind = .typeQ →
    SuperTwistedModule.TwistedQueerTraceData
      (object i).twistedModule (object i).intertwiner hW
  realizedFunctional : Fin D.blockCount → A →ₗ[ℂ] ℂ
  realized_typeM : ∀ i (_hi : (D.block i).kind = .typeM),
    realizedFunctional i =
      ((object i).bottomInverseSupertrace hW (bottomWeight i) (bottomData i)).comp
        E.toTwistedA.toLinearMap
  realized_typeQ : ∀ i (hi : (D.block i).kind = .typeQ),
    realizedFunctional i =
      ((object i).bottomOddTrace hW (bottomWeight i) (bottomData i) (typeQData i hi)).comp
        E.toTwistedA.toLinearMap
  realizes_block : ∀ i, realizedFunctional i = D.blockFunctional i
  realized_hSupersymmetric : ∀ i, realizedFunctional i ∈
    hSupersymmetricFunctionals P centralizerAction.algAut

namespace FiniteCompleteSectorTraceRealization

variable {hW hZ hgr P E D}
  (R : FiniteCompleteSectorTraceRealization.{u, v} (h := h) hW hZ hgr P E D)

/-- The realized bottom-functional family is finite. -/
theorem finite_range_realizedFunctional : (Set.range R.realizedFunctional).Finite :=
  Set.finite_range R.realizedFunctional

/-- Distinct supplied Wedderburn blocks give independent realized M/Q functionals. -/
theorem linearIndependent_realizedFunctional :
    LinearIndependent ℂ R.realizedFunctional := by
  have heq : R.realizedFunctional = D.blockFunctional := by
    funext i
    exact R.realizes_block i
  rw [heq]
  exact D.linearIndependent_blockFunctional

/-- Independence persists after remembering temporal `h`-supersymmetry. -/
theorem linearIndependent_hSupersymmetricSubtype :
    LinearIndependent ℂ (fun i =>
      (⟨R.realizedFunctional i, R.realized_hSupersymmetric i⟩ :
        hSupersymmetricFunctionals P R.centralizerAction.algAut)) := by
  rw [linearIndependent_iff']
  intro s c hc i hi
  apply (linearIndependent_iff'.mp R.linearIndependent_realizedFunctional) s c
  · apply LinearMap.ext
    intro a
    have hca := congrArg
      (fun f : hSupersymmetricFunctionals P R.centralizerAction.algAut =>
        (f : A →ₗ[ℂ] ℂ) a) hc
    simpa using hca
  · exact hi

/-- The exact equivariant dimension input needed to turn independence into spanning. -/
def HFunctionalDimensionBound : Prop :=
  finrank ℂ (hSupersymmetricFunctionals P R.centralizerAction.algAut) ≤ D.blockCount

/-- The supplied decomposition makes the temporal supersymmetric-functional space finite. -/
@[reducible] noncomputable def finiteDimensional_hSupersymmetricFunctionals :
    FiniteDimensional ℂ
      (hSupersymmetricFunctionals P R.centralizerAction.algAut) := by
  letI : FiniteDimensional ℂ A := D.finiteDimensional
  infer_instance

/-- Under the oriented upper bound, independence gives exactly one temporal supersymmetric
functional dimension per realized block. -/
theorem finrank_hSupersymmetricFunctionals_eq_blockCount
    (hbound : HFunctionalDimensionBound (R := R)) :
    finrank ℂ (hSupersymmetricFunctionals P R.centralizerAction.algAut) = D.blockCount := by
  letI : FiniteDimensional ℂ A := D.finiteDimensional
  exact le_antisymm hbound
    (by simpa using R.linearIndependent_hSupersymmetricSubtype.fintype_card_le_finrank)

/-- Under the explicit equivariant dimension bound, the realized M/Q bottom functionals span the
whole temporal supersymmetric-functional space. -/
theorem span_realizedFunctional_eq_hSupersymmetricFunctionals
    (hbound : HFunctionalDimensionBound (R := R)) :
    Submodule.span ℂ (Set.range fun i =>
      (⟨R.realizedFunctional i, R.realized_hSupersymmetric i⟩ :
        hSupersymmetricFunctionals P R.centralizerAction.algAut)) = ⊤ := by
  letI : FiniteDimensional ℂ A := D.finiteDimensional
  let t : Fin D.blockCount →
      hSupersymmetricFunctionals P R.centralizerAction.algAut := fun i =>
    ⟨R.realizedFunctional i, R.realized_hSupersymmetric i⟩
  have hind : LinearIndependent ℂ t := R.linearIndependent_hSupersymmetricSubtype
  have hrank : finrank ℂ (Submodule.span ℂ (Set.range t)) = D.blockCount := by
    simpa using finrank_span_eq_card hind
  apply Submodule.eq_top_of_finrank_eq
  rw [hrank]
  exact le_antisymm (by simpa using hind.fintype_card_le_finrank) hbound

/-- Coefficient form of the conditional finite sector-realization theorem.  The family and all
module data are fixed before the functional `φ` is quantified. -/
theorem exists_eq_sum_hSupersymmetric_realizedFunctional
    (hbound : HFunctionalDimensionBound (R := R))
    (φ : hSupersymmetricFunctionals P R.centralizerAction.algAut) :
    ∃ c : Fin D.blockCount → ℂ,
      (φ : A →ₗ[ℂ] ℂ) = ∑ i, c i • R.realizedFunctional i := by
  have hmem : φ ∈ Submodule.span ℂ (Set.range fun i =>
      (⟨R.realizedFunctional i, R.realized_hSupersymmetric i⟩ :
        hSupersymmetricFunctionals P R.centralizerAction.algAut)) := by
    rw [R.span_realizedFunctional_eq_hSupersymmetricFunctionals hbound]
    trivial
  rw [Submodule.mem_span_range_iff_exists_fun] at hmem
  obtain ⟨c, hc⟩ := hmem
  refine ⟨c, ?_⟩
  apply LinearMap.ext
  intro a
  have hca := congrArg
    (fun f : hSupersymmetricFunctionals P R.centralizerAction.algAut =>
      (f : A →ₗ[ℂ] ℂ) a) hc.symm
  simpa using hca

/-- The same realized block family spans ordinary supersymmetric functionals under the separate
nonequivariant bound supplied by `SuperWedderburnTrace`. -/
theorem exists_eq_sum_supersymmetric_realizedFunctional
    (hbound : D.FunctionalDimensionBound) (φ : supersymmetricFunctionals P) :
    ∃ c : Fin D.blockCount → ℂ,
      (φ : A →ₗ[ℂ] ℂ) = ∑ i, c i • R.realizedFunctional i := by
  obtain ⟨c, hc⟩ := D.exists_eq_sum_blockFunctional hbound φ
  refine ⟨c, ?_⟩
  rw [hc]
  apply Finset.sum_congr rfl
  intro i _
  rw [R.realizes_block]

end FiniteCompleteSectorTraceRealization

end TraceRealization

/-! ## Explicit sign-adjusted convention -/

/-- If `h` commutes with the literal spatial automorphism `g`, then it also commutes with the
separately named sign-adjusted Zhu twist `parityAut * g`. -/
theorem SuperAut.commute_twistedZhuSignAdjusted
    (hcomm : h * g = g * h) :
    h * g.twistedZhuSignAdjusted = g.twistedZhuSignAdjusted * h := by
  rw [SuperAut.twistedZhuSignAdjusted]
  have hpar : h * W.parityAut = W.parityAut * h :=
    (W.parityAut_commute h).eq.symm
  calc
    h * (W.parityAut * g) = (h * W.parityAut) * g := by rw [mul_assoc]
    _ = (W.parityAut * h) * g := by rw [hpar]
    _ = W.parityAut * (h * g) := by rw [mul_assoc]
    _ = W.parityAut * (g * h) := by rw [hcomm]
    _ = (W.parityAut * g) * h := by rw [mul_assoc]

end VOA
