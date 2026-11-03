/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.A2CarrierEmbedding

/-!
# The carrier character input reduces to an upper bound

`OrdinaryCarrierCharacter W Carrier` asks for the *equality*
`∑_{p ≤ N} dim Carrier p N = dim V_N`.  Given current-jet surjectivity and a geometric carrier
embedding, one inequality is automatic:

  `dim V_N = ∑_p dim gr^Li_p V_N ≤ ∑_p dim (Jet-bidegree image) ≤ ∑_p dim Carrier p N`.

So only the upper bound `∑_p dim Carrier p N ≤ dim V_N` is a genuine input
(`ordinaryCarrierCharacter_of_le`).  For the literal quadratic carrier of
`A2CarrierEmbedding` this upper bound is exactly the coefficientwise statement
`Hilb Jet R̃ ≤ ch V` of the Deligne chain; it is recorded as the named hypothesis structure
`QuadraticCarrierUpperBound`, never as an axiom.

The paper proves it via the auxiliary (Casimir) filtration (U3), the carrier identity
(U4 global Weyl modules, U5 fusion upper bound, codimension-one descent), the resummation (U6) and
the character identity `(⋆)`.  None of those is formalized here.
-/

namespace VOA.DeligneAudit.CarrierEmbedding

open VOA.FiniteJet VOA.QuadraticJetCoefficientPairing
open VOA.DeligneHigherRankConditionalCapstone
open VertexOperatorAlgebra

noncomputable section

universe uC

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
variable {case : HigherRankDeligneCase} {W : VertexOperatorAlgebra V}

/-- **Automatic lower bound.**  Surjectivity plus the carrier embedding give
`dim V_N ≤ ∑_p dim Carrier p N` in every conformal weight. -/
theorem finrank_grading_le_carrier (P : CurrentC2Presentation case W)
    (Carrier : ℕ → ℕ → Type uC)
    [∀ p N, AddCommGroup (Carrier p N)]
    [∀ p N, Module ℂ (Carrier p N)]
    [∀ p N, FiniteDimensional ℂ (Carrier p N)]
    (hsurj : CurrentJetSurjectivity case W P)
    (hgeom : GeometricCarrierEmbedding case W P Carrier) (N : ℕ) :
    Module.finrank ℂ (W.grading N) ≤
      ∑ p ∈ Finset.range (N + 1), Module.finrank ℂ (Carrier p N) := by
  rw [← sum_liWeightLayer_finrank_eq_grading W N]
  apply Finset.sum_le_sum
  intro p _
  letI : FiniteDimensional ℂ (PresentedJetLiBidegreeImage
      (fun _ : Fin case.currentDimension => 1) p p N P.ideal) :=
    finiteDimensional_presentedJetLiBidegreeImage (fun _ => 1) (fun _ => Nat.one_pos) p p N _
  letI : FiniteDimensional ℂ (liWeightLayer W p N) :=
    liAssociatedGraded_component_finiteDimensional W p N
  calc Module.finrank ℂ (liWeightLayer W p N)
      ≤ Module.finrank ℂ (PresentedJetLiBidegreeImage
          (fun _ : Fin case.currentDimension => 1) p p N P.ideal) :=
        LinearMap.finrank_le_finrank_of_surjective (hsurj.bidegree p N)
    _ = Module.finrank ℂ (Module.Dual ℂ (PresentedJetLiBidegreeImage
          (fun _ : Fin case.currentDimension => 1) p p N P.ideal)) :=
        Subspace.dual_finrank_eq.symm
    _ ≤ Module.finrank ℂ (Carrier p N) :=
        LinearMap.finrank_le_finrank_of_injective (hgeom.injective p N)

/-- **The character input is only an upper bound.** -/
theorem ordinaryCarrierCharacter_of_le (P : CurrentC2Presentation case W)
    (Carrier : ℕ → ℕ → Type uC)
    [∀ p N, AddCommGroup (Carrier p N)]
    [∀ p N, Module ℂ (Carrier p N)]
    [∀ p N, FiniteDimensional ℂ (Carrier p N)]
    (hsurj : CurrentJetSurjectivity case W P)
    (hgeom : GeometricCarrierEmbedding case W P Carrier)
    (hle : ∀ N, (∑ p ∈ Finset.range (N + 1), Module.finrank ℂ (Carrier p N)) ≤
      Module.finrank ℂ (W.grading N)) :
    OrdinaryCarrierCharacter W Carrier := fun N =>
  le_antisymm (hle N) (finrank_grading_le_carrier P Carrier hsurj hgeom N)

/-- **Capstone with a one-sided character input.** -/
theorem caseClassicallyFree_of_carrier_le (P : CurrentC2Presentation case W)
    (Carrier : ℕ → ℕ → Type uC)
    [∀ p N, AddCommGroup (Carrier p N)]
    [∀ p N, Module ℂ (Carrier p N)]
    [∀ p N, FiniteDimensional ℂ (Carrier p N)]
    (hsurj : CurrentJetSurjectivity case W P)
    (hgeom : GeometricCarrierEmbedding case W P Carrier)
    (hle : ∀ N, (∑ p ∈ Finset.range (N + 1), Module.finrank ℂ (Carrier p N)) ≤
      Module.finrank ℂ (W.grading N)) :
    CaseClassicallyFree case W P ∧
      RingHom.ker
          (MvPolynomial.aeval fun i =>
            liDegreeZeroClass W 1 ⟨P.gen i, P.gen_weight_one i⟩).toRingHom =
        P.ideal :=
  caseClassicallyFree_of_explicit_inputs case W P Carrier hsurj hgeom
    (ordinaryCarrierCharacter_of_le P Carrier hsurj hgeom hle)

/-- **Named residual: the quadratic carrier upper bound.**  For the literal current carrier of the
coefficient family `Q`, the ordinary character is bounded by the VOA character.  For a Deligne
presentation this is the paper's `Hilb Jet R̃ ≤ ch V` (chain steps U3–U6 and `(⋆)`). -/
structure QuadraticCarrierUpperBound {ρ : Type} {n : ℕ} (Q : ρ → Fin n × Fin n → ℂ)
    (W : VertexOperatorAlgebra V) : Prop where
  le : ∀ N, (∑ p ∈ Finset.range (N + 1), Module.finrank ℂ (Carrier Q p N)) ≤
    Module.finrank ℂ (W.grading N)

/-- The named residual in presented-jet form: it is the same statement with the carrier replaced by
the presented jet bidegree image of `quadraticIdeal Q`. -/
theorem quadraticCarrierUpperBound_iff {ρ : Type} {n : ℕ} (Q : ρ → Fin n × Fin n → ℂ)
    (W : VertexOperatorAlgebra V) :
    QuadraticCarrierUpperBound Q W ↔
      ∀ N, (∑ p ∈ Finset.range (N + 1), Module.finrank ℂ
        (PresentedJetLiBidegreeImage (R := ℂ) (fun _ : Fin n => 1) p p N (quadraticIdeal Q))) ≤
        Module.finrank ℂ (W.grading N) := by
  have hsum : ∀ N, (∑ p ∈ Finset.range (N + 1), Module.finrank ℂ (Carrier Q p N)) =
      ∑ p ∈ Finset.range (N + 1), Module.finrank ℂ
        (PresentedJetLiBidegreeImage (R := ℂ) (fun _ : Fin n => 1) p p N (quadraticIdeal Q)) :=
    fun N => Finset.sum_congr rfl fun p hp =>
      finrank_carrier_eq Q (Nat.lt_succ_iff.mp (Finset.mem_range.mp hp))
  constructor
  · intro h N
    rw [← hsum N]
    exact h.le N
  · intro h
    exact ⟨fun N => (hsum N).symm ▸ h N⟩

/-- **Quadratic Deligne capstone.**  For a presentation whose ideal is `quadraticIdeal Q`, classical
freeness (and exactness of the presentation) follows from current-jet surjectivity and the single
named residual `QuadraticCarrierUpperBound Q W`.  The geometric carrier embedding is discharged. -/
theorem caseClassicallyFree_of_quadraticCarrierUpperBound {ρ : Type}
    (P : CurrentC2Presentation case W)
    (Q : ρ → Fin case.currentDimension × Fin case.currentDimension → ℂ)
    (hQ : P.ideal = quadraticIdeal Q)
    (hsurj : CurrentJetSurjectivity case W P)
    (hbound : QuadraticCarrierUpperBound Q W) :
    CaseClassicallyFree case W P ∧
      RingHom.ker
          (MvPolynomial.aeval fun i =>
            liDegreeZeroClass W 1 ⟨P.gen i, P.gen_weight_one i⟩).toRingHom =
        P.ideal :=
  caseClassicallyFree_of_carrier_le P (Carrier Q) hsurj
    (geometricCarrierEmbedding_of_quadraticIdeal P Q hQ) hbound.le

/-- The same, for an ideal given as the span of homogeneous quadratics (the form of
`A2.I2ns`). -/
theorem caseClassicallyFree_of_span_upperBound {ρ : Type}
    (P : CurrentC2Presentation case W)
    (rel : ρ → MvPolynomial (Fin case.currentDimension) ℂ)
    (hrel : ∀ r, (rel r).IsHomogeneous 2)
    (hP : P.ideal = Ideal.span (Set.range rel))
    (hsurj : CurrentJetSurjectivity case W P)
    (hbound : QuadraticCarrierUpperBound (quadraticCoefficients rel hrel) W) :
    CaseClassicallyFree case W P ∧
      RingHom.ker
          (MvPolynomial.aeval fun i =>
            liDegreeZeroClass W 1 ⟨P.gen i, P.gen_weight_one i⟩).toRingHom =
        P.ideal :=
  caseClassicallyFree_of_quadraticCarrierUpperBound P _
    (hP.trans (span_homogeneousQuadratic_eq_quadraticIdeal rel hrel)) hsurj hbound

end

end VOA.DeligneAudit.CarrierEmbedding

section AxiomAudit
open VOA.DeligneAudit.CarrierEmbedding
#print axioms finrank_grading_le_carrier
#print axioms ordinaryCarrierCharacter_of_le
#print axioms caseClassicallyFree_of_carrier_le
#print axioms quadraticCarrierUpperBound_iff
#print axioms caseClassicallyFree_of_quadraticCarrierUpperBound
#print axioms caseClassicallyFree_of_span_upperBound
end AxiomAudit
