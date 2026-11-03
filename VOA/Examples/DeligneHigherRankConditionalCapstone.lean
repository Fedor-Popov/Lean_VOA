/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Examples.DeligneWeightwiseHilbertCapstone
import VOA.DeligneAudit.C2PresentationOfFreeness

/-!
# Conditional classical freeness for the higher-rank Deligne series

The repository constructs genuine affine VOAs in types `A₁` and `A₂`
(`AffineSl3.simpleVOA`; the A₂ case is instantiated in `DeligneAudit.A2Instance`, and its
`CurrentJetSurjectivity` package is discharged in `DeligneAudit.A2CurrentJetSurjectivity`).
This file states the strongest uniform conditional theorem for an abstract VOA carrying the
currents.  (The universal affine VOA for a general simple Lie algebra is
`AffineGeneral.universalAffineVOA`, with simple quotient `AffineGeneral.simpleVOA`;
every case is instantiated on it in `AffineGeneral/DeligneInstance.lean`.)

The seven cases are named and their current dimensions, dual Coxeter numbers,
and Deligne levels are recorded explicitly.  For a VOA carrying the correct
number of weight-one currents, the hypotheses are split into four mathematical
packages:

1. a displayed ideal of relations that vanish in the `C₂` algebra (containment
   only; exactness of the presentation is a *conclusion*, see
   `CurrentC2Presentation.exact_kernel_of_caseClassicallyFree`);
2. surjectivity of the finite bidegree and infinite current-jet maps;
3. an injective restricted-dual map into a concrete geometric carrier in every
   Li/conformal bidegree;
4. equality of the carrier's ordinary conformal-weight character with the VOA
   character.

The geometric hypothesis is the literal family of linear maps and their
injectivity.  It is not hidden behind a proposition called a literature input.
The conclusion is presentation-level classical freeness for the displayed
ideal.  Injectivity of the jet map forces the ideal to be the full kernel, so
the source is the jet algebra of the actual `C₂` algebra and no exact-kernel
input is needed.
-/

namespace VOA.DeligneHigherRankConditionalCapstone

open VertexOperatorAlgebra

noncomputable section

universe uV uC

/-- The seven Deligne cases other than `A₁`. -/
inductive HigherRankDeligneCase
  | A2
  | G2
  | D4
  | F4
  | E6
  | E7
  | E8
  deriving DecidableEq, Fintype

@[simp] theorem card_higherRankDeligneCase :
    Fintype.card HigherRankDeligneCase = 7 := rfl

namespace HigherRankDeligneCase

/-- Dimension of the finite-dimensional simple Lie algebra, hence the number
of weight-one affine currents. -/
def currentDimension : HigherRankDeligneCase → ℕ
  | A2 => 8
  | G2 => 14
  | D4 => 28
  | F4 => 52
  | E6 => 78
  | E7 => 133
  | E8 => 248

/-- Dual Coxeter number in the long-root-square-two normalization. -/
def dualCoxeterNumber : HigherRankDeligneCase → ℕ
  | A2 => 3
  | G2 => 4
  | D4 => 6
  | F4 => 9
  | E6 => 12
  | E7 => 18
  | E8 => 30

/-- The negative affine level in the Deligne series. -/
def level : HigherRankDeligneCase → ℚ
  | A2 => -3 / 2
  | G2 => -5 / 3
  | D4 => -2
  | F4 => -5 / 2
  | E6 => -3
  | E7 => -4
  | E8 => -6

@[simp] theorem currentDimension_A2 : currentDimension A2 = 8 := rfl
@[simp] theorem currentDimension_G2 : currentDimension G2 = 14 := rfl
@[simp] theorem currentDimension_D4 : currentDimension D4 = 28 := rfl
@[simp] theorem currentDimension_F4 : currentDimension F4 = 52 := rfl
@[simp] theorem currentDimension_E6 : currentDimension E6 = 78 := rfl
@[simp] theorem currentDimension_E7 : currentDimension E7 = 133 := rfl
@[simp] theorem currentDimension_E8 : currentDimension E8 = 248 := rfl

@[simp] theorem dualCoxeterNumber_A2 : dualCoxeterNumber A2 = 3 := rfl
@[simp] theorem dualCoxeterNumber_G2 : dualCoxeterNumber G2 = 4 := rfl
@[simp] theorem dualCoxeterNumber_D4 : dualCoxeterNumber D4 = 6 := rfl
@[simp] theorem dualCoxeterNumber_F4 : dualCoxeterNumber F4 = 9 := rfl
@[simp] theorem dualCoxeterNumber_E6 : dualCoxeterNumber E6 = 12 := rfl
@[simp] theorem dualCoxeterNumber_E7 : dualCoxeterNumber E7 = 18 := rfl
@[simp] theorem dualCoxeterNumber_E8 : dualCoxeterNumber E8 = 30 := rfl

@[simp] theorem level_A2 : level A2 = (-3 / 2 : ℚ) := rfl
@[simp] theorem level_G2 : level G2 = (-5 / 3 : ℚ) := rfl
@[simp] theorem level_D4 : level D4 = (-2 : ℚ) := rfl
@[simp] theorem level_F4 : level F4 = (-5 / 2 : ℚ) := rfl
@[simp] theorem level_E6 : level E6 = (-3 : ℚ) := rfl
@[simp] theorem level_E7 : level E7 = (-4 : ℚ) := rfl
@[simp] theorem level_E8 : level E8 = (-6 : ℚ) := rfl

/-- Uniform Deligne-level formula `k = -(h∨ + 6) / 6`. -/
theorem level_eq_neg_dualCoxeter_add_six_div_six
    (case : HigherRankDeligneCase) :
    level case = -((dualCoxeterNumber case : ℚ) + 6) / 6 := by
  cases case <;> norm_num [level, dualCoxeterNumber]

end HigherRankDeligneCase

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (case : HigherRankDeligneCase) (W : VertexOperatorAlgebra V)

/-- Current-coordinate relations for the `C₂` algebra.

Only containment in the kernel is assumed.  This does not let a theorem about
an arbitrary smaller ideal pass as classical freeness of the true `C₂` algebra:
classical freeness gives injectivity of the presented jet map, which forces
the ideal to equal the kernel
(`CurrentC2Presentation.exact_kernel_of_caseClassicallyFree`). -/
structure CurrentC2Presentation where
  /-- The weight-one currents, indexed by a basis of the simple Lie algebra. -/
  gen : Fin case.currentDimension → V
  /-- Every displayed current has conformal weight one. -/
  gen_weight_one : ∀ i, gen i ∈ W.grading (1 : ℤ)
  /-- The proposed defining ideal in current coordinates. -/
  ideal : Ideal (MvPolynomial (Fin case.currentDimension) ℂ)
  /-- The proposed relations vanish in Li degree zero. -/
  relations : ideal ≤ RingHom.ker
      (MvPolynomial.aeval fun i =>
        liDegreeZeroClass W 1 ⟨gen i, gen_weight_one i⟩).toRingHom

namespace CurrentC2Presentation

variable {case W}

/-- Relation containment, under the name used by the downstream packages. -/
theorem relations_vanish (P : CurrentC2Presentation case W) :
    P.ideal ≤ RingHom.ker
      (MvPolynomial.aeval fun i =>
        liDegreeZeroClass W 1 ⟨P.gen i, P.gen_weight_one i⟩).toRingHom :=
  P.relations

end CurrentC2Presentation

/-- Current generation at the finite bidegree level and at the full infinite
jet level.  These are stated separately because neither is smuggled into the
geometric carrier comparison. -/
structure CurrentJetSurjectivity (P : CurrentC2Presentation case W) : Prop where
  /-- Every actual Li/conformal bidegree is hit by current jets. -/
  bidegree : ∀ p N, Function.Surjective
    (liPresentedJetBidegreeMap W p
      (fun i => liDegreeZeroClass W 1 ⟨P.gen i, P.gen_weight_one i⟩)
      P.ideal P.relations_vanish (fun _ => 1) p N)
  /-- Every element of the full Li associated graded is hit by a finite current
  polynomial. -/
  infinite : Function.Surjective
    (liInfinitePresentedJetMap W
      (fun i => liDegreeZeroClass W 1 ⟨P.gen i, P.gen_weight_one i⟩)
      P.ideal P.relations_vanish)

/-- A concrete geometric upper-bound carrier.  The required comparison is an
actual injective map from the dual of every presented-jet bidegree; it is the
precise geometric statement that remains to be constructed case by case. -/
structure GeometricCarrierEmbedding
    (P : CurrentC2Presentation case W)
    (Carrier : ℕ → ℕ → Type uC)
    [∀ p N, AddCommGroup (Carrier p N)]
    [∀ p N, Module ℂ (Carrier p N)] where
  /-- Restricted-dual coefficient evaluation in bidegree `(p,N)`. -/
  toCarrier : ∀ p N,
    Module.Dual ℂ
      (FiniteJet.PresentedJetLiBidegreeImage
        (fun _ : Fin case.currentDimension => 1) p p N P.ideal) →ₗ[ℂ]
      Carrier p N
  /-- Coefficients in the geometric carrier separate the presented-jet
  bidegree. -/
  injective : ∀ p N, Function.Injective (toCarrier p N)

/-- The ordinary, unrefined carrier character agrees weight by weight with the
VOA character.  Summing over Li degree is finite because all currents have
weight one. -/
def OrdinaryCarrierCharacter
    (Carrier : ℕ → ℕ → Type uC)
    [∀ p N, AddCommGroup (Carrier p N)]
    [∀ p N, Module ℂ (Carrier p N)]
    [∀ p N, FiniteDimensional ℂ (Carrier p N)] : Prop :=
  ∀ N,
    (∑ p ∈ Finset.range (N + 1), Module.finrank ℂ (Carrier p N)) =
      Module.finrank ℂ (W.grading N)

/-- Presentation-level classical freeness for the exact current `C₂`
presentation carried by `P`. -/
def CaseClassicallyFree (P : CurrentC2Presentation case W) : Prop :=
  LiPresentationClassicallyFree W
    (fun i => liDegreeZeroClass W 1 ⟨P.gen i, P.gen_weight_one i⟩)
    P.ideal P.relations_vanish

/-- **Exact `C₂` presentation from classical freeness.**  The displayed ideal
is the full kernel as soon as the case is classically free. -/
theorem CurrentC2Presentation.exact_kernel_of_caseClassicallyFree
    {P : CurrentC2Presentation case W} (hfree : CaseClassicallyFree case W P) :
    RingHom.ker
        (MvPolynomial.aeval fun i =>
          liDegreeZeroClass W 1 ⟨P.gen i, P.gen_weight_one i⟩).toRingHom =
      P.ideal :=
  ker_eq_of_liPresentationClassicallyFree W _ P.ideal P.relations_vanish hfree

/-- **Conditional higher-rank Deligne theorem.**

For any one of the seven named cases, a current `C₂` presentation (relations
vanishing in `C₂`; containment only), current-jet surjectivity, literal geometric carrier embedding,
and ordinary
character equality imply classical freeness, and hence that the displayed
ideal is the exact `C₂` kernel. -/
theorem caseClassicallyFree_of_explicit_inputs
    (P : CurrentC2Presentation case W)
    (Carrier : ℕ → ℕ → Type uC)
    [∀ p N, AddCommGroup (Carrier p N)]
    [∀ p N, Module ℂ (Carrier p N)]
    [∀ p N, FiniteDimensional ℂ (Carrier p N)]
    (hsurj : CurrentJetSurjectivity case W P)
    (hgeom : GeometricCarrierEmbedding case W P Carrier)
    (hchar : OrdinaryCarrierCharacter W Carrier) :
    CaseClassicallyFree case W P ∧
      RingHom.ker
          (MvPolynomial.aeval fun i =>
            liDegreeZeroClass W 1 ⟨P.gen i, P.gen_weight_one i⟩).toRingHom =
        P.ideal := by
  have hfree : CaseClassicallyFree case W P :=
    DeligneWeightwiseHilbertCapstone.classicallyFree_of_carrier_weightCharacter
      W P.gen P.gen_weight_one P.ideal P.relations_vanish Carrier
      hsurj.bidegree hsurj.infinite hgeom.toCarrier hgeom.injective hchar
  exact ⟨hfree, CurrentC2Presentation.exact_kernel_of_caseClassicallyFree case W hfree⟩

end

end VOA.DeligneHigherRankConditionalCapstone

section AxiomAudit
open VOA.DeligneHigherRankConditionalCapstone
#print axioms CurrentC2Presentation.relations_vanish
#print axioms CurrentC2Presentation.exact_kernel_of_caseClassicallyFree
#print axioms caseClassicallyFree_of_explicit_inputs
end AxiomAudit
