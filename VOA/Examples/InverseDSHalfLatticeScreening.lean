/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Examples.InverseDSSimpleQuotientGate
import VOA.Examples.InverseDSParameters

/-!
# Half-lattice carrier and external screening sector for inverse DS

Adamović--Milas Proposition 2.1 uses `Pi(0)^(1/2)`, not merely the integral charge line
currently used by the concrete inverse-DS exponential fields.  This file introduces the minimal
algebraic half-lattice carrier.  A label `r : HalfEtaCharge` represents charge `(r/2) eta`, so
even labels recover the integral line and label `1` is the new half-charge sector.

No vertex-algebra structure is asserted.  The file records the exact charge decomposition,
momentum and charge shifts, then specializes the external-screening interfaces from
`InverseDSSimpleQuotientGate` to a carrier of the form
`L^Vir(c,h) ⊗ Pi(0)^(1/2)`.  The screening codomain remains an arbitrary shifted module.
-/

namespace VOA
namespace InverseDS
namespace HalfLattice

open Module (End)
open InverseDSPi
open AffineVOA AffineLie Sl2Sing85
open scoped TensorProduct

noncomputable section

universe u v w

/-- A half-lattice charge label.  The represented charge is `label / 2` times `eta`. -/
structure HalfEtaCharge where
  label : ℤ
  deriving DecidableEq

/-- The complex charge represented by a half-lattice label. -/
def HalfEtaCharge.value (q : HalfEtaCharge) : ℂ := (q.label : ℂ) / 2

/-- Label for the integral charge `q eta`. -/
def integralCharge (q : ℤ) : HalfEtaCharge := ⟨2 * q⟩

/-- The distinguished charge `eta/2`. -/
def halfCharge : HalfEtaCharge := ⟨1⟩

@[simp] theorem integralCharge_value (q : ℤ) : (integralCharge q).value = q := by
  simp [integralCharge, HalfEtaCharge.value]

@[simp] theorem halfCharge_value : halfCharge.value = (1 / 2 : ℂ) := by
  simp [halfCharge, HalfEtaCharge.value]

/-- Addition of charge labels. -/
def addCharge (q r : HalfEtaCharge) : HalfEtaCharge := ⟨q.label + r.label⟩

/-- The group-algebra carrier for half-integral multiples of `eta`. -/
abbrev HalfEtaChargeLine := HalfEtaCharge →₀ ℂ

/-- Basis vector of charge `(q.label/2) eta`. -/
def halfEtaChargeBasis (q : HalfEtaCharge) : HalfEtaChargeLine := Finsupp.single q 1

/-- Oscillator Fock space tensored with the half-lattice charge line. -/
abbrev PiHalfFockCarrier := HyperFock ⊗[ℂ] HalfEtaChargeLine

/-- A pure oscillator/half-charge state. -/
def piHalfFockState (p : HyperFock) (q : HalfEtaCharge) : PiHalfFockCarrier :=
  p ⊗ₜ[ℂ] halfEtaChargeBasis q

/-- The half-lattice vacuum carrier state. -/
def piHalfFockVacuum : PiHalfFockCarrier := piHalfFockState hyperVacuum (integralCharge 0)

/-- Exact algebraic direct-sum decomposition by half-lattice charge. -/
def piHalfChargeDecomp : PiHalfFockCarrier ≃ₗ[ℂ] HalfEtaCharge →₀ HyperFock :=
  TensorProduct.finsuppScalarRight ℂ ℂ HyperFock HalfEtaCharge

@[simp] theorem piHalfChargeDecomp_state (p : HyperFock) (q : HalfEtaCharge) :
    piHalfChargeDecomp (piHalfFockState p q) = Finsupp.single q p := by
  apply piHalfChargeDecomp.symm.injective
  rw [LinearEquiv.symm_apply_apply]
  change p ⊗ₜ[ℂ] Finsupp.single q 1 =
    piHalfChargeDecomp.symm (Finsupp.single q p)
  exact (TensorProduct.finsuppScalarRight_symm_apply_single
    (R := ℂ) (S := ℂ) (M := HyperFock) q p).symm

/-- The exact sector of one half-lattice charge. -/
def piHalfChargeSector (q : HalfEtaCharge) : Submodule ℂ PiHalfFockCarrier :=
  (Finsupp.supported HyperFock ℂ {q}).comap piHalfChargeDecomp.toLinearMap

@[simp] theorem piHalfFockState_mem_sector (p : HyperFock) (q : HalfEtaCharge) :
    piHalfFockState p q ∈ piHalfChargeSector q := by
  change piHalfChargeDecomp (piHalfFockState p q) ∈ Finsupp.supported HyperFock ℂ {q}
  rw [piHalfChargeDecomp_state]
  rw [Finsupp.mem_supported]
  intro y hy
  by_contra hyq
  exact (Finsupp.mem_support_iff.mp hy) (Finsupp.single_eq_of_ne hyq)

/-- Momentum on the half-lattice line, with eigenvalue `q.label/2`. -/
def halfEtaChargeMomentum : End ℂ HalfEtaChargeLine :=
  Finsupp.lsum ℂ (fun q : HalfEtaCharge => q.value •
    (Finsupp.lsingle q : ℂ →ₗ[ℂ] HalfEtaChargeLine))

@[simp] theorem halfEtaChargeMomentum_basis (q : HalfEtaCharge) :
    halfEtaChargeMomentum (halfEtaChargeBasis q) =
      q.value • halfEtaChargeBasis q := by
  rw [halfEtaChargeMomentum, halfEtaChargeBasis, Finsupp.lsum_single,
    LinearMap.smul_apply, Finsupp.lsingle_apply]

/-- Translation by a half-lattice charge. -/
def halfEtaShiftLine (q : HalfEtaCharge) : End ℂ HalfEtaChargeLine :=
  Finsupp.lsum ℂ (fun r : HalfEtaCharge =>
    (Finsupp.lsingle (addCharge q r) : ℂ →ₗ[ℂ] HalfEtaChargeLine))

@[simp] theorem halfEtaShiftLine_basis (q r : HalfEtaCharge) :
    halfEtaShiftLine q (halfEtaChargeBasis r) = halfEtaChargeBasis (addCharge q r) := by
  rw [halfEtaShiftLine, halfEtaChargeBasis, Finsupp.lsum_single, Finsupp.lsingle_apply]
  rfl

/-- The half-charge shift on the oscillator/charge carrier. -/
def halfEtaShift (q : HalfEtaCharge) : End ℂ PiHalfFockCarrier :=
  LinearMap.lTensor HyperFock (halfEtaShiftLine q)

@[simp] theorem halfEtaShift_state (q r : HalfEtaCharge) (p : HyperFock) :
    halfEtaShift q (piHalfFockState p r) = piHalfFockState p (addCharge q r) := by
  rw [halfEtaShift, piHalfFockState, LinearMap.lTensor_tmul, halfEtaShiftLine_basis]
  rfl

/-! ## The exact Adamović--Milas sector shape -/

/-- Carrier for the sector `L^Vir(c,h) ⊗ Pi(0)^(1/2)`, before a tensor near-VOA has been
assembled. -/
abbrev VirPiHalfCarrier (VirCarrier : Type u) [AddCommGroup VirCarrier]
    [Module ℂ VirCarrier] := VirCarrier ⊗[ℂ] PiHalfFockCarrier

/-- Proposition 2.1's sector image, with an external screening landing in a shifted module.
The carrier type itself is the specified Virasoro--half-lattice sector, so its sector submodule
is `⊤`; this is not a claim about the kernel in any larger free-field ambient space. -/
def Prop21HalfLatticeSectorImage
    {Source : Type v} [AddCommGroup Source] [Module ℂ Source]
    {VirCarrier : Type u} [AddCommGroup VirCarrier] [Module ℂ VirCarrier]
    {Shifted : Type w} [AddCommGroup Shifted] [Module ℂ Shifted]
    (f : Source →ₗ[ℂ] VirPiHalfCarrier VirCarrier)
    (Q : VirPiHalfCarrier VirCarrier →ₗ[ℂ] Shifted) : Prop :=
  AdamovicMilasProp21SectorImage f ⊤ Q

/-- On the already restricted half-lattice carrier, the sector-image statement is exactly
`range f = ker Q`. -/
theorem prop21HalfLatticeSectorImage_iff
    {Source : Type v} [AddCommGroup Source] [Module ℂ Source]
    {VirCarrier : Type u} [AddCommGroup VirCarrier] [Module ℂ VirCarrier]
    {Shifted : Type w} [AddCommGroup Shifted] [Module ℂ Shifted]
    {f : Source →ₗ[ℂ] VirPiHalfCarrier VirCarrier}
    {Q : VirPiHalfCarrier VirCarrier →ₗ[ℂ] Shifted} :
    Prop21HalfLatticeSectorImage f Q ↔ LinearMap.range f = LinearMap.ker Q := by
  simp [Prop21HalfLatticeSectorImage, AdamovicMilasProp21SectorImage]

/-- An endomorphism of the half-lattice Pi carrier shifts charge by `eta/2`.  The actual
Adamović--Milas screening has a more refined momentum `nu`; this predicate records exactly the
half-charge information visible on the present one-dimensional charge carrier. -/
def ShiftsByHalfEta (Q : End ℂ PiHalfFockCarrier) : Prop :=
  ∀ p q, Q (piHalfFockState p q) ∈ piHalfChargeSector (addCharge halfCharge q)

/-- Full Proposition 2.1 package specialized to the already restricted carrier
`L^Vir(c,h) ⊗ Pi(0)^(1/2)`.  The screening is external and may land in an unrelated shifted
module; `ambientProd` and `shiftedAction` remain explicit because the current carrier files do
not yet assemble either module into a near-VOA. -/
def Prop21HalfLatticeIdentification
    {Source : Type v} [AddCommGroup Source] [Module ℂ Source]
    {VirCarrier : Type u} [AddCommGroup VirCarrier] [Module ℂ VirCarrier]
    {Shifted : Type w} [AddCommGroup Shifted] [Module ℂ Shifted]
    (V : VertexOperatorAlgebra Source)
    (ambientVacuum : VirPiHalfCarrier VirCarrier)
    (ambientProd : VirPiHalfCarrier VirCarrier → ℤ →
      VirPiHalfCarrier VirCarrier → VirPiHalfCarrier VirCarrier)
    (f : Source →ₗ[ℂ] VirPiHalfCarrier VirCarrier)
    (hf : VacuumModeHom V ambientVacuum ambientProd f)
    (Q : VirPiHalfCarrier VirCarrier →ₗ[ℂ] Shifted)
    (shiftedAction : VirPiHalfCarrier VirCarrier → ℤ → Shifted → Shifted) : Prop :=
  AdamovicMilasProp21VacuumIdentification hf ⊤ Q shiftedAction

/-- The specialized half-lattice package identifies the kernel of the universal affine map
with the source maximal ideal. -/
theorem ker_eq_maxGradedIdeal_of_prop21HalfLattice
    {Source : Type v} [AddCommGroup Source] [Module ℂ Source]
    {VirCarrier : Type u} [AddCommGroup VirCarrier] [Module ℂ VirCarrier]
    {Shifted : Type w} [AddCommGroup Shifted] [Module ℂ Shifted]
    {V : VertexOperatorAlgebra Source}
    {ambientVacuum : VirPiHalfCarrier VirCarrier}
    {ambientProd : VirPiHalfCarrier VirCarrier → ℤ →
      VirPiHalfCarrier VirCarrier → VirPiHalfCarrier VirCarrier}
    {f : Source →ₗ[ℂ] VirPiHalfCarrier VirCarrier}
    (hf : VacuumModeHom V ambientVacuum ambientProd f) (hvac : ambientVacuum ≠ 0)
    {Q : VirPiHalfCarrier VirCarrier →ₗ[ℂ] Shifted}
    {shiftedAction : VirPiHalfCarrier VirCarrier → ℤ → Shifted → Shifted}
    (hAM : Prop21HalfLatticeIdentification V ambientVacuum ambientProd f hf Q shiftedAction) :
    LinearMap.ker f = QuotVOA.maxGradedIdeal V :=
  ker_eq_maxGradedIdeal_of_adamovicMilasProp21 hf hvac hAM

/-! ## The actual shifted zero-mode interface at `k = -8/5`

The source of the Adamović--Milas screening is the half-lattice sector above, while its
codomain is a different Fock sector.  We therefore model the screening current as a heterotypic
formal distribution of linear maps.  Its mode zero is the residue, since `mode S 0 = S (-1)` in
the repository's formal-distribution convention. -/

/-- At `k = -8/5`, the screening momentum is
`nu = xi + (2/5) eta = (1/2)d + (2/5)c`.  The existing one-dimensional `eta` charge line cannot
represent its transverse `xi` component, which is why the target Pi coset remains a separate
carrier below. -/
theorem nuDirection_k85 :
    nuDirection (-8 / 5 : ℂ) = xiDirection + (2 / 5 : ℂ) • etaDirection := by
  funext a
  fin_cases a <;> simp [nuDirection, xiDirection, etaDirection] <;> ring

/-- A shifted Virasoro--Pi carrier.  The Pi factor is deliberately a separate type: for the
Adamović--Milas current it is the coset module shifted by
`nu = (1/2)d - (k/4)c`, not another copy of the source half-lattice VOA. -/
abbrev ShiftedVirPiCarrier (ShiftedVirCarrier : Type u) (ShiftedPiCarrier : Type v)
    [AddCommGroup ShiftedVirCarrier] [Module ℂ ShiftedVirCarrier]
    [AddCommGroup ShiftedPiCarrier] [Module ℂ ShiftedPiCarrier] :=
  ShiftedVirCarrier ⊗[ℂ] ShiftedPiCarrier

/-- A heterotypic field from an ambient free-field sector to a shifted module. -/
abbrev ExternalIntertwiningField (Ambient : Type u) (Shifted : Type v)
    [AddCommGroup Ambient] [Module ℂ Ambient]
    [AddCommGroup Shifted] [Module ℂ Shifted] :=
  FormalDist (Ambient →ₗ[ℂ] Shifted)

/-- The residue/zero mode of a heterotypic screening current. -/
def externalZeroMode {Ambient : Type u} {Shifted : Type v}
    [AddCommGroup Ambient] [Module ℂ Ambient]
    [AddCommGroup Shifted] [Module ℂ Shifted]
    (S : ExternalIntertwiningField Ambient Shifted) : Ambient →ₗ[ℂ] Shifted :=
  mode S 0

@[simp] theorem externalZeroMode_eq_coeff_neg_one
    {Ambient : Type u} {Shifted : Type v}
    [AddCommGroup Ambient] [Module ℂ Ambient]
    [AddCommGroup Shifted] [Module ℂ Shifted]
    (S : ExternalIntertwiningField Ambient Shifted) : externalZeroMode S = S (-1) := rfl

/-- The precise current-intertwining identity needed from the analytic screening calculation.
It is only a three-generator assertion (uniform in the loop mode and state).  In field language
it follows from regularity of the singular OPE of
`Y(v^(k) ⊗ exp(nu), z)` with each of the currents `e`, `h`, and `f`.

This is the smallest explicit OPE/residue gap left by the present carrier infrastructure: the
repository does not yet construct the Virasoro intertwining field `v^(k)`, the coset exponential
`exp(nu)`, or their heterotypic normal product. -/
def K85ScreeningCurrentIntertwining
    {VirCarrier : Type u} [AddCommGroup VirCarrier] [Module ℂ VirCarrier]
    {ShiftedVirCarrier : Type v} [AddCommGroup ShiftedVirCarrier]
      [Module ℂ ShiftedVirCarrier]
    {ShiftedPiCarrier : Type w} [AddCommGroup ShiftedPiCarrier]
      [Module ℂ ShiftedPiCarrier]
    (R : VacuumCurrentRealization (-8 / 5 : ℂ) (VirPiHalfCarrier VirCarrier))
    (S : ExternalIntertwiningField (VirPiHalfCarrier VirCarrier)
      (ShiftedVirPiCarrier ShiftedVirCarrier ShiftedPiCarrier))
    (shiftedCurrent : Fin 3 → ℤ →
      End ℂ (ShiftedVirPiCarrier ShiftedVirCarrier ShiftedPiCarrier)) : Prop :=
  ∀ a n x,
    externalZeroMode S
        (R.rho (ofLoop kappaForm kappaForm_isInvariant (basis a) n) x) =
      shiftedCurrent a n (externalZeroMode S x)

/-- The screening-current condition is exactly three identities, one for each strong affine
generator.  This is the form in which a future OPE calculation should discharge the remaining
analytic hypothesis. -/
theorem k85ScreeningCurrentIntertwining_iff_three
    {VirCarrier : Type u} [AddCommGroup VirCarrier] [Module ℂ VirCarrier]
    {ShiftedVirCarrier : Type v} [AddCommGroup ShiftedVirCarrier]
      [Module ℂ ShiftedVirCarrier]
    {ShiftedPiCarrier : Type w} [AddCommGroup ShiftedPiCarrier]
      [Module ℂ ShiftedPiCarrier]
    {R : VacuumCurrentRealization (-8 / 5 : ℂ) (VirPiHalfCarrier VirCarrier)}
    {S : ExternalIntertwiningField (VirPiHalfCarrier VirCarrier)
      (ShiftedVirPiCarrier ShiftedVirCarrier ShiftedPiCarrier)}
    {shiftedCurrent : Fin 3 → ℤ →
      End ℂ (ShiftedVirPiCarrier ShiftedVirCarrier ShiftedPiCarrier)} :
    K85ScreeningCurrentIntertwining R S shiftedCurrent ↔
      (∀ n x, externalZeroMode S
          (R.rho (ofLoop kappaForm kappaForm_isInvariant (basis colE) n) x) =
        shiftedCurrent colE n (externalZeroMode S x)) ∧
      (∀ n x, externalZeroMode S
          (R.rho (ofLoop kappaForm kappaForm_isInvariant (basis colF) n) x) =
        shiftedCurrent colF n (externalZeroMode S x)) ∧
      (∀ n x, externalZeroMode S
          (R.rho (ofLoop kappaForm kappaForm_isInvariant (basis colH) n) x) =
        shiftedCurrent colH n (externalZeroMode S x)) := by
  constructor
  · intro h
    exact ⟨fun n x => h colE n x, fun n x => h colF n x, fun n x => h colH n x⟩
  · rintro ⟨he, hf, hh⟩ a n x
    fin_cases a
    · exact he n x
    · exact hf n x
    · exact hh n x

/-- Lean-facing specialization of Adamović--Milas Proposition 2.1 to the vacuum sector
`n = 0` and level `k = -8/5`.

The `prop21_image` field is the exact assertion
`range(eval) = ker(Res Y(v^(k) ⊗ exp(nu),z))` on
`L^Vir(c,0) ⊗ Pi(0)^(1/2)`.  `simple_image` records the other content of the proposition,
namely that this kernel is the simple affine vacuum algebra.  No unproved claim about the
kernel on a larger full-Pi space is included. -/
structure K85Prop21ScreeningData
    (VirCarrier : Type u) [AddCommGroup VirCarrier] [Module ℂ VirCarrier]
    (ShiftedVirCarrier : Type v) [AddCommGroup ShiftedVirCarrier]
      [Module ℂ ShiftedVirCarrier]
    (ShiftedPiCarrier : Type w) [AddCommGroup ShiftedPiCarrier]
      [Module ℂ ShiftedPiCarrier] where
  realization : VacuumCurrentRealization (-8 / 5 : ℂ) (VirPiHalfCarrier VirCarrier)
  screeningField : ExternalIntertwiningField (VirPiHalfCarrier VirCarrier)
    (ShiftedVirPiCarrier ShiftedVirCarrier ShiftedPiCarrier)
  shiftedCurrent : Fin 3 → ℤ →
    End ℂ (ShiftedVirPiCarrier ShiftedVirCarrier ShiftedPiCarrier)
  current_intertwining :
    K85ScreeningCurrentIntertwining realization screeningField shiftedCurrent
  prop21_image : Prop21HalfLatticeSectorImage realization.eval
    (externalZeroMode screeningField)
  simple_image : VacuumModeHom.HasSimpleVOAImage
    (affineSl2VOA_closed (-8 / 5 : ℂ) (by norm_num)) realization.eval
  vacuum_ne_zero : realization.vacuum ≠ 0

namespace K85Prop21ScreeningData

variable {VirCarrier : Type u} [AddCommGroup VirCarrier] [Module ℂ VirCarrier]
variable {ShiftedVirCarrier : Type v} [AddCommGroup ShiftedVirCarrier]
  [Module ℂ ShiftedVirCarrier]
variable {ShiftedPiCarrier : Type w} [AddCommGroup ShiftedPiCarrier]
  [Module ℂ ShiftedPiCarrier]

variable (D : K85Prop21ScreeningData VirCarrier ShiftedVirCarrier ShiftedPiCarrier)

/-- The external screening used by the specialized Proposition 2.1 package. -/
abbrev screening : VirPiHalfCarrier VirCarrier →ₗ[ℂ]
    ShiftedVirPiCarrier ShiftedVirCarrier ShiftedPiCarrier :=
  externalZeroMode D.screeningField

/-- Proposition 2.1 says that the concrete affine evaluation has exactly the screening kernel
as its image. -/
theorem range_eval_eq_ker_screening :
    LinearMap.range D.realization.eval = LinearMap.ker D.screening :=
  prop21HalfLatticeSectorImage_iff.mp D.prop21_image

/-- The screening residue annihilates every affine state produced by universal evaluation. -/
theorem screening_eval_zero (x : WakModule (-8 / 5 : ℂ)) :
    D.screening (D.realization.eval x) = 0 := by
  have hx : D.realization.eval x ∈ LinearMap.range D.realization.eval := ⟨x, rfl⟩
  rw [D.range_eval_eq_ker_screening, LinearMap.mem_ker] at hx
  exact hx

/-- In particular the concrete free-field vacuum lies in the screening kernel. -/
theorem screening_vacuum_zero : D.screening D.realization.vacuum = 0 := by
  rw [← D.realization.eval_vacuum]
  exact D.screening_eval_zero _

/-- The kernel of the external screening is stable under all three concrete affine current
modes.  This is the algebraic consequence of the three OPE/residue identities. -/
theorem current_mem_ker_screening (a : Fin 3) (n : ℤ)
    {x : VirPiHalfCarrier VirCarrier} (hx : x ∈ LinearMap.ker D.screening) :
    D.realization.rho (ofLoop kappaForm kappaForm_isInvariant (basis a) n) x ∈
      LinearMap.ker D.screening := by
  rw [LinearMap.mem_ker] at hx ⊢
  rw [D.current_intertwining, hx, map_zero]

/-- At `k = -8/5`, Proposition 2.1 identifies the kernel of the universal affine evaluation
with the maximal ideal.  This route does not require a separate maximal-singular-generator
theorem. -/
theorem ker_eval_eq_maxGradedIdeal :
    LinearMap.ker D.realization.eval = QuotVOA.maxGradedIdeal
      (affineSl2VOA_closed (-8 / 5 : ℂ) (by norm_num)) :=
  AffineEvaluation.eval_ker_eq_maxGradedIdeal_of_simpleImage D.realization
    (by norm_num) D.vacuum_ne_zero D.simple_image

/-- The concrete inverse-DS map from the simple affine vacuum algebra into the half-lattice
free-field carrier. -/
noncomputable def simpleQuotientEval :
    (WakModule (-8 / 5 : ℂ) ⧸ QuotVOA.maxGradedIdeal
      (affineSl2VOA_closed (-8 / 5 : ℂ) (by norm_num))) →ₗ[ℂ]
        VirPiHalfCarrier VirCarrier :=
  AffineEvaluation.evalMaxQuotient D.realization (by norm_num) D.ker_eval_eq_maxGradedIdeal

@[simp] theorem simpleQuotientEval_mkQ (x : WakModule (-8 / 5 : ℂ)) :
    D.simpleQuotientEval
        ((QuotVOA.maxGradedIdeal
          (affineSl2VOA_closed (-8 / 5 : ℂ) (by norm_num))).mkQ x) =
      D.realization.eval x := rfl

/-- Proposition 2.1 makes the concrete simple-quotient map injective. -/
theorem simpleQuotientEval_injective : Function.Injective D.simpleQuotientEval :=
  AffineEvaluation.evalMaxQuotient_injective D.realization (by norm_num)
    D.ker_eval_eq_maxGradedIdeal

/-- Proposition 2.1 also identifies the range of the injected simple quotient exactly: it is
the kernel of the external screening in the stated half-lattice sector. -/
theorem range_simpleQuotientEval_eq_ker_screening :
    LinearMap.range D.simpleQuotientEval = LinearMap.ker D.screening := by
  rw [simpleQuotientEval, AffineEvaluation.range_evalMaxQuotient_eq]
  exact D.range_eval_eq_ker_screening

/-- The known affine weight-five singular vector vanishes under the concrete evaluation as a
formal consequence of Proposition 2.1. -/
theorem eval_sl2Singular85_zero : D.realization.eval sl2Singular85 = 0 := by
  rw [← LinearMap.mem_ker, D.ker_eval_eq_maxGradedIdeal]
  exact Sl2NotSimple85.mem_maxGradedIdeal_85

/-- Hence Proposition 2.1 forces the literal twenty-one-term free-field null identity.  A direct
calculation of this equality is a valuable finite check, but is not needed for
factorization, given the exact screening-kernel theorem. -/
theorem sl2Singular85Eval_zero :
    sl2Singular85Eval
      (fun a n => D.realization.rho
        (ofLoop kappaForm kappaForm_isInvariant (basis a) n))
      D.realization.vacuum = 0 := by
  rw [← map_sl2Singular85 _ D.realization.vacuum D.realization.eval
    D.realization.eval_vacuum D.realization.eval_J]
  exact D.eval_sl2Singular85_zero

end K85Prop21ScreeningData

end
end HalfLattice
end InverseDS
end VOA
