/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Examples.InverseDSLeeYangWardClosure
import Mathlib.Algebra.DualNumber

/-!
# First jets of heterotypic Ward and chain-map identities

This file isolates the formal algebra needed by a logarithmic, or Jantzen, wall operator.  A
first jet of a linear map is a pair `f0 + epsilon f1`, represented as a linear map between
trivial square-zero extensions.  Composition then has the literal Leibniz coefficient

`(g0 + epsilon g1) (f0 + epsilon f1)
  = g0 f0 + epsilon (g0 f1 + g1 f0)`.

Three consequences are proved without analytic or representation-theoretic axioms.

* The first coefficient of a strict heterotypic Ward identity is the inhomogeneous derived Ward
  identity.  Its source is the zeroth operator applied to the first variation of the source and
  target Virasoro actions.
* The first coefficient of a strict chain-map identity is the analogous derived chain-map
  equation.
* A first-order square-zero differential induces the usual Bockstein operation: its first
  coefficient sends special-fibre cycles to cycles and special-fibre boundaries to boundaries.

The final structure `LogarithmicHeterotypicJet` packages exactly these data for a prospective
divided wall field.  It deliberately does not assert that a free-field expression supplies such
data.  Constructing the analytic field, proving its OPEs, and identifying its Felder carriers
remain external obligations.
-/

namespace VOA
namespace InverseDS
namespace WallJets

open Module (End)
open LeeYangWardClosure (homBracket)

noncomputable section

universe u v

variable {Source : Type u} {Target : Type v}
variable [AddCommGroup Source] [Module ℂ Source]
variable [AddCommGroup Target] [Module ℂ Target]

/-- The heterotypic bracket is additive in its middle, map-valued argument. -/
theorem homBracket_sub (targetOp : End ℂ Target) (f g : Source →ₗ[ℂ] Target)
    (sourceOp : End ℂ Source) :
    homBracket targetOp (f - g) sourceOp =
      homBracket targetOp f sourceOp - homBracket targetOp g sourceOp := by
  apply LinearMap.ext
  intro x
  simp only [homBracket, LinearMap.comp_apply, LinearMap.sub_apply, map_sub]
  abel

/-! ## Linear maps over the dual numbers -/

/-- The first-order thickening of a complex vector space.  Its elements are pairs
`x0 + epsilon x1`; multiplication of two infinitesimal coefficients is absent.  The pair model
is used because a vector space need not itself be a ring. -/
abbrev JetSpace (V : Type*) [AddCommGroup V] [Module ℂ V] := V × V

/-- Extend `f0 + epsilon f1` to the first-order thickening of its source and target. -/
def liftLinearJet (f0 f1 : Source →ₗ[ℂ] Target) :
    JetSpace Source →ₗ[ℂ] JetSpace Target where
  toFun x := (f0 x.1, f0 x.2 + f1 x.1)
  map_add' x y := by
    apply Prod.ext
    · simp
    · simp
      module
  map_smul' c x := by
    apply Prod.ext <;> simp

@[simp] theorem liftLinearJet_fst (f0 f1 : Source →ₗ[ℂ] Target) (x : JetSpace Source) :
    (liftLinearJet f0 f1 x).1 = f0 x.1 := rfl

@[simp] theorem liftLinearJet_snd (f0 f1 : Source →ₗ[ℂ] Target) (x : JetSpace Source) :
    (liftLinearJet f0 f1 x).2 = f0 x.2 + f1 x.1 := rfl

@[simp] theorem liftLinearJet_inl (f0 f1 : Source →ₗ[ℂ] Target) (x : Source) :
    liftLinearJet f0 f1 (x, 0) = (f0 x, f1 x) := by
  apply Prod.ext <;> simp [liftLinearJet]

@[simp] theorem liftLinearJet_inr (f0 f1 : Source →ₗ[ℂ] Target) (x : Source) :
    liftLinearJet f0 f1 (0, x) = (0, f0 x) := by
  apply Prod.ext <;> simp [liftLinearJet]

@[simp] theorem liftLinearJet_zero :
    liftLinearJet (0 : Source →ₗ[ℂ] Target) 0 = 0 := by
  apply LinearMap.ext
  intro x
  apply Prod.ext <;> simp [liftLinearJet]

/-- Composition of first jets is the Leibniz rule. -/
theorem liftLinearJet_comp
    {Middle : Type*} [AddCommGroup Middle] [Module ℂ Middle]
    (g0 g1 : Middle →ₗ[ℂ] Target) (f0 f1 : Source →ₗ[ℂ] Middle) :
    (liftLinearJet g0 g1).comp (liftLinearJet f0 f1) =
      liftLinearJet (g0.comp f0) (g0.comp f1 + g1.comp f0) := by
  apply LinearMap.ext
  intro x
  apply Prod.ext
  · simp [liftLinearJet, LinearMap.comp_apply]
  · simp [liftLinearJet, LinearMap.comp_apply]
    module

/-- Equality of lifted first jets detects both coefficients. -/
theorem liftLinearJet_injective {f0 f1 g0 g1 : Source →ₗ[ℂ] Target}
    (h : liftLinearJet f0 f1 = liftLinearJet g0 g1) : f0 = g0 ∧ f1 = g1 := by
  constructor
  · apply LinearMap.ext
    intro x
    have hx := congrArg Prod.fst (LinearMap.congr_fun h (x, 0))
    simpa [liftLinearJet] using hx
  · apply LinearMap.ext
    intro x
    have hx := congrArg Prod.snd (LinearMap.congr_fun h (x, 0))
    simpa [liftLinearJet] using hx

/-! ## Differentiating a heterotypic Ward identity -/

/-- A strict Ward identity over the dual numbers.  The maps `shifted0` and `shifted1` are the
coefficients of the shifted field appearing on the right side, and `a0 + epsilon a1` is its
scalar Ward coefficient. -/
def StrictWardJet
    (source0 source1 : End ℂ Source) (target0 target1 : End ℂ Target)
    (field0 field1 shifted0 shifted1 : Source →ₗ[ℂ] Target) (a0 a1 : ℂ) : Prop :=
  (liftLinearJet target0 target1).comp (liftLinearJet field0 field1) -
      (liftLinearJet field0 field1).comp (liftLinearJet source0 source1) =
    liftLinearJet (a0 • shifted0) (a0 • shifted1 + a1 • shifted0)

/-- The constant coefficient of a strict dual-number Ward identity. -/
theorem StrictWardJet.zero
    {source0 source1 : End ℂ Source} {target0 target1 : End ℂ Target}
    {field0 field1 shifted0 shifted1 : Source →ₗ[ℂ] Target} {a0 a1 : ℂ}
    (h : StrictWardJet source0 source1 target0 target1
      field0 field1 shifted0 shifted1 a0 a1) :
    homBracket target0 field0 source0 = a0 • shifted0 := by
  apply LinearMap.ext
  intro x
  have hx := congrArg Prod.fst (LinearMap.congr_fun h (x, 0))
  simpa [StrictWardJet, homBracket, liftLinearJet, LinearMap.comp_apply,
    LinearMap.sub_apply] using hx

/-- The first coefficient of a strict dual-number Ward identity, before rearranging terms. -/
theorem StrictWardJet.first
    {source0 source1 : End ℂ Source} {target0 target1 : End ℂ Target}
    {field0 field1 shifted0 shifted1 : Source →ₗ[ℂ] Target} {a0 a1 : ℂ}
    (h : StrictWardJet source0 source1 target0 target1
      field0 field1 shifted0 shifted1 a0 a1) :
    target0.comp field1 + target1.comp field0 -
        (field0.comp source1 + field1.comp source0) =
      a0 • shifted1 + a1 • shifted0 := by
  apply LinearMap.ext
  intro x
  have hx := congrArg Prod.snd (LinearMap.congr_fun h (x, 0))
  simpa [StrictWardJet, liftLinearJet, LinearMap.comp_apply,
    LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply] using hx

/-- The inhomogeneous derived Ward equation.  If `field0` is nonzero on chains but trivial on
cohomology, variations of the two Virasoro actions survive and source a non-intertwining
`field1`. -/
theorem StrictWardJet.derived
    {source0 source1 : End ℂ Source} {target0 target1 : End ℂ Target}
    {field0 field1 shifted0 shifted1 : Source →ₗ[ℂ] Target} {a0 a1 : ℂ}
    (h : StrictWardJet source0 source1 target0 target1
      field0 field1 shifted0 shifted1 a0 a1) :
    homBracket target0 field1 source0 =
      a0 • shifted1 + a1 • shifted0 - target1.comp field0 + field0.comp source1 := by
  have hfirst := h.first
  calc
    homBracket target0 field1 source0 =
        (target0.comp field1 + target1.comp field0 -
          (field0.comp source1 + field1.comp source0)) -
          target1.comp field0 + field0.comp source1 := by
      rw [homBracket]
      abel
    _ = (a0 • shifted1 + a1 • shifted0) -
          target1.comp field0 + field0.comp source1 := by rw [hfirst]

/-! ## Differentiating a chain-map identity -/

/-- A differential through first order: the dual-number lift squares to zero. -/
def IsDifferentialJet (d0 d1 : End ℂ Source) : Prop :=
  (liftLinearJet d0 d1).comp (liftLinearJet d0 d1) = 0

/-- The special-fibre differential squares to zero. -/
theorem IsDifferentialJet.zero_sq {d0 d1 : End ℂ Source}
    (h : IsDifferentialJet d0 d1) : d0.comp d0 = 0 := by
  have h' : liftLinearJet (d0.comp d0) (d0.comp d1 + d1.comp d0) =
      liftLinearJet (0 : End ℂ Source) 0 := by
    rw [← liftLinearJet_comp, liftLinearJet_zero]
    exact h
  have hc := (liftLinearJet_injective h').1
  simpa using hc

/-- The first-order coefficient of `d(epsilon)^2=0`. -/
theorem IsDifferentialJet.first_anticommutes {d0 d1 : End ℂ Source}
    (h : IsDifferentialJet d0 d1) : d0.comp d1 + d1.comp d0 = 0 := by
  have h' : liftLinearJet (d0.comp d0) (d0.comp d1 + d1.comp d0) =
      liftLinearJet (0 : End ℂ Source) 0 := by
    rw [← liftLinearJet_comp, liftLinearJet_zero]
    exact h
  have hc := (liftLinearJet_injective h').2
  simpa using hc

/-- A strict chain-map identity over the dual numbers. -/
def IsChainMapJet
    (sourceD0 sourceD1 : End ℂ Source) (targetD0 targetD1 : End ℂ Target)
    (Q0 Q1 : Source →ₗ[ℂ] Target) : Prop :=
  (liftLinearJet targetD0 targetD1).comp (liftLinearJet Q0 Q1) =
    (liftLinearJet Q0 Q1).comp (liftLinearJet sourceD0 sourceD1)

/-- The constant coefficient is an ordinary chain map. -/
theorem IsChainMapJet.zero
    {sourceD0 sourceD1 : End ℂ Source} {targetD0 targetD1 : End ℂ Target}
    {Q0 Q1 : Source →ₗ[ℂ] Target}
    (h : IsChainMapJet sourceD0 sourceD1 targetD0 targetD1 Q0 Q1) :
    targetD0.comp Q0 = Q0.comp sourceD0 := by
  have h' :
      liftLinearJet (targetD0.comp Q0) (targetD0.comp Q1 + targetD1.comp Q0) =
        liftLinearJet (Q0.comp sourceD0) (Q0.comp sourceD1 + Q1.comp sourceD0) := by
    change (liftLinearJet targetD0 targetD1).comp (liftLinearJet Q0 Q1) =
      (liftLinearJet Q0 Q1).comp (liftLinearJet sourceD0 sourceD1) at h
    rw [liftLinearJet_comp, liftLinearJet_comp] at h
    exact h
  exact (liftLinearJet_injective h').1

/-- The first coefficient of a strict chain-map identity. -/
theorem IsChainMapJet.first
    {sourceD0 sourceD1 : End ℂ Source} {targetD0 targetD1 : End ℂ Target}
    {Q0 Q1 : Source →ₗ[ℂ] Target}
    (h : IsChainMapJet sourceD0 sourceD1 targetD0 targetD1 Q0 Q1) :
    targetD0.comp Q1 + targetD1.comp Q0 =
      Q0.comp sourceD1 + Q1.comp sourceD0 := by
  have h' :
      liftLinearJet (targetD0.comp Q0) (targetD0.comp Q1 + targetD1.comp Q0) =
        liftLinearJet (Q0.comp sourceD0) (Q0.comp sourceD1 + Q1.comp sourceD0) := by
    change (liftLinearJet targetD0 targetD1).comp (liftLinearJet Q0 Q1) =
      (liftLinearJet Q0 Q1).comp (liftLinearJet sourceD0 sourceD1) at h
    rw [liftLinearJet_comp, liftLinearJet_comp] at h
    exact h
  exact (liftLinearJet_injective h').2

/-- The inhomogeneous derived chain-map equation. -/
theorem IsChainMapJet.derived
    {sourceD0 sourceD1 : End ℂ Source} {targetD0 targetD1 : End ℂ Target}
    {Q0 Q1 : Source →ₗ[ℂ] Target}
    (h : IsChainMapJet sourceD0 sourceD1 targetD0 targetD1 Q0 Q1) :
    targetD0.comp Q1 - Q1.comp sourceD0 =
      Q0.comp sourceD1 - targetD1.comp Q0 := by
  have hfirst := h.first
  calc
    targetD0.comp Q1 - Q1.comp sourceD0 =
        (targetD0.comp Q1 + targetD1.comp Q0) -
          targetD1.comp Q0 - Q1.comp sourceD0 := by abel
    _ = (Q0.comp sourceD1 + Q1.comp sourceD0) -
          targetD1.comp Q0 - Q1.comp sourceD0 := by rw [hfirst]
    _ = Q0.comp sourceD1 - targetD1.comp Q0 := by abel

/-! ## The wall Bockstein -/

/-- The first coefficient of the differential is the chain-level Bockstein operator. -/
def bockstein (d1 : End ℂ Source) : End ℂ Source := d1

/-- The Bockstein sends a special-fibre cycle to a special-fibre cycle. -/
theorem bockstein_cycle {d0 d1 : End ℂ Source} (h : IsDifferentialJet d0 d1)
    {x : Source} (hx : d0 x = 0) : d0 (bockstein d1 x) = 0 := by
  have hanti := LinearMap.congr_fun h.first_anticommutes x
  simp only [LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.zero_apply, hx, map_zero, add_zero] at hanti
  exact hanti

/-- Changing a cycle representative by the boundary `d0 y` changes its Bockstein by the
boundary `-d0 (d1 y)`.  This is the well-definedness calculation for the induced cohomology
map, stated without hiding it behind a quotient API. -/
theorem bockstein_boundary {d0 d1 : End ℂ Source} (h : IsDifferentialJet d0 d1)
    (y : Source) : bockstein d1 (d0 y) = -d0 (d1 y) := by
  have hanti := LinearMap.congr_fun h.first_anticommutes y
  simp only [LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.zero_apply] at hanti ⊢
  exact eq_neg_of_add_eq_zero_right hanti

/-- Cycles for the special-fibre differential. -/
abbrev cycleSpace (d0 : End ℂ Source) : Submodule ℂ Source := LinearMap.ker d0

/-- Boundaries, regarded as a subspace of cycles.  The `comap` formulation is meaningful even
before the square-zero proof is supplied; `IsDifferentialJet` implies that it contains the full
range of `d0`. -/
def boundarySpace (d0 : End ℂ Source) : Submodule ℂ (cycleSpace d0) :=
  (LinearMap.range d0).comap (cycleSpace d0).subtype

/-- Special-fibre cohomology as cycles modulo boundaries. -/
abbrev SpecialFiberCohomology (d0 : End ℂ Source) :=
  cycleSpace d0 ⧸ boundarySpace d0

/-- The first differential coefficient as a linear endomorphism of the cycle space. -/
def bocksteinOnCycles {d0 d1 : End ℂ Source} (h : IsDifferentialJet d0 d1) :
    End ℂ (cycleSpace d0) where
  toFun x := ⟨d1 x, bockstein_cycle h x.property⟩
  map_add' x y := by ext; simp
  map_smul' c x := by ext; simp

/-- The chain-level Bockstein preserves the boundary subspace. -/
theorem bocksteinOnCycles_preserves_boundary {d0 d1 : End ℂ Source}
    (h : IsDifferentialJet d0 d1) :
    boundarySpace d0 ≤ (boundarySpace d0).comap (bocksteinOnCycles h) := by
  intro x hx
  change (x : Source) ∈ LinearMap.range d0 at hx
  change ((bocksteinOnCycles h x : cycleSpace d0) : Source) ∈ LinearMap.range d0
  obtain ⟨y, hy⟩ := hx
  refine ⟨-d1 y, ?_⟩
  change d0 (-d1 y) = d1 x
  rw [map_neg, ← bockstein_boundary h y, hy]
  rfl

/-- The Bockstein endomorphism induced on special-fibre cohomology. -/
def bocksteinOnCohomology {d0 d1 : End ℂ Source} (h : IsDifferentialJet d0 d1) :
    End ℂ (SpecialFiberCohomology d0) :=
  (boundarySpace d0).mapQ (boundarySpace d0) (bocksteinOnCycles h)
    (bocksteinOnCycles_preserves_boundary h)

@[simp] theorem bocksteinOnCohomology_mk {d0 d1 : End ℂ Source}
    (h : IsDifferentialJet d0 d1) (x : cycleSpace d0) :
    bocksteinOnCohomology h (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (bocksteinOnCycles h x) := rfl

/-! ## Dividing a simple wall factor -/

/-- The literal action of a dual number on a vector-valued first jet. -/
def dualNumberAction (a : DualNumber ℂ) (x : JetSpace Target) : JetSpace Target :=
  (TrivSqZeroExt.fst a • x.1,
    TrivSqZeroExt.fst a • x.2 + TrivSqZeroExt.snd a • x.1)

/-- Multiplication of a vector-valued first jet by the scalar jet `a0 + epsilon a1`. -/
def scalarMulJet (a0 a1 : ℂ) (x0 x1 : Target) : JetSpace Target :=
  dualNumberAction (a0, a1) (x0, x1)

/-- The dual-number generator acts by shifting the constant coefficient into first order. -/
@[simp] theorem dualNumberAction_eps (x0 x1 : Target) :
    dualNumberAction (DualNumber.eps : DualNumber ℂ) (x0, x1) = (0, x0) := by
  apply Prod.ext <;> simp only [dualNumberAction, DualNumber.fst_eps,
    DualNumber.snd_eps, zero_smul, one_smul, zero_add]

/-- On a special-fibre cycle, applying the deformed differential produces exactly the wall
factor `epsilon` times the Bockstein representative.  This is the chain-level connecting-map
construction behind `bocksteinOnCohomology`. -/
theorem differentialJet_cycle_eq_eps_bockstein {d0 d1 : End ℂ Target}
    {x : Target} (hx : d0 x = 0) :
    liftLinearJet d0 d1 (x, 0) =
      dualNumberAction (DualNumber.eps : DualNumber ℂ) (bockstein d1 x, 0) := by
  apply Prod.ext <;> simp [liftLinearJet, dualNumberAction, bockstein, hx]

/-- A scalar with a simple zero, `epsilon u`, kills the unknown first coefficient of the
quotient and exposes `u` times its special value. -/
@[simp] theorem scalarMulJet_simpleWall (u : ℂ) (x0 x1 : Target) :
    scalarMulJet 0 u x0 x1 = (0, u • x0) := by
  apply Prod.ext <;> simp [scalarMulJet, dualNumberAction]

/-- Division by a simple wall factor uniquely recovers the special value of the quotient from
the first nonzero coefficient of the undivided family. -/
theorem dividedSpecialValue_unique {u : ℂ} (hu : u ≠ 0) {x0 y : Target}
    (h : u • x0 = y) : x0 = u⁻¹ • y := by
  calc
    x0 = (1 : ℂ) • x0 := (one_smul ℂ x0).symm
    _ = (u⁻¹ * u) • x0 := by rw [inv_mul_cancel₀ hu]
    _ = u⁻¹ • (u • x0) := by rw [smul_smul]
    _ = u⁻¹ • y := by rw [h]

/-! ## The package consumed by a divided logarithmic wall field -/

/-- Algebraic data of a first-order logarithmic heterotypic wall field.  The index `Mode`
labels field coefficients.  `shift` records the coefficient shift in the primary Ward identity.
The distinguished `residue` coefficient is required to be a chain map through first order.

`field0_boundary` records the crucial derived situation: the zeroth wall operator is nonzero on
chains but chain-null-homotopic, so the inhomogeneous first-order equations can survive while its
cohomology action vanishes. -/
structure LogarithmicHeterotypicJet (Mode : Type*) where
  sourceL0 : ℤ → End ℂ Source
  sourceL1 : ℤ → End ℂ Source
  targetL0 : ℤ → End ℂ Target
  targetL1 : ℤ → End ℂ Target
  field0 : Mode → Source →ₗ[ℂ] Target
  field1 : Mode → Source →ₗ[ℂ] Target
  shift : ℤ → Mode → Mode
  wardCoeff0 : ℤ → Mode → ℂ
  wardCoeff1 : ℤ → Mode → ℂ
  ward : ∀ m t, StrictWardJet
    (sourceL0 m) (sourceL1 m) (targetL0 m) (targetL1 m)
    (field0 t) (field1 t) (field0 (shift m t)) (field1 (shift m t))
    (wardCoeff0 m t) (wardCoeff1 m t)
  sourceD0 : End ℂ Source
  sourceD1 : End ℂ Source
  targetD0 : End ℂ Target
  targetD1 : End ℂ Target
  sourceD_sq : IsDifferentialJet sourceD0 sourceD1
  targetD_sq : IsDifferentialJet targetD0 targetD1
  residue : Mode
  chainMap : IsChainMapJet sourceD0 sourceD1 targetD0 targetD1
    (field0 residue) (field1 residue)
  boundaryHomotopy : Source →ₗ[ℂ] Target
  field0_boundary : field0 residue =
    targetD0.comp boundaryHomotopy + boundaryHomotopy.comp sourceD0

namespace LogarithmicHeterotypicJet

variable {Mode : Type*}

/-- Every packaged coefficient satisfies the derived Ward equation. -/
theorem derivedWard (J : LogarithmicHeterotypicJet (Source := Source) (Target := Target) Mode)
    (m : ℤ) (t : Mode) :
    homBracket (J.targetL0 m) (J.field1 t) (J.sourceL0 m) =
      J.wardCoeff0 m t • J.field1 (J.shift m t) +
        J.wardCoeff1 m t • J.field0 (J.shift m t) -
        (J.targetL1 m).comp (J.field0 t) +
        (J.field0 t).comp (J.sourceL1 m) :=
  (J.ward m t).derived

/-- The residue satisfies the derived chain-map equation. -/
theorem derivedChainMap
    (J : LogarithmicHeterotypicJet (Source := Source) (Target := Target) Mode) :
    J.targetD0.comp (J.field1 J.residue) -
        (J.field1 J.residue).comp J.sourceD0 =
      (J.field0 J.residue).comp J.sourceD1 -
        J.targetD1.comp (J.field0 J.residue) :=
  J.chainMap.derived

/-- The zeroth residue induces the zero map on special-fibre cohomology: on a source cycle its
value is explicitly a target boundary. -/
theorem residue0_cycle_is_boundary
    (J : LogarithmicHeterotypicJet (Source := Source) (Target := Target) Mode)
    {x : Source} (hx : J.sourceD0 x = 0) :
    J.field0 J.residue x = J.targetD0 (J.boundaryHomotopy x) := by
  have h := LinearMap.congr_fun J.field0_boundary x
  simpa [LinearMap.add_apply, LinearMap.comp_apply, hx, map_zero] using h

/-- The corrected first residue.  The two homotopy terms remove exactly the source and target
differential-variation terms in the derived chain-map equation. -/
def secondaryResidue
    (J : LogarithmicHeterotypicJet (Source := Source) (Target := Target) Mode) :
    Source →ₗ[ℂ] Target :=
  J.field1 J.residue - J.boundaryHomotopy.comp J.sourceD1 -
    J.targetD1.comp J.boundaryHomotopy

private theorem sourceVariation_homotopy
    (J : LogarithmicHeterotypicJet (Source := Source) (Target := Target) Mode) :
    J.targetD0.comp (J.boundaryHomotopy.comp J.sourceD1) -
        (J.boundaryHomotopy.comp J.sourceD1).comp J.sourceD0 =
      (J.field0 J.residue).comp J.sourceD1 := by
  apply LinearMap.ext
  intro x
  change J.targetD0 (J.boundaryHomotopy (J.sourceD1 x)) -
      J.boundaryHomotopy (J.sourceD1 (J.sourceD0 x)) =
    J.field0 J.residue (J.sourceD1 x)
  have hb := LinearMap.congr_fun J.field0_boundary (J.sourceD1 x)
  have hs := LinearMap.congr_fun J.sourceD_sq.first_anticommutes x
  have hHs := congrArg J.boundaryHomotopy hs
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.zero_apply,
    map_add, map_zero] at hb hs hHs ⊢
  rw [hb, eq_neg_of_add_eq_zero_left hHs]
  abel

private theorem targetVariation_homotopy
    (J : LogarithmicHeterotypicJet (Source := Source) (Target := Target) Mode) :
    J.targetD0.comp (J.targetD1.comp J.boundaryHomotopy) -
        (J.targetD1.comp J.boundaryHomotopy).comp J.sourceD0 =
      -J.targetD1.comp (J.field0 J.residue) := by
  apply LinearMap.ext
  intro x
  change J.targetD0 (J.targetD1 (J.boundaryHomotopy x)) -
      J.targetD1 (J.boundaryHomotopy (J.sourceD0 x)) =
    -J.targetD1 (J.field0 J.residue x)
  have hb := LinearMap.congr_fun J.field0_boundary x
  have ht := LinearMap.congr_fun J.targetD_sq.first_anticommutes
    (J.boundaryHomotopy x)
  have htb := congrArg J.targetD1 hb
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.zero_apply,
    map_add] at hb ht htb ⊢
  rw [eq_neg_of_add_eq_zero_left ht, htb]
  abel

/-- The corrected first residue is an ordinary chain map on the special fibre.  This is the
secondary operation canonically extracted from the logarithmic first jet and its chosen zeroth
homotopy. -/
theorem secondaryResidue_isChainMap
    (J : LogarithmicHeterotypicJet (Source := Source) (Target := Target) Mode) :
    J.targetD0.comp J.secondaryResidue = J.secondaryResidue.comp J.sourceD0 := by
  rw [← sub_eq_zero]
  calc
    J.targetD0.comp J.secondaryResidue - J.secondaryResidue.comp J.sourceD0 =
        (J.targetD0.comp (J.field1 J.residue) -
          (J.field1 J.residue).comp J.sourceD0) -
        (J.targetD0.comp (J.boundaryHomotopy.comp J.sourceD1) -
          (J.boundaryHomotopy.comp J.sourceD1).comp J.sourceD0) -
        (J.targetD0.comp (J.targetD1.comp J.boundaryHomotopy) -
          (J.targetD1.comp J.boundaryHomotopy).comp J.sourceD0) := by
      apply LinearMap.ext
      intro x
      simp only [secondaryResidue, LinearMap.comp_apply, LinearMap.sub_apply, map_sub]
      abel
    _ = ((J.field0 J.residue).comp J.sourceD1 -
          J.targetD1.comp (J.field0 J.residue)) -
        (J.field0 J.residue).comp J.sourceD1 -
        (-J.targetD1.comp (J.field0 J.residue)) := by
      rw [J.derivedChainMap, J.sourceVariation_homotopy,
        J.targetVariation_homotopy]
    _ = 0 := by abel

/-! ### The exact additional Ward coherence required of the homotopy -/

/-- The differential-variation correction attached to a family of zeroth homotopies. -/
def secondaryCorrection
    (J : LogarithmicHeterotypicJet (Source := Source) (Target := Target) Mode)
    (H : Mode → Source →ₗ[ℂ] Target) (t : Mode) : Source →ₗ[ℂ] Target :=
  (H t).comp J.sourceD1 + J.targetD1.comp (H t)

/-- The corrected first field associated with a family of homotopies. -/
def secondaryField
    (J : LogarithmicHeterotypicJet (Source := Source) (Target := Target) Mode)
    (H : Mode → Source →ₗ[ℂ] Target) (t : Mode) : Source →ₗ[ℂ] Target :=
  J.field1 t - J.secondaryCorrection H t

/-- The minimal Virasoro coherence equation on the zeroth homotopy correction.  Its right side
is exactly the inhomogeneous source in the derived Ward identity.  Thus it says precisely that
subtracting the differential-variation correction leaves an ordinary primary field. -/
def HomotopyWardCoherentAt
    (J : LogarithmicHeterotypicJet (Source := Source) (Target := Target) Mode)
    (H : Mode → Source →ₗ[ℂ] Target) (m : ℤ) (t : Mode) : Prop :=
  homBracket (J.targetL0 m) (J.secondaryCorrection H t) (J.sourceL0 m) =
    J.wardCoeff0 m t • J.secondaryCorrection H (J.shift m t) +
      J.wardCoeff1 m t • J.field0 (J.shift m t) -
      (J.targetL1 m).comp (J.field0 t) +
      (J.field0 t).comp (J.sourceL1 m)

/-- Under the exact homotopy-coherence equation, the corrected first field satisfies the
ordinary special-fibre Ward identity. -/
theorem secondaryField_ward_of_coherent
    (J : LogarithmicHeterotypicJet (Source := Source) (Target := Target) Mode)
    (H : Mode → Source →ₗ[ℂ] Target) (m : ℤ) (t : Mode)
    (hH : J.HomotopyWardCoherentAt H m t) :
    homBracket (J.targetL0 m) (J.secondaryField H t) (J.sourceL0 m) =
      J.wardCoeff0 m t • J.secondaryField H (J.shift m t) := by
  rw [secondaryField, homBracket_sub, J.derivedWard m t, hH,
    secondaryField, smul_sub]
  abel

/-- Conversely, because the derived Ward equation is already part of `J`, ordinary Ward for the
corrected first field forces exactly `HomotopyWardCoherentAt`.  Hence the coherence predicate is
necessary as well as sufficient; it is not a stronger convenient hypothesis. -/
theorem homotopyWardCoherentAt_iff_secondaryField_ward
    (J : LogarithmicHeterotypicJet (Source := Source) (Target := Target) Mode)
    (H : Mode → Source →ₗ[ℂ] Target) (m : ℤ) (t : Mode) :
    J.HomotopyWardCoherentAt H m t ↔
      homBracket (J.targetL0 m) (J.secondaryField H t) (J.sourceL0 m) =
        J.wardCoeff0 m t • J.secondaryField H (J.shift m t) := by
  constructor
  · exact J.secondaryField_ward_of_coherent H m t
  · intro hWard
    rw [secondaryField, homBracket_sub, secondaryField, smul_sub] at hWard
    rw [HomotopyWardCoherentAt]
    have hd := J.derivedWard m t
    calc
      homBracket (J.targetL0 m) (J.secondaryCorrection H t) (J.sourceL0 m) =
          homBracket (J.targetL0 m) (J.field1 t) (J.sourceL0 m) -
            (homBracket (J.targetL0 m) (J.field1 t) (J.sourceL0 m) -
              homBracket (J.targetL0 m) (J.secondaryCorrection H t)
                (J.sourceL0 m)) := by abel
      _ = (J.wardCoeff0 m t • J.field1 (J.shift m t) +
              J.wardCoeff1 m t • J.field0 (J.shift m t) -
              (J.targetL1 m).comp (J.field0 t) +
              (J.field0 t).comp (J.sourceL1 m)) -
            (J.wardCoeff0 m t • J.field1 (J.shift m t) -
              J.wardCoeff0 m t • J.secondaryCorrection H (J.shift m t)) := by
          rw [hWard, hd]
      _ = J.wardCoeff0 m t • J.secondaryCorrection H (J.shift m t) +
            J.wardCoeff1 m t • J.field0 (J.shift m t) -
            (J.targetL1 m).comp (J.field0 t) +
            (J.field0 t).comp (J.sourceL1 m) := by abel

/-- A homotopy family extending the packaged residue homotopy recovers the
secondary residue defined above at the distinguished mode. -/
theorem secondaryField_residue
    (J : LogarithmicHeterotypicJet (Source := Source) (Target := Target) Mode)
    (H : Mode → Source →ₗ[ℂ] Target) (hres : H J.residue = J.boundaryHomotopy) :
    J.secondaryField H J.residue = J.secondaryResidue := by
  rw [secondaryField, secondaryCorrection, secondaryResidue, hres]
  abel

end LogarithmicHeterotypicJet

end
end WallJets
end InverseDS
end VOA
