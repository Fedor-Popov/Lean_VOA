/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modularity.SuperTwistedTrace
import VOA.Modularity.SuperSpinSectorAutomorphisms
import VOA.Modularity.SuperSpinRelationsSq
import VOA.Modularity.SuperSectorSystem

/-!
# Genuine half-integral twisted trace coefficients

The integral trace construction in `SuperTwistedTrace` assembles the zero mode of a state from
the integer conformal-weight grading.  That construction cannot be applied to a genuinely
half-integrally graded state space.  For a denominator-two twisted module, however, a state of
doubled conformal weight `d` has conformal zero mode at the integer twisted-mode label `d - 2`:
the represented fractional mode is `(d - 2)/2 = d/2 - 1`.

This file constructs that genuine zero-mode action, and then its ordinary trace and supertrace on
the finite twisted weight blocks.  The coefficient at exponent `e` is taken on module weight
`e + c/24`, exactly as in the integral construction.  If the module spectrum is contained in one
lower-bounded half-lattice coset, both one-point families land in the existing
`QHalfSeriesAt` carrier.

The final wrappers fix one outer `BoundaryPair`: its spatial automorphism is literally the twist
of the module and its temporal automorphism is literally the lifted insertion.  The four values
of `SpinPair` only project the inserted state into the inner simultaneous eigenspaces of that
fixed pair.  They are not four modules or four outer boundary conditions.  Parity and doubled
conformal weight remain independent throughout; no spin--statistics hypothesis is used.

This is a coefficient realization theorem, not a genus-one recursion theorem.  No sector
existence, convergence, spanning, modularity, or satisfaction of the formal spin relations is
claimed here.
-/

namespace VOA

open Module (End)
open scoped BigOperators
open GammaThetaStmt

set_option autoImplicit false

universe u v

variable {VType : Type u} [AddCommGroup VType] [Module Complex VType]
variable {W : SuperVertexOperatorAlgebra VType}
variable {M : Type v} [AddCommGroup M] [Module Complex M]
variable {g h : SuperAut W}

namespace SuperTwistedModule

variable (T : SuperTwistedModule W g 2 M)

/-! ## Doubled-weight zero modes -/

/-- The denominator-two integer label representing the conformal zero mode of a state of
doubled weight `d`. -/
def halfZeroModeLabel (d : Int) : Int := d - 2

/-- A doubled-weight homogeneous zero mode restricted to one finite twisted weight block. -/
noncomputable def twistedHalfZeroModeBlock (u : VType) (d : Int)
    (hu : u ∈ W.toSuperNearVOA.halfGrading d) (alpha : Complex) :
    End Complex (T.weight alpha) where
  toFun x := ⟨T.YM u (halfZeroModeLabel d) x, by
    have hx := T.weight_mode u
      (show u ∈ W.grading ((d : Complex) / 2) from hu) x x.2 (halfZeroModeLabel d)
    have heq :
        alpha + (d : Complex) / 2 -
            (halfZeroModeLabel d : Int) / ((2 : Nat) : Complex) - 1 =
          alpha := by
      rw [halfZeroModeLabel]
      push_cast
      ring
    rwa [heq] at hx⟩
  map_add' x y := by
    apply Subtype.ext
    exact map_add (T.YM u (halfZeroModeLabel d)) (x : M) (y : M)
  map_smul' c x := by
    apply Subtype.ext
    exact map_smul (T.YM u (halfZeroModeLabel d)) c (x : M)

@[simp] theorem twistedHalfZeroModeBlock_apply_coe (u : VType) (d : Int)
    (hu : u ∈ W.toSuperNearVOA.halfGrading d) (alpha : Complex) (x : T.weight alpha) :
    ((T.twistedHalfZeroModeBlock u d hu alpha x : T.weight alpha) : M) =
      T.YM u (halfZeroModeLabel d) x := rfl

/-- The zero-mode block is linear on one doubled-weight summand. -/
noncomputable def twistedHalfZeroModeFamily (d : Int) (alpha : Complex) :
    W.toSuperNearVOA.halfGrading d →ₗ[Complex] End Complex (T.weight alpha) where
  toFun u := T.twistedHalfZeroModeBlock u d u.2 alpha
  map_add' a b := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact LinearMap.congr_fun
      (congrFun (map_add T.YM (a : VType) b) (halfZeroModeLabel d)) x
  map_smul' c a := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact LinearMap.congr_fun
      (congrFun (map_smul T.YM c (a : VType)) (halfZeroModeLabel d)) x

/-- The genuine half-integral zero-mode action, assembled over the official doubled state
grading. -/
noncomputable def twistedHalfZeroModeAction
    (hhalf : IsHalfIntegerGraded W) (alpha : Complex) :
    VType →ₗ[Complex] End Complex (T.weight alpha) :=
  letI := SuperNearVOA.halfGradingDecomposition W hhalf
  (DFinsupp.lsum Complex (fun d => T.twistedHalfZeroModeFamily d alpha)).comp
    (DirectSum.decomposeLinearEquiv W.toSuperNearVOA.halfGrading).toLinearMap

/-- On a doubled-weight homogeneous state, the global action is the fractional mode
`u_(d/2-1)`, represented by label `d-2`. -/
theorem twistedHalfZeroModeAction_homogeneous
    (hhalf : IsHalfIntegerGraded W) (alpha : Complex) {u : VType} {d : Int}
    (hu : u ∈ W.toSuperNearVOA.halfGrading d) :
    T.twistedHalfZeroModeAction hhalf alpha u =
      T.twistedHalfZeroModeBlock u d hu alpha := by
  letI := SuperNearVOA.halfGradingDecomposition W hhalf
  rw [twistedHalfZeroModeAction, LinearMap.comp_apply]
  change (DFinsupp.lsum Complex (fun j => T.twistedHalfZeroModeFamily j alpha))
    (DirectSum.decompose W.toSuperNearVOA.halfGrading u) = _
  rw [DirectSum.decompose_of_mem W.toSuperNearVOA.halfGrading hu]
  exact DFinsupp.lsum_single Complex
    (fun j => T.twistedHalfZeroModeFamily j alpha) d ⟨u, hu⟩

/-- A doubled-weight zero mode has the parity of its state.  This statement does not relate
the parity `p` to the doubled degree `d`. -/
theorem twistedHalfZeroModeBlock_isParityHomogeneous
    {p : ZMod 2} {u : VType} (huParity : u ∈ W.parity p) (d : Int)
    (huWeight : u ∈ W.toSuperNearVOA.halfGrading d) (alpha : Complex) :
    IsParityHomogeneousEnd (T.twistedWeightParityGrading alpha) p
      (T.twistedHalfZeroModeBlock u d huWeight alpha) := by
  intro q x hx
  exact T.parity_mode u huParity x hx (halfZeroModeLabel d)

/-- The projected global half-integral zero-mode action has the parity of a homogeneous
insertion. -/
theorem twistedHalfZeroModeAction_isParityHomogeneous
    (hhalf : IsHalfIntegerGraded W) {p : ZMod 2} {u : VType} {d : Int}
    (huWeight : u ∈ W.toSuperNearVOA.halfGrading d) (huParity : u ∈ W.parity p)
    (alpha : Complex) :
    IsParityHomogeneousEnd (T.twistedWeightParityGrading alpha) p
      (T.twistedHalfZeroModeAction hhalf alpha u) := by
  rw [T.twistedHalfZeroModeAction_homogeneous hhalf alpha huWeight]
  exact T.twistedHalfZeroModeBlock_isParityHomogeneous huParity d huWeight alpha

/-! ## Actual finite-block traces -/

/-- The finite block operator `Phi(h) o(u)` for the half-integral zero mode. -/
noncomputable def halfInsertedZeroModeBlock
    (phi : SuperTwistedIntertwiner T h) (hhalf : IsHalfIntegerGraded W)
    (u : VType) (alpha : Complex) : End Complex (T.weight alpha) :=
  phi.weightBlock alpha * T.twistedHalfZeroModeAction hhalf alpha u

/-- The literal ordinary trace of the temporal insertion followed by the half-integral zero
mode. -/
noncomputable def twistedHalfPlainOnePoint
    (phi : SuperTwistedIntertwiner T h) (hhalf : IsHalfIntegerGraded W) :
    VType →ₗ[Complex] FormalQSeries where
  toFun u e :=
    let alpha := e + W.centralCharge / 24
    letI := T.weight_finite alpha
    LinearMap.trace Complex (T.weight alpha)
      (T.halfInsertedZeroModeBlock phi hhalf u alpha)
  map_add' u v := by
    funext e
    let alpha := e + W.centralCharge / 24
    letI := T.weight_finite alpha
    change LinearMap.trace Complex (T.weight alpha)
      (T.halfInsertedZeroModeBlock phi hhalf (u + v) alpha) = _
    rw [show T.halfInsertedZeroModeBlock phi hhalf (u + v) alpha =
        T.halfInsertedZeroModeBlock phi hhalf u alpha +
          T.halfInsertedZeroModeBlock phi hhalf v alpha by
      simp [halfInsertedZeroModeBlock, mul_add], map_add]
    rfl
  map_smul' c u := by
    funext e
    let alpha := e + W.centralCharge / 24
    letI := T.weight_finite alpha
    change LinearMap.trace Complex (T.weight alpha)
      (T.halfInsertedZeroModeBlock phi hhalf (c • u) alpha) = _
    rw [show T.halfInsertedZeroModeBlock phi hhalf (c • u) alpha =
        c • T.halfInsertedZeroModeBlock phi hhalf u alpha by
      simp [halfInsertedZeroModeBlock, Algebra.mul_smul_comm], map_smul]
    rfl

/-- The literal supertrace of the same temporal insertion and half-integral zero mode.  The
parity sign occurs exactly once, inside `supertrace`; it is not folded into the temporal
automorphism. -/
noncomputable def twistedHalfSuperOnePoint
    (phi : SuperTwistedIntertwiner T h) (hhalf : IsHalfIntegerGraded W) :
    VType →ₗ[Complex] FormalQSeries where
  toFun u e :=
    let alpha := e + W.centralCharge / 24
    letI := T.weight_finite alpha
    supertrace (T.twistedWeightParityGrading alpha)
      (T.halfInsertedZeroModeBlock phi hhalf u alpha)
  map_add' u v := by
    funext e
    let alpha := e + W.centralCharge / 24
    letI := T.weight_finite alpha
    change supertrace (T.twistedWeightParityGrading alpha)
      (T.halfInsertedZeroModeBlock phi hhalf (u + v) alpha) = _
    rw [show T.halfInsertedZeroModeBlock phi hhalf (u + v) alpha =
        T.halfInsertedZeroModeBlock phi hhalf u alpha +
          T.halfInsertedZeroModeBlock phi hhalf v alpha by
      simp [halfInsertedZeroModeBlock, mul_add], supertrace_add]
    rfl
  map_smul' c u := by
    funext e
    let alpha := e + W.centralCharge / 24
    letI := T.weight_finite alpha
    change supertrace (T.twistedWeightParityGrading alpha)
      (T.halfInsertedZeroModeBlock phi hhalf (c • u) alpha) = _
    rw [show T.halfInsertedZeroModeBlock phi hhalf (c • u) alpha =
        c • T.halfInsertedZeroModeBlock phi hhalf u alpha by
      simp [halfInsertedZeroModeBlock, Algebra.mul_smul_comm], supertrace_smul]
    rfl

@[simp] theorem twistedHalfPlainOnePoint_apply
    (phi : SuperTwistedIntertwiner T h) (hhalf : IsHalfIntegerGraded W)
    (u : VType) (e : Complex) :
    T.twistedHalfPlainOnePoint phi hhalf u e =
      (let alpha := e + W.centralCharge / 24
       letI := T.weight_finite alpha
       LinearMap.trace Complex (T.weight alpha)
        (T.halfInsertedZeroModeBlock phi hhalf u alpha)) := rfl

@[simp] theorem twistedHalfSuperOnePoint_apply
    (phi : SuperTwistedIntertwiner T h) (hhalf : IsHalfIntegerGraded W)
    (u : VType) (e : Complex) :
    T.twistedHalfSuperOnePoint phi hhalf u e =
      (let alpha := e + W.centralCharge / 24
       letI := T.weight_finite alpha
       supertrace (T.twistedWeightParityGrading alpha)
        (T.halfInsertedZeroModeBlock phi hhalf u alpha)) := rfl

/-- A homogeneous insertion whose parity together with the implementer parity is odd has zero
half-integral supertrace.  Doubled conformal degree does not occur in the parity condition. -/
theorem twistedHalfSuperOnePoint_eq_zero_of_total_odd
    (phi : SuperTwistedIntertwiner T h) (hhalf : IsHalfIntegerGraded W)
    {p : ZMod 2} {u : VType} {d : Int}
    (huWeight : u ∈ W.toSuperNearVOA.halfGrading d)
    (huParity : u ∈ W.parity p) (hodd : phi.parityDegree + p = 1) :
    T.twistedHalfSuperOnePoint phi hhalf u = 0 := by
  funext e
  let alpha := e + W.centralCharge / 24
  letI := T.weight_finite alpha
  apply supertrace_eq_zero_of_odd
  have hphi := phi.weightBlock_isParityHomogeneous alpha
  have hu := T.twistedHalfZeroModeAction_isParityHomogeneous
    hhalf huWeight huParity alpha
  simpa only [hodd] using hphi.mul hu

/-! ## Vacuum coefficients -/

/-- The half-integral zero mode of the vacuum is the identity on every twisted weight block. -/
theorem twistedHalfZeroModeBlock_vacuum (alpha : Complex) :
    T.twistedHalfZeroModeBlock W.vacuum 0 (by
      change W.vacuum ∈ W.grading (((0 : Int) : Complex) / 2)
      simpa using W.vacuum_mem) alpha = 1 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  rw [T.twistedHalfZeroModeBlock_apply_coe]
  change T.YM W.vacuum (-2) x = x
  rw [T.vacuum_YM]
  simp

/-- The temporal-inserted ordinary half-character. -/
noncomputable def twistedHalfPlainCharacter
    (phi : SuperTwistedIntertwiner T h) : FormalQSeries := fun e =>
  let alpha := e + W.centralCharge / 24
  letI := T.weight_finite alpha
  LinearMap.trace Complex (T.weight alpha) (phi.weightBlock alpha)

/-- Vacuum insertion recovers the ordinary temporal-inserted half-character. -/
theorem twistedHalfPlainOnePoint_vacuum
    (phi : SuperTwistedIntertwiner T h) (hhalf : IsHalfIntegerGraded W) :
    T.twistedHalfPlainOnePoint phi hhalf W.vacuum =
      T.twistedHalfPlainCharacter phi := by
  funext e
  let alpha := e + W.centralCharge / 24
  letI := T.weight_finite alpha
  have hv : W.vacuum ∈ W.toSuperNearVOA.halfGrading 0 := by
    change W.vacuum ∈ W.grading (((0 : Int) : Complex) / 2)
    simpa using W.vacuum_mem
  change LinearMap.trace Complex (T.weight alpha)
      (T.halfInsertedZeroModeBlock phi hhalf W.vacuum alpha) =
    LinearMap.trace Complex (T.weight alpha) (phi.weightBlock alpha)
  rw [halfInsertedZeroModeBlock,
    T.twistedHalfZeroModeAction_homogeneous hhalf alpha hv,
    T.twistedHalfZeroModeBlock_vacuum, mul_one]

/-- Vacuum insertion recovers the already-defined temporal-inserted supercharacter. -/
theorem twistedHalfSuperOnePoint_vacuum
    (phi : SuperTwistedIntertwiner T h) (hhalf : IsHalfIntegerGraded W) :
    T.twistedHalfSuperOnePoint phi hhalf W.vacuum =
      T.twistedFormalSupercharacter phi := by
  funext e
  let alpha := e + W.centralCharge / 24
  letI := T.weight_finite alpha
  have hv : W.vacuum ∈ W.toSuperNearVOA.halfGrading 0 := by
    change W.vacuum ∈ W.grading (((0 : Int) : Complex) / 2)
    simpa using W.vacuum_mem
  change supertrace (T.twistedWeightParityGrading alpha)
      (T.halfInsertedZeroModeBlock phi hhalf W.vacuum alpha) =
    supertrace (T.twistedWeightParityGrading alpha) (phi.weightBlock alpha)
  rw [halfInsertedZeroModeBlock,
    T.twistedHalfZeroModeAction_homogeneous hhalf alpha hv,
    T.twistedHalfZeroModeBlock_vacuum, mul_one]

/-! ## Half-lattice support and the `T^2` coefficient law -/

/-- The occurring twisted-module weights lie in one lower-bounded half-lattice coset.  The
natural-number index is intentional: unlike `HasTwistedConformalWeight`, this is directly the
support condition consumed by `QHalfSeriesAt`. -/
def HasHalfLatticeSpectrum (beta : Complex) : Prop :=
  ∀ alpha : Complex, T.weight alpha ≠ ⊥ →
    ∃ n : Nat, alpha = beta + halfQExponent n

/-- A plain half-integral trace coefficient vanishes when the corresponding weight block is
zero. -/
theorem twistedHalfPlainOnePoint_apply_eq_zero_of_weight_eq_bot
    (phi : SuperTwistedIntertwiner T h) (hhalf : IsHalfIntegerGraded W)
    (u : VType) (e : Complex)
    (hz : T.weight (e + W.centralCharge / 24) = ⊥) :
    T.twistedHalfPlainOnePoint phi hhalf u e = 0 := by
  let alpha := e + W.centralCharge / 24
  letI := T.weight_finite alpha
  change LinearMap.trace Complex (T.weight alpha)
    (T.halfInsertedZeroModeBlock phi hhalf u alpha) = 0
  have hblock : T.halfInsertedZeroModeBlock phi hhalf u alpha = 0 := by
    apply LinearMap.ext
    intro x
    have hxbot : (x : M) ∈ (⊥ : Submodule Complex M) := by
      rw [← hz]
      exact x.2
    have hx : (x : M) = 0 := by simpa using hxbot
    have hxsub : x = 0 := Subtype.ext hx
    rw [hxsub, map_zero]
    rfl
  rw [hblock, map_zero]

/-- A super half-integral trace coefficient vanishes when the corresponding weight block is
zero. -/
theorem twistedHalfSuperOnePoint_apply_eq_zero_of_weight_eq_bot
    (phi : SuperTwistedIntertwiner T h) (hhalf : IsHalfIntegerGraded W)
    (u : VType) (e : Complex)
    (hz : T.weight (e + W.centralCharge / 24) = ⊥) :
    T.twistedHalfSuperOnePoint phi hhalf u e = 0 := by
  let alpha := e + W.centralCharge / 24
  letI := T.weight_finite alpha
  change supertrace (T.twistedWeightParityGrading alpha)
    (T.halfInsertedZeroModeBlock phi hhalf u alpha) = 0
  have hblock : T.halfInsertedZeroModeBlock phi hhalf u alpha = 0 := by
    apply LinearMap.ext
    intro x
    have hxbot : (x : M) ∈ (⊥ : Submodule Complex M) := by
      rw [← hz]
      exact x.2
    have hx : (x : M) = 0 := by simpa using hxbot
    have hxsub : x = 0 := Subtype.ext hx
    rw [hxsub, map_zero]
    rfl
  rw [hblock]
  simp [supertrace]

/-- A lower-bounded half-lattice spectrum puts every ordinary one-point coefficient series in
the existing doubled-exponent carrier. -/
theorem twistedHalfPlainOnePoint_mem_QHalfSeriesAt
    (phi : SuperTwistedIntertwiner T h) (hhalf : IsHalfIntegerGraded W)
    (beta : Complex) (hspec : T.HasHalfLatticeSpectrum beta) (u : VType) :
    T.twistedHalfPlainOnePoint phi hhalf u ∈
      SuperNearVOA.QHalfSeriesAt (beta - W.centralCharge / 24) := by
  intro e he
  apply T.twistedHalfPlainOnePoint_apply_eq_zero_of_weight_eq_bot phi hhalf
  by_contra hweight
  obtain ⟨n, hn⟩ := hspec (e + W.centralCharge / 24) hweight
  apply he n
  linear_combination hn

/-- The same half-lattice support theorem for supertraces. -/
theorem twistedHalfSuperOnePoint_mem_QHalfSeriesAt
    (phi : SuperTwistedIntertwiner T h) (hhalf : IsHalfIntegerGraded W)
    (beta : Complex) (hspec : T.HasHalfLatticeSpectrum beta) (u : VType) :
    T.twistedHalfSuperOnePoint phi hhalf u ∈
      SuperNearVOA.QHalfSeriesAt (beta - W.centralCharge / 24) := by
  intro e he
  apply T.twistedHalfSuperOnePoint_apply_eq_zero_of_weight_eq_bot phi hhalf
  by_contra hweight
  obtain ⟨n, hn⟩ := hspec (e + W.centralCharge / 24) hweight
  apply he n
  linear_combination hn

/-- `T^2` acts diagonally on every formal series supported on one half-lattice coset.  This is
only the coefficient phase law; it asserts no analytic modular transformation. -/
theorem qShiftN_two_of_mem_QHalfSeriesAt {chi : FormalQSeries} {base : Complex}
    (hchi : chi ∈ SuperNearVOA.QHalfSeriesAt base) :
    qShiftN 2 chi =
      Complex.exp (2 * (Real.pi : Complex) * Complex.I * 2 * base) • chi := by
  funext e
  simp only [qShiftN, Pi.smul_apply, smul_eq_mul]
  norm_num only [Nat.cast_ofNat]
  by_cases he : ∃ n : Nat, e = base + halfQExponent n
  · obtain ⟨n, rfl⟩ := he
    have hexp :
        Complex.exp (2 * (Real.pi : Complex) * Complex.I * 2 *
          (base + halfQExponent n)) =
        Complex.exp (2 * (Real.pi : Complex) * Complex.I * 2 * base) := by
      rw [show 2 * (Real.pi : Complex) * Complex.I * 2 *
            (base + halfQExponent n) =
          2 * (Real.pi : Complex) * Complex.I * 2 * base +
            (n : Complex) * (2 * (Real.pi : Complex) * Complex.I) by
        simp [halfQExponent]
        ring,
        Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]
    rw [hexp]
  · have hz : chi e = 0 := hchi e (by simpa only [not_exists] using he)
    rw [hz, mul_zero, mul_zero]

/-- The actual ordinary trace family obeys the expected `T^2` coefficient phase. -/
theorem twistedHalfPlainOnePoint_qShiftTwo
    (phi : SuperTwistedIntertwiner T h) (hhalf : IsHalfIntegerGraded W)
    (beta : Complex) (hspec : T.HasHalfLatticeSpectrum beta) (u : VType) :
    qShiftN 2 (T.twistedHalfPlainOnePoint phi hhalf u) =
      Complex.exp (2 * (Real.pi : Complex) * Complex.I * 2 *
        (beta - W.centralCharge / 24)) •
          T.twistedHalfPlainOnePoint phi hhalf u :=
  qShiftN_two_of_mem_QHalfSeriesAt
    (T.twistedHalfPlainOnePoint_mem_QHalfSeriesAt phi hhalf beta hspec u)

/-- The actual supertrace family obeys the same `T^2` coefficient phase. -/
theorem twistedHalfSuperOnePoint_qShiftTwo
    (phi : SuperTwistedIntertwiner T h) (hhalf : IsHalfIntegerGraded W)
    (beta : Complex) (hspec : T.HasHalfLatticeSpectrum beta) (u : VType) :
    qShiftN 2 (T.twistedHalfSuperOnePoint phi hhalf u) =
      Complex.exp (2 * (Real.pi : Complex) * Complex.I * 2 *
        (beta - W.centralCharge / 24)) •
          T.twistedHalfSuperOnePoint phi hhalf u :=
  qShiftN_two_of_mem_QHalfSeriesAt
    (T.twistedHalfSuperOnePoint_mem_QHalfSeriesAt phi hhalf beta hspec u)

end SuperTwistedModule

/-! ## A fixed outer boundary pair and its four inner state components -/

namespace BoundaryPair

variable (b : BoundaryPair W)
variable (T : SuperTwistedModule W b.spatial 2 M)
variable (phi : SuperTwistedIntertwiner T b.temporal)

/-- The ordinary half-integral one-point trace with the outer ordering pinned in its type:
`b.spatial` is the module twist and the lift of `b.temporal` is multiplied on the left. -/
noncomputable def halfPlainOnePoint (hhalf : IsHalfIntegerGraded W) :
    VType →ₗ[Complex] FormalQSeries :=
  T.twistedHalfPlainOnePoint phi hhalf

/-- The corresponding supertrace.  No parity automorphism has been inserted into
`b.temporal`. -/
noncomputable def halfSuperOnePoint (hhalf : IsHalfIntegerGraded W) :
    VType →ₗ[Complex] FormalQSeries :=
  T.twistedHalfSuperOnePoint phi hhalf

/-- The ordinary trace of the inner `SpinPair` component of an inserted state.  This is a
projection of the state for one fixed outer pair, not a new trace sector. -/
noncomputable def halfPlainInnerSpinComponent
    (hhalf : IsHalfIntegerGraded W) (p : SpinPair) :
    VType →ₗ[Complex] FormalQSeries :=
  (b.halfPlainOnePoint T phi hhalf).comp
    (SuperAut.spinPairProjector b.spatial b.temporal p)

/-- The supertrace analogue of `halfPlainInnerSpinComponent`. -/
noncomputable def halfSuperInnerSpinComponent
    (hhalf : IsHalfIntegerGraded W) (p : SpinPair) :
    VType →ₗ[Complex] FormalQSeries :=
  (b.halfSuperOnePoint T phi hhalf).comp
    (SuperAut.spinPairProjector b.spatial b.temporal p)

/-- Every ordinary inner-spin component has the same doubled-exponent support as the actual
trace. -/
theorem halfPlainInnerSpinComponent_mem_QHalfSeriesAt
    (hhalf : IsHalfIntegerGraded W) (beta : Complex)
    (hspec : T.HasHalfLatticeSpectrum beta) (p : SpinPair) (u : VType) :
    b.halfPlainInnerSpinComponent T phi hhalf p u ∈
      SuperNearVOA.QHalfSeriesAt (beta - W.centralCharge / 24) := by
  exact T.twistedHalfPlainOnePoint_mem_QHalfSeriesAt phi hhalf beta hspec
    (SuperAut.spinPairProjector b.spatial b.temporal p u)

/-- Every supertrace inner-spin component has the same doubled-exponent support as the actual
supertrace. -/
theorem halfSuperInnerSpinComponent_mem_QHalfSeriesAt
    (hhalf : IsHalfIntegerGraded W) (beta : Complex)
    (hspec : T.HasHalfLatticeSpectrum beta) (p : SpinPair) (u : VType) :
    b.halfSuperInnerSpinComponent T phi hhalf p u ∈
      SuperNearVOA.QHalfSeriesAt (beta - W.centralCharge / 24) := by
  exact T.twistedHalfSuperOnePoint_mem_QHalfSeriesAt phi hhalf beta hspec
    (SuperAut.spinPairProjector b.spatial b.temporal p u)

/-- Each ordinary inner-spin component has the exact `T^2` coefficient phase forced by its
half-lattice support. -/
theorem halfPlainInnerSpinComponent_qShiftTwo
    (hhalf : IsHalfIntegerGraded W) (beta : Complex)
    (hspec : T.HasHalfLatticeSpectrum beta) (p : SpinPair) (u : VType) :
    SuperTwistedModule.qShiftN 2 (b.halfPlainInnerSpinComponent T phi hhalf p u) =
      Complex.exp (2 * (Real.pi : Complex) * Complex.I * 2 *
        (beta - W.centralCharge / 24)) •
          b.halfPlainInnerSpinComponent T phi hhalf p u :=
  SuperTwistedModule.qShiftN_two_of_mem_QHalfSeriesAt
    (b.halfPlainInnerSpinComponent_mem_QHalfSeriesAt T phi hhalf beta hspec p u)

/-- Each supertrace inner-spin component has the same `T^2` coefficient phase. -/
theorem halfSuperInnerSpinComponent_qShiftTwo
    (hhalf : IsHalfIntegerGraded W) (beta : Complex)
    (hspec : T.HasHalfLatticeSpectrum beta) (p : SpinPair) (u : VType) :
    SuperTwistedModule.qShiftN 2 (b.halfSuperInnerSpinComponent T phi hhalf p u) =
      Complex.exp (2 * (Real.pi : Complex) * Complex.I * 2 *
        (beta - W.centralCharge / 24)) •
          b.halfSuperInnerSpinComponent T phi hhalf p u :=
  SuperTwistedModule.qShiftN_two_of_mem_QHalfSeriesAt
    (b.halfSuperInnerSpinComponent_mem_QHalfSeriesAt T phi hhalf beta hspec p u)

/-- On an advertised inner eigenspace, the matching ordinary projected component is exactly the
unprojected trace.  The involution hypotheses are explicit. -/
theorem halfPlainInnerSpinComponent_eq_of_isSpinEigenvector
    (hhalf : IsHalfIntegerGraded W) (htemporal : b.temporal ^ 2 = 1)
    {p : SpinPair} {u : VType}
    (hu : b.IsSpinEigenvector p u) :
    b.halfPlainInnerSpinComponent T phi hhalf p u =
      b.halfPlainOnePoint T phi hhalf u := by
  have hsector : u ∈ SuperAut.spinSectors b.spatial b.temporal p :=
    (SuperAut.mem_spinSectors_iff b.spatial b.temporal T.order_pow htemporal
      b.commute.eq p u).2 hu
  rw [halfPlainInnerSpinComponent, LinearMap.comp_apply,
    SuperAut.spinPairProjector_eq_self b.spatial b.temporal T.order_pow htemporal
      b.commute.eq hsector]

/-- A nonmatching inner projector kills an eigensector before the ordinary trace is taken. -/
theorem halfPlainInnerSpinComponent_eq_zero_of_isSpinEigenvector
    (hhalf : IsHalfIntegerGraded W) (htemporal : b.temporal ^ 2 = 1)
    {p q : SpinPair} (hpq : p ≠ q) {u : VType}
    (hu : b.IsSpinEigenvector q u) :
    b.halfPlainInnerSpinComponent T phi hhalf p u = 0 := by
  have hsector : u ∈ SuperAut.spinSectors b.spatial b.temporal q :=
    (SuperAut.mem_spinSectors_iff b.spatial b.temporal T.order_pow htemporal
      b.commute.eq q u).2 hu
  rw [halfPlainInnerSpinComponent, LinearMap.comp_apply,
    SuperAut.spinPairProjector_eq_zero_of_ne b.spatial b.temporal T.order_pow htemporal
      b.commute.eq hpq hsector, map_zero]

/-- The matching supertrace component is likewise the unprojected supertrace on its inner
eigenspace. -/
theorem halfSuperInnerSpinComponent_eq_of_isSpinEigenvector
    (hhalf : IsHalfIntegerGraded W) (htemporal : b.temporal ^ 2 = 1)
    {p : SpinPair} {u : VType}
    (hu : b.IsSpinEigenvector p u) :
    b.halfSuperInnerSpinComponent T phi hhalf p u =
      b.halfSuperOnePoint T phi hhalf u := by
  have hsector : u ∈ SuperAut.spinSectors b.spatial b.temporal p :=
    (SuperAut.mem_spinSectors_iff b.spatial b.temporal T.order_pow htemporal
      b.commute.eq p u).2 hu
  rw [halfSuperInnerSpinComponent, LinearMap.comp_apply,
    SuperAut.spinPairProjector_eq_self b.spatial b.temporal T.order_pow htemporal
      b.commute.eq hsector]

/-- A nonmatching inner projector also kills the insertion before the supertrace is taken. -/
theorem halfSuperInnerSpinComponent_eq_zero_of_isSpinEigenvector
    (hhalf : IsHalfIntegerGraded W) (htemporal : b.temporal ^ 2 = 1)
    {p q : SpinPair} (hpq : p ≠ q) {u : VType}
    (hu : b.IsSpinEigenvector q u) :
    b.halfSuperInnerSpinComponent T phi hhalf p u = 0 := by
  have hsector : u ∈ SuperAut.spinSectors b.spatial b.temporal q :=
    (SuperAut.mem_spinSectors_iff b.spatial b.temporal T.order_pow htemporal
      b.commute.eq q u).2 hu
  rw [halfSuperInnerSpinComponent, LinearMap.comp_apply,
    SuperAut.spinPairProjector_eq_zero_of_ne b.spatial b.temporal T.order_pow htemporal
      b.commute.eq hpq hsector, map_zero]

/-- The four projected ordinary trace components add back to the actual trace. -/
theorem sum_halfPlainInnerSpinComponent
    (hhalf : IsHalfIntegerGraded W) :
    ∑ p : SpinPair, b.halfPlainInnerSpinComponent T phi hhalf p =
      b.halfPlainOnePoint T phi hhalf := by
  apply LinearMap.ext
  intro u
  change ∑ p : SpinPair,
      b.halfPlainOnePoint T phi hhalf
        (SuperAut.spinPairProjector b.spatial b.temporal p u) =
    b.halfPlainOnePoint T phi hhalf u
  rw [← map_sum, SuperAut.sum_spinPairProjector]

/-- The four projected supertrace components add back to the actual supertrace. -/
theorem sum_halfSuperInnerSpinComponent
    (hhalf : IsHalfIntegerGraded W) :
    ∑ p : SpinPair, b.halfSuperInnerSpinComponent T phi hhalf p =
      b.halfSuperOnePoint T phi hhalf := by
  apply LinearMap.ext
  intro u
  change ∑ p : SpinPair,
      b.halfSuperOnePoint T phi hhalf
        (SuperAut.spinPairProjector b.spatial b.temporal p u) =
    b.halfSuperOnePoint T phi hhalf u
  rw [← map_sum, SuperAut.sum_spinPairProjector]

end BoundaryPair

end VOA
