/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modules.SuperTwistedZhu
import VOA.Modularity.SuperTorusOnePoint
import VOA.Modularity.TwistedSuperSymmetricFunctionals
import VOA.Modularity.QueerOddTrace
import VOA.Modules.Rationality

/-!
# Formal supertraces in a single twisted sector

This file constructs the purely formal one-point coefficient function attached to one
positive-energy `g`-twisted supermodule and one chosen homogeneous lift of a commuting automorphism
`h`.  The integer label of the zero mode of an integral weight-`k` state is `(k-1)N`, since the
twisted carrier interprets label `r` as fractional mode `r/N`.

The trace insertion is the literal module lift `Phi(h)`.  With the intertwining convention
`Phi(h) rho(a) = rho(h a) Phi(h)`, this literal insertion obeys the cyclic law oriented by
`h^{-1}`.  The inverse insertion obeys the `h`-oriented coefficient used in
`TwistedSuperSymmetricFunctionals`.  Both statements are recorded explicitly below.

Ordinary trace, even-insertion supertrace, and Type-II odd trace remain distinct.  The Type-II
path below is restricted to a certified represented queer subalgebra; it is never a functional
on the full endomorphism algebra.

There is no convergence, analytic continuation, or modular-transformation claim in this file.
-/

namespace VOA

open Module (End)
open scoped BigOperators

set_option autoImplicit false

universe u v

variable {VType : Type u} [AddCommGroup VType] [Module ℂ VType]
variable {W : SuperVertexOperatorAlgebra VType}
variable {M : Type v} [AddCommGroup M] [Module ℂ M]
variable {g h : SuperAut W} {N : ℕ}

namespace SuperTwistedModule

/-! ## Parity on finite twisted weight blocks -/

/-- The carried weight decomposition is exactly the eigenspace decomposition of the twisted
module `L0` operator. -/
theorem twistedEigenvector_mem_weight (T : SuperTwistedModule W g N M)
    {γ : ℂ} {y : M} (hy : T.YM W.conformalVector N y = γ • y) : y ∈ T.weight γ := by
  classical
  letI := DirectSum.IsInternal.chooseDecomposition T.weight T.weight_isInternal
  set c : ℂ → M := fun j => ((DirectSum.decompose T.weight y j : T.weight j) : M) with hc
  set s : Finset ℂ := (DirectSum.decompose T.weight y).support with hs
  have hdecomp : (∑ j ∈ s, c j) = y := DirectSum.sum_support_decompose T.weight y
  have hL0comp : ∀ j : ℂ, T.YM W.conformalVector N (c j) = j • c j := fun j =>
    T.L0_weight j _ (DirectSum.decompose T.weight y j).2
  have hzero : (∑ j ∈ s, ((j - γ) • c j)) = 0 := by
    have hLHS : (∑ j ∈ s, ((j - γ) • c j)) =
        T.YM W.conformalVector N y - γ • y := by
      rw [← hdecomp, map_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [hL0comp j, sub_smul]
    rw [hLHS, hy, sub_self]
  have hmem : ∀ j : ℂ, ((j - γ) • c j) ∈ T.weight j := fun j =>
    (T.weight j).smul_mem _ (DirectSum.decompose T.weight y j).2
  have hcvanish : ∀ j ∈ s, j ≠ γ → c j = 0 := by
    intro j hjs hjγ
    have hdz : (DirectSum.decompose T.weight (∑ k ∈ s, ((k - γ) • c k)) j :
        T.weight j) = 0 := by
      rw [hzero, DirectSum.decompose_zero, DirectSum.zero_apply]
    have hcomp : ((DirectSum.decompose T.weight (∑ k ∈ s, ((k - γ) • c k)) j :
        T.weight j) : M) = 0 := by rw [hdz, ZeroMemClass.coe_zero]
    rw [DirectSum.decompose_sum, DirectSum.sum_apply, AddSubmonoidClass.coe_finsetSum,
      Finset.sum_eq_single j (fun k hks hkj => ?_) (fun hjns => ?_)] at hcomp
    · rw [DirectSum.decompose_of_mem_same T.weight (hmem j)] at hcomp
      exact (smul_eq_zero.mp hcomp).resolve_left (sub_ne_zero.mpr hjγ)
    · rw [DirectSum.decompose_of_mem_ne T.weight (hmem k) hkj]
    · exact absurd hjs hjns
  have hyeq : y = c γ := by
    rw [← hdecomp]
    by_cases hγs : γ ∈ s
    · rw [Finset.sum_eq_single γ (fun k hks hkγ => hcvanish k hks hkγ)
        (fun hnot => absurd hγs hnot)]
    · have hcγ0 : c γ = 0 := by
        rw [hc]
        simp only
        have hz : DirectSum.decompose T.weight y γ = 0 := by
          rw [← DFinsupp.notMem_support_iff]
          exact hγs
        rw [hz, ZeroMemClass.coe_zero]
      rw [hcγ0, Finset.sum_eq_zero
        (fun k hks => hcvanish k hks (fun hk => hγs (hk ▸ hks)))]
  rw [hyeq, hc]
  exact (DirectSum.decompose T.weight y γ).2

/-- The twisted `L0` operator preserves module parity. -/
theorem twistedL0_mem_parity (T : SuperTwistedModule W g N M)
    {q : ZMod 2} {x : M} (hx : x ∈ T.parity q) :
    T.YM W.conformalVector N x ∈ T.parity q := by
  have hx' := T.parity_mode W.conformalVector W.conformal_parity x hx N
  simpa using hx'

/-- The module parity projection. -/
noncomputable def twistedParityProj (T : SuperTwistedModule W g N M)
    (p : ZMod 2) : End ℂ M :=
  letI := DirectSum.IsInternal.chooseDecomposition T.parity T.parity_isInternal
  homogProj T.parity p

/-- Module parity projections preserve twisted conformal weight. -/
theorem twistedParityProj_mem_weight (T : SuperTwistedModule W g N M) (p : ZMod 2)
    {α : ℂ} {x : M} (hx : x ∈ T.weight α) : T.twistedParityProj p x ∈ T.weight α := by
  letI := DirectSum.IsInternal.chooseDecomposition T.parity T.parity_isInternal
  change homogProj T.parity p x ∈ T.weight α
  apply T.twistedEigenvector_mem_weight
  have hcomm := homogProj_comm T.parity (T.YM W.conformalVector N)
    (fun q y hy => T.twistedL0_mem_parity hy) p x
  calc
    T.YM W.conformalVector N (homogProj T.parity p x) =
        homogProj T.parity p (T.YM W.conformalVector N x) := hcomm.symm
    _ = homogProj T.parity p (α • x) := by rw [T.L0_weight α x hx]
    _ = α • homogProj T.parity p x := map_smul _ _ _

/-- Parity `p` inside the finite twisted weight block `M_alpha`. -/
def twistedWeightParity (T : SuperTwistedModule W g N M) (α : ℂ) (p : ZMod 2) :
    Submodule ℂ (T.weight α) := (T.parity p).comap (T.weight α).subtype

@[simp] theorem mem_twistedWeightParity (T : SuperTwistedModule W g N M)
    {α : ℂ} {p : ZMod 2} {x : T.weight α} :
    x ∈ T.twistedWeightParity α p ↔ (x : M) ∈ T.parity p := Iff.rfl

/-- Every finite twisted weight block inherits an internal parity grading. -/
theorem twistedWeightParity_isInternal (T : SuperTwistedModule W g N M) (α : ℂ) :
    DirectSum.IsInternal (T.twistedWeightParity α) := by
  letI := DirectSum.IsInternal.chooseDecomposition T.parity T.parity_isInternal
  exact isInternal_comap T.parity (T.weight α)
    (fun p x hx => by simpa [twistedParityProj] using T.twistedParityProj_mem_weight p hx)

/-- Basis-independent parity grading on a finite twisted weight block. -/
def twistedWeightParityGrading (T : SuperTwistedModule W g N M) (α : ℂ) :
    ParityGrading (T.weight α) where
  parity := T.twistedWeightParity α
  isInternal := T.twistedWeightParity_isInternal α

/-! The global block-valued zero-mode action is `twistedZeroModeAction`, constructed in
`SuperTwistedZhu` from the same integral direct sum.  This file uses that audited action rather
than rebuilding it. -/

end SuperTwistedModule

namespace SuperTwistedIntertwiner

variable {T : SuperTwistedModule W g N M}

/-- Restriction of the homogeneous lift `Phi(h)` to one finite weight block. -/
noncomputable def weightBlock (φ : SuperTwistedIntertwiner T h) (α : ℂ) :
    End ℂ (T.weight α) where
  toFun x := ⟨φ x, (φ.map_weight' α x).2 x.2⟩
  map_add' x y := Subtype.ext (φ.toLinearEquiv.map_add x y)
  map_smul' c x := Subtype.ext (φ.toLinearEquiv.map_smul c x)

@[simp] theorem weightBlock_apply_coe (φ : SuperTwistedIntertwiner T h)
    (α : ℂ) (x : T.weight α) : ((φ.weightBlock α x : T.weight α) : M) = φ x := rfl

/-- The intertwiner block has the declared parity degree. -/
theorem weightBlock_isParityHomogeneous (φ : SuperTwistedIntertwiner T h) (α : ℂ) :
    IsParityHomogeneousEnd (T.twistedWeightParityGrading α) φ.parityDegree
      (φ.weightBlock α) := by
  intro q x hx
  exact (φ.map_parity' q x).2 hx

/-- Restriction of `Phi(h)^{-1}` to a finite weight block.  This is the insertion whose cyclic
orientation matches `twistedSuperCyclicCoeff` for `h`. -/
noncomputable def inverseWeightBlock (φ : SuperTwistedIntertwiner T h) (α : ℂ) :
    End ℂ (T.weight α) where
  toFun x := ⟨φ.toLinearEquiv.symm x, by
    apply (φ.map_weight' α ( φ.toLinearEquiv.symm x)).mp
    simpa using x.2⟩
  map_add' x y := Subtype.ext (φ.toLinearEquiv.symm.map_add x y)
  map_smul' c x := Subtype.ext (φ.toLinearEquiv.symm.map_smul c x)

@[simp] theorem inverseWeightBlock_apply_coe (φ : SuperTwistedIntertwiner T h)
    (α : ℂ) (x : T.weight α) :
    ((φ.inverseWeightBlock α x : T.weight α) : M) = φ.toLinearEquiv.symm x := rfl

/-- The inverse intertwiner block has the same parity degree, since degrees are modulo two. -/
theorem inverseWeightBlock_isParityHomogeneous (φ : SuperTwistedIntertwiner T h) (α : ℂ) :
    IsParityHomogeneousEnd (T.twistedWeightParityGrading α) φ.parityDegree
      (φ.inverseWeightBlock α) := by
  intro q x hx
  change φ.toLinearEquiv.symm (x : M) ∈ T.parity (φ.parityDegree + q)
  apply (φ.map_parity' (φ.parityDegree + q)
    (φ.toLinearEquiv.symm x)).mp
  change (x : M) ∈ T.parity q at hx
  have hcancel : φ.parityDegree + (φ.parityDegree + q) = q := by
    rcases zmod2_cases φ.parityDegree with hr | hr <;>
      rcases zmod2_cases q with hq | hq <;> rw [hr, hq] <;> decide
  simpa only [LinearEquiv.apply_symm_apply, hcancel] using hx

@[simp] theorem inverseWeightBlock_mul_weightBlock
    (φ : SuperTwistedIntertwiner T h) (α : ℂ) :
    φ.inverseWeightBlock α * φ.weightBlock α = 1 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  simp [Module.End.mul_apply]

@[simp] theorem weightBlock_mul_inverseWeightBlock
    (φ : SuperTwistedIntertwiner T h) (α : ℂ) :
    φ.weightBlock α * φ.inverseWeightBlock α = 1 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  simp [Module.End.mul_apply]

end SuperTwistedIntertwiner

namespace SuperTwistedModule

variable {T : SuperTwistedModule W g N M}

/-! ## Homogeneous zero-mode blocks -/

/-- A homogeneous zero-mode block has the parity of its state. -/
theorem twistedZeroModeBlock_isParityHomogeneous (T : SuperTwistedModule W g N M)
    {p : ZMod 2} {u : VType} (huParity : u ∈ W.parity p) (k : ℤ)
    (huWeight : u ∈ W.toSuperNearVOA.gradingZ k) (α : ℂ) :
    IsParityHomogeneousEnd (T.twistedWeightParityGrading α) p
      (T.twistedZeroModeBlock u k huWeight α) := by
  intro q x hx
  exact T.twistedZeroModeBlock_parity huParity k huWeight α x hx

/-- The parity degree of a projected global block on a homogeneous insertion. -/
theorem twistedZeroModeAction_isParityHomogeneous (T : SuperTwistedModule W g N M)
    (hW : W.toSuperNearVOA.IntegralWeights) {p : ZMod 2} {k : ℤ} {u : VType}
    (huWeight : u ∈ W.toSuperNearVOA.gradingZ k) (huParity : u ∈ W.parity p) (α : ℂ) :
    IsParityHomogeneousEnd (T.twistedWeightParityGrading α) p
      (T.twistedZeroModeAction hW α u) := by
  rw [T.twistedZeroModeAction_homogeneous hW α huWeight]
  exact T.twistedZeroModeBlock_isParityHomogeneous huParity k huWeight α

/-! ## Even inserted supertraces -/

/-- The finite block operator `Phi(h) o(u)`. -/
noncomputable def insertedZeroModeBlock (T : SuperTwistedModule W g N M)
    (φ : SuperTwistedIntertwiner T h) (hW : W.toSuperNearVOA.IntegralWeights)
    (u : VType) (α : ℂ) : End ℂ (T.weight α) :=
  φ.weightBlock α * T.twistedZeroModeAction hW α u

/-- The formal one-point `h`-inserted supertrace, including the `-c/24` exponent shift. -/
noncomputable def twistedSuperOnePoint (T : SuperTwistedModule W g N M)
    (φ : SuperTwistedIntertwiner T h) (hW : W.toSuperNearVOA.IntegralWeights) :
    VType →ₗ[ℂ] FormalQSeries where
  toFun u e :=
    let α := e + W.centralCharge / 24
    haveI := T.weight_finite α
    supertrace (T.twistedWeightParityGrading α) (T.insertedZeroModeBlock φ hW u α)
  map_add' u v := by
    funext e
    let α := e + W.centralCharge / 24
    haveI := T.weight_finite α
    change supertrace (T.twistedWeightParityGrading α)
      (T.insertedZeroModeBlock φ hW (u + v) α) = _
    rw [show T.insertedZeroModeBlock φ hW (u + v) α =
        T.insertedZeroModeBlock φ hW u α + T.insertedZeroModeBlock φ hW v α by
      simp [insertedZeroModeBlock, mul_add], supertrace_add]
    rfl
  map_smul' c u := by
    funext e
    let α := e + W.centralCharge / 24
    haveI := T.weight_finite α
    change supertrace (T.twistedWeightParityGrading α)
      (T.insertedZeroModeBlock φ hW (c • u) α) = _
    rw [show T.insertedZeroModeBlock φ hW (c • u) α =
        c • T.insertedZeroModeBlock φ hW u α by
      simp [insertedZeroModeBlock, Algebra.mul_smul_comm], supertrace_smul]
    rfl

@[simp] theorem twistedSuperOnePoint_apply (T : SuperTwistedModule W g N M)
    (φ : SuperTwistedIntertwiner T h) (hW : W.toSuperNearVOA.IntegralWeights)
    (u : VType) (e : ℂ) : T.twistedSuperOnePoint φ hW u e =
      (let α := e + W.centralCharge / 24
       letI := T.weight_finite α
       supertrace (T.twistedWeightParityGrading α)
        (T.insertedZeroModeBlock φ hW u α)) := rfl

/-- A homogeneous insertion vanishes whenever its parity plus the implementer parity is odd. -/
theorem twistedSuperOnePoint_eq_zero_of_total_odd
    (T : SuperTwistedModule W g N M) (φ : SuperTwistedIntertwiner T h)
    (hW : W.toSuperNearVOA.IntegralWeights) {p : ZMod 2} {k : ℤ} {u : VType}
    (huWeight : u ∈ W.toSuperNearVOA.gradingZ k) (huParity : u ∈ W.parity p)
    (hodd : φ.parityDegree + p = 1) :
    T.twistedSuperOnePoint φ hW u = 0 := by
  funext e
  let α := e + W.centralCharge / 24
  haveI := T.weight_finite α
  apply supertrace_eq_zero_of_odd
  have hφ := φ.weightBlock_isParityHomogeneous α
  have hu := T.twistedZeroModeAction_isParityHomogeneous hW huWeight huParity α
  simpa only [hodd] using hφ.mul hu

/-- For an even implementer, odd state insertions vanish. -/
theorem twistedSuperOnePoint_eq_zero_of_odd_homogeneous
    (T : SuperTwistedModule W g N M) (φ : SuperTwistedIntertwiner T h)
    (hW : W.toSuperNearVOA.IntegralWeights) (hφEven : φ.parityDegree = 0)
    {k : ℤ} {u : VType} (huWeight : u ∈ W.toSuperNearVOA.gradingZ k)
    (huParity : u ∈ W.parity 1) : T.twistedSuperOnePoint φ hW u = 0 := by
  apply T.twistedSuperOnePoint_eq_zero_of_total_odd φ hW huWeight huParity
  rw [hφEven, zero_add]

/-- The formal `h`-inserted supercharacter. -/
noncomputable def twistedFormalSupercharacter (T : SuperTwistedModule W g N M)
    (φ : SuperTwistedIntertwiner T h) : FormalQSeries := fun e =>
  let α := e + W.centralCharge / 24
  haveI := T.weight_finite α
  supertrace (T.twistedWeightParityGrading α) (φ.weightBlock α)

/-! Ordinary trace is kept as a separate construction.  In particular, no parity-selection
rule is asserted for it. -/

/-- The literal `h`-inserted ordinary trace on the same finite blocks. -/
noncomputable def twistedPlainOnePoint (T : SuperTwistedModule W g N M)
    (φ : SuperTwistedIntertwiner T h) (hW : W.toSuperNearVOA.IntegralWeights) :
    VType →ₗ[ℂ] FormalQSeries where
  toFun u e :=
    let α := e + W.centralCharge / 24
    haveI := T.weight_finite α
    LinearMap.trace ℂ (T.weight α) (T.insertedZeroModeBlock φ hW u α)
  map_add' u v := by
    funext e
    let α := e + W.centralCharge / 24
    haveI := T.weight_finite α
    change LinearMap.trace ℂ (T.weight α) (T.insertedZeroModeBlock φ hW (u + v) α) = _
    rw [show T.insertedZeroModeBlock φ hW (u + v) α =
        T.insertedZeroModeBlock φ hW u α + T.insertedZeroModeBlock φ hW v α by
      simp [insertedZeroModeBlock, mul_add], map_add]
    rfl
  map_smul' c u := by
    funext e
    let α := e + W.centralCharge / 24
    haveI := T.weight_finite α
    change LinearMap.trace ℂ (T.weight α) (T.insertedZeroModeBlock φ hW (c • u) α) = _
    rw [show T.insertedZeroModeBlock φ hW (c • u) α =
        c • T.insertedZeroModeBlock φ hW u α by
      simp [insertedZeroModeBlock, Algebra.mul_smul_comm], map_smul]
    rfl

/-- The vacuum zero-mode block is the identity. -/
theorem twistedZeroModeBlock_vacuum (T : SuperTwistedModule W g N M) (α : ℂ) :
    T.twistedZeroModeBlock W.vacuum 0 (by
      simpa only [SuperNearVOA.gradingZ_apply, Int.cast_zero] using W.vacuum_mem) α = 1 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  rw [T.twistedZeroModeBlock_apply_coe]
  change T.YM W.vacuum (zeroModeLabel N 0) x = x
  rw [show zeroModeLabel N 0 = -(N : ℤ) by simp [zeroModeLabel], T.vacuum_YM]
  simp

/-- Vacuum insertion is the `h`-inserted formal supercharacter. -/
theorem twistedSuperOnePoint_vacuum (T : SuperTwistedModule W g N M)
    (φ : SuperTwistedIntertwiner T h) (hW : W.toSuperNearVOA.IntegralWeights) :
    T.twistedSuperOnePoint φ hW W.vacuum = T.twistedFormalSupercharacter φ := by
  funext e
  let α := e + W.centralCharge / 24
  haveI := T.weight_finite α
  have hv : W.vacuum ∈ W.toSuperNearVOA.gradingZ 0 := by
    simpa only [SuperNearVOA.gradingZ_apply, Int.cast_zero] using W.vacuum_mem
  change supertrace (T.twistedWeightParityGrading α)
      (T.insertedZeroModeBlock φ hW W.vacuum α) =
    supertrace (T.twistedWeightParityGrading α) (φ.weightBlock α)
  rw [insertedZeroModeBlock, T.twistedZeroModeAction_homogeneous hW α hv,
    T.twistedZeroModeBlock_vacuum, mul_one]

/-! ## Certified Type-II represented blocks -/

/-- The ordinary matrix-trace expression attached to an odd involution on one finite block. -/
noncomputable def queerTraceFormula (T : SuperTwistedModule W g N M) (α : ℂ)
    (ξ A : End ℂ (T.weight α)) : ℂ := by
  letI := T.weight_finite α
  exact (2 : ℂ)⁻¹ * LinearMap.trace ℂ (T.weight α) (ξ * A)

/-- A certified faithful representation of a concrete `Q(n)` inside a finite weight block.
The odd trace is only evaluated on this represented image.  The field `trace_formula` records
the usual realization by an odd involution `xi`; it is not asserted for arbitrary block
endomorphisms. -/
structure TwistedQueerBlockRepresentation (T : SuperTwistedModule W g N M) (α : ℂ) where
  size : ℕ
  size_pos : 0 < size
  representation : Queer (Fin size) →ₐ[ℂ] End ℂ (T.weight α)
  faithful : Function.Injective representation
  parity_compatible : ∀ (p : ZMod 2) (a : Queer (Fin size)),
    a ∈ Queer.parity p →
      IsParityHomogeneousEnd (T.twistedWeightParityGrading α) p (representation a)
  xi : End ℂ (T.weight α)
  xi_odd : IsParityHomogeneousEnd (T.twistedWeightParityGrading α) 1 xi
  xi_sq : xi * xi = 1
  trace_formula : ∀ a : Queer (Fin size),
    Queer.oddTrace a = T.queerTraceFormula α xi (representation a)

/-- Data saying that every inverse-inserted zero mode under consideration belongs to a
certified queer representation image.  The preimage is part of the data, so no arbitrary
extension of the odd trace to the full endomorphism algebra is chosen. -/
structure TwistedQueerTraceData (T : SuperTwistedModule W g N M)
    (φ : SuperTwistedIntertwiner T h) (hW : W.toSuperNearVOA.IntegralWeights) where
  block : ∀ α : ℂ, TwistedQueerBlockRepresentation T α
  preimage : ∀ α : ℂ, VType →ₗ[ℂ] Queer (Fin (block α).size)
  represents : ∀ (α : ℂ) (u : VType),
    (block α).representation (preimage α u) =
      φ.inverseWeightBlock α * T.twistedZeroModeAction hW α u
  preimage_parity : ∀ (α : ℂ) (p : ZMod 2) (k : ℤ) (u : VType),
    u ∈ W.toSuperNearVOA.gradingZ k → u ∈ W.parity p →
      preimage α u ∈ Queer.parity p

/-- The primary Type-II one-point function uses the `h`-oriented inverse insertion and the
concrete queer odd trace of its certified preimage. -/
noncomputable def twistedInverseOddOnePoint (T : SuperTwistedModule W g N M)
    (φ : SuperTwistedIntertwiner T h) (hW : W.toSuperNearVOA.IntegralWeights)
    (Θ : TwistedQueerTraceData T φ hW) : VType →ₗ[ℂ] FormalQSeries where
  toFun u e := Queer.oddTrace (Θ.preimage (e + W.centralCharge / 24) u)
  map_add' u v := by
    funext e
    rw [map_add, map_add]
    rfl
  map_smul' c u := by
    funext e
    rw [map_smul, map_smul]
    rfl

/-- The coefficient can equivalently be computed by the certified odd-involution trace formula
on the represented inverse-inserted action operator. -/
theorem twistedInverseOddOnePoint_apply_trace_formula
    (T : SuperTwistedModule W g N M) (φ : SuperTwistedIntertwiner T h)
    (hW : W.toSuperNearVOA.IntegralWeights) (Θ : TwistedQueerTraceData T φ hW)
    (u : VType) (e : ℂ) :
    T.twistedInverseOddOnePoint φ hW Θ u e =
      T.queerTraceFormula (e + W.centralCharge / 24)
        (Θ.block (e + W.centralCharge / 24)).xi
        (φ.inverseWeightBlock (e + W.centralCharge / 24) *
          T.twistedZeroModeAction hW (e + W.centralCharge / 24) u) := by
  change Queer.oddTrace (Θ.preimage (e + W.centralCharge / 24) u) = _
  rw [(Θ.block (e + W.centralCharge / 24)).trace_formula,
    Θ.represents]

/-- Cyclicity is asserted only for represented homogeneous queer elements. -/
theorem twistedQueerRepresented_koszul_cyclic
    (T : SuperTwistedModule W g N M) {α : ℂ}
    (R : TwistedQueerBlockRepresentation T α) {p q : ZMod 2}
    {a b : Queer (Fin R.size)} (ha : a ∈ Queer.parity p)
    (hb : b ∈ Queer.parity q) :
    Queer.oddTrace (a * b) = koszul p q * Queer.oddTrace (b * a) :=
  Queer.oddTrace_koszul_cyclic ha hb

/-- The represented products really are products of action operators. -/
theorem twistedQueerRepresentation_mul
    (T : SuperTwistedModule W g N M) {α : ℂ}
    (R : TwistedQueerBlockRepresentation T α) (a b : Queer (Fin R.size)) :
    R.representation (a * b) = R.representation a * R.representation b :=
  map_mul R.representation a b

/-! ## Coefficient-level sector cyclicity -/

/-- Supertrace with a chosen even inverse insertion, as a linear functional of a block
endomorphism. -/
noncomputable def inverseInsertedSupertraceLinear (T : SuperTwistedModule W g N M)
    (φ : SuperTwistedIntertwiner T h) (α : ℂ) : End ℂ (T.weight α) →ₗ[ℂ] ℂ := by
  letI := T.weight_finite α
  exact
    { toFun := fun A => supertrace (T.twistedWeightParityGrading α)
        (φ.inverseWeightBlock α * A)
      map_add' := fun A B => by rw [mul_add, supertrace_add]
      map_smul' := fun c A => by
        rw [Algebra.mul_smul_comm, supertrace_smul]
        rfl }

/-- Abstract finite-block cyclicity with inverse insertion.  The result is literally the
`twistedSuperCyclicCoeff` convention used by `hSupersymmetricFunctionals`. -/
theorem inverseInsertedSupertrace_cyclic
    (T : SuperTwistedModule W g N M) (φ : SuperTwistedIntertwiner T h) (α : ℂ)
    (p q : ZMod 2) (lam mu : ℂ) (A B : End ℂ (T.weight α))
    (hlam : lam ≠ 0) (hmu : mu ≠ 0)
    (hφEven : φ.parityDegree = 0)
    (hA : IsParityHomogeneousEnd (T.twistedWeightParityGrading α) p A)
    (hB : IsParityHomogeneousEnd (T.twistedWeightParityGrading α) q B)
    (hψA : φ.inverseWeightBlock α * A = lam⁻¹ • (A * φ.inverseWeightBlock α))
    (hψB : φ.inverseWeightBlock α * B = mu⁻¹ • (B * φ.inverseWeightBlock α)) :
    T.inverseInsertedSupertraceLinear φ α (A * B) =
      twistedSuperCyclicCoeff p q lam mu *
        T.inverseInsertedSupertraceLinear φ α (B * A) := by
  let P := T.twistedWeightParityGrading α
  let ψ := φ.inverseWeightBlock α
  haveI := T.weight_finite α
  have hψ : IsParityHomogeneousEnd P 0 ψ := by
    simpa only [hφEven] using φ.inverseWeightBlock_isParityHomogeneous α
  have hψAB : ψ * (A * B) = (lam * mu)⁻¹ • ((A * B) * ψ) := by
    rw [← mul_assoc, hψA, Algebra.smul_mul_assoc, mul_assoc, hψB,
      mul_smul_comm, smul_smul]
    congr 1
    rw [mul_inv_rev, mul_comm]
  by_cases hp : lam * mu = 1
  · have hBψ : B * ψ = mu • (ψ * B) := by
      calc
        B * ψ = (mu * mu⁻¹) • (B * ψ) := by rw [mul_inv_cancel₀ hmu, one_smul]
        _ = mu • (mu⁻¹ • (B * ψ)) := by rw [smul_smul]
        _ = mu • (ψ * B) := by rw [← hψB]
    have hmueq : mu = lam⁻¹ := eq_inv_of_mul_eq_one_right hp
    change supertrace P (ψ * (A * B)) = _
    rw [← mul_assoc]
    calc
      supertrace P ((ψ * A) * B) =
          koszul (0 + p) q * supertrace P (B * (ψ * A)) :=
        supertrace_mul_comm P (hψ.mul hA) hB
      _ = koszul p q * supertrace P (mu • (ψ * (B * A))) := by
        congr 1
        · simp
        · rw [← mul_assoc, hBψ, Algebra.smul_mul_assoc, mul_assoc]
      _ = (koszul p q * lam⁻¹) * supertrace P (ψ * (B * A)) := by
        rw [supertrace_smul, hmueq]
        ring
      _ = twistedSuperCyclicCoeff p q lam mu * supertrace P (ψ * (B * A)) := by
        rw [twistedSuperCyclicCoeff, if_pos hp]
  · have hcyc : supertrace P (ψ * (A * B)) = supertrace P ((A * B) * ψ) := by
      simpa using supertrace_mul_comm P hψ (hA.mul hB)
    have hzero : supertrace P (ψ * (A * B)) = 0 := by
      have heq : supertrace P (ψ * (A * B)) =
          (lam * mu)⁻¹ * supertrace P (ψ * (A * B)) := by
        calc
          supertrace P (ψ * (A * B)) =
              (lam * mu)⁻¹ * supertrace P ((A * B) * ψ) := by
            rw [hψAB, supertrace_smul]
          _ = (lam * mu)⁻¹ * supertrace P (ψ * (A * B)) := by rw [hcyc]
      have hcoef : 1 - (lam * mu)⁻¹ ≠ 0 :=
        sub_ne_zero.mpr (Ne.symm (inv_ne_one.mpr hp))
      have hz : (1 - (lam * mu)⁻¹) * supertrace P (ψ * (A * B)) = 0 := by
        rw [sub_mul, one_mul, sub_eq_zero]
        exact heq
      exact (mul_eq_zero.mp hz).resolve_left hcoef
    change supertrace P (ψ * (A * B)) = _
    rw [hzero, twistedSuperCyclicCoeff, if_neg hp, zero_mul]

/-- An `h`-eigen zero mode satisfies the required inverse-intertwiner relation on every finite
weight block. -/
theorem inverseWeightBlock_mul_twistedZeroModeBlock
    (T : SuperTwistedModule W g N M) (φ : SuperTwistedIntertwiner T h)
    {lam : ℂ} (hlam : lam ≠ 0) {k : ℤ} {u : VType}
    (huWeight : u ∈ W.toSuperNearVOA.gradingZ k) (huEig : h u = lam • u) (α : ℂ) :
    φ.inverseWeightBlock α * T.twistedZeroModeBlock u k huWeight α =
      lam⁻¹ • (T.twistedZeroModeBlock u k huWeight α * φ.inverseWeightBlock α) := by
  let A := T.twistedZeroModeBlock u k huWeight α
  let Φ := φ.weightBlock α
  let Ψ := φ.inverseWeightBlock α
  have hforward : Φ * A = lam • (A * Φ) := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change φ (T.act u (zeroModeLabel N k) (x : M)) =
      lam • T.act u (zeroModeLabel N k) (φ x)
    rw [φ.intertwines, huEig]
    change T.YM (lam • u) (zeroModeLabel N k) (φ x) = _
    rw [map_smul]
    rfl
  have hAΦ : A * Φ = lam⁻¹ • (Φ * A) := by
    calc
      A * Φ = (lam⁻¹ * lam) • (A * Φ) := by rw [inv_mul_cancel₀ hlam, one_smul]
      _ = lam⁻¹ • (lam • (A * Φ)) := by rw [smul_smul]
      _ = lam⁻¹ • (Φ * A) := by rw [← hforward]
  change Ψ * A = lam⁻¹ • (A * Ψ)
  calc
    Ψ * A = Ψ * A * (Φ * Ψ) := by rw [φ.weightBlock_mul_inverseWeightBlock, mul_one]
    _ = Ψ * (A * Φ) * Ψ := by simp only [mul_assoc]
    _ = Ψ * (lam⁻¹ • (Φ * A)) * Ψ := by rw [hAΦ]
    _ = lam⁻¹ • ((Ψ * Φ) * A * Ψ) := by
      rw [mul_smul_comm, Algebra.smul_mul_assoc]
      simp only [mul_assoc]
    _ = lam⁻¹ • (A * Ψ) := by rw [φ.inverseWeightBlock_mul_weightBlock, one_mul]

/-- Coefficient-level `h`-supersymmetry for two homogeneous eigenstate zero modes. -/
theorem inverseInsertedSupertrace_zeroModes_cyclic
    (T : SuperTwistedModule W g N M) (φ : SuperTwistedIntertwiner T h) (α : ℂ)
    (p q : ZMod 2) (lam mu : ℂ) {a b : VType} {ka kb : ℤ}
    (hlam : lam ≠ 0) (hmu : mu ≠ 0)
    (hφEven : φ.parityDegree = 0)
    (haWeight : a ∈ W.toSuperNearVOA.gradingZ ka)
    (hbWeight : b ∈ W.toSuperNearVOA.gradingZ kb)
    (haParity : a ∈ W.parity p) (hbParity : b ∈ W.parity q)
    (haEig : h a = lam • a) (hbEig : h b = mu • b) :
    T.inverseInsertedSupertraceLinear φ α
        (T.twistedZeroModeBlock a ka haWeight α * T.twistedZeroModeBlock b kb hbWeight α) =
      twistedSuperCyclicCoeff p q lam mu * T.inverseInsertedSupertraceLinear φ α
        (T.twistedZeroModeBlock b kb hbWeight α *
          T.twistedZeroModeBlock a ka haWeight α) := by
  apply T.inverseInsertedSupertrace_cyclic φ α p q lam mu _ _ hlam hmu hφEven
  · exact T.twistedZeroModeBlock_isParityHomogeneous haParity ka haWeight α
  · exact T.twistedZeroModeBlock_isParityHomogeneous hbParity kb hbWeight α
  · exact T.inverseWeightBlock_mul_twistedZeroModeBlock φ hlam haWeight haEig α
  · exact T.inverseWeightBlock_mul_twistedZeroModeBlock φ hmu hbWeight hbEig α

/-! ## The formal `T^N` sector label -/

/-- All occurring module weights lie in one `1/N`-spaced coset.  This is explicit extra
positive-energy spectrum data; it is not silently built into `SuperTwistedModule`. -/
def HasTwistedConformalWeight (T : SuperTwistedModule W g N M) (β : ℂ) : Prop :=
  T.weight β ≠ ⊥ ∧ ∀ α : ℂ, T.weight α ≠ ⊥ →
    ∃ n : ℤ, α = β + (n : ℂ) / N

/-- The coefficient action corresponding formally to `tau |-> tau + N`.  It is kept separate
from analytic evaluation. -/
noncomputable def qShiftN (N : ℕ) (χ : FormalQSeries) : FormalQSeries := fun e =>
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (N : ℂ) * e) * χ e

/-- A supertrace coefficient on a zero weight block vanishes. -/
theorem twistedSuperOnePoint_apply_eq_zero_of_weight_eq_bot
    (T : SuperTwistedModule W g N M) (φ : SuperTwistedIntertwiner T h)
    (hW : W.toSuperNearVOA.IntegralWeights) (u : VType) (e : ℂ)
    (hz : T.weight (e + W.centralCharge / 24) = ⊥) :
    T.twistedSuperOnePoint φ hW u e = 0 := by
  let α := e + W.centralCharge / 24
  letI := T.weight_finite α
  change supertrace (T.twistedWeightParityGrading α)
      (T.insertedZeroModeBlock φ hW u α) = 0
  have hblock : T.insertedZeroModeBlock φ hW u α = 0 := by
    apply LinearMap.ext
    intro x
    have hxbot : (x : M) ∈ (⊥ : Submodule ℂ M) := by
      rw [← hz]
      exact x.2
    have hx : (x : M) = 0 := by simpa using hxbot
    have hxsub : x = 0 := Subtype.ext hx
    rw [hxsub, map_zero]
    rfl
  rw [hblock]
  simpa [supertrace]

/-- Under a single `1/N`-spaced weight coset, the formal one-point series is an eigenvector for
the coefficient action of `T^N`.  This is only a sector-label law, not modularity. -/
theorem twistedSuperOnePoint_qShiftN
    (T : SuperTwistedModule W g N M) (φ : SuperTwistedIntertwiner T h)
    (hW : W.toSuperNearVOA.IntegralWeights) (β : ℂ)
    (hβ : T.HasTwistedConformalWeight β) (u : VType) :
    qShiftN N (T.twistedSuperOnePoint φ hW u) =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (N : ℂ) *
        (β - W.centralCharge / 24)) • T.twistedSuperOnePoint φ hW u := by
  funext e
  simp only [qShiftN, Pi.smul_apply, smul_eq_mul]
  by_cases hz : T.weight (e + W.centralCharge / 24) = ⊥
  · rw [T.twistedSuperOnePoint_apply_eq_zero_of_weight_eq_bot φ hW u e hz,
      mul_zero, mul_zero]
  · obtain ⟨n, hn⟩ := hβ.2 _ hz
    have he : e = (β - W.centralCharge / 24) + (n : ℂ) / N := by
      have hN : (N : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt T.order_pos
      field_simp [hN] at hn ⊢
      linear_combination hn
    rw [he]
    have hexp : Complex.exp
        (2 * (Real.pi : ℂ) * Complex.I * (N : ℂ) *
          ((β - W.centralCharge / 24) + (n : ℂ) / N)) =
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (N : ℂ) *
          (β - W.centralCharge / 24)) := by
      have hN : (N : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt T.order_pos
      rw [show 2 * (Real.pi : ℂ) * Complex.I * (N : ℂ) *
            ((β - W.centralCharge / 24) + (n : ℂ) / N) =
          2 * (Real.pi : ℂ) * Complex.I * (N : ℂ) *
              (β - W.centralCharge / 24) +
            (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by field_simp [hN],
        Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    rw [hexp]

end SuperTwistedModule

/-! ## Identity-twist compatibility -/

namespace SuperOrdVModule

variable {A : SuperOrdVModule W M}

/-- The tautological lift of the identity automorphism to the identity-twisted carrier. -/
noncomputable def identityTwistedIntertwiner (A : SuperOrdVModule W M) :
    SuperTwistedIntertwiner A.toIdentityTwist (1 : SuperAut W) where
  commutes := by simp
  toLinearEquiv := LinearEquiv.refl ℂ M
  parityDegree := 0
  map_parity' := fun _ _ => by simp
  map_weight' := fun _ _ => Iff.rfl
  intertwines := by
    intro u k x
    simp only [LinearEquiv.refl_apply, SuperAut.one_apply]

@[simp] theorem identityTwistedIntertwiner_apply (A : SuperOrdVModule W M) (x : M) :
    A.identityTwistedIntertwiner x = x := by
  simp [identityTwistedIntertwiner]

@[simp] theorem identityTwistedIntertwiner_weightBlock
    (A : SuperOrdVModule W M) (α : ℂ) :
    A.identityTwistedIntertwiner.weightBlock α = 1 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  simp [identityTwistedIntertwiner, SuperTwistedIntertwiner.weightBlock]

/-- The inherited parity subspaces in the identity-twisted block are definitionally the
ordinary module block parities. -/
theorem toIdentityTwist_twistedWeightParity (A : SuperOrdVModule W M)
    (α : ℂ) (p : ZMod 2) :
    A.toIdentityTwist.twistedWeightParity α p = A.weightParity α p := rfl

/-- The two packaged block parity gradings agree; the internality witnesses are propositions and
therefore do not introduce extra data. -/
theorem toIdentityTwist_twistedWeightParityGrading (A : SuperOrdVModule W M) (α : ℂ) :
    A.toIdentityTwist.twistedWeightParityGrading α = A.weightParityGrading α := by
  cases hP : A.toIdentityTwist.twistedWeightParityGrading α with
  | mk p hp =>
    cases hQ : A.weightParityGrading α with
    | mk q hq =>
      have hpq : p = q := by
        funext r
        calc
          p r = (A.toIdentityTwist.twistedWeightParityGrading α).parity r :=
            (congrArg (fun P => P.parity r) hP).symm
          _ = (A.weightParityGrading α).parity r :=
            A.toIdentityTwist_twistedWeightParity α r
          _ = q r := congrArg (fun P => P.parity r) hQ
      subst q
      rfl

/-- On an integral homogeneous state, the identity-twisted zero-mode block is the ordinary
zero-mode block. -/
theorem toIdentityTwist_twistedZeroModeBlock (A : SuperOrdVModule W M)
    {k : ℤ} {u : VType} (hu : u ∈ W.toSuperNearVOA.gradingZ k) (α : ℂ) :
    A.toIdentityTwist.twistedZeroModeBlock u k hu α =
      A.zeroModeBlock u (k - 1) (mem_zeroModeWeight_of_mem_gradingZ hu) α := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change A.act u (SuperTwistedModule.zeroModeLabel 1 k) x = A.act u (k - 1) x
  rw [show SuperTwistedModule.zeroModeLabel 1 k = k - 1 by
    simp [SuperTwistedModule.zeroModeLabel]]

/-- The ordinary block-valued global zero-mode action, packaged as a linear map for comparison
with its identity-twisted counterpart. -/
noncomputable def ordinaryZeroModeAction (A : SuperOrdVModule W M)
    (hW : W.toSuperNearVOA.IntegralWeights) (α : ℂ) :
    VType →ₗ[ℂ] End ℂ (A.weight α) where
  toFun u := A.superOModWeightBlock hW u α
  map_add' := fun u v => A.superOModWeightBlock_add hW u v α
  map_smul' := fun c u => A.superOModWeightBlock_smul hW c u α

/-- Identity-twisted and ordinary global zero-mode actions agree. -/
theorem toIdentityTwist_twistedZeroModeAction (A : SuperOrdVModule W M)
    (hW : W.toSuperNearVOA.IntegralWeights) (α : ℂ) :
    A.toIdentityTwist.twistedZeroModeAction hW α = A.ordinaryZeroModeAction hW α := by
  apply LinearMap.ext
  intro u
  have hu : u ∈ Submodule.span ℂ {x : VType | W.toSuperNearVOA.IsHomogZ x} := by
    rw [W.toSuperNearVOA.span_isHomogZ_eq_top hW]
    trivial
  refine Submodule.span_induction
    (p := fun u _ => A.toIdentityTwist.twistedZeroModeAction hW α u =
      A.ordinaryZeroModeAction hW α u) ?_ ?_ ?_ ?_ hu
  · rintro x ⟨k, hk⟩
    rw [A.toIdentityTwist.twistedZeroModeAction_homogeneous hW α hk,
      A.toIdentityTwist_twistedZeroModeBlock hk,
      show A.ordinaryZeroModeAction hW α x = A.superOModWeightBlock hW x α from rfl,
      A.superOModWeightBlock_of_mem_gradingZ hW hk]
  · simp only [map_zero]
    rfl
  · intro x y _ _ hx hy
    simpa using congrArg₂ (· + ·) hx hy
  · intro c x _ hx
    simpa using congrArg (fun z => c • z) hx

/-- The identity-twist, identity-insertion construction is exactly the
ordinary-sector formal torus one-point supertrace. -/
theorem twistedSuperOnePoint_identity (A : SuperOrdVModule W M)
    (hW : W.toSuperNearVOA.IntegralWeights) :
    A.toIdentityTwist.twistedSuperOnePoint A.identityTwistedIntertwiner hW =
      A.superTorusOnePoint hW := by
  apply LinearMap.ext
  intro u
  funext e
  let α := e + W.centralCharge / 24
  letI htw : FiniteDimensional ℂ (A.toIdentityTwist.weight α) :=
    A.toIdentityTwist.weight_finite α
  letI hord : FiniteDimensional ℂ (A.weight α) := A.weight_finite α
  change supertrace (A.toIdentityTwist.twistedWeightParityGrading α)
      (A.identityTwistedIntertwiner.weightBlock α *
        A.toIdentityTwist.twistedZeroModeAction hW α u) =
    supertrace (A.weightParityGrading α) (A.superOModWeightBlock hW u α)
  rw [A.identityTwistedIntertwiner_weightBlock, one_mul,
    A.toIdentityTwist_twistedWeightParityGrading,
    A.toIdentityTwist_twistedZeroModeAction]
  rfl

end SuperOrdVModule

end VOA
