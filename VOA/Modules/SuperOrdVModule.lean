/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modules.SuperWeakModule
import VOA.Modules.ZeroModeMult
import VOA.Modularity.SuperTrace
import VOA.Core.SuperNearVOA

/-!
# Grading-restricted ordinary modules over a super VOA

`SuperOrdVModule W M` is the semisimple, grading-restricted module notion needed by the
rational and logarithmic super-modularity rows.  It consists of a `SuperWeakModule` together
with an internal complex conformal-weight grading, finite-dimensional weight pieces, a global
lower bound, diagonal `L₀`, and the exact homogeneous mode shift

`u_(n) : M_α → M_(α+h-n-1)` for `u ∈ W_h`.

Weight and parity remain independent.  In particular there is no spin--statistics field and no
field saying that either grading determines the other.  Nevertheless, because the conformal
vector is even, `L₀` preserves parity.  The two internal decompositions consequently restrict
to an internal parity decomposition on every weight space; this is proved below and supplies the
basis-independent finite-block supertrace.

## The van Ekeren mode-index bend

This file deliberately does **not** define an adjoint `SuperOrdVModule` for a general
nonintegrally graded super VOA.  The repository's algebraic state fields have integer-labelled
modes, while the identity/twisted-sector convention in van Ekeren's modularity theorem assigns
allowed Fourier indices using the automorphism eigenvalue and the conformal-weight class.  A
nonintegral state therefore cannot silently be assigned an integer zero-mode `h-1`.  The
algebraic self-action remains available as `SuperNearVOA.adjointSuperWeakModule`, but placing it
in an analytic identity-twisted ordinary sector requires the relevant mode-lattice datum.

For the same reason the zero-mode supertrace below takes an explicit integer `n` and the exact
hypothesis `u ∈ W_(n+1)`.  No rounding or hidden choice of a mode is made.

## Status

All declarations in this file are proved from the imported foundations; it introduces no axiom.
-/

namespace VOA

open Module (End)
open scoped BigOperators

universe u v

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- A grading-restricted ordinary module over a super VOA.  The parity grading belongs to the
underlying `SuperWeakModule`; the conformal-weight grading is additional, independent data. -/
structure SuperOrdVModule (W : SuperVertexOperatorAlgebra 𝒱) (M : Type v)
    [AddCommGroup M] [Module ℂ M]
    extends SuperWeakModule W.toSuperVertexAlgebra M where
  /-- The complex conformal-weight grading `M = ⊕_α M_α`. -/
  weight : ℂ → Submodule ℂ M
  /-- The weight grading is an internal direct sum. -/
  weight_isInternal : DirectSum.IsInternal weight
  /-- `L₀` acts by the conformal weight on each homogeneous piece. -/
  L0_weight : ∀ (α : ℂ) (x : M), x ∈ weight α →
    mode (YM W.conformalVector) 1 x = α • x
  /-- Every conformal-weight piece is finite-dimensional. -/
  weight_finite : ∀ α, FiniteDimensional ℂ (weight α)
  /-- The real parts of occurring conformal weights have a global lower bound. -/
  boundedBelow : ∃ B : ℝ, ∀ α : ℂ, weight α ≠ ⊥ → B ≤ α.re
  /-- Exact homogeneous mode shift, with weight and parity kept logically independent. -/
  weight_mode : ∀ {h α : ℂ} (u : 𝒱), u ∈ W.grading h →
    ∀ (x : M), x ∈ weight α → ∀ (n : ℤ),
      mode (YM u) n x ∈ weight (α + h - n - 1)

namespace SuperOrdVModule

variable {W : SuperVertexOperatorAlgebra 𝒱} {M : Type v}
  [AddCommGroup M] [Module ℂ M]

/-- The module action in the graded super-module API. -/
def act (N : SuperOrdVModule W M) (u : 𝒱) (n : ℤ) (x : M) : M :=
  N.toSuperWeakModule.act u n x

@[simp] theorem act_def (N : SuperOrdVModule W M) (u : 𝒱) (n : ℤ) (x : M) :
    N.act u n x = mode (N.YM u) n x := rfl

/-- The parity grading, packaged independently of the weight grading. -/
def toParityGrading (N : SuperOrdVModule W M) : ParityGrading M where
  parity := N.parity
  isInternal := N.parity_isInternal

@[simp] theorem toParityGrading_parity (N : SuperOrdVModule W M) (p : ZMod 2) :
    N.toParityGrading.parity p = N.parity p := rfl

/-- A homogeneous mode has exactly the declared weight shift. -/
theorem act_weight {h α : ℂ} (N : SuperOrdVModule W M) {u : 𝒱}
    (hu : u ∈ W.grading h) {x : M} (hx : x ∈ N.weight α) (n : ℤ) :
    N.act u n x ∈ N.weight (α + h - n - 1) :=
  N.weight_mode u hu x hx n

/-- A homogeneous mode has the parity of its state. -/
theorem act_parity {p q : ZMod 2} (N : SuperOrdVModule W M) {u : 𝒱}
    (hu : u ∈ W.parity p) {x : M} (hx : x ∈ N.parity q) (n : ℤ) :
    N.act u n x ∈ N.parity (p + q) :=
  N.parity_mode u hu x hx n

/-- On `M_α`, `L₀` acts by `α`. -/
theorem L0_eq_weight (N : SuperOrdVModule W M) {α : ℂ} {x : M}
    (hx : x ∈ N.weight α) : mode (N.YM W.conformalVector) 1 x = α • x :=
  N.L0_weight α x hx

/-! ## Weight membership of `L₀` eigenvectors -/

/-- An `L₀` eigenvector belongs to the weight space with that eigenvalue.  This proves that
the carried internal grading is the eigenspace grading, rather than merely a family of
eigensubspaces. -/
theorem eigenvector_mem_weight (N : SuperOrdVModule W M) {γ : ℂ} {y : M}
    (hy : mode (N.YM W.conformalVector) 1 y = γ • y) : y ∈ N.weight γ := by
  classical
  letI := DirectSum.IsInternal.chooseDecomposition N.weight N.weight_isInternal
  set c : ℂ → M := fun j => ((DirectSum.decompose N.weight y j : N.weight j) : M) with hc
  set s : Finset ℂ := (DirectSum.decompose N.weight y).support with hs
  have hdecomp : (∑ j ∈ s, c j) = y := DirectSum.sum_support_decompose N.weight y
  have hL0comp : ∀ j : ℂ, mode (N.YM W.conformalVector) 1 (c j) = j • c j := fun j =>
    N.L0_weight j _ (DirectSum.decompose N.weight y j).2
  have hzero : (∑ j ∈ s, ((j - γ) • c j)) = 0 := by
    have hLHS : (∑ j ∈ s, ((j - γ) • c j)) =
        mode (N.YM W.conformalVector) 1 y - γ • y := by
      rw [← hdecomp, map_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [hL0comp j, sub_smul]
    rw [hLHS, hy, sub_self]
  have hmem : ∀ j : ℂ, ((j - γ) • c j) ∈ N.weight j := fun j =>
    (N.weight j).smul_mem _ (DirectSum.decompose N.weight y j).2
  have hcvanish : ∀ j ∈ s, j ≠ γ → c j = 0 := by
    intro j hjs hjγ
    have hdz : (DirectSum.decompose N.weight (∑ k ∈ s, ((k - γ) • c k)) j : N.weight j)
        = (0 : N.weight j) := by
      rw [hzero, DirectSum.decompose_zero, DirectSum.zero_apply]
    have hcomp : ((DirectSum.decompose N.weight (∑ k ∈ s, ((k - γ) • c k)) j :
        N.weight j) : M) = (0 : M) := by rw [hdz, ZeroMemClass.coe_zero]
    rw [DirectSum.decompose_sum, DirectSum.sum_apply, AddSubmonoidClass.coe_finsetSum,
      Finset.sum_eq_single j (fun k hks hkj => ?_) (fun hjns => ?_)] at hcomp
    · rw [DirectSum.decompose_of_mem_same N.weight (hmem j)] at hcomp
      have hne : (j - γ) ≠ 0 := sub_ne_zero.mpr hjγ
      exact (smul_eq_zero.mp hcomp).resolve_left hne
    · rw [DirectSum.decompose_of_mem_ne N.weight (hmem k) hkj]
    · exact absurd hjs hjns
  have hyeq : y = c γ := by
    rw [← hdecomp]
    by_cases hγs : γ ∈ s
    · rw [Finset.sum_eq_single γ (fun k hks hkγ => hcvanish k hks hkγ)
        (fun h => absurd hγs h)]
    · have hcγ0 : c γ = 0 := by
        rw [hc]
        simp only
        have : DirectSum.decompose N.weight y γ = 0 := by
          rw [← DFinsupp.notMem_support_iff]
          exact hγs
        rw [this, ZeroMemClass.coe_zero]
      rw [hcγ0, Finset.sum_eq_zero
        (fun k hks => hcvanish k hks (fun h => hγs (h ▸ hks)))]
  rw [hyeq, hc]
  exact (DirectSum.decompose N.weight y γ).2

/-! ## The parity grading on a finite weight block -/

/-- Since the conformal vector is even, `L₀` preserves every parity component. -/
theorem L0_mem_parity (N : SuperOrdVModule W M) {q : ZMod 2} {x : M}
    (hx : x ∈ N.parity q) : mode (N.YM W.conformalVector) 1 x ∈ N.parity q := by
  have h := N.parity_mode W.conformalVector W.conformal_parity x hx 1
  simpa using h

/-- The parity projection determined by the internal parity decomposition. -/
noncomputable def parityProj (N : SuperOrdVModule W M) (p : ZMod 2) : End ℂ M :=
  letI := DirectSum.IsInternal.chooseDecomposition N.parity N.parity_isInternal
  homogProj N.parity p

/-- The parity projection of a weight vector has the same weight. -/
theorem parityProj_mem_weight (N : SuperOrdVModule W M) (p : ZMod 2)
    {α : ℂ} {x : M} (hx : x ∈ N.weight α) : N.parityProj p x ∈ N.weight α := by
  letI := DirectSum.IsInternal.chooseDecomposition N.parity N.parity_isInternal
  change homogProj N.parity p x ∈ N.weight α
  apply N.eigenvector_mem_weight
  have hcomm := homogProj_comm N.parity (mode (N.YM W.conformalVector) 1)
    (fun q y hy => N.L0_mem_parity hy) p x
  calc
    mode (N.YM W.conformalVector) 1 (homogProj N.parity p x)
        = homogProj N.parity p (mode (N.YM W.conformalVector) 1 x) := hcomm.symm
    _ = homogProj N.parity p (α • x) := by rw [N.L0_weight α x hx]
    _ = α • homogProj N.parity p x := map_smul _ _ _

/-- The parity-`p` part of a fixed weight space. -/
def weightParity (N : SuperOrdVModule W M) (α : ℂ) (p : ZMod 2) :
    Submodule ℂ (N.weight α) :=
  (N.parity p).comap (N.weight α).subtype

@[simp] theorem mem_weightParity (N : SuperOrdVModule W M) {α : ℂ} {p : ZMod 2}
    {x : N.weight α} : x ∈ N.weightParity α p ↔ (x : M) ∈ N.parity p := Iff.rfl

/-- Each weight space inherits an internal parity decomposition.  This is a theorem from evenness
of `L₀`, not a spin--statistics or weight/parity compatibility field. -/
theorem weightParity_isInternal (N : SuperOrdVModule W M) (α : ℂ) :
    DirectSum.IsInternal (N.weightParity α) := by
  letI := DirectSum.IsInternal.chooseDecomposition N.parity N.parity_isInternal
  exact isInternal_comap N.parity (N.weight α)
    (fun p x hx => by simpa [parityProj] using N.parityProj_mem_weight p hx)

/-- The basis-independent parity grading on the finite block `M_α`. -/
def weightParityGrading (N : SuperOrdVModule W M) (α : ℂ) :
    ParityGrading (N.weight α) where
  parity := N.weightParity α
  isInternal := N.weightParity_isInternal α

/-! ## Formal block supertraces -/

/-- The restriction of an explicitly integral homogeneous zero mode to a weight block.
The hypothesis says exactly that `n = wt(u)-1`; it is intentionally part of the interface. -/
noncomputable def zeroModeBlock (N : SuperOrdVModule W M) (u : 𝒱) (n : ℤ)
    (huWeight : u ∈ W.grading ((n : ℂ) + 1)) (α : ℂ) : End ℂ (N.weight α) where
  toFun x := ⟨N.act u n x, by
    have h := N.act_weight huWeight x.2 n
    simpa only [show α + ((n : ℂ) + 1) - n - 1 = α by ring] using h⟩
  map_add' x y := Subtype.ext (N.toSuperWeakModule.act_add_right u n x y)
  map_smul' c x := Subtype.ext (N.toSuperWeakModule.act_smul_right u c n x)

@[simp] theorem zeroModeBlock_apply_coe (N : SuperOrdVModule W M) (u : 𝒱) (n : ℤ)
    (huWeight : u ∈ W.grading ((n : ℂ) + 1)) (α : ℂ) (x : N.weight α) :
    ((N.zeroModeBlock u n huWeight α x : N.weight α) : M) = N.act u n x := rfl

/-- The zero-mode block has the parity of the inserted state. -/
theorem zeroModeBlock_isParityHomogeneous (N : SuperOrdVModule W M)
    {p : ZMod 2} {u : 𝒱} (huParity : u ∈ W.parity p) (n : ℤ)
    (huWeight : u ∈ W.grading ((n : ℂ) + 1)) (α : ℂ) :
    IsParityHomogeneousEnd (N.weightParityGrading α) p
      (N.zeroModeBlock u n huWeight α) := by
  intro q x hx
  change N.act u n (x : M) ∈ N.parity (p + q)
  exact N.act_parity huParity hx n

/-- The formal one-point **supertrace** of an explicitly integral homogeneous zero mode.
The coefficient at exponent `e` is the basis-independent supertrace on
`M_(e+c/24)`.  Both the conformal zero-mode and parity hypotheses are explicit. -/
noncomputable def zeroModeSupertrace (N : SuperOrdVModule W M)
    {p : ZMod 2} (u : 𝒱) (n : ℤ)
    (huWeight : u ∈ W.grading ((n : ℂ) + 1)) (_huParity : u ∈ W.parity p) :
    FormalQSeries :=
  fun e =>
    let α := e + W.centralCharge / 24
    haveI := N.weight_finite α
    supertrace (N.weightParityGrading α) (N.zeroModeBlock u n huWeight α)

/-- Odd zero modes have identically zero ordinary supertrace.  Their Type-II replacement is the
odd trace model, not an ordinary supertrace disguised as a new character. -/
theorem zeroModeSupertrace_eq_zero_of_odd (N : SuperOrdVModule W M)
    {u : 𝒱} (n : ℤ) (huWeight : u ∈ W.grading ((n : ℂ) + 1))
    (huParity : u ∈ W.parity 1) :
    N.zeroModeSupertrace u n huWeight huParity = 0 := by
  funext e
  let α := e + W.centralCharge / 24
  haveI := N.weight_finite α
  exact supertrace_eq_zero_of_odd _
    (N.zeroModeBlock_isParityHomogeneous huParity n huWeight α)

/-- The formal supercharacter: the block supertrace of the identity, including the usual
`-c/24` exponent shift. -/
noncomputable def formalSupercharacter (N : SuperOrdVModule W M) : FormalQSeries :=
  fun e =>
    let α := e + W.centralCharge / 24
    haveI := N.weight_finite α
    supertrace (N.weightParityGrading α) LinearMap.id

/-- The vacuum has the integral zero-mode index `-1`. -/
theorem vacuum_mem_zeroModeWeight :
    W.vacuum ∈ W.grading (((-1 : ℤ) : ℂ) + 1) := by
  simpa using W.vacuum_mem

/-- The vacuum zero-mode block is the identity on every weight space. -/
theorem zeroModeBlock_vacuum (N : SuperOrdVModule W M) (α : ℂ) :
    N.zeroModeBlock W.vacuum (-1) vacuum_mem_zeroModeWeight α = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact N.toSuperWeakModule.act_vacuum (-1) x

/-- The formal supercharacter is the zero-mode supertrace with vacuum insertion. -/
theorem zeroModeSupertrace_vacuum (N : SuperOrdVModule W M) :
    N.zeroModeSupertrace W.vacuum (-1) vacuum_mem_zeroModeWeight W.vacuum_parity =
      N.formalSupercharacter := by
  funext e
  let α := e + W.centralCharge / 24
  haveI := N.weight_finite α
  change supertrace (N.weightParityGrading α)
    (N.zeroModeBlock W.vacuum (-1) vacuum_mem_zeroModeWeight α) =
      supertrace (N.weightParityGrading α) LinearMap.id
  rw [N.zeroModeBlock_vacuum α]

end SuperOrdVModule

/-! ## Bosonic compatibility -/

namespace OrdVModule

variable {W : VertexOperatorAlgebra 𝒱} {M : Type u}
  [AddCommGroup M] [Module ℂ M]

/-- A bosonic ordinary module is a super ordinary module with purely even parity. -/
noncomputable def toSuper (N : OrdVModule W M) : SuperOrdVModule W.toSuper M where
  toSuperWeakModule := N.toWeakModule.toSuper
  weight := N.weight
  weight_isInternal := N.isInternal
  L0_weight := N.L0_weight
  weight_finite := N.finrank
  boundedBelow := N.boundedBelow
  weight_mode := by
    intro h α u hu x hx n
    classical
    by_cases hh : ∃ k : ℤ, (k : ℂ) = h
    · obtain ⟨k, rfl⟩ := hh
      have hu' : u ∈ W.grading k := by
        simpa [VertexOperatorAlgebra.toSuper, PreVertexAlgebra.toSuper,
          PreVertexAlgebra.gradingC_intCast] using hu
      simpa using (VOA.mode_mem_weight N hu' hx n)
    · have hu0 : u = 0 := by
        have hbot : W.toPreVertexAlgebra.gradingC h = ⊥ :=
          W.toPreVertexAlgebra.gradingC_of_not_int hh
        have : u ∈ (⊥ : Submodule ℂ 𝒱) := by
          simpa [VertexOperatorAlgebra.toSuper, PreVertexAlgebra.toSuper, hbot] using hu
        simpa using this
      subst hu0
      change mode (N.YM (0 : 𝒱)) n x ∈ N.weight (α + h - n - 1)
      rw [map_zero]
      exact Submodule.zero_mem _

@[simp] theorem toSuper_weight (N : OrdVModule W M) (α : ℂ) :
    N.toSuper.weight α = N.weight α := rfl

/-- On a bosonic module, the odd part of every induced weight-block parity grading is zero. -/
theorem toSuper_weightParityGrading_odd (N : OrdVModule W M) (α : ℂ) :
    (N.toSuper.weightParityGrading α).parity 1 = ⊥ := by
  ext x
  change (x : M) ∈ (ParityGrading.even M).parity 1 ↔ x ∈ (⊥ :
    Submodule ℂ (N.toSuper.weight α))
  rw [ParityGrading.even_parity_of_ne (by decide), Submodule.mem_bot, Submodule.mem_bot,
    ZeroMemClass.coe_eq_zero]

/-- The supercharacter of a purely even module is the ordinary graded dimension. -/
theorem formalSupercharacter_toSuper (N : OrdVModule W M) :
    N.toSuper.formalSupercharacter = gradedDim N := by
  funext e
  let α := e + W.centralCharge / 24
  haveI := N.toSuper.weight_finite α
  change supertrace (N.toSuper.weightParityGrading α) LinearMap.id =
    (Module.finrank ℂ (N.toSuper.weight α) : ℂ)
  rw [supertrace_eq_trace_of_odd_eq_bot _ (N.toSuper_weightParityGrading_odd α),
    LinearMap.trace_id]

end OrdVModule

end VOA
