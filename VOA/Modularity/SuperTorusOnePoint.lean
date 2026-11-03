/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli and Fedor K. Popov
-/
import VOA.Modularity.SuperFormalBlock
import VOA.Modularity.ZhuBlockConditions

/-!
# Formal torus one-point supertraces

This file assembles the homogeneous zero-mode supertraces of `SuperOrdVModule` into a genuine
global complex-linear map.  The construction is possible for an integral-weight super VOA:
`gradingZ` is then an internal direct sum, so the global zero mode is the finite direct-sum
linear extension of

`u in V_k |-> u_(k-1)`.

The parity grading is independent of conformal weight.  The only sign-bearing result here is the
odd-vanishing theorem: the weight projections preserve parity, hence the global zero mode of an
odd state is an odd endomorphism on every finite weight block, whose ordinary supertrace is zero.
No two states are interchanged in the construction itself.

For a general super module the corresponding recursion requires the super version of the long
graded-trace calculation in
`GradedTrace`--`ZhuBlockConditions`: q-shifted *Koszul* cyclicity for products of module modes,
followed by the super Jacobi expansion and the Lambert/Eisenstein resummation.  The present module
API supplies the required homogeneous Jacobi identity and finite-block Koszul cyclicity, but that
calculation is only started in `SuperTorusRecursion`; the signed iterate expansion and resummation
reach the signed geometric telescope.  Specializing its supercommutator terms to zero modes
and performing the divisor/Lambert--Eisenstein resummation remain residual.  No recursion
hypothesis is bundled here as substitute data.
-/

namespace VOA

open Module (End)

set_option autoImplicit false

universe u v

variable {VType : Type u} [AddCommGroup VType] [Module ℂ VType]
variable {W : SuperVertexOperatorAlgebra VType}
variable {M : Type v} [AddCommGroup M] [Module ℂ M]

namespace SuperOrdVModule

/-- The conformal zero-mode operator on one integral homogeneous state-space summand. -/
noncomputable def superOModFamily (N : SuperOrdVModule W M) (k : ℤ) :
    (W.toSuperNearVOA.gradingZ k) →ₗ[ℂ] End ℂ M :=
  (modeLinear (k - 1)).comp (N.YM.comp (W.toSuperNearVOA.gradingZ k).subtype)

/-- The global zero mode `o(u)`, assembled linearly from the finite integral-weight
decomposition of `u`. -/
noncomputable def superOMod (N : SuperOrdVModule W M)
    (hW : W.toSuperNearVOA.IntegralWeights) : VType →ₗ[ℂ] End ℂ M :=
  letI := DirectSum.IsInternal.chooseDecomposition W.toSuperNearVOA.gradingZ
    (W.toSuperNearVOA.gradingZ_isInternal hW)
  (DFinsupp.lsum ℂ (N.superOModFamily)).comp
    (DirectSum.decomposeLinearEquiv W.toSuperNearVOA.gradingZ).toLinearMap

/-- On an integral homogeneous vector, the assembled operator is the expected single mode. -/
theorem superOMod_of_mem_gradingZ (N : SuperOrdVModule W M)
    (hW : W.toSuperNearVOA.IntegralWeights) {k : ℤ} {u : VType}
    (hu : u ∈ W.toSuperNearVOA.gradingZ k) :
    N.superOMod hW u = mode (N.YM u) (k - 1) := by
  letI := DirectSum.IsInternal.chooseDecomposition W.toSuperNearVOA.gradingZ
    (W.toSuperNearVOA.gradingZ_isInternal hW)
  have hcollapse : N.superOMod hW u = N.superOModFamily k ⟨u, hu⟩ := by
    change (DFinsupp.lsum ℂ N.superOModFamily)
      (DirectSum.decompose W.toSuperNearVOA.gradingZ u) = _
    rw [DirectSum.decompose_of_mem W.toSuperNearVOA.gradingZ hu]
    exact DFinsupp.lsum_single ℂ N.superOModFamily k ⟨u, hu⟩
  rw [hcollapse]
  rfl

/-- The mode index `k-1` is the conformal zero-mode index for a weight-`k` state. -/
theorem mem_zeroModeWeight_of_mem_gradingZ {k : ℤ} {u : VType}
    (hu : u ∈ W.toSuperNearVOA.gradingZ k) :
    u ∈ W.grading ((((k - 1 : ℤ) : ℂ) + 1)) := by
  rw [show (((k - 1 : ℤ) : ℂ) + 1) = (k : ℂ) by push_cast; ring]
  exact hu

/-- The diagonal block of a global super zero-mode operator on `M_alpha`. -/
noncomputable def superOModWeightBlock (N : SuperOrdVModule W M)
    (hW : W.toSuperNearVOA.IntegralWeights) (u : VType) (α : ℂ) :
    End ℂ (N.weight α) :=
  (internalProjTo N.weight_isInternal α).comp
    ((N.superOMod hW u).comp (N.weight α).subtype)

@[simp] theorem superOModWeightBlock_add (N : SuperOrdVModule W M)
    (hW : W.toSuperNearVOA.IntegralWeights) (u v : VType) (α : ℂ) :
    N.superOModWeightBlock hW (u + v) α =
      N.superOModWeightBlock hW u α + N.superOModWeightBlock hW v α := by
  apply LinearMap.ext
  intro x
  simp [superOModWeightBlock]

@[simp] theorem superOModWeightBlock_smul (N : SuperOrdVModule W M)
    (hW : W.toSuperNearVOA.IntegralWeights) (c : ℂ) (u : VType) (α : ℂ) :
    N.superOModWeightBlock hW (c • u) α = c • N.superOModWeightBlock hW u α := by
  apply LinearMap.ext
  intro x
  simp [superOModWeightBlock]

/-- The formal torus one-point supertrace, linear in the inserted state. -/
noncomputable def superTorusOnePoint (N : SuperOrdVModule W M)
    (hW : W.toSuperNearVOA.IntegralWeights) : VType →ₗ[ℂ] FormalQSeries where
  toFun u e :=
    let α := e + W.centralCharge / 24
    haveI := N.weight_finite α
    supertrace (N.weightParityGrading α) (N.superOModWeightBlock hW u α)
  map_add' u v := by
    funext e
    let α := e + W.centralCharge / 24
    haveI := N.weight_finite α
    change supertrace (N.weightParityGrading α)
        (N.superOModWeightBlock hW (u + v) α) = _
    rw [N.superOModWeightBlock_add hW, supertrace_add]
    rfl
  map_smul' c u := by
    funext e
    let α := e + W.centralCharge / 24
    haveI := N.weight_finite α
    change supertrace (N.weightParityGrading α)
        (N.superOModWeightBlock hW (c • u) α) = _
    rw [N.superOModWeightBlock_smul hW, supertrace_smul]
    rfl

@[simp] theorem superTorusOnePoint_apply (N : SuperOrdVModule W M)
    (hW : W.toSuperNearVOA.IntegralWeights) (u : VType) (e : ℂ) :
    N.superTorusOnePoint hW u e =
      (let α := e + W.centralCharge / 24
       letI := N.weight_finite α
       supertrace (N.weightParityGrading α)
        (N.superOModWeightBlock hW u α)) := rfl

/-- On a homogeneous state, the projected global block is the existing explicit zero-mode
block. -/
theorem superOModWeightBlock_of_mem_gradingZ (N : SuperOrdVModule W M)
    (hW : W.toSuperNearVOA.IntegralWeights) {k : ℤ} {u : VType}
    (hu : u ∈ W.toSuperNearVOA.gradingZ k) (α : ℂ) :
    N.superOModWeightBlock hW u α =
      N.zeroModeBlock u (k - 1) (mem_zeroModeWeight_of_mem_gradingZ hu) α := by
  let hu' : u ∈ W.grading ((((k - 1 : ℤ) : ℂ) + 1)) :=
    mem_zeroModeWeight_of_mem_gradingZ hu
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change ((internalProjTo N.weight_isInternal α)
      ((N.superOMod hW u) (x : M)) : N.weight α) = N.act u (k - 1) x
  rw [N.superOMod_of_mem_gradingZ hW hu]
  have hmem : N.act u (k - 1) (x : M) ∈ N.weight α := by
    have hshift := N.act_weight hu' x.2 (k - 1)
    simpa only [Int.cast_sub, Int.cast_one,
      show α + (((k : ℂ) - 1) + 1) - ((k : ℂ) - 1) - 1 = α by ring]
      using hshift
  exact congrArg Subtype.val
    (internalProjTo_coe N.weight_isInternal α ⟨N.act u (k - 1) x, hmem⟩)

/-- The global one-point map restricts to the pre-existing homogeneous zero-mode supertrace. -/
theorem superTorusOnePoint_of_mem_gradingZ (N : SuperOrdVModule W M)
    (hW : W.toSuperNearVOA.IntegralWeights) {p : ZMod 2} {k : ℤ} {u : VType}
    (huWeight : u ∈ W.toSuperNearVOA.gradingZ k) (huParity : u ∈ W.parity p) :
    N.superTorusOnePoint hW u = N.zeroModeSupertrace u (k - 1)
      (mem_zeroModeWeight_of_mem_gradingZ huWeight)
      huParity := by
  funext e
  let α := e + W.centralCharge / 24
  haveI := N.weight_finite α
  change supertrace (N.weightParityGrading α) (N.superOModWeightBlock hW u α) =
    supertrace (N.weightParityGrading α)
      (N.zeroModeBlock u (k - 1) _ α)
  rw [N.superOModWeightBlock_of_mem_gradingZ hW huWeight]

/-- Odd homogeneous insertions vanish.  This is precisely the finite-block theorem that an odd
endomorphism has zero ordinary supertrace. -/
theorem superTorusOnePoint_eq_zero_of_odd_homogeneous (N : SuperOrdVModule W M)
    (hW : W.toSuperNearVOA.IntegralWeights) {k : ℤ} {u : VType}
    (huWeight : u ∈ W.toSuperNearVOA.gradingZ k) (huParity : u ∈ W.parity 1) :
    N.superTorusOnePoint hW u = 0 := by
  rw [N.superTorusOnePoint_of_mem_gradingZ hW huWeight huParity]
  exact N.zeroModeSupertrace_eq_zero_of_odd (k - 1)
    (mem_zeroModeWeight_of_mem_gradingZ huWeight) huParity

/-- Every odd insertion vanishes, without a homogeneity hypothesis.  The proof decomposes the
state into its finitely many conformal-weight components.  Weight projection preserves parity;
integrality kills every component not indexed by an integer. -/
theorem superTorusOnePoint_eq_zero_of_odd (N : SuperOrdVModule W M)
    (hW : W.toSuperNearVOA.IntegralWeights) {u : VType} (hu : u ∈ W.parity 1) :
    N.superTorusOnePoint hW u = 0 := by
  classical
  let V := W.toSuperNearVOA
  obtain ⟨s, hs, _⟩ := V.exists_sum_wtProj u
  rw [← hs, map_sum]
  refine Finset.sum_eq_zero (fun h hh => ?_)
  by_cases hint : ∃ k : ℤ, (k : ℂ) = h
  · obtain ⟨k, rfl⟩ := hint
    exact N.superTorusOnePoint_eq_zero_of_odd_homogeneous hW
      (V.wtProj_mem (k : ℂ) u) (V.wtProj_mem_parity (k : ℂ) hu)
  · have hbot : V.grading h = ⊥ := hW h hint
    have hz : V.wtProj h u = 0 := by
      have hm : V.wtProj h u ∈ (⊥ : Submodule ℂ VType) := by
        simpa only [hbot] using V.wtProj_mem h u
      simpa using hm
    rw [hz, map_zero]

/-- The vacuum insertion is the formal supercharacter. -/
theorem superTorusOnePoint_vacuum (N : SuperOrdVModule W M)
    (hW : W.toSuperNearVOA.IntegralWeights) :
    N.superTorusOnePoint hW W.vacuum = N.formalSupercharacter := by
  have hv : W.vacuum ∈ W.toSuperNearVOA.gradingZ 0 := by
    simpa only [SuperNearVOA.gradingZ_apply, Int.cast_zero] using W.vacuum_mem
  rw [N.superTorusOnePoint_of_mem_gradingZ hW hv W.vacuum_parity]
  simpa using N.zeroModeSupertrace_vacuum

end SuperOrdVModule

end VOA
