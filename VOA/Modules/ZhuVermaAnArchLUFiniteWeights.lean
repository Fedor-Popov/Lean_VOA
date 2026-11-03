/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchLURealizesIrr

/-!
# `hfin` for `L(Ω(P))`: `FiniteWeights` transported across `realizesIrr`.

The `OrdVModule.finrank` obligation `hfin : (djLU …).FiniteWeights` for the Dong–Jiang module of an
irreducible `P`'s bottom is **derivable**, not an additional carried hypothesis. The **linear** first-isomorphism
equivalence `pRealizesLinEquiv : M(Ω(P))/J ≃ₗ P` — which, unlike `pRealizesIso`/`pRealizesLWIso`, does
**not** take `hfin` — intertwines `L₀` (it is built from `φ̄`, `pPhiBar_intertwine`), hence maps each
weight space `L(Ω(P))_α` **into** `P_α`; and `P_α` is finite-dimensional because `P` is a bundled
`LWModule` (`P.isMod.finrank`).  Transporting finiteness back along the (injective) equivalence gives
`FiniteDimensional ℂ (L(Ω(P))_α)` for every `α`, i.e. `FiniteWeights`.

Two general tools built here, then the transport:
* `mem_weight_of_L0op_eq` — **`L₀`-eigenvector ⟹ in the weight space** for a `GradedLWWeakModule`
  (`L₀ x = α·x ⟹ x ∈ M_α`), by the eigenvalue-isolation operator `isoOp` (mirrors
  `component_mem_of_invariant`).  This is the "eigenspace = weight space" fact the `OrdVModule` grading
  makes true but does not state directly.
* `pRealizesLinEquiv_act` — the `𝒱`-action intertwining of the **linear** equivalence, `hfin`-free.

Proof-term `#print axioms`-clean (`[propext, Classical.choice, Quot.sound]`), `sorry`-free, and
`pbw`-free, but conditional on the explicit `Pr` threaded through `pRealizesLinEquiv`. The
project-level `regularAMod` witness is supplied by `voaPBWBottomProjection`, from the generic
relative-induction field of the theorem `VOA.pbw : PBWPrinciple`.

## References
Gannon Def. 5.3.1c (`L₀`-eigenspace grading).  `ZhuVermaAnArchLUGraded` (`isoOp`, `isoOp_weight`,
`L0op`, `component_mem_of_invariant`), `ZhuVermaAnArchLURealizesIrr` (`pRealizesLinEquiv`),
`ZhuVermaAnArchZhu534` (`FiniteWeights`, `toLWModule`).
-/

namespace VOA

open scoped BigOperators
open VertexOperatorAlgebra
open VHat VHat.DLM3 GradedLWWeakModule

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

section
variable {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M] {h : ℂ}

/-- **`L₀`-eigenvector ⟹ weight vector.**  On a `GradedLWWeakModule`, if `L₀ x = α·x` then `x` lies
in the weight space `M_α`: the eigenvalue-isolation operator `∏_{γ∈supp\{α}}(L₀−γ)` scales `x` by a
nonzero constant and kills every off-`α` component, so `x` equals its own `α`-component. -/
theorem mem_weight_of_L0op_eq (N : GradedLWWeakModule W M h) [DirectSum.Decomposition N.weight]
    {α : ℂ} {x : M} (hx : N.L0op x = α • x) : x ∈ N.weight α := by
  classical
  set S := (DirectSum.decompose N.weight x).support with hS
  set s := S.erase α with hs
  have hc : (∏ γ ∈ s, (α - γ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun γ hγ => sub_ne_zero.mpr (Ne.symm (Finset.ne_of_mem_erase hγ))
  -- `isoOp s x = ∏(α−γ) • x` because `x` is an `α`-eigenvector.
  have h1 : N.isoOp s x = (∏ γ ∈ s, (α - γ)) • x := by
    rw [isoOp, Module.End.aeval_apply_of_mem_apply_eq_smul hx, Polynomial.eval_prod]
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  -- `isoOp s x = ∏(α−γ) • (α-component of x)` because every off-`α` component is annihilated.
  have h2 : N.isoOp s x
      = (∏ γ ∈ s, (α - γ)) • ((DirectSum.decompose N.weight x α : N.weight α) : M) := by
    have e1 : N.isoOp s x
        = ∑ δ ∈ S, N.isoOp s ((DirectSum.decompose N.weight x δ : N.weight δ) : M) := by
      rw [← map_sum]; congr 1; exact (DirectSum.sum_support_decompose N.weight x).symm
    rw [e1, Finset.sum_congr rfl
      (fun δ _ => N.isoOp_weight s (SetLike.coe_mem (DirectSum.decompose N.weight x δ)))]
    by_cases hα : α ∈ S
    · rw [Finset.sum_eq_single α (fun δ hδ hδα => ?_) (fun hαS => absurd hα hαS)]
      have hδs : δ ∈ s := Finset.mem_erase.mpr ⟨hδα, hδ⟩
      rw [Finset.prod_eq_zero hδs (sub_self δ), zero_smul]
    · -- `α ∉ S`: every term dies (each `δ ∈ S = s` contributes a `(δ−δ)` factor), and the
      -- `α`-component is `0`.
      rw [Finset.sum_eq_zero (fun δ hδ => ?_)]
      · have hα0 : (DirectSum.decompose N.weight x α : N.weight α) = 0 :=
          DFinsupp.notMem_support_iff.mp (by rwa [← hS])
        rw [hα0, ZeroMemClass.coe_zero, smul_zero]
      · have hδs : δ ∈ s := Finset.mem_erase.mpr ⟨fun hδα => hα (hδα ▸ hδ), hδ⟩
        rw [Finset.prod_eq_zero hδs (sub_self δ), zero_smul]
  have hxeq : x = ((DirectSum.decompose N.weight x α : N.weight α) : M) :=
    smul_right_injective M hc (h1.symm.trans h2)
  rw [hxeq]
  exact SetLike.coe_mem _

end

section
variable {W : VertexOperatorAlgebra 𝒱}

/-- **`P.isMod` as a finrank-free `GradedLWWeakModule`** (it already carries the grading, `L₀`
eigenvalue and bounded-belowness; `isLow` is `P.isLow`).  Used to run the eigenvalue-isolation
argument on `P`. -/
noncomputable def pGraded (P : LWModule W) : GradedLWWeakModule W P.carrier P.h where
  toWeakModule := P.isMod.toWeakModule
  weight := P.isMod.weight
  isInternal := P.isMod.isInternal
  L0_weight := P.isMod.L0_weight
  boundedBelow := P.isMod.boundedBelow
  isLow := P.isLow
  realized := P.realized

@[simp] theorem pGraded_weight (P : LWModule W) (α : ℂ) :
    (pGraded P).weight α = P.isMod.weight α := rfl

/-- The **linear** first-isomorphism equivalence intertwines the `𝒱`-action (`hfin`-free; the same
computation as `pRealizesIso.map_act`, but on `pRealizesLinEquiv`). -/
theorem pRealizesLinEquiv_act (P : LWModule W)
    (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W)))
    (hU : Nontrivial (pBotAmMod P).carrier)
    (hL0 : ∀ (n : ℕ) (x : DJCarrier W (pBotAmMod P)), x ∈ DJCarrier.deg W (pBotAmMod P) n →
      djModeZero W (pBotAmMod P) 1 W.conformalVector x = (P.h + n) • x)
    (hP : P.IsIrreducibleLW) (u : 𝒱) (n : ℤ)
    (x : DJCarrier W (pBotAmMod P) ⧸ (djJ Pr (pBotAmMod P) hU P.h hL0).carrier) :
    pRealizesLinEquiv P Pr hU hL0 hP
        ((djLU Pr (pBotAmMod P) hU P.h hL0).toWeakModule.act u n x)
      = P.isMod.toWeakModule.act u n (pRealizesLinEquiv P Pr hU hL0 hP x) := by
  refine Submodule.Quotient.induction_on _ x (fun z => ?_)
  rw [djLU_act_mk, pRealizesLinEquiv_mk, pRealizesLinEquiv_mk, pPhiBar_intertwine]

/-- **`hfin` is derivable**: `FiniteWeights (L(Ω(P)))` for an irreducible `P`.  `pRealizesLinEquiv`
maps `L(Ω(P))_α` into `P_α` (it intertwines `L₀`, `pRealizesLinEquiv_act`, and `L₀`-eigenvectors of
`P` lie in `P_α`, `mem_weight_of_L0op_eq`), and `P_α` is finite-dimensional (`P.isMod.finrank`); the
equivalence is injective, so `L(Ω(P))_α` is finite-dimensional too. -/
theorem pFiniteWeights (P : LWModule W)
    (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W)))
    (hU : Nontrivial (pBotAmMod P).carrier)
    (hL0 : ∀ (n : ℕ) (x : DJCarrier W (pBotAmMod P)), x ∈ DJCarrier.deg W (pBotAmMod P) n →
      djModeZero W (pBotAmMod P) 1 W.conformalVector x = (P.h + n) • x)
    (hP : P.IsIrreducibleLW) :
    (djLU Pr (pBotAmMod P) hU P.h hL0).FiniteWeights := by
  classical
  letI := DirectSum.IsInternal.chooseDecomposition (pGraded P).weight (pGraded P).isInternal
  intro α
  -- `pRealizesLinEquiv` maps `L(Ω(P))_α` into `P_α`.
  have hle : Submodule.map ((pRealizesLinEquiv P Pr hU hL0 hP).toLinearMap)
      ((djLU Pr (pBotAmMod P) hU P.h hL0).weight α) ≤ P.isMod.weight α := by
    rintro _ ⟨y, hy, rfl⟩
    refine mem_weight_of_L0op_eq (pGraded P) (α := α)
      (x := pRealizesLinEquiv P Pr hU hL0 hP y) ?_
    -- `L₀ (e y) = α • e y`, from `L₀ y = α • y` and the intertwining.
    have hLy : (djLU Pr (pBotAmMod P) hU P.h hL0).toWeakModule.act W.conformalVector 1 y = α • y := by
      have := (djLU Pr (pBotAmMod P) hU P.h hL0).L0op_weight hy
      rwa [L0op, ← WeakModule.act_def] at this
    have hkey := pRealizesLinEquiv_act P Pr hU hL0 hP W.conformalVector 1 y
    rw [hLy, map_smul] at hkey
    show (pGraded P).L0op (pRealizesLinEquiv P Pr hU hL0 hP y)
      = α • pRealizesLinEquiv P Pr hU hL0 hP y
    rw [L0op, ← WeakModule.act_def]
    exact hkey.symm
  -- `P_α` is finite-dimensional, so its submodule `map e (L(Ω(P))_α)` and hence `L(Ω(P))_α` is too.
  haveI : FiniteDimensional ℂ (P.isMod.weight α) := P.isMod.finrank α
  haveI : FiniteDimensional ℂ (Submodule.map ((pRealizesLinEquiv P Pr hU hL0 hP).toLinearMap)
      ((djLU Pr (pBotAmMod P) hU P.h hL0).weight α)) :=
    FiniteDimensional.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)
  exact (Submodule.equivMapOfInjective (pRealizesLinEquiv P Pr hU hL0 hP).toLinearMap
    (pRealizesLinEquiv P Pr hU hL0 hP).injective
    ((djLU Pr (pBotAmMod P) hU P.h hL0).weight α)).symm.finiteDimensional

end

end VOA
