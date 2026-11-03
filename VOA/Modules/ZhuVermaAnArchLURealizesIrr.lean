/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchLUUniversalIrr
import VOA.Modules.ZhuVermaAnArchZhu534

/-!
# DJ Theorem 4.13, `realizesIrr`: every irreducible `P` is `L(Ω(P))`.

`ZhuVermaAnArchLUUniversalIrr` produced, for an irreducible lowest-weight module `P`, the induced
weak-module map `φ̄ = pPhiBar P : M(Ω(P)) → P` and proved it is **surjective** (`pPhiBar_surjective`)
with **kernel `J(Ω(P))`** (`pPhiBarKer_eq_djJ`, via `djJ_unique` + bottom-triviality + maximality).

This file assembles the **first-isomorphism theorem** in the Dong–Jiang carrier: `M(Ω(P))/J ≃ P`
(`pRealizesLinEquiv`), intertwining the `𝒱`-action (`djLU_act_mk` + `pPhiBar_intertwine`), i.e. a
`ModuleEquiv` (`pRealizesIso`).  Packaged as `LWModule.Iso W ((djLU …).toLWModule hfin) P`
(`pRealizesLWIso`) — this is `realizesIrr` for the single `P`, DJ Thm 4.13's conclusion `P ≅ L(Ω(P))`.
It mirrors `InducedAssignment.RealizesIrrData.iso` (`ZhuVermaAnArchGenBottom`) in the DJ carrier, which
lives in a different (abstract `MU`) track.

Carried, all displayed: the explicit `BottomProjection` assumption `Pr`, the scope nontriviality
`hU`, the grading scalar `hL0`, and the `OrdVModule.finrank` obligation `hfin`. The proof term is
`#print axioms`-clean (`[propext, Classical.choice, Quot.sound]`), `sorry`-free, and does not use
`VOA.pbw`; the declarations remain conditional on the explicit parameters, which
`#print axioms` does not report. The project-level `regularAMod` projection is supplied separately
by `voaPBWBottomProjection`, from the generic relative-induction field of the theorem
`VOA.pbw : PBWPrinciple`.

## References
Dong–Jiang math/0601626 Thm 4.13; DLM3 §4.  `ZhuVermaAnArchLUUniversalIrr`
(`pPhiBar`, `pPhiBar_surjective`, `pPhiBarKer_eq_djJ`, `pPhiBar_intertwine`), `ZhuVermaAnArchLU`
(`djLU`, `djJ`, `djLU_act_mk`), `ZhuVermaAnArchZhu534` (`GradedLWWeakModule.toLWModule`,
`FiniteWeights`), `ZhuVermaAnArchGenBottom` (`RealizesIrrData.iso`, the template).
-/

namespace VOA

open scoped BigOperators
open VertexOperatorAlgebra
open VHat VHat.DLM3 GradedLWWeakModule

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

section
variable {W : VertexOperatorAlgebra 𝒱}

/-- **The first-isomorphism linear equivalence** `M(Ω(P))/J ≃ P`.  `φ̄` is surjective with
`ker φ̄ = J(Ω(P))` (`pPhiBarKer_eq_djJ`), so `M(Ω(P))/J = M(Ω(P))/ker φ̄ ≃ P`. -/
noncomputable def pRealizesLinEquiv (P : LWModule W)
    (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W)))
    (hU : Nontrivial (pBotAmMod P).carrier)
    (hL0 : ∀ (n : ℕ) (x : DJCarrier W (pBotAmMod P)), x ∈ DJCarrier.deg W (pBotAmMod P) n →
      djModeZero W (pBotAmMod P) 1 W.conformalVector x = (P.h + n) • x)
    (hP : P.IsIrreducibleLW) :
    (DJCarrier W (pBotAmMod P) ⧸ (djJ Pr (pBotAmMod P) hU P.h hL0).carrier) ≃ₗ[ℂ] P.carrier :=
  (Submodule.quotEquivOfEq _ _ (pPhiBarKer_eq_djJ P Pr hU hL0 hP).symm).trans
    ((pPhiBar P).quotKerEquivOfSurjective (pPhiBar_surjective P hP))

@[simp] theorem pRealizesLinEquiv_mk (P : LWModule W)
    (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W)))
    (hU : Nontrivial (pBotAmMod P).carrier)
    (hL0 : ∀ (n : ℕ) (x : DJCarrier W (pBotAmMod P)), x ∈ DJCarrier.deg W (pBotAmMod P) n →
      djModeZero W (pBotAmMod P) 1 W.conformalVector x = (P.h + n) • x)
    (hP : P.IsIrreducibleLW) (x : DJCarrier W (pBotAmMod P)) :
    pRealizesLinEquiv P Pr hU hL0 hP (Submodule.Quotient.mk x) = pPhiBar P x := by
  unfold pRealizesLinEquiv
  rw [LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk]
  rfl

/-- **`L(Ω(P)) ≅ P` as a `𝒱`-module isomorphism** — `realizesIrr` for the single irreducible `P`
(DJ Thm 4.13).  Carries `Pr`, `hU`, `hL0` and the `OrdVModule.finrank` obligation `hfin`. -/
noncomputable def pRealizesIso (P : LWModule W)
    (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W)))
    (hU : Nontrivial (pBotAmMod P).carrier)
    (hL0 : ∀ (n : ℕ) (x : DJCarrier W (pBotAmMod P)), x ∈ DJCarrier.deg W (pBotAmMod P) n →
      djModeZero W (pBotAmMod P) 1 W.conformalVector x = (P.h + n) • x)
    (hP : P.IsIrreducibleLW)
    (hfin : (djLU Pr (pBotAmMod P) hU P.h hL0).FiniteWeights) :
    ModuleEquiv W ((djLU Pr (pBotAmMod P) hU P.h hL0).toLWModule hfin).isMod P.isMod where
  toLinearEquiv := pRealizesLinEquiv P Pr hU hL0 hP
  map_act u n x := by
    refine Submodule.Quotient.induction_on _ x (fun z => ?_)
    change pRealizesLinEquiv P Pr hU hL0 hP
        ((djLU Pr (pBotAmMod P) hU P.h hL0).toWeakModule.act u n (Submodule.Quotient.mk z))
      = P.isMod.toWeakModule.act u n (pRealizesLinEquiv P Pr hU hL0 hP (Submodule.Quotient.mk z))
    rw [djLU_act_mk, pRealizesLinEquiv_mk, pRealizesLinEquiv_mk, pPhiBar_intertwine]

/-- **`L(Ω(P)) ≅ P` packaged as `LWModule.Iso`.** -/
theorem pRealizesLWIso (P : LWModule W)
    (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W)))
    (hU : Nontrivial (pBotAmMod P).carrier)
    (hL0 : ∀ (n : ℕ) (x : DJCarrier W (pBotAmMod P)), x ∈ DJCarrier.deg W (pBotAmMod P) n →
      djModeZero W (pBotAmMod P) 1 W.conformalVector x = (P.h + n) • x)
    (hP : P.IsIrreducibleLW)
    (hfin : (djLU Pr (pBotAmMod P) hU P.h hL0).FiniteWeights) :
    LWModule.Iso W ((djLU Pr (pBotAmMod P) hU P.h hL0).toLWModule hfin) P :=
  ⟨pRealizesIso P Pr hU hL0 hP hfin⟩

/-! ## The faithful Zhu bijection from a DJ realization family

The realization `pRealizesLWIso` (`K P ≅ P`) plus the functoriality of `L(·)` on bottoms
(`isoInvariant`, `K P ≅ K Q` whenever the bottoms agree) determine every irreducible from its bottom,
i.e. give `IrredBottomRigidity W`, hence `Function.Bijective (forwardMapIrr W)`
(`forwardMapIrr_bijective_of_rigidity`).  Packaged as one bundle so the exact remaining inputs are
displayed: `K` and its two properties. -/

/-- **A DJ realization family** — the bundle out of which the faithful Zhu bijection is assembled:
a lowest-weight module `K P` for each `P`, isomorphic to every irreducible `P` (`realizes`, supplied
by `pRealizesLWIso` with `K P = L(Ω(P))`) and depending on `P` only through its bottom iso-class
(`isoInvariant`, the functoriality of `L(·)`). -/
structure DJRealizationFamily (W : VertexOperatorAlgebra 𝒱) where
  /-- The realizing lowest-weight module (e.g. `L(Ω(P)) = (djLU …).toLWModule hfin`). -/
  K : LWModule W → LWModule W
  /-- Every irreducible `P` is isomorphic to `K P` (`realizesIrr`, `pRealizesLWIso`). -/
  realizes : ∀ P : LWModule W, P.IsIrreducibleLW → LWModule.Iso W (K P) P
  /-- `K` depends on `P` only through its bottom iso-class (functoriality of `L(·)`). -/
  isoInvariant : ∀ P Q : LWModule W, P.IsIrreducibleLW → Q.IsIrreducibleLW →
    Nonempty (AModEquiv W P.toAMod Q.toAMod) → LWModule.Iso W (K P) (K Q)

/-- **Bottom-rigidity from a realization family**: `P ≅ K P ≅ K Q ≅ Q` for irreducibles with
isomorphic bottoms. -/
theorem DJRealizationFamily.rigidity (D : DJRealizationFamily W) : IrredBottomRigidity W := by
  intro P Q hP hQ hbot
  exact (LWModule.setoid W).trans ((LWModule.setoid W).symm (D.realizes P hP))
    ((LWModule.setoid W).trans (D.isoInvariant P Q hP hQ hbot) (D.realizes Q hQ))

/-- **The faithful Zhu bijection `Function.Bijective (forwardMapIrr W)` from a DJ realization
family** (`forwardMapIrr_bijective_of_rigidity ∘ rigidity`).  This is Zhu Theorem 5.3.4's faithful
form, reduced to the single displayed datum `DJRealizationFamily W`. -/
theorem DJRealizationFamily.bijective (D : DJRealizationFamily W) :
    Function.Bijective (forwardMapIrr W) :=
  forwardMapIrr_bijective_of_rigidity D.rigidity

end

end VOA
