/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchLUIsoInvariant
import VOA.Modules.ZhuVermaAnArchLUFiniteWeights
import VOA.Modules.ZhuVermaAnArchHL0

/-!
# The faithful Zhu correspondence `Function.Bijective (forwardMapIrr W)` from the DJ track.

This main theorem assembles the `DJRealizationFamily W` (`ZhuVermaAnArchLURealizesIrr`) out of the three
Dong–Jiang ingredients:

* `realizes`  — `pRealizesLWIso`: every irreducible `P` is `L(Ω(P))` (`ZhuVermaAnArchLURealizesIrr`);
* `isoInvariant` — `djLUFunctorLWIso`: `L(Ω(P)) ≅ L(Ω(Q))` when the bottoms agree
  (`ZhuVermaAnArchLUIsoInvariant`), with `P.h = Q.h` read off the bottom `ω`-scalar (`pH_eq`);
* the `OrdVModule.finrank` obligation `hfin` — `pFiniteWeights` (`ZhuVermaAnArchLUFiniteWeights`),
  **derived**, not carried.

The one input threaded through as a hypothesis is the `L₀`-grading `hHL0` (`hL0` for every bottom
`Ω(P)` at weight `P.h`); once its discharge `pHL0` is available, `zhuBijective` remains conditional
on the explicit `BottomProjection` assumption `Pr`.

The proof term is `#print axioms`-clean (`[propext, Classical.choice, Quot.sound]`), `sorry`-free,
and does not use `VOA.pbw`; explicit parameters such as `Pr` are not reported by
`#print axioms`. The companion theorem `zhuBijective_of_voaPBW` supplies `Pr` through
`voaPBWBottomProjection`, ultimately using the generic relative-induction field of the theorem
`VOA.pbw : PBWPrinciple`.

## References
Zhu J.AMS 9 (1996) Thm 5.3.4; Dong–Jiang math/0601626 Thm 4.13; DLM3 §4.
-/

namespace VOA

open scoped BigOperators
open VertexOperatorAlgebra
open VHat VHat.DLM3 GradedLWWeakModule

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

section
variable {W : VertexOperatorAlgebra 𝒱}

/-- **The bottom of a realized lowest-weight module is nonzero.** -/
theorem pBotNontrivial (P : LWModule W) : Nontrivial (pBotAmMod P).carrier := by
  obtain ⟨v, hv, hvne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.realized
  refine ⟨(0 : (pBotAmMod P).carrier), ⟨v, hv⟩, ?_⟩
  intro heq
  exact hvne (congrArg Subtype.val heq).symm

/-- **Isomorphic bottoms realize the same lowest weight** — both are `ω`-scalars of `Ω(Q)`. -/
theorem pH_eq {P Q : LWModule W} (ψ : AModEquiv W P.toAMod Q.toAMod) : P.h = Q.h := by
  have h1 : Q.toAMod.OmegaScalar P.h := omegaScalar_of_bottomEquiv ψ
  have h2 : Q.toAMod.OmegaScalar Q.h := LWModule.toAMod_omegaScalar Q
  obtain ⟨v, hv, hvne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot Q.realized
  have e1 := AMod.omegaScalar_apply h1 (⟨v, hv⟩ : Q.toAMod.carrier)
  have e2 := AMod.omegaScalar_apply h2 (⟨v, hv⟩ : Q.toAMod.carrier)
  have hsm : P.h • (⟨v, hv⟩ : Q.toAMod.carrier) = Q.h • (⟨v, hv⟩ : Q.toAMod.carrier) :=
    e1.symm.trans e2
  have hne : (⟨v, hv⟩ : Q.toAMod.carrier) ≠ 0 := fun h => hvne (congrArg Subtype.val h)
  have := sub_eq_zero.mpr hsm
  rw [← sub_smul] at this
  rcases smul_eq_zero.mp this with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h hne

/-! ## The `𝒱`-module descent `L(U₁) ≅ L(U₂)` (needs `toLWModule`) -/

/-- **`L(U₁) ≅ L(U₂)` as a `𝒱`-module isomorphism** — the descended functor map intertwines the
quotient action. -/
noncomputable def djLUFunctorIso (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W)))
    {U₁ U₂ : AmMod W 0} (e : AmModHom U₁ U₂) (hU₁ : Nontrivial U₁.carrier)
    (hU₂ : Nontrivial U₂.carrier) (h : ℂ)
    (hL0₁ : ∀ (n : ℕ) (x : DJCarrier W U₁), x ∈ DJCarrier.deg W U₁ n →
      djModeZero W U₁ 1 W.conformalVector x = (h + n) • x)
    (hL0₂ : ∀ (n : ℕ) (x : DJCarrier W U₂), x ∈ DJCarrier.deg W U₂ n →
      djModeZero W U₂ 1 W.conformalVector x = (h + n) • x)
    (hfin₁ : (djLU Pr U₁ hU₁ h hL0₁).FiniteWeights)
    (hfin₂ : (djLU Pr U₂ hU₂ h hL0₂).FiniteWeights) :
    ModuleEquiv W ((djLU Pr U₁ hU₁ h hL0₁).toLWModule hfin₁).isMod
      ((djLU Pr U₂ hU₂ h hL0₂).toLWModule hfin₂).isMod where
  toLinearEquiv := djLUFunctorLinEquiv Pr e hU₁ hU₂ h hL0₁ hL0₂
  map_act u n x := by
    refine Submodule.Quotient.induction_on _ x (fun z => ?_)
    change djLUFunctorLinEquiv Pr e hU₁ hU₂ h hL0₁ hL0₂
        ((djLU Pr U₁ hU₁ h hL0₁).toWeakModule.act u n (Submodule.Quotient.mk z))
      = (djLU Pr U₂ hU₂ h hL0₂).toWeakModule.act u n
          (djLUFunctorLinEquiv Pr e hU₁ hU₂ h hL0₁ hL0₂ (Submodule.Quotient.mk z))
    rw [djLU_act_mk, djLUFunctorLinEquiv_mk, djLUFunctorLinEquiv_mk, djLU_act_mk,
      djFunctorEquiv_natural]

/-- **`L(U₁) ≅ L(U₂)` as `LWModule.Iso`, allowing distinct lowest weights `h₁ = h₂`** (the two
irreducibles' weights, matched by `pH_eq`). -/
theorem djLUFunctorLWIso' (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W)))
    {U₁ U₂ : AmMod W 0} (e : AmModHom U₁ U₂) (hU₁ : Nontrivial U₁.carrier)
    (hU₂ : Nontrivial U₂.carrier) (h₁ h₂ : ℂ) (heq : h₁ = h₂)
    (hL0₁ : ∀ (n : ℕ) (x : DJCarrier W U₁), x ∈ DJCarrier.deg W U₁ n →
      djModeZero W U₁ 1 W.conformalVector x = (h₁ + n) • x)
    (hL0₂ : ∀ (n : ℕ) (x : DJCarrier W U₂), x ∈ DJCarrier.deg W U₂ n →
      djModeZero W U₂ 1 W.conformalVector x = (h₂ + n) • x)
    (hfin₁ : (djLU Pr U₁ hU₁ h₁ hL0₁).FiniteWeights)
    (hfin₂ : (djLU Pr U₂ hU₂ h₂ hL0₂).FiniteWeights) :
    LWModule.Iso W ((djLU Pr U₁ hU₁ h₁ hL0₁).toLWModule hfin₁)
      ((djLU Pr U₂ hU₂ h₂ hL0₂).toLWModule hfin₂) := by
  subst heq
  exact ⟨djLUFunctorIso Pr e hU₁ hU₂ h₁ hL0₁ hL0₂ hfin₁ hfin₂⟩

/-! ## Assembling the `DJRealizationFamily` and the bijection -/

/-- The realizing family `K P = L(Ω(P))`, using the carried `L₀`-grading `hHL0`.  Non-irreducible `P`
gets the junk value `P` (never inspected by `realizes`/`isoInvariant`). -/
noncomputable def djK (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W)))
    (hHL0 : ∀ (P : LWModule W) (n : ℕ) (x : DJCarrier W (pBotAmMod P)),
      x ∈ DJCarrier.deg W (pBotAmMod P) n →
      djModeZero W (pBotAmMod P) 1 W.conformalVector x = (P.h + n) • x)
    (P : LWModule W) : LWModule W := by
  classical
  exact if hP : P.IsIrreducibleLW then
    (djLU Pr (pBotAmMod P) (pBotNontrivial P) P.h (hHL0 P)).toLWModule
      (pFiniteWeights P Pr (pBotNontrivial P) (hHL0 P) hP)
  else P

/-- **The DJ realization family** — `K = L(Ω(·))`, `realizes` from `pRealizesLWIso`, `isoInvariant`
from `djLUFunctorLWIso'`. -/
noncomputable def djRealizationFamily
    (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W)))
    (hHL0 : ∀ (P : LWModule W) (n : ℕ) (x : DJCarrier W (pBotAmMod P)),
      x ∈ DJCarrier.deg W (pBotAmMod P) n →
      djModeZero W (pBotAmMod P) 1 W.conformalVector x = (P.h + n) • x) :
    DJRealizationFamily W where
  K := djK Pr hHL0
  realizes P hP := by
    rw [djK, dif_pos hP]
    exact pRealizesLWIso P Pr (pBotNontrivial P) (hHL0 P) hP
      (pFiniteWeights P Pr (pBotNontrivial P) (hHL0 P) hP)
  isoInvariant P Q hP hQ hbot := by
    obtain ⟨ψ⟩ := hbot
    rw [djK, dif_pos hP, djK, dif_pos hQ]
    exact djLUFunctorLWIso' Pr (amModHomOfBottomEquiv ψ) (pBotNontrivial P) (pBotNontrivial Q)
      P.h Q.h (pH_eq ψ) (hHL0 P) (hHL0 Q)
      (pFiniteWeights P Pr (pBotNontrivial P) (hHL0 P) hP)
      (pFiniteWeights Q Pr (pBotNontrivial Q) (hHL0 Q) hQ)

/-- **Zhu Theorem 5.3.4 (faithful form), conditional** —
`Function.Bijective (forwardMapIrr W)` from the independent `BottomProjection` assumption `Pr` and
the `L₀`-grading `hHL0` (discharged by `pHL0`). -/
theorem zhuBijective_of_hHL0
    (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W)))
    (hHL0 : ∀ (P : LWModule W) (n : ℕ) (x : DJCarrier W (pBotAmMod P)),
      x ∈ DJCarrier.deg W (pBotAmMod P) n →
      djModeZero W (pBotAmMod P) 1 W.conformalVector x = (P.h + n) • x) :
    Function.Bijective (forwardMapIrr W) :=
  (djRealizationFamily Pr hHL0).bijective

/-- **Zhu Theorem 5.3.4 (faithful form), conditional on `Pr`** —
`Function.Bijective (forwardMapIrr W)`. The `L₀`-grading is discharged by `pHL0`
(`ZhuVermaAnArchHL0`), so the sole remaining input is the explicit `BottomProjection` assumption
`Pr`. The companion wrapper `zhuBijective_of_voaPBW` supplies this `regularAMod` instance from the
generic relative-induction field of the theorem `VOA.pbw : PBWPrinciple`. -/
theorem zhuBijective (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W))) :
    Function.Bijective (forwardMapIrr W) :=
  zhuBijective_of_hHL0 Pr (fun P => pHL0 P)

end

end VOA
