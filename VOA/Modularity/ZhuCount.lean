/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.WedderburnAMod
import VOA.Modularity.LowestWeightExistence
import VOA.Modules.ZhuVermaAnArchLUBijection
import VOA.Modularity.CuspLimit

/-!
# The count: `dim A(𝒱)/[A(𝒱),A(𝒱)] ≤ #Φ(𝒱)`

The count behind Zhu Thm 5.3.3 has three links:

* **(L1)** `#(Wedderburn factors) = #Irr A(𝒱)` — proved
  (`Modularity.AModBridge.isSimpleAMod_iff_isSimpleModule`,
  `Modularity.WedderburnAMod.exists_pairwise_nonIso_simple_aMod`);
* **(L2)** `#Irr A(𝒱) = #IrrAModIsoClass` — the two named gates of `Modules`;
* **(L3)** `#IrrLWModuleIsoClass = #Φ(𝒱)` — proved
  (`Modularity.LowestWeightExistence.irrLWModuleIsoClass_equiv_Φ`).

This file assembles them, and in doing so **halves L2**.

## L2 needs only *one* of its two gates

The count is an *inequality* — it places the Wedderburn factors into `Φ(𝒱)`, so it only needs
`simple ⟹ IsBottomOfIrr`.  That is `SimpleAModsRealized`.  The other gate,
`AllIrrBottomRecovers`, supplies the converse `IsBottomOfIrr ⟹ simple`, which the count never
uses. So the count rests on **one** named gate, not two — together with the explicit
`BottomProjection` assumption `Pr` of `zhuBijective`. The project-level `regularAMod` witness is
supplied by `voaPBWBottomProjection`, from the generic relative-induction field of the theorem
`VOA.pbw : PBWPrinciple`.

⚠ And by `Modularity.SimpleAModFinite.simpleAModsRealized_finiteDimensional`, that gate as typed
already entails `FiniteDimensional ℂ (A 𝒱)` on every simple module, so the finiteness hypotheses
carried here cost nothing.

## The chain

`Fin m` ↪ simple `AMod`s (Artin–Wedderburn, L1)
  ↪ `IrrAMod W` (`SimpleAModsRealized`, the one gate)
  ↠ `IrrAModIsoClass W` ≃ `IrrLWModuleIsoClass W` (`zhuBijective Pr`, Zhu's bijection)
  ≃ `Φ W` (L3),
with `m = finrank ℂ (A(𝒱)/[A(𝒱),A(𝒱)])` by `finrank_quot_commSpan_eq_of_algEquiv_pi_matrix`.

## Main results

* `exists_injective_finrank_quot_commSpan_to_Φ`;
* `finrank_quot_commSpan_le_card_Φ` — the count, as a bound on natural numbers.

## Status
Proof-term `#print axioms`-clean, no `sorry`, but conditional on named hypotheses:
`FiniteDimensional ℂ (A 𝒱)`, `IsSemisimpleRing (A 𝒱)` (Zhu's own rationality inputs),
`SimpleAModsRealized 𝒱`, and the explicit `BottomProjection` assumption `Pr`. The project-level
`regularAMod` witness is supplied as above. Explicit parameters are not reported by
`#print axioms`.
-/

namespace VOA

open VHat VHat.DLM3

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] (W : VertexOperatorAlgebra 𝒱)

/-- **The Wedderburn factors inject into `Φ(𝒱)`.** -/
theorem exists_injective_finrank_quot_commSpan_to_Φ
    (hfd : letI := instRingA W; FiniteDimensional ℂ (A W))
    (hss : letI := instRingA W; IsSemisimpleRing (A W))
    (hreal : SimpleAModsRealized W)
    (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W))) :
    ∃ f : Fin (letI := instRingA W; letI := instAlgebraA W;
        Module.finrank ℂ (A W ⧸ commSpan ℂ (A W))) → Φ W,
      Function.Injective f := by
  classical
  letI := instRingA W
  letI := instAlgebraA W
  obtain ⟨m, U, hm, hsimple, hnoniso⟩ := exists_pairwise_nonIso_simple_aMod hfd hss
  -- Each Wedderburn factor is a bottom of an irreducible module (the single gate).
  have hbot : ∀ j, IsBottomOfIrr (U j) := fun j => isBottomOfIrr_of_simple hreal (hsimple j)
  -- Their iso-classes in `Irr A(𝒱)` are pairwise distinct.
  set c : Fin m → IrrAModIsoClass W :=
    fun j => Quotient.mk (IrrAMod.setoid W) (⟨U j, hbot j⟩ : IrrAMod W) with hc
  have hcinj : Function.Injective c := by
    intro i j hij
    by_contra hne
    exact (hnoniso i j hne).elim' (Quotient.exact hij).some
  -- Transport along Zhu's bijection and L3.
  set e : IrrLWModuleIsoClass W ≃ IrrAModIsoClass W :=
    Equiv.ofBijective (forwardMapIrr W) (zhuBijective Pr) with he
  refine ⟨fun j => irrLWModuleIsoClass_equiv_Φ W (e.symm (c (Fin.cast hm.symm j))), ?_⟩
  intro i j hij
  have := hcinj (e.symm.injective ((irrLWModuleIsoClass_equiv_Φ W).injective hij))
  exact Fin.cast_injective hm.symm this

/-- **The count.**  When there are only finitely many irreducible `𝒱`-modules,
the number of Wedderburn factors of `A(𝒱)` is at most `#Φ(𝒱)`. -/
theorem finrank_quot_commSpan_le_card_Φ [Finite (Φ W)]
    (hfd : letI := instRingA W; FiniteDimensional ℂ (A W))
    (hss : letI := instRingA W; IsSemisimpleRing (A W))
    (hreal : SimpleAModsRealized W)
    (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W))) :
    letI := instRingA W; letI := instAlgebraA W;
    Module.finrank ℂ (A W ⧸ commSpan ℂ (A W)) ≤ Nat.card (Φ W) := by
  letI := instRingA W
  letI := instAlgebraA W
  obtain ⟨f, hf⟩ := exists_injective_finrank_quot_commSpan_to_Φ W hfd hss hreal Pr
  have := Nat.card_le_card_of_injective f hf
  simpa using this

/-- **Zhu's Theorem 5.3.3 at the cusp, in full.**  The dimension of the space of genus-one
conformal blocks *at `q = 0`* is at most the number of irreducible `𝒱`-modules.

This is the complete right-hand end of the modularity chain: `Modularity.CuspLimit` identifies the
cusp relation quotient with `A(𝒱)/[A(𝒱),A(𝒱)]`, and L1–L3 carry that to `Φ(𝒱)`.  The only
inputs are Zhu's own rationality hypotheses, the named gate `SimpleAModsRealized`, and the
independent `BottomProjection` assumption `Pr`; this required `regularAMod` instance is not
currently established.

⚠ This is the bound **at the cusp**.  Transporting it to a point `z₀ ∈ ℍ` is the separate open item
(`E46`-finiteness of the deformed relation module, then Nakayama at `ker evInfty`) and is *not*
claimed here.

No `VacuumGradeZero` hypothesis: it holds for every VOA. -/
theorem finrank_quot_blockRelSpanAtCusp_le_card_Φ [Finite (Φ W)]
    (hfd : letI := instRingA W; FiniteDimensional ℂ (A W))
    (hss : letI := instRingA W; IsSemisimpleRing (A W))
    (hreal : SimpleAModsRealized W)
    (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W))) :
    Module.finrank ℂ (𝒱 ⧸ blockRelSpanAtCusp W) ≤ Nat.card (Φ W) := by
  rw [finrank_quot_blockRelSpanAtCusp_eq]
  exact finrank_quot_commSpan_le_card_Φ W hfd hss hreal Pr

end VOA
