/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.BlockRelSpanTransport
import VOA.Modularity.ZhuCountC2

/-!
# Zhu's Theorem 5.3.3 — `dim 𝔅 ≤ #Φ(𝒱)`

The target here is *one inequality between two natural numbers*: the dimension of
the space of genus-one conformal blocks is at most the number of irreducible `𝒱`-modules.  This
file assembles it.

## The chain

1. **The count at the cusp** (`Modularity.ZhuCount`, `Modularity.ZhuCountC2`):
   `dim (𝒱 ⧸ blockRelSpanAtCusp 𝒱) = dim A(𝒱)/[A(𝒱),A(𝒱)] ≤ #Φ(𝒱)`, using L1
   (Artin–Wedderburn in the language of `AMod`), L2's single gate `SimpleAModsRealized`, L3
   (`IrrLWModuleIsoClass ≃ Φ`), and Zhu's bijection `zhuBijective Pr`.
2. **A cusp-spanning family of that size** (`CuspPoint.exists_finset_card_le_span_sup_eq_top`).
3. **Zhu Lemma 4.4.1 / DLM Lemma 5.2** (`Modularity.BlockRelSpanE`): the relation module is finite
   over `E46 = ℂ[E₄,E₆]`.
4. **The transport** (`Modularity.BlockRelSpanTransport`): Nakayama at the cusp point moves that
   spanning family to an **interior** `z₀ ∈ ℍ`.
5. **The dual descent** (`BlockFiniteDim.finrank_analyticBlocks_le_card_of_blockRel`): a spanning
   family at `z₀` bounds the block space.

## Main result

* `finrank_analyticBlocks_le_card_Φ` — **`dim 𝔅 ≤ #Φ(𝒱)`**.

## What this does and does not close

It closes the *dimension count* of residual **(a)** for the analytic block space `𝔅`.  It does
**not** by itself supply the `hrank` hypothesis of
`Modularity.ConformalWeightChoice.zhu_modularity_of_sqAnalyticRank_le_irr`, because that hypothesis
is about `sqAnalyticSlashAmbient = map sqRestrict 𝔅 ⊔ span (range of the S-slashes of the trace
blocks)`.  Bounding the second summand is residual **(e1)** — *analytic representability of the
`S`-slash* — which is a separate, open statement.

## Status
Proof-term `#print axioms`-clean, no `sorry`, but conditional on the displayed inputs:
`VacuumGradeZero`, `C2Cofinite`, `IsSemisimpleRing (A 𝒱)`, `SimpleAModsRealized 𝒱`,
`Finite (Φ 𝒱)`, and the explicit `BottomProjection` assumption `Pr`. The project-level
`regularAMod` witness is supplied by `voaPBWBottomProjection`, from the generic
relative-induction field of the theorem `VOA.pbw : PBWPrinciple`.
-/

namespace VOA

open VHat VHat.DLM3 Module

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] (W : VertexOperatorAlgebra 𝒱)

/-- **A spanning family of size `≤ #Φ(𝒱)` at an interior point.**  Steps 1–4 of the chain. -/
theorem exists_interior_span_sup_blockRelSpan_card_le_Φ [Finite (Φ W)]
    (hzero : VacuumGradeZero W) (hC2 : C2Cofinite W)
    (hss : letI := instRingA W; IsSemisimpleRing (A W))
    (hreal : SimpleAModsRealized W)
    (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W))) :
    ∃ (T : Finset 𝒱) (z₀ : UpperHalfPlane), T.card ≤ Nat.card (Φ W) ∧
      (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ (T : Set 𝒱) ⊔ blockRelSpan W (z₀ : ℂ) := by
  classical
  haveI : FiniteDimensional ℂ (𝒱 ⧸ blockRelSpanAtCusp W) :=
    finiteDimensional_quot_blockRelSpanAtCusp (finiteDimensional_A_of_C2Cofinite W hC2)
  obtain ⟨T, hTcard, hTspan⟩ :=
    exists_finset_card_le_span_sup_eq_top (K := blockRelSpanAtCusp W)
      (finrank_quot_blockRelSpanAtCusp_le_card_Φ_of_C2 W hC2 hss hreal Pr)
  obtain ⟨z₀, hz₀⟩ :=
    exists_interior_span_sup_blockRelSpan_of_cusp W hzero hC2 (T : Set 𝒱) hTspan
  exact ⟨T, z₀, hTcard, hz₀⟩

/-- **ZHU'S THEOREM 5.3.3.**  The space of genus-one conformal blocks has dimension at
most the number of irreducible `𝒱`-modules. -/
theorem finrank_analyticBlocks_le_card_Φ [Finite (Φ W)]
    (hzero : VacuumGradeZero W) (hC2 : C2Cofinite W)
    (hss : letI := instRingA W; IsSemisimpleRing (A W))
    (hreal : SimpleAModsRealized W)
    (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W))) :
    Module.finrank ℂ (Submodule.map restrictImGT (analyticBlocks W)) ≤ Nat.card (Φ W) := by
  obtain ⟨T, z₀, hTcard, hz₀⟩ :=
    exists_interior_span_sup_blockRelSpan_card_le_Φ W hzero hC2 hss hreal Pr
  exact le_trans
    (finrank_analyticBlocks_le_card_of_blockRel (coe_mem_imGT_zero z₀) T hz₀).2 hTcard

/-- The same, with the block space also recorded as finite-dimensional. -/
theorem finiteDimensional_and_finrank_analyticBlocks_le_card_Φ [Finite (Φ W)]
    (hzero : VacuumGradeZero W) (hC2 : C2Cofinite W)
    (hss : letI := instRingA W; IsSemisimpleRing (A W))
    (hreal : SimpleAModsRealized W)
    (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W))) :
    FiniteDimensional ℂ (Submodule.map restrictImGT (analyticBlocks W)) ∧
      Module.finrank ℂ (Submodule.map restrictImGT (analyticBlocks W)) ≤ Nat.card (Φ W) := by
  obtain ⟨T, z₀, hTcard, hz₀⟩ :=
    exists_interior_span_sup_blockRelSpan_card_le_Φ W hzero hC2 hss hreal Pr
  obtain ⟨hfd, hle⟩ := finrank_analyticBlocks_le_card_of_blockRel (coe_mem_imGT_zero z₀) T hz₀
  exact ⟨hfd, le_trans hle hTcard⟩

end VOA
