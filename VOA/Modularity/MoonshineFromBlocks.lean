/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modularity.RhoS
import VOA.Modularity.BlockRank
import VOA.Modularity.BlockFiniteDim
import VOA.Modularity.MoonshineHauptmodul

/-!
# The Moonshine character statement, from the block-spanning statement

`Modularity.RhoS` derives Zhu's modularity from the single spanning statement
`BlockSpannedByTraces`.  For a **holomorphic** VOA of central charge `24` — one irreducible module,
`Φ(𝒱) = {𝒱}`, conformal weight `0` — Gannon's main corollary follows at once, because `ρ` is then
forced
to be trivial (`modularRepOf_eq_one_of_holomorphic`):

  `char_SL2Z_invariant_of_blockSpanned` — `χ(Aτ) = χ(τ)` for every `A ∈ SL₂(ℤ)`;
  `char_sub_jInvariant_smul_of_blockSpanned` — hence `χ − j` is `SL₂(ℤ)`-invariant, and
  `Modularity.MoonshineHauptmodul.char_eq_jInvariant_add_const` finishes Question 5.3.4 in the
  abstract form `χ = J + const`.

This is kept in Gannon's **abstract** Q-5.3.4 form and is not instantiated at `V♮`.  The VOA
`V♮` is constructed in `VOA/Moonshine` (`Moonshine.moonshine`, which proves `dim V♮ₙ = [qⁿ]JShift`
directly, not through this file).

## Status
Proved, axiom-clean, `pbw`-free, no `sorry`, conditional on exactly the named data of
`Modularity.RhoS` plus the nonvanishing `hne`.
-/

namespace VOA

open scoped BigOperators MatrixGroups

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

/-- For a one-element family the `T`-eigenvalue map is trivially injective. -/
theorem tEigen_injective_unit (h : Unit → ℂ) : Function.Injective (tEigen W h) :=
  fun a b _ => Subsingleton.elim a b

/-- **The character of a holomorphic `c = 24` VOA is `SL₂(ℤ)`-invariant** — from the
block-spanning statement, i.e. from the analytic theory of `Modularity.{AnalyticBlock, BlockSlash,
GradedBlock}` together with the named inputs of `Modularity.RhoS`. -/
theorem char_SL2Z_invariant_of_blockSpanned (V : IrrModule W)
    (hcw : HasConformalWeight V.isMod 0)
    (hsub : ∀ i : Unit, OnePointSubexp (singleFam V i).isMod
      ((fun _ : Unit => (0 : ℂ)) i - W.centralCharge / 24))
    (hwt : SqModeWeighted W)
    (hspan : BlockSpannedByTraces (singleFam V) (fun _ => (0 : ℂ)))
    (hnv : TraceNonvanishing (singleFam V) (fun _ => (0 : ℂ)))
    (hc : W.centralCharge = 24)
    (hne : ∃ τ : UpperHalfPlane, traceFun (singleFam V) (fun _ => (0 : ℂ)) () W.vacuum τ ≠ 0)
    (A : SL(2, ℤ)) (τ : UpperHalfPlane) :
    traceFun (singleFam V) (fun _ => (0 : ℂ)) () W.vacuum (A • τ)
      = traceFun (singleFam V) (fun _ => (0 : ℂ)) () W.vacuum τ := by
  have hcwf : ∀ i : Unit, HasConformalWeight (singleFam V i).isMod ((fun _ : Unit => (0 : ℂ)) i) :=
    fun _ => hcw
  have hsp : TraceSpanning (singleFam V) (fun _ => (0 : ℂ)) :=
    traceSpanning_of_blockSpanned (singleFam V) (fun _ => (0 : ℂ)) hcwf hsub hwt hspan
  have hind : TraceIndependent (singleFam V) (fun _ => (0 : ℂ)) :=
    traceIndependent_of_tEigen_injective (singleFam V) (fun _ => (0 : ℂ)) hcwf
      (tEigen_injective_unit _) hnv
  exact char_SL2Z_invariant_of_spanning V hsp hind hcw hc hne A τ

/-- **`χ − j` is `SL₂(ℤ)`-invariant**, from the block-spanning statement. -/
theorem char_sub_jInvariant_smul_of_blockSpanned (V : IrrModule W)
    (hcw : HasConformalWeight V.isMod 0)
    (hsub : ∀ i : Unit, OnePointSubexp (singleFam V i).isMod
      ((fun _ : Unit => (0 : ℂ)) i - W.centralCharge / 24))
    (hwt : SqModeWeighted W)
    (hspan : BlockSpannedByTraces (singleFam V) (fun _ => (0 : ℂ)))
    (hnv : TraceNonvanishing (singleFam V) (fun _ => (0 : ℂ)))
    (hc : W.centralCharge = 24)
    (hne : ∃ τ : UpperHalfPlane, traceFun (singleFam V) (fun _ => (0 : ℂ)) () W.vacuum τ ≠ 0)
    (A : SL(2, ℤ)) (τ : UpperHalfPlane) :
    traceFun (singleFam V) (fun _ => (0 : ℂ)) () W.vacuum (A • τ) - jInvariant (A • τ)
      = traceFun (singleFam V) (fun _ => (0 : ℂ)) () W.vacuum τ - jInvariant τ := by
  rw [char_SL2Z_invariant_of_blockSpanned V hcw hsub hwt hspan hnv hc hne A τ, jInvariant_smul A τ]

/-- **The Moonshine consequence from a one-line dimension bound.**

For a holomorphic VOA of central charge `24` — one irreducible module, conformal weight `0` — the
graded dimension is `SL₂(ℤ)`-invariant **as soon as the space of genus-one conformal blocks is at
most one-dimensional**.  Everything else is proved: the trace function is a block, the block
conditions are `SL₂(ℤ)`-stable, and the trace function is nonzero, so it already accounts for that
one dimension.

This is the sharpest packaging of Gannon's Question 5.3.4 reachable here; `dim 𝔅 ≤ 1` is the
`#Φ(𝒱) = 1` case of Zhu's Theorems 5.3.2–5.3.3. -/
theorem char_SL2Z_invariant_of_rank_le (V : IrrModule W)
    (hcw : HasConformalWeight V.isMod 0)
    (hsub : ∀ i : Unit, OnePointSubexp (singleFam V i).isMod
      ((fun _ : Unit => (0 : ℂ)) i - W.centralCharge / 24))
    (hwt : SqModeWeighted W)
    (hnv : TraceNonvanishing (singleFam V) (fun _ => (0 : ℂ)))
    (hrank : Module.rank ℂ (Submodule.map restrictImGT (gradedBlocks W)) ≤ 1)
    (hc : W.centralCharge = 24)
    (hne : ∃ τ : UpperHalfPlane, traceFun (singleFam V) (fun _ => (0 : ℂ)) () W.vacuum τ ≠ 0)
    (A : SL(2, ℤ)) (τ : UpperHalfPlane) :
    traceFun (singleFam V) (fun _ => (0 : ℂ)) () W.vacuum (A • τ)
      = traceFun (singleFam V) (fun _ => (0 : ℂ)) () W.vacuum τ := by
  have hcwf : ∀ i : Unit, HasConformalWeight (singleFam V i).isMod ((fun _ : Unit => (0 : ℂ)) i) :=
    fun _ => hcw
  have hind : TraceIndependent (singleFam V) (fun _ => (0 : ℂ)) :=
    traceIndependent_of_tEigen_injective (singleFam V) (fun _ => (0 : ℂ)) hcwf
      (tEigen_injective_unit _) hnv
  have hcard : ((Fintype.card Unit : ℕ) : Cardinal) = 1 := by simp
  have hspan : BlockSpannedByTraces (singleFam V) (fun _ => (0 : ℂ)) :=
    blockSpannedByTraces_of_rank_le (singleFam V) (fun _ => (0 : ℂ)) hcwf hsub hind
      (by rw [hcard]; exact hrank)
  exact char_SL2Z_invariant_of_blockSpanned V hcw hsub hwt hspan hnv hc hne A τ

/-- **Gannon's Question 5.3.4, minimal form.**

For a **holomorphic** VOA of central charge `24` the graded dimension is `SL₂(ℤ)`-invariant given
exactly three things: the conformal weight, the growth datum (reduced in
`Modularity.OnePointDescent` to `g+1` sequences), Zhu's square-bracket mode grading, and the
dimension bound `dim 𝔅 ≤ 1`.  The nonvanishing data (`TraceNonvanishing`, `hne`) are **discharged**
from the growth datum (`traceNonvanishing_of_onePointSubexp`, `traceFun_vacuum_ne_zero`).

Feed the conclusion to `Modularity.MoonshineHauptmodul.char_eq_jInvariant_add_const` for
`χ = J + const`. -/
theorem char_SL2Z_invariant_minimal (V : IrrModule W)
    (hcw : HasConformalWeight V.isMod 0)
    (hsub : ∀ i : Unit, OnePointSubexp (singleFam V i).isMod
      ((fun _ : Unit => (0 : ℂ)) i - W.centralCharge / 24))
    (hwt : SqModeWeighted W)
    (hrank : Module.rank ℂ (Submodule.map restrictImGT (gradedBlocks W)) ≤ 1)
    (hc : W.centralCharge = 24)
    (A : SL(2, ℤ)) (τ : UpperHalfPlane) :
    traceFun (singleFam V) (fun _ => (0 : ℂ)) () W.vacuum (A • τ)
      = traceFun (singleFam V) (fun _ => (0 : ℂ)) () W.vacuum τ := by
  have hcwf : ∀ i : Unit, HasConformalWeight (singleFam V i).isMod ((fun _ : Unit => (0 : ℂ)) i) :=
    fun _ => hcw
  exact char_SL2Z_invariant_of_rank_le V hcw hsub hwt
    (traceNonvanishing_of_onePointSubexp (singleFam V) (fun _ => (0 : ℂ)) hcwf hsub) hrank hc
    (traceFun_vacuum_ne_zero (singleFam V) (fun _ => (0 : ℂ)) hcwf hsub ()) A τ

/-- **GANNON'S QUESTION 5.3.4, SHARPEST FORM.**

For a holomorphic VOA of central charge `24`, the graded dimension is `SL₂(ℤ)`-invariant given
exactly **three** substantive inputs:

* `hcw` — the module has conformal weight `0` (definitional for a holomorphic VOA);
* `hsub` — the growth datum, which `Modularity.OnePointDescent` reduces to `g + 1` sequences;
* `hrank` — `dim 𝔅 ≤ 1`, the `#Φ(𝒱) = 1` case of Zhu's Theorems 5.3.2–5.3.3.

Everything else is proved here: the trace function is a genus-one block, the block conditions are
`SL₂(ℤ)`-stable, independence and nonvanishing are discharged, and — because this route goes
through `slashSpannedAtS_of_rank_le` — **`SqModeWeighted` is not needed either**.

Feed the conclusion to `Modularity.MoonshineHauptmodul.char_eq_jInvariant_add_const` for
`χ = J + const`. -/
theorem char_SL2Z_invariant_of_slashRank (V : IrrModule W)
    (hcw : HasConformalWeight V.isMod 0)
    (hsub : ∀ i : Unit, OnePointSubexp (singleFam V i).isMod
      ((fun _ : Unit => (0 : ℂ)) i - W.centralCharge / 24))
    (hrank : Module.rank ℂ (slashAmbient (singleFam V) (fun _ => (0 : ℂ)) ModularGroup.S) ≤ 1)
    (hc : W.centralCharge = 24)
    (A : SL(2, ℤ)) (τ : UpperHalfPlane) :
    traceFun (singleFam V) (fun _ => (0 : ℂ)) () W.vacuum (A • τ)
      = traceFun (singleFam V) (fun _ => (0 : ℂ)) () W.vacuum τ := by
  have hcwf : ∀ i : Unit, HasConformalWeight (singleFam V i).isMod ((fun _ : Unit => (0 : ℂ)) i) :=
    fun _ => hcw
  have hnv : TraceNonvanishing (singleFam V) (fun _ => (0 : ℂ)) :=
    traceNonvanishing_of_onePointSubexp (singleFam V) (fun _ => (0 : ℂ)) hcwf hsub
  have hind : TraceIndependent (singleFam V) (fun _ => (0 : ℂ)) :=
    traceIndependent_of_tEigen_injective (singleFam V) (fun _ => (0 : ℂ)) hcwf
      (tEigen_injective_unit _) hnv
  have hcard : ((Fintype.card Unit : ℕ) : Cardinal) = 1 := by simp
  have hsp : TraceSpanning (singleFam V) (fun _ => (0 : ℂ)) :=
    traceSpanning_of_slashSpannedAtS (singleFam V) (fun _ => (0 : ℂ)) hcwf hsub
      (slashSpannedAtS_of_rank_le (singleFam V) (fun _ => (0 : ℂ)) hcwf hsub hind
        (by rw [hcard]; exact hrank))
  exact char_SL2Z_invariant_of_spanning V hsp hind hcw hc
    (traceFun_vacuum_ne_zero (singleFam V) (fun _ => (0 : ℂ)) hcwf hsub ()) A τ

/-- **Gannon's Question 5.3.4 with finite-dimensionality discharged.**

For a `C₂`-cofinite **holomorphic** VOA of central charge `24`, the graded dimension is
`SL₂(ℤ)`-invariant given the conformal weight, the growth datum (itself reduced by
`Modularity.OnePointDescent` to `g` generator sequences), and the single inequality
`dim 𝔅 ≤ 1`.  That the space `𝔅` is finite-dimensional at all is a **theorem**
(`Modularity.BlockFiniteDim`, Zhu Thm 5.3.2), not a hypothesis. -/
theorem char_SL2Z_invariant_of_analyticRank (V : IrrModule W) (hC2 : C2Cofinite W) {z₀ : ℂ}
    (hz₀ : z₀ ∈ imGT 0) (hcw : HasConformalWeight V.isMod 0)
    (hsub : ∀ i : Unit, OnePointSubexp (singleFam V i).isMod
      ((fun _ : Unit => (0 : ℂ)) i - W.centralCharge / 24))
    (hle : Module.finrank ℂ (analyticSlashAmbient (singleFam V) (fun _ => (0 : ℂ))) ≤ 1)
    (hc : W.centralCharge = 24)
    (A : SL(2, ℤ)) (τ : UpperHalfPlane) :
    traceFun (singleFam V) (fun _ => (0 : ℂ)) () W.vacuum (A • τ)
      = traceFun (singleFam V) (fun _ => (0 : ℂ)) () W.vacuum τ := by
  have hcwf : ∀ i : Unit, HasConformalWeight (singleFam V i).isMod ((fun _ : Unit => (0 : ℂ)) i) :=
    fun _ => hcw
  have hnv : TraceNonvanishing (singleFam V) (fun _ => (0 : ℂ)) :=
    traceNonvanishing_of_onePointSubexp (singleFam V) (fun _ => (0 : ℂ)) hcwf hsub
  have hind : TraceIndependent (singleFam V) (fun _ => (0 : ℂ)) :=
    traceIndependent_of_tEigen_injective (singleFam V) (fun _ => (0 : ℂ)) hcwf
      (tEigen_injective_unit _) hnv
  haveI := finiteDimensional_analyticSlashAmbient (singleFam V) (fun _ => (0 : ℂ)) hC2 hz₀
  have hrank : Module.rank ℂ (analyticSlashAmbient (singleFam V) (fun _ => (0 : ℂ)))
      ≤ (Fintype.card Unit : Cardinal) := by
    rw [← Module.finrank_eq_rank]
    have : (Fintype.card Unit : ℕ) = 1 := by simp
    rw [this]
    exact_mod_cast hle
  have hsp : TraceSpanning (singleFam V) (fun _ => (0 : ℂ)) :=
    traceSpanning_of_slashSpannedAtS (singleFam V) (fun _ => (0 : ℂ)) hcwf hsub
      (slashSpannedAtS_of_rank_le' (singleFam V) (fun _ => (0 : ℂ)) _ hind
        (traceBlock_mem_analyticSlashAmbient (singleFam V) (fun _ => (0 : ℂ)) hcwf hsub)
        (slash_mem_analyticSlashAmbient (singleFam V) (fun _ => (0 : ℂ))) hrank)
  exact char_SL2Z_invariant_of_spanning V hsp hind hcw hc
    (traceFun_vacuum_ne_zero (singleFam V) (fun _ => (0 : ℂ)) hcwf hsub ()) A τ

end VOA
