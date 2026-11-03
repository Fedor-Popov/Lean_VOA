/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.SlashAmbientObstruction
import VOA.Modularity.JacobiZhu
import VOA.Modularity.MoonshineFromBlocks

/-!
# The modularity consumers on the square-graded ambient

`Modularity.SlashAmbientObstruction` shows that the rank hypothesis on `analyticSlashAmbient` is
**contradictory**, so every downstream statement that consumed it — the `v = 0` slice of Zhu's
Theorem 5.3.9 (`exists_jacobiTransformation_v_zero`) and Gannon's Question 5.3.4
(`char_SL2Z_invariant_of_analyticRank`) — was resting on a vacuous hypothesis.

This file restates both over the repaired ambients, where the hypothesis is satisfiable:

* `sqAnalyticSlashAmbient` — `L[0]`-homogeneous restrictions of the analytic blocks plus the
  `S`-slashes; **finite-dimensional unconditionally** (`finiteDimensional_sqAnalyticSlashAmbient`,
  i.e. Zhu Thm 5.3.2 survives the repair);
* `sqGradedAmbient` — the graded blocks, where both membership hypotheses are discharged from
  `isGradedBlock_blockSlash` (consuming the pre-existing `SqModeWeighted`).

## Main results

* `exists_jacobiTransformation_v_zero_sq` / `_sqGraded` — the `v = 0` slice of Thm 5.3.9
  (5.3.20) for **every** `A ∈ SL₂(ℤ)`, on the repaired hypothesis;
* `char_SL2Z_invariant_of_sqAnalyticRank` — Gannon's Question 5.3.4 (`c = 24`, holomorphic ⟹
  the character is `SL₂(ℤ)`-invariant), on the repaired hypothesis.

Together with the **unconditional** `A = T` slice `jacobiTransformation_T_holds` and the stated
Conjecture 5.3.10 (`Modularity.Twisted.Conjecture_5_3_10`), this is the honest content of the
`Modularity/JacobiCharacter` row.  The general `(A, v)` case of 5.3.9 is Miyamoto's `𝒱₁`-refinement
of Zhu's recursion — a separate theory, not a consequence of `ρ`.

## Status
Proved, axiom-clean, `pbw`-free, no `sorry`.
-/

namespace VOA

open Complex
open scoped BigOperators MatrixGroups

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

section Jacobi

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {W : VertexOperatorAlgebra 𝒱}

/-- **The `v = 0` slice of Theorem 5.3.9 (5.3.20), on the repaired analytic ambient.**  Same
inputs as Zhu's theorem; unlike `exists_jacobiTransformation_v_zero`, the rank hypothesis here is
satisfiable (see `not_rank_analyticSlashAmbient_le`). -/
theorem exists_jacobiTransformation_v_zero_sq (Mfam : ι → IrrModule W) (hh : ι → ℂ)
    (β : 𝒱 →ₗ[ℂ] 𝒱 →ₗ[ℂ] ℂ)
    (hcw : ∀ i, HasConformalWeight (Mfam i).isMod (hh i))
    (hgr : ∀ i, OnePointSubexp (Mfam i).isMod (hh i - W.centralCharge / 24))
    (hinj : Function.Injective (tEigen W hh))
    (hrank : Module.rank ℂ (sqAnalyticSlashAmbient Mfam hh) ≤ (Fintype.card ι : Cardinal)) :
    ∃ D : ModularData W ι, ZhuModularityAnalytic D ∧
      ∀ (A : SL(2, ℤ)) (w : ℂ) (i : ι) (τ : UpperHalfPlane),
        jacobiChar (D.Mfam i).isMod (D.h i) β ((autFactor A τ)⁻¹ • (0 : 𝒱))
            (w - ((A : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) * β 0 0 / (2 * autFactor A τ)) (A • τ)
          = ∑ j, D.rep A i j * jacobiChar (D.Mfam j).isMod (D.h j) β 0 w τ :=
  ⟨_, zhu_modularity_of_sqAnalyticRank_le Mfam hh hcw hgr hinj hrank,
    fun A w i τ => jacobiTransformation_v_zero_of_zhu _ β
      (zhu_modularity_of_sqAnalyticRank_le Mfam hh hcw hgr hinj hrank) A w i τ⟩

/-- The `finrank` form: `C₂`-cofiniteness makes the repaired analytic ambient finite-dimensional
(`finiteDimensional_sqAnalyticSlashAmbient`), so `hfd` stays discharged. -/
theorem exists_jacobiTransformation_v_zero_sq' (Mfam : ι → IrrModule W) (hh : ι → ℂ)
    (β : 𝒱 →ₗ[ℂ] 𝒱 →ₗ[ℂ] ℂ) (hC2 : C2Cofinite W) {z₀ : ℂ} (hz₀ : z₀ ∈ imGT 0)
    (hcw : ∀ i, HasConformalWeight (Mfam i).isMod (hh i))
    (hgr : ∀ i, OnePointSubexp (Mfam i).isMod (hh i - W.centralCharge / 24))
    (hinj : Function.Injective (tEigen W hh))
    (hle : Module.finrank ℂ (sqAnalyticSlashAmbient Mfam hh) ≤ Fintype.card ι) :
    ∃ D : ModularData W ι, ZhuModularityAnalytic D ∧
      ∀ (A : SL(2, ℤ)) (w : ℂ) (i : ι) (τ : UpperHalfPlane),
        jacobiChar (D.Mfam i).isMod (D.h i) β ((autFactor A τ)⁻¹ • (0 : 𝒱))
            (w - ((A : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) * β 0 0 / (2 * autFactor A τ)) (A • τ)
          = ∑ j, D.rep A i j * jacobiChar (D.Mfam j).isMod (D.h j) β 0 w τ := by
  haveI := finiteDimensional_sqAnalyticSlashAmbient Mfam hh hC2 hz₀
  refine exists_jacobiTransformation_v_zero_sq Mfam hh β hcw hgr hinj ?_
  rw [← Module.finrank_eq_rank]
  exact_mod_cast hle

/-- The same slice on the **graded** repaired ambient, where the two membership hypotheses are
free from `SqModeWeighted`. -/
theorem exists_jacobiTransformation_v_zero_sqGraded (Mfam : ι → IrrModule W) (hh : ι → ℂ)
    (β : 𝒱 →ₗ[ℂ] 𝒱 →ₗ[ℂ] ℂ)
    (hcw : ∀ i, HasConformalWeight (Mfam i).isMod (hh i))
    (hgr : ∀ i, OnePointSubexp (Mfam i).isMod (hh i - W.centralCharge / 24))
    (hwt : SqModeWeighted W)
    (hinj : Function.Injective (tEigen W hh))
    (hrank : Module.rank ℂ (sqGradedAmbient W) ≤ (Fintype.card ι : Cardinal)) :
    ∃ D : ModularData W ι, ZhuModularityAnalytic D ∧
      ∀ (A : SL(2, ℤ)) (w : ℂ) (i : ι) (τ : UpperHalfPlane),
        jacobiChar (D.Mfam i).isMod (D.h i) β ((autFactor A τ)⁻¹ • (0 : 𝒱))
            (w - ((A : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) * β 0 0 / (2 * autFactor A τ)) (A • τ)
          = ∑ j, D.rep A i j * jacobiChar (D.Mfam j).isMod (D.h j) β 0 w τ :=
  ⟨_, zhu_modularity_of_sqGradedRank_le Mfam hh hcw hgr hwt hinj hrank,
    fun A w i τ => jacobiTransformation_v_zero_of_zhu _ β
      (zhu_modularity_of_sqGradedRank_le Mfam hh hcw hgr hwt hinj hrank) A w i τ⟩

end Jacobi

/-! ## Gannon's Question 5.3.4, on the repaired ambient -/

section Moonshine

variable {W : VertexOperatorAlgebra 𝒱}

/-- **Gannon Question 5.3.4, repaired**: a holomorphic `C₂`-cofinite `𝒱` with `c = 24` has an
`SL₂(ℤ)`-invariant character, from the *satisfiable* rank bound on `sqAnalyticSlashAmbient`. -/
theorem char_SL2Z_invariant_of_sqAnalyticRank (V : IrrModule W) (hC2 : C2Cofinite W) {z₀ : ℂ}
    (hz₀ : z₀ ∈ imGT 0) (hcw : HasConformalWeight V.isMod 0)
    (hsub : ∀ i : Unit, OnePointSubexp (singleFam V i).isMod
      ((fun _ : Unit => (0 : ℂ)) i - W.centralCharge / 24))
    (hle : Module.finrank ℂ (sqAnalyticSlashAmbient (singleFam V) (fun _ => (0 : ℂ))) ≤ 1)
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
  haveI := finiteDimensional_sqAnalyticSlashAmbient (singleFam V) (fun _ => (0 : ℂ)) hC2 hz₀
  have hrank : Module.rank ℂ (sqAnalyticSlashAmbient (singleFam V) (fun _ => (0 : ℂ)))
      ≤ (Fintype.card Unit : Cardinal) := by
    rw [← Module.finrank_eq_rank, show (Fintype.card Unit : ℕ) = 1 from by simp]
    exact_mod_cast hle
  have hsp : TraceSpanning (singleFam V) (fun _ => (0 : ℂ)) :=
    traceSpanning_of_slashSpannedAtS (singleFam V) (fun _ => (0 : ℂ)) hcwf hsub
      (slashSpannedAtS_of_sqRank_le (singleFam V) (fun _ => (0 : ℂ)) _ hind
        (sqRestrict_traceBlock_mem_sqAnalyticSlashAmbient (singleFam V) (fun _ => (0 : ℂ)) hcwf hsub)
        (sqRestrict_slash_mem_sqAnalyticSlashAmbient (singleFam V) (fun _ => (0 : ℂ))) hrank)
  exact char_SL2Z_invariant_of_spanning V hsp hind hcw hc
    (traceFun_vacuum_ne_zero (singleFam V) (fun _ => (0 : ℂ)) hcwf hsub ()) A τ

end Moonshine

end VOA
