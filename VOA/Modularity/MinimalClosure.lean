/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.SqAmbientAssembly

/-!
# Zhu's modularity theorem on the minimal hypothesis closure

The assemblies of `Modularity.SqAmbientAssembly` consume `tEigen`-injectivity — the hypothesis
that the conformal weights of the family are pairwise distinct modulo `ℤ` — only in order to
produce `TraceIndependent` (through `traceIndependent_of_tEigen_injective`, which also needs the
growth datum, to get `TraceNonvanishing`).  That is strictly more than the theorem needs:
`Modularity.TraceIndependence.traceIndependent_of_fibreIndependent` derives `TraceIndependent`
from `FibreIndependent` — the `T`-eigenvalue-class-local statement — **with no distinctness
hypothesis and no growth datum**.

So the versions below take `TraceIndependent` (or `FibreIndependent`) directly, and `tEigen`
disappears from the closure.

## Hypothesis closure of `zhu_modularity_of_sqAnalyticRank_le_of_traceIndependent`

Traced to the leaves:

* `hcw : ∀ i, HasConformalWeight (Mfam i).isMod (h i)` — structural grading data;
* `hgr : ∀ i, OnePointSubexp …` — the growth datum (reduced by `Modularity.OnePointDescent` to
  the `g+1` `C₂`-generator sequences; not yet fully derived from `C2Cofinite`);
* `hind : TraceIndependent Mfam h` — implied by `FibreIndependent` (Pr-free, distinctness-free);
* `hrank : rank ℂ (sqAnalyticSlashAmbient Mfam h) ≤ #ι` — Zhu Thms 5.3.2–5.3.3.

`C2Cofinite` enters only through `finiteDimensional_sqAnalyticSlashAmbient` when the `finrank`
form is used.  **No `Pr`, no `tEigen`, no `SqModeWeighted`** on the analytic ambient.

## Status
Proved, axiom-clean, `pbw`-free, no `sorry`.
-/

namespace VOA

open Complex
open scoped BigOperators MatrixGroups

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {W : VertexOperatorAlgebra 𝒱}
variable (Mfam : ι → IrrModule W) (h : ι → ℂ)

/-- **Zhu's modularity theorem, `tEigen`-free.** -/
theorem zhu_modularity_of_sqAnalyticRank_le_of_traceIndependent
    (hcw : ∀ i, HasConformalWeight (Mfam i).isMod (h i))
    (hgr : ∀ i, OnePointSubexp (Mfam i).isMod (h i - W.centralCharge / 24))
    (hind : TraceIndependent Mfam h)
    (hrank : Module.rank ℂ (sqAnalyticSlashAmbient Mfam h) ≤ (Fintype.card ι : Cardinal)) :
    ZhuModularityAnalytic
      (modularDataOf Mfam h
        (traceSpanning_of_slashSpannedAtS Mfam h hcw hgr
          (slashSpannedAtS_of_sqRank_le Mfam h (sqAnalyticSlashAmbient Mfam h) hind
            (sqRestrict_traceBlock_mem_sqAnalyticSlashAmbient Mfam h hcw hgr)
            (sqRestrict_slash_mem_sqAnalyticSlashAmbient Mfam h) hrank))
        hind hcw) :=
  zhu_modularity_of_spanning Mfam h _ _ hcw

/-- The same on the graded ambient (which trades `C₂`-finite-dimensionality for the
pre-existing `SqModeWeighted`). -/
theorem zhu_modularity_of_sqGradedRank_le_of_traceIndependent
    (hcw : ∀ i, HasConformalWeight (Mfam i).isMod (h i))
    (hgr : ∀ i, OnePointSubexp (Mfam i).isMod (h i - W.centralCharge / 24))
    (hwt : SqModeWeighted W)
    (hind : TraceIndependent Mfam h)
    (hrank : Module.rank ℂ (sqGradedAmbient W) ≤ (Fintype.card ι : Cardinal)) :
    ZhuModularityAnalytic
      (modularDataOf Mfam h
        (traceSpanning_of_slashSpannedAtS Mfam h hcw hgr
          (slashSpannedAtS_of_sqRank_le Mfam h (sqGradedAmbient W) hind
            (sqRestrict_traceBlock_mem_sqGradedAmbient Mfam h hcw hgr)
            (sqRestrict_slash_mem_sqGradedAmbient Mfam h hwt hcw hgr) hrank))
        hind hcw) :=
  zhu_modularity_of_spanning Mfam h _ _ hcw

/-- **Zhu's modularity theorem from `FibreIndependent`** — the `T`-eigenvalue-class-local
form of independence, which needs neither distinct weights nor the growth datum to be stated. -/
theorem zhu_modularity_of_sqAnalyticRank_le_of_fibreIndependent
    (hcw : ∀ i, HasConformalWeight (Mfam i).isMod (h i))
    (hgr : ∀ i, OnePointSubexp (Mfam i).isMod (h i - W.centralCharge / 24))
    (hfib : FibreIndependent Mfam h)
    (hrank : Module.rank ℂ (sqAnalyticSlashAmbient Mfam h) ≤ (Fintype.card ι : Cardinal)) :
    ZhuModularityAnalytic
      (modularDataOf Mfam h
        (traceSpanning_of_slashSpannedAtS Mfam h hcw hgr
          (slashSpannedAtS_of_sqRank_le Mfam h (sqAnalyticSlashAmbient Mfam h)
            (traceIndependent_of_fibreIndependent Mfam h hcw hfib)
            (sqRestrict_traceBlock_mem_sqAnalyticSlashAmbient Mfam h hcw hgr)
            (sqRestrict_slash_mem_sqAnalyticSlashAmbient Mfam h) hrank))
        (traceIndependent_of_fibreIndependent Mfam h hcw hfib) hcw) :=
  zhu_modularity_of_spanning Mfam h _ _ hcw

/-- The `v = 0` slice of Theorem 5.3.9, on the same minimal closure. -/
theorem exists_jacobiTransformation_v_zero_minimal (β : 𝒱 →ₗ[ℂ] 𝒱 →ₗ[ℂ] ℂ)
    (hcw : ∀ i, HasConformalWeight (Mfam i).isMod (h i))
    (hgr : ∀ i, OnePointSubexp (Mfam i).isMod (h i - W.centralCharge / 24))
    (hind : TraceIndependent Mfam h)
    (hrank : Module.rank ℂ (sqAnalyticSlashAmbient Mfam h) ≤ (Fintype.card ι : Cardinal)) :
    ∃ D : ModularData W ι, ZhuModularityAnalytic D ∧
      ∀ (A : SL(2, ℤ)) (w : ℂ) (i : ι) (τ : UpperHalfPlane),
        jacobiChar (D.Mfam i).isMod (D.h i) β ((autFactor A τ)⁻¹ • (0 : 𝒱))
            (w - ((A : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) * β 0 0 / (2 * autFactor A τ)) (A • τ)
          = ∑ j, D.rep A i j * jacobiChar (D.Mfam j).isMod (D.h j) β 0 w τ :=
  ⟨_, zhu_modularity_of_sqAnalyticRank_le_of_traceIndependent Mfam h hcw hgr hind hrank,
    fun A w i τ => jacobiTransformation_v_zero_of_zhu _ β
      (zhu_modularity_of_sqAnalyticRank_le_of_traceIndependent Mfam h hcw hgr hind hrank) A w i τ⟩

end

end VOA
