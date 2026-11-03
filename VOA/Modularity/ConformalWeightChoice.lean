/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.LowestWeightExistence
import VOA.Modularity.MinimalClosure

/-!
# `hcw` is not a hypothesis — every irreducible module HAS a conformal weight

Every modularity theorem downstream of `Modularity.BlockSpanning` carries

  `hcw : ∀ i, HasConformalWeight (Mfam i).isMod (h i)`

as a named hypothesis, with `h : ι → ℂ` supplied as *data* alongside the family
`Mfam : ι → IrrModule 𝒱`.  Since `Modularity.LowestWeightExistence` proves Gannon Lemma 5.3.3's
existence half (`OrdVModule.exists_hasConformalWeight_of_irreducible`, unconditional), the weight is
not data at all: it is *determined* by the module, and `hcw` then holds by construction.

This file makes that canonical choice and re-states the sharpest banked forms of Zhu's theorem
with `hcw` **discharged**.

⚠ What this does *not* discharge: the independence datum.  With the canonical choice,
`tEigen W h i = modularTEntry W (conformalWeightOf (Mfam i))`, so the stronger `hinj` form says
distinct irreducibles have distinct `T`-eigenvalues `e^{2πi(hᵢ − c/24)}` — i.e. distinct conformal
weights mod `1`.  That is **false in general** (two non-isomorphic irreducibles may share a
conformal weight), which is precisely why the minimal closure uses the weaker, fibrewise
`FibreIndependent` instead.  It remains a genuine named hypothesis.

## Main results

* `conformalWeightOf` — the canonical conformal weight of an irreducible module;
* `hasConformalWeight_conformalWeightOf`, `hasConformalWeight_family`;
* `zhu_modularity_of_sqAnalyticRank_le_irr` — Zhu's law for every `A ∈ SL₂(ℤ)` with the
  hypothesis list reduced to exactly the three standing residuals `hgr`, `hfib`, `hrank`.

## Status
Proved, axiom-clean, `pbw`-free, no `sorry`.
-/

namespace VOA

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

/-- The **canonical conformal weight** of an irreducible `𝒱`-module, supplied by Lemma 5.3.3's
existence half. -/
noncomputable def conformalWeightOf (V : IrrModule W) : ℂ :=
  (OrdVModule.exists_hasConformalWeight_of_irreducible V.isMod V.irreducible).choose

/-- It is a conformal weight. -/
theorem hasConformalWeight_conformalWeightOf (V : IrrModule W) :
    HasConformalWeight V.isMod (conformalWeightOf V) :=
  (OrdVModule.exists_hasConformalWeight_of_irreducible V.isMod V.irreducible).choose_spec

/-- The family form: `hcw` holds for the canonical choice, for every family. -/
theorem hasConformalWeight_family {ι : Type*} (Mfam : ι → IrrModule W) :
    ∀ i, HasConformalWeight (Mfam i).isMod (conformalWeightOf (Mfam i)) :=
  fun i => hasConformalWeight_conformalWeightOf (Mfam i)

section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (Mfam : ι → IrrModule W)

/-- **Zhu's modularity theorem with `hcw` discharged**, on the *minimal closure*.

⚠ Built on `Modularity.MinimalClosure.zhu_modularity_of_sqAnalyticRank_le_of_fibreIndependent`,
NOT on `Modularity.BlockFiniteDim.zhu_modularity_of_analytic_finrank_le`: the latter is marked
**VACUOUS — DO NOT USE**, because
`SlashAmbientObstruction.not_finrank_analyticSlashAmbient_le` refutes its `hle`.  The satisfiable
ambient is the `L[0]`-homogeneous restriction `sqAnalyticSlashAmbient`.

The remaining hypotheses are exactly the three standing modularity residuals: `hgr` (the trace
growth
datum), `hfib` (fibrewise independence of the trace functions), and `hrank` (Zhu Thm 5.3.3 at an
interior point). -/
theorem zhu_modularity_of_sqAnalyticRank_le_irr
    (hgr : ∀ i, OnePointSubexp (Mfam i).isMod
      (conformalWeightOf (Mfam i) - W.centralCharge / 24))
    (hfib : FibreIndependent Mfam (fun i => conformalWeightOf (Mfam i)))
    (hrank : Module.rank ℂ
        (sqAnalyticSlashAmbient Mfam (fun i => conformalWeightOf (Mfam i)))
      ≤ (Fintype.card ι : Cardinal)) :
    ZhuModularityAnalytic
      (modularDataOf Mfam (fun i => conformalWeightOf (Mfam i))
        (traceSpanning_of_slashSpannedAtS Mfam _ (hasConformalWeight_family Mfam) hgr
          (slashSpannedAtS_of_sqRank_le Mfam _
            (sqAnalyticSlashAmbient Mfam (fun i => conformalWeightOf (Mfam i)))
            (traceIndependent_of_fibreIndependent Mfam _
              (hasConformalWeight_family Mfam) hfib)
            (sqRestrict_traceBlock_mem_sqAnalyticSlashAmbient Mfam _
              (hasConformalWeight_family Mfam) hgr)
            (sqRestrict_slash_mem_sqAnalyticSlashAmbient Mfam _) hrank))
        (traceIndependent_of_fibreIndependent Mfam _
          (hasConformalWeight_family Mfam) hfib)
        (hasConformalWeight_family Mfam)) :=
  zhu_modularity_of_sqAnalyticRank_le_of_fibreIndependent Mfam _
    (hasConformalWeight_family Mfam) hgr hfib hrank

end

end VOA
