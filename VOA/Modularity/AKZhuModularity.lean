/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.C2Corollaries
import VOA.Modularity.SqSlashBridge
import VOA.Modularity.BlockFiniteEtingof
import VOA.Modularity.BlockBoundC2
import VOA.Modularity.AKSl2Payoff

/-!
# Arakawa–Kawasetsu at the top: `ZhuModularityAnalytic` under `EtingofFinite`

`Modules.QuasiLisseFinite` proved the growth datum `OnePointSubexp` from `EtingofFinite W`
(`onePointSubexp_of_etingofFinite`), and `Modularity.BlockFiniteEtingof` audited that substitution
rung by rung against the `C₂` chain.  This file carries the substitution up to the *statement of
Zhu's theorem itself*.

## Why this is a short file, and what the dependency graph actually is

One might expect `fg_blockSpan` and `exists_finrank_analyticBlocks_le` to be
consecutive rungs of one chain.  They are not: they are **siblings**, both fed by the single
spanning datum `Modularity.C2Extraction.exists_homog_gen_of_C2Cofinite`.  Reading
`Modularity.BlockFiniteDim.exists_finrank_analyticBlocks_le` line by line, `hC2` occurs exactly
twice — once in the binder, once in `obtain … := exists_homog_gen_of_C2Cofinite W hC2` — and the
declaration never mentions `fg_blockSpan`, `blockSpanS`, `GSeries`, or anything formal-`q`-series.

More importantly, the **top** of the modularity chain never sees either sibling.
`Modularity.ConformalWeightChoice.zhu_modularity_of_sqAnalyticRank_le_irr`,
`Modularity.MinimalClosure.zhu_modularity_of_sqAnalyticRank_le_of_traceIndependent` and
`Modularity.SlashAmbientObstruction.zhu_modularity_of_sqAnalyticRank_le` take the *raw* hypothesis
`hrank : Module.rank ℂ (sqAnalyticSlashAmbient …) ≤ #ι`, which already entails
finite-dimensionality.  `C2Cofinite` enters those statements at exactly one place — the growth
datum `hgr`, supplied by `Modularity.BlockGrowth.onePointSubexp_of_c2` — and `hgr` is precisely
what `onePointSubexp_of_etingofFinite` already delivers from `EtingofFinite`.

So the Arakawa–Kawasetsu form of the modularity headline is a one-subterm substitution in
`Modularity.C2Corollaries.exists_zhuModularity_of_sqAnalyticRank_le_irr_c2`, and the `finrank`
wrappers (`finiteDimensional_sqAnalyticSlashAmbient`, `exists_finrank_analyticBlocks_le`) are not
on the path at all.

## Main results

* `exists_zhuModularity_of_sqAnalyticRank_le_irr_etingofFinite` — **the headline**:
  `ZhuModularityAnalytic` under `EtingofFinite` in place of `C2Cofinite`;
* `exists_zhuModularity_of_sqAnalyticRank_le_irr_c2_via_etingofFinite` and the `example` beneath
  it — the **subsumption check**, the verbatim `C₂` statement re-proved through the Etingof route,
  together with a kernel-level check that the two statements are *the same type*;
* `subexponentialCoeffs_of_etingofFinite`, `qSummable_gradedDim_of_etingofFinite` — the
  character `q`-series of any module over an `EtingofFinite` VOA converges on `ℍ`; with their
  subsumption checks;
* `traceBlock_S_sqRestrict_mem_analyticBlocks_of_etingofFinite` — residual **(e1)** under
  `EtingofFinite`; with its subsumption check;
* `sqAnalyticSlashAmbient_eq_map_sqRestrict` — the slash summand of the repaired ambient is
  **redundant**: given `hcw` and `hgr` the ambient *is* `Submodule.map (sqRestrict W)
  (analyticBlocks W)`.  This is `Modularity.SqSlashBridge`'s discharge of residual (e1) in
  submodule form, and it reduces `hrank` to a bound on the analytic blocks alone;
* `fibreIndependent_of_subsingleton` — `hfib` is free for a one-element family;
* `rank_map_sqRestrict_analyticBlocks_le_one_of_span_vacuum` — if `𝟙` alone spans `𝒱`
  modulo `O₂ W`, the restricted analytic blocks have rank `≤ 1`;
* `trivial_exists_zhuModularity_etingofFinite` — **the headline with every hypothesis
  discharged**, at `trivialVOA`.  Nothing above is vacuous, and in particular `hrank` is
  **satisfiable** (see the honesty block);
* `brk_mem_of_blockRelSpan`, `grading_le_span_sup_blockRelSpan_of_poisson`,
  `exists_finset_span_sup_blockRelSpan_of_etingofFinite` — §8, the one rung that is *not* a
  substitution: the analytic descent past `blockRelSpan` ported from spanning modulo `O₂ W` to
  spanning modulo `O₂P W`;
* `finiteDimensional_analyticBlocks_of_etingofFinite` — **Zhu's Theorem 5.3.2 under
  `EtingofFinite`**, with `exists_finrank_analyticBlocks_le_of_etingofFinite` and subsumption
  checks against both `C₂` originals;
* `finiteDimensional_sqAnalyticSlashAmbient_of_etingofFinite`,
  `exists_jacobiTransformation_v_zero_sq'_of_etingofFinite`,
  `char_SL2Z_invariant_of_sqAnalyticRank_of_etingofFinite` — §9, the `finrank`-form wrappers, each
  with its subsumption check.

## ⚠⚠ What is and is not claimed

**1. No non-lisse Zhu-modularity instance.**  `EtingofFinite` is discharged
unconditionally at a non-`C₂`-cofinite VOA, `L_{-4/3}(𝔰𝔩₂)` (`Sl2Pres.etingofFinite_simpleSl2QL'`,
`Examples/AffineSl2Presentation.lean`; `¬ C2Cofinite` is `Sl2NonLisse.not_C2Cofinite_simpleSl2QL`),
and `Modularity.AKSl2Instance` uses it for finite-dimensionality of the analytic blocks.  But the
modularity headline here also needs `hfib` and the rank bound `hrank`, which `EtingofFinite` does not
supply, and neither is discharged at `L_{-4/3}(𝔰𝔩₂)`.  So this file **must not** be read as
"Arakawa–Kawasetsu has a non-lisse Zhu-modularity instance".  What is gained is the
implication.

**2. The remaining hypotheses, one by one.**

* `hzero : VacuumGradeZero W` — **free for every VOA**
  (`QuasiLisseSl2.vacuumGradeZero_of_vacuum_grade`, the VOA4 axiom weakened from `=` to `≤`).
* `hcw : ∀ i, HasConformalWeight …` — **free for irreducible modules**
  (`hasConformalWeight_family`, off the unconditional
  `OrdVModule.exists_hasConformalWeight_of_irreducible`); already discharged in the `_irr` forms.
* `hgr : ∀ i, OnePointSubexp …` — **discharged by the Etingof route**; this is the whole content
  of the substitution and it was already proved in `Modules.QuasiLisseFinite`.
* `hfib : FibreIndependent …` — a genuine named hypothesis in general.  Proved conditionally by
  `Modularity.FibreIndependence.fibreIndependent_of_bottomSeparation` from `hsimp` (simplicity of
  the bottom `A(𝒱)`-modules) and `hsep` (pairwise non-isomorphy of bottoms at equal conformal
  weight), neither of which is discharged for any non-trivial VOA here.  It is free for a
  one-element family (`fibreIndependent_of_subsingleton`, below).
* `hinj : Function.Injective (tEigen W h)` — **not used here, and not satisfiable in general**:
  two non-isomorphic irreducibles may share a conformal weight
  (`Modularity.ConformalWeightChoice`, module docstring).  The `_irr` route uses `hfib` instead.
* `hwt : SqModeWeighted W` — **free for every VOA** (`Modularity.SqModeWeight.sqModeWeighted_holds`
  is unconditional).  Not needed on the analytic ambient anyway.
* `hrank : Module.rank ℂ (sqAnalyticSlashAmbient …) ≤ #ι` — **the one that matters.**
  - It is **not vacuous**: `trivial_sqAnalyticRank_le` below discharges it at `trivialVOA` with
    `ι = Fin 1`.  That is genuine satisfiability, and it is what makes the headline non-vacuous.

    ⚠ **But it does *not* sharply distinguish this hypothesis from the refuted pointwise-slash
    one.**
    The pointwise-slash hypothesis on
    `analyticSlashAmbient` is refuted by `Modularity.SlashAmbientObstruction`'s
    `not_rank_analyticSlashAmbient_le` — which is why
    `Modularity.BlockFiniteDim.zhu_modularity_of_analytic_finrank_le` is marked **DO NOT USE** —
    but `not_rank_analyticSlashAmbient_le`'s own hypotheses are *themselves* unsatisfiable at
    `trivialVOA`, since `sqWeightSpace trivialVOA n = ⊥` for every `n ≠ 0`.  So the single witness
    used here cannot separate the two: it shows this hypothesis is satisfiable **somewhere**, not
    that it avoids the pointwise-slash failure mode **in general**.  Separating them needs a witness
    at a
    VOA with non-trivial `sqWeightSpace`, which this repository does not have.
  - It is **not discharged for any non-trivial VOA**.  The two routes that could discharge it —
    rational Zhu Thm 5.3.3 (`Modularity.SqAmbientRank.rank_map_sqRestrict_analyticBlocks_le` via
    `Modularity.ZhuBlockCount`) and Arike–Nagatomo (`Modularity.BlockBoundC2`) — both pass through
    `Modularity.ZhuAlgebraFinite.finiteDimensional_A_of_C2Cofinite` **and**
    `Modularity.BlockRelSpanE.moduleFinite_quot_blockRelSpanE`, two `C2Cofinite` entry points that
    are *independent* of `fg_blockSpan`.
  - **`EtingofFinite` cannot discharge it.**  `EtingofFinite W` is finiteness of `𝒱 ⧸ O₂P W`
    (`Modules.QuasiLisseFinite.etingofFinite_iff_quot_O₂P`), which does **not** bound
    `A(𝒱) = 𝒱 ⧸ O(𝒱)`, because `a₍₀₎b ∉ O(𝒱)` in general.  So `hrank` stays a hypothesis on this
    route, and that is a real limitation, not a presentational one.

**3. No new analysis, no MLDE.**  Nothing here proves a modular linear differential equation.
Arakawa–Kawasetsu Lemma 5.5 is already proved elsewhere (`Modularity.AKModularODE`,
`huni_of_sqPrimary` + `vacuum_isSqPrimary`); this file consumes only the growth interface.

## Status
Proved, `sorry`-free, axiom-clean (`propext` / `Classical.choice` / `Quot.sound` only); the
theorem `VOA.pbw` is **not** used by any declaration in this
file.  All thirty declarations are enforced by `scripts/audit/AKZhuModularityAxiomAudit.lean`,
registered in `scripts/audit/run_axiom_audits.py`.
-/

namespace VOA

open scoped BigOperators MatrixGroups
open VHat VHat.DLM3 Module

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

/-! ## §1  The headline: Zhu modularity under `EtingofFinite` -/

section Headline

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (Mfam : ι → IrrModule W)

/-- **Arakawa–Kawasetsu at the top.**  `Modularity.C2Corollaries.
exists_zhuModularity_of_sqAnalyticRank_le_irr_c2` with `C2Cofinite W` weakened to
`EtingofFinite W`.

Every hypothesis except `hfib` and `hrank` is discharged: `hcw` by
`hasConformalWeight_family`, and the growth datum `hgr` by
`Modules.QuasiLisseFinite.onePointSubexp_of_etingofFinite` — which is the entire Arakawa–Kawasetsu
substitution, and the *only* place `C2Cofinite` entered the statement being generalised.

⚠ This is an **implication**, not a new example: the only VOA at which `EtingofFinite` is
discharged unconditionally in this repository is `trivialVOA`, which is `C₂`-cofinite.  See the
module docstring.  ⚠ `hrank` is satisfiable (`trivial_sqAnalyticRank_le`) but is discharged for no
non-trivial VOA, and `EtingofFinite` provably cannot discharge it.

No `VacuumGradeZero` hypothesis: it holds for every VOA (`vacuumGradeZero_holds`). -/
theorem exists_zhuModularity_of_sqAnalyticRank_le_irr_etingofFinite
    (hE : EtingofFinite W)
    (hfib : FibreIndependent Mfam (fun i => conformalWeightOf (Mfam i)))
    (hrank : Module.rank ℂ
        (sqAnalyticSlashAmbient Mfam (fun i => conformalWeightOf (Mfam i)))
      ≤ (Fintype.card ι : Cardinal)) :
    ∃ D : ModularData W ι, ZhuModularityAnalytic D :=
  ⟨_, zhu_modularity_of_sqAnalyticRank_le_irr Mfam
    (fun i => onePointSubexp_of_etingofFinite W (Mfam i).isMod
      (hasConformalWeight_family Mfam i) (vacuumGradeZero_holds W) hE)
    hfib hrank⟩

/-- **Subsumption check for the headline.**  The *verbatim statement* of
`Modularity.C2Corollaries.exists_zhuModularity_of_sqAnalyticRank_le_irr_c2`, re-proved through the
Etingof route.  A theorem `P → Q` proved from `P → R` and `R → Q` cannot be a sideways restatement
of `P → Q`, so the existence of this proof is the assertion that the substitution *generalises*
rather than sidesteps.

No `VacuumGradeZero` hypothesis: it holds for every VOA (`vacuumGradeZero_holds`). -/
theorem exists_zhuModularity_of_sqAnalyticRank_le_irr_c2_via_etingofFinite
    (hC2 : C2Cofinite W)
    (hfib : FibreIndependent Mfam (fun i => conformalWeightOf (Mfam i)))
    (hrank : Module.rank ℂ
        (sqAnalyticSlashAmbient Mfam (fun i => conformalWeightOf (Mfam i)))
      ≤ (Fintype.card ι : Cardinal)) :
    ∃ D : ModularData W ι, ZhuModularityAnalytic D :=
  exists_zhuModularity_of_sqAnalyticRank_le_irr_etingofFinite Mfam
    (EtingofFinite_of_C2Cofinite W hC2) hfib hrank

end Headline

/-- **Statement identity, checked in the kernel.**  The subsumption theorem and the original `C₂`
theorem have the *same type*, character for character: this `example` would fail to elaborate if
any binder, implicit argument or universe differed.  (`rfl` closes it by definitional proof
irrelevance, which is available precisely because both sides are proofs of one `Prop`.) -/
example : @exists_zhuModularity_of_sqAnalyticRank_le_irr_c2
    = @exists_zhuModularity_of_sqAnalyticRank_le_irr_c2_via_etingofFinite := rfl

/-! ### ⚠ What the subsumption check does *not* say

There is no Lean check that the Etingof form is strictly stronger, and there cannot be one here:
that would require a VOA with `EtingofFinite` and `¬ C2Cofinite`, which is exactly the witness this
repository does not have.  The one-directional facts that *are* available are
`Modules.PoissonTrace.EtingofFinite_of_C2Cofinite` and, at the spanning level,
`Modules.QuasiLisseFinite.span_sup_O₂P_eq_top_of_span_sup_O₂` — each with no converse proved.
-/

/-! ## §2  Character corollaries under `EtingofFinite`

`Modularity.C2Corollaries.subexponentialCoeffs_of_c2` and `qSummable_gradedDim_of_c2` use
`C2Cofinite` only through `onePointSubexp_of_c2`.  Same substitution, same one subterm.
-/

section Character

variable {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- **The character growth datum from `EtingofFinite`.**  `SubexponentialCoeffs` is the
`v = 𝟙` case of `OnePointSubexp`. -/
theorem subexponentialCoeffs_of_etingofFinite (N : OrdVModule W M) {hw : ℂ}
    (hcw : HasConformalWeight N hw) (hzero : VacuumGradeZero W) (hE : EtingofFinite W) :
    SubexponentialCoeffs N (hw - W.centralCharge / 24) := by
  have h := onePointSubexp_of_etingofFinite W N hcw hzero hE W.vacuum
  rwa [show (fun n : ℕ => ‖torusOnePoint N W.vacuum (hw - W.centralCharge / 24 + (n : ℂ))‖)
    = (fun n : ℕ => ‖gradedDim N (hw - W.centralCharge / 24 + (n : ℂ))‖) from by
      funext n; rw [torusOnePoint_vacuum]; rfl] at h

/-- **The character `q`-series converges on `ℍ` from `EtingofFinite` alone.** -/
theorem qSummable_gradedDim_of_etingofFinite (N : OrdVModule W M) {hw : ℂ}
    (hcw : HasConformalWeight N hw) (hzero : VacuumGradeZero W) (hE : EtingofFinite W)
    (τ : UpperHalfPlane) :
    QSummableAt (gradedDim N) (hw - W.centralCharge / 24) τ :=
  qSummable_gradedDim N _ (subexponentialCoeffs_of_etingofFinite N hcw hzero hE) τ

/-- **Subsumption check.**  The verbatim statement of
`Modularity.C2Corollaries.subexponentialCoeffs_of_c2`, through the Etingof route. -/
theorem subexponentialCoeffs_of_c2_via_etingofFinite (N : OrdVModule W M) {hw : ℂ}
    (hcw : HasConformalWeight N hw) (hzero : VacuumGradeZero W) (hC2 : C2Cofinite W) :
    SubexponentialCoeffs N (hw - W.centralCharge / 24) :=
  subexponentialCoeffs_of_etingofFinite N hcw hzero (EtingofFinite_of_C2Cofinite W hC2)

/-- **Subsumption check.**  The verbatim statement of
`Modularity.C2Corollaries.qSummable_gradedDim_of_c2`, through the Etingof route. -/
theorem qSummable_gradedDim_of_c2_via_etingofFinite (N : OrdVModule W M) {hw : ℂ}
    (hcw : HasConformalWeight N hw) (hzero : VacuumGradeZero W) (hC2 : C2Cofinite W)
    (τ : UpperHalfPlane) :
    QSummableAt (gradedDim N) (hw - W.centralCharge / 24) τ :=
  qSummable_gradedDim_of_etingofFinite N hcw hzero (EtingofFinite_of_C2Cofinite W hC2) τ

end Character

example : @subexponentialCoeffs_of_c2 = @subexponentialCoeffs_of_c2_via_etingofFinite := rfl

example : @qSummable_gradedDim_of_c2 = @qSummable_gradedDim_of_c2_via_etingofFinite := rfl

/-! ## §3  Residual (e1) under `EtingofFinite`

`Modularity.SqSlashBridge.traceBlock_S_sqRestrict_mem_analyticBlocks` spends `hC2` on exactly one
subterm, `onePointSubexp_of_c2`.
-/

section SlashBridge

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (Mfam : ι → IrrModule W) (h : ι → ℂ)

/-- **Residual (e1) from `EtingofFinite`**: the `S`-slash of every trace block, restricted to
`L[0]`-homogeneous vectors, is represented by an honest analytic block. -/
theorem traceBlock_S_sqRestrict_mem_analyticBlocks_of_etingofFinite
    (hcw : ∀ i, HasConformalWeight (Mfam i).isMod (h i))
    (hzero : VacuumGradeZero W) (hE : EtingofFinite W) (i : ι) :
    sqRestrict W (blockSlash W ModularGroup.S (traceBlock Mfam h i)) ∈
      Submodule.map (sqRestrict W) (analyticBlocks W) := by
  apply sqRestrict_blockSlash_mem_analyticBlocks
  exact traceBlock_isAnalyticBlock Mfam h hcw
    (fun j ↦ onePointSubexp_of_etingofFinite W (Mfam j).isMod (hcw j) hzero hE) i

/-- **Subsumption check.**  The verbatim statement of
`Modularity.SqSlashBridge.traceBlock_S_sqRestrict_mem_analyticBlocks`, through the Etingof
route. -/
theorem traceBlock_S_sqRestrict_mem_analyticBlocks_c2_via_etingofFinite
    (hcw : ∀ i, HasConformalWeight (Mfam i).isMod (h i))
    (hzero : VacuumGradeZero W) (hC2 : C2Cofinite W) (i : ι) :
    sqRestrict W (blockSlash W ModularGroup.S (traceBlock Mfam h i)) ∈
      Submodule.map (sqRestrict W) (analyticBlocks W) :=
  traceBlock_S_sqRestrict_mem_analyticBlocks_of_etingofFinite Mfam h hcw hzero
    (EtingofFinite_of_C2Cofinite W hC2) i

end SlashBridge

example : @traceBlock_S_sqRestrict_mem_analyticBlocks
    = @traceBlock_S_sqRestrict_mem_analyticBlocks_c2_via_etingofFinite := rfl

/-! ## §4  The slash summand of the repaired ambient is redundant

`Modularity.SlashAmbientObstruction.sqAnalyticSlashAmbient` is
`map (sqRestrict W) (analyticBlocks W) ⊔ span {S-slashes}`.  Residual (e1) says the second summand
sits inside the first, so — given only `hcw` and `hgr`, both of which the Etingof route supplies —
the sup collapses.  This is *unconditional in `C₂`* and reduces `hrank` to a bound on the analytic
blocks alone.
-/

section Redundant

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (Mfam : ι → IrrModule W) (h : ι → ℂ)

/-- **The repaired analytic ambient has no slash summand.**  Given the conformal weights and
the growth datum, `sqAnalyticSlashAmbient Mfam h` *equals* the restricted analytic blocks. -/
theorem sqAnalyticSlashAmbient_eq_map_sqRestrict
    (hcw : ∀ i, HasConformalWeight (Mfam i).isMod (h i))
    (hgr : ∀ i, OnePointSubexp (Mfam i).isMod (h i - W.centralCharge / 24)) :
    sqAnalyticSlashAmbient Mfam h = Submodule.map (sqRestrict W) (analyticBlocks W) := by
  change Submodule.map (sqRestrict W) (analyticBlocks W)
      ⊔ Submodule.span ℂ (Set.range fun i : ι =>
          sqRestrict W (blockSlash W ModularGroup.S (traceBlock Mfam h i)))
      = Submodule.map (sqRestrict W) (analyticBlocks W)
  refine sup_eq_left.mpr ?_
  rw [Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact sqRestrict_blockSlash_mem_analyticBlocks
    (traceBlock_isAnalyticBlock Mfam h hcw hgr i) ModularGroup.S

end Redundant

/-! ## §5  `hfib` is free for a one-element family -/

section Subsingleton

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Subsingleton ι]

/-- **Fibre independence for a one-element (or empty) family.**  With at most one module the
fibre sums have a single term, and the character is nonzero on the imaginary axis
(`Modularity.RhoS.traceFun_vacuum_ne_zero`, itself free from the growth datum). -/
theorem fibreIndependent_of_subsingleton (Mfam : ι → IrrModule W) (h : ι → ℂ)
    (hcw : ∀ i, HasConformalWeight (Mfam i).isMod (h i))
    (hgr : ∀ i, OnePointSubexp (Mfam i).isMod (h i - W.centralCharge / 24)) :
    FibreIndependent Mfam h := by
  classical
  intro i c hc j hj
  obtain ⟨τ, hτ⟩ := traceFun_vacuum_ne_zero Mfam h hcw hgr j
  have hfil : (Finset.univ.filter (fun k => tEigen W h k = tEigen W h i)) = {j} := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro _; exact Subsingleton.elim k j
    · intro _; rw [Subsingleton.elim k i]
  have hsum := hc 0 W.vacuum (vacuum_mem_sqWeightSpace_zero W) τ
  rw [hfil, Finset.sum_singleton] at hsum
  exact (mul_eq_zero.mp hsum).resolve_right hτ

end Subsingleton

/-! ## §6  `hrank` is satisfiable

The rank hypothesis of the headline is *not* the refuted pointwise-slash one.  Below it is
discharged, with
no hypotheses at all, at `trivialVOA`.  This settles the one honesty question the file's precedent
(`Modularity.BlockFiniteDim.zhu_modularity_of_analytic_finrank_le`, whose hypothesis is
**refuted**) makes urgent.
-/

section Rank

/-- The vacuum as an `L[0]`-homogeneous point of `𝒱`. -/
noncomputable def vacuumSqPt (W : VertexOperatorAlgebra 𝒱) : SqPt W :=
  ⟨0, ⟨W.vacuum, by simpa using vacuum_mem_sqWeightSpace_zero W⟩⟩

/-- Evaluation of a function on homogeneous points at a fixed point and a fixed `z`. -/
def sqPtEvalAt (W : VertexOperatorAlgebra 𝒱) (p : SqPt W) (z : ℂ) :
    (SqPt W → ℂ → ℂ) →ₗ[ℂ] ℂ where
  toFun f := f p z
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- **If `𝟙` alone spans `𝒱` modulo `O₂ W`, the restricted analytic blocks have rank `≤ 1`.**

The evaluation `F ↦ F(𝟙)(i)` is injective on `map (sqRestrict W) (analyticBlocks W)`: block
condition (ii) propagates vanishing at one point of `ℍ` across all of `𝒱`
(`IsAnalyticBlock.eq_zero_of_vanish_at`), and `sqRestrict` is supported on `ℍ`. -/
theorem rank_map_sqRestrict_analyticBlocks_le_one_of_span_vacuum
    (htop : (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ ({W.vacuum} : Set 𝒱) ⊔ O₂ W) :
    Module.rank ℂ (Submodule.map (sqRestrict W) (analyticBlocks W)) ≤ 1 := by
  classical
  set 𝔄 : Submodule ℂ (SqPt W → ℂ → ℂ) :=
    Submodule.map (sqRestrict W) (analyticBlocks W) with h𝔄
  have hz₀ : (Complex.I : ℂ) ∈ imGT 0 := by
    change (0 : ℝ) < Complex.I.im
    simp
  have hShom : ∀ s ∈ ({W.vacuum} : Set 𝒱), IsHomog W s := by
    intro s hs
    rw [Set.mem_singleton_iff] at hs
    exact ⟨0, hs ▸ W.vacuum_mem_grading_zero⟩
  have hinj : Function.Injective
      ((sqPtEvalAt W (vacuumSqPt W) Complex.I).domRestrict 𝔄) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    rintro ⟨f, hf⟩ hker
    have hker' : (sqPtEvalAt W (vacuumSqPt W) Complex.I).domRestrict 𝔄 ⟨f, hf⟩ = 0 := hker
    obtain ⟨F, hFmem, hFeq⟩ := hf
    have hvan : ∀ x ∈ ({W.vacuum} : Set 𝒱), F x Complex.I = 0 := by
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      have h1 : f (vacuumSqPt W) Complex.I = 0 := hker'
      rw [← hFeq, sqRestrict_apply W F (vacuumSqPt W) hz₀] at h1
      exact h1
    have hall := (hFmem : IsAnalyticBlock W F).eq_zero_of_vanish_at hz₀ _ hShom htop hvan
    refine Subtype.ext ?_
    change f = 0
    rw [← hFeq]
    funext p z
    by_cases hz : z ∈ imGT 0
    · rw [sqRestrict_apply W F p hz, hall (p.2 : 𝒱) z hz]; rfl
    · change Set.indicator (imGT 0) (F (p.2 : 𝒱)) z = _
      rw [Set.indicator_of_notMem hz]; rfl
  haveI : FiniteDimensional ℂ 𝔄 :=
    FiniteDimensional.of_injective ((sqPtEvalAt W (vacuumSqPt W) Complex.I).domRestrict 𝔄) hinj
  have hle := LinearMap.finrank_le_finrank_of_injective
    (f := (sqPtEvalAt W (vacuumSqPt W) Complex.I).domRestrict 𝔄) hinj
  rw [Module.finrank_self] at hle
  rw [← Module.finrank_eq_rank]
  exact_mod_cast hle

end Rank

/-! ## §7  Non-vacuity: the headline with every hypothesis discharged

⚠ As stated at the top: `trivialVOA` is `C₂`-cofinite, so this is *not* a new mathematical
example.  Its job is to certify that no statement in this file is vacuous — in particular that
`hrank`, the hypothesis whose pointwise-slash analogue is *refuted*, is satisfiable.
-/

section Trivial

/-- The one-element family of irreducible `trivialVOA`-modules. -/
noncomputable def trivialFam : Fin 1 → IrrModule trivialVOA := fun _ => trivialAdjointIrr

/-- `𝟙` spans the trivial VOA modulo `O₂`. -/
theorem trivial_top_eq_span_vacuum_sup_O₂ :
    (⊤ : Submodule ℂ (LatGen.LatModuleGen (stdLattice 0)))
      = Submodule.span ℂ ({trivialVOA.vacuum} : Set (LatGen.LatModuleGen (stdLattice 0)))
        ⊔ O₂ trivialVOA := by
  rw [trivial_span_vacuum, top_sup_eq]

/-- The growth datum for the trivial family, obtained through the Arakawa–Kawasetsu route. -/
theorem trivial_onePointSubexp_fam (i : Fin 1) :
    OnePointSubexp (trivialFam i).isMod
      (conformalWeightOf (trivialFam i) - trivialVOA.centralCharge / 24) :=
  onePointSubexp_of_etingofFinite trivialVOA (trivialFam i).isMod
    (hasConformalWeight_family trivialFam i) trivial_vacuumGradeZero trivial_etingofFinite

/-- **`hrank` is satisfiable.**  The rank hypothesis of the headline holds, with no
hypotheses, at `trivialVOA` with a one-element family.  Contrast
`Modularity.SlashAmbientObstruction.not_rank_analyticSlashAmbient_le`, which *refutes* the
corresponding hypothesis on the unrepaired ambient. -/
theorem trivial_sqAnalyticRank_le :
    Module.rank ℂ (sqAnalyticSlashAmbient trivialFam
        (fun i => conformalWeightOf (trivialFam i)))
      ≤ (Fintype.card (Fin 1) : Cardinal) := by
  rw [sqAnalyticSlashAmbient_eq_map_sqRestrict trivialFam _
    (hasConformalWeight_family trivialFam) trivial_onePointSubexp_fam]
  simpa using rank_map_sqRestrict_analyticBlocks_le_one_of_span_vacuum
    (W := trivialVOA) trivial_top_eq_span_vacuum_sup_O₂

/-- **The Arakawa–Kawasetsu headline, instantiated with every hypothesis discharged.**
`hzero`, `hE`, `hfib` and `hrank` are all proved, not assumed — so
`exists_zhuModularity_of_sqAnalyticRank_le_irr_etingofFinite` is not vacuous.

⚠ `trivialVOA` is `C₂`-cofinite (`Examples.ZhuInstantiation.trivial_C2Cofinite`), so this is a
non-vacuity certificate, **not** a new instance of Arakawa–Kawasetsu.  It does, however, reach the
modularity conclusion without `Finite (Φ trivialVOA)`, without the classification input
`Nat.card (Φ trivialVOA) = 1`, and without the theorem `VOA.pbw`
— all three of which `Examples.ZhuInstantiation.trivialVOA_zhuModularity` needs. -/
theorem trivial_exists_zhuModularity_etingofFinite :
    ∃ D : ModularData trivialVOA (Fin 1), ZhuModularityAnalytic D :=
  exists_zhuModularity_of_sqAnalyticRank_le_irr_etingofFinite trivialFam
    trivial_etingofFinite
    (fibreIndependent_of_subsingleton trivialFam _
      (hasConformalWeight_family trivialFam) trivial_onePointSubexp_fam)
    trivial_sqAnalyticRank_le

/-- The character corollary, instantiated: the trivial VOA's character `q`-series converges on
`ℍ`, obtained through the Arakawa–Kawasetsu route. -/
theorem trivial_qSummable_gradedDim_adjoint (τ : UpperHalfPlane) :
    QSummableAt (gradedDim (adjointModule trivialVOA))
      (0 - trivialVOA.centralCharge / 24) τ :=
  qSummable_gradedDim_of_etingofFinite (adjointModule trivialVOA)
    (adjoint_hasConformalWeight trivialVOA trivialVacuum_ne_zero)
    trivial_vacuumGradeZero trivial_etingofFinite τ


end Trivial

/-! ## §8  The genuinely new rung: **Zhu's Theorem 5.3.2 under `EtingofFinite`**

Everything above was a substitution of one already-proved subterm.  This section is real work: it
ports the *analytic* descent past `blockRelSpan` from spanning modulo `O₂ W` to spanning modulo the
larger `O₂P W = O₂ W + {𝒱, 𝒱}`, which is what
`Modules.QuasiLisseFinite.exists_homog_gen_of_etingofFinite` delivers.

The gate is a single extra generator branch.  `Modules.QuasiLisseFinite.O₂P_inf_grading_le_span_deg`
produces **two** homogeneous generating families in each degree — the `a₍₋₂₎b` of `O₂homGenDeg` and
the Poisson brackets `a₍₀₎b` of `PhomGenDeg` — where the `C₂` version produced only the first.  The
first branch is `Modularity.BlockRelSpanning`'s existing argument; the second,
`brk_mem_of_blockRelSpan`, is the exact analytic analogue of
`Modules.QuasiLisseFinite.brk_mem_pullbackG`, and it closes
because `blockRelSpan`'s *first* generating family is literally `{vSqZ W a ka 0 v}` — block
condition (i) — so the `a[0]`-relation is exact and only the strictly-lower-degree defect
`sqDefect0` has to be absorbed.

⚠ This rung is **not** on the path to `ZhuModularityAnalytic` (see §1): it feeds only the
`finrank`-form wrappers of §9.  It does, however, bypass both `C2Cofinite` entry points that are
*independent* of `fg_blockSpan` — `Modularity.ZhuAlgebraFinite.finiteDimensional_A_of_C2Cofinite`
and `Modularity.BlockRelSpanE.moduleFinite_quot_blockRelSpanE` — which the `C₂` route
(`Modularity.BlockBoundC2`) needs and which `EtingofFinite` cannot supply.
-/

section BlockFinite

variable (W)

/-- The `[−2]`-generator descends past `blockRelSpan`.  This is the generator branch already
inlined in `Modularity.BlockRelSpanning.grading_le_span_sup_blockRelSpan`, factored out so that the
`O₂P` induction below can reuse it verbatim. -/
theorem negTwo_mem_of_blockRelSpan (hzero : VacuumGradeZero W) (z : ℂ) {p q n : ℤ} {a b : 𝒱}
    (ha : a ∈ W.grading p) (hb : b ∈ W.grading q) (hpq : p + q + 1 = n)
    (T : Submodule ℂ 𝒱) (hT : ∀ m : ℤ, m < n → W.grading m ≤ T)
    (hrel : blockRelSpan W z ≤ T) :
    W.smul a (-2) b ∈ T := by
  by_cases hg0 : W.smul a (-2) b = 0
  · rw [hg0]; exact Submodule.zero_mem _
  have hp0 : 0 ≤ p := by
    by_contra hc
    exact hg0 (by rw [show a = 0 by
      rw [W.positivity p (not_le.mp hc), Submodule.mem_bot] at ha; exact ha, W.smul_zero_left])
  have hexp := vSqZ_neg_two_eq W a p.toNat b
  have hstep : W.smul a (-2) b = vSqZ W a p.toNat (-2) b - sqDefect W a p.toNat b := by
    rw [hexp, add_sub_cancel_right]
    rfl
  rw [hstep]
  refine Submodule.sub_mem _ ?_ (sqDefect_mem_of_lower W ha hb hpq hp0 T hT)
  rcases eq_or_lt_of_le hp0 with hp | hp1
  · have ha0 : a ∈ W.grading 0 := by rw [hp]; exact ha
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp (hzero ha0)
    have hp0' : p.toNat = 0 := by omega
    rw [hp0']
    have hlin : vSqZ W (c • W.vacuum) 0 (-2) b = c • vSqZ W W.vacuum 0 (-2) b := by
      rw [vSqZ_apply, vSqZ_apply,
        smul_finsum' c (sqModeZ_support_finite W W.vacuum 0 (-2) b)]
      refine finsum_congr (fun i => ?_)
      change sqBracketCoeffZ 0 (-2) i • W.smul (c • W.vacuum) i b
        = c • (sqBracketCoeffZ 0 (-2) i • W.smul W.vacuum i b)
      rw [PreVertexAlgebra.smul_smul_left, smul_comm]
    rw [hlin, vSqZ_vacuum_scalar, smul_smul]
    exact Submodule.smul_mem _ _ (hT q (by omega) hb)
  · exact vSqZ_negTwo_mem_of_blockRelSpan W z ha hb hp1 hpq T hT hrel

/-- **The bracket generator descends past `blockRelSpan`** — the new step.

For homogeneous `a ∈ 𝒱ₚ`, `b ∈ 𝒱_q` with `p + q − 1 = n`, the Poisson representative `a₍₀₎b` lies
in `T` as soon as every strictly lower degree does.  The argument is *easier* than the `[−2]` one:
block condition (i) makes the `a[0]`-relation exact — there is no Eisenstein tail — so only the
strictly-lower-degree defect `sqDefect0` has to be absorbed.  Exact analytic analogue of
`Modules.QuasiLisseFinite.brk_mem_pullbackG`. -/
theorem brk_mem_of_blockRelSpan (hzero : VacuumGradeZero W) (z : ℂ) {p q n : ℤ} {a b : 𝒱}
    (ha : a ∈ W.grading p) (hb : b ∈ W.grading q) (hpq : p + q - 1 = n)
    (T : Submodule ℂ 𝒱) (hT : ∀ m : ℤ, m < n → W.grading m ≤ T)
    (hrel : blockRelSpan W z ≤ T) :
    W.smul a 0 b ∈ T := by
  rcases lt_or_ge p 0 with hp | hp0
  · have ha0 : a = 0 := by
      rw [W.positivity p hp, Submodule.mem_bot] at ha; exact ha
    rw [ha0, W.smul_zero_left]
    exact Submodule.zero_mem _
  rcases eq_or_lt_of_le hp0 with hp | hp1
  · -- `p = 0`: `a = c·𝟙` and `𝟙₍₀₎b = 0`.
    have ha0 : a ∈ W.grading 0 := by rw [hp]; exact ha
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp (hzero ha0)
    rw [PreVertexAlgebra.smul_smul_left, W.smul_vacuum_left, if_neg (by norm_num), smul_zero]
    exact Submodule.zero_mem _
  · -- `p ≥ 1`: the exact `a[0]`-relation, minus a strictly lower-degree defect.
    have hka : 1 ≤ p.toNat := by omega
    have ha' : a ∈ W.grading ((p.toNat : ℕ) : ℤ) := by
      rwa [show ((p.toNat : ℕ) : ℤ) = p from by omega]
    have hrelmem : vSqZ W a p.toNat 0 b ∈ T :=
      hrel (Submodule.subset_span (Or.inl ⟨p.toNat, a, b, hka, ha', rfl⟩))
    have hdef : sqDefect0 W a p.toNat b ∈ T :=
      sqDefect0_mem_of_lower W ha hb hpq T hT
    have hstep : W.smul a 0 b = vSqZ W a p.toNat 0 b - sqDefect0 W a p.toNat b := by
      rw [vSqZ_zero_eq W a p.toNat b, add_sub_cancel_right]
      rfl
    rw [hstep]
    exact Submodule.sub_mem _ hrelmem hdef

/-- **The degree induction, modulo `O₂P`.**  Verbatim
`Modularity.BlockRelSpanning.grading_le_span_sup_blockRelSpan` except that the spanning hypothesis
is modulo `O₂P W = O₂ W + {𝒱,𝒱}` rather than modulo `O₂ W`, and the induction therefore has the
second generator branch `brk_mem_of_blockRelSpan`. -/
theorem grading_le_span_sup_blockRelSpan_of_poisson (hzero : VacuumGradeZero W) (S : Set 𝒱)
    (hShom : ∀ s ∈ S, IsHomog W s)
    (htop : (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ S ⊔ O₂P W) (z : ℂ) (n : ℤ) :
    W.grading n ≤ Submodule.span ℂ S ⊔ blockRelSpan W z := by
  classical
  set T : Submodule ℂ 𝒱 := Submodule.span ℂ S ⊔ blockRelSpan W z with hTdef
  have hrel : blockRelSpan W z ≤ T := le_sup_right
  rcases lt_or_ge n 0 with hneg | hnn
  · rw [W.positivity n hneg]; exact bot_le
  obtain ⟨N, rfl⟩ : ∃ N : ℕ, n = (N : ℤ) := ⟨n.toNat, by omega⟩
  induction N using Nat.strong_induction_on with
  | _ N ihN =>
    have hT : ∀ m : ℤ, m < (N : ℤ) → W.grading m ≤ T := by
      intro m hm
      rcases lt_or_ge m 0 with hm0 | hm0
      · rw [W.positivity m hm0]; exact bot_le
      · obtain ⟨M, rfl⟩ : ∃ M : ℕ, m = (M : ℤ) := ⟨m.toNat, by omega⟩
        exact ihN M (by exact_mod_cast hm) (by exact_mod_cast hm0)
    refine le_trans (grading_le_span_sup_O₂P_inf W S hShom htop (N : ℤ)) ?_
    refine sup_le le_sup_left ?_
    refine le_trans (O₂P_inf_grading_le_span_deg W (N : ℤ)) ?_
    rw [Submodule.span_le]
    rintro g (⟨p, q, a, b, ha, hb, hpq, rfl⟩ | ⟨p, q, a, b, ha, hb, hpq, rfl⟩)
    · exact negTwo_mem_of_blockRelSpan W hzero z ha hb hpq T hT hrel
    · exact brk_mem_of_blockRelSpan W hzero z ha hb hpq T hT hrel

/-- **The span form of Zhu's descent, modulo `O₂P`**, for every `z`. -/
theorem span_sup_blockRelSpan_eq_top_of_poisson (hzero : VacuumGradeZero W) (S : Set 𝒱)
    (hShom : ∀ s ∈ S, IsHomog W s)
    (htop : (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ S ⊔ O₂P W) (z : ℂ) :
    (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ S ⊔ blockRelSpan W z := by
  refine le_antisymm ?_ le_top
  rw [← span_homog_eq_top W, Submodule.span_le]
  rintro x ⟨m, hx⟩
  exact grading_le_span_sup_blockRelSpan_of_poisson W hzero S hShom htop z m hx

/-- `Finset` form: `EtingofFinite` gives finitely many vectors spanning `𝒱` modulo the
deformed relations, at **every** `z`.  Etingof twin of
`Modularity.BlockRelSpanning.exists_finset_span_sup_blockRelSpan`. -/
theorem exists_finset_span_sup_blockRelSpan_of_etingofFinite (hzero : VacuumGradeZero W)
    (hE : EtingofFinite W) (z : ℂ) :
    ∃ T : Finset 𝒱, (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ (T : Set 𝒱) ⊔ blockRelSpan W z := by
  classical
  obtain ⟨g, gen, wt, hwt, hgen, hdec⟩ := exists_homog_gen_of_etingofFinite W hE
  refine ⟨(Finset.univ.image gen) ∪ {W.vacuum}, ?_⟩
  have hset : (((Finset.univ.image gen) ∪ {W.vacuum} : Finset 𝒱) : Set 𝒱)
      = Set.range gen ∪ {W.vacuum} := by
    ext x
    simp [Set.mem_range]
  rw [hset]
  refine span_sup_blockRelSpan_eq_top_of_poisson W hzero _ ?_ hdec z
  rintro s (⟨i, rfl⟩ | hs)
  · exact ⟨(wt i : ℤ), hgen i⟩
  · rw [Set.mem_singleton_iff] at hs
    exact ⟨0, hs ▸ W.vacuum_mem_grading_zero⟩

/-- **ZHU'S THEOREM 5.3.2 UNDER `EtingofFinite`.**  The space of genus-one conformal blocks
is finite-dimensional for every VOA satisfying the Arakawa–Kawasetsu finiteness hypothesis.

Etingof twin of `Modularity.BlockBoundC2.finiteDimensional_analyticBlocks_of_C2Cofinite`, and it
reaches the conclusion **without** `finiteDimensional_A_of_C2Cofinite` and **without**
`moduleFinite_quot_blockRelSpanE` — the two `C2Cofinite` entry points that the `C₂` route needs and
that `EtingofFinite` cannot supply. -/
theorem finiteDimensional_analyticBlocks_of_etingofFinite (hzero : VacuumGradeZero W)
    (hE : EtingofFinite W) :
    FiniteDimensional ℂ (Submodule.map restrictImGT (analyticBlocks W)) := by
  have hI : (Complex.I : ℂ) ∈ imGT 0 := by
    change (0 : ℝ) < Complex.I.im
    simp
  obtain ⟨T, hT⟩ := exists_finset_span_sup_blockRelSpan_of_etingofFinite W hzero hE Complex.I
  exact (finrank_analyticBlocks_le_card_of_blockRel hI T hT).1

/-- The bounded form: Etingof twin of
`Modularity.BlockFiniteDim.exists_finrank_analyticBlocks_le`. -/
theorem exists_finrank_analyticBlocks_le_of_etingofFinite (hzero : VacuumGradeZero W)
    (hE : EtingofFinite W) {z₀ : ℂ} (hz₀ : z₀ ∈ imGT 0) :
    ∃ g : ℕ, FiniteDimensional ℂ (Submodule.map restrictImGT (analyticBlocks W)) ∧
      Module.finrank ℂ (Submodule.map restrictImGT (analyticBlocks W)) ≤ g + 1 := by
  obtain ⟨T, hT⟩ := exists_finset_span_sup_blockRelSpan_of_etingofFinite W hzero hE z₀
  obtain ⟨hfd, hle⟩ := finrank_analyticBlocks_le_card_of_blockRel hz₀ T hT
  exact ⟨T.card, hfd, le_trans hle (Nat.le_succ _)⟩

/-- **Subsumption check.**  The verbatim statement of
`Modularity.BlockBoundC2.finiteDimensional_analyticBlocks_of_C2Cofinite`, re-proved through the
Etingof route. -/
theorem finiteDimensional_analyticBlocks_of_C2Cofinite_via_etingofFinite
    (hzero : VacuumGradeZero W) (hC2 : C2Cofinite W) :
    FiniteDimensional ℂ (Submodule.map restrictImGT (analyticBlocks W)) :=
  finiteDimensional_analyticBlocks_of_etingofFinite W hzero (EtingofFinite_of_C2Cofinite W hC2)

/-- **Subsumption check.**  The verbatim statement of
`Modularity.BlockFiniteDim.exists_finrank_analyticBlocks_le`, re-proved through the Etingof route.
The `hzero` the Etingof route needs is free (`QuasiLisseSl2.vacuumGradeZero_of_vacuum_grade`), so
the hypothesis list really is unchanged. -/
theorem exists_finrank_analyticBlocks_le_c2_via_etingofFinite (hC2 : C2Cofinite W) {z₀ : ℂ}
    (hz₀ : z₀ ∈ imGT 0) :
    ∃ g : ℕ, FiniteDimensional ℂ (Submodule.map restrictImGT (analyticBlocks W)) ∧
      Module.finrank ℂ (Submodule.map restrictImGT (analyticBlocks W)) ≤ g + 1 :=
  exists_finrank_analyticBlocks_le_of_etingofFinite W
    (QuasiLisseSl2.vacuumGradeZero_of_vacuum_grade W) (EtingofFinite_of_C2Cofinite W hC2) hz₀

end BlockFinite

example : @finiteDimensional_analyticBlocks_of_C2Cofinite
    = @finiteDimensional_analyticBlocks_of_C2Cofinite_via_etingofFinite := rfl

example : @exists_finrank_analyticBlocks_le
    = @exists_finrank_analyticBlocks_le_c2_via_etingofFinite := rfl

/-! ## §9  The `finrank`-form wrappers under `EtingofFinite`

`Modularity.SlashAmbientObstruction.finiteDimensional_sqAnalyticSlashAmbient` spends `hC2` on one
line, `exists_finrank_analyticBlocks_le`.  §8 replaces that line.  The two consumers of the
resulting instance — `Modularity.SqAmbientAssembly.exists_jacobiTransformation_v_zero_sq'` and
`char_SL2Z_invariant_of_sqAnalyticRank`, both of which use it only to turn a `finrank ≤ n`
hypothesis into `rank ≤ n` — follow.
-/

section FinrankForms

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Zhu's Theorem 5.3.2 on the repaired ambient, under `EtingofFinite`.**  Etingof twin of
`Modularity.SlashAmbientObstruction.finiteDimensional_sqAnalyticSlashAmbient`. -/
theorem finiteDimensional_sqAnalyticSlashAmbient_of_etingofFinite
    (Mfam : ι → IrrModule W) (h : ι → ℂ) (hzero : VacuumGradeZero W) (hE : EtingofFinite W) :
    FiniteDimensional ℂ (sqAnalyticSlashAmbient Mfam h) := by
  haveI := finiteDimensional_analyticBlocks_of_etingofFinite W hzero hE
  have hmapeq : Submodule.map (sqRestrict W) (analyticBlocks W)
      = Submodule.map (sqPtEval W) (Submodule.map restrictImGT (analyticBlocks W)) := by
    rw [sqRestrict_eq_comp, Submodule.map_comp]
  haveI : FiniteDimensional ℂ (Submodule.map (sqRestrict W) (analyticBlocks W)) := by
    rw [hmapeq]; infer_instance
  haveI : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun i : ι =>
      sqRestrict W (blockSlash W ModularGroup.S (traceBlock Mfam h i)))) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  exact Submodule.finiteDimensional_sup _ _

/-- **Subsumption check.**  The verbatim statement of
`Modularity.SlashAmbientObstruction.finiteDimensional_sqAnalyticSlashAmbient`, through the Etingof
route.  (The `z₀` argument of the original is genuinely unused on this route — §8 works at every
point of `ℍ` — but it is kept so that the statement is character-for-character the original.) -/
theorem finiteDimensional_sqAnalyticSlashAmbient_c2_via_etingofFinite
    (Mfam : ι → IrrModule W) (h : ι → ℂ) (hC2 : C2Cofinite W) {z₀ : ℂ}
    (hz₀ : z₀ ∈ imGT 0) : FiniteDimensional ℂ (sqAnalyticSlashAmbient Mfam h) :=
  finiteDimensional_sqAnalyticSlashAmbient_of_etingofFinite Mfam h
    (QuasiLisseSl2.vacuumGradeZero_of_vacuum_grade W) (EtingofFinite_of_C2Cofinite W hC2)

/-- Zhu Theorem 5.3.9's `v = 0` slice in `finrank` form, under `EtingofFinite`.  Etingof twin
of `Modularity.SqAmbientAssembly.exists_jacobiTransformation_v_zero_sq'`. -/
theorem exists_jacobiTransformation_v_zero_sq'_of_etingofFinite (Mfam : ι → IrrModule W)
    (hh : ι → ℂ) (β : 𝒱 →ₗ[ℂ] 𝒱 →ₗ[ℂ] ℂ) (hzero : VacuumGradeZero W) (hE : EtingofFinite W)
    (hcw : ∀ i, HasConformalWeight (Mfam i).isMod (hh i))
    (hinj : Function.Injective (tEigen W hh))
    (hle : Module.finrank ℂ (sqAnalyticSlashAmbient Mfam hh) ≤ Fintype.card ι) :
    ∃ D : ModularData W ι, ZhuModularityAnalytic D ∧
      ∀ (A : SL(2, ℤ)) (w : ℂ) (i : ι) (τ : UpperHalfPlane),
        jacobiChar (D.Mfam i).isMod (D.h i) β ((autFactor A τ)⁻¹ • (0 : 𝒱))
            (w - ((A : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) * β 0 0 / (2 * autFactor A τ)) (A • τ)
          = ∑ j, D.rep A i j * jacobiChar (D.Mfam j).isMod (D.h j) β 0 w τ := by
  haveI := finiteDimensional_sqAnalyticSlashAmbient_of_etingofFinite Mfam hh hzero hE
  refine exists_jacobiTransformation_v_zero_sq Mfam hh β hcw
    (fun i => onePointSubexp_of_etingofFinite W (Mfam i).isMod (hcw i) hzero hE) hinj ?_
  rw [← Module.finrank_eq_rank]
  exact_mod_cast hle

end FinrankForms

/-- **Subsumption check.**  The verbatim statement of
`Modularity.SqAmbientAssembly.exists_jacobiTransformation_v_zero_sq'`, through the Etingof route.
(The binder list is written out rather than taken from section variables, so that the order of the
implicit `ι` / `W` arguments matches the original character for character.) -/
theorem exists_jacobiTransformation_v_zero_sq'_c2_via_etingofFinite {ι : Type*} [Fintype ι]
    [DecidableEq ι] {W : VertexOperatorAlgebra 𝒱} (Mfam : ι → IrrModule W)
    (hh : ι → ℂ) (β : 𝒱 →ₗ[ℂ] 𝒱 →ₗ[ℂ] ℂ) (hC2 : C2Cofinite W) {z₀ : ℂ} (hz₀ : z₀ ∈ imGT 0)
    (hcw : ∀ i, HasConformalWeight (Mfam i).isMod (hh i))
    (hgr : ∀ i, OnePointSubexp (Mfam i).isMod (hh i - W.centralCharge / 24))
    (hinj : Function.Injective (tEigen W hh))
    (hle : Module.finrank ℂ (sqAnalyticSlashAmbient Mfam hh) ≤ Fintype.card ι) :
    ∃ D : ModularData W ι, ZhuModularityAnalytic D ∧
      ∀ (A : SL(2, ℤ)) (w : ℂ) (i : ι) (τ : UpperHalfPlane),
        jacobiChar (D.Mfam i).isMod (D.h i) β ((autFactor A τ)⁻¹ • (0 : 𝒱))
            (w - ((A : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) * β 0 0 / (2 * autFactor A τ)) (A • τ)
          = ∑ j, D.rep A i j * jacobiChar (D.Mfam j).isMod (D.h j) β 0 w τ := by
  haveI := finiteDimensional_sqAnalyticSlashAmbient_c2_via_etingofFinite Mfam hh hC2 hz₀
  refine exists_jacobiTransformation_v_zero_sq Mfam hh β hcw hgr hinj ?_
  rw [← Module.finrank_eq_rank]
  exact_mod_cast hle

example : @finiteDimensional_sqAnalyticSlashAmbient
    = @finiteDimensional_sqAnalyticSlashAmbient_c2_via_etingofFinite := rfl

example : @exists_jacobiTransformation_v_zero_sq'
    = @exists_jacobiTransformation_v_zero_sq'_c2_via_etingofFinite := rfl


/-- **Gannon Question 5.3.4 under `EtingofFinite`.**  A holomorphic `𝒱` with `c = 24`
satisfying the Arakawa–Kawasetsu finiteness hypothesis has an `SL₂(ℤ)`-invariant character, from
the *satisfiable* rank bound on `sqAnalyticSlashAmbient`.  Etingof twin of
`Modularity.SqAmbientAssembly.char_SL2Z_invariant_of_sqAnalyticRank`; the growth datum `hsub`,
which the `C₂` form carries as a hypothesis, is here discharged by the Etingof route. -/
theorem char_SL2Z_invariant_of_sqAnalyticRank_of_etingofFinite {W : VertexOperatorAlgebra 𝒱}
    (V : IrrModule W) (hzero : VacuumGradeZero W) (hE : EtingofFinite W)
    (hcw : HasConformalWeight V.isMod 0)
    (hle : Module.finrank ℂ (sqAnalyticSlashAmbient (singleFam V) (fun _ => (0 : ℂ))) ≤ 1)
    (hc : W.centralCharge = 24) (A : SL(2, ℤ)) (τ : UpperHalfPlane) :
    traceFun (singleFam V) (fun _ => (0 : ℂ)) () W.vacuum (A • τ)
      = traceFun (singleFam V) (fun _ => (0 : ℂ)) () W.vacuum τ := by
  have hcwf : ∀ i : Unit, HasConformalWeight (singleFam V i).isMod ((fun _ : Unit => (0 : ℂ)) i) :=
    fun _ => hcw
  have hsub : ∀ i : Unit, OnePointSubexp (singleFam V i).isMod
      ((fun _ : Unit => (0 : ℂ)) i - W.centralCharge / 24) :=
    fun i => onePointSubexp_of_etingofFinite W (singleFam V i).isMod (hcwf i) hzero hE
  have hnv : TraceNonvanishing (singleFam V) (fun _ => (0 : ℂ)) :=
    traceNonvanishing_of_onePointSubexp (singleFam V) (fun _ => (0 : ℂ)) hcwf hsub
  have hind : TraceIndependent (singleFam V) (fun _ => (0 : ℂ)) :=
    traceIndependent_of_tEigen_injective (singleFam V) (fun _ => (0 : ℂ)) hcwf
      (tEigen_injective_unit _) hnv
  haveI := finiteDimensional_sqAnalyticSlashAmbient_of_etingofFinite (singleFam V)
    (fun _ => (0 : ℂ)) hzero hE
  have hrank : Module.rank ℂ (sqAnalyticSlashAmbient (singleFam V) (fun _ => (0 : ℂ)))
      ≤ (Fintype.card Unit : Cardinal) := by
    rw [← Module.finrank_eq_rank, show (Fintype.card Unit : ℕ) = 1 from by simp]
    exact_mod_cast hle
  have hsp : TraceSpanning (singleFam V) (fun _ => (0 : ℂ)) :=
    traceSpanning_of_slashSpannedAtS (singleFam V) (fun _ => (0 : ℂ)) hcwf hsub
      (slashSpannedAtS_of_sqRank_le (singleFam V) (fun _ => (0 : ℂ)) _ hind
        (sqRestrict_traceBlock_mem_sqAnalyticSlashAmbient (singleFam V) (fun _ => (0 : ℂ))
          hcwf hsub)
        (sqRestrict_slash_mem_sqAnalyticSlashAmbient (singleFam V) (fun _ => (0 : ℂ))) hrank)
  exact char_SL2Z_invariant_of_spanning V hsp hind hcw hc
    (traceFun_vacuum_ne_zero (singleFam V) (fun _ => (0 : ℂ)) hcwf hsub ()) A τ

/-- **Subsumption check.**  The verbatim statement of
`Modularity.SqAmbientAssembly.char_SL2Z_invariant_of_sqAnalyticRank`, through the Etingof route.
Its `hsub` is genuinely unused on this route (the Etingof hypothesis supplies it), and its `hC2`
is spent only on `EtingofFinite_of_C2Cofinite`. -/
theorem char_SL2Z_invariant_of_sqAnalyticRank_c2_via_etingofFinite
    {W : VertexOperatorAlgebra 𝒱} (V : IrrModule W) (hC2 : C2Cofinite W) {z₀ : ℂ}
    (hz₀ : z₀ ∈ imGT 0) (hcw : HasConformalWeight V.isMod 0)
    (hsub : ∀ i : Unit, OnePointSubexp (singleFam V i).isMod
      ((fun _ : Unit => (0 : ℂ)) i - W.centralCharge / 24))
    (hle : Module.finrank ℂ (sqAnalyticSlashAmbient (singleFam V) (fun _ => (0 : ℂ))) ≤ 1)
    (hc : W.centralCharge = 24) (A : SL(2, ℤ)) (τ : UpperHalfPlane) :
    traceFun (singleFam V) (fun _ => (0 : ℂ)) () W.vacuum (A • τ)
      = traceFun (singleFam V) (fun _ => (0 : ℂ)) () W.vacuum τ :=
  char_SL2Z_invariant_of_sqAnalyticRank_of_etingofFinite V
    (QuasiLisseSl2.vacuumGradeZero_of_vacuum_grade W) (EtingofFinite_of_C2Cofinite W hC2)
    hcw hle hc A τ

example : @char_SL2Z_invariant_of_sqAnalyticRank
    = @char_SL2Z_invariant_of_sqAnalyticRank_c2_via_etingofFinite := rfl

end VOA
