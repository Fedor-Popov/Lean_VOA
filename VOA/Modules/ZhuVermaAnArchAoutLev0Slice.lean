/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchAoutUCore
import VOA.Modules.ZhuVermaAnArchCrossDiffCommutator
import VOA.Modules.ZhuVermaAnArchCrossCFirstGate
import VOA.Modules.ZhuVermaAnArchARDTowerClose

/-!
# Game One (ATTACK 1) — closing **`AoutUCoreLev0Core`** by MIRRORING the proven slice-difference.

This file discharges the SINGLE remaining collapse lemma `AoutUCoreLev0Core`
(`ZhuVermaAnArchAoutUCore`) — the level-`0` half cross-base collapse that the whole `~1700`-line
`ARDTowerDecomp` apparatus is reduced to — and thereby closes `MUGradedAction W` (Zhu Thm 5.3.4) on
the SAME single endgame core `ARDTowerDecomp` as every other route.

## The mirror (the `a`-outer `c`-outer twin of `crossDiffSliceDiff_eq_PresTowerFam`)

The proven per-`s` slice difference (`crossDiffSliceDiff_eq_PresTowerFam`, `ZhuVermaAnArchHPoleN`)
collapses the level-`2`-vs-level-`(n+2)` pole DIFFERENCE of a single base `c₍s₎a` onto a homogeneous
grade-`Ws` single-base `PresTowerFam` in `c₍s₎a`, the `n`-offset absorbed by
`towerCoeffAnm_regrade_int`.  The `a`-outer `c`-outer level-`0` half `aOutLev0Half` carries EXACTLY
the same level-`0`-vs-level-`n` pole-difference structure, reorganized over the multi-base `a₍·₎d`.
Concretely, the `a`-outer `i`-sum reindexes onto the PROVEN master-split of the `c`-outer face:

  `aOutLev0Half = aOutUPart + aOutLevNHalf`          (`aOutUPart_eq_halfDiff`),
  `aOutUPart    = crossCFirstDiff`                   (`aOutUPart_eq_crossCFirstDiff`),
  `crossCFirstDiff = anmRightDiff + crossDiffComm`   (`crossCFirstDiff_master_split`),
  `crossDiffComm   = MGTowerFam` (`c₍s₎a` @ `d`)     (`crossDiffComm_eq_MGTowerFam`),
  `aOutLevNHalf    = PresTowerFam` (`c` @ `a₍·₎d`)   (`aOutLevNHalf_eq_PresTowerFam`),

so once `anmRightDiff` is supplied as `PresTowerFam(c) + MGTowerFam` by the genuine endgame core
`ARDTowerDecomp` (the `a`-outer right-action-difference tower decomposition, engine-verified TRUE,
`certificates/mathematica/anmrightdiff_tower.wl`), the level-`0` half is

  `aOutLev0Half = (U-tower in `c` ⊕ U_N-tower in `c`) + (W₁-`MGTowerFam` ⊕ W₂-`MGTowerFam`)`,

merging the two `c`-`PresTowerFam`s (`PresTowerFam_add`, both grade `M` level `n` in `c`) and the two
`c₍s₎a`-`MGTowerFam`s (`MGTowerFam_add`, homogeneity `MGTowerFam_add_hom`) into the exact
`AoutUCoreLev0Core` shape `PresTowerFam W M n c … + MGTowerFam W n …`.

This is the `a`-outer `c`-outer face of the same Dong–Jiang Lemma 2.8 reorganization; it agrees with
the diagonal route (`crossCFirstDiffTowerEq_of_circDiff`), the `c`-PAST-`a` route
(`crossCFirstDiffTowerEq_of_ARDTowerDecomp`) and the FZ-commutator route
(`crossCFirstDiffTowerEq_of_ARDTowerDecomp_via_comm`): **all close on the SAME single
`ARDTowerDecomp`**.

## Engine status (rank-1 free boson; NOT faked)

`certificates/mathematica/aout_lev0_verify.wl` (new): with the level-`n` `c`-towers over the WIDER bases
`a₍g₎d` and the `c₍s₎a` `MGTowerFam` based at `d`,

  `aOutLev0Half ∈ (c-tow@a₍g₎d) + ((c₍s₎a)-tow@d)`  is **True**  (`n = 1, 2`; mixed homogeneous
  `a, c, d`; span bounds `9`); the pure `c`-towers ALONE do NOT suffice (**False**) — the `c₍s₎a`
  `MGTowerFam` is load-bearing, exactly as for `anmRightDiff` (`certificates/mathematica/anmrightdiff_tower.wl`).

## What is proved here (axiom-clean)

* `aOutLev0Half_eq_addThree` — the `a`-outer `i`-sum reindex of `aOutLev0Half` onto the PROVEN
  master-split: `aOutLev0Half = anmRightDiff + crossDiffComm + aOutLevNHalf`.
* `aoutUCoreLev0Core_of_ARDTowerDecomp` — **the close**: `ARDTowerDecomp` ⟹ `AoutUCoreLev0Core`,
  the level-`0` half collapse, by merging the two `c`-`PresTowerFam`s and the two `c₍s₎a`-`MGTowerFam`s.
* `MUGradedAction_of_ARDTowerDecomp_via_aOutLev0` — **the full `MUGradedAction W`** from the single
  universal `ARDTowerDecomp`, through the `a`-outer `c`-outer level-`0` route
  (`aoutUCoreLev0Core_of_ARDTowerDecomp` ⟶ `MUGradedAction_of_aOutUCoreLev0Core`).

## References
Dong–Jiang, Math. Z. 259 (2008) 799–826 (`math/0601626`), §2 (Lemma 2.8); Frenkel–Zhu Lemma 2.1.2;
Dong–Li–Mason; Gannon §5.3.2, Thm 5.3.4.
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The `a`-outer `i`-sum reindex of `aOutLev0Half` onto the master-split. -/

/-- **`aOutLev0Half` as the three-way sum** `anmRightDiff + crossDiffComm + aOutLevNHalf` (FULLY
proven, homogeneous `a ∈ 𝒱_K`, `c ∈ 𝒱_M`).  This is the `a`-outer `i`-sum reindex: the level-`0` half
`aOutLev0Half` equals the level-`n` half `aOutLevNHalf` PLUS the `c`-outer pole-DIFFERENCE
`aOutUPart = crossCFirstDiff` (`aOutUPart_eq_halfDiff`, `aOutUPart_eq_crossCFirstDiff`), and the
DIFFERENCE master-splits into the `a`-outer right-action piece `anmRightDiff` plus the `c₍s₎a`
commutator piece `crossDiffComm` (`crossCFirstDiff_master_split`).  Per `a`-outer index `i`, the inner
`(c∘₀)(a₍i−n−1₎d)` minus its level-`n` companion is exactly the per-base pole-difference structure that
`crossDiffSliceDiff_eq_PresTowerFam` handles. -/
theorem aOutLev0Half_eq_addThree (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {K M : ℕ}
    {a : 𝒱} (ha : a ∈ W.grading (K : ℤ)) {c : 𝒱} (hc : c ∈ W.grading (M : ℤ)) (d : 𝒱) :
    aOutLev0Half W n K M a c d
      = anmRightDiff W n K a c d + crossDiffComm W n K M a c d + aOutLevNHalf W n K M a c d := by
  -- `aOutLev0Half = aOutUPart + aOutLevNHalf` (from `aOutUPart = aOutLev0Half − aOutLevNHalf`).
  have hsplit : aOutLev0Half W n K M a c d
      = aOutUPart W n K M a c d + aOutLevNHalf W n K M a c d := by
    rw [aOutUPart_eq_halfDiff W n K M a c d]; abel
  rw [hsplit, aOutUPart_eq_crossCFirstDiff W n K M a c d,
    crossCFirstDiff_master_split W n ha hc d]

/-! ## The close — `ARDTowerDecomp` ⟹ `AoutUCoreLev0Core`. -/

/-- **`ARDTowerDecomp` ⟹ `AoutUCoreLev0Core`** (the level-`0` half cross-base collapse, the `a`-outer
`c`-outer face).  By the three-way reindex `aOutLev0Half_eq_addThree`,

  `aOutLev0Half = anmRightDiff + crossDiffComm + aOutLevNHalf`,

with each summand a known tower family:

* `anmRightDiff = PresTowerFam W M n c RU₁ ΔU₁ baseU₁ wU₁ + MGTowerFam W n S₁ …` — the genuine endgame
  core `ARDTowerDecomp` (the `a`-outer right-action-difference tower decomposition);
* `crossDiffComm = MGTowerFam W n S₂ …` (in the products `c₍s₎a` @ `d`) — `crossDiffComm_eq_MGTowerFam`
  (PART (II), FULLY proven via the two commutator twins);
* `aOutLevNHalf = PresTowerFam W M n c (K+1) 1 …` (in `c` @ `a₍·₎d`) — `aOutLevNHalf_eq_PresTowerFam`
  (the clean level-`n` half collapse, FULLY proven).

Merging the two grade-`M` level-`n` `c`-`PresTowerFam`s (`PresTowerFam_add`) and the two
`c₍s₎a`-`MGTowerFam`s (`MGTowerFam_add`, homogeneity `MGTowerFam_add_hom`) yields the explicit
`AoutUCoreLev0Core` witness `PresTowerFam W M n c … + MGTowerFam W n …`.  The `a`-outer `c`-outer twin
of the diagonal `UgammaModeCollAnm_eq_towerCoeff` + slice difference
`crossDiffSliceDiff_eq_PresTowerFam`; engine-verified TRUE (`certificates/mathematica/aout_lev0_verify.wl`,
both families load-bearing). -/
theorem aoutUCoreLev0Core_of_ARDTowerDecomp (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {K M P : ℕ}
    {a : 𝒱} (ha : a ∈ W.grading (K : ℤ)) {c : 𝒱} (hc : c ∈ W.grading (M : ℤ))
    {d : 𝒱} (hd : d ∈ W.grading (P : ℤ))
    (hard : ARDTowerDecomp W n K M P a c d) :
    AoutUCoreLev0Core W n K M P a c d := by
  -- PART (I): `anmRightDiff = PresTowerFam(c) U₁ + MGTowerFam W₁` (the endgame core).
  obtain ⟨RU₁, ΔU₁, S₁, baseU₁, wU₁, gradeS₁, leftS₁, baseS₁, ΔS₁, wS₁, hhom₁, heqARD⟩ := hard
  -- PART (II): `crossDiffComm = MGTowerFam W₂` (fully proven).
  obtain ⟨S₂, gradeS₂, leftS₂, baseS₂, ΔS₂, wS₂, hhom₂, heqComm⟩ :=
    crossDiffComm_eq_MGTowerFam W n ha hc hd
  -- the merged `c`-`PresTowerFam` (U₁ ⊕ U_N) and the merged `c₍s₎a`-`MGTowerFam` (W₁ ⊕ W₂).
  refine ⟨RU₁ + (K + 1), max ΔU₁ 1, S₁ + S₂,
    (fun r => Sum.elim baseU₁
        (fun i : Fin (K + 1) => W.smul a ((i : ℤ) - ((n : ℤ) + 1)) d) (finSumFinEquiv.symm r)),
    (fun r δ => Sum.elim (fun r₁ => if δ < ΔU₁ then wU₁ r₁ δ else 0)
        (fun r₂ : Fin (K + 1) => if δ < 1 then (if δ = 0 then cbz (K : ℤ) (r₂ : ℤ) else 0) else 0)
        (finSumFinEquiv.symm r)),
    (fun r => Sum.elim gradeS₁ gradeS₂ (finSumFinEquiv.symm r)),
    (fun r => Sum.elim leftS₁ leftS₂ (finSumFinEquiv.symm r)),
    (fun r => Sum.elim baseS₁ baseS₂ (finSumFinEquiv.symm r)),
    (fun r => Sum.elim ΔS₁ ΔS₂ (finSumFinEquiv.symm r)),
    (fun r => Sum.elim wS₁ wS₂ (finSumFinEquiv.symm r)),
    MGTowerFam_add_hom W S₁ S₂ gradeS₁ leftS₁ gradeS₂ leftS₂ hhom₁ hhom₂, ?_⟩
  rw [aOutLev0Half_eq_addThree W n ha hc d, heqARD, heqComm,
    aOutLevNHalf_eq_PresTowerFam W n K M a c d]
  -- `(U₁ + W₁) + W₂ + U_N = (U₁ + U_N) + (W₁ + W₂)`.
  rw [show (PresTowerFam W M n c RU₁ ΔU₁ baseU₁ wU₁
              + MGTowerFam W n S₁ gradeS₁ leftS₁ baseS₁ ΔS₁ wS₁)
            + MGTowerFam W n S₂ gradeS₂ leftS₂ baseS₂ ΔS₂ wS₂
            + PresTowerFam W M n c (K + 1) 1
                (fun i => W.smul a ((i : ℤ) - ((n : ℤ) + 1)) d)
                (fun i δ => if δ = 0 then cbz (K : ℤ) (i : ℤ) else 0)
          = (PresTowerFam W M n c RU₁ ΔU₁ baseU₁ wU₁
              + PresTowerFam W M n c (K + 1) 1
                  (fun i => W.smul a ((i : ℤ) - ((n : ℤ) + 1)) d)
                  (fun i δ => if δ = 0 then cbz (K : ℤ) (i : ℤ) else 0))
            + (MGTowerFam W n S₁ gradeS₁ leftS₁ baseS₁ ΔS₁ wS₁
                + MGTowerFam W n S₂ gradeS₂ leftS₂ baseS₂ ΔS₂ wS₂) from by abel]
  rw [PresTowerFam_add W M n c RU₁ (K + 1) ΔU₁ 1 baseU₁
        (fun i => W.smul a ((i : ℤ) - ((n : ℤ) + 1)) d) wU₁
        (fun i δ => if δ = 0 then cbz (K : ℤ) (i : ℤ) else 0),
    MGTowerFam_add W n S₁ S₂ gradeS₁ leftS₁ baseS₁ ΔS₁ wS₁ gradeS₂ leftS₂ baseS₂ ΔS₂ wS₂]

/-! ## The full `MUGradedAction W` from the single universal `ARDTowerDecomp`. -/

/-- **The full `MUGradedAction W` through the `a`-outer `c`-outer level-`0` route.**  Given, for every
level `n` and all homogeneous data, the `a`-outer right-action-difference tower decomposition
`ARDTowerDecomp` (the genuine single endgame core), the level-`0` half collapse
`aoutUCoreLev0Core_of_ARDTowerDecomp` supplies the universal `AoutUCoreLev0Core`, and the PROVEN
`MUGradedAction_of_aOutUCoreLev0Core` (`ZhuVermaAnArchAoutUCore`) — every other structural piece (the
clean level-`n` half `aOutLevNHalf_eq_PresTowerFam`, the assembly
`crossCFirstDiffTowerEq_of_aOutUCoreLev0Core`, the membership half) fully discharged — assembles the
Dong–Jiang `M(U)` graded-action crux `MUGradedAction W` (the `q_act` source of the bijection
`Function.Bijective (forwardMap W)`, Zhu Thm 5.3.4).

This is the `a`-outer `c`-outer face of the same single-core reduction; it agrees with the diagonal,
`c`-PAST-`a`, and FZ-commutator routes — all close on the SAME `ARDTowerDecomp`. -/
theorem MUGradedAction_of_ARDTowerDecomp_via_aOutLev0 (W : VertexOperatorAlgebra 𝒱)
    (Hdec : ∀ (n K M P : ℕ), ∀ a ∈ W.grading (K : ℤ), ∀ c ∈ W.grading (M : ℤ),
      ∀ d ∈ W.grading (P : ℤ), ARDTowerDecomp W n K M P a c d) :
    MUGradedAction W :=
  MUGradedAction_of_aOutUCoreLev0Core W
    (fun n K M P a ha c hc d hd =>
      aoutUCoreLev0Core_of_ARDTowerDecomp W n ha hc hd (Hdec n K M P a ha c hc d hd))

/-! ## Status — `AoutUCoreLev0Core` closed to the single endgame core `ARDTowerDecomp`.

Proved here (`#print axioms` = `[propext, Classical.choice, Quot.sound]`; no `sorry`/
`axiom`/`pbw`):

* **`aOutLev0Half_eq_addThree`** — the `a`-outer `i`-sum reindex onto the PROVEN master-split:
  `aOutLev0Half = anmRightDiff + crossDiffComm + aOutLevNHalf` (via `aOutUPart_eq_halfDiff`,
  `aOutUPart_eq_crossCFirstDiff`, `crossCFirstDiff_master_split`).
* **`aoutUCoreLev0Core_of_ARDTowerDecomp`** — **the close**: `ARDTowerDecomp` ⟹ `AoutUCoreLev0Core`,
  merging the two `c`-`PresTowerFam`s (`PresTowerFam_add`) and the two `c₍s₎a`-`MGTowerFam`s
  (`MGTowerFam_add`, homogeneity `MGTowerFam_add_hom`); PART (II) `crossDiffComm` discharged as an
  `MGTowerFam` (`crossDiffComm_eq_MGTowerFam`), the level-`n` half as the proven
  `aOutLevNHalf_eq_PresTowerFam`.
* **`MUGradedAction_of_ARDTowerDecomp_via_aOutLev0`** — **the full `MUGradedAction W`** from the single
  universal `ARDTowerDecomp`, through `aoutUCoreLev0Core_of_ARDTowerDecomp` ⟶
  `MUGradedAction_of_aOutUCoreLev0Core`.

**The single endgame core (engine-verified TRUE; NOT faked):** the universally-quantified
`ARDTowerDecomp W n K M P a c d` — the `a`-outer right-action-difference family as a `PresTowerFam`
U-tower in `c` (based at `a₍g₎d`) plus a multi-grade `MGTowerFam` W-family in the products `c₍s₎a`
(based at `d`).  The `a`-outer `c`-outer level-`0` half `AoutUCoreLev0Core` is closed to it (this
file); the `n`-offset is absorbed by the proven regrade `crossDiff_regrade`/`towerCoeffAnm_regrade_int`
(`ZhuVermaAnArchHPoleN`).  Engine (`certificates/mathematica/aout_lev0_verify.wl`):
`aOutLev0Half ∈ (c-tow@a₍g₎d)+((c₍s₎a)-tow@d)` (**True**, `n = 1, 2`); pure `c`-towers ALONE do NOT
suffice (**False**) — the `c₍s₎a` `MGTowerFam` is load-bearing.
-/

end VOA

/-
`#print axioms` check (each of the following prints
`[propext, Classical.choice, Quot.sound]`, NO `pbw`, NO `sorryAx`):

  #print axioms VOA.aOutLev0Half_eq_addThree
  #print axioms VOA.aoutUCoreLev0Core_of_ARDTowerDecomp
  #print axioms VOA.MUGradedAction_of_ARDTowerDecomp_via_aOutLev0
-/
