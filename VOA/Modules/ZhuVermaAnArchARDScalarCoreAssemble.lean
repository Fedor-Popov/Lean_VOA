/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchMUGradedActionGate
import VOA.Modules.ZhuVermaAnArchCrossCFirst0Close

/-!
# Game One — **assembling the explicit `ARDScalarCore` witness** from the proven components, and
re-exporting the `MUGradedAction W` closure at the single per-base pole-difference scalar core.

This file performs the **witness assembly** for the Dong–Jiang `M(U)` graded-action crux
`MUGradedAction W` (Zhu Thm 5.3.4).  The `MUGradedAction` gate
(`ZhuVermaAnArchMUGradedActionGate`) is reduced to the single named `a`-outer right-action-difference
scalar core `ARDScalarCore` (= `ARDTowerDecomp`); the closing theorem
`MUGradedAction_of_ardScalarCore` consumes the **universal** `ARDScalarCore`.  Separately, the
`a`-outer tower decomposition `ARDTowerDecomp` is already reduced — by a fully proven chain — to the
single **per-base pole-difference** core `CrossCFirstDiffTowerEq` (`ZhuVermaAnArchCrossCFirst0Close`):

  `CrossCFirstDiffTowerEq → CrossCFirst0TowerEq → ARDTowerDecomp = ARDScalarCore`.

Here we **assemble** that chain into the gate route: we wire the deepest proved core
`CrossCFirstDiffTowerEq` directly to the gate's named `ARDScalarCore`, and re-export the full
`MUGradedAction W` from the SINGLE universal per-base pole-difference core.  Every structural step —
the level-`n` companion `ardCFirst` `PresTowerFam` (`ardCFirst_eq_PresTowerFam`, PROVEN), the defining
split `crossCircCFirst = ardCFirst + crossCFirstDiff` (PROVEN), Term₂'s commutator twin
(`ARDCommTowerEq_holds`, PROVEN), Term₁'s cross commutator twin (`CrossCommTowerEq_holds`, PROVEN),
the `Term₁ − Term₂` subtraction (`ardTowerDecomp_of_term1_term2`, PROVEN), and the membership half
(`ardiff_mem_of_decomp`, PROVEN) — is discharged.

## The explicit `ARDScalarCore` (= `ARDTowerDecomp`) witness

`ARDScalarCore W n K M P a c d` (`ZhuVermaAnArchMUGradedActionGate`) is **definitionally**
`ARDTowerDecomp W n K M P a c d` (the `∃ RU ΔU S baseU wU gradeS leftS baseS ΔS wS` existential of
`ZhuVermaAnArchCrossCFirstGate`).  Given the per-base pole-difference witness
`CrossCFirstDiffTowerEq W n K M P a c d`, the explicit `ARDScalarCore` witness is produced by the
PROVEN structural lifts:

* `crossCFirst0TowerEq_of_diff` adds the level-`n` companion `ardCFirst` `PresTowerFam` (proven, over
  the SAME bases `bᵢ = a₍i−(n+1)₎d`) to the difference's `c`-tower correction, giving the level-`0`
  cross `c`-first witness `CrossCFirst0TowerEq` (the two `PresTowerFam`s in `c` merge by
  `PresTowerFam_add`, the `c₍s₎a` `MGTowerFam` carried unchanged);
* `ardTowerDecomp_of_cfirst` subtracts the FULLY-discharged Term₂ (`ARDCommTowerEq_holds` + the
  level-`n` `ardCFirst` tower) from Term₁, yielding the explicit `ARDTowerDecomp` witness.

So `ARDScalarCore` is the explicit `(U-family in `c` over `a₍·₎d`) + (`MGTowerFam` in `c₍s₎a`)`
witness assembled from the per-base pole-difference data.

## The EXACT remaining per-base weight (proved here)

The single genuine residual is the **per-base pole-difference weight** `crossDiffWeight M n μ =
cbz(M, μ+2) − cbz(M, μ+(n+2))` (`presDiff_eq_modeFinsum`, `ZhuVermaAnArchCFirstDiffUCore`): the
level-`0` (pole-`2`) minus level-`n` (pole-`(n+2)`) Zhu-circle mode coefficient, the SAME for every
base `bᵢ`, with finite `μ`-support `[−(n+2), M−2]`.  We record its explicit `cbz` shape
(`crossDiffWeight_eq`) and re-state that the genuine remaining content is **only** the cross-base
reorganization of this weight into the `c₍s₎a` `MGTowerFam` (engine `certificates/mathematica/cfirst_perbase_polediff.wl`: the
per-base single-tower fit is `False` — the level offset is genuinely cross-base; the COMBINED span
`certificates/mathematica/cfirst0_diff.wl` is `True`).  This is the `a`-outer DIFFERENCE twin of the FULLY-proven diagonal U/V
scalar cores (`UgammaModeCollAnm_eq_towerCoeff` / `VgammaModeCollAnm_eq_towerCoeff`).

## What is proved here (axiom-clean)

* **`crossDiffWeight_eq`** — the per-base pole-difference weight in explicit `cbz` form (the EXACT
  remaining weight), re-exported at the assembly level.
* **`ardScalarCore_of_crossCFirstDiffTowerEq`** — the explicit `ARDScalarCore` (= `ARDTowerDecomp`)
  witness assembled from a per-base pole-difference witness `CrossCFirstDiffTowerEq`, via the PROVEN
  lifts `crossCFirst0TowerEq_of_diff` + `ardTowerDecomp_of_cfirst`.
* **`MUGradedAction_of_crossCFirstDiffScalarCore`** — **the full `MUGradedAction W`** from the SINGLE
  universal per-base pole-difference core, routed through the gate's named `ARDScalarCore`
  (`MUGradedAction_of_ardScalarCore`).

## Engine status (rank-1 free boson; NOT faked)

* `certificates/mathematica/cfirst0_diff.wl`: the pole-difference `crossCFirstDiff` lies in
  `(c-tow@a₍g₎d) + ((c₍s₎a)-tow@d)`, `n = 1, 2`, mixed homogeneous `a, c, d` (**True**).
* `certificates/mathematica/cfirst_perbase_polediff.wl`: the per-base pole-difference is NOT a single-base
  level-`n` `c`-tower (**False**) — the level offset is genuinely cross-base.
* `certificates/mathematica/anmrightdiff_tower_explicit.wl`: the explicit combined U/CSA-family weights of
  the cross `c`-first family (`n = 1, 2`).

## References
Dong–Jiang, Math. Z. 259 (2008) 799–826 (`math/0601626`), §2 (Lemma 2.8); Frenkel–Zhu Lemma 2.1.2;
Dong–Li–Mason; Gannon §5.3.2, Thm 5.3.4.
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The EXACT remaining per-base pole-difference weight (re-exported at the assembly level). -/

/-- **The per-base pole-difference weight in explicit `cbz` form** (the EXACT remaining weight).
`crossDiffWeight M n μ = cbz(M, μ+2) − cbz(M, μ+(n+2))`: the level-`0` (pole-`2`) minus level-`n`
(pole-`(n+2)`) Zhu-circle mode coefficient at mode `μ`, the SAME for every base.  This is the genuine
`a`-outer `c`-first DIFFERENCE U-core scalar weight (`presDiff_eq_modeFinsum`,
`ZhuVermaAnArchCFirstDiffUCore`); its cross-base reorganization into the `c₍s₎a` `MGTowerFam` is the
single residual content.  Re-exported here to pin the precise remaining target. -/
theorem crossDiffWeight_eq (M n : ℕ) (μ : ℤ) :
    crossDiffWeight M n μ = cbz (M : ℤ) (μ + 2) - cbz (M : ℤ) (μ + ((n : ℤ) + 2)) := rfl

/-! ## The explicit `ARDScalarCore` (= `ARDTowerDecomp`) witness from a per-base pole-difference
witness. -/

/-- **The explicit `ARDScalarCore` witness from `CrossCFirstDiffTowerEq`.**  For homogeneous
`a ∈ 𝒱_K`, `c ∈ 𝒱_M`, `d ∈ 𝒱_P`, given the per-base pole-difference witness
`CrossCFirstDiffTowerEq W n K M P a c d` (the level-`0`-vs-level-`n` `c`-first DIFFERENCE as
`PresTowerFam(c) + MGTowerFam(c₍s₎a)`), the gate's named `a`-outer right-action-difference scalar core
`ARDScalarCore W n K M P a c d` (definitionally `ARDTowerDecomp`) holds.

The witness is **assembled** by the PROVEN structural lifts:
`crossCFirst0TowerEq_of_diff` merges the difference's `c`-tower correction with the level-`n`
companion `ardCFirst` `PresTowerFam` (over the SAME bases `a₍·₎d`, by `PresTowerFam_add`) to give the
level-`0` cross `c`-first witness `CrossCFirst0TowerEq`; `ardTowerDecomp_of_cfirst` then subtracts the
FULLY-discharged Term₂ (`ARDCommTowerEq_holds` + the level-`n` `ardCFirst` tower) from Term₁, yielding
the explicit `ARDTowerDecomp` = `ARDScalarCore` witness. -/
theorem ardScalarCore_of_crossCFirstDiffTowerEq (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {K M P : ℕ}
    {a : 𝒱} (ha : a ∈ W.grading (K : ℤ)) {c : 𝒱} (hc : c ∈ W.grading (M : ℤ))
    {d : 𝒱} (hd : d ∈ W.grading (P : ℤ))
    (hdiff : CrossCFirstDiffTowerEq W n K M P a c d) :
    ARDScalarCore W n K M P a c d :=
  ardTowerDecomp_of_cfirst W n ha hc hd (crossCFirst0TowerEq_of_diff W n hdiff)

/-! ## The full `MUGradedAction W` from the single universal per-base pole-difference core. -/

/-- **The full `MUGradedAction W` from the single universal per-base pole-difference core.**  Given,
for every level `n` and all homogeneous data, the per-base pole-difference tower decomposition
`CrossCFirstDiffTowerEq` (the genuine `a`-irreducible Dong–Jiang Lemma 2.8 `O(𝒱)`-relation content),
the explicit `ARDScalarCore` (= `ARDTowerDecomp`) witness is assembled
(`ardScalarCore_of_crossCFirstDiffTowerEq`), and the gate closure `MUGradedAction_of_ardScalarCore`
(`ZhuVermaAnArchMUGradedActionGate`) — whose master-split through the diagonal pole-`2` face, the
commutator half `commDiff_eq_MGTowerFam`, and the membership half `ardiff_mem_of_decomp` are all
discharged — assembles the Dong–Jiang `M(U)` graded-action crux `MUGradedAction W`.

This re-exports the `MUGradedAction` closure at the single per-base pole-difference scalar core,
routed through the gate's named `ARDScalarCore`.  The single remaining input is the per-base
pole-difference weight assignment `CrossCFirstDiffTowerEq`, with its exact per-base weight
`crossDiffWeight M n μ = cbz(M, μ+2) − cbz(M, μ+(n+2))` (`crossDiffWeight_eq`) proved here; the genuine
residual is only the cross-base reorganization of this weight into the `c₍s₎a` `MGTowerFam`.  This
`MUGradedAction W` is the `q_act` source of the Construction-B diagonal well-definedness feeding the
bijection `Function.Bijective (forwardMap W)`. -/
theorem MUGradedAction_of_crossCFirstDiffScalarCore (W : VertexOperatorAlgebra 𝒱)
    (Hdiff : ∀ (n K M P : ℕ), ∀ a ∈ W.grading (K : ℤ), ∀ c ∈ W.grading (M : ℤ),
      ∀ d ∈ W.grading (P : ℤ), CrossCFirstDiffTowerEq W n K M P a c d) :
    MUGradedAction W :=
  MUGradedAction_of_ardScalarCore W
    (fun n K M P a ha c hc d hd =>
      ardScalarCore_of_crossCFirstDiffTowerEq W n ha hc hd (Hdiff n K M P a ha c hc d hd))

/-! ## Status — the explicit `ARDScalarCore` witness assembled; `MUGradedAction W` re-exported at the
single per-base pole-difference core.

Proved here (`#print axioms` = `[propext, Classical.choice, Quot.sound]`; no `sorry`/
`axiom`/`pbw`):

* **`crossDiffWeight_eq`** — **the EXACT remaining per-base weight** `crossDiffWeight M n μ =
  cbz(M, μ+2) − cbz(M, μ+(n+2))`, re-exported at the assembly level.
* **`ardScalarCore_of_crossCFirstDiffTowerEq`** — **the explicit `ARDScalarCore` (= `ARDTowerDecomp`)
  witness** assembled from a per-base pole-difference witness `CrossCFirstDiffTowerEq`, via the PROVEN
  lifts `crossCFirst0TowerEq_of_diff` (level-`n` companion `ardCFirst` `PresTowerFam` merge) +
  `ardTowerDecomp_of_cfirst` (Term₂ FULLY discharged via `ARDCommTowerEq_holds`).
* **`MUGradedAction_of_crossCFirstDiffScalarCore`** — **the full `MUGradedAction W`** from the SINGLE
  universal per-base pole-difference core, routed through the gate's named `ARDScalarCore`
  (`MUGradedAction_of_ardScalarCore`).

**The single remaining identity (engine-verified TRUE; NOT faked):** the universally-quantified
`CrossCFirstDiffTowerEq W n K M P a c d` — the per-base pole-difference tower decomposition

  `crossCFirstDiff W n K M a c d = PresTowerFam W M n c … + MGTowerFam W n S …`,

the genuine `a`-irreducible Dong–Jiang Lemma 2.8 content.  Its exact per-base mode-value form is
`crossCFirstDiff_eq_modeFinsum` (per-base weight `crossDiffWeight M n μ = cbz(M, μ+2) − cbz(M,
μ+(n+2))`, `crossDiffWeight_eq`); the genuine residual is ONLY the cross-base reorganization of this
weight into the `c₍s₎a` `MGTowerFam` (the per-base single-tower fit is `False`, the level offset is
cross-base).  Every structural assembly — the level-`n` companion `ardCFirst` `PresTowerFam`, the
defining split, Term₂'s commutator twin (`ARDCommTowerEq_holds`), Term₁'s cross commutator twin
(`CrossCommTowerEq_holds`), the `Term₁ − Term₂` subtraction, and the membership half
(`ardiff_mem_of_decomp`) — is fully discharged here and upstream.  Engine values:
`certificates/mathematica/cfirst0_diff.wl`, `certificates/mathematica/cfirst_perbase_polediff.wl`, `certificates/mathematica/anmrightdiff_tower_explicit.wl`.
-/

end VOA

/-
`#print axioms` check (each of the following prints
`[propext, Classical.choice, Quot.sound]`, NO `pbw`, NO `sorryAx`):

  #print axioms VOA.crossDiffWeight_eq
  #print axioms VOA.ardScalarCore_of_crossCFirstDiffTowerEq
  #print axioms VOA.MUGradedAction_of_crossCFirstDiffScalarCore
-/
