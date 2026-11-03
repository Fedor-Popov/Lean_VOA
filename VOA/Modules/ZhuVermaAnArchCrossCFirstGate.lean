/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchAnmRightDiff
import VOA.Modules.ZhuVermaAnArchVcoreTwins

/-!
# Game One — closing the single combinatorial gate `CrossCFirstOnm` to ONE tower decomposition.

This file works on the **single** remaining open family of the Dong–Jiang induced module `M(U)`
`V`-action crux `MUGradedAction W` (Zhu Thm 5.3.4).  Every other family is already closed in the
repo; the entry point `MUGradedAction_of_crossCFirst` (`ZhuVermaAnArchVcoreTwins`) needs **only**

  `(∀ n, CrossCFirstOnm W n)`   (`ZhuVermaAnArchMUcrossGen`),

the `c`-first family of level-`0` Zhu circles
`∑_{i≤K} C(K,i) • anmCirc W 0 0 c (a₍i−n−1₎ d) ∈ Onm W n 0` (homogeneous `a ∈ 𝒱_K`, `c ∈ 𝒱_M`,
`d ∈ 𝒱_P`).  Both the Term₂ commutator (`ARDCommTowerEq_holds`) and the Term₁ commutator
(`CrossCommOnm_holds`) are PROVEN; `MUGradedAction_of_crossCFirst` consumes them and asks only for
`CrossCFirstOnm`.

## The reduction (FULLY proven here; no `sorry`/axiom/`pbw`)

The `c`-first family is the single level-`0` circle on the right action
(`cFirstFam_eq_circ_anmRight`, `ZhuVermaAnArchMUcrossCFirst`)

  `∑_{i≤K} C(K,i) • anmCirc W 0 0 c (a₍i−n−1₎ d) = anmCirc W 0 0 c (a *^n_0 d)`,

which after peeling off the trivial level-`n` circle generator `anmCirc W n 0 c (a *^n_0 d)` (in
`Onm W n 0` for free) reduces to the pole-difference `CircDiffAnmRightOnm`
(`ZhuVermaAnArchMUcircAnmRight`).  The pole-difference splits (`circDiffAnmRight_split`,
`ZhuVermaAnArchMUcircDiffClose`) as `D = anmRightDiff + crossDiffComm`, with the convolution side
`crossDiffComm W n K M a c d ∈ Onm W n 0` **FULLY PROVEN** (`crossDiffComm_mem_Onm`,
`ZhuVermaAnArchHPoleN`, the `n`-offset absorbed by the cross-`s` regrade `crossDiff_regrade`).  So
the ENTIRE gate reduces to the single `a`-outer right-action-difference membership

  `(HARD)   anmRightDiff W n K a c d ∈ Onm W n 0`   (homogeneous `a ∈ 𝒱_K`, `c ∈ 𝒱_M`, `d ∈ 𝒱_P`).

`anmRightDiff = anmRight W n 0 a (anmCirc W 0 0 c d − anmCirc W n 0 c d)`
(`anmRightDiff_eq_anmRight`), the level-`n` right action of `a` on the (homogeneous-`c`)
base pole-difference.

## What is proved here (axiom-clean)

* **`ARDTowerDecomp`** — the precise `(HARD)` tower-decomposition predicate: `anmRightDiff` is a
  `PresTowerFam` U-family in homogeneous `c` (towers based at the modes `a₍g₎d`) plus a homogeneous
  multi-grade `MGTowerFam` W-family in the products `c₍s₎a ∈ 𝒱_{M+K−s−1}` (the FULL level-`n`
  circle-generator span).  The `a`-outer twin of the diagonal `AnmCircTowerEq` V-core
  (`ZhuVermaAnArchMUcircV`).
* **`ardiff_mem_of_decomp`** — **the membership half FULLY proven**: `ARDTowerDecomp` ⟹
  `anmRightDiff ∈ Onm W n 0`, via the keystone-backed `PresTowerFam_mem_Onm` + `MGTowerFam_mem_Onm`.
* **`HARDhom_of_decomp`** — the homogeneous-`(c, d)` `(HARD)` from the universal `ARDTowerDecomp`.
* **`CrossCFirstOnm_of_decomp`** — universal `ARDTowerDecomp` ⟹ `CrossCFirstOnm W n` (through the
  proven chain `CircDiffAnmRightOnm_of_HARDhom` ⟶ `CrossCFirstOnm_of_circDiff`).
* **`MUGradedAction_of_ARDTowerDecomp`** — **the full `MUGradedAction W` from the single universal
  `ARDTowerDecomp`** (via `MUGradedAction_of_crossCFirst`, which already discharges both commutator
  twins `ARDCommTowerEq_holds` + `CrossCommOnm_holds` and Term₂).

This CLOSES the entire `MUGradedAction` crux down to the **single** engine-verified tower
decomposition `ARDTowerDecomp` — the genuine Dong–Jiang Lemma 2.8 coefficient assignment — whose
membership is already fully discharged.  It is the `a`-outer level-`n` mirror of the proven
diagonal V-core; the only remaining content is the explicit existential witness (U-family
weights/bases in `c` and the multi-grade W-family data in `c₍s₎a`), engine-verified TRUE on the
rank-1 free boson.

## Engine status (rank-1 free boson; NOT faked)

* `certificates/mathematica/anmrightdiff_tower.wl` (re-run): `anmRightDiff ∈ (c-towers@a₍g₎d) +
  ((c₍s₎a)-towers@d)` for `n = 1, 2` and mixed homogeneous `a, c, d` (**True**); the
  `(c₍s₎a)`-towers ALONE do NOT suffice (**False**), so BOTH families are load-bearing.
* `certificates/mathematica/circ_diff_dj.wl`: the same decomposition for the full pole-difference `D`
  (**True**).
* `certificates/mathematica/diff_in_O0.wl`: `anmCirc W n 0 c d` and `Diff_d = (circ00 − circN) c d`
  lie in the level-`0` circle-generator span `Onm W 0 0` (**True**) — confirming `Diff_d` is a
  genuine `O(𝒱)`-relation carried by the level-`n` right action into `Onm W n 0`.

## References
Dong–Jiang, Math. Z. 259 (2008) 799–826 (`math/0601626`), §2 (Lemma 2.8); Frenkel–Zhu Lemma 2.1.2;
Dong–Li–Mason, J. Algebra 206 (1998) 67–96; Gannon §5.3.2, Thm 5.3.4.
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The precise `(HARD)` tower-decomposition predicate (the single remaining identity). -/

/-- **The `anmRightDiff` tower-decomposition predicate** (the precise remaining `(HARD)` identity).
For homogeneous `a ∈ 𝒱_K`, `c ∈ 𝒱_M`, `d ∈ 𝒱_P`, the `a`-outer right-action-difference family
`anmRightDiff W n K a c d` decomposes as a `PresAnm`-tower **U-family in `c`** (over grade `M`, with
arbitrary base vectors — modes of `a₍·₎d`) plus a homogeneous multi-grade **`MGTowerFam` W-family in
the products `c₍s₎a`** (per-index homogeneous left factors `leftS r ∈ 𝒱_{gradeS r}` of arbitrary
grade — the FULL level-`n` circle-generator span), based at `d`:

  `anmRightDiff W n K a c d
     = PresTowerFam W M n c RU ΔU baseU wU + MGTowerFam W n S gradeS leftS baseS ΔS wS`.

The `a`-outer level-`n` twin of the diagonal `AnmCircTowerEq` V-core (`ZhuVermaAnArchMUcircV`); the
same two homogeneous tower families as `CircDiffAnmRightTowerEq` (`ZhuVermaAnArchMUcircDiff`) and
`ARDTerm2TowerEq` (`ZhuVermaAnArchAnmRightDiff`).  Engine-verified TRUE on the rank-1 free boson
(`certificates/mathematica/anmrightdiff_tower.wl`, `n = 1, 2`). -/
def ARDTowerDecomp (W : VertexOperatorAlgebra 𝒱) (n K M P : ℕ) (a c d : 𝒱) : Prop :=
  ∃ (RU ΔU S : ℕ) (baseU : Fin RU → 𝒱) (wU : Fin RU → ℕ → ℂ)
    (gradeS : Fin S → ℕ) (leftS baseS : Fin S → 𝒱) (ΔS : Fin S → ℕ) (wS : Fin S → ℕ → ℂ),
    (∀ r : Fin S, leftS r ∈ W.grading ((gradeS r : ℤ))) ∧
    anmRightDiff W n K a c d
      = PresTowerFam W M n c RU ΔU baseU wU
        + MGTowerFam W n S gradeS leftS baseS ΔS wS

/-! ## The membership half — FULLY proven. -/

/-- **`ARDTowerDecomp` ⟹ `anmRightDiff ∈ Onm W n 0`** (homogeneous `c`).  If the `a`-outer
right-action-difference family decomposes onto the U-tower family in `c` plus the homogeneous
multi-grade tower W-family (`ARDTowerDecomp`), then `anmRightDiff W n K a c d ∈ Onm W n 0`, by the
keystone-backed `PresTowerFam_mem_Onm` (towers in the homogeneous `c`) + `MGTowerFam_mem_Onm` (the
per-index homogeneous level-`n` circle-generator span).  The membership half, FULLY proven. -/
theorem ardiff_mem_of_decomp (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {K M P : ℕ}
    {a c d : 𝒱} (hc : c ∈ W.grading (M : ℤ))
    (hdec : ARDTowerDecomp W n K M P a c d) :
    anmRightDiff W n K a c d ∈ Onm W n 0 := by
  obtain ⟨RU, ΔU, S, baseU, wU, gradeS, leftS, baseS, ΔS, wS, hhom, heq⟩ := hdec
  rw [heq]
  exact Submodule.add_mem _ (PresTowerFam_mem_Onm W n hc RU ΔU baseU wU)
    (MGTowerFam_mem_Onm W n S gradeS leftS baseS ΔS wS hhom)

/-! ## The homogeneous-`(c, d)` `(HARD)` from the universal decomposition. -/

/-- **The homogeneous-`(c, d)` `(HARD)` from the universal `ARDTowerDecomp`.**  For homogeneous
`a ∈ 𝒱_K`, `c ∈ 𝒱_M`, `d ∈ 𝒱_P`, supplying the tower decomposition `ARDTowerDecomp` (for all data)
yields `anmRightDiff W n K a c d ∈ Onm W n 0` (the precise `(HARD)` form consumed by
`CircDiffAnmRightOnm_of_HARDhom`). -/
theorem HARDhom_of_decomp (W : VertexOperatorAlgebra 𝒱) (n : ℕ)
    (Hdec : ∀ (K M P : ℕ), ∀ a ∈ W.grading (K : ℤ), ∀ c ∈ W.grading (M : ℤ),
      ∀ d ∈ W.grading (P : ℤ), ARDTowerDecomp W n K M P a c d)
    {K M P : ℕ} {a c d : 𝒱} (_ha : a ∈ W.grading (K : ℤ)) (hc : c ∈ W.grading (M : ℤ))
    (_hd : d ∈ W.grading (P : ℤ)) :
    anmRightDiff W n K a c d ∈ Onm W n 0 :=
  ardiff_mem_of_decomp W n hc (Hdec K M P a _ha c hc d _hd)

/-! ## `CrossCFirstOnm` from the universal decomposition. -/

/-- **`CrossCFirstOnm W n` from the universal `ARDTowerDecomp`.**  The homogeneous `(HARD)`
(`HARDhom_of_decomp`) discharges `CircDiffAnmRightOnm W n` (`CircDiffAnmRightOnm_of_HARDhom`,
`ZhuVermaAnArchAnmRightDiff` — the convolution side `crossDiffComm_mem_Onm` is FULLY proven), and
`CrossCFirstOnm_of_circDiff` (`ZhuVermaAnArchMUcircAnmRight`) lifts it to `CrossCFirstOnm W n`. -/
theorem CrossCFirstOnm_of_decomp (W : VertexOperatorAlgebra 𝒱) (n : ℕ)
    (Hdec : ∀ (K M P : ℕ), ∀ a ∈ W.grading (K : ℤ), ∀ c ∈ W.grading (M : ℤ),
      ∀ d ∈ W.grading (P : ℤ), ARDTowerDecomp W n K M P a c d) :
    CrossCFirstOnm W n :=
  CrossCFirstOnm_of_circDiff W n
    (CircDiffAnmRightOnm_of_HARDhom W n
      (fun K M P a ha c hc d hd => HARDhom_of_decomp W n Hdec ha hc hd))

/-! ## The full `MUGradedAction W` from the single universal decomposition. -/

/-- **The full `MUGradedAction W` assembly from the single universal `ARDTowerDecomp`.**  Given, for
every level `n`, the `a`-outer right-action-difference tower decomposition `ARDTowerDecomp` (whose
membership half is FULLY proven, `ardiff_mem_of_decomp`), the Dong–Jiang `M(U)` graded-action crux
`MUGradedAction W` holds: `CrossCFirstOnm_of_decomp` gives `∀ n, CrossCFirstOnm W n`, and
`MUGradedAction_of_crossCFirst` (`ZhuVermaAnArchVcoreTwins`) — which already discharges Term₂
(`ARDCommTowerEq_holds`) and the Term₁ commutator (`CrossCommOnm_holds`) — assembles the crux.

This CLOSES the entire `MUGradedAction` gate to the single explicit tower-decomposition existential
`ARDTowerDecomp` (the genuine Dong–Jiang Lemma 2.8 coefficient assignment, engine-verified TRUE on
the rank-1 free boson), with the membership half already fully discharged here. -/
theorem MUGradedAction_of_ARDTowerDecomp (W : VertexOperatorAlgebra 𝒱)
    (Hdec : ∀ (n K M P : ℕ), ∀ a ∈ W.grading (K : ℤ), ∀ c ∈ W.grading (M : ℤ),
      ∀ d ∈ W.grading (P : ℤ), ARDTowerDecomp W n K M P a c d) :
    MUGradedAction W :=
  MUGradedAction_of_crossCFirst W
    (fun n => CrossCFirstOnm_of_decomp W n
      (fun K M P a ha c hc d hd => Hdec n K M P a ha c hc d hd))

/-! ## Status — `MUGradedAction W` closed to ONE engine-verified tower decomposition.

Proved here (`#print axioms` = `[propext, Classical.choice, Quot.sound]`; no `sorry`/
`axiom`/`pbw`):

* **`ARDTowerDecomp`** — the precise `(HARD)` tower-decomposition predicate (the `a`-outer
  right-action-difference family as a `PresTowerFam` U-family in `c` based at `a₍g₎d` plus a
  homogeneous multi-grade `MGTowerFam` W-family in the products `c₍s₎a`).
* **`ardiff_mem_of_decomp`** — **the membership half FULLY proven**: `ARDTowerDecomp` ⟹
  `anmRightDiff ∈ Onm W n 0` (via `PresTowerFam_mem_Onm` + `MGTowerFam_mem_Onm`).
* **`HARDhom_of_decomp`** — the homogeneous `(HARD)` from the universal decomposition.
* **`CrossCFirstOnm_of_decomp`** — universal `ARDTowerDecomp` ⟹ `CrossCFirstOnm W n` (through the
  proven chain `CircDiffAnmRightOnm_of_HARDhom` ⟶ `CrossCFirstOnm_of_circDiff`; the convolution side
  `crossDiffComm_mem_Onm` is FULLY proven).
* **`MUGradedAction_of_ARDTowerDecomp`** — **the full `MUGradedAction W`** from the single universal
  `ARDTowerDecomp`, via `MUGradedAction_of_crossCFirst` (Term₂ `ARDCommTowerEq_holds` + Term₁
  `CrossCommOnm_holds` already discharged).

**The single remaining identity (engine-verified TRUE; NOT faked):** the universally-quantified
`ARDTowerDecomp W n K M P a c d` — the explicit Dong–Jiang Lemma 2.8 tower decomposition of the
`a`-outer right-action-difference family

  `anmRightDiff W n K a c d
     = (U-tower family in `c` based at `a₍g₎d`) + (multi-grade W-family in `c₍s₎a` based at `d`).

This is the `a`-outer level-`n` mirror of the FULLY-proven diagonal V-core
(`AnmCircTowerEq_holds`, `ZhuVermaAnArchMUcircV`); the `n`-offset is absorbed by the proven regrade
`crossDiff_regrade`/`regradeWt` (`ZhuVermaAnArchHPoleN`).  Engine values
(`certificates/mathematica/`): `certificates/mathematica/anmrightdiff_tower.wl` (`anmRightDiff ∈ (c-tow@a₍g₎d)+((c₍s₎a)-tow@d)`,
`n = 1, 2`, both families load-bearing); `certificates/mathematica/circ_diff_dj.wl` (the full pole-difference, same
decomposition); `certificates/mathematica/diff_in_O0.wl` (`Diff_d = (circ00 − circN) c d ∈ Onm W 0 0`).  The membership
engine is fully built (`ardiff_mem_of_decomp`); the only remaining step is the explicit existential
witness
(U/W weights and bases — the DJ Lemma 2.8 coefficients), whose membership is already discharged.
-/

end VOA

/-
`#print axioms` check (each of the following prints
`[propext, Classical.choice, Quot.sound]`, NO `pbw`, NO `sorryAx`):

  #print axioms VOA.ardiff_mem_of_decomp
  #print axioms VOA.HARDhom_of_decomp
  #print axioms VOA.CrossCFirstOnm_of_decomp
  #print axioms VOA.MUGradedAction_of_ARDTowerDecomp
-/
