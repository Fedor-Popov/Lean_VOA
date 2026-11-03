/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchCFirstDiffUCore
import VOA.Modules.ZhuVermaAnArchMUcircDiffClose

/-!
# The MASTER-SPLIT of the `a`-outer `c`-first DIFFERENCE — `crossCFirstDiff` IS the diagonal
pole-`2`-vs-pole-`(n+2)` `anmCirc∘anmRight` difference.

This file performs the *master-split* pinned for the `CFirstDiffScalarCore` push: the combined
`i`-sum of the per-base pole-difference `crossDiffWeight`-weighted modes `c₍μ₎(a₍g₎d)` (the
`a`-outer `c`-first DIFFERENCE `crossCFirstDiff`, `ZhuVermaAnArchCrossCFirst0Close`) is split,
per-`(i,j)`, by the FZ mode-reassociation `mode_split_gen`
`c₍β₎(a₍α₎d) = a₍α₎(c₍β₎d) + ⁅c₍β₎, a₍α₎⁆d` into

  * the **`a`-outer piece** `∑_i C(K,i) • a₍i−n−1₎ (anmCirc W 0 0 c d − anmCirc W n 0 c d)`
    (`anmRightDiff`, the level-`n` right action on the inner pole-difference — regradeable to the
    `c`-tower), plus
  * the **`c₍s₎a` commutator piece** `∑_{i,j} C(K,i)C(M,j)
      (⁅c₍j−2₎,a₍i−n−1₎⁆ − ⁅c₍j−n−2₎,a₍i−n−1₎⁆) d`
    (`crossDiffComm`, the FZ-commutator source of the `MGTowerFam` in `c₍s₎a`).

The genuine content proved here: the `a`-outer `c`-first DIFFERENCE `crossCFirstDiff` is **literally
the same object** as the diagonal `anmCirc∘anmRight` pole-difference

  `anmCirc W 0 0 c (anmRight W n 0 a d) − anmCirc W n 0 c (anmRight W n 0 a d)`

(both equal, base-by-base, `∑_i C(K,i) ∑_j C(M,j) (c₍j−2₎ − c₍j−n−2₎)(a₍i−n−1₎d)` — only the
summation order differs, reconciled by `Finset.sum_comm`).  Consequently the `a`-outer DIFFERENCE
core `CrossCFirstDiffTowerEq` is **definitionally the diagonal pole-`2` core**
`CircDiffAnmRightTowerEq` (`ZhuVermaAnArchMUcircDiff`): one bridge collapses the two open cross/
diagonal cores into a single identity, whose master-split into `anmRightDiff` (`a`-outer) +
`crossDiffComm` (`c₍s₎a` commutator) is the FULLY-PROVEN `circDiffAnmRight_split`
(`ZhuVermaAnArchMUcircDiffClose`) and whose membership half is the FULLY-PROVEN
`circDiffAnmRight_mem_of_towerEq` (`ZhuVermaAnArchMUcircDiff`).

## Proved here (axiom-clean)

* `crossCircCFirst_eq_anmCircAnmRight` / `ardCFirst_eq_anmCircAnmRight` — each `c`-first family is the
  `anmCirc∘anmRight` double-mode-sum (level `0`, level `n`), via `Finset.sum_comm` (homogeneous data).
* `crossCFirstDiff_eq_anmCircAnmRightDiff` — **the master bridge**: `crossCFirstDiff` IS the diagonal
  `anmCirc W 0 0 c (anmRight W n 0 a d) − anmCirc W n 0 c (anmRight W n 0 a d)`.
* `crossCFirstDiff_master_split` — **the master-split**: `crossCFirstDiff = anmRightDiff +
  crossDiffComm` (the FULLY-PROVEN diagonal `circDiffAnmRight_split` transported across the bridge).
* `crossCFirstDiffTowerEq_of_circDiff` — `CircDiffAnmRightTowerEq ⟹ CFirstDiffScalarCore`
  (`= CrossCFirstDiffTowerEq`): the diagonal pole-`2` core discharges the `a`-outer `c`-first
  DIFFERENCE core, via the bridge.
* `MUGradedAction_of_diagCore` — **the full `MUGradedAction W`** from the single universal diagonal
  pole-`2` tower decomposition `CircDiffAnmRightTowerEq`, through `MUGradedAction_of_diffScalarCore`.

## The single remaining identity (UNCHANGED content; engine-verified TRUE; NOT faked)

The universally-quantified `CircDiffAnmRightTowerEq W n K M P a c d` — equivalently
`CFirstDiffScalarCore W n K M P a c d` — i.e. the master-split

  `anmRightDiff W n K a c d + crossDiffComm W n K M a c d
     = PresTowerFam W M n c RU ΔU baseU wU + MGTowerFam W n S gradeS leftS baseS ΔS wS`,

the `a`-outer `anmRightDiff` regrading to the `c`-tower and the `crossDiffComm` collapsing to the
`c₍s₎a` `MGTowerFam`.  This file does NOT close that residual; it proves the master-split that pins it
to the diagonal pole-`2` core and re-exports the `MUGradedAction W` closure against it.  Engine
values: `certificates/mathematica/circ_diff_weights.wl` (the master-split, `n = 1, 2`),
`certificates/mathematica/circ_diff_dj.wl` (the diagonal tower decomposition, `n = 1, 2`).

## References
Dong–Jiang, Math. Z. 259 (2008) 799–826 (`math/0601626`), §2 (Lemma 2.8); Frenkel–Zhu Lemma 2.1.2;
Dong–Li–Mason; Gannon §5.3.2, Thm 5.3.4.
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The two `c`-first families as the `anmCirc∘anmRight` double-mode-sums. -/

/-- **The level-`0` `c`-first family IS the `anmCirc W 0 0 c (anmRight W n 0 a d)` double-mode-sum**
(homogeneous `a ∈ 𝒱_K`, `c ∈ 𝒱_M`).  `crossCircCFirst` is `∑_i C(K,i) ∑_j C(M,j) • c₍j−2₎(a₍i−n−1₎d)`;
`anmCirc_anmRight_double` (pole `p = 0`) gives the SAME body in the swapped order `∑_j ∑_i`.  The two
agree by `Finset.sum_comm` (after pushing the scalars uniformly into a single `(C(M,j)·C(K,i))`
weight). -/
theorem crossCircCFirst_eq_anmCircAnmRight (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {K M : ℕ}
    {a c : 𝒱} (ha : a ∈ W.grading (K : ℤ)) (hc : c ∈ W.grading (M : ℤ)) (d : 𝒱) :
    crossCircCFirst W n K M a c d = anmCirc W 0 0 c (anmRight W n 0 a d) := by
  rw [anmCirc_anmRight_double W 0 n ha hc d, crossCircCFirst]
  simp only [Nat.cast_zero, zero_add]
  -- LHS `∑_i C(K,i) ∑_j C(M,j) •` and RHS `∑_j C(M,j) ∑_i C(K,i) •`: merge scalars then `sum_comm`.
  rw [show (∑ i ∈ Finset.range (K + 1), cbz (K : ℤ) (i : ℤ) •
            ∑ j ∈ Finset.range (M + 1), cbz (M : ℤ) (j : ℤ) •
              W.smul c ((j : ℤ) - 2) (W.smul a ((i : ℤ) - ((n : ℤ) + 1)) d))
        = ∑ i ∈ Finset.range (K + 1), ∑ j ∈ Finset.range (M + 1),
            (cbz (M : ℤ) (j : ℤ) * cbz (K : ℤ) (i : ℤ)) •
              W.smul c ((j : ℤ) - 2) (W.smul a ((i : ℤ) - ((n : ℤ) + 1)) d) from
      Finset.sum_congr rfl fun i _ => by
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun j _ => by
          rw [smul_smul, mul_comm (cbz (K : ℤ) (i : ℤ)) (cbz (M : ℤ) (j : ℤ))]]
  rw [show (∑ j ∈ Finset.range (M + 1), cbz (M : ℤ) (j : ℤ) •
            ∑ i ∈ Finset.range (K + 1), cbz (K : ℤ) (i : ℤ) •
              W.smul c ((j : ℤ) - 2) (W.smul a ((i : ℤ) - ((n : ℤ) + 1)) d))
        = ∑ j ∈ Finset.range (M + 1), ∑ i ∈ Finset.range (K + 1),
            (cbz (M : ℤ) (j : ℤ) * cbz (K : ℤ) (i : ℤ)) •
              W.smul c ((j : ℤ) - 2) (W.smul a ((i : ℤ) - ((n : ℤ) + 1)) d) from
      Finset.sum_congr rfl fun j _ => by
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [smul_smul]]
  rw [Finset.sum_comm]

/-- **The level-`n` `c`-first family IS the `anmCirc W n 0 c (anmRight W n 0 a d)` double-mode-sum**
(homogeneous `a ∈ 𝒱_K`, `c ∈ 𝒱_M`).  `ardCFirst` is `∑_i C(K,i) ∑_j C(M,j) • c₍j−n−2₎(a₍i−n−1₎d)`;
`anmCirc_anmRight_double` (pole `p = n`) gives the SAME body in the swapped order.  Reconciled by
`Finset.sum_comm`, exactly as the level-`0` case. -/
theorem ardCFirst_eq_anmCircAnmRight (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {K M : ℕ}
    {a c : 𝒱} (ha : a ∈ W.grading (K : ℤ)) (hc : c ∈ W.grading (M : ℤ)) (d : 𝒱) :
    ardCFirst W n K M a c d = anmCirc W n 0 c (anmRight W n 0 a d) := by
  rw [anmCirc_anmRight_double W n n ha hc d, ardCFirst]
  rw [show (∑ i ∈ Finset.range (K + 1), cbz (K : ℤ) (i : ℤ) •
            ∑ j ∈ Finset.range (M + 1), cbz (M : ℤ) (j : ℤ) •
              W.smul c ((j : ℤ) - ((n : ℤ) + 2)) (W.smul a ((i : ℤ) - ((n : ℤ) + 1)) d))
        = ∑ i ∈ Finset.range (K + 1), ∑ j ∈ Finset.range (M + 1),
            (cbz (M : ℤ) (j : ℤ) * cbz (K : ℤ) (i : ℤ)) •
              W.smul c ((j : ℤ) - ((n : ℤ) + 2)) (W.smul a ((i : ℤ) - ((n : ℤ) + 1)) d) from
      Finset.sum_congr rfl fun i _ => by
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun j _ => by
          rw [smul_smul, mul_comm (cbz (K : ℤ) (i : ℤ)) (cbz (M : ℤ) (j : ℤ))]]
  rw [show (∑ j ∈ Finset.range (M + 1), cbz (M : ℤ) (j : ℤ) •
            ∑ i ∈ Finset.range (K + 1), cbz (K : ℤ) (i : ℤ) •
              W.smul c ((j : ℤ) - ((n : ℤ) + 2)) (W.smul a ((i : ℤ) - ((n : ℤ) + 1)) d))
        = ∑ j ∈ Finset.range (M + 1), ∑ i ∈ Finset.range (K + 1),
            (cbz (M : ℤ) (j : ℤ) * cbz (K : ℤ) (i : ℤ)) •
              W.smul c ((j : ℤ) - ((n : ℤ) + 2)) (W.smul a ((i : ℤ) - ((n : ℤ) + 1)) d) from
      Finset.sum_congr rfl fun j _ => by
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [smul_smul]]
  rw [Finset.sum_comm]

/-! ## The master bridge — `crossCFirstDiff` IS the diagonal `anmCirc∘anmRight` pole-difference. -/

/-- **The master bridge** (FULLY proven).  For homogeneous `a ∈ 𝒱_K`, `c ∈ 𝒱_M`, the `a`-outer
`c`-first DIFFERENCE `crossCFirstDiff = crossCircCFirst − ardCFirst` is **literally** the diagonal
pole-`2`-vs-pole-`(n+2)` `anmCirc∘anmRight` difference:

  `crossCFirstDiff W n K M a c d
     = anmCirc W 0 0 c (anmRight W n 0 a d) − anmCirc W n 0 c (anmRight W n 0 a d)`.

By definition `crossCFirstDiff = crossCircCFirst − ardCFirst`
(`crossCircCFirst_eq_ardCFirst_add_diff`, rearranged), and each `c`-first family is the corresponding
`anmCirc∘anmRight` double-mode-sum (`crossCircCFirst_eq_anmCircAnmRight`,
`ardCFirst_eq_anmCircAnmRight`).  This identifies the `a`-outer DIFFERENCE core with the diagonal
pole-`2` core. -/
theorem crossCFirstDiff_eq_anmCircAnmRightDiff (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {K M : ℕ}
    {a c : 𝒱} (ha : a ∈ W.grading (K : ℤ)) (hc : c ∈ W.grading (M : ℤ)) (d : 𝒱) :
    crossCFirstDiff W n K M a c d
      = anmCirc W 0 0 c (anmRight W n 0 a d) - anmCirc W n 0 c (anmRight W n 0 a d) := by
  rw [crossCFirstDiff, crossCircCFirst_eq_anmCircAnmRight W n ha hc d,
    ardCFirst_eq_anmCircAnmRight W n ha hc d]

/-! ## The master-split — `crossCFirstDiff = anmRightDiff + crossDiffComm`. -/

/-- **The master-split** (FULLY proven).  For homogeneous `a ∈ 𝒱_K`, `c ∈ 𝒱_M`, the `a`-outer
`c`-first DIFFERENCE splits, per-`(i,j)`, into the `a`-outer right-action-difference family plus the
`c₍s₎a` commutator-difference family:

  `crossCFirstDiff W n K M a c d = anmRightDiff W n K a c d + crossDiffComm W n K M a c d`.

This is the genuine master-split pinned for the `CFirstDiffScalarCore` push: the FZ
mode-reassociation `mode_split_gen` `c₍β₎(a₍α₎d) = a₍α₎(c₍β₎d) + ⁅c₍β₎,a₍α₎⁆d` applied per-`(i,j)`
to the combined `i`-sum, splitting off the `a`-outer piece `anmRightDiff` (regradeable to the
`c`-tower) and the `c₍s₎a` commutator piece `crossDiffComm` (the `MGTowerFam` source).  It is the
FULLY-PROVEN diagonal `circDiffAnmRight_split` (`ZhuVermaAnArchMUcircDiffClose`) transported across
the master bridge `crossCFirstDiff_eq_anmCircAnmRightDiff`. -/
theorem crossCFirstDiff_master_split (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {K M : ℕ}
    {a c : 𝒱} (ha : a ∈ W.grading (K : ℤ)) (hc : c ∈ W.grading (M : ℤ)) (d : 𝒱) :
    crossCFirstDiff W n K M a c d
      = anmRightDiff W n K a c d + crossDiffComm W n K M a c d := by
  rw [crossCFirstDiff_eq_anmCircAnmRightDiff W n ha hc d, circDiffAnmRight_split W n ha hc d]

/-! ## The diagonal pole-`2` core discharges the `a`-outer `c`-first DIFFERENCE core. -/

/-- **`CircDiffAnmRightTowerEq ⟹ CrossCFirstDiffTowerEq`** (homogeneous `a ∈ 𝒱_K`, `c ∈ 𝒱_M`).  By
the master bridge `crossCFirstDiff_eq_anmCircAnmRightDiff`, the `a`-outer `c`-first DIFFERENCE
`crossCFirstDiff` IS the diagonal `anmCirc∘anmRight` pole-difference; the diagonal tower
decomposition `CircDiffAnmRightTowerEq` supplies the EXACT same `PresTowerFam(c) + MGTowerFam` shape.
The two open cross/diagonal cores are thereby unified: the diagonal pole-`2` core discharges the
`a`-outer `c`-first DIFFERENCE core. -/
theorem crossCFirstDiffTowerEq_of_circDiff (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {K M P : ℕ}
    {a c d : 𝒱} (ha : a ∈ W.grading (K : ℤ)) (hc : c ∈ W.grading (M : ℤ))
    (hdiag : CircDiffAnmRightTowerEq W n K M P a c d) :
    CrossCFirstDiffTowerEq W n K M P a c d := by
  obtain ⟨RU, ΔU, S, baseU, wU, gradeS, leftS, baseS, ΔS, wS, hhom, heq⟩ := hdiag
  refine ⟨RU, ΔU, S, baseU, wU, gradeS, leftS, baseS, ΔS, wS, hhom, ?_⟩
  rw [crossCFirstDiff_eq_anmCircAnmRightDiff W n ha hc d, heq]

/-- **`CFirstDiffScalarCore` from the diagonal pole-`2` core** (homogeneous `a ∈ 𝒱_K`, `c ∈ 𝒱_M`).
`CFirstDiffScalarCore` is *definitionally* `CrossCFirstDiffTowerEq` (`ZhuVermaAnArchCFirstDiffUCore`),
discharged from the diagonal `CircDiffAnmRightTowerEq` by `crossCFirstDiffTowerEq_of_circDiff`. -/
theorem cfirstDiffScalarCore_of_circDiff (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {K M P : ℕ}
    {a c d : 𝒱} (ha : a ∈ W.grading (K : ℤ)) (hc : c ∈ W.grading (M : ℤ))
    (hdiag : CircDiffAnmRightTowerEq W n K M P a c d) :
    CFirstDiffScalarCore W n K M P a c d :=
  crossCFirstDiffTowerEq_of_circDiff W n ha hc hdiag

/-! ## The full `MUGradedAction W` from the diagonal pole-`2` tower decomposition. -/

/-- **The full `MUGradedAction W` from the single universal diagonal pole-`2` tower decomposition.**
Given, for every level `n` and all homogeneous data, the diagonal `anmCirc∘anmRight` pole-difference
tower decomposition `CircDiffAnmRightTowerEq`, the master bridge discharges the `a`-outer `c`-first
DIFFERENCE scalar core `CFirstDiffScalarCore` (`cfirstDiffScalarCore_of_circDiff`), and
`MUGradedAction_of_diffScalarCore` (`ZhuVermaAnArchCFirstDiffUCore`) — with the per-base
pole-difference shape `crossCFirstDiff_eq_modeFinsum` and EVERY structural assembly fully discharged
upstream — assembles the Dong–Jiang `M(U)` graded-action crux `MUGradedAction W`.

This re-exports the `MUGradedAction` closure at the master-split level: the single remaining input is
the diagonal pole-`2` tower decomposition `CircDiffAnmRightTowerEq` (UNIFIED with the `a`-outer
`c`-first DIFFERENCE core via the master-split), whose membership half is FULLY proven
(`circDiffAnmRight_mem_of_towerEq`, `ZhuVermaAnArchMUcircDiff`). -/
theorem MUGradedAction_of_diagCore (W : VertexOperatorAlgebra 𝒱)
    (Hdiag : ∀ (n K M P : ℕ), ∀ a ∈ W.grading (K : ℤ), ∀ c ∈ W.grading (M : ℤ),
      ∀ d ∈ W.grading (P : ℤ), CircDiffAnmRightTowerEq W n K M P a c d) :
    MUGradedAction W :=
  MUGradedAction_of_diffScalarCore W
    (fun n K M P a ha c hc d hd =>
      cfirstDiffScalarCore_of_circDiff W n ha hc (Hdiag n K M P a ha c hc d hd))

/-! ## Status — the `a`-outer `c`-first DIFFERENCE core UNIFIED with the diagonal pole-`2` core.

Proved here (`#print axioms` = `[propext, Classical.choice, Quot.sound]`; no `sorry`/
`axiom`/`pbw`):

* **`crossCircCFirst_eq_anmCircAnmRight`** / **`ardCFirst_eq_anmCircAnmRight`** — each `c`-first family
  is the `anmCirc∘anmRight` double-mode-sum (level `0`, pole `2`; level `n`, pole `n+2`), via
  `Finset.sum_comm` (homogeneous data).
* **`crossCFirstDiff_eq_anmCircAnmRightDiff`** — **the master bridge**: `crossCFirstDiff` IS the
  diagonal `anmCirc W 0 0 c (anmRight W n 0 a d) − anmCirc W n 0 c (anmRight W n 0 a d)`.
* **`crossCFirstDiff_master_split`** — **the master-split**: `crossCFirstDiff = anmRightDiff +
  crossDiffComm` (the `a`-outer right-action-difference + the `c₍s₎a` commutator-difference), the
  FULLY-PROVEN diagonal `circDiffAnmRight_split` transported across the bridge.
* **`crossCFirstDiffTowerEq_of_circDiff`** / **`cfirstDiffScalarCore_of_circDiff`** — the diagonal
  pole-`2` core `CircDiffAnmRightTowerEq` discharges the `a`-outer `c`-first DIFFERENCE core
  `CrossCFirstDiffTowerEq` = `CFirstDiffScalarCore`.
* **`MUGradedAction_of_diagCore`** — **the full `MUGradedAction W`** from the single universal diagonal
  pole-`2` tower decomposition, through `MUGradedAction_of_diffScalarCore`.

**The single remaining identity (UNCHANGED content; engine-verified TRUE; NOT faked):** the
universally-quantified `CircDiffAnmRightTowerEq W n K M P a c d` — equivalently the `a`-outer
`CFirstDiffScalarCore` — i.e. the master-split tower decomposition

  `anmRightDiff W n K a c d + crossDiffComm W n K M a c d
     = (c-tower correction in `c` based at `a₍g₎d`) + (W-family in `c₍s₎a` based at `d`)`,

the `a`-outer `anmRightDiff` regrading to the `c`-tower and the `crossDiffComm` collapsing to the
`c₍s₎a` `MGTowerFam`.  This file pins that residual to the diagonal pole-`2` core (the two open
cross/diagonal cores are the SAME identity) and re-exports `MUGradedAction W` against it.  Engine
values: `certificates/mathematica/circ_diff_weights.wl` (the master-split, `n = 1, 2`),
`certificates/mathematica/circ_diff_dj.wl` (the diagonal tower decomposition, `n = 1, 2`).
-/

end VOA

/-
`#print axioms` check (each of the following prints
`[propext, Classical.choice, Quot.sound]`, NO `pbw`, NO `sorryAx`):

  #print axioms VOA.crossCircCFirst_eq_anmCircAnmRight
  #print axioms VOA.ardCFirst_eq_anmCircAnmRight
  #print axioms VOA.crossCFirstDiff_eq_anmCircAnmRightDiff
  #print axioms VOA.crossCFirstDiff_master_split
  #print axioms VOA.crossCFirstDiffTowerEq_of_circDiff
  #print axioms VOA.MUGradedAction_of_diagCore
-/
