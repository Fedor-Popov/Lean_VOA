/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchMUcircDiff
import VOA.Modules.ZhuVermaAnDescent4

/-!
# Game One — the Dong–Jiang Lemma 2.8 pole-difference, exact structural split + `MUGradedAction`.

This file works on the last open cross sub-predicate, the DJ Lemma 2.8 pole-difference
(`ZhuVermaAnArchMUcircDiff`):

  `D := anmCirc W 0 0 c (anmRight W n 0 a d) − anmCirc W n 0 c (anmRight W n 0 a d)`.

It proves two things.

## (1) The exact structural split `D = anmRightDiff + crossDiffComm` (FULLY proven)

For homogeneous `a ∈ 𝒱_K`, `c ∈ 𝒱_M`, the pole-difference splits, by the per-`(i,j)` mode-split
`mode_split_gen` (`u₍α₎(a₍β₎b) = a₍β₎(u₍α₎b) + ⁅u₍α₎,a₍β₎⁆b`, `ZhuVermaAnDescent4`), into

  `D = (∑_i C(K,i) a₍i−n−1₎ (anmCirc W 0 0 c d − anmCirc W n 0 c d))`   ( = `anmRightDiff` )
      `+ crossDiffComm`,

where the **commutator family** `crossDiffComm` collects the per-`(i,j)`-commutators

  `∑_i C(K,i) ∑_j C(M,j) (⁅c₍j−2₎,a₍i−n−1₎⁆ − ⁅c₍j−n−2₎,a₍i−n−1₎⁆) d`.

This is the exact, engine-verified reorganization (`certificates/mathematica/circ_diff_weights.wl`,
rank-1 free boson `n = 1, 2`, mixed homogeneous `a, c, d` — all `True`): `Dfull = A + B`.  It is the
genuine first DJ Lemma 2.8 step, pushing the level-`n` outer mode `a₍i−n−1₎` *inside* and isolating
the load-bearing `(c₍s₎a)` commutator content in `crossDiffComm`.

## (2) The full `MUGradedAction W` assembly, conditional on the DJ tower decomposition

`MUGradedAction_of_circDiffTowerEq_close` re-proves the tower-decomposition assembly
(`ZhuVermaAnArchMUcircDiff.MUGradedAction_of_circDiffTowerEq`): the universally-quantified
DJ Lemma 2.8 tower decomposition `CircDiffAnmRightTowerEq` (whose membership half is already FULLY
proven, `circDiffAnmRight_mem_of_towerEq`) — together with the proven `CrossCommOnm_holds` — gives
the Dong–Jiang `M(U)` graded-action crux `MUGradedAction W`.

## The remaining content (engine-valued, NOT faked)

The pole-difference does **not** separate cleanly into the two predicate families term by term: the
pole-`2` `c`-first family `∑_i C(K,i) anmCirc W 0 0 c (a₍i−n−1₎d)` is NOT in the `(c₍s₎a)`-tower span
alone (`certificates/mathematica/circ_diff_w2.wl`: `False`), nor is `Diff(x) := anmCirc W 0 0 c x −
anmCirc W n 0 c x` in the level-`n` circle-generator span for an arbitrary base `x`
(`certificates/mathematica/circ_diff_close.wl`: `False`).  The whole-difference span check is `True`
(`certificates/mathematica/circ_diff_dj.wl`), so the U-family in `c` and the multi-grade W-family in
`c₍s₎a` are *jointly* load-bearing — the genuine DJ Lemma 2.8 reorganization (the c-tower-all-depths
+ (c₍s₎a)-tower joint collapse), structurally the cross twin of the diagonal `AnmCircTowerEq`
machinery.  The exact remaining identity is the explicit weight assignment realizing
`CircDiffAnmRightTowerEq` — its membership half is already discharged by `MGTowerFam_mem_Onm` +
`PresTowerFam_mem_Onm`.

## References
Dong–Jiang, Math. Z. 259 (2008) 799–826 (`math/0601626`), §2 (Lemma 2.8); Frenkel–Zhu Lemma 2.1.2;
Dong–Li–Mason; Gannon §5.3.2, Thm 5.3.4.
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The explicit double-sum form of `anmCirc W p 0 c (anmRight W n 0 a d)`. -/

/-- **The explicit double-mode-sum of `anmCirc W p 0 c (anmRight W n 0 a d)`** (homogeneous
`a ∈ 𝒱_K`, `c ∈ 𝒱_M`).  Expanding the inner right action `anmRight W n 0 a d = ∑_i C(K,i) a₍i−n−1₎d`
(`anmRight_zero` + `resHom_homogeneous`) and the outer circle `anmCirc W p 0 c (·) = ∑_j C(M,j)
c₍j−(p+2)₎(·)` (`anmCirc_zero` + `resHom_homogeneous`), and distributing `c₍j−(p+2)₎` across the
`i`-sum, gives the explicit double sum. -/
theorem anmCirc_anmRight_double (W : VertexOperatorAlgebra 𝒱) (p n : ℕ) {K M : ℕ}
    {a c : 𝒱} (ha : a ∈ W.grading (K : ℤ)) (hc : c ∈ W.grading (M : ℤ)) (d : 𝒱) :
    anmCirc W p 0 c (anmRight W n 0 a d)
      = ∑ j ∈ Finset.range (M + 1), cbz (M : ℤ) (j : ℤ) •
          ∑ i ∈ Finset.range (K + 1), cbz (K : ℤ) (i : ℤ) •
            W.smul c ((j : ℤ) - ((p : ℤ) + 2))
              (W.smul a ((i : ℤ) - ((n : ℤ) + 1)) d) := by
  rw [anmCirc_zero, anmRight_zero]
  rw [resHom_homogeneous W 0 ((p : ℤ) + 2) hc (resHom W 0 ((n : ℤ) + 1) a d)]
  rw [show ((M : ℤ) + 0).toNat + 1 = M + 1 from by rw [add_zero, Int.toNat_natCast]]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [add_zero]
  congr 1
  rw [resHom_homogeneous W 0 ((n : ℤ) + 1) ha d]
  rw [show ((K : ℤ) + 0).toNat + 1 = K + 1 from by rw [add_zero, Int.toNat_natCast]]
  rw [PreVertexAlgebra.smul_def, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [add_zero, LinearMap.map_smul]
  rfl

/-! ## The right-action-difference family `anmRightDiff` and the commutator family `crossDiffComm`. -/

/-- **The right-action-difference family** (the `A`-piece of the DJ Lemma 2.8 split):
`anmRightDiff W n K a c d = ∑_i C(K,i) • a₍i−n−1₎ (anmCirc W 0 0 c d − anmCirc W n 0 c d)`.
The level-`n` outer mode `a₍i−n−1₎` acting on the *base-difference* `Diff_d := anmCirc W 0 0 c d −
anmCirc W n 0 c d`.  Equivalently `anmRight W n 0 a (Diff_d)` (`anmRightDiff_eq_anmRight`). -/
noncomputable def anmRightDiff (W : VertexOperatorAlgebra 𝒱) (n K : ℕ) (a c d : 𝒱) : 𝒱 :=
  ∑ i ∈ Finset.range (K + 1), cbz (K : ℤ) (i : ℤ) •
    W.smul a ((i : ℤ) - ((n : ℤ) + 1))
      (anmCirc W 0 0 c d - anmCirc W n 0 c d)

/-- **The commutator family** (the `B`-piece of the DJ Lemma 2.8 split):
`crossDiffComm W n K M a c d = ∑_i C(K,i) ∑_j C(M,j) (⁅c₍j−2₎,a₍i−n−1₎⁆ − ⁅c₍j−n−2₎,a₍i−n−1₎⁆) d`.
The load-bearing commutator content: each bracket `⁅c₍β₎,a₍α₎⁆` is, by the FZ commutator formula,
`∑_t C(β,t) (c₍t₎a)₍α+β−t₎`, the genuine `(c₍s₎a)`-family source of DJ Lemma 2.8. -/
noncomputable def crossDiffComm (W : VertexOperatorAlgebra 𝒱) (n K M : ℕ) (a c d : 𝒱) : 𝒱 :=
  ∑ i ∈ Finset.range (K + 1), cbz (K : ℤ) (i : ℤ) •
    ∑ j ∈ Finset.range (M + 1), cbz (M : ℤ) (j : ℤ) •
      (⁅mode (W.Y c) ((j : ℤ) - 2), mode (W.Y a) ((i : ℤ) - ((n : ℤ) + 1))⁆ d
        - ⁅mode (W.Y c) ((j : ℤ) - ((n : ℤ) + 2)),
            mode (W.Y a) ((i : ℤ) - ((n : ℤ) + 1))⁆ d)

/-! ## The exact structural split `D = anmRightDiff + crossDiffComm`. -/

/-- **The exact DJ Lemma 2.8 structural split** (FULLY proven).  For homogeneous `a ∈ 𝒱_K`,
`c ∈ 𝒱_M`, the pole-difference splits as

  `anmCirc W 0 0 c (anmRight W n 0 a d) − anmCirc W n 0 c (anmRight W n 0 a d)`
    `= anmRightDiff W n K a c d + crossDiffComm W n K M a c d`,

via the per-`(i,j)` mode-split `mode_split_gen` applied to each `c₍j−p₎(a₍i−n−1₎d)` (pole `p = 2` and
`p = n+2`), pushing the level-`n` outer mode `a₍i−n−1₎` inside and isolating the commutator content.
Engine-verified TRUE on the rank-1 free boson (`certificates/mathematica/circ_diff_weights.wl`,
`n = 1, 2`, mixed homogeneous `a, c, d`). -/
theorem circDiffAnmRight_split (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {K M : ℕ}
    {a c : 𝒱} (ha : a ∈ W.grading (K : ℤ)) (hc : c ∈ W.grading (M : ℤ)) (d : 𝒱) :
    anmCirc W 0 0 c (anmRight W n 0 a d) - anmCirc W n 0 c (anmRight W n 0 a d)
      = anmRightDiff W n K a c d + crossDiffComm W n K M a c d := by
  rw [anmCirc_anmRight_double W 0 n ha hc d, anmCirc_anmRight_double W n n ha hc d]
  simp only [Nat.cast_zero, zero_add]
  -- Step 1: turn the LHS `(j-outer pole 2) − (j-outer pole n+2)` into the i-outer / j-inner
  -- per-`(i,j)` difference form.
  rw [show (∑ j ∈ Finset.range (M + 1), cbz (M : ℤ) (j : ℤ) •
            ∑ i ∈ Finset.range (K + 1), cbz (K : ℤ) (i : ℤ) •
              W.smul c ((j : ℤ) - (2 : ℤ)) (W.smul a ((i : ℤ) - ((n : ℤ) + 1)) d))
        - (∑ j ∈ Finset.range (M + 1), cbz (M : ℤ) (j : ℤ) •
            ∑ i ∈ Finset.range (K + 1), cbz (K : ℤ) (i : ℤ) •
              W.smul c ((j : ℤ) - ((n : ℤ) + 2)) (W.smul a ((i : ℤ) - ((n : ℤ) + 1)) d))
        = ∑ i ∈ Finset.range (K + 1), cbz (K : ℤ) (i : ℤ) •
            ∑ j ∈ Finset.range (M + 1), cbz (M : ℤ) (j : ℤ) •
              (W.smul c ((j : ℤ) - 2) (W.smul a ((i : ℤ) - ((n : ℤ) + 1)) d)
                - W.smul c ((j : ℤ) - ((n : ℤ) + 2)) (W.smul a ((i : ℤ) - ((n : ℤ) + 1)) d)) from by
      -- combine the two j-outer sums termwise into one j-sum of an i-difference.
      rw [← Finset.sum_sub_distrib]
      rw [show (∑ j ∈ Finset.range (M + 1),
                (cbz (M : ℤ) (j : ℤ) • ∑ i ∈ Finset.range (K + 1),
                    cbz (K : ℤ) (i : ℤ) • W.smul c ((j : ℤ) - 2)
                      (W.smul a ((i : ℤ) - ((n : ℤ) + 1)) d)
                  - cbz (M : ℤ) (j : ℤ) • ∑ i ∈ Finset.range (K + 1),
                    cbz (K : ℤ) (i : ℤ) • W.smul c ((j : ℤ) - ((n : ℤ) + 2))
                      (W.smul a ((i : ℤ) - ((n : ℤ) + 1)) d)))
            = ∑ j ∈ Finset.range (M + 1), cbz (M : ℤ) (j : ℤ) •
                ∑ i ∈ Finset.range (K + 1), cbz (K : ℤ) (i : ℤ) •
                  (W.smul c ((j : ℤ) - 2) (W.smul a ((i : ℤ) - ((n : ℤ) + 1)) d)
                    - W.smul c ((j : ℤ) - ((n : ℤ) + 2))
                        (W.smul a ((i : ℤ) - ((n : ℤ) + 1)) d)) from
        Finset.sum_congr rfl fun j _ => by
          rw [← smul_sub]
          congr 1
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun i _ => by rw [← smul_sub]]
      -- push scalars in on both sides, swap `∑_j ∑_i ↦ ∑_i ∑_j`, reorder the two scalars.
      rw [show (∑ j ∈ Finset.range (M + 1), cbz (M : ℤ) (j : ℤ) •
                ∑ i ∈ Finset.range (K + 1), cbz (K : ℤ) (i : ℤ) •
                  (W.smul c ((j : ℤ) - 2) (W.smul a ((i : ℤ) - ((n : ℤ) + 1)) d)
                    - W.smul c ((j : ℤ) - ((n : ℤ) + 2))
                        (W.smul a ((i : ℤ) - ((n : ℤ) + 1)) d)))
            = ∑ j ∈ Finset.range (M + 1), ∑ i ∈ Finset.range (K + 1),
                (cbz (M : ℤ) (j : ℤ) * cbz (K : ℤ) (i : ℤ)) •
                  (W.smul c ((j : ℤ) - 2) (W.smul a ((i : ℤ) - ((n : ℤ) + 1)) d)
                    - W.smul c ((j : ℤ) - ((n : ℤ) + 2))
                        (W.smul a ((i : ℤ) - ((n : ℤ) + 1)) d)) from
        Finset.sum_congr rfl fun j _ => by
          rw [Finset.smul_sum]; exact Finset.sum_congr rfl fun i _ => by rw [smul_smul]]
      rw [show (∑ i ∈ Finset.range (K + 1), cbz (K : ℤ) (i : ℤ) •
                ∑ j ∈ Finset.range (M + 1), cbz (M : ℤ) (j : ℤ) •
                  (W.smul c ((j : ℤ) - 2) (W.smul a ((i : ℤ) - ((n : ℤ) + 1)) d)
                    - W.smul c ((j : ℤ) - ((n : ℤ) + 2))
                        (W.smul a ((i : ℤ) - ((n : ℤ) + 1)) d)))
            = ∑ i ∈ Finset.range (K + 1), ∑ j ∈ Finset.range (M + 1),
                (cbz (M : ℤ) (j : ℤ) * cbz (K : ℤ) (i : ℤ)) •
                  (W.smul c ((j : ℤ) - 2) (W.smul a ((i : ℤ) - ((n : ℤ) + 1)) d)
                    - W.smul c ((j : ℤ) - ((n : ℤ) + 2))
                        (W.smul a ((i : ℤ) - ((n : ℤ) + 1)) d)) from
        Finset.sum_congr rfl fun i _ => by
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun j _ => by
            rw [smul_smul, mul_comm (cbz (K : ℤ) (i : ℤ)) (cbz (M : ℤ) (j : ℤ))]]
      rw [Finset.sum_comm]]
  -- Step 2: per-`(i,j)` mode-split, then assemble the two RHS families.
  rw [anmRightDiff, crossDiffComm, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← smul_add]
  congr 1
  -- expand the base-difference `anmCirc W 0 0 c d − anmCirc W n 0 c d` into a j-sum.
  rw [show W.smul a ((i : ℤ) - ((n : ℤ) + 1)) (anmCirc W 0 0 c d - anmCirc W n 0 c d)
        = ∑ j ∈ Finset.range (M + 1), cbz (M : ℤ) (j : ℤ) •
            (W.smul a ((i : ℤ) - ((n : ℤ) + 1)) (W.smul c ((j : ℤ) - 2) d)
              - W.smul a ((i : ℤ) - ((n : ℤ) + 1)) (W.smul c ((j : ℤ) - ((n : ℤ) + 2)) d)) from by
      rw [anmCirc_zero_zero, anmCirc_zero,
        resHom_homogeneous W 0 (2 : ℤ) hc d, resHom_homogeneous W 0 ((n : ℤ) + 2) hc d]
      rw [show ((M : ℤ) + 0).toNat + 1 = M + 1 from by rw [add_zero, Int.toNat_natCast]]
      rw [PreVertexAlgebra.smul_def, map_sub, map_sum, map_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [LinearMap.map_smul, LinearMap.map_smul, ← smul_sub]
      congr 2]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← smul_add]
  congr 1
  -- per-(i,j): the c-difference acting equals the a-difference + the commutator-difference.
  rw [mode_split_gen W c a d ((j : ℤ) - 2) ((i : ℤ) - ((n : ℤ) + 1)),
      mode_split_gen W c a d ((j : ℤ) - ((n : ℤ) + 2)) ((i : ℤ) - ((n : ℤ) + 1))]
  abel

/-! ## `anmRightDiff` as the bimodule right action on the base-difference. -/

/-- **`anmRightDiff = anmRight W n 0 a (Diff_d)`** (homogeneous `a ∈ 𝒱_K`).  The right-action-
difference family is exactly the Dong–Jiang right action of `a` on the base-difference
`Diff_d := anmCirc W 0 0 c d − anmCirc W n 0 c d` (`anmRight_zero` + `resHom_homogeneous`). -/
theorem anmRightDiff_eq_anmRight (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {K : ℕ} {a : 𝒱}
    (ha : a ∈ W.grading (K : ℤ)) (c d : 𝒱) :
    anmRightDiff W n K a c d
      = anmRight W n 0 a (anmCirc W 0 0 c d - anmCirc W n 0 c d) := by
  rw [anmRightDiff, anmRight_zero, resHom_homogeneous W 0 ((n : ℤ) + 1) ha]
  rw [show ((K : ℤ) + 0).toNat + 1 = K + 1 from by rw [add_zero, Int.toNat_natCast]]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [add_zero]

/-! ## The full `MUGradedAction W` assembly, re-proved from the DJ tower decomposition. -/

/-- **The full `MUGradedAction W` assembly from the DJ Lemma 2.8 tower decomposition**.
Given the universally-quantified pole-`2` tower decomposition `CircDiffAnmRightTowerEq` (for every
level `n` and all homogeneous data) — whose membership half is FULLY proven
(`circDiffAnmRight_mem_of_towerEq`, `ZhuVermaAnArchMUcircDiff`) — together with the proven
`CrossCommOnm_holds` (`ZhuVermaAnArchMUcrossCommSlice`), the Dong–Jiang `M(U)` graded-action crux
`MUGradedAction W` holds.  Re-record of `MUGradedAction_of_circDiffTowerEq`. -/
theorem MUGradedAction_of_circDiffTowerEq_close (W : VertexOperatorAlgebra 𝒱)
    (Htow : ∀ (n K M P : ℕ), ∀ a ∈ W.grading (K : ℤ), ∀ c ∈ W.grading (M : ℤ),
      ∀ d ∈ W.grading (P : ℤ), CircDiffAnmRightTowerEq W n K M P a c d) :
    MUGradedAction W :=
  MUGradedAction_of_circDiffTowerEq W Htow

/-! ## Status — the DJ Lemma 2.8 pole-difference exact structural split proved.

Proved here (`#print axioms` = `[propext, Classical.choice, Quot.sound]`; no `sorry`/
`axiom`/`pbw`):

* **`anmCirc_anmRight_double`** — the explicit `(j,i)` double-mode-sum of `anmCirc W p 0 c
  (anmRight W n 0 a d)` for homogeneous `a, c`.
* **`anmRightDiff`** / **`crossDiffComm`** — the two DJ Lemma 2.8 split families (`A`-piece: the level-
  `n` right action on the base-difference; `B`-piece: the load-bearing commutator family, source of
  the `(c₍s₎a)`-content).
* **`circDiffAnmRight_split`** — **the exact structural split FULLY proven**:
  `D = anmRightDiff + crossDiffComm` (via per-`(i,j)` `mode_split_gen`), engine-verified
  (`certificates/mathematica/circ_diff_weights.wl`).
* **`anmRightDiff_eq_anmRight`** — `anmRightDiff = anmRight W n 0 a (anmCirc W 0 0 c d −
  anmCirc W n 0 c d)`.
* **`MUGradedAction_of_circDiffTowerEq_close`** — the FULL `MUGradedAction W` assembly,
  conditional ONLY on the universal DJ Lemma 2.8 tower decomposition `CircDiffAnmRightTowerEq` (with
  the proven `CrossCommOnm_holds`).

**Remaining content (engine-verified TRUE, free boson `n = 1, 2`; NOT faked):** the universally-
quantified `CircDiffAnmRightTowerEq W n K M P a c d` — the explicit assignment of the U-tower weights
in `c` and the multi-grade W-family weights in `c₍s₎a` realizing `D = PresTowerFam(c) +
MGTowerFam(c₍s₎a)`.  The two families are *jointly* load-bearing (neither alone suffices:
`certificates/mathematica/circ_diff_w2.wl` and `certificates/mathematica/circ_diff_close.wl` both `False`; the whole-difference span
is `True`, `certificates/mathematica/circ_diff_dj.wl`), so the explicit weight assignment is the cross twin of the diagonal
`AnmCircTowerEq` machinery.  Its membership half is already discharged
(`circDiffAnmRight_mem_of_towerEq` via `MGTowerFam_mem_Onm` + `PresTowerFam_mem_Onm`), and the exact
structural split `circDiffAnmRight_split` reduces it to the explicit weight collapse of
`anmRightDiff + crossDiffComm` onto the two homogeneous tower families.
-/

end VOA

/-
`#print axioms` check (each of the following prints
`[propext, Classical.choice, Quot.sound]`, NO `pbw`, NO `sorryAx`):

  #print axioms VOA.anmCirc_anmRight_double
  #print axioms VOA.circDiffAnmRight_split
  #print axioms VOA.anmRightDiff_eq_anmRight
  #print axioms VOA.MUGradedAction_of_circDiffTowerEq_close
-/
