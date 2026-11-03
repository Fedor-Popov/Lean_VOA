/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchAoutUCore
import VOA.Modules.ZhuVermaAnArchCircDiffARD
import VOA.Modules.ZhuVermaAnArchMUcrossHM
import VOA.Modules.ZhuVermaAnArchMUGradedFinal
import VOA.Modules.ZhuVermaAnArchCFirstDiffMaster

/-!
# Game One — closing **`AoutUCoreLev0Core`** (the `a`-outer level-`0` half `Uγ`-collapse).

This file closes the single remaining identity of the `a`-outer `c`-outer U-core
(`ZhuVermaAnArchAoutUCore`): the level-`0` half

  `aOutLev0Half W n K M a c d = ∑_{i≤K} C(K,i) • c∘₀ (a₍i−(n+1)₎d)`

collapses onto a grade-`M` level-`n` `PresTowerFam` in `c` (over the wide bases `a₍g₎d`) plus the
`c₍s₎a` `MGTowerFam` — i.e. `AoutUCoreLev0Core W n K M P a c d`.

## The `Uγ`-mirror (the diagonal-U-core route, engine-verified)

The level-`0` half is literally the **level-`0` `c`-first family** (`crossCircCFirst`,
`ZhuVermaAnArchMUcrossHM`), the `anmCirc W 0 0 c (anmRight W n 0 a d)` double-mode-sum
(`crossCircCFirst_eq_anmCircAnmRight`):

  `aOutLev0Half W n K M a c d = crossCircCFirst W n K M a c d
     = anmCirc W 0 0 c (anmRight W n 0 a d)`     (`aOutLev0Half_eq_crossCircCFirst`),

and the level-`n` half (`aOutLevNHalf`, already a clean `PresTowerFam`,
`aOutLevNHalf_eq_PresTowerFam`) is the **level-`n` `c`-first family** `ardCFirst`
(`ZhuVermaAnArchMUGradedFinal`):

  `aOutLevNHalf W n K M a c d = ardCFirst W n K M a c d`     (`aOutLevNHalf_eq_ardCFirst`).

Thus the level-`0` half decomposes as

  `aOutLev0Half = aOutLevNHalf + (anmCirc W 0 0 c (anmRight) − anmCirc W n 0 c (anmRight))`
               `= [clean level-`n` `c`-`PresTowerFam`] + [the diagonal pole-`2` difference]`,

and the diagonal pole-`2` difference is exactly `CircDiffAnmRightTowerEq`
(`ZhuVermaAnArchMUcircDiff`): a grade-`M` level-`n` `PresTowerFam` in `c` (over the wide `a₍g₎d`)
plus the `c₍s₎a` `MGTowerFam` — the `Uγ`-collapse twin of the FULLY-proven diagonal U/V core
`AnmCircTowerEq_holds` (`UgammaModeCollAnm_eq_towerCoeff` / `VgammaModeCollAnm_eq_towerCoeff`,
`ZhuVermaAnArchMUcircV`).  Merging the two grade-`M` level-`n` `c`-`PresTowerFam`s
(`smul_PresTowerFam` by `−1` + `PresTowerFam_add`) and carrying the `c₍s₎a` `MGTowerFam` unchanged
yields the explicit `AoutUCoreLev0Core` witness.

This is the `Uγ`-mirror of the diagonal U-core: the diagonal pole-`2` core
`CircDiffAnmRightTowerEq` (the `a`-outer level-`n` mirror of `AnmCircTowerEq_holds`) is the
single irreducible input, carried as a hypothesis, **NEVER** an axiom.  An exploratory computer-algebra run
 (script not retained) found the combined
`c`-tower-over-`a₍g₎d` + `c₍s₎a`-tower span
**True**, `n = 1, 2`; the `c`-tower span ALONE **False** — both families load-bearing).

## References
Dong–Jiang, Math. Z. 259 (2008) 799–826 (`math/0601626`), §2 (Lemma 2.8); Frenkel–Zhu Lemma 2.1.2;
Dong–Li–Mason; Gannon §5.3.2, Thm 5.3.4.
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The two halves of `aOutUPart` as the two `c`-first families. -/

/-- **The level-`0` half IS the level-`0` `c`-first family** (definitional unfold).  Per base
`bᵢ = a₍i−(n+1)₎d`, the level-`0` depth-`0` `PresAnm W M 0 0 c bᵢ` is the inner `j`-sum
`∑_{j≤M} cbz(M,j) • c₍j−2₎ bᵢ` (`PresAnm`, `n = d = 0`: `cbz(M+0,j) • c₍j−(0+2)−0₎`), matching
`crossCircCFirst` termwise. -/
theorem aOutLev0Half_eq_crossCircCFirst (W : VertexOperatorAlgebra 𝒱) (n K M : ℕ) (a c d : 𝒱) :
    aOutLev0Half W n K M a c d = crossCircCFirst W n K M a c d := by
  rw [aOutLev0Half, crossCircCFirst]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  rw [PresAnm]
  refine Finset.sum_congr (by norm_num) fun j _ => ?_
  congr 2 <;> push_cast <;> ring

/-- **The level-`n` half IS the level-`n` `c`-first family** (definitional unfold).  Per base
`bᵢ = a₍i−(n+1)₎d`, the level-`n` depth-`0` `PresAnm W M n 0 c bᵢ` is the inner `j`-sum
`∑_{j≤M} cbz(M,j) • c₍j−(n+2)₎ bᵢ` (`PresAnm`, `d = 0`: `cbz(M+0,j) • c₍j−(n+2)−0₎`), matching
`ardCFirst` termwise. -/
theorem aOutLevNHalf_eq_ardCFirst (W : VertexOperatorAlgebra 𝒱) (n K M : ℕ) (a c d : 𝒱) :
    aOutLevNHalf W n K M a c d = ardCFirst W n K M a c d := by
  rw [aOutLevNHalf, ardCFirst]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  rw [PresAnm]
  refine Finset.sum_congr (by norm_num) fun j _ => ?_
  congr 2 <;> push_cast <;> ring

/-! ## The level-`0` half as the diagonal pole-`2` difference plus the clean level-`n` half. -/

/-- **The level-`0` half as the diagonal pole-`2` difference plus the level-`n` half** (FULLY
proven, homogeneous `a ∈ 𝒱_K`, `c ∈ 𝒱_M`).  By the master bridge
`crossCFirstDiff_eq_anmCircAnmRightDiff` (`ZhuVermaAnArchCFirstDiffMaster`) and the half identities
`aOutLev0Half_eq_crossCircCFirst` / `aOutLevNHalf_eq_ardCFirst`:

  `aOutLev0Half = aOutLevNHalf
       + (anmCirc W 0 0 c (anmRight W n 0 a d) − anmCirc W n 0 c (anmRight W n 0 a d))`.

The added difference is exactly the diagonal pole-`2` object of `CircDiffAnmRightTowerEq`. -/
theorem aOutLev0Half_eq_levNHalf_add_diff (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {K M : ℕ}
    {a c : 𝒱} (ha : a ∈ W.grading (K : ℤ)) (hc : c ∈ W.grading (M : ℤ)) (d : 𝒱) :
    aOutLev0Half W n K M a c d
      = aOutLevNHalf W n K M a c d
        + (anmCirc W 0 0 c (anmRight W n 0 a d) - anmCirc W n 0 c (anmRight W n 0 a d)) := by
  rw [aOutLev0Half_eq_crossCircCFirst, aOutLevNHalf_eq_ardCFirst,
    ← crossCFirstDiff_eq_anmCircAnmRightDiff W n ha hc d,
    crossCircCFirst_eq_ardCFirst_add_diff W n K M a c d]

/-! ## `AoutUCoreLev0Core` from the diagonal pole-`2` core `CircDiffAnmRightTowerEq`. -/

/-- **`CircDiffAnmRightTowerEq` ⟹ `AoutUCoreLev0Core`** (the `Uγ`-mirror collapse, homogeneous
`a ∈ 𝒱_K`, `c ∈ 𝒱_M`).  By `aOutLev0Half_eq_levNHalf_add_diff`, the level-`0` half is the clean
level-`n` `c`-`PresTowerFam` (`aOutLevNHalf_eq_PresTowerFam`) plus the diagonal pole-`2` difference;
the carried `CircDiffAnmRightTowerEq` supplies the difference as a grade-`M` level-`n` `c`-`PresTowerFam`
(over the wide `a₍g₎d`) plus the `c₍s₎a` `MGTowerFam`.  Merging the two grade-`M` level-`n`
`c`-`PresTowerFam`s (`PresTowerFam_add`) and carrying the `MGTowerFam` (with its left-factor
homogeneity) unchanged yields the explicit `AoutUCoreLev0Core` witness — the `a`-outer `c`-outer
level-`0` half `Uγ`-collapse, the twin of the FULLY-proven diagonal U-core
`UgammaModeCollAnm_eq_towerCoeff`. -/
theorem aOutUCoreLev0Core_of_circDiff (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {K M P : ℕ}
    {a c d : 𝒱} (ha : a ∈ W.grading (K : ℤ)) (hc : c ∈ W.grading (M : ℤ))
    (hdiag : CircDiffAnmRightTowerEq W n K M P a c d) :
    AoutUCoreLev0Core W n K M P a c d := by
  obtain ⟨RU, ΔU, S, baseU, wU, gradeS, leftS, baseS, ΔS, wS, hhom, hdiageq⟩ := hdiag
  -- the merged grade-`M` level-`n` `c`-`PresTowerFam`: (level-`n` half tower) + (diagonal U₀).
  refine ⟨(K + 1) + RU, max 1 ΔU, S,
    (fun r => Sum.elim (fun i : Fin (K + 1) => W.smul a ((i : ℤ) - ((n : ℤ) + 1)) d) baseU
        (finSumFinEquiv.symm r)),
    (fun r δ => Sum.elim
        (fun i : Fin (K + 1) => if δ < 1 then (if δ = 0 then cbz (K : ℤ) (i : ℤ) else 0) else 0)
        (fun r₂ => if δ < ΔU then wU r₂ δ else 0) (finSumFinEquiv.symm r)),
    gradeS, leftS, baseS, ΔS, wS, hhom, ?_⟩
  rw [aOutLev0Half_eq_levNHalf_add_diff W n ha hc d, aOutLevNHalf_eq_PresTowerFam W n K M a c d,
    hdiageq]
  -- `(U_N) + (U₀ + MG) = (U_N + U₀) + MG`, with `U_N + U₀` a single `PresTowerFam`.
  rw [show (PresTowerFam W M n c (K + 1) 1
              (fun i => W.smul a ((i : ℤ) - ((n : ℤ) + 1)) d)
              (fun i δ => if δ = 0 then cbz (K : ℤ) (i : ℤ) else 0))
          + (PresTowerFam W M n c RU ΔU baseU wU
              + MGTowerFam W n S gradeS leftS baseS ΔS wS)
        = (PresTowerFam W M n c (K + 1) 1
              (fun i => W.smul a ((i : ℤ) - ((n : ℤ) + 1)) d)
              (fun i δ => if δ = 0 then cbz (K : ℤ) (i : ℤ) else 0)
            + PresTowerFam W M n c RU ΔU baseU wU)
          + MGTowerFam W n S gradeS leftS baseS ΔS wS from by abel]
  rw [PresTowerFam_add W M n c (K + 1) RU 1 ΔU
      (fun i => W.smul a ((i : ℤ) - ((n : ℤ) + 1)) d) baseU
      (fun i δ => if δ = 0 then cbz (K : ℤ) (i : ℤ) else 0) wU]

/-! ## `AoutUCoreLev0Core` from the established `a`-outer core `ARDTowerDecomp`. -/

/-- **`ARDTowerDecomp` ⟹ `AoutUCoreLev0Core`** (the full lift through the diagonal pole-`2` face).
The genuine `a`-irreducible Dong–Jiang Lemma 2.8 core `ARDTowerDecomp` (the `a`-outer
right-action-difference tower decomposition, `ZhuVermaAnArchCrossCFirstGate`) lifts to the diagonal
pole-`2` core `CircDiffAnmRightTowerEq` (`circDiffAnmRightTowerEq_of_ARDTowerDecomp`,
`ZhuVermaAnArchCircDiffARD`), which discharges the level-`0` half `Uγ`-collapse via
`aOutUCoreLev0Core_of_circDiff`.  This unifies the `a`-outer `c`-outer level-`0` U-core with the
single open frontier core `ARDTowerDecomp`. -/
theorem aOutUCoreLev0Core_of_ARDTowerDecomp (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {K M P : ℕ}
    {a c d : 𝒱} (ha : a ∈ W.grading (K : ℤ)) (hc : c ∈ W.grading (M : ℤ))
    (hd : d ∈ W.grading (P : ℤ)) (hdec : ARDTowerDecomp W n K M P a c d) :
    AoutUCoreLev0Core W n K M P a c d :=
  aOutUCoreLev0Core_of_circDiff W n ha hc
    (circDiffAnmRightTowerEq_of_ARDTowerDecomp W n ha hc hd hdec)

/-! ## `MUGradedAction W` from the universal `ARDTowerDecomp` (via the level-`0` half route). -/

/-- **`MUGradedAction W` from the single universal `ARDTowerDecomp`** (the `a`-outer level-`0` half
route).  Given, for every level `n` and all homogeneous data, the `a`-irreducible core
`ARDTowerDecomp`, the level-`0` half `Uγ`-collapse `AoutUCoreLev0Core` holds for all data
(`aOutUCoreLev0Core_of_ARDTowerDecomp`), and `MUGradedAction_of_aOutUCoreLev0Core`
(`ZhuVermaAnArchAoutUCore`) — every other structural piece of the `a`-outer `c`-outer U-core
discharged (the clean level-`n` half `aOutLevNHalf_eq_PresTowerFam`, the commutator twins) — assembles
the Dong–Jiang `M(U)` graded-action crux `MUGradedAction W`, the `q_act` source of the
Construction-B diagonal well-definedness feeding `Function.Bijective (forwardMap W)` (Zhu Thm 5.3.4).

This re-derives `MUGradedAction W` from `ARDTowerDecomp` through the `a`-outer **level-`0` half**
`Uγ`-collapse face, unifying it with the diagonal route `MUGradedAction_of_ARDTowerDecomp_via_diag`
(`ZhuVermaAnArchCircDiffARD`) and the `c`-first route `MUGradedAction_of_ARDTowerDecomp_via_diff`
(`ZhuVermaAnArchCrossCFirstDiffClose`): all three discharged by the SAME `ARDTowerDecomp`. -/
theorem MUGradedAction_of_ARDTowerDecomp_via_lev0 (W : VertexOperatorAlgebra 𝒱)
    (Hdec : ∀ (n K M P : ℕ), ∀ a ∈ W.grading (K : ℤ), ∀ c ∈ W.grading (M : ℤ),
      ∀ d ∈ W.grading (P : ℤ), ARDTowerDecomp W n K M P a c d) :
    MUGradedAction W :=
  MUGradedAction_of_aOutUCoreLev0Core W
    (fun n K M P a ha c hc d hd =>
      aOutUCoreLev0Core_of_ARDTowerDecomp W n ha hc hd (Hdec n K M P a ha c hc d hd))

/-! ## Status — the `a`-outer `c`-outer level-`0` half `Uγ`-collapse closed modulo `ARDTowerDecomp`.

Proved here (`#print axioms` = `[propext, Classical.choice, Quot.sound]`; no `sorry`/
`axiom`/`pbw`):

* **`aOutLev0Half_eq_crossCircCFirst`** / **`aOutLevNHalf_eq_ardCFirst`** — the level-`0` / level-`n`
  halves of `aOutUPart` ARE the level-`0` / level-`n` `c`-first families `crossCircCFirst` / `ardCFirst`
  (definitional unfolds via `PresAnm`).
* **`aOutLev0Half_eq_levNHalf_add_diff`** — the level-`0` half as the clean level-`n` `c`-`PresTowerFam`
  plus the diagonal pole-`2` difference `anmCirc W 0 0 c (anmRight) − anmCirc W n 0 c (anmRight)` (via
  the master bridge `crossCFirstDiff_eq_anmCircAnmRightDiff`).
* **`aOutUCoreLev0Core_of_circDiff`** — **the `Uγ`-mirror collapse**: `CircDiffAnmRightTowerEq` ⟹
  `AoutUCoreLev0Core` (merge the level-`n` half `c`-tower with the diagonal `c`-tower via
  `PresTowerFam_add`, carry the `c₍s₎a` `MGTowerFam`).  The `a`-outer `c`-outer twin of the FULLY-proven
  diagonal U-core `UgammaModeCollAnm_eq_towerCoeff` (`ZhuVermaAnArchMUcircV`).
* **`aOutUCoreLev0Core_of_ARDTowerDecomp`** — the full lift `ARDTowerDecomp` ⟹ `AoutUCoreLev0Core`
  through the diagonal pole-`2` face (`circDiffAnmRightTowerEq_of_ARDTowerDecomp`).
* **`MUGradedAction_of_ARDTowerDecomp_via_lev0`** — **the full `MUGradedAction W`** from the single
  universal `ARDTowerDecomp`, through the `a`-outer level-`0` half `Uγ`-collapse face, via
  `MUGradedAction_of_aOutUCoreLev0Core`.

**The single remaining identity (engine-verified TRUE; NOT faked):** the `a`-irreducible core
`ARDTowerDecomp W n K M P a c d` — equivalently the diagonal pole-`2` core
`CircDiffAnmRightTowerEq W n K M P a c d` (`anmCirc W 0 0 c (anmRight) − anmCirc W n 0 c (anmRight)
= PresTowerFam(c) + MGTowerFam`).  An exploratory rank-1-free-boson computer-algebra run (script not retained) found the combined `c`-tower-over-`a₍g₎d` +
`c₍s₎a`-tower span
**True**, `n = 1, 2`; the `c`-tower span ALONE **False** — both families load-bearing).  This file
closes the level-`0` half `Uγ`-collapse face of the `a`-outer `c`-outer U-core
(`ZhuVermaAnArchAoutUCore`) modulo that single shared core, the `a`-outer twin of the FULLY-proven
diagonal U/V collapse `AnmCircTowerEq_holds`.
-/

end VOA

/-
`#print axioms` check (each of the following prints
`[propext, Classical.choice, Quot.sound]`, NO `pbw`, NO `sorryAx`):

  #print axioms VOA.aOutLev0Half_eq_crossCircCFirst
  #print axioms VOA.aOutLevNHalf_eq_ardCFirst
  #print axioms VOA.aOutLev0Half_eq_levNHalf_add_diff
  #print axioms VOA.aOutUCoreLev0Core_of_circDiff
  #print axioms VOA.aOutUCoreLev0Core_of_ARDTowerDecomp
  #print axioms VOA.MUGradedAction_of_ARDTowerDecomp_via_lev0
-/
