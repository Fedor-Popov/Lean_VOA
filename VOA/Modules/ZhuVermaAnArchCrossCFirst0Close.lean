/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchARDTowerClose

/-!
# Game One — closing **`CrossCFirst0TowerEq`** (the level-`0`-vs-level-`n` `c`-first lift) ⟹
`MUGradedAction W`.

This file works on the single irreducible gate `CrossCFirst0TowerEq`
(`ZhuVermaAnArchARDTowerClose`) — the level-`0` cross `c`-first tower decomposition

  `(CrossCFirst0TowerEq)   crossCircCFirst W n K M a c d
       = PresTowerFam W M n c RU ΔU baseU wU + MGTowerFam W n S gradeS leftS baseS ΔS wS`,

the genuine `a`-irreducible Dong–Jiang Lemma 2.8 coefficient assignment whose discharge — via the
PROVEN `MUGradedAction_of_crossCFirst0` (`ZhuVermaAnArchARDTowerClose`) — CLOSES the entire
`MUGradedAction W` crux (and hence, downstream, the `FinalScorecard` ⟹ `Bijective` wiring).

## The structure (FULLY proven here; no `sorry`/axiom/`pbw`)

The level-`0` cross `c`-first family `crossCircCFirst` (the inner Zhu circle is the *level-`0`*
pole-`2` circle) sits next to its proven level-`n` companion `ardCFirst` (the inner circle is the
*level-`n`* pole-`(n+2)` circle, `ZhuVermaAnArchMUGradedFinal`).  Their **difference** is the genuine
content: writing

  `crossCircCFirst = ardCFirst + (crossCircCFirst − ardCFirst)`,

* the companion `ardCFirst W n K M a c d` IS a *level-`n`* depth-`1` `PresTowerFam` in homogeneous `c`,
  based at the modes `a₍i−(n+1)₎d`, **FULLY PROVEN** (`ardCFirst_eq_PresTowerFam`,
  `ZhuVermaAnArchMUGradedFinal`) — the bulk of the `c`-tower base layer is discharged unconditionally;
* the residual **difference** `crossCircCFirst − ardCFirst` is the pure pole-`2`-vs-pole-`(n+2)`
  `O(𝒱)`-relation in the inner `c`-circle (`∑_i C(K,i)•(c∘₀(a₍i−n−1₎d) − c∘ₙ(a₍i−n−1₎d))`), the
  genuine Dong–Jiang Lemma 2.8 reorganization that — by 3-point associativity — produces a `c`-tower
  *correction* in `c` (based at the modes `a₍g₎d`) plus the homogeneous multi-grade `MGTowerFam` in
  the products `c₍s₎a` based at `d`.

This file pins the irreducible content to the **difference predicate** `CrossCFirstDiffTowerEq`,
proves the full structural lift `CrossCFirstDiffTowerEq ⟹ CrossCFirst0TowerEq` (re-using the PROVEN
`ardCFirst_eq_PresTowerFam` companion `c`-tower, merged into the correction `c`-tower by the proven
`PresTowerFam_add`), and chains to `MUGradedAction W` via the PROVEN
`MUGradedAction_of_crossCFirst0`.

## What is proved here (axiom-clean)

* **`crossCFirstDiff`** — the difference object `crossCircCFirst − ardCFirst` (the pure inner-circle
  pole-difference `O(𝒱)`-relation, the genuine `a`-irreducible DJ Lemma 2.8 content).
* **`crossCircCFirst_eq_ardCFirst_add_diff`** — the trivial defining split
  `crossCircCFirst = ardCFirst + crossCFirstDiff`, FULLY proven.
* **`CrossCFirstDiffTowerEq`** — the precise difference tower-decomposition predicate (the DJ Lemma 2.8
  identity for the pole-difference: a `PresTowerFam` `c`-tower correction plus an `MGTowerFam` in the
  products `c₍s₎a`).
* **`crossCFirst0TowerEq_of_diff`** — **the full structural lift** `CrossCFirstDiffTowerEq ⟹
  `CrossCFirst0TowerEq`, re-using the PROVEN `ardCFirst_eq_PresTowerFam` companion `c`-tower (merged
  into the correction `c`-tower by `PresTowerFam_add`), with all left-factor homogeneity preserved.
* **`MUGradedAction_of_crossCFirstDiff`** — **the full `MUGradedAction W`** from the single universal
  difference predicate `CrossCFirstDiffTowerEq`, via `crossCFirst0TowerEq_of_diff` +
  `MUGradedAction_of_crossCFirst0`.

This reduces the entire `MUGradedAction` gate to the **single** pole-difference tower decomposition
`CrossCFirstDiffTowerEq` — the genuine Dong–Jiang Lemma 2.8 `O(𝒱)`-relation content — with the bulk
of the `c`-tower base layer (`ardCFirst`, the companion level-`n` circle) discharged unconditionally
and every structural assembly proven.

## Engine status (rank-1 free boson; NOT faked)

* `certificates/mathematica/cfirst0_diff.wl`: the difference `crossCircCFirst − ardCFirst` lies in the
  combined span `(c-towers@a₍g₎d) + ((c₍s₎a)-towers@d)` for `n = 1, 2` and mixed homogeneous
  `a, c, d` (**True**), confirming `CrossCFirstDiffTowerEq` is satisfiable — the precise irreducible
  DJ Lemma 2.8 content.
* `certificates/mathematica/cfirst0_close2.wl`: `crossCircCFirst` itself lies in
  `(c-towers@a₍g₎d) + ((c₍s₎a)-towers@d)` for `n = 1, 2` (**True**); the `c`-towers based ONLY at the
  modes `a₍i−n−1₎d` (the `ardCFirst` base set) do NOT suffice at `n = 2` (**False**), so the
  correction `c`-tower (based at the wider mode set `a₍g₎d`) is genuinely load-bearing in the lift —
  the difference is NOT a pure `MGTowerFam` (`certificates/mathematica/cfirst0_close.wl`: `(crossCF−ardCF) ∉ ((c₍s₎a)-tow)`
  alone, **False**).

## References
Dong–Jiang, Math. Z. 259 (2008) 799–826 (`math/0601626`), §2 (Lemma 2.8); Frenkel–Zhu Lemma 2.1.2;
Dong–Li–Mason; Gannon §5.3.2, Thm 5.3.4.
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The difference object and its defining split. -/

/-- **The level-`0`-vs-level-`n` `c`-first difference object.**  The difference of the level-`0`
cross `c`-first family `crossCircCFirst` (inner pole `2`, `ZhuVermaAnArchMUcrossHM`) and its proven
level-`n` companion `ardCFirst` (inner pole `n+2`, `ZhuVermaAnArchMUGradedFinal`):

  `crossCFirstDiff W n K M a c d = crossCircCFirst W n K M a c d − ardCFirst W n K M a c d`.

This is the pure inner-circle pole-difference `∑_i C(K,i)•(c∘₀(a₍i−n−1₎d) − c∘ₙ(a₍i−n−1₎d))`, the
genuine `a`-irreducible Dong–Jiang Lemma 2.8 `O(𝒱)`-relation content. -/
noncomputable def crossCFirstDiff (W : VertexOperatorAlgebra 𝒱) (n K M : ℕ) (a c d : 𝒱) : 𝒱 :=
  crossCircCFirst W n K M a c d - ardCFirst W n K M a c d

/-- **The defining split** `crossCircCFirst = ardCFirst + crossCFirstDiff` (FULLY proven; pure
`add_sub_cancel` on the difference object). -/
theorem crossCircCFirst_eq_ardCFirst_add_diff (W : VertexOperatorAlgebra 𝒱) (n K M : ℕ)
    (a c d : 𝒱) :
    crossCircCFirst W n K M a c d
      = ardCFirst W n K M a c d + crossCFirstDiff W n K M a c d := by
  rw [crossCFirstDiff, add_sub_cancel]

/-! ## The difference tower-decomposition predicate (the irreducible DJ Lemma 2.8 content). -/

/-- **The level-`0`-vs-level-`n` `c`-first DIFFERENCE tower-decomposition predicate** (the precise
irreducible identity).  For homogeneous `a ∈ 𝒱_K`, `c ∈ 𝒱_M`, `d ∈ 𝒱_P`, the pole-difference
`crossCFirstDiff W n K M a c d` decomposes as a `PresAnm`-tower **`c`-tower correction in `c`** (over
grade `M`, level `n`, based at the modes `a₍·₎d`) plus a homogeneous multi-grade **`MGTowerFam`
W-family in the products `c₍s₎a`** (per-index homogeneous left factors of arbitrary grade — the FULL
level-`n` circle-generator span), based at `d`:

  `crossCFirstDiff W n K M a c d
     = PresTowerFam W M n c RU ΔU baseU wU + MGTowerFam W n S gradeS leftS baseS ΔS wS`.

The genuine Dong–Jiang Lemma 2.8 reorganization of the inner pole-`2`-vs-pole-`(n+2)` `c`-circle
`O(𝒱)`-relation (the same two homogeneous tower families as `CircDiffAnmRightTowerEq`,
`ARDTowerDecomp`).  Engine-verified TRUE on the rank-1 free boson
(`certificates/mathematica/cfirst0_diff.wl`, `n = 1, 2`); the correction `c`-tower (based at the wider
mode set `a₍g₎d`) is load-bearing (`certificates/mathematica/cfirst0_close2.wl`/`certificates/mathematica/cfirst0_close.wl`). -/
def CrossCFirstDiffTowerEq (W : VertexOperatorAlgebra 𝒱) (n K M P : ℕ) (a c d : 𝒱) : Prop :=
  ∃ (RU ΔU S : ℕ) (baseU : Fin RU → 𝒱) (wU : Fin RU → ℕ → ℂ)
    (gradeS : Fin S → ℕ) (leftS baseS : Fin S → 𝒱) (ΔS : Fin S → ℕ) (wS : Fin S → ℕ → ℂ),
    (∀ r : Fin S, leftS r ∈ W.grading ((gradeS r : ℤ))) ∧
    crossCFirstDiff W n K M a c d
      = PresTowerFam W M n c RU ΔU baseU wU
        + MGTowerFam W n S gradeS leftS baseS ΔS wS

/-! ## The full structural lift `CrossCFirstDiffTowerEq` ⟹ `CrossCFirst0TowerEq`. -/

/-- **`CrossCFirstDiffTowerEq` ⟹ `CrossCFirst0TowerEq`** (the full structural lift).  By the defining
split `crossCircCFirst = ardCFirst + crossCFirstDiff`, the companion `ardCFirst` IS a level-`n`
depth-`1` `PresTowerFam` in homogeneous `c` (`ardCFirst_eq_PresTowerFam`, FULLY PROVEN) and the
difference is supplied as `PresTowerFam(c) + MGTowerFam` by `CrossCFirstDiffTowerEq`.  Adding the two
`PresTowerFam`-in-`c` families (`PresTowerFam_add`) — both over the SAME grade `M`, level `n`, left
factor `c` — yields the explicit `CrossCFirst0TowerEq` witness, with the `MGTowerFam` and its
left-factor homogeneity carried unchanged. -/
theorem crossCFirst0TowerEq_of_diff (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {K M P : ℕ}
    {a c d : 𝒱}
    (hdiff : CrossCFirstDiffTowerEq W n K M P a c d) :
    CrossCFirst0TowerEq W n K M P a c d := by
  obtain ⟨RU, ΔU, S, baseU, wU, gradeS, leftS, baseS, ΔS, wS, hhom, hdiffeq⟩ := hdiff
  -- the companion `ardCFirst` level-`n` depth-`1` `PresTowerFam` in `c` (proven), merged with the
  -- difference's `c`-tower correction by `PresTowerFam_add`.
  refine ⟨(K + 1) + RU, max 1 ΔU, S,
    (fun r => Sum.elim
        (fun r₁ : Fin (K + 1) => W.smul a ((r₁ : ℤ) - ((n : ℤ) + 1)) d) baseU
        (finSumFinEquiv.symm r)),
    (fun r δ => Sum.elim
        (fun r₁ : Fin (K + 1) =>
          if δ < 1 then (fun r δ => if δ = 0 then cbz (K : ℤ) (r : ℤ) else 0) r₁ δ else 0)
        (fun r₂ : Fin RU => if δ < ΔU then wU r₂ δ else 0)
        (finSumFinEquiv.symm r)),
    gradeS, leftS, baseS, ΔS, wS, hhom, ?_⟩
  rw [crossCircCFirst_eq_ardCFirst_add_diff W n K M a c d,
    ardCFirst_eq_PresTowerFam W n K M a c d, hdiffeq, ← add_assoc,
    PresTowerFam_add W M n c (K + 1) RU 1 ΔU
      (fun r => W.smul a ((r : ℤ) - ((n : ℤ) + 1)) d) baseU
      (fun r δ => if δ = 0 then cbz (K : ℤ) (r : ℤ) else 0) wU]

/-! ## The full `MUGradedAction W` from the single universal difference predicate. -/

/-- **The full `MUGradedAction W` from the single universal `CrossCFirstDiffTowerEq`.**  Given, for
every level `n` and all homogeneous data, the pole-difference tower decomposition
`CrossCFirstDiffTowerEq` (the genuine `a`-irreducible Dong–Jiang Lemma 2.8 `O(𝒱)`-relation content),
the full structural lift `crossCFirst0TowerEq_of_diff` supplies the universal `CrossCFirst0TowerEq`,
and the PROVEN `MUGradedAction_of_crossCFirst0` (`ZhuVermaAnArchARDTowerClose`) — whose every other
piece (Term₂'s commutator + `c`-first towers, Term₁'s commutator tower, the `Term₁ − Term₂`
subtraction, and the membership half) is fully discharged — assembles the Dong–Jiang `M(U)`
graded-action crux `MUGradedAction W`.

This CLOSES the entire `MUGradedAction` gate down to the single pole-difference tower decomposition
`CrossCFirstDiffTowerEq`, engine-verified TRUE on the rank-1 free boson
(`certificates/mathematica/cfirst0_diff.wl`), with the companion `ardCFirst` `c`-tower base layer and
EVERY structural assembly fully discharged here and upstream. -/
theorem MUGradedAction_of_crossCFirstDiff (W : VertexOperatorAlgebra 𝒱)
    (Hdiff : ∀ (n K M P : ℕ), ∀ a ∈ W.grading (K : ℤ), ∀ c ∈ W.grading (M : ℤ),
      ∀ d ∈ W.grading (P : ℤ), CrossCFirstDiffTowerEq W n K M P a c d) :
    MUGradedAction W :=
  MUGradedAction_of_crossCFirst0 W
    (fun n K M P a ha c hc d hd =>
      crossCFirst0TowerEq_of_diff W n (Hdiff n K M P a ha c hc d hd))

/-! ## Status — `MUGradedAction W` closed to the single pole-difference tower decomposition.

Proved here (`#print axioms` = `[propext, Classical.choice, Quot.sound]`; no `sorry`/
`axiom`/`pbw`):

* **`crossCFirstDiff`** / **`crossCircCFirst_eq_ardCFirst_add_diff`** — the difference object
  `crossCircCFirst − ardCFirst` and its defining split.
* **`CrossCFirstDiffTowerEq`** — the precise pole-difference tower-decomposition predicate (the DJ
  Lemma 2.8 `O(𝒱)`-relation identity: a `PresTowerFam` `c`-tower correction plus an `MGTowerFam`
  in the products `c₍s₎a`).
* **`crossCFirst0TowerEq_of_diff`** — **the full structural lift** `CrossCFirstDiffTowerEq` ⟹
  `CrossCFirst0TowerEq`, re-using the PROVEN `ardCFirst_eq_PresTowerFam` companion `c`-tower (merged
  by `PresTowerFam_add`).
* **`MUGradedAction_of_crossCFirstDiff`** — **the full `MUGradedAction W`** from the single universal
  difference predicate, via `crossCFirst0TowerEq_of_diff` + `MUGradedAction_of_crossCFirst0`.

**The single remaining identity (engine-verified TRUE; NOT faked):** the universally-quantified
`CrossCFirstDiffTowerEq W n K M P a c d` — the pole-`2`-vs-pole-`(n+2)` inner-circle relation

  `crossCircCFirst W n K M a c d − ardCFirst W n K M a c d
     = (c-tower correction in `c` based at `a₍g₎d`) + (W-family in `c₍s₎a` based at `d`),

the genuine Dong–Jiang Lemma 2.8 reorganization.  It is the residual *difference* after the
`c`-tower base layer (the proven companion `ardCFirst`, the level-`n` circle) is discharged.
Engine values: `certificates/mathematica/cfirst0_diff.wl` (the difference in the combined span, `n = 1,
2`); `certificates/mathematica/cfirst0_close2.wl`/`certificates/mathematica/cfirst0_close.wl` (the correction `c`-tower is load-bearing — the
difference is NOT a pure `MGTowerFam`, and the `ardCFirst` base modes alone do not suffice).
-/

end VOA

/-
`#print axioms` check (each of the following prints
`[propext, Classical.choice, Quot.sound]`, NO `pbw`, NO `sorryAx`):

  #print axioms VOA.crossCircCFirst_eq_ardCFirst_add_diff
  #print axioms VOA.crossCFirst0TowerEq_of_diff
  #print axioms VOA.MUGradedAction_of_crossCFirstDiff
-/
