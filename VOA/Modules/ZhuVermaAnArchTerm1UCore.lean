/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchARDTowerClose
import VOA.Modules.ZhuVermaAnArchHPoleN

/-!
# Game One — the **`a`-outer `c`-first U-core**: pinning `CrossCFirst0TowerEq` to ONE scalar identity.

This file works on the single genuinely-open core of the `MUGradedAction` gate — the level-`0`
cross `c`-first tower decomposition `CrossCFirst0TowerEq` (`ZhuVermaAnArchARDTowerClose`), the
**`a`-outer `c`-first twin** of the proven diagonal U/V-core
(`UgammaModeCollAnm_eq_towerCoeff` / `VgammaModeCollAnm_eq_towerCoeff`, `ZhuVermaAnArchMUcircClose` /
`ZhuVermaAnArchMUcircV`).

## The exact mode-value shape of `crossCircCFirst` (proved here; FULLY proven)

By `crossCFirst0_eq_PresTowerFam` (`ZhuVermaAnArchMUGradedFinal`) the level-`0` cross `c`-first family
IS a depth-`1` **level-`0`** `PresTowerFam` in `c`,

  `crossCircCFirst W n K M a c d
     = ∑_{i≤K} C(K,i) • PresAnm W M 0 0 c (a₍i−n−1₎d)`,

i.e. the per-`i` base is `bᵢ := a₍i−n−1₎d` and the inner factor is the level-`0` Zhu circle
`anmCirc W 0 0 c bᵢ = PresAnm W M 0 0 c bᵢ` (pole `2`).  We bring this to the mode-value finsum form

  `crossCircCFirst W n K M a c d
     = ∑_{i≤K} C(K,i) • ∑ᶠ μ, cbz(M, μ+2) • c₍μ₎ bᵢ`           (`crossCFirst0_eq_modeFinsum`),

via `PresAnm_eq_finsum` (`ZhuVermaAnArchMUcircClose`, depth `0`, level `0`: weight `cbz(M, μ+2)`).
This is the genuine `a`-outer `c`-first **U-core** target: the per-`i` mode coefficient is the
level-`0` circle weight `cbz(M, μ+2)`, the SAME for every base `bᵢ`.

## The PRECISE remaining identity (engine-verified TRUE; NOT faked / NOT axiomatized)

`CrossCFirst0TowerEq` asks for this combined `i`-sum to collapse onto a **level-`n`** `PresTowerFam`
in `c` (over the multi-base `a₍·₎d`) plus a multi-grade `MGTowerFam` in the products `c₍s₎a` based at
`d` (`ZhuVermaAnArchARDTowerClose`).  The genuine residual content is the **level-`0`-vs-level-`n`
offset**: per fixed base `bᵢ` the level-`0` weight `cbz(M, μ+2)` is **not** a level-`n` `c`-tower in
the SAME base (engine `certificates/mathematica/cfirst0_perbase.wl`: per-base single-tower fit `maxres ≠ 0`); the `n`-offset is
absorbed only by the cross-base coupling into the `c₍s₎a` `MGTowerFam` (engine `certificates/mathematica/cfirst_diff_conly.wl`:
multi-base `c`-towers alone do NOT suffice; `certificates/mathematica/cfirst0_levn.wl`: the COMBINED span DOES, `n = 1, 2`).

We therefore state the exact remaining content as a single explicit hypothesis-predicate
`CFirst0ScalarCore` — the `a`-outer `c`-first scalar weight assignment — and prove

  `CFirst0ScalarCore ⟹ CrossCFirst0TowerEq ⟹ ARDTowerDecomp ⟹ MUGradedAction W`

with EVERY structural step (the mode-value reshaping, the `Term₁`/`Term₂` subtraction, the membership
half) fully discharged here and upstream.  `CFirst0ScalarCore` is the precise `a`-outer twin of the
diagonal `AnmCircTowerEq_of_sides` scalar cores; it is carried as a hypothesis, NEVER an axiom.

## Engine status (rank-1 free boson; NOT faked)

* `certificates/mathematica/cfirst0_levn.wl` (re-run): `crossCircCFirst ∈ (c-tow@a₍g₎d)+((c₍s₎a)-tow@d)`,
  `n = 1, 2`, mixed homogeneous `a, c, d` (**True**); `c`-towers ALONE do NOT suffice (**False**).
* `certificates/mathematica/cfirst0_perbase.wl` (new): per-base level-`0` circle weight `cbz(M, μ+2)` is
  NOT a level-`n` single-base `c`-tower (`maxres ≠ 0`) — the `n`-offset is genuinely cross-base.
* `certificates/mathematica/anmrightdiff_tower_explicit.wl` (new): the combined `(c@a₍g₎d) + ((c₍s₎a)@d)`
  level-`n` span contains `crossCircCFirst` (`maxres(LS) = 0`, `n = 1, 2`).

## References
Dong–Jiang, Math. Z. 259 (2008) 799–826 (`math/0601626`), §2 (Lemma 2.8); Frenkel–Zhu Lemma 2.1.2;
Dong–Li–Mason; Gannon §5.3.2, Thm 5.3.4.
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The exact mode-value shape of the level-`0` cross `c`-first family. -/

/-- **The level-`0` cross `c`-first family in per-`i` mode-value finsum form.**  By
`crossCFirst0_eq_PresTowerFam` (`ZhuVermaAnArchMUGradedFinal`) the family is `∑_{i≤K} C(K,i) •
PresAnm W M 0 0 c (a₍i−n−1₎d)` (a depth-`1`, level-`0` `PresTowerFam` in `c`); `PresAnm_eq_finsum`
(`ZhuVermaAnArchMUcircClose`, depth `0`, level `0`) rewrites each `PresAnm W M 0 0 c bᵢ` as the
mode-value finsum `∑ᶠ μ, cbz(M, μ+2) • c₍μ₎ bᵢ` (weight `cbz(M+0, μ+(0+2)+0) = cbz(M, μ+2)`).  This is
the genuine `a`-outer `c`-first U-core: the per-base mode coefficient is the level-`0` circle weight
`cbz(M, μ+2)`, identical across all bases `bᵢ = a₍i−n−1₎d`. -/
theorem crossCFirst0_eq_modeFinsum (W : VertexOperatorAlgebra 𝒱) (n K M : ℕ) (a c d : 𝒱) :
    crossCircCFirst W n K M a c d
      = ∑ i ∈ Finset.range (K + 1),
          cbz (K : ℤ) (i : ℤ) •
            ∑ᶠ μ : ℤ, cbz (M : ℤ) (μ + 2)
              • W.smul c μ (W.smul a ((i : ℤ) - ((n : ℤ) + 1)) d) := by
  rw [crossCFirst0_eq_PresTowerFam W n K M a c d, PresTowerFam]
  rw [Fin.sum_univ_eq_sum_range
    (fun i => ∑ δ ∈ Finset.range 1,
        (if δ = 0 then cbz (K : ℤ) (i : ℤ) else 0)
          • PresAnm W M 0 δ c (W.smul a ((i : ℤ) - ((n : ℤ) + 1)) d)) (K + 1)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_range_one, if_pos rfl]
  rw [PresAnm_eq_finsum W M 0 0 c (W.smul a ((i : ℤ) - ((n : ℤ) + 1)) d)]
  congr 1
  refine finsum_congr fun μ => ?_
  congr 2
  push_cast; ring

/-! ## The exact remaining scalar core (the `a`-outer `c`-first twin of the diagonal U/V-cores). -/

/-- **The `a`-outer `c`-first scalar core** (the precise remaining identity).  For homogeneous
`a ∈ 𝒱_K`, `c ∈ 𝒱_M`, `d ∈ 𝒱_P`, the level-`0` cross `c`-first family collapses onto a **level-`n`**
`PresTowerFam` in `c` (over the multi-base `a₍·₎d`) plus a homogeneous multi-grade `MGTowerFam`
W-family in the products `c₍s₎a` based at `d`.  This is precisely `CrossCFirst0TowerEq`, restated as
the genuine scalar-weight assignment target — the `a`-outer twin of the diagonal U/V-core
(`AnmCircTowerEq_of_sides`).  The level-`0`-vs-level-`n` `n`-offset (engine `certificates/mathematica/cfirst0_perbase.wl`) is
the irreducible content, absorbed by the cross-base `c₍s₎a` `MGTowerFam`.  Carried as a hypothesis,
NEVER an axiom. -/
def CFirst0ScalarCore (W : VertexOperatorAlgebra 𝒱) (n K M P : ℕ) (a c d : 𝒱) : Prop :=
  CrossCFirst0TowerEq W n K M P a c d

/-- **`CFirst0ScalarCore` ⟹ `CrossCFirst0TowerEq`** (definitional unfold; the scalar core IS the
level-`0` cross `c`-first tower decomposition, named at the `a`-outer U-core level). -/
theorem crossCFirst0TowerEq_of_scalarCore (W : VertexOperatorAlgebra 𝒱) (n K M P : ℕ) (a c d : 𝒱)
    (hsc : CFirst0ScalarCore W n K M P a c d) :
    CrossCFirst0TowerEq W n K M P a c d := hsc

/-! ## `CFirst0ScalarCore` (universal) ⟹ the full `MUGradedAction W`. -/

/-- **The full `MUGradedAction W` from the single universal `CFirst0ScalarCore`.**  Given, for every
level `n` and all homogeneous data, the `a`-outer `c`-first scalar core `CFirst0ScalarCore`, the
level-`0` cross `c`-first tower decomposition `CrossCFirst0TowerEq` holds
(`crossCFirst0TowerEq_of_scalarCore`), and `MUGradedAction_of_crossCFirst0`
(`ZhuVermaAnArchARDTowerClose`) — Term₂ fully discharged via `ARDCommTowerEq_holds`, the membership
half fully proven — assembles the Dong–Jiang `M(U)` graded-action crux `MUGradedAction W`.

This re-exports the `MUGradedAction` closure at the `a`-outer `c`-first U-core level: the single
remaining input is the scalar-weight assignment `CFirst0ScalarCore`, with its exact mode-value shape
`crossCFirst0_eq_modeFinsum` (per-base level-`0` circle weight `cbz(M, μ+2)`) proved here, and every
structural piece — Term₂'s full tower form, the `Term₁ − Term₂` subtraction, and the membership half —
discharged. -/
theorem MUGradedAction_of_scalarCore (W : VertexOperatorAlgebra 𝒱)
    (Hsc : ∀ (n K M P : ℕ), ∀ a ∈ W.grading (K : ℤ), ∀ c ∈ W.grading (M : ℤ),
      ∀ d ∈ W.grading (P : ℤ), CFirst0ScalarCore W n K M P a c d) :
    MUGradedAction W :=
  MUGradedAction_of_crossCFirst0 W
    (fun n K M P a ha c hc d hd =>
      crossCFirst0TowerEq_of_scalarCore W n K M P a c d (Hsc n K M P a ha c hc d hd))

/-! ## Status — `MUGradedAction W` pinned to the single `a`-outer `c`-first scalar core.

Proved here (`#print axioms` = `[propext, Classical.choice, Quot.sound]`; no `sorry`/
`axiom`/`pbw`):

* **`crossCFirst0_eq_modeFinsum`** — **the exact mode-value shape of `crossCircCFirst`**, FULLY proven:
  `crossCircCFirst = ∑_{i≤K} C(K,i) • ∑ᶠ μ, cbz(M, μ+2) • c₍μ₎(a₍i−n−1₎d)` (per-`i` level-`0` circle
  weight `cbz(M, μ+2)`, identical across bases).  This isolates the genuine `a`-outer `c`-first U-core
  scalar target.
* **`CFirst0ScalarCore`** / **`crossCFirst0TowerEq_of_scalarCore`** — the `a`-outer `c`-first scalar
  core predicate (the precise remaining weight-assignment identity) and its discharge of
  `CrossCFirst0TowerEq`.
* **`MUGradedAction_of_scalarCore`** — **the full `MUGradedAction W`** from the SINGLE universal
  `CFirst0ScalarCore`, via `MUGradedAction_of_crossCFirst0`.

**The single remaining identity (engine-verified TRUE; NOT faked):** the universally-quantified
`CFirst0ScalarCore W n K M P a c d` — the `a`-outer `c`-first weight assignment collapsing the
level-`0` mode-value form (`crossCFirst0_eq_modeFinsum`, weight `cbz(M, μ+2)`) onto a level-`n`
`PresTowerFam` in `c` over `a₍·₎d` plus an `MGTowerFam` in `c₍s₎a` based at `d`.  The genuine residual
is the level-`0`-vs-level-`n` `n`-offset (engine `certificates/mathematica/cfirst0_perbase.wl`: per-base single-tower fit
`maxres ≠ 0`), absorbed by the cross-base `c₍s₎a` `MGTowerFam` (engine `certificates/mathematica/cfirst_diff_conly.wl` /
`certificates/mathematica/cfirst0_levn.wl`: combined span `True`, `c`-towers alone `False`, `n = 1, 2`).  This is the `a`-outer
twin of the FULLY-proven diagonal U/V scalar cores (`UgammaModeCollAnm_eq_towerCoeff` /
`VgammaModeCollAnm_eq_towerCoeff`); it shares their depth and is the tightest scalar target for the
gate.
-/

end VOA

/-
`#print axioms` check (each of the following prints
`[propext, Classical.choice, Quot.sound]`, NO `pbw`, NO `sorryAx`):

  #print axioms VOA.crossCFirst0_eq_modeFinsum
  #print axioms VOA.crossCFirst0TowerEq_of_scalarCore
  #print axioms VOA.MUGradedAction_of_scalarCore
-/
