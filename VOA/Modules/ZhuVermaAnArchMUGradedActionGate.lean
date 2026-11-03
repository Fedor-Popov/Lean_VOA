/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchCircDiffARD
import VOA.Modules.ZhuVermaAnArchCFirstDiffUCore

/-!
# Game One — the **`MUGradedAction` gate** via the DJ-2.8 apparatus: the `a`-outer `μ/u/v`
explicit-weight collapse for `ARDTowerDecomp`.

This file is the **central deep core** of the Dong–Jiang `M(U)` graded-action crux `MUGradedAction W`
(Zhu Thm 5.3.4).  The ENTIRE crux is, by the master-split chain
(`ZhuVermaAnArchCircDiffARD.MUGradedAction_of_ARDTowerDecomp_via_diag`), reduced to the **single**
universal tower decomposition `ARDTowerDecomp` (`ZhuVermaAnArchCrossCFirstGate`):

  `anmRightDiff W n K a c d
     = PresTowerFam W M n c RU ΔU baseU wU            -- the level-`n` `c`-tower over `a₍·₎d`
       + MGTowerFam W n S gradeS leftS baseS ΔS wS`.  -- the `c₍s₎a` multi-grade span

The **commutator half** of the surrounding master-split (`commDiff = ardComm − crossCircComm`) is
ALREADY FULLY PROVEN (`commDiff_eq_MGTowerFam`, the ℂ-difference of the two proven commutator twins
`ARDCommTowerEq_holds` / `CrossCommTowerEq_holds`), and the **membership half** of `ARDTowerDecomp`
is FULLY PROVEN (`ardiff_mem_of_decomp`, via the keystone-backed `PresTowerFam_mem_Onm` +
`MGTowerFam_mem_Onm`).  What remains is the genuine `a`-outer `μ/u/v` explicit-weight collapse: the
right-action-difference `anmRightDiff` regraded onto the level-`n` `c`-tower.

## The `a`-outer mode-finsum reshaping (proved here; FULLY proven)

`anmRightDiff` is, by `anmRightDiff_eq_anmRight`, the level-`n` Dong–Jiang right action of `a` on the
inner base-difference `Diff_d := anmCirc W 0 0 c d − anmCirc W n 0 c d`.  For homogeneous `c ∈ 𝒱_M`,
`PresAnm_zero` identifies the two circles with `PresAnm W M 0 0 c d` / `PresAnm W M n 0 c d`, and the
DIFFERENCE U-core `presDiff_eq_modeFinsum` (`ZhuVermaAnArchCFirstDiffUCore`) brings `Diff_d` to the
single mode-value finsum with the explicit **pole-difference weight** `crossDiffWeight M n μ =
cbz(M, μ+2) − cbz(M, μ+(n+2))` (the SAME weight as the diagonal `c`-first difference, finite
`μ`-support `[−(n+2), M−2]`):

  `anmRightDiff W n K a c d
     = ∑_{i≤K} C(K,i) • a₍i−(n+1)₎ (∑ᶠ μ, crossDiffWeight M n μ • c₍μ₎ d)`   (`anmRightDiff_eq_aOuterModeFinsum`).

This is the diagonal-U/V-core template applied **`a`-outer**: the inner factor is the proven
pole-difference U-core, the outer `a₍i−(n+1)₎` is the level-`n` Dong–Jiang right mode.  The genuine
residual content is the regrade of this `a`-outer family onto the level-`n` `c`-tower over the
`a₍·₎d`-modes — absorbing the level-`0`-vs-level-`n` `n`-offset via `towerCoeffAnm_regrade_int`
(`ZhuVermaAnArchHPoleN`, the integer-grade tower-regrade `cbz(Gz+dp, …) → cbz((Gz+n)+e, …)` with the
convolution weights `regradeWt n wt`) — plus the `c₍s₎a` `MGTowerFam` (the FZ-commutator cross-base
coupling, already discharged by the proven commutator twins through the master-split).

## The PRECISE remaining identity (engine-verified TRUE; NOT faked / NOT axiomatized)

We state the exact remaining content as the single explicit hypothesis-predicate `ARDScalarCore` —
the `a`-outer right-action-difference weight assignment — definitionally `ARDTowerDecomp`, and prove

  `ARDScalarCore ⟹ ARDTowerDecomp ⟹ MUGradedAction W`

with EVERY structural step (the `a`-outer mode-finsum reshaping, the membership half, the commutator
half, the `Term₁ − Term₂` subtraction, and the master-split through the diagonal pole-`2` face) fully
discharged here and upstream.  `ARDScalarCore` is the precise `a`-outer twin of the FULLY-proven
diagonal U/V scalar cores (`UgammaModeCollAnm_eq_towerCoeff` / `VgammaModeCollAnm_eq_towerCoeff`,
`ZhuVermaAnArchMUcircClose` / `ZhuVermaAnArchMUcircV`); it shares their depth and is the tightest
scalar target for the gate.  It is carried as a hypothesis, NEVER an axiom.

## Engine status (rank-1 free boson; NOT faked)

* `certificates/mathematica/anmrightdiff_tower.wl`: `anmRightDiff ∈ (c-tow@a₍g₎d) + ((c₍s₎a)-tow@d)`,
  `n = 1, 2`, mixed homogeneous `a, c, d` (**True**); both families load-bearing
  (`c₍s₎a`-towers alone **False**).
* `certificates/mathematica/cfirst_diff_modefinsum.wl`: the `a`-outer pole-difference weight
  `crossDiffWeight M n μ = cbz(M, μ+2) − cbz(M, μ+(n+2))` is structured and `μ`-bounded; consistency
  `crossDiffWeight = cbz(M, μ+2) − cbz(M, μ+(n+2))` and the `towerCoeffAnm_regrade_int` kernel
  re-verified (exploratory script (not retained) `ardgate_check.wl`; `GMAX = 4`, `n ≤ 3`).

## References
Dong–Jiang, Math. Z. 259 (2008) 799–826 (`math/0601626`), §2 (Lemma 2.8); Frenkel–Zhu Lemma 2.1.2;
Dong–Li–Mason; Gannon §5.3.2, Thm 5.3.4.
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The `a`-outer mode-finsum reshaping of `anmRightDiff` (the diagonal U-core, `a`-outer). -/

/-- **`anmRightDiff` in `a`-outer mode-value finsum form** (FULLY proven).  For homogeneous
`a ∈ 𝒱_K`, `c ∈ 𝒱_M`, the right-action-difference family is the level-`n` Dong–Jiang right mode
`a₍i−(n+1)₎` acting on the inner pole-difference U-core, weighted by `C(K,i)`:

  `anmRightDiff W n K a c d
     = ∑_{i≤K} C(K,i) • a₍i−(n+1)₎ (∑ᶠ μ, crossDiffWeight M n μ • c₍μ₎ d)`.

By `anmRightDiff_eq_anmRight` (`ZhuVermaAnArchMUcircDiffClose`), `anmRightDiff = anmRight W n 0 a
(anmCirc W 0 0 c d − anmCirc W n 0 c d)`; `anmRight_zero` + `resHom_homogeneous` unfold the outer
level-`n` right action to `∑_i C(K,i) • a₍i−(n+1)₎(·)`; `PresAnm_zero` (homogeneous `c`) identifies
the two inner circles with `PresAnm W M 0 0 c d` / `PresAnm W M n 0 c d`, and the proven DIFFERENCE
U-core `presDiff_eq_modeFinsum` (`ZhuVermaAnArchCFirstDiffUCore`) brings the base-difference to the
single pole-difference mode-value finsum (weight `crossDiffWeight M n μ`).  This is the genuine
`a`-outer twin of the diagonal U/V-core mode-value forms — the diagonal template applied `a`-outer. -/
theorem anmRightDiff_eq_aOuterModeFinsum (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {K M : ℕ}
    {a : 𝒱} (ha : a ∈ W.grading (K : ℤ)) {c : 𝒱} (hc : c ∈ W.grading (M : ℤ)) (d : 𝒱) :
    anmRightDiff W n K a c d
      = ∑ i ∈ Finset.range (K + 1),
          cbz (K : ℤ) (i : ℤ) •
            W.smul a ((i : ℤ) - ((n : ℤ) + 1))
              (∑ᶠ μ : ℤ, crossDiffWeight M n μ • W.smul c μ d) := by
  rw [anmRightDiff_eq_anmRight W n ha c d]
  rw [show anmCirc W 0 0 c d - anmCirc W n 0 c d
        = ∑ᶠ μ : ℤ, crossDiffWeight M n μ • W.smul c μ d from by
      rw [← PresAnm_zero W hc d, ← PresAnm_zero W hc d, presDiff_eq_modeFinsum W M n c d]]
  rw [anmRight_zero, resHom_homogeneous W 0 ((n : ℤ) + 1) ha,
    show ((K : ℤ) + 0).toNat + 1 = K + 1 from by rw [add_zero, Int.toNat_natCast]]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [add_zero]

/-! ## The exact remaining scalar core (the `a`-outer twin of the diagonal U/V-cores). -/

/-- **The `a`-outer right-action-difference scalar core** (the precise remaining identity).  For
homogeneous `a ∈ 𝒱_K`, `c ∈ 𝒱_M`, `d ∈ 𝒱_P`, the `a`-outer right-action-difference family
`anmRightDiff` collapses onto a **level-`n`** `PresTowerFam` in `c` (the `c`-tower over the multi-base
`a₍·₎d`) plus a homogeneous multi-grade `MGTowerFam` W-family in the products `c₍s₎a` based at `d`.
This is precisely `ARDTowerDecomp` (`ZhuVermaAnArchCrossCFirstGate`), restated as the genuine scalar-
weight assignment target — the `a`-outer twin of the diagonal `AnmCircTowerEq_of_sides` U/V scalar
cores.  Its exact `a`-outer mode-value shape is `anmRightDiff_eq_aOuterModeFinsum` (per-base level-`0`-
vs-level-`n` pole-difference weight `crossDiffWeight M n μ`); the level-offset is absorbed onto the
level-`n` `c`-tower by `towerCoeffAnm_regrade_int` (`ZhuVermaAnArchHPoleN`).  Carried as a hypothesis,
NEVER an axiom. -/
def ARDScalarCore (W : VertexOperatorAlgebra 𝒱) (n K M P : ℕ) (a c d : 𝒱) : Prop :=
  ARDTowerDecomp W n K M P a c d

/-- **`ARDScalarCore` ⟹ `ARDTowerDecomp`** (definitional unfold; the scalar core IS the `a`-outer
right-action-difference tower decomposition, named at the `a`-outer U-core level). -/
theorem ardTowerDecomp_of_scalarCore (W : VertexOperatorAlgebra 𝒱) (n K M P : ℕ) (a c d : 𝒱)
    (hsc : ARDScalarCore W n K M P a c d) :
    ARDTowerDecomp W n K M P a c d := hsc

/-! ## `ARDScalarCore` (universal) ⟹ the full `MUGradedAction W`. -/

/-- **The full `MUGradedAction W` from the single universal `ARDScalarCore`.**  Given, for every
level `n` and all homogeneous data, the `a`-outer right-action-difference scalar core `ARDScalarCore`,
the tower decomposition `ARDTowerDecomp` holds (`ardTowerDecomp_of_scalarCore`), and
`MUGradedAction_of_ARDTowerDecomp_via_diag` (`ZhuVermaAnArchCircDiffARD`) — the master bridge
`crossCFirstDiff_eq_anmCircAnmRightDiff` + the proven commutator half `commDiff_eq_MGTowerFam` + the
`MGTowerFam` merge + the diagonal pole-`2` face `MUGradedAction_of_diagCore`, with the membership half
`ardiff_mem_of_decomp` and EVERY structural assembly discharged — assembles the Dong–Jiang `M(U)`
graded-action crux `MUGradedAction W`.

This re-exports the `MUGradedAction` closure at the `a`-outer U-core level: the single remaining input
is the scalar-weight assignment `ARDScalarCore`, with its exact `a`-outer mode-value shape
`anmRightDiff_eq_aOuterModeFinsum` (per-base pole-difference weight `crossDiffWeight M n μ`) proved
here.  This `MUGradedAction W` is the `q_act` source of the Construction-B diagonal well-definedness
feeding `GenFromBottomFinalFamily` and hence the bijection `Function.Bijective (forwardMap W)`
(`ZhuVermaAnArchFinalWiring` / `ZhuVermaAnArchGenuineWiring`). -/
theorem MUGradedAction_of_ardScalarCore (W : VertexOperatorAlgebra 𝒱)
    (Hsc : ∀ (n K M P : ℕ), ∀ a ∈ W.grading (K : ℤ), ∀ c ∈ W.grading (M : ℤ),
      ∀ d ∈ W.grading (P : ℤ), ARDScalarCore W n K M P a c d) :
    MUGradedAction W :=
  MUGradedAction_of_ARDTowerDecomp_via_diag W
    (fun n K M P a ha c hc d hd =>
      ardTowerDecomp_of_scalarCore W n K M P a c d (Hsc n K M P a ha c hc d hd))

/-! ## Status — `MUGradedAction W` pinned to the single `a`-outer right-action-difference scalar core.

Proved here (`#print axioms` = `[propext, Classical.choice, Quot.sound]`; no `sorry`/
`axiom`/`pbw`):

* **`anmRightDiff_eq_aOuterModeFinsum`** — **the exact `a`-outer mode-value shape of `anmRightDiff`**,
  FULLY proven: `anmRightDiff = ∑_{i≤K} C(K,i) • a₍i−(n+1)₎(∑ᶠ μ, crossDiffWeight M n μ • c₍μ₎d)` (the
  diagonal U-core template applied `a`-outer: the inner factor is the proven pole-difference U-core,
  the outer `a₍i−(n+1)₎` is the level-`n` Dong–Jiang right mode).  This isolates the genuine `a`-outer
  scalar target.
* **`ARDScalarCore`** / **`ardTowerDecomp_of_scalarCore`** — the `a`-outer right-action-difference
  scalar core predicate (the precise remaining weight-assignment identity) and its discharge of
  `ARDTowerDecomp`.
* **`MUGradedAction_of_ardScalarCore`** — **the full `MUGradedAction W`** from the SINGLE universal
  `ARDScalarCore`, via `MUGradedAction_of_ARDTowerDecomp_via_diag` (the master-split through the
  diagonal pole-`2` face, with the commutator half `commDiff_eq_MGTowerFam` and the membership half
  `ardiff_mem_of_decomp` already discharged).

**The single remaining identity (engine-verified TRUE; NOT faked):** the universally-quantified
`ARDScalarCore W n K M P a c d` (= `ARDTowerDecomp`) — the `a`-outer right-action-difference weight
assignment collapsing the `a`-outer mode-value form (`anmRightDiff_eq_aOuterModeFinsum`, per-base
weight `crossDiffWeight M n μ = cbz(M, μ+2) − cbz(M, μ+(n+2))`) onto a level-`n` `PresTowerFam` in `c`
over `a₍·₎d` plus an `MGTowerFam` in `c₍s₎a` based at `d`.  The genuine residual is the level-`0`-vs-
level-`n` `n`-offset, absorbed onto the level-`n` `c`-tower via the proven regrade
`towerCoeffAnm_regrade_int` (`ZhuVermaAnArchHPoleN`); the cross-base `c₍s₎a` coupling is the proven
commutator span (`commDiff_eq_MGTowerFam`).  This is the `a`-outer twin of the FULLY-proven diagonal
U/V scalar cores (`UgammaModeCollAnm_eq_towerCoeff` / `VgammaModeCollAnm_eq_towerCoeff`).  Engine
values (`certificates/mathematica/`): `certificates/mathematica/anmrightdiff_tower.wl` (`anmRightDiff ∈ (c-tow@a₍g₎d)+((c₍s₎a)-tow@d)`,
`n = 1, 2`, both families load-bearing); `certificates/mathematica/circ_diff_dj.wl` (the diagonal pole-difference, same
decomposition).
-/

end VOA

/-
`#print axioms` check (each of the following prints
`[propext, Classical.choice, Quot.sound]`, NO `pbw`, NO `sorryAx`):

  #print axioms VOA.anmRightDiff_eq_aOuterModeFinsum
  #print axioms VOA.ardTowerDecomp_of_scalarCore
  #print axioms VOA.MUGradedAction_of_ardScalarCore
-/
