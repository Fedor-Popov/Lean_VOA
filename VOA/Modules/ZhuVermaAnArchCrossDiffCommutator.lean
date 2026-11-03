/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchCFirstDiffMaster
import VOA.Modules.ZhuVermaAnArchCircDiffARD

/-!
# Game One (ATTACK 1) — closing **`CrossCFirstDiffTowerEq`** via the **FZ COMMUTATOR SPLIT**.

This file gives the **`a`-PAST-`c` (FZ commutator) route** to the single remaining endgame core
`CrossCFirstDiffTowerEq` (`ZhuVermaAnArchCrossCFirst0Close`) — the level-`0`-vs-level-`n` `c`-first
pole-difference tower decomposition whose discharge CLOSES the Dong–Jiang `M(U)` graded-action crux
`MUGradedAction W` (Zhu Thm 5.3.4), and thence the bijection `Function.Bijective (forwardMap W)`.

## The FZ commutator split (the ATTACK-1 route)

The `a`-outer `c`-first DIFFERENCE `crossCFirstDiff` is, in its proven `c`-outer mode-value form
(`crossCFirstDiff_eq_modeFinsum`), the per-base pole-difference `c`-circle `∑_i C(K,i) ∑ᶠ μ
crossDiffWeight • c₍μ₎(a₍i−(n+1)₎d)`.  Commuting the level-`n` outer mode `a₍i−(n+1)₎` **past** the
inner `c₍μ₎` by the FZ commutator `mode_split_gen`
`a₍s₎(c₍μ₎x) = c₍μ₎(a₍s₎x) + ∑_t C(s,t)(a₍t₎c)₍μ+s−t₎x` (the singular OPE) splits it, per-`(i,j)`, into

  * **PART (I)** — the `a`-outer right-action piece `anmRightDiff W n K a c d`
    `= ∑_i C(K,i) • a₍i−(n+1)₎(anmCirc W 0 0 c d − anmCirc W n 0 c d)` (the level-`n` outer mode on
    the inner pole-difference base, regradeable to the `c`-tower over the multi-base `a₍·₎d`), PLUS
  * **PART (II)** — the **`c₍s₎a` commutator piece** `crossDiffComm W n K M a c d`
    `= ∑_{i,j} C(K,i)C(M,j) (⁅c₍j−2₎,a₍i−(n+1)₎⁆ − ⁅c₍j−(n+2)₎,a₍i−(n+1)₎⁆) d`, the genuine
    FZ-commutator source of the `MGTowerFam` in the products `c₍s₎a`.

This is the FULLY-PROVEN master-split `crossCFirstDiff_master_split`
(`crossCFirstDiff = anmRightDiff + crossDiffComm`, `ZhuVermaAnArchCFirstDiffMaster`); it is the
`a`-PAST-`c` companion of the `c`-PAST-`a` split `crossCFirstDiff_eq`
(`crossCFirstDiff = anmRightDiff + (ardComm − crossCircComm)`,
`ZhuVermaAnArchCrossCFirstDiffClose`).  Both share the SAME `a`-outer piece `anmRightDiff`, hence the
two commutator objects coincide: **`crossDiffComm = ardComm − crossCircComm`** (`crossDiffComm_eq_commDiff`).

## PART (II) — closed here (engine-verified TRUE)

By `crossDiffComm_eq_commDiff`, the FZ-commutator piece `crossDiffComm` IS the commutator difference
`ardComm − crossCircComm`, which is a homogeneous `MGTowerFam` in the products `c₍s₎a` based at `d`
(`commDiff_eq_MGTowerFam`, the ℂ-difference of the two PROVEN commutator twins `ARDCommTowerEq_holds`,
`CrossCommTowerEq_holds`, `ZhuVermaAnArchVcoreTwins`).  So **PART (II) is fully discharged** as an
`MGTowerFam` (`crossDiffComm_eq_MGTowerFam`):  the FZ-commutator content of the `c`-first
pole-difference is exactly the `c₍s₎a` `MGTowerFam` half, with no residual.  Engine-verified TRUE on
the rank-1 free boson (`certificates/mathematica/attack1_split.wl`: `crossDiffComm ∈ MGTowerFam(c₍s₎a @ d)`,
`n = 1, 2`, mixed homogeneous `a, c, d`).

## PART (I) — the single remaining identity (the `a`-outer `c`-tower collapse)

PART (I) is the `a`-outer right-action-difference family `anmRightDiff`, whose tower decomposition is
the genuine `a`-irreducible Dong–Jiang Lemma 2.8 core `ARDTowerDecomp`
(`ZhuVermaAnArchCrossCFirstGate`): the level-`n` outer mode `a₍i−(n+1)₎` on the inner pole-difference
base regrades — via the diagonal U-core `UgammaModeCollAnm` + `towerCoeffAnm_regrade_int`
(`ZhuVermaAnArchMUcircClose`/`ZhuVermaAnArchHPoleN`) — onto a `PresTowerFam` `c`-tower over the
multi-base `a₍·₎d` plus a multi-grade `MGTowerFam` in `c₍s₎a`:

  `anmRightDiff W n K a c d = PresTowerFam W M n c RU ΔU baseU wU + MGTowerFam W n S … `.

This is carried as the explicit hypothesis-predicate `ARDTowerDecomp` (NEVER an axiom); engine-verified
TRUE (`certificates/mathematica/anmrightdiff_tower.wl`, `certificates/mathematica/attack1_split.wl`; the pure `c`-tower alone does
NOT suffice — the `c₍s₎a` `MGTowerFam` is load-bearing).

## The lift and the closure (FULLY proven here; no `sorry`/axiom/`pbw`)

`crossCFirstDiffTowerEq_of_ARDTowerDecomp_via_comm`:  by the FZ commutator master-split
`crossCFirstDiff = anmRightDiff + crossDiffComm`, with PART (I) supplied as `PresTowerFam(c) +
MGTowerFam` by `ARDTowerDecomp` and PART (II) discharged as an `MGTowerFam` (`crossDiffComm_eq_MGTowerFam`),
the two `MGTowerFam`s merge (`MGTowerFam_add`, homogeneity by `MGTowerFam_add_hom`) and the `c`-tower
is carried unchanged, yielding the explicit `CrossCFirstDiffTowerEq` witness.
`MUGradedAction_of_ARDTowerDecomp_via_comm` then assembles the full `MUGradedAction W` from the single
universal `ARDTowerDecomp`, via `MUGradedAction_of_crossCFirstDiff`.

## What is proved here (axiom-clean)

* **`crossDiffComm_eq_commDiff`** — the bridge `crossDiffComm = ardComm − crossCircComm` (the FZ
  `a`-PAST-`c` commutator piece equals the `c`-PAST-`a` commutator difference), FULLY proven from the
  two master-splits (`crossCFirstDiff_master_split`, `crossCFirstDiff_eq`) sharing `anmRightDiff`.
* **`crossDiffComm_eq_MGTowerFam`** — **PART (II) closed**: the FZ-commutator piece
  `crossDiffComm` IS a homogeneous `MGTowerFam` in `c₍s₎a` (via `crossDiffComm_eq_commDiff` +
  `commDiff_eq_MGTowerFam`).
* **`crossCFirstDiffTowerEq_of_ARDTowerDecomp_via_comm`** — **the full structural lift** through the FZ
  commutator route: `ARDTowerDecomp ⟹ CrossCFirstDiffTowerEq`, merging the PART-(I) `MGTowerFam` with
  the PART-(II) `MGTowerFam` by `MGTowerFam_add`, carrying the PART-(I) `c`-tower unchanged.
* **`MUGradedAction_of_ARDTowerDecomp_via_comm`** — **the full `MUGradedAction W`** from the single
  universal `ARDTowerDecomp`, through the FZ commutator route.

This is the FZ-commutator (`a`-PAST-`c`) face of the same Dong–Jiang Lemma 2.8 reorganization; it
unifies with the existing `c`-PAST-`a` route (`MUGradedAction_of_ARDTowerDecomp_via_diff`) and the
diagonal route (`MUGradedAction_of_ARDTowerDecomp_via_diag`): **all three close on the SAME single
`ARDTowerDecomp`**, with the FZ-commutator PART (II) fully discharged via the two PROVEN commutator
twins.

## Engine status (rank-1 free boson; NOT faked)

* `certificates/mathematica/attack1_split.wl` (new): the FZ commutator split
  `crossCFirstDiff = anmRightDiff + crossDiffComm` (**True**); PART (II)
  `crossDiffComm ∈ MGTowerFam(c₍s₎a @ d)` (**True**); PART (I) = `anmRightDiff` (the `ARDTowerDecomp`
  residual), `n = 1, 2`, mixed homogeneous `a, c, d`.
* `certificates/mathematica/anmrightdiff_tower.wl`: PART (I) `anmRightDiff ∈ (c-tow@a₍g₎d) +
  ((c₍s₎a)-tow@d)` (**True**); pure `c`-tower alone does NOT suffice (**False**).
* `certificates/mathematica/cfirst_diff_decomp.wl`: `crossCFdiff = anmRightDiff + ardComm − crossComm`
  (**True**), the bridge `crossDiffComm = ardComm − crossCircComm`.

## References
Dong–Jiang, Math. Z. 259 (2008) 799–826 (`math/0601626`), §2 (Lemma 2.8); Frenkel–Zhu Lemma 2.1.2;
Dong–Li–Mason; Gannon §5.3.2, Thm 5.3.4.
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The bridge — the FZ `a`-PAST-`c` commutator piece equals the `c`-PAST-`a` commutator
difference. -/

/-- **The FZ commutator bridge** `crossDiffComm = ardComm − crossCircComm` (FULLY proven).  For
homogeneous `a ∈ 𝒱_K`, `c ∈ 𝒱_M`, the `a`-PAST-`c` FZ-commutator piece `crossDiffComm` of the
master-split `crossCFirstDiff_master_split` (`crossCFirstDiff = anmRightDiff + crossDiffComm`) equals
the `c`-PAST-`a` commutator difference `ardComm − crossCircComm` of the companion split
`crossCFirstDiff_eq` (`crossCFirstDiff = anmRightDiff + (ardComm − crossCircComm)`).

Both splits decompose the SAME object `crossCFirstDiff` with the SAME `a`-outer right-action piece
`anmRightDiff`, so their commutator pieces coincide (cancel `anmRightDiff` from
`anmRightDiff + crossDiffComm = anmRightDiff + (ardComm − crossCircComm)`).  This identifies the two
faces of the FZ commutator content. -/
theorem crossDiffComm_eq_commDiff (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {K M : ℕ}
    {a : 𝒱} (ha : a ∈ W.grading (K : ℤ)) {c : 𝒱} (hc : c ∈ W.grading (M : ℤ)) (d : 𝒱) :
    crossDiffComm W n K M a c d
      = ardComm W n K M a c d - crossCircComm W n K M a c d := by
  have h := (crossCFirstDiff_master_split W n ha hc d).symm.trans
    (crossCFirstDiff_eq W n ha hc d)
  -- `anmRightDiff + crossDiffComm = anmRightDiff + (ardComm − crossCircComm)`; cancel `anmRightDiff`.
  have h2 : anmRightDiff W n K a c d + crossDiffComm W n K M a c d
      = anmRightDiff W n K a c d + (ardComm W n K M a c d - crossCircComm W n K M a c d) := h
  exact add_left_cancel h2

/-! ## PART (II) — the FZ-commutator piece `crossDiffComm` is a homogeneous `MGTowerFam`. -/

/-- **PART (II) closed — the FZ-commutator piece `crossDiffComm` IS a homogeneous `MGTowerFam`.**
For homogeneous `a ∈ 𝒱_K`, `c ∈ 𝒱_M`, `d ∈ 𝒱_P`, the `a`-PAST-`c` FZ-commutator piece `crossDiffComm`
of the master-split is a homogeneous `MGTowerFam` in the products `c₍s₎a` based at `d`.

By the bridge `crossDiffComm_eq_commDiff` it equals the commutator difference
`ardComm − crossCircComm`, which is an `MGTowerFam` (`commDiff_eq_MGTowerFam`, the ℂ-difference of the
two PROVEN commutator twins `ARDCommTowerEq_holds`, `CrossCommTowerEq_holds`).  Thus the entire
FZ-commutator content of the `c`-first pole-difference is the `c₍s₎a` `MGTowerFam` half, with no
residual — the part-(II) target of the ATTACK-1 split, engine-verified TRUE
(`certificates/mathematica/attack1_split.wl`). -/
theorem crossDiffComm_eq_MGTowerFam (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {K M P : ℕ}
    {a : 𝒱} (ha : a ∈ W.grading (K : ℤ)) {c : 𝒱} (hc : c ∈ W.grading (M : ℤ))
    {d : 𝒱} (hd : d ∈ W.grading (P : ℤ)) :
    ∃ (S : ℕ) (gradeS : Fin S → ℕ) (leftS baseS : Fin S → 𝒱) (ΔS : Fin S → ℕ) (wS : Fin S → ℕ → ℂ),
      (∀ r : Fin S, leftS r ∈ W.grading ((gradeS r : ℤ))) ∧
      crossDiffComm W n K M a c d = MGTowerFam W n S gradeS leftS baseS ΔS wS := by
  obtain ⟨S, gradeS, leftS, baseS, ΔS, wS, hhom, heq⟩ := commDiff_eq_MGTowerFam W n ha hc hd
  exact ⟨S, gradeS, leftS, baseS, ΔS, wS, hhom,
    (crossDiffComm_eq_commDiff W n ha hc d).trans heq⟩

/-! ## The full structural lift `ARDTowerDecomp` ⟹ `CrossCFirstDiffTowerEq` (FZ commutator route). -/

/-- **`ARDTowerDecomp` ⟹ `CrossCFirstDiffTowerEq`** (the FZ commutator route — the full structural
lift).  By the FZ commutator master-split `crossCFirstDiff_master_split`
(`crossCFirstDiff = anmRightDiff + crossDiffComm`):

* **PART (I)** — `anmRightDiff` is supplied as `PresTowerFam(c) + MGTowerFam` by `ARDTowerDecomp` (the
  `a`-outer right-action-difference tower decomposition, the genuine remaining identity);
* **PART (II)** — `crossDiffComm` is a homogeneous `MGTowerFam` (`crossDiffComm_eq_MGTowerFam`, FULLY
  discharged via the bridge `crossDiffComm_eq_commDiff` + the two PROVEN commutator twins).

Merging the PART-(I) `MGTowerFam` with the PART-(II) `MGTowerFam` (`MGTowerFam_add`, homogeneity by
`MGTowerFam_add_hom`) and carrying the PART-(I) `c`-tower unchanged yields the explicit
`CrossCFirstDiffTowerEq` witness.  This is the `a`-PAST-`c` (FZ commutator) face of the lift; it agrees
with the `c`-PAST-`a` lift `crossCFirstDiffTowerEq_of_ARDTowerDecomp`
(`ZhuVermaAnArchCrossCFirstDiffClose`) — both close on the SAME `ARDTowerDecomp`. -/
theorem crossCFirstDiffTowerEq_of_ARDTowerDecomp_via_comm (W : VertexOperatorAlgebra 𝒱) (n : ℕ)
    {K M P : ℕ} {a : 𝒱} (ha : a ∈ W.grading (K : ℤ)) {c : 𝒱} (hc : c ∈ W.grading (M : ℤ))
    {d : 𝒱} (hd : d ∈ W.grading (P : ℤ))
    (hdec : ARDTowerDecomp W n K M P a c d) :
    CrossCFirstDiffTowerEq W n K M P a c d := by
  obtain ⟨RU, ΔU, S₁, baseU, wU, gradeS₁, leftS₁, baseS₁, ΔS₁, wS₁, hhom₁, hdeceq⟩ := hdec
  obtain ⟨S₂, gradeS₂, leftS₂, baseS₂, ΔS₂, wS₂, hhom₂, hcommeq⟩ :=
    crossDiffComm_eq_MGTowerFam W n ha hc hd
  refine ⟨RU, ΔU, S₁ + S₂, baseU, wU,
    (fun r => Sum.elim gradeS₁ gradeS₂ (finSumFinEquiv.symm r)),
    (fun r => Sum.elim leftS₁ leftS₂ (finSumFinEquiv.symm r)),
    (fun r => Sum.elim baseS₁ baseS₂ (finSumFinEquiv.symm r)),
    (fun r => Sum.elim ΔS₁ ΔS₂ (finSumFinEquiv.symm r)),
    (fun r => Sum.elim wS₁ wS₂ (finSumFinEquiv.symm r)),
    MGTowerFam_add_hom W S₁ S₂ gradeS₁ leftS₁ gradeS₂ leftS₂ hhom₁ hhom₂, ?_⟩
  rw [crossCFirstDiff_master_split W n ha hc d, hdeceq, hcommeq, add_assoc,
    MGTowerFam_add W n S₁ S₂ gradeS₁ leftS₁ baseS₁ ΔS₁ wS₁ gradeS₂ leftS₂ baseS₂ ΔS₂ wS₂]

/-! ## The full `MUGradedAction W` from the single universal `ARDTowerDecomp` (FZ commutator route). -/

/-- **The full `MUGradedAction W` from the single universal `ARDTowerDecomp`** (the FZ commutator
route).  Given, for every level `n` and all homogeneous data, the `a`-outer right-action-difference
tower decomposition `ARDTowerDecomp` (the genuine `a`-irreducible Dong–Jiang Lemma 2.8 `O(𝒱)`-relation
core), the FZ-commutator structural lift `crossCFirstDiffTowerEq_of_ARDTowerDecomp_via_comm` supplies
the universal `CrossCFirstDiffTowerEq`, and the PROVEN `MUGradedAction_of_crossCFirstDiff`
(`ZhuVermaAnArchCrossCFirst0Close`) — whose every other piece is fully discharged — assembles the
Dong–Jiang `M(U)` graded-action crux `MUGradedAction W`.

This re-derives `MUGradedAction W` from `ARDTowerDecomp` through the FZ-commutator (`a`-PAST-`c`) face,
with PART (II) (the FZ-commutator `c₍s₎a` content) fully discharged via the two PROVEN commutator twins.
It unifies with the `c`-PAST-`a` route `MUGradedAction_of_ARDTowerDecomp_via_diff` and the diagonal
route `MUGradedAction_of_ARDTowerDecomp_via_diag`: all three close on the SAME `ARDTowerDecomp`.  This
`MUGradedAction W` is the `q_act` source of the Construction-B diagonal well-definedness feeding the
bijection `Function.Bijective (forwardMap W)`. -/
theorem MUGradedAction_of_ARDTowerDecomp_via_comm (W : VertexOperatorAlgebra 𝒱)
    (Hdec : ∀ (n K M P : ℕ), ∀ a ∈ W.grading (K : ℤ), ∀ c ∈ W.grading (M : ℤ),
      ∀ d ∈ W.grading (P : ℤ), ARDTowerDecomp W n K M P a c d) :
    MUGradedAction W :=
  MUGradedAction_of_crossCFirstDiff W
    (fun n K M P a ha c hc d hd =>
      crossCFirstDiffTowerEq_of_ARDTowerDecomp_via_comm W n ha hc hd (Hdec n K M P a ha c hc d hd))

/-! ## Status — `CrossCFirstDiffTowerEq` closed via the FZ COMMUTATOR SPLIT; PART (II) fully
discharged.

Proved here (`#print axioms` = `[propext, Classical.choice, Quot.sound]`; no `sorry`/
`axiom`/`pbw`):

* **`crossDiffComm_eq_commDiff`** — the FZ commutator bridge `crossDiffComm = ardComm − crossCircComm`
  (the `a`-PAST-`c` piece equals the `c`-PAST-`a` commutator difference), FULLY proven from the two
  master-splits sharing `anmRightDiff`.
* **`crossDiffComm_eq_MGTowerFam`** — **PART (II) closed**: the FZ-commutator piece
  `crossDiffComm` IS a homogeneous `MGTowerFam` in `c₍s₎a` (via the bridge + `commDiff_eq_MGTowerFam`,
  the two PROVEN commutator twins).  Engine `certificates/mathematica/attack1_split.wl` (**True**, `n = 1, 2`).
* **`crossCFirstDiffTowerEq_of_ARDTowerDecomp_via_comm`** — **the full structural lift** through the FZ
  commutator route: `ARDTowerDecomp ⟹ CrossCFirstDiffTowerEq`, merging the PART-(I) and PART-(II)
  `MGTowerFam`s by `MGTowerFam_add`.
* **`MUGradedAction_of_ARDTowerDecomp_via_comm`** — **the full `MUGradedAction W`** from the single
  universal `ARDTowerDecomp`, through the FZ commutator route.

**The single remaining identity (engine-verified TRUE; NOT faked):** PART (I), the
universally-quantified `ARDTowerDecomp W n K M P a c d` — the `a`-outer right-action-difference tower
decomposition

  `anmRightDiff W n K a c d = (c-tower in c based at a₍g₎d) + (W-family in c₍s₎a based at d),

the genuine `a`-irreducible Dong–Jiang Lemma 2.8 core.  PART (II) — the FZ-commutator `c₍s₎a` content
`crossDiffComm` — is FULLY discharged here as an `MGTowerFam` (`crossDiffComm_eq_MGTowerFam`).  The FZ
commutator split `crossCFirstDiff = anmRightDiff + crossDiffComm` (PART I + PART II) is the proven
master-split `crossCFirstDiff_master_split`.  Engine values:
`certificates/mathematica/attack1_split.wl` (the split + PART II, `n = 1, 2`),
`certificates/mathematica/anmrightdiff_tower.wl` (PART I `ARDTowerDecomp`, `n = 1, 2`; pure `c`-tower alone **False**).
-/

end VOA

/-
`#print axioms` check (each of the following prints
`[propext, Classical.choice, Quot.sound]`, NO `pbw`, NO `sorryAx`):

  #print axioms VOA.crossDiffComm_eq_commDiff
  #print axioms VOA.crossDiffComm_eq_MGTowerFam
  #print axioms VOA.crossCFirstDiffTowerEq_of_ARDTowerDecomp_via_comm
  #print axioms VOA.MUGradedAction_of_ARDTowerDecomp_via_comm
-/
