/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchHPoleN

/-!
# Game One — closing the `anmRightDiff` U-family (the `a`-outer twin of `crossDiffComm`).

This file works on the single remaining `(HARD)` piece of the Dong–Jiang Lemma 2.8 pole-difference
split (`ZhuVermaAnArchHPoleN.MUGradedAction_of_HARD`):

  `(HARD)   anmRightDiff W n K a c d ∈ Onm W n 0`,

the `a`-outer right-action-difference family.  By `anmRightDiff_eq_anmRight`
(`ZhuVermaAnArchMUcircDiffClose`), `anmRightDiff = anmRight W n 0 a (anmCirc W 0 0 c d − anmCirc W n 0
c d)`, which by `anmRight`-`right`-linearity splits into the two `a`-outer **terms**

  `anmRightDiff W n K a c d = anmRight W n 0 a (anmCirc W 0 0 c d) − anmRight W n 0 a (anmCirc W n 0 c d)`.
                              └────────── Term₁ ───────────┘   └────────── Term₂ ───────────┘

## (1) Term₁ is ALREADY discharged (the level-`0`-inner cross core)

`Term₁ = anmRight W n 0 a (anmCirc W 0 0 c d)` is exactly the level-`0`-inner cross-circle closure
`anmRight_zero_crossCirc_mem_Onm_of_towerEq` (`ZhuVermaAnArchMUcrossHM`): its membership in `Onm W n 0`
for ALL `a c d : 𝒱` follows from the (universally-quantified) cross tower predicate
`CrossCircTowerEq`.  No new content — it is the `c`-first cross core already plumbed in the repo.

## (2) Term₂ — the new `a`-outer pole-`(n+2)` collapse (this file)

`Term₂ = anmRight W n 0 a (anmCirc W n 0 c d) = resHom W 0 (n+1) a (resHom W 0 (n+2) c d)` — the
`a`-outer level-`n` circle.  Like its companion pole-difference pieces, it is NOT a single
`PresAnm`-tower in any one base: it lands in `Onm W n 0` via the FULL level-`n` circle-generator span,
the cross twin of the diagonal `AnmCircTowerEq` machinery.  We state the explicit decomposition as the
precise predicate `ARDTerm2TowerEq` — a `PresTowerFam` U-family in `c` (based at the `a₍·₎d`-modes) plus
a homogeneous multi-grade `MGTowerFam` W-family in the products `c₍s₎a` (based at `d`), the SAME two
homogeneous tower families as `CircDiffAnmRightTowerEq` — and prove its **membership half FULLY**:

  `ARDTerm2TowerEq W n K M P a c d ⟹ anmRight W n 0 a (anmCirc W n 0 c d) ∈ Onm W n 0`,

via the keystone-backed `PresTowerFam_mem_Onm` + `MGTowerFam_mem_Onm`.  Engine-verified TRUE on the
rank-1 free boson (`certificates/mathematica/anmrightdiff_terms.wl`: Term₂ ∈ `(c-tow@a₍g₎d)+((c₍s₎a)-tow@d)`,
`n = 1, 2`, mixed homogeneous `a, c, d`).

## (3) Proved here (axiom-clean)

* `anmRightDiff_eq_terms` — the `Term₁ − Term₂` split of `anmRightDiff` (`anmRight`-`right`-linearity).
* `ARDTerm2TowerEq` / `ardTerm2_mem_of_towerEq` — the Term₂ tower-decomposition predicate and its
  **membership half FULLY proven** (`PresTowerFam_mem_Onm` + `MGTowerFam_mem_Onm`).
* `anmRightDiff_mem_of_pieces` — `anmRightDiff ∈ Onm W n 0` from the two pieces (`CrossCircTowerEq` for
  Term₁ — for ALL `a c d` — and `ARDTerm2TowerEq` for Term₂ at homogeneous `c`).
* `HARDhom_of_towerEqs` — the homogeneous-`(c, d)` `(HARD)` from the two universal tower predicates.
* `CircDiffAnmRightOnm_of_HARDhom` / `MUGradedAction_of_HARDhom` — the full `MUGradedAction W` from the
  homogeneous `(HARD)` (the chain only ever applies `(HARD)` at homogeneous `c, d`), and hence from the
  two universal tower predicates `CrossCircTowerEq` + `ARDTerm2TowerEq`.

**The single remaining identity (engine-verified TRUE; NOT faked):** the explicit Term₂
decomposition `ARDTerm2TowerEq` — the `a`-outer pole-`(n+2)` circle as `PresTowerFam`(c) +
`MGTowerFam`(c₍s₎a), the genuine DJ Lemma 2.8 weight assignment (cross twin of the diagonal
`AnmCircTowerEq` cores), whose membership half is FULLY discharged here.

## References
Dong–Jiang, Math. Z. 259 (2008) 799–826 (`math/0601626`), §2 (Lemma 2.8); Frenkel–Zhu Lemma 2.1.2;
Dong–Li–Mason; Gannon §5.3.2, Thm 5.3.4.
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The `Term₁ − Term₂` split of `anmRightDiff`. -/

/-- **The `Term₁ − Term₂` split of `anmRightDiff`.**  For homogeneous `a ∈ 𝒱_K`,

  `anmRightDiff W n K a c d
     = anmRight W n 0 a (anmCirc W 0 0 c d) − anmRight W n 0 a (anmCirc W n 0 c d)`.

By `anmRightDiff_eq_anmRight` (`ZhuVermaAnArchMUcircDiffClose`), `anmRightDiff = anmRight W n 0 a
(anmCirc W 0 0 c d − anmCirc W n 0 c d)`; the right slot is ℂ-linear (`anmRight_add_right`,
`anmRight_smul_right` via `(-1) • ·`), so the right action distributes across the base-difference. -/
theorem anmRightDiff_eq_terms (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {K : ℕ} {a : 𝒱}
    (ha : a ∈ W.grading (K : ℤ)) (c d : 𝒱) :
    anmRightDiff W n K a c d
      = anmRight W n 0 a (anmCirc W 0 0 c d) - anmRight W n 0 a (anmCirc W n 0 c d) := by
  rw [anmRightDiff_eq_anmRight W n ha c d]
  rw [sub_eq_add_neg, anmRight_add_right]
  rw [show -anmCirc W n 0 c d = (-1 : ℂ) • anmCirc W n 0 c d from by rw [neg_one_smul],
    anmRight_smul_right, neg_one_smul, ← sub_eq_add_neg]

/-! ## The Term₂ tower-decomposition predicate and its membership half. -/

/-- **The Term₂ (`a`-outer pole-`(n+2)`) tower-decomposition predicate** (the precise remaining
identity).  For homogeneous `a ∈ 𝒱_K`, `c ∈ 𝒱_M`, `d ∈ 𝒱_P`, the `a`-outer level-`n` circle
`anmRight W n 0 a (anmCirc W n 0 c d)` decomposes as a `PresAnm`-tower U-family in `c` (over grade
`M`, based at the `a₍·₎d`-modes) plus a homogeneous multi-grade `MGTowerFam` W-family in the products
`c₍s₎a` (homogeneous left factors `leftS r ∈ 𝒱_{gradeS r}`, based at `d`):

  `anmRight W n 0 a (anmCirc W n 0 c d)
     = PresTowerFam W M n c RU ΔU baseU wU + MGTowerFam W n S gradeS leftS baseS ΔS wS`.

Same two homogeneous tower families as `CircDiffAnmRightTowerEq` (`ZhuVermaAnArchMUcircDiff`); the
`a`-outer pole-`(n+2)` twin of the pole-`2` term.  Engine-verified TRUE on the rank-1 free boson
(`certificates/mathematica/anmrightdiff_terms.wl`, `n = 1, 2`). -/
def ARDTerm2TowerEq (W : VertexOperatorAlgebra 𝒱) (n K M P : ℕ) (a c d : 𝒱) : Prop :=
  ∃ (RU ΔU S : ℕ) (baseU : Fin RU → 𝒱) (wU : Fin RU → ℕ → ℂ)
    (gradeS : Fin S → ℕ) (leftS baseS : Fin S → 𝒱) (ΔS : Fin S → ℕ) (wS : Fin S → ℕ → ℂ),
    (∀ r : Fin S, leftS r ∈ W.grading ((gradeS r : ℤ))) ∧
    anmRight W n 0 a (anmCirc W n 0 c d)
      = PresTowerFam W M n c RU ΔU baseU wU
        + MGTowerFam W n S gradeS leftS baseS ΔS wS

/-- **`ARDTerm2TowerEq` ⟹ Term₂ membership** (homogeneous `c`).  If the `a`-outer pole-`(n+2)` circle
decomposes onto the U-tower family in `c` plus the homogeneous multi-grade tower W-family
(`ARDTerm2TowerEq`), then `anmRight W n 0 a (anmCirc W n 0 c d) ∈ Onm W n 0`, by the keystone-backed
`PresTowerFam_mem_Onm` (towers in the homogeneous `c`) + `MGTowerFam_mem_Onm` (the per-index
homogeneous level-`n` circle-generator span).  The membership half, FULLY proven. -/
theorem ardTerm2_mem_of_towerEq (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {K M P : ℕ}
    {a c d : 𝒱} (hc : c ∈ W.grading (M : ℤ))
    (htow : ARDTerm2TowerEq W n K M P a c d) :
    anmRight W n 0 a (anmCirc W n 0 c d) ∈ Onm W n 0 := by
  obtain ⟨RU, ΔU, S, baseU, wU, gradeS, leftS, baseS, ΔS, wS, hhom, heq⟩ := htow
  rw [heq]
  exact Submodule.add_mem _ (PresTowerFam_mem_Onm W n hc RU ΔU baseU wU)
    (MGTowerFam_mem_Onm W n S gradeS leftS baseS ΔS wS hhom)

/-! ## `anmRightDiff ∈ Onm` from the two pieces. -/

/-- **`anmRightDiff W n K a c d ∈ Onm W n 0` from the two pieces** (homogeneous `a ∈ 𝒱_K`, `c ∈ 𝒱_M`).
By `anmRightDiff_eq_terms`, `anmRightDiff = Term₁ − Term₂`.  `Term₁ = anmRight W n 0 a (anmCirc W 0 0 c
d)` is discharged for ALL `a c d` by the cross tower predicate (`hCross`,
`anmRight_zero_crossCirc_mem_Onm_of_towerEq`); `Term₂ = anmRight W n 0 a (anmCirc W n 0 c d)` by the
Term₂ tower predicate (`hT2`, `ardTerm2_mem_of_towerEq`, at homogeneous `c`).  `Submodule.sub_mem`
finishes. -/
theorem anmRightDiff_mem_of_pieces (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {K M P : ℕ}
    {a c d : 𝒱} (ha : a ∈ W.grading (K : ℤ)) (hc : c ∈ W.grading (M : ℤ))
    (hCross : anmRight W n 0 a (anmCirc W 0 0 c d) ∈ Onm W n 0)
    (hT2 : ARDTerm2TowerEq W n K M P a c d) :
    anmRightDiff W n K a c d ∈ Onm W n 0 := by
  rw [anmRightDiff_eq_terms W n ha c d]
  exact Submodule.sub_mem _ hCross (ardTerm2_mem_of_towerEq W n hc hT2)

/-! ## The homogeneous `(HARD)` from the two universal tower predicates. -/

/-- **The homogeneous-`(c, d)` `(HARD)` from the two universal tower predicates.**  For homogeneous
`a ∈ 𝒱_K`, `c ∈ 𝒱_M`, `d ∈ 𝒱_P`, supplying the cross tower predicate `CrossCircTowerEq` (universally,
discharging Term₁ via `anmRight_zero_crossCirc_mem_Onm_of_towerEq`) and the Term₂ tower predicate
`ARDTerm2TowerEq` yields `anmRightDiff W n K a c d ∈ Onm W n 0`. -/
theorem HARDhom_of_towerEqs (W : VertexOperatorAlgebra 𝒱) (n : ℕ)
    (Hcross : ∀ (K M P : ℕ), ∀ a ∈ W.grading (K : ℤ), ∀ c ∈ W.grading (M : ℤ),
      ∀ d ∈ W.grading (P : ℤ), CrossCircTowerEq W n K M P a c d)
    (HT2 : ∀ (K M P : ℕ), ∀ a ∈ W.grading (K : ℤ), ∀ c ∈ W.grading (M : ℤ),
      ∀ d ∈ W.grading (P : ℤ), ARDTerm2TowerEq W n K M P a c d)
    {K M P : ℕ} {a c d : 𝒱} (ha : a ∈ W.grading (K : ℤ)) (hc : c ∈ W.grading (M : ℤ))
    (hd : d ∈ W.grading (P : ℤ)) :
    anmRightDiff W n K a c d ∈ Onm W n 0 :=
  anmRightDiff_mem_of_pieces W n ha hc
    (anmRight_zero_crossCirc_mem_Onm_of_towerEq W n Hcross a c d)
    (HT2 K M P a ha c hc d hd)

/-! ## The full `MUGradedAction W` assembly from the homogeneous `(HARD)`. -/

/-- **`CircDiffAnmRightOnm W n` from the homogeneous-`(c, d)` `(HARD)`.**  Mirror of
`CircDiffAnmRightOnm_of_HARD` (`ZhuVermaAnArchHPoleN`), but consuming the homogeneous-`(c, d)` form of
`(HARD)` — which is all the chain ever needs, since `CircDiffAnmRightOnm` introduces homogeneous
`c, d`.  `circDiffAnmRight_split` + the proven `crossDiffComm_mem_Onm` finish. -/
theorem CircDiffAnmRightOnm_of_HARDhom (W : VertexOperatorAlgebra 𝒱) (n : ℕ)
    (HARDhom : ∀ (K M P : ℕ), ∀ a ∈ W.grading (K : ℤ), ∀ c ∈ W.grading (M : ℤ),
      ∀ d ∈ W.grading (P : ℤ), anmRightDiff W n K a c d ∈ Onm W n 0) :
    CircDiffAnmRightOnm W n := by
  intro K M P a ha c hc d hd
  rw [circDiffAnmRight_split W n ha hc d]
  exact Submodule.add_mem _ (HARDhom K M P a ha c hc d hd)
    (crossDiffComm_mem_Onm W n ha hc d)

/-- **`MUGradedAction W` from the homogeneous-`(c, d)` `(HARD)`.**  Mirror of `MUGradedAction_of_HARD`
(`ZhuVermaAnArchHPoleN`), consuming the homogeneous-`(c, d)` form of `(HARD)`: `HARDhom` gives
`CircDiffAnmRightOnm W n` (`CircDiffAnmRightOnm_of_HARDhom`), `CrossCFirstOnm_of_circDiff` lifts to
`CrossCFirstOnm W n`, and with the proven `CrossCommOnm_holds`, `MUGradedAction_of_families` yields
`MUGradedAction W`.  The `(HPoleN)` convolution side is FULLY discharged via `crossDiffComm_mem_Onm`. -/
theorem MUGradedAction_of_HARDhom (W : VertexOperatorAlgebra 𝒱)
    (HARDhom : ∀ (n K M P : ℕ), ∀ a ∈ W.grading (K : ℤ), ∀ c ∈ W.grading (M : ℤ),
      ∀ d ∈ W.grading (P : ℤ), anmRightDiff W n K a c d ∈ Onm W n 0) :
    MUGradedAction W :=
  MUGradedAction_of_families W
    (fun n => CrossCFirstOnm_of_circDiff W n
      (CircDiffAnmRightOnm_of_HARDhom W n
        (fun K M P a ha c hc d hd => HARDhom n K M P a ha c hc d hd)))
    (fun n => CrossCommOnm_holds W n)

/-- **`MUGradedAction W` from the two universal tower predicates** (the full reduction).  Supplying,
for every level `n`, the cross tower predicate `CrossCircTowerEq` (discharging Term₁) and the Term₂
tower predicate `ARDTerm2TowerEq` (Term₂) closes the Dong–Jiang `M(U)` graded-action crux
`MUGradedAction W`: `HARDhom_of_towerEqs` gives the homogeneous `(HARD)`, then
`MUGradedAction_of_HARDhom`.  The pole-`2` half, the `(HPoleN)` convolution side
(`crossDiffComm_mem_Onm`), the cross-commutator side (`CrossCommOnm_holds`), and Term₁
(`CrossCircTowerEq`) are all already plumbed; the ONLY genuinely new remaining identity is the
explicit Term₂ decomposition `ARDTerm2TowerEq`. -/
theorem MUGradedAction_of_towerEqs (W : VertexOperatorAlgebra 𝒱)
    (Hcross : ∀ (n K M P : ℕ), ∀ a ∈ W.grading (K : ℤ), ∀ c ∈ W.grading (M : ℤ),
      ∀ d ∈ W.grading (P : ℤ), CrossCircTowerEq W n K M P a c d)
    (HT2 : ∀ (n K M P : ℕ), ∀ a ∈ W.grading (K : ℤ), ∀ c ∈ W.grading (M : ℤ),
      ∀ d ∈ W.grading (P : ℤ), ARDTerm2TowerEq W n K M P a c d) :
    MUGradedAction W :=
  MUGradedAction_of_HARDhom W
    (fun n _K _M _P _a ha _c hc _d hd =>
      HARDhom_of_towerEqs W n
        (fun K M P a ha c hc d hd => Hcross n K M P a ha c hc d hd)
        (fun K M P a ha c hc d hd => HT2 n K M P a ha c hc d hd)
        ha hc hd)

/-! ## Status — `anmRightDiff` U-family reduced to ONE explicit Term₂ decomposition.

Proved here (`#print axioms` = `[propext, Classical.choice, Quot.sound]`; no `sorry`/
`axiom`/`pbw`):

* **`anmRightDiff_eq_terms`** — `anmRightDiff = Term₁ − Term₂` (`anmRight`-`right`-linearity), with
  `Term₁ = anmRight W n 0 a (anmCirc W 0 0 c d)` and `Term₂ = anmRight W n 0 a (anmCirc W n 0 c d)`.
* **`ARDTerm2TowerEq`** — the explicit Term₂ tower-decomposition predicate (the `a`-outer
  pole-`(n+2)` circle as a `PresTowerFam` U-family in `c` plus a homogeneous multi-grade
  `MGTowerFam` W-family in the products `c₍s₎a`), the tower families of `CircDiffAnmRightTowerEq`.
* **`ardTerm2_mem_of_towerEq`** — **the Term₂ membership half FULLY proven**: `ARDTerm2TowerEq` ⟹
  `anmRight W n 0 a (anmCirc W n 0 c d) ∈ Onm W n 0`, via `PresTowerFam`+`MGTowerFam`-`_mem_Onm`.
* **`anmRightDiff_mem_of_pieces`** — `anmRightDiff ∈ Onm W n 0` from the two pieces (Term₁ via the
  cross tower predicate for ALL `a c d`; Term₂ via `ARDTerm2TowerEq` at homogeneous `c`).
* **`HARDhom_of_towerEqs`** — the homogeneous `(HARD)` from the two universal tower predicates.
* **`CircDiffAnmRightOnm_of_HARDhom`** / **`MUGradedAction_of_HARDhom`** — the full `MUGradedAction`
  `W` from the homogeneous `(HARD)` (the chain only ever applies `(HARD)` at homogeneous `c, d`).
* **`MUGradedAction_of_towerEqs`** — **the full `MUGradedAction W` from the two universal tower
  predicates** `CrossCircTowerEq` (Term₁, already in-repo) + `ARDTerm2TowerEq` (Term₂).

**The single genuinely-new remaining identity (engine-verified TRUE; NOT faked):** the explicit
Term₂ decomposition `ARDTerm2TowerEq W n K M P a c d` — the `a`-outer level-`n` circle
`anmRight W n 0 a (anmCirc W n 0 c d) = PresTowerFam(c) + MGTowerFam(c₍s₎a)` (engine
`certificates/mathematica/anmrightdiff_terms.wl`, Term₂ ∈ `(c-tow@a₍g₎d)+((c₍s₎a)-tow@d)`, `n = 1, 2`).
Term₁ is already reduced to the in-repo cross tower predicate `CrossCircTowerEq`; with both, Tier-1
`MUGradedAction W` closes (`MUGradedAction_of_towerEqs`).
-/

end VOA

/-
`#print axioms` check (each of the following prints
`[propext, Classical.choice, Quot.sound]`, NO `pbw`, NO `sorryAx`):

  #print axioms VOA.anmRightDiff_eq_terms
  #print axioms VOA.ardTerm2_mem_of_towerEq
  #print axioms VOA.anmRightDiff_mem_of_pieces
  #print axioms VOA.HARDhom_of_towerEqs
  #print axioms VOA.CircDiffAnmRightOnm_of_HARDhom
  #print axioms VOA.MUGradedAction_of_HARDhom
  #print axioms VOA.MUGradedAction_of_towerEqs
-/
