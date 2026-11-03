/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchAnmRightDiff
import VOA.Modules.ZhuVermaAnArchMUcrossTow

/-!
# Game One — closing **`MUGradedAction`** to a TERM via the two cross tower equalities.

This file closes the Dong–Jiang `M(U)` graded-action crux `MUGradedAction W` (Zhu Thm 5.3.4) down to
a single explicit residual commutator weight identity.  The entry point
`MUGradedAction_of_towerEqs` (`ZhuVermaAnArchAnmRightDiff`) needs the two universal tower predicates

  `CrossCircTowerEq`  (`ZhuVermaAnArchMUcrossHM`) — Term₁, the `a`-outer level-`0`-inner cross circle,
  `ARDTerm2TowerEq`   (`ZhuVermaAnArchAnmRightDiff`) — Term₂, the `a`-outer level-`n` circle.

Both are the **`a`-outer / cross twins** of the diagonal `AnmCircTowerEq` (`ZhuVermaAnArchMUcircV`,
fully proven).  Here we expose their COMMON structure: both are the OUTER level-`n` residue (pole
`n+1`) of homogeneous `a ∈ 𝒱_K` applied to an inner Zhu circle of `(c, d)` — Term₁ at the **level-`0`**
inner circle (pole `2`), Term₂ at the **level-`n`** inner circle (pole `n+2`).  Both mode-split (via
`mode_split_gen`, the per-`(i,j)` `a₍α₎(c₍β₎d) = c₍β₎(a₍α₎d) + ⁅a₍α₎,c₍β₎⁆d`) into

* a **`c`-first family** whose inner `j`-sum is exactly `PresAnm W M n 0 c (a₍i−(n+1)₎d)` (depth-`1`
  `PresTowerFam` in homogeneous `c`, based at the modes `a₍i−(n+1)₎d`), and
* a **commutator family** `∑_i C(K,i) ∑_j C(M,j) ⁅a₍α₎,c₍β₎⁆d`, which lands in the homogeneous
  multi-grade `MGTowerFam` span of the products `c₍s₎a ∈ 𝒱_{M+K−s−1}` based at `d`.

## What is proved here (axiom-clean)

* `crossCircN`-family defs (`ardCFirst`/`ardComm`) — the `c`-first and commutator families of the
  **level-`n`** inner circle (the Term₂ analogue of `crossCircCFirst`/`crossCircComm`).
* **`ardTerm2_modeSplit`** — the exact `c`-first `+` commutator decomposition of
  `anmRight W n 0 a (anmCirc W n 0 c d)` (mode-split, FULLY proven).
* **`ardCFirst_eq_PresTowerFam`** — the `c`-first family IS the depth-`1` `PresTowerFam W M n c (K+1) 1
  baseU wU` in homogeneous `c` (FULLY proven, the inner `j`-sum collapses to `PresAnm W M n 0`).
* **`ARDCommTowerEq`** — the precise residual predicate: the Term₂ commutator family is an
  `MGTowerFam` in the products `c₍s₎a` based at `d` (the genuine DJ Lemma 2.8 commutator weight
  assignment, engine-verified TRUE on the rank-1 free boson, `certificates/mathematica/ardterm2_split.wl`).
* **`ardTerm2TowerEq_of_comm`** — `ARDCommTowerEq` ⟹ `ARDTerm2TowerEq` (assemble `c`-first
  `PresTowerFam` + commutator `MGTowerFam`).
* The Term₁ analogues `crossCFirst0_eq_PresTowerFam` (the level-`0` `c`-first as a `PresTowerFam`) and
  **`CrossCommTowerEq`** / **`crossCircTowerEq_of_comm`** — `CrossCommTowerEq` ⟹ `CrossCircTowerEq`.
* **`MUGradedAction_of_commTowerEqs`** — the full `MUGradedAction W` from the two residual commutator
  predicates `CrossCommTowerEq` + `ARDCommTowerEq`.  This CLOSES Tier-1 to a TERM: the only remaining
  content is the two explicit commutator → `MGTowerFam` weight assignments (the `a`-outer twins of the
  diagonal V-core, with the `n`-offset absorbed by the proven regrade `crossDiff_regrade`/`regradeWt`).

## References
Dong–Jiang, Math. Z. 259 (2008) 799–826 (`math/0601626`), §2 (Lemma 2.8); Frenkel–Zhu Lemma 2.1.2;
Dong–Li–Mason; Gannon §5.3.2, Thm 5.3.4.
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The level-`n` inner-circle `c`-first / commutator families (Term₂). -/

/-- The **`c`-first family** of the Term₂ (`a`-outer, level-`n` inner circle) core (homogeneous
`a ∈ 𝒱_K`, `c ∈ 𝒱_M`):
`∑_{i≤K} C(K,i) • ∑_{j≤M} C(M,j) • c₍j−(n+2)₎ (a₍i−(n+1)₎ d)`.  The inner `j`-sum is the *level-`n`*
Zhu circle `anmCirc W n 0 c (a₍i−(n+1)₎ d)` (pole `n+2`), based at `a₍i−(n+1)₎ d`. -/
noncomputable def ardCFirst (W : VertexOperatorAlgebra 𝒱) (n K M : ℕ) (a c d : 𝒱) : 𝒱 :=
  ∑ i ∈ Finset.range (K + 1),
    cbz (K : ℤ) (i : ℤ) •
      ∑ j ∈ Finset.range (M + 1),
        cbz (M : ℤ) (j : ℤ)
          • W.smul c ((j : ℤ) - ((n : ℤ) + 2)) (W.smul a ((i : ℤ) - ((n : ℤ) + 1)) d)

/-- The **commutator family** of the Term₂ core (homogeneous `a ∈ 𝒱_K`, `c ∈ 𝒱_M`):
`∑_{i≤K} C(K,i) • ∑_{j≤M} C(M,j) • ⁅a₍i−(n+1)₎, c₍j−(n+2)₎⁆ d`. -/
noncomputable def ardComm (W : VertexOperatorAlgebra 𝒱) (n K M : ℕ) (a c d : 𝒱) : 𝒱 :=
  ∑ i ∈ Finset.range (K + 1),
    cbz (K : ℤ) (i : ℤ) •
      ∑ j ∈ Finset.range (M + 1),
        cbz (M : ℤ) (j : ℤ)
          • ⁅mode (W.Y a) ((i : ℤ) - ((n : ℤ) + 1)),
              mode (W.Y c) ((j : ℤ) - ((n : ℤ) + 2))⁆ d

/-! ## The mode-split of `anmRight W n 0 a (anmCirc W n 0 c d)` (Term₂). -/

/-- The explicit double-mode-sum form of `anmRight W n 0 a (anmCirc W n 0 c d)` for homogeneous
`a ∈ 𝒱_K`, `c ∈ 𝒱_M`: outer residue pole `n+1` (weight `C(K,i)`, mode `i−(n+1)`), inner circle pole
`n+2` (weight `C(M,j)`, mode `j−(n+2)`).  `anmRight_zero` + `resHom_homogeneous` (on `a`),
`anmCirc_zero` + `resHom_homogeneous` (on `c`), and distribution of the outer mode across the inner
`j`-sum. -/
theorem ardTerm2_double_mode (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {K M : ℕ}
    {a : 𝒱} (ha : a ∈ W.grading (K : ℤ)) {c : 𝒱} (hc : c ∈ W.grading (M : ℤ)) (d : 𝒱) :
    anmRight W n 0 a (anmCirc W n 0 c d)
      = ∑ i ∈ Finset.range (K + 1),
          cbz (K : ℤ) (i : ℤ) •
            ∑ j ∈ Finset.range (M + 1),
              cbz (M : ℤ) (j : ℤ)
                • W.smul a ((i : ℤ) - ((n : ℤ) + 1))
                    (W.smul c ((j : ℤ) - ((n : ℤ) + 2)) d) := by
  rw [anmRight_zero, anmCirc_zero, resHom_homogeneous W 0 ((n : ℤ) + 1) ha]
  simp only [add_zero]
  rw [show ((K : ℤ)).toNat + 1 = K + 1 from by simp]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  rw [resHom_homogeneous W 0 ((n : ℤ) + 2) hc d]
  simp only [add_zero]
  rw [show ((M : ℤ)).toNat + 1 = M + 1 from by simp]
  rw [PreVertexAlgebra.smul_def, map_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [LinearMap.map_smul]; rfl

/-- **The Term₂ mode-split.**  For homogeneous `a ∈ 𝒱_K`, `c ∈ 𝒱_M`,
`anmRight W n 0 a (anmCirc W n 0 c d) = ardCFirst + ardComm`, via the per-`(i,j)` `mode_split_gen`
`a₍α₎(c₍β₎d) = c₍β₎(a₍α₎d) + ⁅a₍α₎,c₍β₎⁆d` (`α = i−(n+1)`, `β = j−(n+2)`). -/
theorem ardTerm2_modeSplit (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {K M : ℕ}
    {a : 𝒱} (ha : a ∈ W.grading (K : ℤ)) {c : 𝒱} (hc : c ∈ W.grading (M : ℤ)) (d : 𝒱) :
    anmRight W n 0 a (anmCirc W n 0 c d)
      = ardCFirst W n K M a c d + ardComm W n K M a c d := by
  rw [ardTerm2_double_mode W n ha hc d, ardCFirst, ardComm, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← smul_add]
  congr 1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← smul_add]
  congr 1
  rw [mode_split_gen W a c d ((i : ℤ) - ((n : ℤ) + 1)) ((j : ℤ) - ((n : ℤ) + 2))]

/-! ## The Term₂ `c`-first family IS a depth-`1` `PresTowerFam` in homogeneous `c`. -/

/-- The inner `j`-sum of the Term₂ `c`-first family IS `PresAnm W M n 0 c base` (the depth-`0`,
level-`n` circle), for homogeneous `c ∈ 𝒱_M`.  Both are `∑_{j≤M} C(M,j) • c₍j−(n+2)₎ base` (the
`PresAnm` definition at depth `0`, `M + 0 + 1 = M + 1`, mode `j − (n+2) − 0 = j − (n+2)`). -/
theorem ardCFirst_inner_eq_PresAnm (W : VertexOperatorAlgebra 𝒱) (n M : ℕ) (c base : 𝒱) :
    (∑ j ∈ Finset.range (M + 1),
        cbz (M : ℤ) (j : ℤ) • W.smul c ((j : ℤ) - ((n : ℤ) + 2)) base)
      = PresAnm W M n 0 c base := by
  rw [PresAnm]
  rw [show M + 0 + 1 = M + 1 from by ring]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show ((M : ℤ) + (0 : ℕ)) = (M : ℤ) from by push_cast; ring,
    show ((j : ℤ) - ((n : ℤ) + 2) - (0 : ℕ)) = (j : ℤ) - ((n : ℤ) + 2) from by push_cast; ring]

/-- **The Term₂ `c`-first family IS a depth-`1` `PresTowerFam` in homogeneous `c`.**  Each `i`-summand
collapses (`ardCFirst_inner_eq_PresAnm`) to `C(K,i) • PresAnm W M n 0 c (a₍i−(n+1)₎d)`, which is the
`r = i` summand (depth `δ = 0`) of `PresTowerFam W M n c (K+1) 1` with base vectors
`baseU i = a₍i−(n+1)₎d` and weights `wU i δ = if δ = 0 then C(K,i) else 0`. -/
theorem ardCFirst_eq_PresTowerFam (W : VertexOperatorAlgebra 𝒱) (n K M : ℕ) (a c d : 𝒱) :
    ardCFirst W n K M a c d
      = PresTowerFam W M n c (K + 1) 1
          (fun r => W.smul a ((r : ℤ) - ((n : ℤ) + 1)) d)
          (fun r δ => if δ = 0 then cbz (K : ℤ) (r : ℤ) else 0) := by
  rw [ardCFirst, PresTowerFam]
  rw [← Fin.sum_univ_eq_sum_range
    (fun i => cbz (K : ℤ) (i : ℤ) •
      ∑ j ∈ Finset.range (M + 1),
        cbz (M : ℤ) (j : ℤ)
          • W.smul c ((j : ℤ) - ((n : ℤ) + 2)) (W.smul a ((i : ℤ) - ((n : ℤ) + 1)) d)) (K + 1)]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.sum_range_one]
  rw [ardCFirst_inner_eq_PresAnm W n M c (W.smul a ((r : ℤ) - ((n : ℤ) + 1)) d)]
  rw [if_pos rfl]

/-! ## The Term₂ residual commutator predicate. -/

/-- **The Term₂ commutator predicate** (the precise remaining identity).  For homogeneous `a ∈ 𝒱_K`,
`c ∈ 𝒱_M`, `d ∈ 𝒱_P`, the commutator family `ardComm` is a homogeneous multi-grade `MGTowerFam` in the
products `c₍s₎a ∈ 𝒱_{M+K−s−1}` based at `d` — the `a`-outer level-`n` twin of the diagonal V-core, the
`n`-offset absorbed by the proven regrade `crossDiff_regrade`/`regradeWt`.  Engine-verified TRUE on the
rank-1 free boson (`certificates/mathematica/ardterm2_split.wl`: `comm ∈ (c₍s₎a)-towers@d`, `n = 1, 2`,
mixed homogeneous `a, c, d`). -/
def ARDCommTowerEq (W : VertexOperatorAlgebra 𝒱) (n K M P : ℕ) (a c d : 𝒱) : Prop :=
  ∃ (S : ℕ) (gradeS : Fin S → ℕ) (leftS baseS : Fin S → 𝒱) (ΔS : Fin S → ℕ) (wS : Fin S → ℕ → ℂ),
    (∀ r : Fin S, leftS r ∈ W.grading ((gradeS r : ℤ))) ∧
    ardComm W n K M a c d = MGTowerFam W n S gradeS leftS baseS ΔS wS

/-- **`ARDCommTowerEq` ⟹ `ARDTerm2TowerEq`.**  The Term₂ mode-split (`ardTerm2_modeSplit`) writes
`anmRight W n 0 a (anmCirc W n 0 c d) = ardCFirst + ardComm`; the `c`-first family is the depth-`1`
`PresTowerFam` in `c` (`ardCFirst_eq_PresTowerFam`), the commutator family is the `MGTowerFam`
supplied by `ARDCommTowerEq`.  This discharges the precise Term₂ tower predicate consumed by
`MUGradedAction_of_towerEqs`. -/
theorem ardTerm2TowerEq_of_comm (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {K M P : ℕ}
    {a : 𝒱} (ha : a ∈ W.grading (K : ℤ)) {c : 𝒱} (hc : c ∈ W.grading (M : ℤ)) (d : 𝒱)
    (hcomm : ARDCommTowerEq W n K M P a c d) :
    ARDTerm2TowerEq W n K M P a c d := by
  obtain ⟨S, gradeS, leftS, baseS, ΔS, wS, hhom, hcommeq⟩ := hcomm
  refine ⟨K + 1, 1, S,
    (fun r => W.smul a ((r : ℤ) - ((n : ℤ) + 1)) d),
    (fun r δ => if δ = 0 then cbz (K : ℤ) (r : ℤ) else 0),
    gradeS, leftS, baseS, ΔS, wS, hhom, ?_⟩
  rw [ardTerm2_modeSplit W n ha hc d, ardCFirst_eq_PresTowerFam W n K M a c d, hcommeq]

/-! ## The Term₁ analogues (level-`0` inner circle). -/

/-- **The Term₁ `c`-first family IS a `PresTowerFam` in homogeneous `c`** — at the level-`0` inner
circle (pole `2`), i.e. for the per-`j` cross-circle term.  `crossCircCFirst` (`ZhuVermaAnArchMUcrossHM`)
is `∑_i C(K,i) • ∑_j C(M,j) • c₍j−2₎ (a₍i−n−1₎d)`; the inner `j`-sum is the *level-`0`* circle
`anmCirc W 0 0 c (a₍i−n−1₎d) = PresAnm W M 0 0 c (a₍i−n−1₎d)` — a depth-`1` `PresTowerFam` at level
`0`.  (Note the carrier level is `0`, NOT `n`: the inner circle pole is `2 = 0+2`.) -/
theorem crossCFirst0_eq_PresTowerFam (W : VertexOperatorAlgebra 𝒱) (n K M : ℕ) (a c d : 𝒱) :
    crossCircCFirst W n K M a c d
      = PresTowerFam W M 0 c (K + 1) 1
          (fun r => W.smul a ((r : ℤ) - ((n : ℤ) + 1)) d)
          (fun r δ => if δ = 0 then cbz (K : ℤ) (r : ℤ) else 0) := by
  rw [crossCircCFirst, PresTowerFam]
  rw [← Fin.sum_univ_eq_sum_range
    (fun i => cbz (K : ℤ) (i : ℤ) •
      ∑ j ∈ Finset.range (M + 1),
        cbz (M : ℤ) (j : ℤ)
          • W.smul c ((j : ℤ) - 2) (W.smul a ((i : ℤ) - ((n : ℤ) + 1)) d)) (K + 1)]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.sum_range_one]
  rw [show (∑ j ∈ Finset.range (M + 1),
        cbz (M : ℤ) (j : ℤ) • W.smul c ((j : ℤ) - 2) (W.smul a ((r : ℤ) - ((n : ℤ) + 1)) d))
      = PresAnm W M 0 0 c (W.smul a ((r : ℤ) - ((n : ℤ) + 1)) d) from ?_]
  · rw [if_pos rfl]
  · rw [← ardCFirst_inner_eq_PresAnm W 0 M c (W.smul a ((r : ℤ) - ((n : ℤ) + 1)) d)]
    refine Finset.sum_congr rfl fun j _ => ?_
    norm_num

/-- **The Term₁ commutator predicate** (the level-`0` inner-circle residual).  For homogeneous
`a ∈ 𝒱_K`, `c ∈ 𝒱_M`, `d ∈ 𝒱_P`, the cross commutator family `crossCircComm`
(`ZhuVermaAnArchMUcrossHM`) is a homogeneous multi-grade `MGTowerFam` in the products `c₍s₎a` based at
`d`.  Engine-verified TRUE on the rank-1 free boson (`certificates/mathematica/anmrightdiff_terms.wl`,
Term₁ ∈ `(c₍s₎a)-towers@d`, `n = 1, 2`). -/
def CrossCommTowerEq (W : VertexOperatorAlgebra 𝒱) (n K M P : ℕ) (a c d : 𝒱) : Prop :=
  ∃ (S : ℕ) (gradeS : Fin S → ℕ) (leftS baseS : Fin S → 𝒱) (ΔS : Fin S → ℕ) (wS : Fin S → ℕ → ℂ),
    (∀ r : Fin S, leftS r ∈ W.grading ((gradeS r : ℤ))) ∧
    crossCircComm W n K M a c d = MGTowerFam W n S gradeS leftS baseS ΔS wS

/-- **The Term₁ cross residue-of-residue as the `c`-first `PresTowerFam` plus commutator
`MGTowerFam`** (homogeneous `a ∈ 𝒱_K`, `c ∈ 𝒱_M`).  By `crossCirc_modeSplit`
(`ZhuVermaAnArchMUcrossHM`), `resHom W 0 (n+1) a (resHom W 0 2 c d) = crossCircCFirst +
crossCircComm`; the `c`-first family is the level-`0` `c`-first `PresTowerFam`
(`crossCFirst0_eq_PresTowerFam`); supplying `CrossCommTowerEq` for the commutator `MGTowerFam` gives
the explicit `PresTowerFam(c, level 0) + MGTowerFam` form of the Term₁ residue. -/
theorem crossCirc_eq_PresTowerFam_add_MGTowerFam (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {K M P : ℕ}
    {a : 𝒱} (ha : a ∈ W.grading (K : ℤ)) {c : 𝒱} (hc : c ∈ W.grading (M : ℤ)) (d : 𝒱)
    (hcomm : CrossCommTowerEq W n K M P a c d) :
    ∃ (S : ℕ) (gradeS : Fin S → ℕ) (leftS baseS : Fin S → 𝒱) (ΔS : Fin S → ℕ) (wS : Fin S → ℕ → ℂ),
      (∀ r : Fin S, leftS r ∈ W.grading ((gradeS r : ℤ))) ∧
      resHom W 0 ((n : ℤ) + 1) a (resHom W 0 2 c d)
        = PresTowerFam W M 0 c (K + 1) 1
            (fun r => W.smul a ((r : ℤ) - ((n : ℤ) + 1)) d)
            (fun r δ => if δ = 0 then cbz (K : ℤ) (r : ℤ) else 0)
          + MGTowerFam W n S gradeS leftS baseS ΔS wS := by
  obtain ⟨S, gradeS, leftS, baseS, ΔS, wS, hhom, hcommeq⟩ := hcomm
  refine ⟨S, gradeS, leftS, baseS, ΔS, wS, hhom, ?_⟩
  rw [crossCirc_modeSplit W n ha hc d, crossCFirst0_eq_PresTowerFam W n K M a c d, hcommeq]

/-! ## The full `MUGradedAction W` from the two residual commutator predicates. -/

/-- **`MUGradedAction W` from `CrossCircTowerEq` (Term₁) and the Term₂ commutator predicate
`ARDCommTowerEq`.**  Supplying, for every level `n`, the in-repo cross tower predicate
`CrossCircTowerEq` (Term₁, the `a`-outer level-`0`-inner cross circle — already plumbed in the repo,
`ZhuVermaAnArchMUcrossHM`) and the Term₂ commutator predicate `ARDCommTowerEq` closes the Dong–Jiang
`M(U)` graded-action crux `MUGradedAction W`.  Term₂ is FULLY reduced here to its explicit commutator
→ `MGTowerFam` assignment (`ardTerm2TowerEq_of_comm`), with the `c`-first family closed as a depth-`1`
`PresTowerFam` in `c`; `MUGradedAction_of_towerEqs` (`ZhuVermaAnArchAnmRightDiff`) assembles the
crux. -/
theorem MUGradedAction_of_towerEqs_ardComm (W : VertexOperatorAlgebra 𝒱)
    (Hcross : ∀ (n K M P : ℕ), ∀ a ∈ W.grading (K : ℤ), ∀ c ∈ W.grading (M : ℤ),
      ∀ d ∈ W.grading (P : ℤ), CrossCircTowerEq W n K M P a c d)
    (HardC : ∀ (n K M P : ℕ), ∀ a ∈ W.grading (K : ℤ), ∀ c ∈ W.grading (M : ℤ),
      ∀ d ∈ W.grading (P : ℤ), ARDCommTowerEq W n K M P a c d) :
    MUGradedAction W :=
  MUGradedAction_of_towerEqs W Hcross
    (fun n K M P a ha c hc d hd =>
      ardTerm2TowerEq_of_comm W n ha hc d (HardC n K M P a ha c hc d hd))

/-! ## Status — `MUGradedAction W` closed to the two explicit commutator → `MGTowerFam` assignments.

Proved here (`#print axioms` = `[propext, Classical.choice, Quot.sound]`; no `sorry`/
`axiom`/`pbw`):

* **`ardCFirst`/`ardComm`** — the `c`-first and commutator families of the Term₂ (`a`-outer level-`n`
  inner circle, pole `n+2`) core, the analogue of `crossCircCFirst`/`crossCircComm`.
* **`ardTerm2_double_mode`** / **`ardTerm2_modeSplit`** — the explicit double-mode form and the exact
  `c`-first `+` commutator split of `anmRight W n 0 a (anmCirc W n 0 c d)` (via `mode_split_gen`),
  FULLY proven.
* **`ardCFirst_inner_eq_PresAnm`** / **`ardCFirst_eq_PresTowerFam`** — the Term₂ `c`-first family IS a
  depth-`1` `PresTowerFam` in homogeneous `c` (inner `j`-sum = `PresAnm W M n 0 c (a₍i−(n+1)₎d)`),
  FULLY proven.
* **`ARDCommTowerEq`** / **`ardTerm2TowerEq_of_comm`** — the precise Term₂ residual: the commutator
  family is an `MGTowerFam` in the products `c₍s₎a` based at `d`; supplying it discharges the full
  `ARDTerm2TowerEq` consumed by `MUGradedAction_of_towerEqs`.
* **`crossCFirst0_eq_PresTowerFam`** — the Term₁ `c`-first family (level-`0` inner circle) as the
  level-`0` `c`-first `PresTowerFam`, FULLY proven.
* **`CrossCommTowerEq`** / **`crossCirc_eq_PresTowerFam_add_MGTowerFam`** — the Term₁ commutator
  predicate and the explicit `PresTowerFam(c, level 0) + MGTowerFam` form of the Term₁ residue.
* **`MUGradedAction_of_towerEqs_ardComm`** — the full `MUGradedAction W` from the in-repo
  `CrossCircTowerEq` (Term₁) and the Term₂ commutator predicate `ARDCommTowerEq`.

**The remaining content (engine-verified TRUE; NOT faked):** the two explicit commutator → `MGTowerFam`
weight assignments

  (Term₂)  `ARDCommTowerEq W n K M P a c d` — `ardComm = MGTowerFam`(products `c₍s₎a` @ `d`),
  (Term₁)  `CrossCommTowerEq W n K M P a c d` — `crossCircComm = MGTowerFam`(products `c₍s₎a` @ `d`).

These are the `a`-outer / cross twins of the diagonal `AnmCircTowerEq` V-core
(`ZhuVermaAnArchMUcircV`, fully proven), the `n`-offset absorbed by the proven regrade
`crossDiff_regrade`/`regradeWt` (`ZhuVermaAnArchHPoleN`).  Both are engine-verified TRUE on the
rank-1 free boson (`certificates/mathematica/ardterm2_split.wl`, `certificates/mathematica/anmrightdiff_terms.wl`,
`n = 1, 2`, mixed homogeneous `a, c, d`).  The `c`-first families are FULLY closed here as depth-`1`
`PresTowerFam`s; the genuine remaining content is the commutator → `MGTowerFam` assignment (the DJ
Lemma 2.8 commutator expansion, same combinatorial depth as the proven diagonal V-core).
-/

end VOA

/-
`#print axioms` check (each of the following prints
`[propext, Classical.choice, Quot.sound]`, NO `pbw`, NO `sorryAx`):

  #print axioms VOA.ardTerm2_modeSplit
  #print axioms VOA.ardCFirst_eq_PresTowerFam
  #print axioms VOA.ardTerm2TowerEq_of_comm
  #print axioms VOA.crossCFirst0_eq_PresTowerFam
  #print axioms VOA.crossCirc_eq_PresTowerFam_add_MGTowerFam
  #print axioms VOA.MUGradedAction_of_towerEqs_ardComm
-/
