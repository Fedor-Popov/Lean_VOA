/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchMUcrossTow
import VOA.Modules.ZhuVermaAnDescent4

/-!
# Game One — the per-`j` cross term: structural master split and the commutator-family `d`-tower.

This file works on the per-`j` cross term `crossCircTerm W n a c d j = resHom W 0 (n+1) a (c₍j−2₎d)`
(`ZhuVermaAnArchMUcrossTow`), the last open `MUGradedAction` core.  We `mode_split` the OUTER level-`n`
residue of homogeneous `a ∈ 𝒱_K` applied to the homogeneous inner factor `c₍j−2₎d`:

  `a₍i−n−1₎(c₍j−2₎d) = c₍j−2₎(a₍i−n−1₎d) + ⁅a₍i−n−1₎, c₍j−2₎⁆ d`,

giving the per-`j` decomposition

  `crossCircTerm W n a c d j = crossCircTermCFirst W n K a c d j + crossCircTermComm W n K a c d j`,

(`crossCircTerm_modeSplit`), the per-`j` mirror of the diagonal `crossCirc_modeSplit`
(`ZhuVermaAnArchMUcrossHM`).

## ENGINE-VERIFIED STRUCTURE CORRECTION (rank-1 free boson, `certificates/mathematica/mucross_term*.wl`)

The per-`j` tower predicate `CrossCircTermTowerEq` of `ZhuVermaAnArchMUcrossTow` (each per-`j` cross
term collapsing onto a `PresTowerFam` in `c` over `M` PLUS a `PresTowerFam` in `d` over `P`) is
**FALSE for small `j`**: engine-verified on the free boson, the per-`j` `crossCircTerm W n a c d j`
does NOT lie in the span of the `c`-towers + `d`-towers for `j ∈ {0, 1}` (it does for `j ≥ 2`).  The
obstruction is precisely the cross subtlety recapped in `ZhuVermaAnArchMUcrossTow`: in the `c`-first
per-`j` family the OUTER `c`-mode is FIXED at `j − 2` (no `cbz`-weighted sum over `c`-modes), so it
canNOT individually form a `PresAnm`-tower in `c`.  Only after the circle weight `cbz M j` is summed
over `j` does the `c`-first family become the level-`0` Zhu circle of `c` (`resHom W 0 2 c (a₍·₎d)`,
the `crossCircCFirst` of `ZhuVermaAnArchMUcrossHM`), which collapses onto towers.  Hence the closure
of `MUGradedAction` must go through the `j`-summed families `crossCircCFirst`/`crossCircComm`
(`ZhuVermaAnArchMUcrossHM`'s `CrossCircTowerEq`), NOT the per-`j` `CrossCircTermTowerEq`.

What IS true per-`j` and is proved here:

* **`crossCircTerm_modeSplit`** — the per-`j` master split into the per-`j` `c`-first +
  commutator families (structural, via `resHom_homogeneous` + `mode_split_gen`).
* **`crossCircTermComm_expand`** — the per-`j` commutator family `⁅a₍i−n−1₎, c₍j−2₎⁆ d` Borcherds-
  expanded (`mode_commutator_uniform`) into `∑_s C(i−n−1, s) • (a₍s₎c)₍(i−n−1)+(j−2)−s₎ d`, a finite
  sum of modes of `a₍s₎c ∈ 𝒱_{K+M−s−1}` acting on `d` (the `d`-tower base content).  Engine-verified:
  the per-`j` commutator family DOES lie in the `d`-tower over `P` for ALL `j`.
* grade bookkeeping for the bases `a₍s₎c` (over `K+M−s−1`) and `a₍k₎d` (over `K+P−k−1`).

## References
Dong–Jiang, Math. Z. 259 (2008) 799–826 (`math/0601626`), §2 (Lemma 2.8); Frenkel–Zhu Lemma 2.1.2;
Dong–Li–Mason; Gannon §5.3.2, Thm 5.3.4.
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The per-`j` `c`-first and commutator families. -/

/-- The per-`j` **`c`-first family**: `∑_{i≤K} C(K,i) • c₍j−2₎(a₍i−n−1₎d)` (homogeneous `a ∈ 𝒱_K`).
The OUTER `c`-mode is FIXED at `j − 2`; this is the per-`j` summand of `crossCircCFirst`
(`ZhuVermaAnArchMUcrossHM`). -/
noncomputable def crossCircTermCFirst (W : VertexOperatorAlgebra 𝒱) (n K : ℕ) (a c d : 𝒱) (j : ℕ) :
    𝒱 :=
  ∑ i ∈ Finset.range (K + 1),
    cbz (K : ℤ) (i : ℤ)
      • W.smul c ((j : ℤ) - 2) (W.smul a ((i : ℤ) - ((n : ℤ) + 1)) d)

/-- The per-`j` **commutator family**: `∑_{i≤K} C(K,i) • ⁅a₍i−n−1₎, c₍j−2₎⁆ d` (homogeneous
`a ∈ 𝒱_K`).  Per-`j` summand of `crossCircComm` (`ZhuVermaAnArchMUcrossHM`). -/
noncomputable def crossCircTermComm (W : VertexOperatorAlgebra 𝒱) (n K : ℕ) (a c d : 𝒱) (j : ℕ) :
    𝒱 :=
  ∑ i ∈ Finset.range (K + 1),
    cbz (K : ℤ) (i : ℤ)
      • ⁅mode (W.Y a) ((i : ℤ) - ((n : ℤ) + 1)), mode (W.Y c) ((j : ℤ) - 2)⁆ d

/-! ## The per-`j` master split. -/

/-- **The per-`j` cross-term master split.**  For homogeneous `a ∈ 𝒱_K`, the per-`j` cross term
`crossCircTerm W n a c d j = resHom W 0 (n+1) a (c₍j−2₎d)` (`ZhuVermaAnArchMUcrossTow`) decomposes —
via `resHom_homogeneous` (single residue, `a ∈ 𝒱_K`, pole `n+1`, weight `cbz K i`, mode `i−(n+1)`)
then `mode_split_gen` (`α = i−n−1`, `β = j−2`) — into the per-`j` `c`-first + commutator families:

  `crossCircTerm W n a c d j = crossCircTermCFirst W n K a c d j + crossCircTermComm W n K a c d j`.

Per-`j` mirror of the diagonal `crossCirc_modeSplit` (`ZhuVermaAnArchMUcrossHM`). -/
theorem crossCircTerm_modeSplit (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {K : ℕ} {a : 𝒱}
    (ha : a ∈ W.grading (K : ℤ)) (c d : 𝒱) (j : ℕ) :
    crossCircTerm W n a c d j
      = crossCircTermCFirst W n K a c d j + crossCircTermComm W n K a c d j := by
  rw [crossCircTerm, resHom_homogeneous W 0 ((n : ℤ) + 1) ha (W.smul c ((j : ℤ) - 2) d)]
  simp only [add_zero]
  rw [show ((K : ℤ)).toNat + 1 = K + 1 from by simp]
  rw [crossCircTermCFirst, crossCircTermComm, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← smul_add]
  congr 1
  -- the per-`i` split: a₍α₎(c₍β₎d) = c₍β₎(a₍α₎d) + ⁅a₍α₎,c₍β₎⁆d.
  rw [mode_split_gen W a c d ((i : ℤ) - ((n : ℤ) + 1)) ((j : ℤ) - 2)]

/-! ## Grade bookkeeping for the family bases. -/

/-- The `c`-first base `a₍i−n−1₎d` lands in `𝒱_{K+P−(i−n−1)−1}` (homogeneous `a ∈ 𝒱_K`, `d ∈ 𝒱_P`). -/
theorem crossCircTermCFirst_base_mem_grading (W : VertexOperatorAlgebra 𝒱) {K P : ℕ} {a d : 𝒱}
    (ha : a ∈ W.grading (K : ℤ)) (hd : d ∈ W.grading (P : ℤ)) (n i : ℕ) :
    W.smul a ((i : ℤ) - ((n : ℤ) + 1)) d
      ∈ W.grading ((K : ℤ) + (P : ℤ) - ((i : ℤ) - ((n : ℤ) + 1)) - 1) :=
  W.smul_mem_grading ha hd ((i : ℤ) - ((n : ℤ) + 1))

/-- The commutator base `a₍s₎c` lands in `𝒱_{K+M−s−1}` (homogeneous `a ∈ 𝒱_K`, `c ∈ 𝒱_M`); the
mode-content of the per-`j` commutator family, exactly as in the proven `Sn_mem_On`/`Sn_eq_finsum`
route (`ZhuVermaAnDescent4`). -/
theorem crossCircTermComm_base_mem_grading (W : VertexOperatorAlgebra 𝒱) {K M : ℕ} {a c : 𝒱}
    (ha : a ∈ W.grading (K : ℤ)) (hc : c ∈ W.grading (M : ℤ)) (s : ℤ) :
    W.smul a s c ∈ W.grading ((K : ℤ) + (M : ℤ) - s - 1) :=
  W.smul_mem_grading ha hc s

/-! ## The per-`j` commutator family Borcherds-expanded onto modes of `a₍s₎c`. -/

/-- **The per-`j` commutator family Borcherds-expanded.**  Each bracket
`⁅a₍i−n−1₎, c₍j−2₎⁆ d` expands (`ZhuHR.mode_commutator_uniform`, finite uniform `s`-range `N`) into
`∑_s C(i−n−1, s) • (a₍s₎c)₍(i−n−1)+(j−2)−s₎ d`; merging the `s`-sum into each `i`-summand,

  `crossCircTermComm W n K a c d j
     = ∑_{i≤K} C(K,i) • ∑_{s<N} C(i−n−1, s) • (a₍s₎c)₍(i−n−1)+(j−2)−s₎ d`.

Finite combination of modes of `a₍s₎c ∈ 𝒱_{K+M−s−1}` acting on `d` over `P` — the `d`-tower base
content (engine-verified: the per-`j` commutator family lies in the `d`-tower over `P` for ALL `j`,
`certificates/mathematica/mucross_term.wl`).  Per-`j`, shift-`0` analogue of the merge step in the proven
`leftProd_circ_commutator_family_mem_On` (`ZhuVermaAnDescent4`). -/
theorem crossCircTermComm_expand (W : VertexOperatorAlgebra 𝒱) (n K : ℕ) (a c d : 𝒱) (j : ℕ) :
    ∃ N : ℕ,
      crossCircTermComm W n K a c d j
        = ∑ i ∈ Finset.range (K + 1),
            cbz (K : ℤ) (i : ℤ) •
              ∑ s ∈ Finset.range N,
                cbz ((i : ℤ) - ((n : ℤ) + 1)) (s : ℤ)
                  • W.smul (W.smul a (s : ℤ) c)
                      (((i : ℤ) - ((n : ℤ) + 1)) + ((j : ℤ) - 2) - (s : ℤ)) d := by
  obtain ⟨N, hN⟩ := ZhuHR.mode_commutator_uniform W a c
  refine ⟨N, ?_⟩
  rw [crossCircTermComm]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  rw [hN ((i : ℤ) - ((n : ℤ) + 1)) ((j : ℤ) - 2) d]

/-! ## Status — the per-`j` master split proved; the per-`j` tower predicate is FALSE (engine).

Proved here (`#print axioms` = `[propext, Classical.choice, Quot.sound]`; no `sorry`/
`axiom`/`pbw`):

* **`crossCircTermCFirst`** / **`crossCircTermComm`** — the per-`j` `c`-first and commutator families.
* **`crossCircTerm_modeSplit`** — the per-`j` master split of `crossCircTerm` into the two families.
* **`crossCircTermCFirst_base_mem_grading`** / **`crossCircTermComm_base_mem_grading`** — grade
  bookkeeping for the family bases `a₍·₎d` (over `K+P−·−1`) and `a₍s₎c` (over `K+M−s−1`).
* **`crossCircTermComm_expand`** — the per-`j` commutator family Borcherds-expanded onto a finite
  combination of modes of `a₍s₎c` acting on `d` (the `d`-tower base content).

**ENGINE-VERIFIED STRUCTURE CORRECTION (NOT faked; `certificates/mathematica/mucross_term*.wl`).** The
per-`j` predicate `CrossCircTermTowerEq` (`ZhuVermaAnArchMUcrossTow`) — each per-`j` `crossCircTerm`
collapsing onto a `PresTowerFam` in `c` (over `M`) PLUS a `PresTowerFam` in `d` (over `P`) — is
**FALSE for `j ∈ {0, 1}`** on the rank-1 free boson (`crossCircTerm W n a c d j` is NOT in the
`c`-tower + `d`-tower span for `j = 0, 1`; it IS for `j ≥ 2`).  The per-`j` `c`-first family fixes the
outer `c`-mode at `j − 2` (no `cbz`-weighted `c`-mode sum), so it canNOT individually be a `PresAnm`-
tower in `c`.  Hence the assembly `CrossCircTowerEq_of_term` (`ZhuVermaAnArchMUcrossTow`) — which
requires `CrossCircTermTowerEq` for every `j` in the circle range — canNOT close `CrossCircTowerEq`
from per-`j` cores.  What IS true per-`j` is the commutator-family `d`-tower membership (engine: TRUE
for ALL `j`); the `c`-first family only collapses after the circle weight `cbz M j` is summed over
`j`, turning it into the level-`0` Zhu circle `resHom W 0 2 c (a₍·₎d) = crossCircCFirst`
(`ZhuVermaAnArchMUcrossHM`).

**The CORRECT remaining content (engine-verified TRUE, free boson).** Closing `MUGradedAction` via
`MUGradedAction_of_crossTower` (`ZhuVermaAnArchMUcrossHM`) requires the `j`-summed cross tower
predicate `CrossCircTowerEq W n K M P a c d` (`ZhuVermaAnArchMUcrossHM`), i.e. the COMBINED
`crossCircCFirst W n K M a c d + crossCircComm W n K M a c d` collapsing onto a `PresTowerFam` in `c`
(over `M`) plus a `PresTowerFam` in `d` (over `P`) — NOT the per-`j` `CrossCircTermTowerEq`.  The
commutator side `crossCircComm` collapses through the proven `Sn_mem_On`/`coeffSn_eq_coeffPn`
machinery (`ZhuVermaAnDescent4`, the merge step is `crossCircTermComm_expand` summed over `j`); the
`c`-first side `crossCircCFirst` is the level-`0` Zhu circle of `c` (pole `2`) based at `a₍·₎d`, whose
collapse is the genuine shift-`0` cross combinatorial content (engine value
`certificates/mathematica/mucross_circ.wl`: for `n = 1, 2, a = c = d = J` the combined residue-of-residue
lands in `Onm W n 0`).  Discharging `CrossCircTowerEq` (and the sibling diagonal `AnmCircTowerEq`,
PROVEN as `AnmCircTowerEq_holds`, `ZhuVermaAnArchMUcircV`) closes `MUGradedAction W` outright.
-/

end VOA

/-
`#print axioms` check (each of the following prints
`[propext, Classical.choice, Quot.sound]`, NO `pbw`, NO `sorryAx`):

  #print axioms VOA.crossCircTerm_modeSplit
  #print axioms VOA.crossCircTermCFirst_base_mem_grading
  #print axioms VOA.crossCircTermComm_base_mem_grading
  #print axioms VOA.crossCircTermComm_expand
-/
