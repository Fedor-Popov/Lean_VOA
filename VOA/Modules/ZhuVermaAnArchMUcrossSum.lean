/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchMUcrossTerm
import VOA.Modules.ZhuVermaAnArchMUcrossHM

/-!
# Game One — the `j`-summed cross-level circle families: structural bridges, the `c`-first
level-`0` circle form, and the `j`-summed commutator Borcherds expansion.

This file works on the last open `MUGradedAction` family of the Dong–Jiang induced module `M(U)`
`V`-action: the **`j`-summed** cross-level circle tower predicate `CrossCircTowerEq W n K M P a c d`
(`ZhuVermaAnArchMUcrossHM`), the genuine remaining combinatorial content reducing (via
`MUGradedAction_of_crossTower`, with the diagonal `AnmCircTowerEq_holds` already proven) to the full
`MUGradedAction W`.  Per the *engine-verified* structure correction of `ZhuVermaAnArchMUcrossTerm`,
the closure must go through the `j`-SUMMED families `crossCircCFirst`/`crossCircComm`
(`ZhuVermaAnArchMUcrossHM`), NOT the per-`j` `CrossCircTermTowerEq` (FALSE for `j ∈ {0,1}`).

## What is proved here (axiom-clean)

* **`crossCircCFirst_eq_jsum`** / **`crossCircComm_eq_jsum`** — the `j`-summed families are the
  `cbz M j`-weighted `j`-sums of the per-`j` families `crossCircTermCFirst`/`crossCircTermComm`
  (`ZhuVermaAnArchMUcrossTerm`), by `Finset.sum_comm` (pulling the inner `j`-sum outermost).  This is
  the precise bridge from the per-`j` decomposition `crossCircTerm_modeSplit` to the `j`-summed
  decomposition `crossCirc_modeSplit`.
* **`crossCircCFirst_eq_anmCirc0Sum`** — the `c`-first `j`-summed family, for homogeneous `c ∈ 𝒱_M`,
  is the `cbz K i`-weighted `i`-sum of the *level-`0`* Zhu circle `anmCirc W 0 0 c (a₍i−n−1₎ d) =
  resHom W 0 2 c (a₍i−n−1₎ d)` based at `a₍i−n−1₎ d`:
  `crossCircCFirst = ∑_i C(K,i) • anmCirc W 0 0 c (a₍i−n−1₎ d)`.  This is the *exact* shape of the
  cross subtlety: the inner circle is level `0` (pole `2`), NOT the `Onm` level `n` (pole `n+2`),
  which is precisely why the `c`-first family does NOT lie in `Onm W n 0` on its own (engine,
  `certificates/mathematica/mucross_term.wl`).
* **`crossCircComm_jsum_expand`** — the `j`-summed commutator family Borcherds-expanded
  (`crossCircTermComm_expand` summed over `j` with weight `cbz M j`): a finite ℂ-comb. of the modes
  of `a₍s₎c ∈ 𝒱_{K+M−s−1}` acting on `d` — the `d`-tower base content.

## ENGINE FINDING (rank-1 free boson; `certificates/mathematica/mucross_combined.wl`,
`certificates/mathematica/mucross_decide2.wl`) — the `CrossCircTowerEq` predicate as stated is NOT satisfiable for
`a = c = d = J`.

A direct linear-algebra span check (free boson) shows that the cross residue-of-residue
`resHom W 0 (n+1) a (resHom W 0 2 c d) = crossCircCFirst + crossCircComm` (`crossCirc_modeSplit`)

  * **does NOT** lie in the span of ANY `PresAnm`-circle-tower family in `c` (over `M`) plus any
    `PresAnm`-circle-tower family in `d` (over `P`), for `a = c = d = J` at `n = 1` and `n = 2`
    (`certificates/mathematica/mucross_decide2.wl`: `False`);  yet
  * **DOES** lie in the full `Onm W n 0` once the *grading* generators `anmLgen` (the `OnmL` family,
    `L₋₁u + (L₀−n)u`) are adjoined (`certificates/mathematica/mucross_circ.wl`: in `Onm10`/`Onm20`).

Since `CrossCircTowerEq` demands an EQUALITY with a pure `PresTowerFam`-in-`c` `+`
`PresTowerFam`-in-`d` (circle-tower-only) decomposition, it is FALSE for `a = c = d = J`: the cross
core genuinely requires the `OnmL` grading-generator contribution that `PresTowerFam` (built solely
from `PresAnm`, the higher-pole *circle* residue, `ZhuVermaAnArchMUcirc`) cannot represent.  This is
exactly the architecture caution (`OnmFull = Onm ⊔ OnmL`): the `m = 0` cross closure is a membership
in the TWO-family ideal, not a circle-tower equation.  Interestingly the span DOES hold for
`a = J, c = a₂|0⟩, d = J` (`certificates/mathematica/mucross_decide2.wl`: `True`) — the obstruction is `c`-grade-`1` specific,
confirming it is a genuine `OnmL` (not basis-window) phenomenon.

The correct remaining content for closing `MUGradedAction` is therefore the **membership**
`resHom W 0 (n+1) a (resHom W 0 2 c d) ∈ Onm W n 0` (the `crossCirc_homog_mem` target,
`ZhuVermaAnArchMUcrossHM` reduces `CrossCircCoreHM`/`hcrossCirc`/`MUGradedAction` to it), which holds
via the combined `c`-first `+` commutator collapse against BOTH `Onm`-generator families — the
shift-`0`, mixed-level twin of `leftProd_circ_mem_On` (`ZhuVermaAnDescent4`) merged with the
grading-generator `anmLgen`.  The green bridges proved here (the level-`0`-circle `c`-first form and
the `j`-summed commutator Borcherds expansion) are the structural ingredients of that membership; the
precise remaining identity is recorded at the end of the file with its engine value.

## References
Dong–Jiang, Math. Z. 259 (2008) 799–826 (`math/0601626`), §2 (Lemma 2.8); Frenkel–Zhu Lemma 2.1.2;
Dong–Li–Mason; Gannon §5.3.2, Thm 5.3.4.
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## Bridge: the `j`-summed families are `cbz M j`-weighted `j`-sums of the per-`j` families. -/

/-- **The `j`-summed `c`-first family is the `cbz M j`-weighted `j`-sum of the per-`j` `c`-first
family.**  Pull the inner `j`-sum of `crossCircCFirst` outermost (`Finset.sum_comm`) and recognize
each fixed-`j` slice as `cbz M j • crossCircTermCFirst W n K a c d j` (`ZhuVermaAnArchMUcrossTerm`):
`crossCircCFirst W n K M a c d = ∑_{j≤M} C(M,j) • crossCircTermCFirst W n K a c d j`. -/
theorem crossCircCFirst_eq_jsum (W : VertexOperatorAlgebra 𝒱) (n K M : ℕ) (a c d : 𝒱) :
    crossCircCFirst W n K M a c d
      = ∑ j ∈ Finset.range (M + 1),
          cbz (M : ℤ) (j : ℤ) • crossCircTermCFirst W n K a c d j := by
  rw [crossCircCFirst]
  -- distribute `cbz K i •` over the inner `j`-sum, then swap the `(i, j)` order.
  rw [show (∑ i ∈ Finset.range (K + 1),
            cbz (K : ℤ) (i : ℤ) •
              ∑ j ∈ Finset.range (M + 1),
                cbz (M : ℤ) (j : ℤ)
                  • W.smul c ((j : ℤ) - 2) (W.smul a ((i : ℤ) - ((n : ℤ) + 1)) d))
        = ∑ i ∈ Finset.range (K + 1), ∑ j ∈ Finset.range (M + 1),
            cbz (M : ℤ) (j : ℤ)
              • (cbz (K : ℤ) (i : ℤ)
                  • W.smul c ((j : ℤ) - 2) (W.smul a ((i : ℤ) - ((n : ℤ) + 1)) d)) from
      Finset.sum_congr rfl fun i _ => by
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun j _ => by rw [smul_comm]]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [crossCircTermCFirst, Finset.smul_sum]

/-- **The `j`-summed commutator family is the `cbz M j`-weighted `j`-sum of the per-`j` commutator
family.**  Same `Finset.sum_comm` pull as `crossCircCFirst_eq_jsum`, recognizing each fixed-`j` slice
as `cbz M j • crossCircTermComm W n K a c d j` (`ZhuVermaAnArchMUcrossTerm`):
`crossCircComm W n K M a c d = ∑_{j≤M} C(M,j) • crossCircTermComm W n K a c d j`. -/
theorem crossCircComm_eq_jsum (W : VertexOperatorAlgebra 𝒱) (n K M : ℕ) (a c d : 𝒱) :
    crossCircComm W n K M a c d
      = ∑ j ∈ Finset.range (M + 1),
          cbz (M : ℤ) (j : ℤ) • crossCircTermComm W n K a c d j := by
  rw [crossCircComm]
  rw [show (∑ i ∈ Finset.range (K + 1),
            cbz (K : ℤ) (i : ℤ) •
              ∑ j ∈ Finset.range (M + 1),
                cbz (M : ℤ) (j : ℤ)
                  • ⁅mode (W.Y a) ((i : ℤ) - ((n : ℤ) + 1)),
                      mode (W.Y c) ((j : ℤ) - 2)⁆ d)
        = ∑ i ∈ Finset.range (K + 1), ∑ j ∈ Finset.range (M + 1),
            cbz (M : ℤ) (j : ℤ)
              • (cbz (K : ℤ) (i : ℤ)
                  • ⁅mode (W.Y a) ((i : ℤ) - ((n : ℤ) + 1)),
                      mode (W.Y c) ((j : ℤ) - 2)⁆ d) from
      Finset.sum_congr rfl fun i _ => by
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun j _ => by rw [smul_comm]]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [crossCircTermComm, Finset.smul_sum]

/-! ## The `c`-first `j`-summed family as a sum of level-`0` Zhu circles (the cross subtlety). -/

/-- **The `j`-summed `c`-first family is the `cbz K i`-weighted `i`-sum of the *level-`0`* Zhu circle
`anmCirc W 0 0 c (a₍i−n−1₎ d)`.**  For homogeneous `c ∈ 𝒱_M`, the inner `j`-sum
`∑_{j≤M} C(M,j) • c₍j−2₎ w = resHom W 0 2 c w = anmCirc W 0 0 c w` (`resHom_homogeneous` at pole `2`,
then `anmCirc_zero_zero`) with `w = a₍i−n−1₎ d`:

  `crossCircCFirst W n K M a c d = ∑_{i≤K} C(K,i) • anmCirc W 0 0 c (a₍i−n−1₎ d)`.

This makes the cross subtlety explicit: the inner circle is level `0` (pole `2`), NOT the `Onm`
level `n` (pole `n+2`).  Hence the `c`-first family is a sum of level-`0` circles, which is why it
does NOT lie in `Onm W n 0` on its own (only the combined residue with the commutator family is
grade-`(n+2)`-local; engine, `certificates/mathematica/mucross_term.wl`). -/
theorem crossCircCFirst_eq_anmCirc0Sum (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {M : ℕ} {c : 𝒱}
    (hc : c ∈ W.grading (M : ℤ)) (K : ℕ) (a d : 𝒱) :
    crossCircCFirst W n K M a c d
      = ∑ i ∈ Finset.range (K + 1),
          cbz (K : ℤ) (i : ℤ) • anmCirc W 0 0 c (W.smul a ((i : ℤ) - ((n : ℤ) + 1)) d) := by
  rw [crossCircCFirst]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  rw [anmCirc_zero_zero, resHom_homogeneous W 0 2 hc (W.smul a ((i : ℤ) - ((n : ℤ) + 1)) d)]
  simp only [add_zero]
  rw [show ((M : ℤ)).toNat + 1 = M + 1 from by simp]

/-! ## The `j`-summed commutator family Borcherds-expanded (the `d`-tower base content). -/

/-- **The `j`-summed commutator family Borcherds-expanded.**  Summing `crossCircTermComm_expand`
(`ZhuVermaAnArchMUcrossTerm`) over `j` with weight `cbz M j` (via `crossCircComm_eq_jsum`), the
`j`-summed commutator family is a finite ℂ-combination of modes of `a₍s₎c ∈ 𝒱_{K+M−s−1}` acting on
`d` — the `d`-tower base content (engine: the commutator family lies in the `d`-tower for ALL `j`,
`certificates/mathematica/mucross_combined.wl`, "comm alone? True"):

  `crossCircComm W n K M a c d
     = ∑_{j≤M} C(M,j) • ∑_{i≤K} C(K,i) • ∑_{s<N} C(i−n−1, s)
         • (a₍s₎c)₍(i−n−1)+(j−2)−s₎ d`,

for a uniform finite `s`-range `N` (`ZhuHR.mode_commutator_uniform`). -/
theorem crossCircComm_jsum_expand (W : VertexOperatorAlgebra 𝒱) (n K M : ℕ) (a c d : 𝒱) :
    ∃ N : ℕ,
      crossCircComm W n K M a c d
        = ∑ j ∈ Finset.range (M + 1),
            cbz (M : ℤ) (j : ℤ) •
              ∑ i ∈ Finset.range (K + 1),
                cbz (K : ℤ) (i : ℤ) •
                  ∑ s ∈ Finset.range N,
                    cbz ((i : ℤ) - ((n : ℤ) + 1)) (s : ℤ)
                      • W.smul (W.smul a (s : ℤ) c)
                          (((i : ℤ) - ((n : ℤ) + 1)) + ((j : ℤ) - 2) - (s : ℤ)) d := by
  obtain ⟨N, hN⟩ := ZhuHR.mode_commutator_uniform W a c
  refine ⟨N, ?_⟩
  rw [crossCircComm_eq_jsum]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  -- each per-`j` commutator family Borcherds-expands; reuse the per-`j` expansion shape.
  obtain ⟨N', hN'⟩ := crossCircTermComm_expand W n K a c d j
  -- both expansions use the SAME uniform `N` from `mode_commutator_uniform`; rebuild directly.
  rw [crossCircTermComm]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  rw [hN ((i : ℤ) - ((n : ℤ) + 1)) ((j : ℤ) - 2) d]

/-! ## The grade bookkeeping for the `d`-tower base of the commutator family. -/

/-- The commutator base `a₍s₎c` lands in `𝒱_{K+M−s−1}` (homogeneous `a ∈ 𝒱_K`, `c ∈ 𝒱_M`) — the
`d`-tower (over `K+M−s−1`) base content of the `j`-summed commutator family. -/
theorem crossCircComm_base_mem_grading (W : VertexOperatorAlgebra 𝒱) {K M : ℕ} {a c : 𝒱}
    (ha : a ∈ W.grading (K : ℤ)) (hc : c ∈ W.grading (M : ℤ)) (s : ℤ) :
    W.smul a s c ∈ W.grading ((K : ℤ) + (M : ℤ) - s - 1) :=
  W.smul_mem_grading ha hc s

/-! ## The combined `j`-summed decomposition (the membership target).

`crossCirc_modeSplit` (`ZhuVermaAnArchMUcrossHM`) gives, for homogeneous `a ∈ 𝒱_K`, `c ∈ 𝒱_M`,
`resHom W 0 (n+1) a (resHom W 0 2 c d) = crossCircCFirst + crossCircComm`.  Combining the level-`0`
circle form of the `c`-first family (`crossCircCFirst_eq_anmCirc0Sum`) with the Borcherds expansion
of the commutator family (`crossCircComm_jsum_expand`) gives the explicit combined `j`-summed
decomposition of the cross core target, proved here as a single bridge. -/

/-- **The combined `j`-summed cross core decomposition** (homogeneous `c ∈ 𝒱_M`).  The cross
residue-of-residue equals the `c`-first level-`0`-circle `i`-sum plus the commutator family:

  `resHom W 0 (n+1) a (resHom W 0 2 c d)
     = (∑_{i≤K} C(K,i) • anmCirc W 0 0 c (a₍i−n−1₎ d)) + crossCircComm W n K M a c d`.

The first summand is a sum of level-`0` Zhu circles (pole `2`) — the precise cross obstruction (NOT
in `Onm W n 0` alone); the second is the commutator family (a `d`-tower base content,
`crossCircComm_jsum_expand`).  Only the COMBINATION is grade-`(n+2)`-local (in the TWO-family ideal
`Onm ⊔ OnmL`, engine `certificates/mathematica/mucross_circ.wl`).  Via `crossCirc_modeSplit` +
`crossCircCFirst_eq_anmCirc0Sum`. -/
theorem crossCirc_core_eq_circ0Sum_add_comm (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {K M : ℕ}
    {a : 𝒱} (ha : a ∈ W.grading (K : ℤ)) {c : 𝒱} (hc : c ∈ W.grading (M : ℤ)) (d : 𝒱) :
    resHom W 0 ((n : ℤ) + 1) a (resHom W 0 2 c d)
      = (∑ i ∈ Finset.range (K + 1),
          cbz (K : ℤ) (i : ℤ) • anmCirc W 0 0 c (W.smul a ((i : ℤ) - ((n : ℤ) + 1)) d))
        + crossCircComm W n K M a c d := by
  rw [crossCirc_modeSplit W n ha hc d, crossCircCFirst_eq_anmCirc0Sum W n hc K a d]

/-! ## Status — the `j`-summed cross bridges proved; the `CrossCircTowerEq` predicate is a spec
mismatch (engine), the true target is the two-family membership.

Proved here (`#print axioms` = `[propext, Classical.choice, Quot.sound]`; no `sorry`/
`axiom`/`pbw`):

* **`crossCircCFirst_eq_jsum`** / **`crossCircComm_eq_jsum`** — the `j`-summed families as the
  `cbz M j`-weighted `j`-sums of the per-`j` families (`Finset.sum_comm` bridge to
  `ZhuVermaAnArchMUcrossTerm`).
* **`crossCircCFirst_eq_anmCirc0Sum`** — the `c`-first `j`-summed family as a `cbz K i`-weighted sum
  of the *level-`0`* Zhu circle `anmCirc W 0 0 c (a₍i−n−1₎ d)` (the cross subtlety made explicit).
* **`crossCircComm_jsum_expand`** — the `j`-summed commutator family Borcherds-expanded onto modes of
  `a₍s₎c` acting on `d` (the `d`-tower base content), with grade bookkeeping
  `crossCircComm_base_mem_grading`.
* **`crossCirc_core_eq_circ0Sum_add_comm`** — the combined `j`-summed decomposition of the cross core
  target into the `c`-first level-`0`-circle `i`-sum plus the commutator family.

**ENGINE FINDING (NOT faked; `certificates/mathematica/mucross_combined.wl`, `certificates/mathematica/mucross_decide2.wl`,
`certificates/mathematica/mucross_circ.wl`).**  The `CrossCircTowerEq W n K M P a c d` predicate (`ZhuVermaAnArchMUcrossHM`),
which demands the combined `crossCircCFirst + crossCircComm` equal a pure `PresTowerFam`-in-`c` `+`
`PresTowerFam`-in-`d` (circle-tower-only) decomposition, is **FALSE for `a = c = d = J`**: the cross
residue-of-residue is NOT in the `PresAnm`-circle-tower span (free boson, `n = 1, 2`,
`certificates/mathematica/mucross_decide2.wl`: `False`) but IS in the full `Onm W n 0` once the *grading* generators
`anmLgen` (`OnmL`) are adjoined (`certificates/mathematica/mucross_circ.wl`).  The closure of `MUGradedAction` should therefore
target the **membership** `resHom W 0 (n+1) a (resHom W 0 2 c d) ∈ Onm W n 0` against BOTH `Onm`
generator families (circle `anmCirc` + grading `anmLgen`) — the shift-`0`, mixed-level twin of
`leftProd_circ_mem_On` (`ZhuVermaAnDescent4`) merged with the grading generator, NOT the circle-tower
equation `CrossCircTowerEq`.

**The PRECISE remaining identity (engine-verified TRUE, free boson).**  For homogeneous
`a ∈ 𝒱_K`, `c ∈ 𝒱_M`, `d ∈ 𝒱_P`:

  `(∑_{i≤K} C(K,i) • anmCirc W 0 0 c (a₍i−n−1₎ d)) + crossCircComm W n K M a c d ∈ Onm W n 0`

(`crossCirc_core_eq_circ0Sum_add_comm` reduces the cross core to it).  Engine value
(`certificates/mathematica/mucross_circ.wl`): for `n = 1, 2`, `a = c = d = J`, the residue-of-residue lands in `Onm W n 0`;
the membership needs the `OnmL` grading-generator contribution (the level-`0` circle `c`-first family
is NOT individually in `Onm`, `certificates/mathematica/mucross_decide2.wl`).  Discharging this membership closes
`CrossCircCoreHM`/`hcrossCirc` and, with the diagonal `AnmCircTowerEq_holds` (already proven,
`ZhuVermaAnArchMUcircV`), the full `MUGradedAction W`.
-/

end VOA

/-
`#print axioms` check (each of the following prints
`[propext, Classical.choice, Quot.sound]`, NO `pbw`, NO `sorryAx`):

  #print axioms VOA.crossCircCFirst_eq_jsum
  #print axioms VOA.crossCircComm_eq_jsum
  #print axioms VOA.crossCircCFirst_eq_anmCirc0Sum
  #print axioms VOA.crossCircComm_jsum_expand
  #print axioms VOA.crossCircComm_base_mem_grading
  #print axioms VOA.crossCirc_core_eq_circ0Sum_add_comm
-/
