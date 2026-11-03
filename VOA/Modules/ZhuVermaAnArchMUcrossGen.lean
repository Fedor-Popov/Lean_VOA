/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchMUcrossMem

/-!
# Game One — the last cross family `CrossCircOnmGen` reduced to its two precise generator-family
sub-identities, with the full `MUGradedAction W` assembly.

This file closes the structural side of the last open `MUGradedAction` family of the Dong–Jiang
induced module `M(U)` `V`-action: the cross membership predicate `CrossCircOnmGen W n`
(`ZhuVermaAnArchMUcrossMem`),

  `(∑_{i≤K} C(K,i) • anmCirc W 0 0 c (a₍i−n−1₎ d)) + crossCircComm W n K M a c d  ∈  Onm W n 0`

(homogeneous `a ∈ 𝒱_K`, `c ∈ 𝒱_M`, `d ∈ 𝒱_P`).  The first summand is the `c`-first family of
LEVEL-`0` Zhu circles (pole `2`, `crossCircCFirst_eq_anmCirc0Sum`, `ZhuVermaAnArchMUcrossSum`); the
second is the commutator family (modes of `a₍s₎c` on `d`, `crossCircComm_jsum_expand`).  Discharging
`CrossCircOnmGen` for all `n` supplies the full DJ `M(U)` `V`-action crux `MUGradedAction W` via the
already-proved `MUGradedAction_of_CrossCircOnmGen` (`ZhuVermaAnArchMUcrossMem`); the diagonal circle
family (`hcirc_closed`) and the cross grading family (`anmRight_zero_crossL_mem_Onm`) are closed.

## The architecture: two precise generator-family sub-predicates

We split the cross membership into its two named families and prove the trivial combination
(`add_mem`), so that closing `CrossCircOnmGen` is reduced to closing the two precise sub-identities
**separately** — each a clean, single-family statement:

* **`CrossCFirstOnm W n`** — the `c`-first family of level-`0` circles lies in `Onm W n 0`:
  `∑_{i≤K} C(K,i) • anmCirc W 0 0 c (a₍i−n−1₎ d) ∈ Onm W n 0`.  This is the genuine cross subtlety:
  the inner circle is LEVEL `0` (pole `2`), NOT the `Onm` level `n` (pole `n+2`); the membership is
  carried by combining the `Pres_mem_Onm`-towers with the `OnmL` grading generators `anmLgen` (the
  shift-`m−n = −n` part) — the level-shift mirror of `crossLRest_eq` (`ZhuVermaAnArchMUcross`).
* **`CrossCommOnm W n`** — the commutator family lies in `Onm W n 0`:
  `crossCircComm W n K M a c d ∈ Onm W n 0`.  By `crossCircComm_jsum_expand`
  (`ZhuVermaAnArchMUcrossSum`) it is a finite ℂ-combination of modes of `a₍s₎c ∈ 𝒱_{K+M−s−1}` on
  `d`; it collapses onto the `Pres_mem_Onm`-towers — the shift-`0`, mixed-level twin of
  `leftProd_circ_commutator_family_mem_On` (`ZhuVermaAnDescent4`).

## What is proved here (axiom-clean)

* **`CrossCFirstOnm`** / **`CrossCommOnm`** — the two precise generator-family sub-predicates.
* **`crossCircOnmGen_of_families`** — `CrossCFirstOnm W n → CrossCommOnm W n → CrossCircOnmGen W n`
  (the combination, by `Submodule.add_mem`): the precise reduction of the last cross family to its
  two named single-family sub-identities.
* **`MUGradedAction_of_families`** — the FULL `MUGradedAction W` assembly conditional on the two
  generator-family sub-predicates ALONE (combining `crossCircOnmGen_of_families` with the already-
  proved `MUGradedAction_of_CrossCircOnmGen`).

This isolates the remaining cross content to two clean single-family membership statements, each the
shift-`0` / level-`0`-inner twin of a PROVEN level-`n` membership: `CrossCommOnm` mirrors
`leftProd_circ_commutator_family_mem_On`, and `CrossCFirstOnm` mirrors the `c`-first-family branch of
`leftProd_circ_mem_On_homog` (both `ZhuVermaAnDescent4`), with the inner circle dropped from level `n`
to level `0`.

## The PRECISE remaining content (NOT `sorry`'d / NOT axiomatized) and its engine value

Both sub-predicates are engine-verified TRUE on the rank-1 free boson (the cross core lands in
`Onm` = circle + `OnmL`; the `OnmL` grading generators are load-bearing):

* `certificates/mathematica/mucross_circ_fast2.wl`: `JJJ n=1` combined residue ∈ circle + `OnmL` (True),
  ∉ circle-only (False).
* `certificates/mathematica/mucross_comm_nondeg.wl` (`a = c = a₂|0⟩, d = J, n = 1`): the commutator family
  alone ∈ circle + `OnmL` (True), and the `c`-first family alone ∈ circle + `OnmL` (True) — both
  sub-predicates hold non-degenerately (the commutator is non-zero here).
* `certificates/mathematica/mucross_combined.wl`/`certificates/mathematica/mucross_decide2.wl`: a single LEVEL-`0` circle is NOT
  generically in `Onm W n 0` (no clean `O(𝒱) ⊆ Onm W n 0` containment) — so `CrossCFirstOnm` is a
  genuine `i`-summed cancellation identity, not a term-wise containment; the `cbz K i`-weighted
  `i`-sum (and the `OnmL` generators) are essential.

`CrossCFirstOnm` is the genuine cross combinatorial content (the depth-`n` level-shift collapse of a
level-`0`-circle `i`-sum into the level-`n` ideal `Onm`); `CrossCommOnm` is the cross commutator
collapse (the shift-`0` lift of `leftProd_circ_commutator_family_mem_On`).  They are left as the two
precise stated sub-predicates, NOT a `sorry`/axiom.

## References
Dong–Jiang, Math. Z. 259 (2008) 799–826 (`math/0601626`), §2 (Lemma 2.8); Frenkel–Zhu Lemma 2.1.2;
Dong–Li–Mason, J. Algebra 206 (1998) 67–96; Gannon §5.3.2, Thm 5.3.4.
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The two precise generator-family sub-predicates of the cross membership. -/

/-- **The `c`-first family sub-predicate** (`Prop`).  For all grades `K M P` and homogeneous
`a ∈ 𝒱_K`, `c ∈ 𝒱_M`, `d ∈ 𝒱_P`, the `c`-first family of LEVEL-`0` Zhu circles lies in `Onm W n 0`:

  `∑_{i≤K} C(K,i) • anmCirc W 0 0 c (a₍i−n−1₎ d) ∈ Onm W n 0`.

The inner circle is level `0` (pole `2`, `anmCirc W 0 0 = resHom W 0 2`), NOT the `Onm` level `n`
(pole `n+2`).  This is the genuine cross subtlety: a single level-`0` circle is NOT generically in
`Onm W n 0` (`certificates/mathematica/mucross_O0sub.wl`); the `cbz K i`-weighted `i`-sum is, via the
level-shift collapse against BOTH `Onm` generator families (circle towers `Pres_mem_Onm` + the `OnmL`
grading generators `anmLgen`) — the level-`0`-inner twin of the `c`-first branch of
`leftProd_circ_mem_On_homog` (`ZhuVermaAnDescent4`). -/
def CrossCFirstOnm (W : VertexOperatorAlgebra 𝒱) (n : ℕ) : Prop :=
  ∀ (K M P : ℕ), ∀ a ∈ W.grading (K : ℤ), ∀ c ∈ W.grading (M : ℤ),
    ∀ d ∈ W.grading (P : ℤ),
    (∑ i ∈ Finset.range (K + 1),
        cbz (K : ℤ) (i : ℤ) • anmCirc W 0 0 c (W.smul a ((i : ℤ) - ((n : ℤ) + 1)) d))
      ∈ Onm W n 0

/-- **The commutator family sub-predicate** (`Prop`).  For all grades `K M P` and homogeneous
`a ∈ 𝒱_K`, `c ∈ 𝒱_M`, `d ∈ 𝒱_P`, the cross commutator family lies in `Onm W n 0`:

  `crossCircComm W n K M a c d ∈ Onm W n 0`.

By `crossCircComm_jsum_expand` (`ZhuVermaAnArchMUcrossSum`) it is a finite ℂ-combination of modes of
`a₍s₎c ∈ 𝒱_{K+M−s−1}` (`crossCircComm_base_mem_grading`) acting on `d` — the `d`-tower base content;
it collapses onto the `Pres_mem_Onm`-towers (`ZhuVermaAnArchMUcirc`).  This is the shift-`0`,
mixed-level twin of the PROVEN `leftProd_circ_commutator_family_mem_On` (`ZhuVermaAnDescent4`). -/
def CrossCommOnm (W : VertexOperatorAlgebra 𝒱) (n : ℕ) : Prop :=
  ∀ (K M P : ℕ), ∀ a ∈ W.grading (K : ℤ), ∀ c ∈ W.grading (M : ℤ),
    ∀ d ∈ W.grading (P : ℤ),
    crossCircComm W n K M a c d ∈ Onm W n 0

/-! ## The combination: the two sub-predicates give `CrossCircOnmGen`. -/

/-- **`CrossCFirstOnm W n → CrossCommOnm W n → CrossCircOnmGen W n`.**  The combined two-family form
is the sum of the `c`-first family and the commutator family; by `Submodule.add_mem` it lies in
`Onm W n 0` whenever both families do.  This is the precise reduction of the last cross membership
`CrossCircOnmGen` to its two named single-family sub-identities. -/
theorem crossCircOnmGen_of_families (W : VertexOperatorAlgebra 𝒱) (n : ℕ)
    (hCF : CrossCFirstOnm W n) (hComm : CrossCommOnm W n) :
    CrossCircOnmGen W n := by
  intro K M P a ha c hc d hd
  exact (Onm W n 0).add_mem (hCF K M P a ha c hc d hd) (hComm K M P a ha c hc d hd)

/-! ## (hcrossCirc) and the full `MUGradedAction W`, conditional on the two sub-predicates. -/

/-- **(hcrossCirc) from the two cross sub-predicates.**  Combining `crossCircOnmGen_of_families` with
`anmRight_zero_crossCirc_mem_Onm_of_OnmGen` (`ZhuVermaAnArchMUcrossMem`) discharges the cross-level
circle closure `anmRight W n 0 a (anmCirc W 0 0 c d) ∈ Onm W n 0` for ALL `a c d : 𝒱`. -/
theorem anmRight_zero_crossCirc_mem_Onm_of_families (W : VertexOperatorAlgebra 𝒱) (n : ℕ)
    (hCF : CrossCFirstOnm W n) (hComm : CrossCommOnm W n) (a c d : 𝒱) :
    anmRight W n 0 a (anmCirc W 0 0 c d) ∈ Onm W n 0 :=
  anmRight_zero_crossCirc_mem_Onm_of_OnmGen W n (crossCircOnmGen_of_families W n hCF hComm) a c d

/-- **The full `MUGradedAction W` assembly, conditional on the two cross sub-predicates.**  Given the
two generator-family sub-predicates `CrossCFirstOnm W n` and `CrossCommOnm W n` for every level `n`,
the Dong–Jiang composition crux `MUGradedAction W` holds.  Routes through
`crossCircOnmGen_of_families` and the already-proved `MUGradedAction_of_CrossCircOnmGen`
(`ZhuVermaAnArchMUcrossMem`), which consumes the closed diagonal-circle family (`hcirc_closed`) and
the closed cross grading family (`anmRight_zero_crossL_mem_Onm`). -/
theorem MUGradedAction_of_families (W : VertexOperatorAlgebra 𝒱)
    (hCF : ∀ n : ℕ, CrossCFirstOnm W n) (hComm : ∀ n : ℕ, CrossCommOnm W n) :
    MUGradedAction W :=
  MUGradedAction_of_CrossCircOnmGen W
    (fun n => crossCircOnmGen_of_families W n (hCF n) (hComm n))

/-! ## Status — the last Game-One cross family split into two precise single-family sub-predicates.

Proved here (`#print axioms` = `[propext, Classical.choice, Quot.sound]`; no `sorry`/
`axiom`/`pbw`):

* **`CrossCFirstOnm`** / **`CrossCommOnm`** — the two precise generator-family sub-predicates of the
  last cross membership.
* **`crossCircOnmGen_of_families`** — `CrossCFirstOnm W n → CrossCommOnm W n → CrossCircOnmGen W n`
  (the trivial combination by `Submodule.add_mem`).
* **`anmRight_zero_crossCirc_mem_Onm_of_families`** — (hcrossCirc) from the two sub-predicates.
* **`MUGradedAction_of_families`** — the FULL `MUGradedAction W` assembly conditional on the two
  generator-family sub-predicates alone.

**Remaining content (engine-verified TRUE, free boson; NOT faked):** the two single-family
sub-predicates `CrossCFirstOnm W n` and `CrossCommOnm W n`.

* `CrossCFirstOnm W n`: `∑_{i≤K} C(K,i) • anmCirc W 0 0 c (a₍i−n−1₎ d) ∈ Onm W n 0`.  The inner
  circle is LEVEL `0` (pole `2`); a single level-`0` circle is NOT generically in `Onm W n 0`
  (`certificates/mathematica/mucross_O0sub.wl`), so this is a genuine `cbz K i`-weighted `i`-sum cancellation/level-shift
  identity into the level-`n` ideal, carried by the `Pres_mem_Onm`-towers AND the `OnmL` grading
  generators `anmLgen` (the shift-`−n` part) — the level-shift mirror of `crossLRest_eq`
  (`ZhuVermaAnArchMUcross`).  The level-`0`-inner twin of the `c`-first branch of
  `leftProd_circ_mem_On_homog` (`ZhuVermaAnDescent4`).
* `CrossCommOnm W n`: `crossCircComm W n K M a c d ∈ Onm W n 0`.  By `crossCircComm_jsum_expand`
  (`ZhuVermaAnArchMUcrossSum`) a finite ℂ-combination of modes of `a₍s₎c ∈ 𝒱_{K+M−s−1}` on `d`,
  collapsing onto the `Pres_mem_Onm`-towers — the shift-`0`, mixed-level twin of the PROVEN
  `leftProd_circ_commutator_family_mem_On` (`ZhuVermaAnDescent4`).

Engine values:
* `certificates/mathematica/mucross_circ_fast2.wl`: `JJJ n=1` combined residue ∈ circle + `OnmL` (True), ∉ circle-only
  (False).
* `certificates/mathematica/mucross_comm_nondeg.wl` (`a = c = a₂|0⟩, d = J, n = 1`): commutator family alone ∈ circle + `OnmL`
  (True); `c`-first family alone ∈ circle + `OnmL` (True) — both sub-predicates hold
  non-degenerately (the commutator is non-zero here).
* `certificates/mathematica/mucross_combined.wl`/`certificates/mathematica/mucross_decide2.wl`: no clean `O(𝒱) ⊆ Onm W n 0` containment (the `i`-sum,
  and the `OnmL` generators, are load-bearing).

Discharging both sub-predicates closes (hcrossCirc) outright via
`anmRight_zero_crossCirc_mem_Onm_of_families`, and then `MUGradedAction_of_families` supplies the full
DJ `M(U)` `V`-action crux `MUGradedAction W`.
-/

end VOA

/-
`#print axioms` check (each of the following prints
`[propext, Classical.choice, Quot.sound]`, NO `pbw`, NO `sorryAx`):

  #print axioms VOA.crossCircOnmGen_of_families
  #print axioms VOA.anmRight_zero_crossCirc_mem_Onm_of_families
  #print axioms VOA.MUGradedAction_of_families
-/
