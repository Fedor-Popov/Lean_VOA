/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchMUcrossClose
import VOA.Modules.ZhuVermaAnArchMUcrossSum
import VOA.Modules.ZhuVermaAnArchMUcircV

/-!
# Game One — the cross membership route `CrossCircCoreHM` via the OnmL grading generators.

This file works on the LAST open `MUGradedAction` family of the Dong–Jiang induced module `M(U)`
`V`-action: the **cross-level circle** core `CrossCircCoreHM W n`
(`ZhuVermaAnArchMUcrossClose`),

  `resHom W 0 (n+1) a (resHom W 0 2 c d) ∈ Onm W n 0`   (homogeneous `a ∈ 𝒱_K`, `c ∈ 𝒱_M`,
  `d ∈ 𝒱_P`),

i.e. the outer level-`n` residue (pole `n+1`, the right action `a *^n_0 (·)`) applied to the inner
**level-`0`** Zhu circle `anmCirc W 0 0 c d = resHom W 0 2 c d` (pole `2`).  This is the `m = 0`,
mixed-level analogue of the PROVEN left-slot `leftProd_circ_mem_On` (`ZhuVermaAnDescent4`).

## The MEMBERSHIP — not a circle-tower equation (engine-corrected route)

Two prior cross *sub-predicates* (the pure-circle-tower predicates `CrossCircTowerEq`
(`ZhuVermaAnArchMUcrossHM`) and the per-`j` `CrossCircTermTowerEq`
(`ZhuVermaAnArchMUcrossTerm`)) were
engine-**DISPROVEN**: the combined cross residue is NOT in the `PresAnm`-circle-tower span on the
rank-1 free boson (`certificates/mathematica/mucross_decide2.wl`).  The CORRECT target is the
**MEMBERSHIP** `resHom W 0 (n+1) a (resHom W 0 2 c d) ∈ Onm W n 0`, using `Onm = span{anmCirc} ⊔
OnmL` — i.e. the **grading generators** `anmLgen` (`OnmL`) are genuinely required, exactly as the
proven `leftProd_circ_mem_On` lands in `On` INCLUDING the `L₋₁+L₀` generators (`OnL`).  This is
re-confirmed here by `certificates/mathematica/mucross_circ_fast2.wl`:

  `JJJ n=1` (target grade 5): in circle-gens ONLY? **False**; in circle + `OnmL`-gens? **True**.

So `Onm`'s `OnmL` summand is load-bearing — the c-first level-`0`-circle family is NOT in the
circle-generator span alone, and is brought into `Onm` only with the `anmLgen` generators (the
shift-`m−n = −n` grading part) plus the commutator family — the cross mirror of how `crossLRest`
(`ZhuVermaAnArchMUcross`) collapses the level-`0` `(L₋₁+L₀)` action onto `anmLgen W n 0` + circle.

## What is proved here (axiom-clean)

* **`crossCirc_combined_eq`** — the cross residue-of-residue equals the COMBINED two-family form
  `(∑_{i≤K} C(K,i) • anmCirc W 0 0 c (a₍i−n−1₎ d)) + crossCircComm W n K M a c d`
  (re-exporting `crossCirc_core_eq_circ0Sum_add_comm`, `ZhuVermaAnArchMUcrossSum`).
* **`CrossCircOnmGen`** — the **precise remaining membership predicate**: the combined two-family
  form lies in `Onm W n 0` (for all homogeneous data).  This is the genuine cross combinatorial
  content; the `OnmL` grading generators ARE used (engine, `certificates/mathematica/mucross_circ_fast2.wl`).
* **`crossCircCoreHM_of_OnmGen`** — `CrossCircOnmGen W n → CrossCircCoreHM W n`, the bridge that
  turns the membership predicate into the consumed homogeneous core (via `crossCirc_combined_eq`).
* **`MUGradedAction_of_CrossCircOnmGen`** — the FULL `MUGradedAction W` assembly **conditional on
  `CrossCircOnmGen`** alone: it consumes `hcirc_closed`/`AnmRightModule_closed` (the diagonal circle
  family, already closed, `ZhuVermaAnArchMUcircV`), `anmRight_zero_crossL_mem_Onm` (hcrossL, already
  closed, `ZhuVermaAnArchMUcross`), and the cross-circle family discharged from `CrossCircOnmGen`.

This reduces the entire last `MUGradedAction` family to the ONE precise membership predicate
`CrossCircOnmGen W n` (engine-verified TRUE, free boson; NOT a `sorry`/axiom).

## The PRECISE remaining content (NOT `sorry`'d / NOT axiomatized)

`CrossCircOnmGen W n` is the membership of the explicit combined two-family form in `Onm W n 0`.
By `crossCircCFirst_eq_anmCirc0Sum` the first family is the `cbz K i`-weighted `i`-sum of the
level-`0` circle `anmCirc W 0 0 c (a₍i−n−1₎ d)` (pole `2`, NOT in `Onm`'s pole-`n+2` circle span
alone); by `crossCircComm_jsum_expand` the commutator family is a finite ℂ-combination of modes of
`a₍s₎c ∈ 𝒱_{K+M−s−1}` on `d`.  The combined collapse into `Onm` is carried by the level-shift mirror
of `crossLRest_eq` (`ZhuVermaAnArchMUcross`), which converts the `−n`-shifted grading action onto
`anmLgen W n 0` generators + `PresAnm`-towers (`Pres_mem_Onm`, `ZhuVermaAnArchMUcirc`).  Engine
values:
* `certificates/mathematica/mucross_circ_fast2.wl`: `JJJ n=1` combined residue ∈ circle + `OnmL` (True), ∉ circle-only
  (False).
* `certificates/mathematica/mucross_comm_nondeg.wl`: `a=c=d` Heisenberg: commutator family vanishes, the c-first family is
  the whole content and lands in circle + `OnmL` (True).
It is left as the precise stated `CrossCircOnmGen` predicate, NOT a `sorry`/axiom.

## References
Dong–Jiang, Math. Z. 259 (2008) 799–826 (`math/0601626`), §2 (Lemma 2.8); Frenkel–Zhu Lemma 2.1.2;
Dong–Li–Mason, J. Algebra 206 (1998) 67–96; Gannon §5.3.2, Thm 5.3.4.
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The combined two-family form of the cross residue-of-residue (re-export). -/

/-- **The cross residue-of-residue equals the combined two-family form.**  For homogeneous
`a ∈ 𝒱_K`, `c ∈ 𝒱_M`,
`resHom W 0 (n+1) a (resHom W 0 2 c d)
   = (∑_{i≤K} C(K,i) • anmCirc W 0 0 c (a₍i−n−1₎ d)) + crossCircComm W n K M a c d`.
(Re-export of `crossCirc_core_eq_circ0Sum_add_comm`, `ZhuVermaAnArchMUcrossSum`.)  The first summand
is the `c`-first **level-`0`** Zhu-circle `i`-sum (pole `2`); the second is the commutator
family. -/
theorem crossCirc_combined_eq (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {K M : ℕ}
    {a : 𝒱} (ha : a ∈ W.grading (K : ℤ)) {c : 𝒱} (hc : c ∈ W.grading (M : ℤ)) (d : 𝒱) :
    resHom W 0 ((n : ℤ) + 1) a (resHom W 0 2 c d)
      = (∑ i ∈ Finset.range (K + 1),
          cbz (K : ℤ) (i : ℤ) • anmCirc W 0 0 c (W.smul a ((i : ℤ) - ((n : ℤ) + 1)) d))
        + crossCircComm W n K M a c d :=
  crossCirc_core_eq_circ0Sum_add_comm W n ha hc d

/-! ## The precise remaining membership predicate (the genuine cross content). -/

/-- **The precise cross membership predicate** (`Prop`).  For all grades `K M P` and homogeneous
`a ∈ 𝒱_K`, `c ∈ 𝒱_M`, `d ∈ 𝒱_P`, the COMBINED two-family form

  `(∑_{i≤K} C(K,i) • anmCirc W 0 0 c (a₍i−n−1₎ d)) + crossCircComm W n K M a c d`

lies in `Onm W n 0`.  This is the genuine remaining cross combinatorial identity: it is the
membership of the combined `c`-first level-`0`-circle `i`-sum (pole `2`, NOT in the `Onm` circle span
alone) plus the commutator family, into `Onm = span{anmCirc} ⊔ OnmL` — the `OnmL` **grading**
generators are load-bearing (engine, `certificates/mathematica/mucross_circ_fast2.wl`).  It is the `m = 0`, mixed-level twin
of `leftProd_circ_mem_On_homog` (`ZhuVermaAnDescent4`), whose combined `c`-first + commutator lands
in `On` INCLUDING the `L₋₁+L₀` generators (`OnL`). -/
def CrossCircOnmGen (W : VertexOperatorAlgebra 𝒱) (n : ℕ) : Prop :=
  ∀ (K M P : ℕ), ∀ a ∈ W.grading (K : ℤ), ∀ c ∈ W.grading (M : ℤ), ∀ d ∈ W.grading (P : ℤ),
    (∑ i ∈ Finset.range (K + 1),
        cbz (K : ℤ) (i : ℤ) • anmCirc W 0 0 c (W.smul a ((i : ℤ) - ((n : ℤ) + 1)) d))
      + crossCircComm W n K M a c d ∈ Onm W n 0

/-! ## `CrossCircOnmGen W n → CrossCircCoreHM W n`. -/

/-- **`CrossCircOnmGen W n → CrossCircCoreHM W n`.**  Rewrites the consumed homogeneous core
`resHom W 0 (n+1) a (resHom W 0 2 c d)` to its combined two-family form (`crossCirc_combined_eq`)
and applies the membership predicate.  This is the precise reduction of the consumed
`CrossCircCoreHM` (`ZhuVermaAnArchMUcrossClose`) to the single cross membership identity. -/
theorem crossCircCoreHM_of_OnmGen (W : VertexOperatorAlgebra 𝒱) (n : ℕ)
    (hGen : CrossCircOnmGen W n) : CrossCircCoreHM W n := by
  intro K M P a ha c hc d hd
  rw [crossCirc_combined_eq W n ha hc d]
  exact hGen K M P a ha c hc d hd

/-! ## (hcrossCirc) from `CrossCircOnmGen`. -/

/-- **(hcrossCirc) from the cross membership predicate.**  Combining `crossCircCoreHM_of_OnmGen`
with `CrossCircCore_of_HM` (`ZhuVermaAnArchMUcrossClose`) and
`anmRight_zero_crossCirc_mem_Onm_of_core` (`ZhuVermaAnArchMUcross`) discharges the cross-level circle
closure `anmRight W n 0 a (anmCirc W 0 0 c d) ∈ Onm W n 0` for ALL `a c d : 𝒱`. -/
theorem anmRight_zero_crossCirc_mem_Onm_of_OnmGen (W : VertexOperatorAlgebra 𝒱) (n : ℕ)
    (hGen : CrossCircOnmGen W n) (a c d : 𝒱) :
    anmRight W n 0 a (anmCirc W 0 0 c d) ∈ Onm W n 0 :=
  anmRight_zero_crossCirc_mem_Onm_of_core W n
    (CrossCircCore_of_HM W n (crossCircCoreHM_of_OnmGen W n hGen)) a c d

/-! ## The FULL `MUGradedAction W` assembly, conditional on `CrossCircOnmGen` alone. -/

/-- **The full `MUGradedAction W` assembly, conditional on `CrossCircOnmGen`.**  Given the single
cross membership predicate `CrossCircOnmGen W n` for every level `n`, the Dong–Jiang composition crux
`MUGradedAction W` holds.  The two other families are already closed:
* `hcirc` (the diagonal circle family) by `hcirc_closed` (`ZhuVermaAnArchMUcircV`);
* `hcrossL` (the cross grading family) by `anmRight_zero_crossL_mem_Onm` (`ZhuVermaAnArchMUcross`);
and `hcrossCirc` (the cross circle family) is discharged here from `CrossCircOnmGen`.  This is the
precise reduction of the entire last `MUGradedAction` family to the one cross membership identity. -/
theorem MUGradedAction_of_CrossCircOnmGen (W : VertexOperatorAlgebra 𝒱)
    (hGen : ∀ n : ℕ, CrossCircOnmGen W n) :
    MUGradedAction W :=
  MUGradedAction_of_gens W
    (fun n c d v => hcirc_closed W n c d v)
    (fun n a c d => anmRight_zero_crossCirc_mem_Onm_of_OnmGen W n (hGen n) a c d)
    (fun n a c => anmRight_zero_crossL_mem_Onm W n a c)

/-! ## Status — the last Game-One cross family reduced to ONE precise MEMBERSHIP predicate.

Proved here (`#print axioms` = `[propext, Classical.choice, Quot.sound]`; no `sorry`/
`axiom`/`pbw`):

* **`crossCirc_combined_eq`** — the cross residue-of-residue equals the combined two-family form
  (re-export of `crossCirc_core_eq_circ0Sum_add_comm`).
* **`CrossCircOnmGen`** — the precise remaining cross MEMBERSHIP predicate (combined two-family form
  ∈ `Onm W n 0`, with the `OnmL` grading generators load-bearing).
* **`crossCircCoreHM_of_OnmGen`** — `CrossCircOnmGen W n → CrossCircCoreHM W n`.
* **`anmRight_zero_crossCirc_mem_Onm_of_OnmGen`** — (hcrossCirc) from `CrossCircOnmGen`.
* **`MUGradedAction_of_CrossCircOnmGen`** — the FULL `MUGradedAction W` assembly, conditional on
  `CrossCircOnmGen` alone (the other two families `hcirc`/`hcrossL` are already closed).

**Remaining content (engine-verified TRUE, free boson; NOT faked):** `CrossCircOnmGen W n` — the
combined two-family membership
`(∑_{i≤K} C(K,i) • anmCirc W 0 0 c (a₍i−n−1₎ d)) + crossCircComm W n K M a c d ∈ Onm W n 0`.
The `c`-first family is the `cbz K i`-weighted `i`-sum of the level-`0` Zhu circle `anmCirc W 0 0 c
(a₍i−n−1₎ d)` (pole `2`; `crossCircCFirst_eq_anmCirc0Sum`), and the commutator family is a finite
ℂ-combination of modes of `a₍s₎c` on `d` (`crossCircComm_jsum_expand`); the combined collapse into
`Onm` uses BOTH the circle generators (via `Pres_mem_Onm`) AND the `OnmL` grading generators
`anmLgen` — the cross level-shift mirror of `crossLRest_eq`.  Engine values:
* `certificates/mathematica/mucross_circ_fast2.wl`: `JJJ n=1` combined residue ∈ circle + `OnmL` = **True**, ∈ circle-only =
  **False** (the `OnmL` generators are load-bearing).
* `certificates/mathematica/mucross_comm_nondeg.wl`: Heisenberg `a=c=d`: the commutator family vanishes, the c-first family is
  the whole content and lands in circle + `OnmL` = **True**.
Discharging `CrossCircOnmGen` closes (hcrossCirc) outright via
`anmRight_zero_crossCirc_mem_Onm_of_OnmGen`, and then `MUGradedAction_of_CrossCircOnmGen` supplies
the full DJ `M(U)` `V`-action crux `MUGradedAction W`.
-/

end VOA
