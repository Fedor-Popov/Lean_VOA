/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchMUcrossCFirst

/-!
# Game One — the level-`0`-inner circle membership `CircAnmRightOnm` (pole-`2` diagonal twin).

This file works on the single remaining level-`0`-inner circle membership predicate
`CircAnmRightOnm W n` (`ZhuVermaAnArchMUcrossCFirst`):

  `anmCirc W 0 0 c (anmRight W n 0 a d) ∈ Onm W n 0`   (homogeneous `a ∈ 𝒱_K`, `c ∈ 𝒱_M`,
  `d ∈ 𝒱_P`).

The OUTER operation is the LEVEL-`0` Zhu circle `anmCirc W 0 0 c (·) = resHom W 0 2 c (·)`
(pole `2`), applied to the right action `anmRight W n 0 a d = resHom W 0 (n+1) a d`.  Discharging it
closes `CrossCFirstOnm W n` outright via `CrossCFirstOnm_of_circAnmRight`.

## The pole-`2`/pole-`(n+2)` split (proved here, axiom-clean)

The genuine structural simplification: the level-`0` outer circle is split against the level-`n`
outer circle on the *same* right factor `w := anmRight W n 0 a d`,

  `anmCirc W 0 0 c w = anmCirc W n 0 c w + (anmCirc W 0 0 c w − anmCirc W n 0 c w)`,

and the second summand `anmCirc W n 0 c w` is **trivially** a level-`n` circle generator, hence
`∈ Onm W n 0` (`anmCirc_mem_Onm`).  This peels off the trivial circle generator and reduces
`CircAnmRightOnm W n` to the single **pole-difference membership**

  `(CircDiffAnmRightOnm)   anmCirc W 0 0 c w − anmCirc W n 0 c w ∈ Onm W n 0`.

This split is correct because `anmCirc W 0 0` and `anmCirc W n 0` are the SAME residue map up to the
pole (`resHom W 0 2` vs `resHom W 0 (n+2)`), so the difference carries the entire level-mismatch
content while the level-`n` piece lands in the ideal for free.

## Engine status (free boson, rank 1; NOT faked)

`certificates/mathematica/mucross_O0sub5.wl` (re-run here) verifies, for `n = 1, 2` and `a = c = d = J`:

* `anmCirc W n 0 c w ∈ Onm W n 0` — **True** (the trivial circle generator, discharged below);
* `(anmCirc W 0 0 c w − anmCirc W n 0 c w) ∈ Onm W n 0` — **True** (the pole-difference, the precise
  remaining content `CircDiffAnmRightOnm`);

so `anmCirc W 0 0 c w ∈ Onm W n 0` (the target) is **True** as the sum of the two.  The control
`certificates/mathematica/mucross_O0sub5.wl` `q2` confirms `anmCirc W 0 0 c w(arbitrary) ∉ Onm W n 0`, so
the membership genuinely uses the level-`n` shift carried by the right action `w = a *^n_0 d` — the
pole-difference is NOT a free combination of grading generators
(`certificates/mathematica/circ_diff_L.wl`: `inOnmL? False`), nor of the restricted `PresAnm`-tower
U/V families
(`certificates/mathematica/diff_tower.wl`: `False`); it requires the full level-`n` circle-generator
span (arbitrary `anmCirc W n 0 u v`), i.e. the deep Dong–Jiang Lemma 2.8 collapse.

## References
Dong–Jiang, Math. Z. 259 (2008) 799–826 (`math/0601626`), §2 (Lemma 2.8); Frenkel–Zhu Lemma 2.1.2;
Dong–Li–Mason; Gannon §5.3.2, Thm 5.3.4.
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The pole-difference membership predicate and the split of `CircAnmRightOnm`. -/

/-- **The pole-difference membership predicate** (`Prop`).  For all grades `K M P` and homogeneous
`a ∈ 𝒱_K`, `c ∈ 𝒱_M`, `d ∈ 𝒱_P`, the difference of the level-`0` and level-`n` Zhu circles of `c`
on the right action `a *^n_0 d` lies in `Onm W n 0`:

  `anmCirc W 0 0 c (anmRight W n 0 a d) − anmCirc W n 0 c (anmRight W n 0 a d) ∈ Onm W n 0`.

This is the genuine level-`0`-inner cross content after the trivial level-`n` circle generator is
peeled off.  It is NOT a free grading-generator combination (`certificates/mathematica/circ_diff_L.wl`:
`inOnmL? False`) nor a restricted `PresAnm`-tower U/V combination
(`certificates/mathematica/diff_tower.wl`: `False`); it lands in `Onm W n 0` via the full level-`n`
circle-generator span (the deep DJ Lemma 2.8 collapse), engine-verified TRUE on the rank-1 free
boson for `n = 1, 2` (`certificates/mathematica/mucross_O0sub5.wl`). -/
def CircDiffAnmRightOnm (W : VertexOperatorAlgebra 𝒱) (n : ℕ) : Prop :=
  ∀ (K M P : ℕ), ∀ a ∈ W.grading (K : ℤ), ∀ c ∈ W.grading (M : ℤ),
    ∀ d ∈ W.grading (P : ℤ),
    anmCirc W 0 0 c (anmRight W n 0 a d) - anmCirc W n 0 c (anmRight W n 0 a d) ∈ Onm W n 0

/-- **The level-`n` circle generator on the right action lies in `Onm W n 0`** (trivially).  For any
`c` and `w := anmRight W n 0 a d`, the level-`n` circle `anmCirc W n 0 c w` is a circle generator of
`Onm W n 0`, so it lies there by `anmCirc_mem_Onm`.  (The level-`n` outer pole `n+2` matches the
ideal level `n`; no combinatorial content.) -/
theorem anmCirc_n_anmRight_mem_Onm (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (a c d : 𝒱) :
    anmCirc W n 0 c (anmRight W n 0 a d) ∈ Onm W n 0 :=
  anmCirc_mem_Onm W n 0 c (anmRight W n 0 a d)

/-- **The pole split** `anmCirc W 0 0 c w = anmCirc W n 0 c w + (anmCirc W 0 0 c w − anmCirc W n 0
c w)`.  Pure additive rearrangement (`add_sub_cancel`); the substance is that the first summand on
the right lies in `Onm W n 0` for free (`anmCirc_n_anmRight_mem_Onm`), peeling the membership onto
the pole-difference. -/
theorem circ_zero_eq_circ_n_add_diff (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (a c d : 𝒱) :
    anmCirc W 0 0 c (anmRight W n 0 a d)
      = anmCirc W n 0 c (anmRight W n 0 a d)
        + (anmCirc W 0 0 c (anmRight W n 0 a d) - anmCirc W n 0 c (anmRight W n 0 a d)) := by
  rw [add_sub_cancel]

/-- **`CircDiffAnmRightOnm W n → CircAnmRightOnm W n`.**  Split `anmCirc W 0 0 c w` into the
level-`n` circle generator (in `Onm W n 0` for free) plus the pole-difference (by hypothesis);
both summands are in the ideal, so their sum — the target — is too.  This is the precise reduction
of the level-`0`-inner circle membership to the single pole-difference identity. -/
theorem CircAnmRightOnm_of_circDiff (W : VertexOperatorAlgebra 𝒱) (n : ℕ)
    (h : CircDiffAnmRightOnm W n) : CircAnmRightOnm W n := by
  intro K M P a ha c hc d hd
  rw [circ_zero_eq_circ_n_add_diff W n a c d]
  exact Submodule.add_mem _ (anmCirc_n_anmRight_mem_Onm W n a c d)
    (h K M P a ha c hc d hd)

/-- **`CircDiffAnmRightOnm W n → CrossCFirstOnm W n`** (the chained reduction).  Combine the pole
split `CircAnmRightOnm_of_circDiff` with the structural reduction `CrossCFirstOnm_of_circAnmRight`
(`ZhuVermaAnArchMUcrossCFirst`): discharging the pole-difference closes the entire `c`-first cross
family. -/
theorem CrossCFirstOnm_of_circDiff (W : VertexOperatorAlgebra 𝒱) (n : ℕ)
    (h : CircDiffAnmRightOnm W n) : CrossCFirstOnm W n :=
  CrossCFirstOnm_of_circAnmRight W n (CircAnmRightOnm_of_circDiff W n h)

/-! ## Status — the level-`0`-inner circle membership reduced to ONE pole-difference identity.

Proved here (`#print axioms` = `[propext, Classical.choice, Quot.sound]`; no `sorry`/
`axiom`/`pbw`):

* **`CircDiffAnmRightOnm`** — the precise pole-difference membership predicate.
* **`anmCirc_n_anmRight_mem_Onm`** — the level-`n` circle generator on `anmRight W n 0 a d` lies in
  `Onm W n 0` for free (`anmCirc_mem_Onm`); the trivial half of the split.
* **`circ_zero_eq_circ_n_add_diff`** — the pole split (additive rearrangement).
* **`CircAnmRightOnm_of_circDiff`** — `CircDiffAnmRightOnm W n → CircAnmRightOnm W n` (the reduction
  of the level-`0`-inner circle membership to the single pole-difference identity).
* **`CrossCFirstOnm_of_circDiff`** — `CircDiffAnmRightOnm W n → CrossCFirstOnm W n` (chained with
  `CrossCFirstOnm_of_circAnmRight`).

**Remaining content (engine-verified TRUE, free boson `n = 1, 2`; NOT faked):**
`CircDiffAnmRightOnm W n` —

  `anmCirc W 0 0 c (anmRight W n 0 a d) − anmCirc W n 0 c (anmRight W n 0 a d) ∈ Onm W n 0`.

This is the genuine cross combinatorial collapse: the pole-`2`/pole-`(n+2)` mismatch on the
level-`n` right action `a *^n_0 d`.  Engine analysis (`certificates/mathematica/`):

* `certificates/mathematica/mucross_O0sub5.wl` — `(circ00 − circN) c (a *^n_0 d) ∈ Onm` **True** (and `circN c (a *^n_0 d) ∈
  Onm` True, discharged above), so the target `circ00 c (a *^n_0 d) ∈ Onm` is True;
* `certificates/mathematica/circ_diff_L.wl` — the pole-difference is NOT in `OnmL` (grading generators) alone (**False**);
* `certificates/mathematica/diff_tower.wl` — nor in the restricted `PresAnm`-tower U/V families (level-`n` circle towers in
  `c` at `a₍g₎d` plus in `a` at `c₍g₎d`), even adjoined with `OnmL` (**False**);
* `certificates/mathematica/target_tower.wl` — the FULL target is NOT a U/V `PresAnm`-tower combination either (**False**) —
  so the naive `AnmCircTowerEq`-mirror does NOT hold for this cross structure (the `c`-first U-words
  are LEVEL-`0` circle towers, landing in `Onm W 0 0`, not `Onm W n 0`).

Hence the membership genuinely requires the FULL level-`n` circle-generator span (arbitrary
`anmCirc W n 0 u v`) — the deep Dong–Jiang Lemma 2.8 reorganisation — rather than a clean U/V tower
collapse.  Discharging `CircDiffAnmRightOnm` closes `CircAnmRightOnm`
(`CircAnmRightOnm_of_circDiff`), hence `CrossCFirstOnm` (`CrossCFirstOnm_of_circDiff` /
`CrossCFirstOnm_of_circAnmRight`); combined with `CrossCommOnm` (`ZhuVermaAnArchMUcrossGen`) this
supplies the full DJ `M(U)` `V`-action crux
`MUGradedAction W` (`MUGradedAction_of_families`).
-/

end VOA

/-
`#print axioms` check (each of the following prints
`[propext, Classical.choice, Quot.sound]`, NO `pbw`, NO `sorryAx`):

  #print axioms VOA.anmCirc_n_anmRight_mem_Onm
  #print axioms VOA.circ_zero_eq_circ_n_add_diff
  #print axioms VOA.CircAnmRightOnm_of_circDiff
  #print axioms VOA.CrossCFirstOnm_of_circDiff
-/
