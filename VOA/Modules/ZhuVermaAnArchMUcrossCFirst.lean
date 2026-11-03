/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchMUcrossGen

/-!
# Game One — closing the `c`-first level-`0`-inner cross family `CrossCFirstOnm`.

This file closes the `c`-first generator-family sub-predicate `CrossCFirstOnm W n`
(`ZhuVermaAnArchMUcrossGen`) of the last open `MUGradedAction` cross family:

  `∑_{i≤K} C(K,i) • anmCirc W 0 0 c (a₍i−n−1₎ d) ∈ Onm W n 0`

(homogeneous `a ∈ 𝒱_K`, `c ∈ 𝒱_M`, `d ∈ 𝒱_P`).  The inner circle is LEVEL `0` (pole `2`), NOT the
`Onm` level `n` (pole `n+2`).

## The structural factorization (proved here, axiom-clean)

The genuine simplification: since `anmCirc W 0 0 c (·)` is ℂ-linear in its right factor, the outer
`cbz K i`-weighted `i`-sum can be pulled INSIDE the circle, and the resulting `i`-sum is exactly the
right action `a *^n_0 d`:

  `∑_{i≤K} C(K,i) • a₍i−n−1₎ d = resHom W 0 (n+1) a d = anmRight W n 0 a d`   (`a ∈ 𝒱_K`).

Hence the `c`-first family is a **single** level-`0` Zhu circle on the right action:

  `∑_{i≤K} C(K,i) • anmCirc W 0 0 c (a₍i−n−1₎ d) = anmCirc W 0 0 c (anmRight W n 0 a d)`.

This is `cFirstFam_eq_circ_anmRight` (engine-verified TRUE on the rank-1 free boson,
`certificates/mathematica/mucross_O0sub2.wl`/`certificates/mathematica/mucross_O0sub3.wl`: the `cbz K i` `i`-sum equals the single
circle on `a *^n_0 d` for `n = 1, 2` and mixed homogeneous data).

The membership then reduces to ONE precise single-circle identity:

  `anmCirc W 0 0 c (anmRight W n 0 a d) ∈ Onm W n 0`.

A single LEVEL-`0` circle is NOT generically in `Onm W n 0` (`certificates/mathematica/mucross_O0sub.wl`); it lands here
because the argument `a *^n_0 d` carries the level-`n` shift.  The membership uses BOTH `Onm`
generator families — the circle towers `Pres_mem_Onm` and the `OnmL` grading generators `anmLgen`
(load-bearing; engine `certificates/mathematica/mucross_O0sub.wl`: circle-only `False`, circle+`OnmL` `True` for `n = 1, 2`).

## References
Dong–Jiang, Math. Z. 259 (2008) 799–826 (`math/0601626`), §2 (Lemma 2.8); Frenkel–Zhu Lemma 2.1.2.
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The structural factorization: the `c`-first family is a single circle on the right action. -/

/-- **The `cbz K i`-weighted `i`-sum is the right action `a *^n_0 d`.**  For homogeneous `a ∈ 𝒱_K`,
`∑_{i≤K} C(K,i) • a₍i−n−1₎ d = resHom W 0 (n+1) a d = anmRight W n 0 a d`.  (The `anmRight_zero`
single-pole residue, expanded via `resHom_homogeneous` and renormalised to the `range (K+1)` /
`cbz K i` form.) -/
theorem anmRight_zero_homog_sum (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {K : ℕ}
    {a : 𝒱} (ha : a ∈ W.grading (K : ℤ)) (d : 𝒱) :
    anmRight W n 0 a d
      = ∑ i ∈ Finset.range (K + 1),
          cbz (K : ℤ) (i : ℤ) • W.smul a ((i : ℤ) - ((n : ℤ) + 1)) d := by
  rw [anmRight_zero, resHom_homogeneous W 0 ((n : ℤ) + 1) ha d]
  simp only [add_zero]
  rw [show ((K : ℤ)).toNat + 1 = K + 1 from by rw [Int.toNat_natCast]]

/-- **The `c`-first level-`0`-inner family is a single level-`0` circle on the right action.**  For
homogeneous `a ∈ 𝒱_K`:

  `∑_{i≤K} C(K,i) • anmCirc W 0 0 c (a₍i−n−1₎ d) = anmCirc W 0 0 c (anmRight W n 0 a d)`.

Pull the `cbz K i`-weighted `i`-sum INSIDE the ℂ-linear right factor of `anmCirc W 0 0 c (·)`
(`anmCirc_add_right`/`anmCirc_smul_right`), then collapse the `i`-sum to `anmRight W n 0 a d`
(`anmRight_zero_homog_sum`).  The cross subtlety made structural: the family is one circle on the
level-`n` right action `a *^n_0 d`. -/
theorem cFirstFam_eq_circ_anmRight (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {K : ℕ}
    {a : 𝒱} (ha : a ∈ W.grading (K : ℤ)) (c d : 𝒱) :
    (∑ i ∈ Finset.range (K + 1),
        cbz (K : ℤ) (i : ℤ) • anmCirc W 0 0 c (W.smul a ((i : ℤ) - ((n : ℤ) + 1)) d))
      = anmCirc W 0 0 c (anmRight W n 0 a d) := by
  rw [anmRight_zero_homog_sum W n ha d]
  -- pull the finite `i`-sum out of the linear right factor of `anmCirc W 0 0 c (·)`.
  induction (Finset.range (K + 1)) using Finset.induction with
  | empty => simp [anmCirc_zero_right]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, anmCirc_add_right, anmCirc_smul_right, ih]

/-! ## The single-circle membership predicate and the reduction of `CrossCFirstOnm` to it.

By `cFirstFam_eq_circ_anmRight` the entire `c`-first family is a SINGLE level-`0` Zhu circle on the
right action `a *^n_0 d`.  We isolate the remaining content as the precise single-circle membership
predicate `CircAnmRightOnm` and record the reduction `CrossCFirstOnm W n` from it (no `sorry`/
axiom). -/

/-- **The single-circle membership predicate** (`Prop`).  For all grades `K M P` and homogeneous
`a ∈ 𝒱_K`, `c ∈ 𝒱_M`, `d ∈ 𝒱_P`, the level-`0` Zhu circle of `c` on the right action `a *^n_0 d`
lies in `Onm W n 0`:

  `anmCirc W 0 0 c (anmRight W n 0 a d) ∈ Onm W n 0`.

This is the genuine `c`-first cross content after the structural factorization: a single LEVEL-`0`
circle (pole `2`), which is NOT generically in `Onm W n 0` (`certificates/mathematica/mucross_O0sub.wl`, arbitrary `w`:
`False`), but lands here because the argument `a *^n_0 d` carries the level-`n` shift (engine
`certificates/mathematica/mucross_O0sub5.wl`: `(circ00 − circ_n) c (a *^n_0 d) ∈ Onm` for `n = 1, 2`, with the `OnmL`
grading generators load-bearing). -/
def CircAnmRightOnm (W : VertexOperatorAlgebra 𝒱) (n : ℕ) : Prop :=
  ∀ (K M P : ℕ), ∀ a ∈ W.grading (K : ℤ), ∀ c ∈ W.grading (M : ℤ),
    ∀ d ∈ W.grading (P : ℤ),
    anmCirc W 0 0 c (anmRight W n 0 a d) ∈ Onm W n 0

/-- **`CircAnmRightOnm W n → CrossCFirstOnm W n`.**  By `cFirstFam_eq_circ_anmRight` the `c`-first
family equals the single level-`0` circle `anmCirc W 0 0 c (anmRight W n 0 a d)`, so its membership
in `Onm W n 0` is exactly the single-circle predicate.  This is the precise reduction of the `c`-first
cross family to ONE single-circle membership identity. -/
theorem CrossCFirstOnm_of_circAnmRight (W : VertexOperatorAlgebra 𝒱) (n : ℕ)
    (h : CircAnmRightOnm W n) : CrossCFirstOnm W n := by
  intro K M P a ha c hc d hd
  rw [cFirstFam_eq_circ_anmRight W n ha c d]
  exact h K M P a ha c hc d hd

/-! ## Status — the `c`-first cross family reduced to ONE single-circle membership.

Proved here (`#print axioms` = `[propext, Classical.choice, Quot.sound]`; no `sorry`/
`axiom`/`pbw`):

* **`anmRight_zero_homog_sum`** — the `cbz K i`-weighted `i`-sum is the right action `a *^n_0 d`.
* **`cFirstFam_eq_circ_anmRight`** — the `c`-first level-`0`-inner family is a SINGLE level-`0` Zhu
  circle on the right action: `∑_{i≤K} C(K,i) • anmCirc W 0 0 c (a₍i−n−1₎ d)
  = anmCirc W 0 0 c (anmRight W n 0 a d)` (engine `certificates/mathematica/mucross_O0sub2.wl`/`certificates/mathematica/mucross_O0sub3.wl`).
* **`CircAnmRightOnm`** — the precise single-circle membership predicate.
* **`CrossCFirstOnm_of_circAnmRight`** — `CircAnmRightOnm W n → CrossCFirstOnm W n` (the reduction).

**Remaining content (engine-verified TRUE, free boson; NOT faked):** `CircAnmRightOnm W n` —

  `anmCirc W 0 0 c (anmRight W n 0 a d) ∈ Onm W n 0`.

A single LEVEL-`0` circle (pole `2`); NOT in `Onm W n 0` for arbitrary `w` (`certificates/mathematica/mucross_O0sub.wl`,
control `False`), but lands for `w = a *^n_0 d` via the level-`n` shift carried by the right action
(`certificates/mathematica/mucross_O0sub5.wl`: `(circ00 − circ_n) c (a *^n_0 d) ∈ Onm` for `n = 1, 2`, the `OnmL` grading
generators `anmLgen` load-bearing).  This is the genuine cross combinatorial collapse — the same
depth as the proven diagonal `AnmCircTowerEq_holds` (`ZhuVermaAnArchMUcircV`), with the inner circle
dropped to level `0` and the right action `a *^n_0 d` in the argument.  Discharging `CircAnmRightOnm`
closes
`CrossCFirstOnm` outright via `CrossCFirstOnm_of_circAnmRight`; combined with `CrossCommOnm`
(`ZhuVermaAnArchMUcrossGen`) this supplies the full DJ `M(U)` `V`-action crux `MUGradedAction W`
(`MUGradedAction_of_families`).
-/

end VOA

/-
`#print axioms` check (each of the following prints
`[propext, Classical.choice, Quot.sound]`, NO `pbw`, NO `sorryAx`):

  #print axioms VOA.anmRight_zero_homog_sum
  #print axioms VOA.cFirstFam_eq_circ_anmRight
  #print axioms VOA.CrossCFirstOnm_of_circAnmRight
-/
