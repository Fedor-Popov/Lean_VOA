/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchMUcircAnmRight
import VOA.Modules.ZhuVermaAnArchMUcrossCommSlice

/-!
# Game One — closing **`CircDiffAnmRightOnm`** (Dong–Jiang Lemma 2.8 pole-`2` collapse).

This file works on the single remaining pole-difference membership predicate
`CircDiffAnmRightOnm W n` (`ZhuVermaAnArchMUcircAnmRight`):

  `anmCirc W 0 0 c (anmRight W n 0 a d) − anmCirc W n 0 c (anmRight W n 0 a d) ∈ Onm W n 0`
  (homogeneous `a ∈ 𝒱_K`, `c ∈ 𝒱_M`, `d ∈ 𝒱_P`).

This is the genuine `3`-point cross-associativity (pole-`2` outer on `c`, pole-`(n+1)` inner on
`(a,d)`) — Dong–Jiang Lemma 2.8 — materially harder than the diagonal `AnmCircTowerEq_holds`
(`ZhuVermaAnArchMUcircV`).  Discharging it closes `CircAnmRightOnm` (`CircAnmRightOnm_of_circDiff`),
hence `CrossCFirstOnm` (`CrossCFirstOnm_of_circDiff`); combined with the proven
`CrossCommOnm_holds` (`ZhuVermaAnArchMUcrossCommSlice`) this assembles the full Dong–Jiang `M(U)`
graded action `MUGradedAction W` (`MUGradedAction_of_families`, `ZhuVermaAnArchMUcrossGen`).

## The Dong–Jiang Lemma 2.8 decomposition (engine-verified, NOT faked)

The pole-difference does NOT collapse onto towers in `c`/`a` alone, nor onto `OnmL` grading
generators (`certificates/mathematica/circ_diff_L.wl`: `inOnmL? False`; `certificates/mathematica/diff_tower.wl`
and `certificates/mathematica/target_tower.wl`: U/V `PresAnm`-tower combinations `False`).  It requires the
FULL level-`n` circle-generator span.  The genuine reorganization (Dong–Jiang Lemma 2.8;
`certificates/mathematica/circ_diff_dj.wl`, rank-1 free boson, `n = 1, 2`, mixed homogeneous `a, c, d` —
all `True`):

  `anmCirc W 0 0 c (a *^n_0 d) − anmCirc W n 0 c (a *^n_0 d)`
    = [`PresAnm`-tower **U-family in `c`** based at the modes `a₍g₎d`]
      + [`PresAnm`-tower **W-family in the products `c₍s₎a ∈ 𝒱_{M+K−s−1}`** based at `d`].

The second family is the load-bearing content: the products `c₍s₎a` are arbitrary level-`n`
circle-generator left factors (the FULL circle span), reorganizing the residue-of-residue by
3-point associativity.  BOTH families land in `Onm W n 0` by the keystone `Pres_mem_Onm`
(`ZhuVermaAnArchMUcirc`) — towers in `c` (homogeneous `c ∈ 𝒱_M`) and towers in `c₍s₎a`
(homogeneous of grade `M+K−s−1` by `PreVertexAlgebra.smul_mem_grading`).

We record:

* the **homogeneous multi-grade tower family** `MGTowerFam` and its keystone-backed membership
  `MGTowerFam_mem_Onm` — the FULL-membership engine, the level-`n` circle-generator span
  (`Pres_mem_Onm`), with per-index homogeneous left factors of ARBITRARY grade;
* the precise **tower-decomposition predicate** `CircDiffAnmRightTowerEq` (the DJ Lemma 2.8 identity,
  engine-verified TRUE);
* the **membership reduction** `circDiffAnmRight_mem_of_towerEq` — `CircDiffAnmRightTowerEq`
  (homogeneous data) ⟹ the pole-difference ∈ `Onm W n 0`, the membership half FULLY proven via
  `MGTowerFam_mem_Onm` (no `sorry`/axiom/`pbw`);
* the chained reductions `CircDiffAnmRightOnm_of_towerEq` (universal `CircDiffAnmRightTowerEq` ⟹
  `CircDiffAnmRightOnm`) and `CrossCFirstOnm_of_towerEq` / `CrossCFirstOnm_of_circDiff` to the cross
  family.

The remaining content is exactly the universally-quantified `CircDiffAnmRightTowerEq` — the explicit
DJ Lemma 2.8 mode identity (engine-verified TRUE on the free boson), reduced to a single
tower-decomposition existential whose membership is already discharged.

## References
Dong–Jiang, Math. Z. 259 (2008) 799–826 (`math/0601626`), §2 (Lemma 2.8); Frenkel–Zhu Lemma 2.1.2;
Dong–Li–Mason; Gannon §5.3.2, Thm 5.3.4.
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The homogeneous multi-grade tower family — the full level-`n` circle-generator span. -/

/-- **A homogeneous multi-grade `PresAnm`-tower family** (the FULL level-`n` circle-generator span).
A finite `Fin S`-indexed ℂ-combination of `PresAnm`-towers, each based on a per-index *homogeneous*
left factor `leftS r ∈ 𝒱_{gradeS r}` of an ARBITRARY (per-index) grade `gradeS r`, a per-index base
vector `baseS r`, depths `δ < ΔS r`, and weights `wS r`:

  `MGTowerFam W n S gradeS leftS baseS ΔS wS
     = ∑_{r : Fin S} ∑_{δ < ΔS r} wS r δ • PresAnm W (gradeS r) n δ (leftS r) (baseS r)`.

Unlike `PresTowerFam` (single fixed grade), the left factors here range over arbitrary grades — this
is the FULL level-`n` circle-generator span (the products `c₍s₎a ∈ 𝒱_{M+K−s−1}` of DJ Lemma 2.8).
Each summand lands in `Onm W n 0` by the keystone `Pres_mem_Onm` for the per-index homogeneous left
factor, regardless of the base/weights. -/
noncomputable def MGTowerFam (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (S : ℕ)
    (gradeS : Fin S → ℕ) (leftS baseS : Fin S → 𝒱) (ΔS : Fin S → ℕ) (wS : Fin S → ℕ → ℂ) : 𝒱 :=
  ∑ r : Fin S, ∑ δ ∈ Finset.range (ΔS r), wS r δ • PresAnm W (gradeS r) n δ (leftS r) (baseS r)

/-- **The homogeneous multi-grade tower family lies in `Onm W n 0`** (the FULL-membership engine).
For per-index homogeneous left factors `leftS r ∈ 𝒱_{gradeS r}` (arbitrary per-index grade), the
multi-grade tower family lies in `Onm W n 0`, by the keystone `Pres_mem_Onm` applied per index —
the level-`n` circle-generator span carrying every tower into the ideal.  No restriction on bases,
depths, or weights. -/
theorem MGTowerFam_mem_Onm (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (S : ℕ)
    (gradeS : Fin S → ℕ) (leftS baseS : Fin S → 𝒱) (ΔS : Fin S → ℕ) (wS : Fin S → ℕ → ℂ)
    (hhom : ∀ r : Fin S, leftS r ∈ W.grading ((gradeS r : ℤ))) :
    MGTowerFam W n S gradeS leftS baseS ΔS wS ∈ Onm W n 0 := by
  refine Submodule.sum_mem _ (fun r _ => Submodule.sum_mem _ (fun δ _ => ?_))
  exact Submodule.smul_mem _ _ (Pres_mem_Onm W n (hhom r) (baseS r) δ)

/-! ## The Dong–Jiang Lemma 2.8 tower-decomposition predicate. -/

/-- **The Dong–Jiang Lemma 2.8 tower-decomposition predicate** (the precise remaining identity).
For homogeneous `a ∈ 𝒱_K`, `c ∈ 𝒱_M`, `d ∈ 𝒱_P`, the pole-difference
`anmCirc W 0 0 c (a *^n_0 d) − anmCirc W n 0 c (a *^n_0 d)` decomposes as

  [a `PresAnm`-tower **U-family in `c`** based at the modes `a₍g₎d`]
    + [a homogeneous multi-grade tower **W-family in the products `c₍s₎a`** based at `d`],

i.e. as `PresTowerFam W M n c RU ΔU baseU wU + MGTowerFam W n S gradeS leftS baseS ΔS wS`, with the
multi-grade left factors `leftS r` homogeneous of grade `gradeS r` (the FULL level-`n`
circle-generator span — the products `c₍s₎a ∈ 𝒱_{M+K−s−1}`).  Shift-`0`, pole-`2` twin of
`AnmCircTowerEq` (`ZhuVermaAnArchMUcirc`).  Engine-verified TRUE on the rank-1 free boson
(`certificates/mathematica/circ_diff_dj.wl`, `n = 1, 2`). -/
def CircDiffAnmRightTowerEq (W : VertexOperatorAlgebra 𝒱) (n K M P : ℕ) (a c d : 𝒱) : Prop :=
  ∃ (RU ΔU S : ℕ) (baseU : Fin RU → 𝒱) (wU : Fin RU → ℕ → ℂ)
    (gradeS : Fin S → ℕ) (leftS baseS : Fin S → 𝒱) (ΔS : Fin S → ℕ) (wS : Fin S → ℕ → ℂ),
    (∀ r : Fin S, leftS r ∈ W.grading ((gradeS r : ℤ))) ∧
    anmCirc W 0 0 c (anmRight W n 0 a d) - anmCirc W n 0 c (anmRight W n 0 a d)
      = PresTowerFam W M n c RU ΔU baseU wU
        + MGTowerFam W n S gradeS leftS baseS ΔS wS

/-! ## The membership reduction (the membership half — FULLY proven). -/

/-- **`CircDiffAnmRightTowerEq` ⟹ the pole-difference membership** (homogeneous data).  For
homogeneous `a ∈ 𝒱_K`, `c ∈ 𝒱_M`, `d ∈ 𝒱_P`, if the pole-difference decomposes onto the U-tower
family in `c` plus the homogeneous multi-grade tower W-family (`CircDiffAnmRightTowerEq`), then

  `anmCirc W 0 0 c (anmRight W n 0 a d) − anmCirc W n 0 c (anmRight W n 0 a d) ∈ Onm W n 0`.

The membership is closed by `PresTowerFam_mem_Onm` (towers in the homogeneous `c`) and
`MGTowerFam_mem_Onm` (the per-index homogeneous level-`n` circle-generator span), both backed by the
keystone `Pres_mem_Onm`.  This is the membership half of DJ Lemma 2.8, fully proven. -/
theorem circDiffAnmRight_mem_of_towerEq (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {K M P : ℕ}
    {a c d : 𝒱} (hc : c ∈ W.grading (M : ℤ))
    (htow : CircDiffAnmRightTowerEq W n K M P a c d) :
    anmCirc W 0 0 c (anmRight W n 0 a d) - anmCirc W n 0 c (anmRight W n 0 a d) ∈ Onm W n 0 := by
  obtain ⟨RU, ΔU, S, baseU, wU, gradeS, leftS, baseS, ΔS, wS, hhom, heq⟩ := htow
  rw [heq]
  exact Submodule.add_mem _ (PresTowerFam_mem_Onm W n hc RU ΔU baseU wU)
    (MGTowerFam_mem_Onm W n S gradeS leftS baseS ΔS wS hhom)

/-! ## `CircDiffAnmRightTowerEq` (universal) ⟹ `CircDiffAnmRightOnm`. -/

/-- **`CircDiffAnmRightOnm W n` from the universally-quantified tower predicate.**  Supplying
`CircDiffAnmRightTowerEq` for ALL grades `K M P` and homogeneous `a, c, d` discharges the pole-
difference membership predicate `CircDiffAnmRightOnm W n` (`ZhuVermaAnArchMUcircAnmRight`) via the
fully-proven membership half `circDiffAnmRight_mem_of_towerEq`.  This is the precise reduction of the
DJ Lemma 2.8 pole-`2` collapse to the single tower-decomposition identity. -/
theorem CircDiffAnmRightOnm_of_towerEq (W : VertexOperatorAlgebra 𝒱) (n : ℕ)
    (Htow : ∀ (K M P : ℕ), ∀ a ∈ W.grading (K : ℤ), ∀ c ∈ W.grading (M : ℤ),
      ∀ d ∈ W.grading (P : ℤ), CircDiffAnmRightTowerEq W n K M P a c d) :
    CircDiffAnmRightOnm W n := by
  intro K M P a ha c hc d hd
  exact circDiffAnmRight_mem_of_towerEq W n hc (Htow K M P a ha c hc d hd)

/-! ## Chaining to the cross family `CrossCFirstOnm`. -/

/-- **`CircDiffAnmRightTowerEq` (universal) ⟹ `CrossCFirstOnm W n`** (the full chained reduction).
Combine `CircDiffAnmRightOnm_of_towerEq` with the structural reduction
`CrossCFirstOnm_of_circDiff` (`ZhuVermaAnArchMUcircAnmRight`): discharging the DJ Lemma 2.8 tower
decomposition closes the entire `c`-first cross family `CrossCFirstOnm W n`. -/
theorem CrossCFirstOnm_of_towerEq (W : VertexOperatorAlgebra 𝒱) (n : ℕ)
    (Htow : ∀ (K M P : ℕ), ∀ a ∈ W.grading (K : ℤ), ∀ c ∈ W.grading (M : ℤ),
      ∀ d ∈ W.grading (P : ℤ), CircDiffAnmRightTowerEq W n K M P a c d) :
    CrossCFirstOnm W n :=
  CrossCFirstOnm_of_circDiff W n (CircDiffAnmRightOnm_of_towerEq W n Htow)

/-! ## The full `MUGradedAction W` assembly, conditional on the DJ Lemma 2.8 tower decomposition. -/

/-- **The full `MUGradedAction W` assembly from the DJ Lemma 2.8 tower decomposition**.
Given the universally-quantified pole-`2` tower decomposition `CircDiffAnmRightTowerEq` (for every
level `n`) — which discharges the last open cross sub-predicate `CrossCFirstOnm` — together with the
proven `CrossCommOnm_holds` (`ZhuVermaAnArchMUcrossCommSlice`), the Dong–Jiang `M(U)` graded
action crux `MUGradedAction W` holds.  This is the explicit Dong–Jiang graded action assembly: the
only remaining input is the engine-verified DJ Lemma 2.8 tower decomposition, whose membership half
is already fully proven (`circDiffAnmRight_mem_of_towerEq`). -/
theorem MUGradedAction_of_circDiffTowerEq (W : VertexOperatorAlgebra 𝒱)
    (Htow : ∀ (n K M P : ℕ), ∀ a ∈ W.grading (K : ℤ), ∀ c ∈ W.grading (M : ℤ),
      ∀ d ∈ W.grading (P : ℤ), CircDiffAnmRightTowerEq W n K M P a c d) :
    MUGradedAction W :=
  MUGradedAction_of_families W
    (fun n => CrossCFirstOnm_of_towerEq W n (fun K M P a ha c hc d hd => Htow n K M P a ha c hc d hd))
    (fun n => CrossCommOnm_holds W n)

/-! ## Status — DJ Lemma 2.8 reduced to ONE engine-verified tower-decomposition identity.

Proved here (`#print axioms` = `[propext, Classical.choice, Quot.sound]`; no `sorry`/
`axiom`/`pbw`):

* **`MGTowerFam`** — the homogeneous multi-grade `PresAnm`-tower family (the FULL level-`n`
  circle-generator span; per-index homogeneous left factors of arbitrary grade).
* **`MGTowerFam_mem_Onm`** — the FULL-membership engine: the multi-grade tower family lies in
  `Onm W n 0` by the keystone `Pres_mem_Onm` per index (the level-`n` circle-generator span).
* **`CircDiffAnmRightTowerEq`** — the precise DJ Lemma 2.8 tower-decomposition predicate (the pole-`2`
  difference as a U-tower family in `c` plus the homogeneous multi-grade W-family in the products
  `c₍s₎a`).
* **`circDiffAnmRight_mem_of_towerEq`** — **the membership half FULLY proven**:
  `CircDiffAnmRightTowerEq` ⟹ the pole-difference ∈ `Onm W n 0` (via `PresTowerFam_mem_Onm` +
  `MGTowerFam_mem_Onm`).
* **`CircDiffAnmRightOnm_of_towerEq`** — universal `CircDiffAnmRightTowerEq` ⟹ `CircDiffAnmRightOnm`.
* **`CrossCFirstOnm_of_towerEq`** — universal `CircDiffAnmRightTowerEq` ⟹ `CrossCFirstOnm` (chained
  with `CrossCFirstOnm_of_circDiff`).
* **`MUGradedAction_of_circDiffTowerEq`** — the FULL `MUGradedAction W` assembly, conditional
  ONLY on the universal DJ Lemma 2.8 tower decomposition (with the proven `CrossCommOnm_holds`).

**Remaining content (engine-verified TRUE, free boson `n = 1, 2`; NOT faked):** the universally-
quantified `CircDiffAnmRightTowerEq W n K M P a c d` — the explicit DJ Lemma 2.8 tower decomposition

  `anmCirc W 0 0 c (a *^n_0 d) − anmCirc W n 0 c (a *^n_0 d)`
    = (U-tower family in `c` based at `a₍g₎d`) + (multi-grade W-family in `c₍s₎a` based at `d`).

Engine values (`certificates/mathematica/`):

* `certificates/mathematica/circ_diff_dj.wl` — the pole-difference is in the span of (`c`-towers based at `a₍g₎d`) +
  ((`c₍s₎a`)-towers based at `d`) for `n = 1, 2` and mixed homogeneous `a, c, d` (**True**); the
  `(c₍s₎a)`-towers ALONE do NOT suffice (**False**), so the U-family in `c` is load-bearing;
* `certificates/mathematica/mucross_O0sub5.wl` — `(circ00 − circ_n) c (a *^n_0 d) ∈ Onm` **True** (the target, `n = 1, 2`);
* `certificates/mathematica/circ_diff_L.wl` — NOT in `OnmL` (grading generators) alone (**False**);
* `certificates/mathematica/diff_tower.wl` / `certificates/mathematica/target_tower.wl` — NOT the naive U/V `PresAnm`-tower mirror (**False**) — so it
  genuinely requires the FULL level-`n` circle-generator span (the products `c₍s₎a`), the deep DJ
  Lemma 2.8 reorganization, NOT the diagonal `AnmCircTowerEq` mirror.

The membership engine (`MGTowerFam_mem_Onm`, the full circle span) is fully built; the only remaining
step is the explicit mode-identity producing the U-tower weights/bases and the multi-grade W-family
data (the DJ Lemma 2.8 coefficients) — an existential over `PresTowerFam` + `MGTowerFam` whose
membership is already discharged.
-/

end VOA

/-
`#print axioms` check (each of the following prints
`[propext, Classical.choice, Quot.sound]`, NO `pbw`, NO `sorryAx`):

  #print axioms VOA.MGTowerFam_mem_Onm
  #print axioms VOA.circDiffAnmRight_mem_of_towerEq
  #print axioms VOA.CircDiffAnmRightOnm_of_towerEq
  #print axioms VOA.CrossCFirstOnm_of_towerEq
  #print axioms VOA.MUGradedAction_of_circDiffTowerEq
-/
