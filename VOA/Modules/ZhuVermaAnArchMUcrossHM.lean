/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchMUcrossClose
import VOA.Modules.ZhuVermaAnArchMUcross
import VOA.Modules.ZhuVermaAnArchMUcirc
import VOA.Modules.ZhuVermaAnArchMU
import VOA.Modules.ZhuVermaAnDescent4

/-!
# Game One — the `m = 0` cross-level circle core `CrossCircCoreHM` and the `MUGradedAction` assembly.

This file works on the last open `MUGradedAction` family of the Dong–Jiang induced module `M(U)`
`V`-action: the **fully-homogeneous cross-level circle** core `CrossCircCoreHM W n`
(`ZhuVermaAnArchMUcrossClose`),

  `resHom W 0 (n+1) a (resHom W 0 2 c d) ∈ Onm W n 0`   (homogeneous `a ∈ 𝒱_K`, `c ∈ 𝒱_M`, `d ∈ 𝒱_P`),

i.e. the outer level-`n` residue (pole `n+1`, the right action `a *^n_0 (·)`) applied to the inner
**level-`0`** Zhu circle generator `anmCirc W 0 0 c d = resHom W 0 2 c d` (pole `2`).  This is the
`m = 0`, mixed-level analogue of the proven left-slot `leftProd_circ_mem_On`
(`ZhuVermaAnDescent4`), and — being cross-level — the genuine combinatorial twin of the still-open
shift-`0` tower predicate `AnmCircTowerEq` (`ZhuVermaAnArchMUcirc`).

## The explicit mode-split of the cross-level circle core (proved here, axiom-clean)

By `crossCirc_resHom_homog` (`ZhuVermaAnArchMUcrossClose`) the core target is the explicit double
mode sum

  `∑_{i≤K} C(K,i) • a₍i−n−1₎ (∑_{j≤M} C(M,j) • c₍j−2₎ d)`.

The mode-split `a₍α₎(c₍β₎d) = c₍β₎(a₍α₎d) + ⁅a₍α₎,c₍β₎⁆d` (`mode_split_gen`, `ZhuVermaAnDescent4`,
`α = i−n−1`, `β = j−2`) splits this into

* the **`c`-first family** `crossCircCFirst` — `∑_i C(K,i) ∑_j C(M,j) • c₍j−2₎(a₍i−n−1₎d)`, whose
  inner `j`-sum is the *level-`0`* circle `resHom W 0 2 c (a₍i−n−1₎d)` (pole `2`, **not** the `Onm`
  pole `n+2`); and
* the **commutator family** `crossCircComm` — `∑_i C(K,i) ∑_j C(M,j) • ⁅a₍i−n−1₎,c₍j−2₎⁆d`.

We record the split identity `crossCirc_modeSplit` (target = `crossCircCFirst` + `crossCircComm`),
and the precise tower-collapse predicate `CrossCircTowerEq` (the shift-`0`, mixed-level twin of
`AnmCircTowerEq`): the COMBINATION of the two families collapses onto a `PresAnm`-tower U-family
(in `c`) + V-family (in `d`), all in `Onm W n 0` via the keystone `Pres_mem_Onm`
(`ZhuVermaAnArchMUcirc`).  This is the cross subtlety: neither family lands on its own (the `c`-first
inner circle is level `0`, pole `2`), only the combined residue is `(z)`-grade-`(n+2)`-local.

## What is proved here (axiom-clean)

* `crossCircCFirst`/`crossCircComm` — the `c`-first and commutator double-mode-sum families.
* **`crossCirc_modeSplit`** — the exact decomposition of the core target into the two families.
* **`CrossCircTowerEq`** — the precise tower-collapse predicate (shift-`0`, mixed-level twin of
  `AnmCircTowerEq`); the genuine remaining cross combinatorial identity, engine-verified TRUE on the
  rank-1 free boson (`certificates/mathematica/mucross_circ.wl`).
* **`crossCircCoreHM_of_towerEq`** — `CrossCircTowerEq` (universally quantified) ⟹ `CrossCircCoreHM`.
* **`MUGradedAction_of_crossTower`** — the FULL `MUGradedAction W` assembly, conditional on the two
  open homogeneous tower predicates (`AnmCircTowerEq` for the diagonal circle `hcirc`, and
  `CrossCircTowerEq` for the cross circle `hcrossCirc`); the `hcrossL` family is already closed
  unconditionally (`anmRight_zero_crossL_mem_Onm`, `ZhuVermaAnArchMUcross`).

## References
Dong–Jiang, Math. Z. 259 (2008) 799–826 (`math/0601626`), §2 (Lemma 2.8); Frenkel–Zhu Lemma 2.1.2;
Dong–Li–Mason; Gannon §5.3.2, Thm 5.3.4.
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The two families of the cross-level circle mode-split. -/

/-- The **`c`-first family** of the cross-level circle core (homogeneous `a ∈ 𝒱_K`, `c ∈ 𝒱_M`):
`∑_{i≤K} C(K,i) • ∑_{j≤M} C(M,j) • c₍j−2₎ (a₍i−n−1₎ d)`.  The inner `j`-sum is the *level-`0`* Zhu
circle `resHom W 0 2 c (a₍i−n−1₎ d)` (pole `2`), based at `a₍i−n−1₎ d`. -/
noncomputable def crossCircCFirst (W : VertexOperatorAlgebra 𝒱) (n K M : ℕ) (a c d : 𝒱) : 𝒱 :=
  ∑ i ∈ Finset.range (K + 1),
    cbz (K : ℤ) (i : ℤ) •
      ∑ j ∈ Finset.range (M + 1),
        cbz (M : ℤ) (j : ℤ)
          • W.smul c ((j : ℤ) - 2) (W.smul a ((i : ℤ) - ((n : ℤ) + 1)) d)

/-- The **commutator family** of the cross-level circle core (homogeneous `a ∈ 𝒱_K`, `c ∈ 𝒱_M`):
`∑_{i≤K} C(K,i) • ∑_{j≤M} C(M,j) • ⁅a₍i−n−1₎, c₍j−2₎⁆ d`. -/
noncomputable def crossCircComm (W : VertexOperatorAlgebra 𝒱) (n K M : ℕ) (a c d : 𝒱) : 𝒱 :=
  ∑ i ∈ Finset.range (K + 1),
    cbz (K : ℤ) (i : ℤ) •
      ∑ j ∈ Finset.range (M + 1),
        cbz (M : ℤ) (j : ℤ)
          • ⁅mode (W.Y a) ((i : ℤ) - ((n : ℤ) + 1)),
              mode (W.Y c) ((j : ℤ) - 2)⁆ d

/-! ## The mode-split decomposition of the cross-level circle core. -/

/-- **The cross-level circle core mode-split.**  For homogeneous `a ∈ 𝒱_K`, `c ∈ 𝒱_M`, `d ∈ 𝒱_P`,
the explicit double-mode-sum form of `resHom W 0 (n+1) a (resHom W 0 2 c d)`
(`crossCirc_resHom_homog`) decomposes — via `mode_split_gen` (`α = i−n−1`, `β = j−2`) — into the
`c`-first family plus the commutator family:
`resHom W 0 (n+1) a (resHom W 0 2 c d) = crossCircCFirst + crossCircComm`. -/
theorem crossCirc_modeSplit (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {K M : ℕ}
    {a : 𝒱} (ha : a ∈ W.grading (K : ℤ)) {c : 𝒱} (hc : c ∈ W.grading (M : ℤ)) (d : 𝒱) :
    resHom W 0 ((n : ℤ) + 1) a (resHom W 0 2 c d)
      = crossCircCFirst W n K M a c d + crossCircComm W n K M a c d := by
  rw [crossCirc_resHom_homog W n ha hc d, crossCircCFirst, crossCircComm,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  -- distribute the outer mode `a₍i−n−1₎` across the inner `j`-sum.
  rw [show W.smul a ((i : ℤ) - ((n : ℤ) + 1))
            (∑ j ∈ Finset.range (M + 1),
              cbz (M : ℤ) (j : ℤ) • W.smul c ((j : ℤ) - 2) d)
        = ∑ j ∈ Finset.range (M + 1),
            cbz (M : ℤ) (j : ℤ)
              • W.smul a ((i : ℤ) - ((n : ℤ) + 1)) (W.smul c ((j : ℤ) - 2) d) from by
      rw [PreVertexAlgebra.smul_def, map_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [LinearMap.map_smul]; rfl]
  rw [← smul_add]
  congr 1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← smul_add]
  congr 1
  -- the per-(i,j) split: a₍α₎(c₍β₎d) = c₍β₎(a₍α₎d) + ⁅a₍α₎,c₍β₎⁆d.
  rw [mode_split_gen W a c d ((i : ℤ) - ((n : ℤ) + 1)) ((j : ℤ) - 2)]

/-! ## The precise tower-collapse predicate (shift-`0`, mixed-level twin of `AnmCircTowerEq`).

`crossCirc_modeSplit` reduces `CrossCircCoreHM` to the membership of `crossCircCFirst +
crossCircComm`.  The genuine remaining content is that this COMBINATION collapses onto a
`PresAnm`-tower U-family in `c` (based at `a₍·₎d`-style modes) plus a V-family in `d` (based at
`c₍·₎(a₍·₎d)`-style modes), all carried into `Onm W n 0` by the keystone `Pres_mem_Onm`
(`ZhuVermaAnArchMUcirc`).  This is the cross subtlety (the `c`-first inner circle is level `0`, pole
`2`, so neither family lands alone — only the combined residue is grade-`(n+2)`-local).  We state it
as the precise predicate `CrossCircTowerEq`, the shift-`0`, mixed-level twin of `AnmCircTowerEq`;
engine-verified TRUE on the rank-1 free boson (`certificates/mathematica/mucross_circ.wl`). -/

/-- A **general `PresAnm`-tower family** in the left factor `u ∈ 𝒱_M`: a finite ℂ-combination of
`PresAnm W M n δ u (baseU r)` over depths `δ < Δ` and an arbitrary finite index set `Fin R`, with
arbitrary base vectors `baseU : Fin R → 𝒱` and weights `w : Fin R → ℕ → ℂ`.  Each summand lands in
`Onm W n 0` by the keystone `Pres_mem_Onm` (for homogeneous `u`), regardless of the base/weights. -/
noncomputable def PresTowerFam (W : VertexOperatorAlgebra 𝒱) (M n : ℕ) (u : 𝒱)
    (R Δ : ℕ) (baseU : Fin R → 𝒱) (w : Fin R → ℕ → ℂ) : 𝒱 :=
  ∑ r : Fin R, ∑ δ ∈ Finset.range Δ, w r δ • PresAnm W M n δ u (baseU r)

/-- **A general `PresAnm`-tower family lies in `Onm W n 0`** (for homogeneous `u ∈ 𝒱_M`), by the
keystone `Pres_mem_Onm` (`ZhuVermaAnArchMUcirc`), for ANY base vectors and weights. -/
theorem PresTowerFam_mem_Onm (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {M : ℕ} {u : 𝒱}
    (hu : u ∈ W.grading (M : ℤ)) (R Δ : ℕ) (baseU : Fin R → 𝒱) (w : Fin R → ℕ → ℂ) :
    PresTowerFam W M n u R Δ baseU w ∈ Onm W n 0 := by
  refine Submodule.sum_mem _ (fun r _ => Submodule.sum_mem _ (fun δ _ => ?_))
  exact Submodule.smul_mem _ _ (Pres_mem_Onm W n hu (baseU r) δ)

/-- **The `m = 0` cross-level circle tower-decomposition predicate** (precise remaining identity).
For homogeneous `a ∈ 𝒱_K`, `c ∈ 𝒱_M`, `d ∈ 𝒱_P`, the combined `c`-first + commutator families
collapse onto a general `PresAnm`-tower family in `c` (over `M`, with arbitrary base vectors —
modes of `a₍·₎d`) plus a general `PresAnm`-tower family in `d` (over `P`, with arbitrary base
vectors — iterated modes `c₍·₎(a₍·₎d)`).  Shift-`0`, mixed-level twin of `AnmCircTowerEq`.
Engine-verified TRUE (`certificates/mathematica/mucross_circ.wl`). -/
def CrossCircTowerEq (W : VertexOperatorAlgebra 𝒱) (n K M P : ℕ) (a c d : 𝒱) : Prop :=
  ∃ (RU RV ΔU ΔV : ℕ) (baseU : Fin RU → 𝒱) (baseV : Fin RV → 𝒱)
    (wU : Fin RU → ℕ → ℂ) (wV : Fin RV → ℕ → ℂ),
    crossCircCFirst W n K M a c d + crossCircComm W n K M a c d
      = PresTowerFam W M n c RU ΔU baseU wU + PresTowerFam W P n d RV ΔV baseV wV

/-- **`CrossCircTowerEq` ⟹ the homogeneous core membership** (homogeneous data).  For homogeneous
`a ∈ 𝒱_K`, `c ∈ 𝒱_M`, `d ∈ 𝒱_P`, if the combined cross families collapse onto the U/V `PresAnm`-tower
families (`CrossCircTowerEq`), then `resHom W 0 (n+1) a (resHom W 0 2 c d) ∈ Onm W n 0`.  The
membership is closed by `crossCirc_modeSplit` + the keystone-backed `PresTowerFam_mem_Onm`
(itself `Pres_mem_Onm`, `ZhuVermaAnArchMUcirc`). -/
theorem crossCirc_homog_mem_of_towerEq (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {K M P : ℕ}
    {a c d : 𝒱} (ha : a ∈ W.grading (K : ℤ)) (hc : c ∈ W.grading (M : ℤ))
    (hd : d ∈ W.grading (P : ℤ)) (htow : CrossCircTowerEq W n K M P a c d) :
    resHom W 0 ((n : ℤ) + 1) a (resHom W 0 2 c d) ∈ Onm W n 0 := by
  obtain ⟨RU, RV, ΔU, ΔV, baseU, baseV, wU, wV, heq⟩ := htow
  rw [crossCirc_modeSplit W n ha hc d, heq]
  exact Submodule.add_mem _ (PresTowerFam_mem_Onm W n hc RU ΔU baseU wU)
    (PresTowerFam_mem_Onm W n hd RV ΔV baseV wV)

/-! ## `CrossCircTowerEq` (universal) ⟹ `CrossCircCoreHM`. -/

/-- **`CrossCircCoreHM W n` from the (universally-quantified) cross tower predicate.**  Supplying
`CrossCircTowerEq` for ALL grades `K, M, P` and homogeneous `a, c, d` discharges the fully-homogeneous
cross-level circle core `CrossCircCoreHM W n` (`ZhuVermaAnArchMUcrossClose`).  This is the precise
reduction of the last `MUGradedAction` family to the one cross combinatorial identity. -/
theorem crossCircCoreHM_of_towerEq (W : VertexOperatorAlgebra 𝒱) (n : ℕ)
    (Htow : ∀ (K M P : ℕ), ∀ a ∈ W.grading (K : ℤ), ∀ c ∈ W.grading (M : ℤ),
      ∀ d ∈ W.grading (P : ℤ), CrossCircTowerEq W n K M P a c d) :
    CrossCircCoreHM W n := by
  intro K M P a ha c hc d hd
  exact crossCirc_homog_mem_of_towerEq W n ha hc hd (Htow K M P a ha c hc d hd)

/-! ## (hcrossCirc) from the cross tower predicate. -/

/-- **(hcrossCirc) from the (universally-quantified) cross tower predicate.**  Combining
`crossCircCoreHM_of_towerEq` with `CrossCircCore_of_HM` (`ZhuVermaAnArchMUcrossClose`) and
`anmRight_zero_crossCirc_mem_Onm_of_core` (`ZhuVermaAnArchMUcross`) discharges the cross-level circle
closure `anmRight W n 0 a (anmCirc W 0 0 c d) ∈ Onm W n 0` for ALL `a c d : 𝒱`. -/
theorem anmRight_zero_crossCirc_mem_Onm_of_towerEq (W : VertexOperatorAlgebra 𝒱) (n : ℕ)
    (Htow : ∀ (K M P : ℕ), ∀ a ∈ W.grading (K : ℤ), ∀ c ∈ W.grading (M : ℤ),
      ∀ d ∈ W.grading (P : ℤ), CrossCircTowerEq W n K M P a c d)
    (a c d : 𝒱) :
    anmRight W n 0 a (anmCirc W 0 0 c d) ∈ Onm W n 0 :=
  anmRight_zero_crossCirc_mem_Onm_of_core W n
    (CrossCircCore_of_HM W n (crossCircCoreHM_of_towerEq W n Htow)) a c d

/-! ## The full `MUGradedAction` assembly.

`MUGradedAction_of_gens` (`ZhuVermaAnArchMU`) consumes three families:
* `hcirc` — the diagonal circle `anmRight W n 0 (anmCirc W n 0 c d) v ∈ Onm W n 0` (sibling target,
  closed from the diagonal tower predicate `AnmCircTowerEq` via `hcirc_of_towerEq`,
  `ZhuVermaAnArchMUcirc`);
* `hcrossCirc` — the cross circle, closed here from `CrossCircTowerEq`
  (`anmRight_zero_crossCirc_mem_Onm_of_towerEq`);
* `hcrossL` — the cross grading generator, closed unconditionally
  (`anmRight_zero_crossL_mem_Onm`, `ZhuVermaAnArchMUcross`).

We assemble `MUGradedAction W` conditional on the two open homogeneous tower predicates.  When the
diagonal `AnmCircTowerEq` and the cross `CrossCircTowerEq` are discharged, this yields the full DJ
`M(U)` `V`-action crux unconditionally. -/

/-- **The full `MUGradedAction W` assembly**, conditional on the two homogeneous tower predicates.
Given the diagonal circle tower predicate `AnmCircTowerEq` (for all levels `n` and all homogeneous
`c, d` and all `v`) and the cross circle tower predicate `CrossCircTowerEq` (for all levels `n` and
all homogeneous `a, c, d`), the Dong–Jiang composition crux `MUGradedAction W` holds.  The third
family (`hcrossL`) is supplied unconditionally by `anmRight_zero_crossL_mem_Onm`. -/
theorem MUGradedAction_of_crossTower (W : VertexOperatorAlgebra 𝒱)
    (HdiagTow : ∀ (n : ℕ) (M P : ℕ), ∀ c ∈ W.grading (M : ℤ), ∀ d ∈ W.grading (P : ℤ), ∀ v : 𝒱,
      AnmCircTowerEq W n M P c d v)
    (HcrossTow : ∀ (n : ℕ) (K M P : ℕ), ∀ a ∈ W.grading (K : ℤ), ∀ c ∈ W.grading (M : ℤ),
      ∀ d ∈ W.grading (P : ℤ), CrossCircTowerEq W n K M P a c d) :
    MUGradedAction W :=
  MUGradedAction_of_gens W
    (fun n => hcirc_of_towerEq W n (HdiagTow n))
    (fun n => anmRight_zero_crossCirc_mem_Onm_of_towerEq W n (HcrossTow n))
    (fun n => anmRight_zero_crossL_mem_Onm W n)

/-! ## Status — the last Game-One cross family reduced to ONE cross tower predicate; full assembly.

Proved here (`#print axioms` = `[propext, Classical.choice, Quot.sound]`; no `sorry`/
`axiom`/`pbw`):

* `crossCircCFirst`/`crossCircComm` — the `c`-first and commutator double-mode-sum families.
* **`crossCirc_modeSplit`** — the exact decomposition of the explicit cross-level circle core target
  (`crossCirc_resHom_homog`) into the two families, via `mode_split_gen`.
* **`CrossCircTowerEq`** — the precise tower-collapse predicate (shift-`0`, mixed-level twin of
  `AnmCircTowerEq`).
* **`crossCirc_homog_mem_of_towerEq`** — the homogeneous core membership from `CrossCircTowerEq`,
  closed by `crossCirc_modeSplit` + `UfamAnm_add_VfamAnm_mem_Onm`.
* **`crossCircCoreHM_of_towerEq`** — `CrossCircTowerEq` (universal) ⟹ `CrossCircCoreHM W n`.
* **`anmRight_zero_crossCirc_mem_Onm_of_towerEq`** — (hcrossCirc) from `CrossCircTowerEq`.
* **`MUGradedAction_of_crossTower`** — the FULL `MUGradedAction W` assembly, conditional on the two
  open homogeneous tower predicates (diagonal `AnmCircTowerEq` + cross `CrossCircTowerEq`); the
  `hcrossL` family is unconditional (`anmRight_zero_crossL_mem_Onm`).

**Remaining core (engine-verified TRUE, free boson; NOT faked):** `CrossCircTowerEq W n K M P a c d`
— the shift-`0`, mixed-level tower decomposition of the combined `c`-first + commutator families onto
the U/V `PresAnm`-tower families.  This is the genuine cross combinatorial collapse — the same depth
as the sibling diagonal `AnmCircTowerEq` (the `c`-first inner circle being level `0`, pole `2`, so
neither family lands alone; only the combined residue is grade-`(n+2)`-local).  Engine value
(`certificates/mathematica/mucross_circ.wl`): for `n = 1, a = c = d = J` and `n = 2`, the
residue-of-residue `anmRight W n 0 a (anmCirc W 0 0 c d)` lands in `Onm W n 0`.  Discharging
`CrossCircTowerEq` (and the sibling `AnmCircTowerEq`) closes `MUGradedAction W` outright via
`MUGradedAction_of_crossTower`.
-/

end VOA

/-
`#print axioms` check (each of the following prints
`[propext, Classical.choice, Quot.sound]`, NO `pbw`, NO `sorryAx`):

  #print axioms VOA.crossCirc_modeSplit
  #print axioms VOA.crossCirc_homog_mem_of_towerEq
  #print axioms VOA.crossCircCoreHM_of_towerEq
  #print axioms VOA.anmRight_zero_crossCirc_mem_Onm_of_towerEq
  #print axioms VOA.MUGradedAction_of_crossTower
-/
