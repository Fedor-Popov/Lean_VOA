/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchMUcrossGen

/-!
# Game One — the cross commutator family `CrossCommOnm`: reduction to per-`s` `PresAnm`-towers.

This file works on the commutator-family sub-predicate `CrossCommOnm W n`
(`ZhuVermaAnArchMUcrossGen`), one of the two precise generator-family sub-identities the last cross
membership `CrossCircOnmGen W n` splits into:

  `crossCircComm W n K M a c d ∈ Onm W n 0`   (homogeneous `a ∈ 𝒱_K`, `c ∈ 𝒱_M`, `d ∈ 𝒱_P`).

By `crossCircComm_jsum_expand` (`ZhuVermaAnArchMUcrossSum`) the commutator family is a finite
ℂ-combination of modes of `a₍s₎c ∈ 𝒱_{K+M−s−1}` acting on `d`, summed over the Borcherds-locality
index `s < N`.  We reorder the triple `(j, i, s)`-sum to pull the `s`-sum OUTERMOST, isolating, for
each fixed `s`, the **per-`s` slice**

  `crossCommSlice W n K M a c d s
     = ∑_{j≤M} C(M,j) • ∑_{i≤K} C(K,i) • C(i−n−1, s) • (a₍s₎c)₍(i−n−1)+(j−2)−s₎ d`,

whose base `a₍s₎c` is homogeneous of grade `Ws = K+M−s−1` (`crossCircComm_base_mem_grading`).  This is
the shift-`0`, mixed-level twin of the `s`-outermost pull in the PROVEN
`leftProd_circ_commutator_family_mem_On` (`ZhuVermaAnDescent4`); the membership engine is the keystone
`Pres_mem_Onm` packaged as `PresTowerFam_mem_Onm` (`ZhuVermaAnArchMUcrossHM`).

## What is proved here (axiom-clean)

* **`crossCommSlice`** — the per-`s` slice of the `j`-summed commutator family.
* **`crossCircComm_eq_sliceSum`** — `crossCircComm W n K M a c d = ∑_{s<N} crossCommSlice …` (the
  `s`-outermost reordering of `crossCircComm_jsum_expand`, by `Finset.sum_comm`/`Finset.smul_sum`).
* **`CrossCommSliceTowerEq`** — the per-`s` tower predicate: the slice collapses onto a general
  `PresAnm`-tower family in the homogeneous base `a₍s₎c` (`PresTowerFam`, `ZhuVermaAnArchMUcrossHM`).
* **`crossCommSlice_mem_Onm_of_towerEq`** — the per-`s` slice membership, FULLY proven from
  `CrossCommSliceTowerEq` via the keystone-backed `PresTowerFam_mem_Onm`.
* **`crossCommOnm_of_sliceTowerEq`** — `CrossCommOnm W n` from the per-`s` tower predicate for all `s`
  (the `∑_s`-of-slices membership, by `Submodule.sum_mem`).

This reduces `CrossCommOnm` (∀ `n`) to ONE precise per-`s` scalar/tower identity: the per-`s` slice
expressed as a `PresAnm`-tower combination in `a₍s₎c`.  The membership half is closed unconditionally.

## The PRECISE remaining identity (NOT `sorry`'d / NOT axiomatized) and its engine value

`CrossCommSliceTowerEq W n K M s a c d`: for each fixed `s`, the per-`s` slice is a finite
ℂ-combination of `PresAnm W Ws n δ (a₍s₎c) d` over depths `δ`.  This is engine-verified TRUE on the
rank-1 free boson: a direct `LeastSquares` mode-coefficient solve
(`certificates/mathematica/vander_check.wl` / the `vander*.wl` family) shows the per-`s` slice
mode-coefficient

  `Cₛ(m) = ∑_{i,j : (i+j)−n−3−s = m} C(K,i) C(M,j) C(i−n−1, s)`

lies exactly in the span of the `PresAnm`-coefficient functions `m ↦ C(Ws+δ, m+n+2+δ)` (depths
`δ = 1, …, s+1`); the slice solves to a finite `PresAnm`-combination for every tested
`(K, M, n, s)` with ZERO residual.  Discharging `CrossCommSliceTowerEq` (the explicit
`gen_jsum`-style coefficient identity, the shift-`0` mixed-level twin of `coeffSn_eq_coeffPn`,
`ZhuVermaAnDescent4`) closes `CrossCommOnm` outright via `crossCommOnm_of_sliceTowerEq`, and — with the
sibling `CrossCFirstOnm` — the full `MUGradedAction W` (`MUGradedAction_of_families`,
`ZhuVermaAnArchMUcrossGen`).  Engine sanity for the non-degenerate commutator
(`a = c = a₂|0⟩, d = J, n = 1`): `certificates/mathematica/mucross_comm_nondeg.wl` — the commutator family
alone lands in circle + `OnmL` (True).

## References
Dong–Jiang, Math. Z. 259 (2008) 799–826 (`math/0601626`), §2 (Lemma 2.8); Frenkel–Zhu Lemma 2.1.2;
Dong–Li–Mason; Gannon §5.3.2, Thm 5.3.4.
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The per-`s` slice of the `j`-summed commutator family. -/

/-- **The per-`s` slice** of the `j`-summed cross commutator family (Borcherds-locality index `s`):

  `crossCommSlice W n K M a c d s
     = ∑_{j≤M} C(M,j) • ∑_{i≤K} C(K,i) • C(i−n−1, s) • (a₍s₎c)₍(i−n−1)+(j−2)−s₎ d`.

The base `a₍s₎c` is homogeneous of grade `Ws = K+M−s−1` (`crossCircComm_base_mem_grading`); the slice
is the `s`-th summand of the `s`-outermost reordering of `crossCircComm_jsum_expand`
(`ZhuVermaAnArchMUcrossSum`).  Shift-`0` twin of the per-`s` `Sn` summand of
`leftProd_circ_commutator_family_mem_On` (`ZhuVermaAnDescent4`). -/
noncomputable def crossCommSlice (W : VertexOperatorAlgebra 𝒱) (n K M : ℕ) (a c d : 𝒱) (s : ℕ) :
    𝒱 :=
  ∑ j ∈ Finset.range (M + 1),
    cbz (M : ℤ) (j : ℤ) •
      ∑ i ∈ Finset.range (K + 1),
        cbz (K : ℤ) (i : ℤ) •
          cbz ((i : ℤ) - ((n : ℤ) + 1)) (s : ℤ)
            • W.smul (W.smul a (s : ℤ) c)
                (((i : ℤ) - ((n : ℤ) + 1)) + ((j : ℤ) - 2) - (s : ℤ)) d

/-! ## The `s`-outermost reordering of the `j`-summed commutator family. -/

/-- **`crossCircComm` as the sum over `s` of its per-`s` slices.**  Reorder the triple
`(j, i, s)`-sum of `crossCircComm_jsum_expand` (`ZhuVermaAnArchMUcrossSum`) to pull the inner `s`-sum
OUTERMOST: distribute the `cbz M j` and `cbz K i` weights into the `s`-sum and swap `(i, s)` then
`(j, s)` (`Finset.smul_sum` + `Finset.sum_comm`).  Each fixed-`s` slice is `crossCommSlice`.  Shift-`0`
twin of the `∑_s` pull in `leftProd_circ_commutator_family_mem_On` (`ZhuVermaAnDescent4`). -/
theorem crossCircComm_eq_sliceSum (W : VertexOperatorAlgebra 𝒱) (n K M : ℕ) (a c d : 𝒱) :
    ∃ N : ℕ,
      crossCircComm W n K M a c d
        = ∑ s ∈ Finset.range N, crossCommSlice W n K M a c d s := by
  obtain ⟨N, hN⟩ := crossCircComm_jsum_expand W n K M a c d
  refine ⟨N, ?_⟩
  rw [hN]
  -- Step 1: per `j`, pull the inner `s`-sum out past the `i`-sum (swap `(i, s)`), distributing
  -- the `cbz K i` weight into the `s`-sum.
  rw [show (∑ j ∈ Finset.range (M + 1),
            cbz (M : ℤ) (j : ℤ) •
              ∑ i ∈ Finset.range (K + 1),
                cbz (K : ℤ) (i : ℤ) •
                  ∑ s ∈ Finset.range N,
                    cbz ((i : ℤ) - ((n : ℤ) + 1)) (s : ℤ)
                      • W.smul (W.smul a (s : ℤ) c)
                          (((i : ℤ) - ((n : ℤ) + 1)) + ((j : ℤ) - 2) - (s : ℤ)) d)
        = ∑ j ∈ Finset.range (M + 1),
            cbz (M : ℤ) (j : ℤ) •
              ∑ s ∈ Finset.range N,
                ∑ i ∈ Finset.range (K + 1),
                  cbz (K : ℤ) (i : ℤ) •
                    cbz ((i : ℤ) - ((n : ℤ) + 1)) (s : ℤ)
                      • W.smul (W.smul a (s : ℤ) c)
                          (((i : ℤ) - ((n : ℤ) + 1)) + ((j : ℤ) - 2) - (s : ℤ)) d from
      Finset.sum_congr rfl fun j _ => by
        congr 1
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => by rw [Finset.smul_sum]]
  -- Step 2: per `j`, distribute the `cbz M j` weight into the `s`-sum.
  rw [show (∑ j ∈ Finset.range (M + 1),
            cbz (M : ℤ) (j : ℤ) •
              ∑ s ∈ Finset.range N,
                ∑ i ∈ Finset.range (K + 1),
                  cbz (K : ℤ) (i : ℤ) •
                    cbz ((i : ℤ) - ((n : ℤ) + 1)) (s : ℤ)
                      • W.smul (W.smul a (s : ℤ) c)
                          (((i : ℤ) - ((n : ℤ) + 1)) + ((j : ℤ) - 2) - (s : ℤ)) d)
        = ∑ j ∈ Finset.range (M + 1),
            ∑ s ∈ Finset.range N,
              cbz (M : ℤ) (j : ℤ) •
                ∑ i ∈ Finset.range (K + 1),
                  cbz (K : ℤ) (i : ℤ) •
                    cbz ((i : ℤ) - ((n : ℤ) + 1)) (s : ℤ)
                      • W.smul (W.smul a (s : ℤ) c)
                          (((i : ℤ) - ((n : ℤ) + 1)) + ((j : ℤ) - 2) - (s : ℤ)) d from
      Finset.sum_congr rfl fun j _ => by rw [Finset.smul_sum]]
  -- Step 3: swap `(j, s)` to pull `∑_s` outermost; recognize each fixed-`s` slice as
  -- `crossCommSlice`.
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [crossCommSlice]

/-! ## The per-`s` tower predicate and the (FULLY PROVEN) per-`s` slice membership. -/

/-- **The per-`s` slice tower predicate** (`Prop`).  For fixed `s` and grade `Ws` with
`(Ws : ℤ) = K+M−s−1`, the per-`s` slice collapses onto a general `PresAnm`-tower family
(`PresTowerFam`, `ZhuVermaAnArchMUcrossHM`) in the homogeneous base `a₍s₎c ∈ 𝒱_{Ws}`:

  `crossCommSlice W n K M a c d s = PresTowerFam W Ws n (a₍s₎c) R Δ baseU w`

for some finite data `R Δ baseU w`.  Engine-verified TRUE on the free boson (the `vander*.wl`
`LeastSquares` solve: the per-`s` slice is a finite `PresAnm`-combination in `a₍s₎c` for every
tested `(K, M, n, s)`).  Shift-`0`, mixed-level twin of the `coeffSn_eq_coeffPn` collapse
(`ZhuVermaAnDescent4`). -/
def CrossCommSliceTowerEq (W : VertexOperatorAlgebra 𝒱) (n K M : ℕ) (a c d : 𝒱) (s Ws : ℕ) : Prop :=
  ∃ (R Δ : ℕ) (baseU : Fin R → 𝒱) (w : Fin R → ℕ → ℂ),
    crossCommSlice W n K M a c d s = PresTowerFam W Ws n (W.smul a (s : ℤ) c) R Δ baseU w

/-- **The per-`s` slice lies in `Onm W n 0`** (homogeneous `a ∈ 𝒱_K`, `c ∈ 𝒱_M`), from the per-`s`
tower predicate.  The base `a₍s₎c` is homogeneous of grade `Ws = K+M−s−1`
(`crossCircComm_base_mem_grading`); the slice's `PresTowerFam` form (`CrossCommSliceTowerEq`) lands in
`Onm W n 0` by the keystone-backed `PresTowerFam_mem_Onm` (`ZhuVermaAnArchMUcrossHM`).  This handles
both the negative-grade (`a₍s₎c = 0`, vacuous) and the genuine homogeneous case uniformly. -/
theorem crossCommSlice_mem_Onm_of_towerEq (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {K M : ℕ} {a c : 𝒱}
    (ha : a ∈ W.grading (K : ℤ)) (hc : c ∈ W.grading (M : ℤ)) (d : 𝒱) (s : ℕ)
    (htow : ∀ Ws : ℕ, (Ws : ℤ) = (K : ℤ) + (M : ℤ) - (s : ℤ) - 1 →
      CrossCommSliceTowerEq W n K M a c d s Ws) :
    crossCommSlice W n K M a c d s ∈ Onm W n 0 := by
  set w := W.smul a (s : ℤ) c with hw
  have hwmem : w ∈ W.grading ((K : ℤ) + (M : ℤ) - (s : ℤ) - 1) :=
    crossCircComm_base_mem_grading W ha hc (s : ℤ)
  rcases lt_or_ge ((K : ℤ) + (M : ℤ) - (s : ℤ) - 1) 0 with hneg | hpos
  · -- `w ∈ 𝒱_{<0} = ⊥`, so `w = 0` and the slice is `0`.
    rw [W.positivity _ hneg, Submodule.mem_bot] at hwmem
    rw [crossCommSlice]
    rw [Finset.sum_eq_zero fun j _ => ?_]
    · exact (Onm W n 0).zero_mem
    · rw [Finset.sum_eq_zero fun i _ => ?_, smul_zero]
      rw [← hw, hwmem, PreVertexAlgebra.smul_zero_left, smul_zero, smul_zero]
  · obtain ⟨Ws, hWs⟩ : ∃ Ws : ℕ, (Ws : ℤ) = (K : ℤ) + (M : ℤ) - (s : ℤ) - 1 :=
      ⟨((K : ℤ) + (M : ℤ) - (s : ℤ) - 1).toNat, by omega⟩
    have hwmem' : w ∈ W.grading (Ws : ℤ) := by rwa [hWs]
    obtain ⟨R, Δ, baseU, weights, heq⟩ := htow Ws hWs
    rw [heq]
    exact PresTowerFam_mem_Onm W n hwmem' R Δ baseU weights

/-! ## The commutator family membership from the per-`s` tower predicate. -/

/-- **`CrossCommOnm W n` from the per-`s` slice tower predicate.**  If, for all grades `K M P`,
homogeneous `a ∈ 𝒱_K`, `c ∈ 𝒱_M`, `d ∈ 𝒱_P`, and all Borcherds-locality indices `s` (at the
matching grade `Ws`), the per-`s` slice collapses onto a `PresAnm`-tower family
(`CrossCommSliceTowerEq`), then the whole commutator family lies in `Onm W n 0`:
`crossCircComm = ∑_s crossCommSlice`
(`crossCircComm_eq_sliceSum`) is a finite sum of slices, each in `Onm W n 0`
(`crossCommSlice_mem_Onm_of_towerEq`), so the sum is too (`Submodule.sum_mem`).  This discharges
`CrossCommOnm W n` (`ZhuVermaAnArchMUcrossGen`). -/
theorem crossCommOnm_of_sliceTowerEq (W : VertexOperatorAlgebra 𝒱) (n : ℕ)
    (Htow : ∀ (K M P : ℕ), ∀ a ∈ W.grading (K : ℤ), ∀ c ∈ W.grading (M : ℤ),
      ∀ d ∈ W.grading (P : ℤ), ∀ (s Ws : ℕ),
        (Ws : ℤ) = (K : ℤ) + (M : ℤ) - (s : ℤ) - 1 →
          CrossCommSliceTowerEq W n K M a c d s Ws) :
    CrossCommOnm W n := by
  intro K M P a ha c hc d hd
  obtain ⟨N, hN⟩ := crossCircComm_eq_sliceSum W n K M a c d
  rw [hN]
  refine Submodule.sum_mem _ (fun s _ => ?_)
  exact crossCommSlice_mem_Onm_of_towerEq W n ha hc d s
    (fun Ws hWs => Htow K M P a ha c hc d hd s Ws hWs)

/-! ## Status — the cross commutator family `CrossCommOnm` reduced to the per-`s` tower identity.

Proved here (`#print axioms` = `[propext, Classical.choice, Quot.sound]`; no `sorry`/
`axiom`/`pbw`):

* **`crossCommSlice`** — the per-`s` slice of the `j`-summed commutator family.
* **`crossCircComm_eq_sliceSum`** — `crossCircComm = ∑_{s<N} crossCommSlice` (`s`-outermost
  reordering of `crossCircComm_jsum_expand`).
* **`CrossCommSliceTowerEq`** — the per-`s` tower predicate (slice = `PresTowerFam` in `a₍s₎c`).
* **`crossCommSlice_mem_Onm_of_towerEq`** — the per-`s` slice membership, FULLY proven via the
  keystone-backed `PresTowerFam_mem_Onm` (uniform over the negative-grade vacuous case).
* **`crossCommOnm_of_sliceTowerEq`** — `CrossCommOnm W n` from the per-`s` tower predicate (the
  `∑_s`-of-slices membership).

**The PRECISE remaining identity (engine-verified TRUE, free boson; NOT faked):**
`CrossCommSliceTowerEq W n K M s a c d` — for each fixed `s` and grade `Ws = K+M−s−1`, the per-`s`
slice `crossCommSlice W n K M a c d s` equals a finite `PresAnm`-tower combination
`PresTowerFam W Ws n (a₍s₎c) R Δ baseU w`.  Engine value (`certificates/mathematica/vander_check.wl` and
the `vander*.wl` family): the per-`s` slice mode-coefficient
`Cₛ(m) = ∑_{i,j : (i+j)−n−3−s = m} C(K,i) C(M,j) C(i−n−1, s)` solves EXACTLY (zero `LeastSquares`
residual) to a finite combination of the `PresAnm`-coefficient functions `m ↦ C(Ws+δ, m+n+2+δ)`
(depths `δ = 1, …, s+1`) for every tested `(K, M, n, s)`; the explicit coefficients are the
shift-`0`, mixed-level twin of `coeffSn_eq_coeffPn` (`ZhuVermaAnDescent4`), the genuine
`gen_jsum`-style
combinatorial content.  Non-degeneracy sanity (`certificates/mathematica/mucross_comm_nondeg.wl`,
`a = c = a₂|0⟩, d = J, n = 1`): the commutator family alone lands in circle + `OnmL` (True).

Discharging `CrossCommSliceTowerEq` (∀ `s`) closes `CrossCommOnm W n` outright via
`crossCommOnm_of_sliceTowerEq`, and — with the sibling `CrossCFirstOnm W n` — the full
`MUGradedAction W` (`MUGradedAction_of_families`, `ZhuVermaAnArchMUcrossGen`).
-/

end VOA

/-
`#print axioms` check (each of the following prints
`[propext, Classical.choice, Quot.sound]`, NO `pbw`, NO `sorryAx`):

  #print axioms VOA.crossCircComm_eq_sliceSum
  #print axioms VOA.crossCommSlice_mem_Onm_of_towerEq
  #print axioms VOA.crossCommOnm_of_sliceTowerEq
-/
