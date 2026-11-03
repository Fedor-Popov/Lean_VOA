/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchMUGradedFinal
import VOA.Modules.ZhuVermaAnArchMUcrossCommSlice
import VOA.Modules.ZhuVermaAnArchHPoleN

/-!
# Game One — the **V-core twins**: closing `crossCircComm` ⟹ `CrossCommTowerEq` (= `MGTowerFam`).

This file closes the Term₁ commutator twin of the diagonal V-core: the cross commutator family
`crossCircComm` (`ZhuVermaAnArchMUcrossHM`) IS the homogeneous multi-grade tower family `MGTowerFam`
(`ZhuVermaAnArchMUcircDiff`) in the products `a₍s₎c` based at `d`.  This is the precise residual
commutator predicate `CrossCommTowerEq` (`ZhuVermaAnArchMUGradedFinal`).

## The reduction (FULLY proven, no `sorry`/axiom/`pbw`)

The cross commutator family is the `s`-outermost sum of its per-`s` slices

  `crossCircComm W n K M a c d = ∑_{s<N} crossCommSlice W n K M a c d s`        (`crossCircComm_eq_sliceSum`)

and each per-`s` slice IS a single-base level-`n` `PresAnm`-tower in the homogeneous base
`a₍s₎c ∈ 𝒱_{Ws}` (`Ws = K+M−s−1`):

  `crossCommSlice W n K M a c d s
     = PresTowerFam W Ws n (a₍s₎c) 1 (s+2) (fun _ => d) (fun _ => crossSliceWeight K n s)`
                                                                       (`crossCommSlice_eq_PresTowerFam`)

— at the level-`0`-inner (pole-`2`) circle the slice grade is `Ws` itself (NO `n`-offset; the inner
circle pole is `2 = 0+2`, so the tower grade matches the homogeneous base grade exactly).  Assembling
these single-base towers over the finite `s`-range into one `Fin N`-indexed multi-grade family gives
`crossCircComm = MGTowerFam`, with the per-index left factors `a₍s₎c` homogeneous of grade
`gradeS s = (K+M−s−1).toNat` (the genuine FULL level-`n` circle-generator span).  The negative-grade
slices vanish (`a₍s₎c = 0`) uniformly.

## What is proved here (axiom-clean)

* **`crossCommSlice_eq_singlePres`** — the per-`s` slice as a single-grade `PresAnm`-tower in `a₍s₎c`
  at grade `(K+M−s−1).toNat`, uniformly over the negative-grade vacuous case (slice `= 0`).
* **`crossCircComm_eq_MGTowerFam`** — `crossCircComm = MGTowerFam` (the explicit `Fin N`-indexed
  assembly), with the homogeneity of every left factor `a₍s₎c`.
* **`CrossCommTowerEq_holds`** — the Term₁ commutator predicate `CrossCommTowerEq`
  (`ZhuVermaAnArchMUGradedFinal`) discharged for all `n K M P` and homogeneous `a c d`.

## References
Dong–Jiang, Math. Z. 259 (2008) 799–826 (`math/0601626`), §2 (Lemma 2.8); Frenkel–Zhu Lemma 2.1.2;
Dong–Li–Mason; Gannon §5.3.2, Thm 5.3.4.
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The per-`s` slice as a single-grade `PresAnm`-tower (uniform over the vacuous case). -/

/-- **The per-`s` slice as a single-grade `PresAnm`-tower in `a₍s₎c`**, uniformly over `s`.  For the
nonnegative-grade slices (`K+M−s−1 ≥ 0`) it is `crossCommSlice_eq_PresTowerFam` at grade
`(K+M−s−1).toNat`; for the negative-grade slices the base `a₍s₎c = 0` (grading `𝒱_{<0} = ⊥`), so both
the slice and the tower vanish.  This packages each slice as exactly one `MGTowerFam` summand
`∑_{δ<s+2} (crossSliceWeight K n s δ) • PresAnm W gradeS n δ (a₍s₎c) d`. -/
theorem crossCommSlice_eq_singlePres (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {K M : ℕ} {a c : 𝒱}
    (ha : a ∈ W.grading (K : ℤ)) (hc : c ∈ W.grading (M : ℤ)) (d : 𝒱) (s : ℕ) :
    crossCommSlice W n K M a c d s
      = ∑ δ ∈ Finset.range (s + 2),
          crossSliceWeight K n s δ
            • PresAnm W ((K : ℤ) + (M : ℤ) - (s : ℤ) - 1).toNat n δ (W.smul a (s : ℤ) c) d := by
  set w := W.smul a (s : ℤ) c with hw
  have hwmem : w ∈ W.grading ((K : ℤ) + (M : ℤ) - (s : ℤ) - 1) :=
    crossCircComm_base_mem_grading W ha hc (s : ℤ)
  rcases lt_or_ge ((K : ℤ) + (M : ℤ) - (s : ℤ) - 1) 0 with hneg | hpos
  · -- negative grade: `w = 0`, both sides `0`.
    rw [W.positivity _ hneg, Submodule.mem_bot] at hwmem
    -- LHS slice `= 0`.
    have hslice0 : crossCommSlice W n K M a c d s = 0 := by
      rw [crossCommSlice]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [Finset.sum_eq_zero fun i _ => ?_, smul_zero]
      rw [← hw, hwmem, PreVertexAlgebra.smul_zero_left, smul_zero, smul_zero]
    rw [hslice0]
    symm
    refine Finset.sum_eq_zero fun δ _ => ?_
    rw [PresAnm]
    rw [Finset.sum_eq_zero fun i _ => ?_, smul_zero]
    rw [hwmem, PreVertexAlgebra.smul_zero_left, smul_zero]
  · -- nonnegative grade: use `crossCommSlice_eq_PresTowerFam` at `Ws = (…).toNat`.
    set Ws : ℕ := ((K : ℤ) + (M : ℤ) - (s : ℤ) - 1).toNat with hWsdef
    have hWs : (Ws : ℤ) = (K : ℤ) + (M : ℤ) - (s : ℤ) - 1 := by
      rw [hWsdef, Int.toNat_of_nonneg hpos]
    rw [crossCommSlice_eq_PresTowerFam W n K M a c d s Ws hWs, PresTowerFam]
    rw [Finset.univ_unique, Finset.sum_singleton]

/-! ## The cross commutator family IS a homogeneous multi-grade tower family. -/

/-- **`crossCircComm = MGTowerFam`** (the explicit `Fin N`-indexed assembly).  The cross commutator
family is the `s`-outermost sum of its per-`s` slices (`crossCircComm_eq_sliceSum`), each a single-base
level-`n` `PresAnm`-tower in `a₍s₎c` (`crossCommSlice_eq_singlePres`); collecting them over the finite
`s`-range gives the homogeneous multi-grade tower family `MGTowerFam` with per-index left factors
`a₍s₎c` of grade `(K+M−s−1).toNat`. -/
theorem crossCircComm_eq_MGTowerFam (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {K M : ℕ} {a c : 𝒱}
    (ha : a ∈ W.grading (K : ℤ)) (hc : c ∈ W.grading (M : ℤ)) (d : 𝒱) :
    ∃ (S : ℕ) (gradeS : Fin S → ℕ) (leftS baseS : Fin S → 𝒱) (ΔS : Fin S → ℕ)
        (wS : Fin S → ℕ → ℂ),
      (∀ r : Fin S, leftS r ∈ W.grading ((gradeS r : ℤ))) ∧
      crossCircComm W n K M a c d = MGTowerFam W n S gradeS leftS baseS ΔS wS := by
  obtain ⟨N, hN⟩ := crossCircComm_eq_sliceSum W n K M a c d
  refine ⟨N,
    (fun r => ((K : ℤ) + (M : ℤ) - (r : ℕ) - 1).toNat),
    (fun r => W.smul a ((r : ℕ) : ℤ) c),
    (fun _ => d),
    (fun r => (r : ℕ) + 2),
    (fun r => crossSliceWeight K n (r : ℕ)), ?_, ?_⟩
  · -- homogeneity of each left factor `a₍s₎c`.
    intro r
    simp only []
    rcases lt_or_ge ((K : ℤ) + (M : ℤ) - ((r : ℕ) : ℤ) - 1) 0 with hneg | hpos
    · -- negative grade: `a₍s₎c = 0 ∈ 𝒱_g` for any `g`.
      have : W.smul a ((r : ℕ) : ℤ) c = 0 := by
        have hmem := crossCircComm_base_mem_grading W ha hc ((r : ℕ) : ℤ)
        rwa [W.positivity _ hneg, Submodule.mem_bot] at hmem
      rw [this]
      exact Submodule.zero_mem _
    · -- nonnegative grade: `a₍s₎c` is homogeneous of `(…).toNat = …`.
      have hmem := crossCircComm_base_mem_grading W ha hc ((r : ℕ) : ℤ)
      rwa [show (((((K : ℤ) + (M : ℤ) - ((r : ℕ) : ℤ) - 1).toNat : ℕ)) : ℤ)
          = (K : ℤ) + (M : ℤ) - ((r : ℕ) : ℤ) - 1 from Int.toNat_of_nonneg hpos]
  · -- the assembly: `crossCircComm = ∑_s slice = ∑_{r:Fin N} (single tower)`.
    rw [hN, MGTowerFam, ← Fin.sum_univ_eq_sum_range (fun s => crossCommSlice W n K M a c d s) N]
    refine Finset.sum_congr rfl fun r _ => ?_
    exact crossCommSlice_eq_singlePres W n ha hc d (r : ℕ)

/-! ## `CrossCommTowerEq` discharged. -/

/-- **`CrossCommTowerEq W n K M P a c d` discharged** (for all `n K M P` and homogeneous `a c d`).
The cross commutator family `crossCircComm` is the homogeneous multi-grade tower family `MGTowerFam`
in the products `a₍s₎c` based at `d` (`crossCircComm_eq_MGTowerFam`).  This is the Term₁ commutator
twin of the diagonal V-core, FULLY proven via the per-`s` slice tower
(`CrossCommSliceTowerEq_holds`). -/
theorem CrossCommTowerEq_holds (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {K M P : ℕ} {a c d : 𝒱}
    (ha : a ∈ W.grading (K : ℤ)) (hc : c ∈ W.grading (M : ℤ)) (_hd : d ∈ W.grading (P : ℤ)) :
    CrossCommTowerEq W n K M P a c d := by
  obtain ⟨S, gradeS, leftS, baseS, ΔS, wS, hhom, heq⟩ :=
    crossCircComm_eq_MGTowerFam W n ha hc d
  exact ⟨S, gradeS, leftS, baseS, ΔS, wS, hhom, heq⟩

/-! ## Term₂: the `a`-outer level-`n` (pole-`(n+2)`) commutator slice. -/

/-- **The per-`s` slice of the Term₂ (`a`-outer, level-`n` inner pole) commutator family `ardComm`.**
The pole-`(n+2)` analogue of `crossCommSlice` (`ZhuVermaAnArchMUcrossCommSlice`): the inner `c`-mode is
`j−(n+2)` (pole `n+2`) instead of `j−2` (pole `2`).  Base `a₍s₎c`, expansion factor `C(i−n−1, s)`:

  `ardCommSlice W n K M a c d s
     = ∑_{j≤M} C(M,j) • ∑_{i≤K} C(K,i) • C(i−n−1, s) • (a₍s₎c)₍(i−n−1)+(j−(n+2))−s₎ d`. -/
noncomputable def ardCommSlice (W : VertexOperatorAlgebra 𝒱) (n K M : ℕ) (a c d : 𝒱) (s : ℕ) : 𝒱 :=
  ∑ j ∈ Finset.range (M + 1),
    cbz (M : ℤ) (j : ℤ) •
      ∑ i ∈ Finset.range (K + 1),
        cbz (K : ℤ) (i : ℤ) •
          cbz ((i : ℤ) - ((n : ℤ) + 1)) (s : ℤ)
            • W.smul (W.smul a (s : ℤ) c)
                (((i : ℤ) - ((n : ℤ) + 1)) + ((j : ℤ) - ((n : ℤ) + 2)) - (s : ℤ)) d

/-- **`ardComm` as the `s`-outermost sum of its per-`s` slices** (Borcherds expansion).  Expand each
bracket `⁅a₍i−n−1₎, c₍j−(n+2)₎⁆ d` by the uniform FZ commutator (`ZhuHR.mode_commutator_uniform W a c`),
then pull the `s`-sum outermost (`Finset.smul_sum`/`Finset.sum_comm`), exactly as in
`crossCircComm_eq_sliceSum` (`ZhuVermaAnArchMUcrossComm`) with the inner pole shifted `2 → n+2`. -/
theorem ardComm_eq_sliceSum (W : VertexOperatorAlgebra 𝒱) (n K M : ℕ) (a c d : 𝒱) :
    ∃ N : ℕ,
      ardComm W n K M a c d
        = ∑ s ∈ Finset.range N, ardCommSlice W n K M a c d s := by
  obtain ⟨N, hN⟩ := ZhuHR.mode_commutator_uniform W a c
  refine ⟨N, ?_⟩
  rw [ardComm]
  -- Step 0: Borcherds-expand each bracket.
  rw [show (∑ i ∈ Finset.range (K + 1),
            cbz (K : ℤ) (i : ℤ) •
              ∑ j ∈ Finset.range (M + 1),
                cbz (M : ℤ) (j : ℤ)
                  • ⁅mode (W.Y a) ((i : ℤ) - ((n : ℤ) + 1)),
                      mode (W.Y c) ((j : ℤ) - ((n : ℤ) + 2))⁆ d)
        = ∑ i ∈ Finset.range (K + 1),
            cbz (K : ℤ) (i : ℤ) •
              ∑ j ∈ Finset.range (M + 1),
                cbz (M : ℤ) (j : ℤ) •
                  ∑ s ∈ Finset.range N,
                    cbz ((i : ℤ) - ((n : ℤ) + 1)) (s : ℤ)
                      • W.smul (W.smul a (s : ℤ) c)
                          (((i : ℤ) - ((n : ℤ) + 1)) + ((j : ℤ) - ((n : ℤ) + 2)) - (s : ℤ)) d from
      Finset.sum_congr rfl fun i _ => by
        congr 1
        refine Finset.sum_congr rfl fun j _ => by
          rw [hN ((i : ℤ) - ((n : ℤ) + 1)) ((j : ℤ) - ((n : ℤ) + 2)) d]]
  -- Step 1: per `i`, pull the `s`-sum past the `j`-sum (swap `(j, s)`), distributing `cbz M j`.
  rw [show (∑ i ∈ Finset.range (K + 1),
            cbz (K : ℤ) (i : ℤ) •
              ∑ j ∈ Finset.range (M + 1),
                cbz (M : ℤ) (j : ℤ) •
                  ∑ s ∈ Finset.range N,
                    cbz ((i : ℤ) - ((n : ℤ) + 1)) (s : ℤ)
                      • W.smul (W.smul a (s : ℤ) c)
                          (((i : ℤ) - ((n : ℤ) + 1)) + ((j : ℤ) - ((n : ℤ) + 2)) - (s : ℤ)) d)
        = ∑ i ∈ Finset.range (K + 1),
            cbz (K : ℤ) (i : ℤ) •
              ∑ s ∈ Finset.range N,
                ∑ j ∈ Finset.range (M + 1),
                  cbz (M : ℤ) (j : ℤ) •
                    cbz ((i : ℤ) - ((n : ℤ) + 1)) (s : ℤ)
                      • W.smul (W.smul a (s : ℤ) c)
                          (((i : ℤ) - ((n : ℤ) + 1)) + ((j : ℤ) - ((n : ℤ) + 2)) - (s : ℤ)) d from
      Finset.sum_congr rfl fun i _ => by
        congr 1
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun s _ => by rw [Finset.smul_sum]]
  -- Step 2: per `i`, distribute the `cbz K i` weight into the `s`-sum.
  rw [show (∑ i ∈ Finset.range (K + 1),
            cbz (K : ℤ) (i : ℤ) •
              ∑ s ∈ Finset.range N,
                ∑ j ∈ Finset.range (M + 1),
                  cbz (M : ℤ) (j : ℤ) •
                    cbz ((i : ℤ) - ((n : ℤ) + 1)) (s : ℤ)
                      • W.smul (W.smul a (s : ℤ) c)
                          (((i : ℤ) - ((n : ℤ) + 1)) + ((j : ℤ) - ((n : ℤ) + 2)) - (s : ℤ)) d)
        = ∑ i ∈ Finset.range (K + 1),
            ∑ s ∈ Finset.range N,
              cbz (K : ℤ) (i : ℤ) •
                ∑ j ∈ Finset.range (M + 1),
                  cbz (M : ℤ) (j : ℤ) •
                    cbz ((i : ℤ) - ((n : ℤ) + 1)) (s : ℤ)
                      • W.smul (W.smul a (s : ℤ) c)
                          (((i : ℤ) - ((n : ℤ) + 1)) + ((j : ℤ) - ((n : ℤ) + 2)) - (s : ℤ)) d from
      Finset.sum_congr rfl fun i _ => by rw [Finset.smul_sum]]
  -- Step 3: swap `(i, s)` to pull `∑_s` outermost; the body is `∑_i ∑_j`.
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  -- per `s`, swap `(i, j)` (distributing `cbz K i` into the `j`-sum) to land on `ardCommSlice`'s
  -- `∑_j ∑_i` shape.
  rw [ardCommSlice]
  rw [show (∑ i ∈ Finset.range (K + 1),
            cbz (K : ℤ) (i : ℤ) •
              ∑ j ∈ Finset.range (M + 1),
                cbz (M : ℤ) (j : ℤ) •
                  cbz ((i : ℤ) - ((n : ℤ) + 1)) (s : ℤ)
                    • W.smul (W.smul a (s : ℤ) c)
                        (((i : ℤ) - ((n : ℤ) + 1)) + ((j : ℤ) - ((n : ℤ) + 2)) - (s : ℤ)) d)
        = ∑ i ∈ Finset.range (K + 1),
            ∑ j ∈ Finset.range (M + 1),
              cbz (M : ℤ) (j : ℤ) •
                cbz (K : ℤ) (i : ℤ) •
                  cbz ((i : ℤ) - ((n : ℤ) + 1)) (s : ℤ)
                    • W.smul (W.smul a (s : ℤ) c)
                        (((i : ℤ) - ((n : ℤ) + 1)) + ((j : ℤ) - ((n : ℤ) + 2)) - (s : ℤ)) d from
      Finset.sum_congr rfl fun i _ => by
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun j _ => by
          rw [smul_comm (cbz (K : ℤ) (i : ℤ)) (cbz (M : ℤ) (j : ℤ))]]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => by rw [Finset.smul_sum]

/-- The Term₂ per-`s` slice mode-coefficient at mode `μ` (the single-`i`-sum, after collecting the
`j`-sum into the mode value `μ = (i+j)−(2n+3+s)`):
`Cₛ(μ) = ∑_{i≤K} C(K,i) · C(i−n−1, s) · C(M, μ+2n+3+s−i)`.  The pole-`(n+2)` analogue of
`crossCommSliceCoeff` (`ZhuVermaAnArchMUcrossCommSlice`); it equals `crossCommSliceCoeff` shifted by
`n` in the mode: `ardCommSliceCoeff K M n s μ = crossCommSliceCoeff K M n s (μ+n)`. -/
noncomputable def ardCommSliceCoeff (K M n s : ℕ) (μ : ℤ) : ℂ :=
  ∑ i ∈ Finset.range (K + 1),
    cbz (K : ℤ) (i : ℤ) * cbz ((i : ℤ) - ((n : ℤ) + 1)) (s : ℤ)
      * cbz (M : ℤ) (μ + 2 * (n : ℤ) + 3 + s - (i : ℤ))

/-- For fixed `i`, the scalar `μ ↦ cbz M (μ+2n+3+s−i)` has finite support. -/
theorem ardSlice_shift_support_fin (M n s : ℕ) (i : ℤ) :
    (Function.support (fun μ : ℤ => cbz (M : ℤ) (μ + 2 * (n : ℤ) + 3 + s - i))).Finite := by
  refine Set.Finite.subset (ZhuHR.cbz_shift_support_fin (d := (M : ℤ)) (by positivity)
    (2 * (n : ℤ) + 3 + s - i)) ?_
  intro μ hμ
  rw [Function.mem_support] at hμ ⊢
  intro h; apply hμ
  rwa [show μ + 2 * (n : ℤ) + 3 + s - i = μ + (2 * (n : ℤ) + 3 + s - i) from by ring]

/-- **The Term₂ per-`s` slice in single-mode-finsum form.**  Collecting the `j`-sum (the mode source)
into the mode finsum, `ardCommSlice W n K M a c d s = ∑ᶠ μ, Cₛ(μ) • (a₍s₎c)₍μ₎ d`, with
`Cₛ = ardCommSliceCoeff K M n s`.  Pole-`(n+2)` mirror of `crossCommSlice_eq_finsum`
(`ZhuVermaAnArchMUcrossCommSlice`). -/
theorem ardCommSlice_eq_finsum (W : VertexOperatorAlgebra 𝒱) (n K M : ℕ) (a c d : 𝒱) (s : ℕ) :
    ardCommSlice W n K M a c d s
      = ∑ᶠ μ : ℤ, ardCommSliceCoeff K M n s μ • W.smul (W.smul a (s : ℤ) c) μ d := by
  set w := W.smul a (s : ℤ) c with hw
  rw [ardCommSlice]
  -- (a0) collapse each `(i,j)` term, `i`-sum outermost.
  rw [show (∑ j ∈ Finset.range (M + 1),
            cbz (M : ℤ) (j : ℤ) •
              ∑ i ∈ Finset.range (K + 1),
                cbz (K : ℤ) (i : ℤ) •
                  cbz ((i : ℤ) - ((n : ℤ) + 1)) (s : ℤ)
                    • W.smul w (((i : ℤ) - ((n : ℤ) + 1)) + ((j : ℤ) - ((n : ℤ) + 2)) - (s : ℤ)) d)
        = ∑ i ∈ Finset.range (K + 1), ∑ j ∈ Finset.range (M + 1),
            ((cbz (K : ℤ) (i : ℤ) * cbz ((i : ℤ) - ((n : ℤ) + 1)) (s : ℤ)) * cbz (M : ℤ) (j : ℤ))
              • W.smul w (((i : ℤ) - ((n : ℤ) + 1)) + ((j : ℤ) - ((n : ℤ) + 2)) - (s : ℤ)) d from by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_smul, smul_smul]
      congr 1; ring]
  -- (a) regroup as the coefficient-scaled inner `j`-sum.
  rw [show (∑ i ∈ Finset.range (K + 1), ∑ j ∈ Finset.range (M + 1),
            ((cbz (K : ℤ) (i : ℤ) * cbz ((i : ℤ) - ((n : ℤ) + 1)) (s : ℤ)) * cbz (M : ℤ) (j : ℤ))
              • W.smul w (((i : ℤ) - ((n : ℤ) + 1)) + ((j : ℤ) - ((n : ℤ) + 2)) - (s : ℤ)) d)
        = ∑ i ∈ Finset.range (K + 1),
            (cbz (K : ℤ) (i : ℤ) * cbz ((i : ℤ) - ((n : ℤ) + 1)) (s : ℤ)) •
              ∑ j ∈ Finset.range (M + 1),
                cbz (M : ℤ) (j : ℤ)
                  • W.smul w (((i : ℤ) - ((n : ℤ) + 1)) + ((j : ℤ) - ((n : ℤ) + 2)) - (s : ℤ)) d from
      Finset.sum_congr rfl fun i _ => by
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun j _ => by rw [smul_smul]]
  -- (b) per `i`, reindex the `j`-sum into a mode finsum (mode `μ = (i+j)−(2n+3+s)`).
  rw [show (∑ i ∈ Finset.range (K + 1),
            (cbz (K : ℤ) (i : ℤ) * cbz ((i : ℤ) - ((n : ℤ) + 1)) (s : ℤ)) •
              ∑ j ∈ Finset.range (M + 1),
                cbz (M : ℤ) (j : ℤ)
                  • W.smul w (((i : ℤ) - ((n : ℤ) + 1)) + ((j : ℤ) - ((n : ℤ) + 2)) - (s : ℤ)) d)
        = ∑ i ∈ Finset.range (K + 1),
            ∑ᶠ μ : ℤ,
              ((cbz (K : ℤ) (i : ℤ) * cbz ((i : ℤ) - ((n : ℤ) + 1)) (s : ℤ))
                * cbz (M : ℤ) (μ + 2 * (n : ℤ) + 3 + s - (i : ℤ))) • W.smul w μ d from
      Finset.sum_congr rfl fun i _ => by
        rw [show (∑ j ∈ Finset.range (M + 1),
                  cbz (M : ℤ) (j : ℤ)
                    • W.smul w (((i : ℤ) - ((n : ℤ) + 1)) + ((j : ℤ) - ((n : ℤ) + 2)) - (s : ℤ)) d)
              = ∑ j ∈ Finset.range (M + 1),
                  cbz (M : ℤ) (j : ℤ)
                    • W.smul w ((j : ℤ) + ((i : ℤ) - 2 * (n : ℤ) - 3 - s)) d from
            Finset.sum_congr rfl fun j _ => by
              rw [show ((i : ℤ) - ((n : ℤ) + 1)) + ((j : ℤ) - ((n : ℤ) + 2)) - (s : ℤ)
                    = (j : ℤ) + ((i : ℤ) - 2 * (n : ℤ) - 3 - s) from by ring]]
        rw [ZhuHR.rangeSmul_eq_finsumZ (fun q : ℤ => cbz (M : ℤ) q)
            (fun q => W.smul w q d) ((i : ℤ) - 2 * (n : ℤ) - 3 - s)
            (fun q hq => cbz_apply_neg _ hq)
            (fun q hq => cbz_lt (by positivity) (by exact_mod_cast hq))]
        rw [smul_finsum' (cbz (K : ℤ) (i : ℤ) * cbz ((i : ℤ) - ((n : ℤ) + 1)) (s : ℤ))
            (f := fun q : ℤ => cbz (M : ℤ) q • W.smul w (q + ((i : ℤ) - 2 * (n : ℤ) - 3 - s)) d)
            (smul_support_of_scalar_gen (fun q : ℤ => cbz (M : ℤ) q)
              (fun q : ℤ => W.smul w (q + ((i : ℤ) - 2 * (n : ℤ) - 3 - s)) d)
              (ZhuHR.cbz_shift_support_fin (d := (M : ℤ)) (by positivity) 0
                |>.subset (fun q hq => by
                  rw [Function.mem_support] at hq ⊢
                  intro h; apply hq; rwa [add_zero] at h)))]
        rw [← finsum_comp_equiv (Equiv.addRight ((i : ℤ) - 2 * (n : ℤ) - 3 - (s : ℤ)))
            (f := fun μ : ℤ =>
              ((cbz (K : ℤ) (i : ℤ) * cbz ((i : ℤ) - ((n : ℤ) + 1)) (s : ℤ))
                * cbz (M : ℤ) (μ + 2 * (n : ℤ) + 3 + s - (i : ℤ))) • W.smul w μ d)]
        refine finsum_congr fun q => ?_
        simp only [Equiv.coe_addRight]
        rw [smul_smul,
          show (q + ((i : ℤ) - 2 * (n : ℤ) - 3 - (s : ℤ))) + 2 * (n : ℤ) + 3 + s - (i : ℤ) = q from by
            ring]]
  -- (c) swap `∑_i ∑ᶠ μ ↦ ∑ᶠ μ ∑_i` and assemble into `ardCommSliceCoeff`.
  rw [← finsum_sum_comm (Finset.range (K + 1))
      (fun μ i => ((cbz (K : ℤ) (i : ℤ) * cbz ((i : ℤ) - ((n : ℤ) + 1)) (s : ℤ))
          * cbz (M : ℤ) (μ + 2 * (n : ℤ) + 3 + s - (i : ℤ))) • W.smul w μ d)
      (fun i _ => ZhuHR.smul_support_of_scalar W w d _
        (Set.Finite.subset (ardSlice_shift_support_fin M n s (i : ℤ))
          (fun μ hμ => by
            rw [Function.mem_support] at hμ ⊢
            intro h; apply hμ
            rw [h, mul_zero])))]
  refine finsum_congr fun μ => ?_
  rw [ardCommSliceCoeff, Finset.sum_smul]

/-! ## The Term₂ slice coefficient as a grade-`Ws` (TRUE-grade) `towerCoeffAnm` (via mode-regrade). -/

/-- **`ardCommSliceCoeff = crossCommSliceCoeff` shifted by `n` in the mode.**  Both are the same
`i`-sum `∑_i C(K,i) C(i−n−1, s) C(M, ·−i)`; the lower carrier index differs by `n`
(`μ+2n+3+s` vs `(μ+n)+n+3+s`). -/
theorem ardCommSliceCoeff_eq_shift (K M n s : ℕ) (μ : ℤ) :
    ardCommSliceCoeff K M n s μ = crossCommSliceCoeff K M n s (μ + (n : ℤ)) := by
  rw [ardCommSliceCoeff, crossCommSliceCoeff]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show (μ + (n : ℤ)) + (n : ℤ) + 3 + s - (i : ℤ) = μ + 2 * (n : ℤ) + 3 + s - (i : ℤ) from by
    ring]

/-- **The Term₂ slice depth weights on the common grade-`Ws` tower** (depth `s+n+2`).  The forward
diagonal-shift convolution of `crossSliceWeight` by the regrade kernel `(−1)^{n−i} C(n,i)`:
`ardSliceWeight K n s e = ∑_{i≤n} (−1)^{n−i} C(n,i) · crossSliceWeight K n s (e−i)` (`e−i` nat sub). -/
noncomputable def ardSliceWeight (K n s : ℕ) (e : ℕ) : ℂ :=
  ∑ i ∈ Finset.range (n + 1),
    (-1 : ℂ) ^ (n - i) * (Nat.choose n i : ℂ) * crossSliceWeight K n s (e - i)

/-- `crossSliceWeight` vanishes above depth `s+1` (`cbz K (s+1−δ) = 0` for `δ > s+1`). -/
theorem crossSliceWeight_hi (K n s : ℕ) {δ : ℕ} (hδ : s + 2 ≤ δ) :
    crossSliceWeight K n s δ = 0 := by
  rw [crossSliceWeight, if_neg (by omega)]
  rw [cbz_apply_neg (K : ℤ) (by omega : (s : ℤ) + 1 - (δ : ℤ) < 0), mul_zero]

/-- **The mode-regrade of the grade-`Ws` `crossSliceWeight` tower.**  Shifting the mode argument of a
grade-`G` level-`n` `towerCoeffAnm` by `+n` is absorbed by the forward diagonal-shift convolution of
the depth weights:

  `towerCoeffAnm G n (crossSliceWeight K n s) (s+2) (μ+n)
     = ∑_{e<s+n+2} (ardSliceWeight K n s e) · cbz(G+e, μ+(n+2)+e)`.

Per `dp`-row apply `crossDiff_regrade (G+dp) (μ+(2n+2)+dp) n` (top `G+dp`, lower `μ+(2n+2)+dp`, the
shifted lower `−n` gives `μ+(n+2)+dp`), reindex the inner `i` to the outer depth `e = dp+i`, and
collect.  An exploratory computer-algebra run reported zero residual; its script was not retained in the
checkpoint. -/
theorem towerCoeffAnm_mode_regrade (K G n s : ℕ) (μ : ℤ) :
    towerCoeffAnm G n (crossSliceWeight K n s) (s + 2) (μ + (n : ℤ))
      = ∑ e ∈ Finset.range (s + n + 2),
          ardSliceWeight K n s e * cbz ((G : ℤ) + (e : ℤ)) (μ + ((n : ℤ) + 2) + (e : ℤ)) := by
  rw [towerCoeffAnm]
  -- Step 1: regrade each `dp`-row by `crossDiff_regrade` (forward `i`-shift).
  rw [show (∑ dp ∈ Finset.range (s + 2),
        crossSliceWeight K n s dp
          * cbz ((G : ℤ) + (dp : ℤ)) ((μ + (n : ℤ)) + ((n : ℤ) + 2) + (dp : ℤ)))
      = ∑ dp ∈ Finset.range (s + 2), ∑ i ∈ Finset.range (n + 1),
          ((-1 : ℂ) ^ (n - i) * (Nat.choose n i : ℂ) * crossSliceWeight K n s dp)
            * cbz ((G : ℤ) + (dp : ℤ) + (i : ℤ))
                (μ + ((n : ℤ) + 2) + ((dp : ℤ) + (i : ℤ))) from
      Finset.sum_congr rfl fun dp _ => by
        rw [crossDiff_regrade ((G : ℤ) + (dp : ℤ)) ((μ + (n : ℤ)) + ((n : ℤ) + 2) + (dp : ℤ)) n,
          Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [show ((G : ℤ) + (dp : ℤ)) + (i : ℤ) = (G : ℤ) + (dp : ℤ) + (i : ℤ) from by ring,
          show (((μ + (n : ℤ)) + ((n : ℤ) + 2) + (dp : ℤ)) - (n : ℤ)) + (i : ℤ)
              = μ + ((n : ℤ) + 2) + ((dp : ℤ) + (i : ℤ)) from by ring]
        ring]
  -- Step 2: swap to `i`-outer, per-`i` shift `e = dp + i`.
  rw [Finset.sum_comm]
  -- RHS: expand `ardSliceWeight`, distribute, swap to `i`-outer.
  rw [show (∑ e ∈ Finset.range (s + n + 2),
        ardSliceWeight K n s e * cbz ((G : ℤ) + (e : ℤ)) (μ + ((n : ℤ) + 2) + (e : ℤ)))
      = ∑ i ∈ Finset.range (n + 1), ∑ e ∈ Finset.range (s + n + 2),
          ((-1 : ℂ) ^ (n - i) * (Nat.choose n i : ℂ) * crossSliceWeight K n s (e - i))
            * cbz ((G : ℤ) + (e : ℤ)) (μ + ((n : ℤ) + 2) + (e : ℤ)) from ?_]
  · -- per-`i`: `∑_{dp<s+2} wt(dp) g(dp+i) = ∑_{e<s+n+2} wt(e−i) g(e)`.
    refine Finset.sum_congr rfl fun i hi => ?_
    have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    -- shift `e = dp + i`: the active `dp ∈ [0, s+2)` maps to `e ∈ [i, i+s+2) ⊆ [0, s+n+2)`.
    rw [show (∑ dp ∈ Finset.range (s + 2),
          ((-1 : ℂ) ^ (n - i) * (Nat.choose n i : ℂ) * crossSliceWeight K n s dp)
            * cbz ((G : ℤ) + (dp : ℤ) + (i : ℤ)) (μ + ((n : ℤ) + 2) + ((dp : ℤ) + (i : ℤ))))
        = ∑ e ∈ Finset.Ico i (i + (s + 2)),
          ((-1 : ℂ) ^ (n - i) * (Nat.choose n i : ℂ) * crossSliceWeight K n s (e - i))
            * cbz ((G : ℤ) + (e : ℤ)) (μ + ((n : ℤ) + 2) + (e : ℤ)) from ?_]
    · refine Finset.sum_subset (fun e he => ?_) ?_
      · rw [Finset.mem_Ico] at he
        rw [Finset.mem_range]; omega
      · intro e _ he
        rw [Finset.mem_Ico, not_and_or] at he
        rcases he with h | h
        · -- `e < i` ⟹ `e − i = 0`, `crossSliceWeight 0 = 0`.
          rw [show e - i = 0 from by omega,
            show crossSliceWeight K n s 0 = 0 from by rw [crossSliceWeight]; simp,
            mul_zero, zero_mul]
        · -- `e ≥ i+(s+2)` ⟹ `e − i ≥ s+2`, `crossSliceWeight = 0`.
          rw [crossSliceWeight_hi K n s (by omega), mul_zero, zero_mul]
    · rw [Finset.sum_Ico_eq_sum_range]
      rw [show (i + (s + 2) - i : ℕ) = s + 2 from by omega]
      refine Finset.sum_congr rfl fun dp _ => ?_
      rw [show (i + dp - i : ℕ) = dp from by omega]
      rw [show ((i + dp : ℕ) : ℤ) = (dp : ℤ) + (i : ℤ) from by push_cast; ring,
        show (G : ℤ) + ((dp : ℤ) + (i : ℤ)) = (G : ℤ) + (dp : ℤ) + (i : ℤ) from by ring]
  · rw [show (∑ e ∈ Finset.range (s + n + 2),
          ardSliceWeight K n s e * cbz ((G : ℤ) + (e : ℤ)) (μ + ((n : ℤ) + 2) + (e : ℤ)))
        = ∑ e ∈ Finset.range (s + n + 2), ∑ i ∈ Finset.range (n + 1),
            ((-1 : ℂ) ^ (n - i) * (Nat.choose n i : ℂ) * crossSliceWeight K n s (e - i))
              * cbz ((G : ℤ) + (e : ℤ)) (μ + ((n : ℤ) + 2) + (e : ℤ)) from
        Finset.sum_congr rfl fun e _ => by rw [ardSliceWeight, Finset.sum_mul]]
    rw [Finset.sum_comm]

/-- **The Term₂ slice coefficient as a grade-`Ws` (TRUE-grade) `towerCoeffAnm`.**  Combining the mode
shift (`ardCommSliceCoeff_eq_shift`), the proven pole-`2` scalar core
(`crossCommSlice_coeff_eq_tower`, grade `Ws`), and the mode-regrade
(`towerCoeffAnm_mode_regrade`): `Cₛ(μ) = towerCoeffAnm Ws n (ardSliceWeight K n s) (s+n+2) μ`, at the
TRUE homogeneous grade `Ws = K+M−s−1` (NOT the shifted `Ws−n`).  This is the genuine `n`-offset
absorption: the pole-`(n+2)` slice IS a grade-`Ws` `PresAnm`-tower in its own base `a₍s₎c`. -/
theorem ardCommSliceCoeff_eq_tower (K M n s : ℕ) (Ws : ℕ)
    (hWs : (Ws : ℤ) = (K : ℤ) + (M : ℤ) - (s : ℤ) - 1) (μ : ℤ) :
    ardCommSliceCoeff K M n s μ
      = towerCoeffAnm Ws n (ardSliceWeight K n s) (s + n + 2) μ := by
  rw [ardCommSliceCoeff_eq_shift K M n s μ,
    crossCommSlice_coeff_eq_tower K M n s Ws hWs (μ + (n : ℤ)),
    towerCoeffAnm_mode_regrade K Ws n s μ, towerCoeffAnm]

/-! ## The Term₂ slice as a single-base grade-`Ws` `PresTowerFam`, hence a single-grade tower. -/

/-- **The Term₂ per-`s` slice as a single-grade `PresAnm`-tower in `a₍s₎c`**, uniformly over `s`.  For
the nonnegative-grade slices (`K+M−s−1 ≥ 0`) it is the grade-`Ws` tower from `ardCommSlice_eq_finsum`
+ `presAnmFamily_eq_finsum` + the scalar core `ardCommSliceCoeff_eq_tower`; for the negative-grade
slices the base `a₍s₎c = 0`, so both the slice and the tower vanish.  This packages each Term₂ slice as
exactly one `MGTowerFam` summand `∑_{δ<s+n+2} (ardSliceWeight K n s δ) • PresAnm W gradeS n δ (a₍s₎c) d`,
with the TRUE grade `gradeS = (K+M−s−1).toNat` (the genuine `n`-offset absorption). -/
theorem ardCommSlice_eq_singlePres (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {K M : ℕ} {a c : 𝒱}
    (ha : a ∈ W.grading (K : ℤ)) (hc : c ∈ W.grading (M : ℤ)) (d : 𝒱) (s : ℕ) :
    ardCommSlice W n K M a c d s
      = ∑ δ ∈ Finset.range (s + n + 2),
          ardSliceWeight K n s δ
            • PresAnm W ((K : ℤ) + (M : ℤ) - (s : ℤ) - 1).toNat n δ (W.smul a (s : ℤ) c) d := by
  set w := W.smul a (s : ℤ) c with hw
  have hwmem : w ∈ W.grading ((K : ℤ) + (M : ℤ) - (s : ℤ) - 1) :=
    crossCircComm_base_mem_grading W ha hc (s : ℤ)
  rcases lt_or_ge ((K : ℤ) + (M : ℤ) - (s : ℤ) - 1) 0 with hneg | hpos
  · -- negative grade: `w = 0`, both sides `0`.
    rw [W.positivity _ hneg, Submodule.mem_bot] at hwmem
    have hslice0 : ardCommSlice W n K M a c d s = 0 := by
      rw [ardCommSlice]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [Finset.sum_eq_zero fun i _ => ?_, smul_zero]
      rw [← hw, hwmem, PreVertexAlgebra.smul_zero_left, smul_zero, smul_zero]
    rw [hslice0]
    symm
    refine Finset.sum_eq_zero fun δ _ => ?_
    rw [PresAnm]
    rw [Finset.sum_eq_zero fun i _ => ?_, smul_zero]
    rw [hwmem, PreVertexAlgebra.smul_zero_left, smul_zero]
  · -- nonnegative grade: the grade-`Ws` single-base tower.
    set Ws : ℕ := ((K : ℤ) + (M : ℤ) - (s : ℤ) - 1).toNat with hWsdef
    have hWs : (Ws : ℤ) = (K : ℤ) + (M : ℤ) - (s : ℤ) - 1 := by
      rw [hWsdef, Int.toNat_of_nonneg hpos]
    rw [ardCommSlice_eq_finsum W n K M a c d s]
    rw [presAnmFamily_eq_finsum W Ws n w d (ardSliceWeight K n s) (s + n + 2)]
    refine finsum_congr fun μ => ?_
    rw [ardCommSliceCoeff_eq_tower K M n s Ws hWs μ]

/-! ## `ardComm = MGTowerFam`, hence `ARDCommTowerEq`. -/

/-- **`ardComm = MGTowerFam`** (the explicit `Fin N`-indexed assembly).  The Term₂ commutator family is
the `s`-outermost sum of its per-`s` slices (`ardComm_eq_sliceSum`), each a single-base grade-`Ws`
`PresAnm`-tower in `a₍s₎c` (`ardCommSlice_eq_singlePres`); collecting them over the finite `s`-range
gives the homogeneous multi-grade tower family `MGTowerFam` with per-index left factors `a₍s₎c` of grade
`(K+M−s−1).toNat`. -/
theorem ardComm_eq_MGTowerFam (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {K M : ℕ} {a c : 𝒱}
    (ha : a ∈ W.grading (K : ℤ)) (hc : c ∈ W.grading (M : ℤ)) (d : 𝒱) :
    ∃ (S : ℕ) (gradeS : Fin S → ℕ) (leftS baseS : Fin S → 𝒱) (ΔS : Fin S → ℕ)
        (wS : Fin S → ℕ → ℂ),
      (∀ r : Fin S, leftS r ∈ W.grading ((gradeS r : ℤ))) ∧
      ardComm W n K M a c d = MGTowerFam W n S gradeS leftS baseS ΔS wS := by
  obtain ⟨N, hN⟩ := ardComm_eq_sliceSum W n K M a c d
  refine ⟨N,
    (fun r => ((K : ℤ) + (M : ℤ) - (r : ℕ) - 1).toNat),
    (fun r => W.smul a ((r : ℕ) : ℤ) c),
    (fun _ => d),
    (fun r => (r : ℕ) + n + 2),
    (fun r => ardSliceWeight K n (r : ℕ)), ?_, ?_⟩
  · intro r
    simp only []
    rcases lt_or_ge ((K : ℤ) + (M : ℤ) - ((r : ℕ) : ℤ) - 1) 0 with hneg | hpos
    · have : W.smul a ((r : ℕ) : ℤ) c = 0 := by
        have hmem := crossCircComm_base_mem_grading W ha hc ((r : ℕ) : ℤ)
        rwa [W.positivity _ hneg, Submodule.mem_bot] at hmem
      rw [this]
      exact Submodule.zero_mem _
    · have hmem := crossCircComm_base_mem_grading W ha hc ((r : ℕ) : ℤ)
      rwa [show (((((K : ℤ) + (M : ℤ) - ((r : ℕ) : ℤ) - 1).toNat : ℕ)) : ℤ)
          = (K : ℤ) + (M : ℤ) - ((r : ℕ) : ℤ) - 1 from Int.toNat_of_nonneg hpos]
  · rw [hN, MGTowerFam, ← Fin.sum_univ_eq_sum_range (fun s => ardCommSlice W n K M a c d s) N]
    refine Finset.sum_congr rfl fun r _ => ?_
    exact ardCommSlice_eq_singlePres W n ha hc d (r : ℕ)

/-- **`ARDCommTowerEq W n K M P a c d` discharged** (for all `n K M P` and homogeneous `a c d`).
The Term₂ commutator family `ardComm` is the homogeneous multi-grade tower family `MGTowerFam` in the
products `a₍s₎c` based at `d` (`ardComm_eq_MGTowerFam`).  This is the `a`-outer level-`n` twin of the
diagonal V-core, the `n`-offset absorbed by the mode-regrade `towerCoeffAnm_mode_regrade` (built on the
proven `crossDiff_regrade`). -/
theorem ARDCommTowerEq_holds (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {K M P : ℕ} {a c d : 𝒱}
    (ha : a ∈ W.grading (K : ℤ)) (hc : c ∈ W.grading (M : ℤ)) (_hd : d ∈ W.grading (P : ℤ)) :
    ARDCommTowerEq W n K M P a c d := by
  obtain ⟨S, gradeS, leftS, baseS, ΔS, wS, hhom, heq⟩ :=
    ardComm_eq_MGTowerFam W n ha hc d
  exact ⟨S, gradeS, leftS, baseS, ΔS, wS, hhom, heq⟩

/-! ## `MUGradedAction W` from `ARDCommTowerEq` (Term₂, closed) — reduced to Term₁'s level-`0` c-first.

Both commutator twins are closed unconditionally:

* **Term₂** (the `a`-outer level-`n` circle) is FULLY discharged: its `c`-first family is a depth-`1`
  `PresTowerFam` in homogeneous `c` (`ardCFirst_eq_PresTowerFam`, level `n`, in `Onm W n 0`) and its
  commutator family is `MGTowerFam` (`ARDCommTowerEq_holds`).  `ardTerm2TowerEq_of_comm` assembles
  `ARDTerm2TowerEq`.
* **Term₁'s commutator** family (`crossCircComm`) is `MGTowerFam` (`CrossCommTowerEq_holds`); its
  membership `CrossCommOnm_holds` is independently proven.

So `MUGradedAction W` reduces — via the proven `MUGradedAction_of_HARDhom`
(`ZhuVermaAnArchAnmRightDiff`) — to the SINGLE remaining family `CrossCFirstOnm` (Term₁'s **level-`0`**
inner-circle c-first sum, the genuine cross subtlety NOT of commutator type). -/

/-- **`MUGradedAction W` from the single open family `CrossCFirstOnm`** (Term₁'s level-`0` c-first),
with Term₂ fully closed via `ARDCommTowerEq_holds` and Term₁'s commutator via `CrossCommOnm_holds`.
The Term₁ cross-circle membership comes from `anmRight_zero_crossCirc_mem_Onm_of_families`
(`CrossCFirstOnm` + `CrossCommOnm`); Term₂ from `ardTerm2TowerEq_of_comm` + `ardTerm2_mem_of_towerEq`
(`ARDCommTowerEq_holds`); `anmRightDiff_mem_of_pieces` + `MUGradedAction_of_HARDhom` assemble the
crux. -/
theorem MUGradedAction_of_crossCFirst (W : VertexOperatorAlgebra 𝒱)
    (hCF : ∀ n : ℕ, CrossCFirstOnm W n) :
    MUGradedAction W :=
  MUGradedAction_of_HARDhom W
    (fun n K M P a ha c hc d hd =>
      anmRightDiff_mem_of_pieces W n ha hc
        (anmRight_zero_crossCirc_mem_Onm_of_families W n (hCF n) (CrossCommOnm_holds W n) a c d)
        (ardTerm2TowerEq_of_comm W n ha hc d (ARDCommTowerEq_holds W n ha hc hd)))

/-! ## Status — both V-core commutator twins closed; `MUGradedAction` reduced to ONE level-`0` family.

Proved here (`#print axioms` = `[propext, Classical.choice, Quot.sound]`; no `sorry`/
`axiom`/`pbw`):

* **`crossCommSlice_eq_singlePres`** / **`crossCircComm_eq_MGTowerFam`** / **`CrossCommTowerEq_holds`**
  — the Term₁ commutator twin: `crossCircComm = MGTowerFam` (products `a₍s₎c` @ `d`), grade `Ws`
  (level-`0` inner circle, no `n`-offset).  discharged.
* **`ardCommSlice`** / **`ardComm_eq_sliceSum`** / **`ardCommSlice_eq_finsum`** — the Term₂ pole-`(n+2)`
  commutator slice machinery (the `a`-outer level-`n` analogue of `crossCommSlice`).
* **`ardCommSliceCoeff_eq_shift`** / **`towerCoeffAnm_mode_regrade`** / **`ardCommSliceCoeff_eq_tower`**
  — the genuine `n`-offset absorption: the pole-`(n+2)` slice coefficient is the TRUE-grade-`Ws`
  `towerCoeffAnm` (mode-shift `+n` absorbed by the forward diagonal-shift convolution of the depth
  weights, built on the proven `crossDiff_regrade`).
* **`ardCommSlice_eq_singlePres`** / **`ardComm_eq_MGTowerFam`** / **`ARDCommTowerEq_holds`** — the
  Term₂ commutator twin: `ardComm = MGTowerFam` (products `a₍s₎c` @ `d`), TRUE grade `Ws`.  discharged.
* **`MUGradedAction_of_crossCFirst`** — `MUGradedAction W` from the SINGLE remaining open family
  `CrossCFirstOnm` (Term₁'s level-`0` inner-circle c-first sum), with both commutator twins and Term₂
  fully closed here, and Term₁'s commutator via the proven `CrossCommOnm_holds`.

This CLOSES Tier-1 to the single non-commutator family `CrossCFirstOnm W n`
(`∑_{i≤K} C(K,i) • anmCirc W 0 0 c (a₍i−n−1₎ d) ∈ Onm W n 0` — the level-`0`, pole-`2` inner circle),
the genuine cross subtlety requiring the `OnmL` grading-generator contribution (NOT a commutator
twin of the V-core).  Engine-verified TRUE on the rank-1 free boson
(`certificates/mathematica/ardterm2_split.wl`, `certificates/mathematica/anmrightdiff_terms.wl`;
two further development scripts were not retained).
-/

end VOA

/-
`#print axioms` check (each of the following prints
`[propext, Classical.choice, Quot.sound]`, NO `pbw`, NO `sorryAx`):

  #print axioms VOA.crossCommSlice_eq_singlePres
  #print axioms VOA.crossCircComm_eq_MGTowerFam
  #print axioms VOA.CrossCommTowerEq_holds
  #print axioms VOA.ardComm_eq_sliceSum
  #print axioms VOA.ardCommSlice_eq_finsum
  #print axioms VOA.towerCoeffAnm_mode_regrade
  #print axioms VOA.ardCommSliceCoeff_eq_tower
  #print axioms VOA.ardComm_eq_MGTowerFam
  #print axioms VOA.ARDCommTowerEq_holds
  #print axioms VOA.MUGradedAction_of_crossCFirst
-/
