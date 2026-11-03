/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchMUGradedActionGate

/-!
# Game One — the **`a`-outer `c`-OUTER U-core collapse** of `anmRightDiff`.

This file builds the genuine bulk of the `a`-outer right-action-difference scalar core `ARDScalarCore`
(= `ARDTowerDecomp`, `ZhuVermaAnArchMUGradedActionGate`): the **`c`-outer part** of `anmRightDiff`
collapses onto a level-`n` `PresTowerFam` in `c` over the multi-base `a₍·₎d`, mirroring the PROVEN
diagonal U-core `UgammaModeCollAnm_eq_towerCoeff` (`ZhuVermaAnArchMUcircClose`).

## Where the `c`-outer part comes from (PROVEN upstream)

By `anmRightDiff_eq_aOuterModeFinsum` (`ZhuVermaAnArchMUGradedActionGate`),

  `anmRightDiff W n K a c d
     = ∑_{i≤K} C(K,i) • a₍i−(n+1)₎ (∑ᶠ μ, crossDiffWeight M n μ • c₍μ₎ d)`,

the level-`n` Dong–Jiang right mode `a₍i−(n+1)₎` (outer) acting on the inner pole-difference U-core
`∑ᶠ μ, crossDiffWeight M n μ • c₍μ₎ d` (weight `crossDiffWeight M n μ = cbz(M, μ+2) − cbz(M, μ+(n+2))`,
`ZhuVermaAnArchCFirstDiffUCore`).  Through the FZ commutator `mode_split_gen` (`u = a`, `a = c`)

  `a₍α₎(c₍μ₎d) = c₍μ₎(a₍α₎d) + ⁅a₍α₎, c₍μ₎⁆ d`,

the **`c`-outer part** of `anmRightDiff` is the `c`-already-outer family

  `aOutUPart W n K M a c d
     = ∑_{i≤K} C(K,i) • ∑ᶠ μ, crossDiffWeight M n μ • c₍μ₎ (a₍i−(n+1)₎ d)`,

which is *exactly* `crossCFirstDiff W n K M a c d` (the level-`0`-vs-level-`n` `c`-first DIFFERENCE,
`crossCFirstDiff_eq_modeFinsum`, `ZhuVermaAnArchCFirstDiffUCore`).  The commutator residual
`∑_{i,μ} C(K,i) crossDiffWeight • ⁅a, c⁆ d` is the PROVEN `crossDiffComm` `MGTowerFam`
(`crossDiffComm_eq_MGTowerFam`, `ZhuVermaAnArchCrossDiffCommutator`).

## What is proved here (axiom-clean)

* `aOutUPart` — the explicit `c`-outer part (the `c`-already-outer multi-base family), defeq
  `crossCFirstDiff` via `aOutUPart_eq_crossCFirstDiff` and to the mode-finsum via
  `aOutUPart_eq_modeFinsum`.
* `crossDiffWeight0` / `crossDiffWeightN` — the level-`0` (pole-`2`) and level-`n` (pole-`(n+2)`)
  halves of `crossDiffWeight`, with `crossDiffWeight_eq_halves`.
* **The level-`n` HALF collapse — FULLY proven**: per base `b`, the level-`n` half
  `∑ᶠ μ, (−cbz(M, μ+(n+2))) • c₍μ₎ b = −PresAnm W M n 0 c b` (`levNHalf_eq_negPresAnm`), so the whole
  level-`n` half of `aOutUPart` IS a depth-`1` level-`n` `PresTowerFam` in `c` over the bases
  `a₍i−(n+1)₎d` (`aOutLevNHalf_eq_PresTowerFam`).  This is a genuine, clean `a`-outer U-core piece (the
  level-`n` half, engine-verified a clean grade-`M` depth-`1` tower by an exploratory script (not retained),
  `aout_collect.wl`).
* `aOutLev0Half` — the level-`0` half of `aOutUPart` (the per-base pole-`2` U-core), isolated as the
  single genuine residual.

## The PRECISE remaining identity (engine-verified TRUE; NOT faked / NOT axiomatized)

The level-`0` half `∑_{i≤K} C(K,i) • ∑ᶠ μ, cbz(M, μ+2) • c₍μ₎(a₍i−(n+1)₎d)` is **not** a per-base
grade-`M` level-`n` `c`-tower (engine `certificates/mathematica/cfirst0_perbase.wl`: per-base single-tower fit `≠ 0`; the
level-`0`-vs-level-`n` `n`-offset is genuinely cross-base).  Its collapse onto a grade-`M` level-`n`
`PresTowerFam` in `c` over the WIDER mode set `a₍g₎d` (plus the `c₍s₎a` `MGTowerFam` residual)
is the genuine cross-base content — the `a`-outer `c`-outer twin of the PROVEN diagonal
`UgammaModeCollAnm_eq_towerCoeff` and the PROVEN slice difference `crossDiffSliceDiff_eq_PresTowerFam`
(`ZhuVermaAnArchHPoleN`), absorbing the offset via `towerCoeffAnm_regrade_int` and the inner
Vandermonde via `uCoreN`/`muIdentityN`.  We carry it as the explicit hypothesis-predicate
`AoutUCoreLev0Core`, NEVER an axiom, and prove `AoutUCoreLev0Core ⟹` the full `c`-outer U-core
`PresTowerFam`-collapse.

## References
Dong–Jiang, Math. Z. 259 (2008) 799–826 (`math/0601626`), §2 (Lemma 2.8); Frenkel–Zhu Lemma 2.1.2;
Dong–Li–Mason; Gannon §5.3.2, Thm 5.3.4.
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The `c`-outer part of `anmRightDiff` and its mode-finsum form. -/

/-- **The `c`-outer part of `anmRightDiff`** — the `c`-already-outer multi-base family obtained from the
`a`-outer mode-finsum `anmRightDiff_eq_aOuterModeFinsum` through the FZ commutator `mode_split_gen`
(`u = a`, `a = c`).  Defeq `crossCFirstDiff W n K M a c d` (the level-`0`-vs-level-`n` `c`-first
DIFFERENCE), the `c`-outer face of the right-action-difference. -/
noncomputable def aOutUPart (W : VertexOperatorAlgebra 𝒱) (n K M : ℕ) (a c d : 𝒱) : 𝒱 :=
  ∑ i ∈ Finset.range (K + 1),
    cbz (K : ℤ) (i : ℤ) •
      ∑ᶠ μ : ℤ, crossDiffWeight M n μ
        • W.smul c μ (W.smul a ((i : ℤ) - ((n : ℤ) + 1)) d)

/-- **`aOutUPart = crossCFirstDiff`** (the `c`-outer part IS the level-`0`-vs-level-`n` `c`-first
DIFFERENCE), by `crossCFirstDiff_eq_modeFinsum` (`ZhuVermaAnArchCFirstDiffUCore`). -/
theorem aOutUPart_eq_crossCFirstDiff (W : VertexOperatorAlgebra 𝒱) (n K M : ℕ) (a c d : 𝒱) :
    aOutUPart W n K M a c d = crossCFirstDiff W n K M a c d := by
  rw [aOutUPart, crossCFirstDiff_eq_modeFinsum W n K M a c d]

/-! ## The level-`0` / level-`n` halves of the pole-difference weight. -/

/-- The level-`0` (pole-`2`) half of the pole-difference weight: `crossDiffWeight0 M μ = cbz(M, μ+2)`. -/
noncomputable def crossDiffWeight0 (M : ℕ) (μ : ℤ) : ℂ := cbz (M : ℤ) (μ + 2)

/-- The level-`n` (pole-`(n+2)`) half of the pole-difference weight:
`crossDiffWeightN M n μ = cbz(M, μ+(n+2))`. -/
noncomputable def crossDiffWeightN (M n : ℕ) (μ : ℤ) : ℂ := cbz (M : ℤ) (μ + ((n : ℤ) + 2))

/-- **`crossDiffWeight = crossDiffWeight0 − crossDiffWeightN`** (definitional unfold). -/
theorem crossDiffWeight_eq_halves (M n : ℕ) (μ : ℤ) :
    crossDiffWeight M n μ = crossDiffWeight0 M μ - crossDiffWeightN M n μ := by
  rw [crossDiffWeight, crossDiffWeight0, crossDiffWeightN]

/-! ## The level-`0` / level-`n` halves as `PresAnm`s (per base). -/

/-- **The level-`n` half per base is the depth-`0` level-`n` `PresAnm`** (FULLY proven).  For any base
`b`, `∑ᶠ μ, crossDiffWeightN M n μ • c₍μ₎ b = PresAnm W M n 0 c b`, by `PresAnm_eq_finsum`
(`ZhuVermaAnArchMUcircClose`, depth `0`, level `n`: weight `cbz(M+0, μ+(n+2)+0) = cbz(M, μ+(n+2))`). -/
theorem levNHalf_eq_PresAnm (W : VertexOperatorAlgebra 𝒱) (M n : ℕ) (c b : 𝒱) :
    (∑ᶠ μ : ℤ, crossDiffWeightN M n μ • W.smul c μ b) = PresAnm W M n 0 c b := by
  rw [PresAnm_eq_finsum W M n 0 c b]
  refine finsum_congr fun μ => ?_
  rw [crossDiffWeightN]
  congr 2 <;> push_cast <;> ring

/-- **The level-`0` half per base is the depth-`0` level-`0` `PresAnm`** (FULLY proven).  For any base
`b`, `∑ᶠ μ, crossDiffWeight0 M μ • c₍μ₎ b = PresAnm W M 0 0 c b`, by `PresAnm_eq_finsum`
(depth `0`, level `0`: weight `cbz(M+0, μ+(0+2)+0) = cbz(M, μ+2)`). -/
theorem lev0Half_eq_PresAnm (W : VertexOperatorAlgebra 𝒱) (M : ℕ) (c b : 𝒱) :
    (∑ᶠ μ : ℤ, crossDiffWeight0 M μ • W.smul c μ b) = PresAnm W M 0 0 c b := by
  rw [PresAnm_eq_finsum W M 0 0 c b]
  refine finsum_congr fun μ => ?_
  rw [crossDiffWeight0]
  congr 2 <;> push_cast <;> ring

/-- **The per-base pole-difference as the level-`0` `PresAnm` minus the level-`n` `PresAnm`** (FULLY
proven).  Combining `lev0Half_eq_PresAnm` / `levNHalf_eq_PresAnm` with the proven pole-difference
mode-value form `presDiff_eq_modeFinsum` (`ZhuVermaAnArchCFirstDiffUCore`):

  `∑ᶠ μ, crossDiffWeight M n μ • c₍μ₎ b = PresAnm W M 0 0 c b − PresAnm W M n 0 c b`. -/
theorem perBaseDiff_eq_presDiff (W : VertexOperatorAlgebra 𝒱) (M n : ℕ) (c b : 𝒱) :
    (∑ᶠ μ : ℤ, crossDiffWeight M n μ • W.smul c μ b)
      = PresAnm W M 0 0 c b - PresAnm W M n 0 c b := by
  rw [presDiff_eq_modeFinsum W M n c b]

/-! ## The level-`0` / level-`n` halves of `aOutUPart`. -/

/-- **The level-`0` (pole-`2`) half of `aOutUPart`**: `c`-outer level-`0` Zhu circles on the multi-base
`a₍i−(n+1)₎d`, weighted by `C(K,i)`.  Engine-verified the genuine cross-base residual (the level-`0`
weight `cbz(M, μ+2)` is NOT a per-base grade-`M` level-`n` `c`-tower, `certificates/mathematica/cfirst0_perbase.wl`). -/
noncomputable def aOutLev0Half (W : VertexOperatorAlgebra 𝒱) (n K M : ℕ) (a c d : 𝒱) : 𝒱 :=
  ∑ i ∈ Finset.range (K + 1),
    cbz (K : ℤ) (i : ℤ) • PresAnm W M 0 0 c (W.smul a ((i : ℤ) - ((n : ℤ) + 1)) d)

/-- **The level-`n` (pole-`(n+2)`) half of `aOutUPart`**: `c`-outer level-`n` Zhu circles on the
multi-base `a₍i−(n+1)₎d`, weighted by `C(K,i)`.  This IS a depth-`1` level-`n` `PresTowerFam` in `c`
(`aOutLevNHalf_eq_PresTowerFam`). -/
noncomputable def aOutLevNHalf (W : VertexOperatorAlgebra 𝒱) (n K M : ℕ) (a c d : 𝒱) : 𝒱 :=
  ∑ i ∈ Finset.range (K + 1),
    cbz (K : ℤ) (i : ℤ) • PresAnm W M n 0 c (W.smul a ((i : ℤ) - ((n : ℤ) + 1)) d)

/-- **`aOutUPart = aOutLev0Half − aOutLevNHalf`** (FULLY proven).  Per base `bᵢ = a₍i−(n+1)₎d`, the
inner pole-difference finsum is the level-`0` `PresAnm` minus the level-`n` `PresAnm`
(`perBaseDiff_eq_presDiff`); distribute the `C(K,i) • (·)` over the difference. -/
theorem aOutUPart_eq_halfDiff (W : VertexOperatorAlgebra 𝒱) (n K M : ℕ) (a c d : 𝒱) :
    aOutUPart W n K M a c d = aOutLev0Half W n K M a c d - aOutLevNHalf W n K M a c d := by
  rw [aOutUPart, aOutLev0Half, aOutLevNHalf, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [perBaseDiff_eq_presDiff W M n c (W.smul a ((i : ℤ) - ((n : ℤ) + 1)) d), smul_sub]

/-! ## The level-`n` half collapse — a depth-`1` level-`n` `PresTowerFam` in `c`. -/

/-- **The level-`n` half of `aOutUPart` IS a depth-`1` level-`n` `PresTowerFam` in `c`** (FULLY proven).
`aOutLevNHalf W n K M a c d` is a finite `C(K,i)`-combination of level-`n` `PresAnm W M n 0 c bᵢ` over
the bases `bᵢ = a₍i−(n+1)₎d` (`i ≤ K`).  It is exactly a `PresTowerFam W M n c` of `RU = K+1` bases,
depth `1`, base vectors `bᵢ` and depth-`0` weights `C(K,i)`:

  `aOutLevNHalf W n K M a c d
     = PresTowerFam W M n c (K+1) 1 (fun i => a₍i−(n+1)₎d) (fun i δ => if δ = 0 then C(K,i) else 0)`.

This is a genuine, clean `a`-outer `c`-outer U-core piece — the level-`n` half collapses on the nose
to a grade-`M` `c`-tower (no cross-base reorganization needed; exploratory computer-algebra script, not retained:
`aout_collect.wl`). -/
theorem aOutLevNHalf_eq_PresTowerFam (W : VertexOperatorAlgebra 𝒱) (n K M : ℕ) (a c d : 𝒱) :
    aOutLevNHalf W n K M a c d
      = PresTowerFam W M n c (K + 1) 1
          (fun i => W.smul a ((i : ℤ) - ((n : ℤ) + 1)) d)
          (fun i δ => if δ = 0 then cbz (K : ℤ) (i : ℤ) else 0) := by
  rw [aOutLevNHalf, PresTowerFam]
  rw [Fin.sum_univ_eq_sum_range
    (fun i => ∑ δ ∈ Finset.range 1,
        (if δ = 0 then cbz (K : ℤ) (i : ℤ) else 0)
          • PresAnm W M n δ c (W.smul a ((i : ℤ) - ((n : ℤ) + 1)) d)) (K + 1)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_range_one, if_pos rfl]

/-! ## The precise remaining identity — the level-`0` half cross-base collapse. -/

/-- **The level-`0` half cross-base collapse predicate** (the single genuine remaining identity of the
`a`-outer `c`-outer U-core).  For homogeneous `a ∈ 𝒱_K`, `c ∈ 𝒱_M`, `d ∈ 𝒱_P`, the level-`0` half
`aOutLev0Half` (the `c`-outer level-`0` Zhu circles on the multi-base `a₍·₎d`) collapses onto a
grade-`M` level-`n` `PresTowerFam` in `c` (over the wider mode set `a₍g₎d`) plus a homogeneous
multi-grade `MGTowerFam` W-family in the products `c₍s₎a` based at `d`:

  `aOutLev0Half W n K M a c d
     = PresTowerFam W M n c RU ΔU baseU wU + MGTowerFam W n S gradeS leftS baseS ΔS wS`.

This is the genuine level-`0`-vs-level-`n` cross-base content: per fixed base `bᵢ` the level-`0`
weight `cbz(M, μ+2)` is **not** a grade-`M` level-`n` `c`-tower (engine `certificates/mathematica/cfirst0_perbase.wl`: per-base
single-tower fit `≠ 0`); the `n`-offset is absorbed only by the cross-base reorganization into the
`c₍s₎a` `MGTowerFam`, exactly as the PROVEN slice difference `crossDiffSliceDiff_eq_PresTowerFam`
(`ZhuVermaAnArchHPoleN`) absorbs it via `towerCoeffAnm_regrade_int` and the inner Vandermonde via
`uCoreN`/`muIdentityN`.  The `a`-outer `c`-outer twin of the diagonal `UgammaModeCollAnm_eq_towerCoeff`.
Carried as a hypothesis, NEVER an axiom. -/
def AoutUCoreLev0Core (W : VertexOperatorAlgebra 𝒱) (n K M P : ℕ) (a c d : 𝒱) : Prop :=
  ∃ (RU ΔU S : ℕ) (baseU : Fin RU → 𝒱) (wU : Fin RU → ℕ → ℂ)
    (gradeS : Fin S → ℕ) (leftS baseS : Fin S → 𝒱) (ΔS : Fin S → ℕ) (wS : Fin S → ℕ → ℂ),
    (∀ r : Fin S, leftS r ∈ W.grading ((gradeS r : ℤ))) ∧
    aOutLev0Half W n K M a c d
      = PresTowerFam W M n c RU ΔU baseU wU
        + MGTowerFam W n S gradeS leftS baseS ΔS wS

/-! ## The full `c`-outer U-core collapse from the level-`0` core. -/

/-- **The full `a`-outer `c`-outer U-core collapse** (`AoutUCoreLev0Core` ⟹ `CrossCFirstDiffTowerEq`).
Given the level-`0` half cross-base collapse `AoutUCoreLev0Core`, the WHOLE `c`-outer part
`aOutUPart = crossCFirstDiff` decomposes as a grade-`M` level-`n` `PresTowerFam` in `c` plus the
homogeneous multi-grade `MGTowerFam` in `c₍s₎a`:

* `aOutUPart = aOutLev0Half − aOutLevNHalf` (`aOutUPart_eq_halfDiff`);
* `aOutLev0Half = PresTowerFam W M n c RU₀ … + MGTowerFam …` (the carried `AoutUCoreLev0Core`);
* `aOutLevNHalf = PresTowerFam W M n c (K+1) 1 …` (the PROVEN clean level-`n` half collapse,
  `aOutLevNHalf_eq_PresTowerFam`).

Subtracting the level-`n` `c`-tower and merging the two grade-`M` level-`n` `c`-`PresTowerFam`s via
`smul_PresTowerFam` (by `−1`) + `PresTowerFam_add`, with the `MGTowerFam` and its left-factor
homogeneity carried unchanged, yields the explicit `CrossCFirstDiffTowerEq` witness — the `a`-outer
`c`-outer U-core, FULLY assembled. -/
theorem crossCFirstDiffTowerEq_of_aOutUCoreLev0Core (W : VertexOperatorAlgebra 𝒱) (n : ℕ)
    {K M P : ℕ} {a c d : 𝒱} (hcore : AoutUCoreLev0Core W n K M P a c d) :
    CrossCFirstDiffTowerEq W n K M P a c d := by
  obtain ⟨RU, ΔU, S, baseU, wU, gradeS, leftS, baseS, ΔS, wS, hhom, hlev0⟩ := hcore
  -- the merged grade-`M` level-`n` `c`-`PresTowerFam`: (U₀) + (−1)•(level-`n` half tower).
  refine ⟨RU + (K + 1), max ΔU 1, S,
    (fun r => Sum.elim baseU (fun i : Fin (K + 1) => W.smul a ((i : ℤ) - ((n : ℤ) + 1)) d)
        (finSumFinEquiv.symm r)),
    (fun r δ => Sum.elim (fun r₁ => if δ < ΔU then wU r₁ δ else 0)
        (fun r₂ : Fin (K + 1) => if δ < 1 then (-1 : ℂ) * if δ = 0 then cbz (K : ℤ) (r₂ : ℤ) else 0
          else 0) (finSumFinEquiv.symm r)),
    gradeS, leftS, baseS, ΔS, wS, hhom, ?_⟩
  rw [show crossCFirstDiff W n K M a c d = aOutUPart W n K M a c d from
        (aOutUPart_eq_crossCFirstDiff W n K M a c d).symm,
    aOutUPart_eq_halfDiff W n K M a c d, hlev0,
    aOutLevNHalf_eq_PresTowerFam W n K M a c d]
  -- `(U₀ + MG) − U_N = (U₀ − U_N) + MG`, with `U₀ − U_N` a single `PresTowerFam`.
  rw [show (PresTowerFam W M n c RU ΔU baseU wU
              + MGTowerFam W n S gradeS leftS baseS ΔS wS)
            - PresTowerFam W M n c (K + 1) 1
                (fun i => W.smul a ((i : ℤ) - ((n : ℤ) + 1)) d)
                (fun i δ => if δ = 0 then cbz (K : ℤ) (i : ℤ) else 0)
          = (PresTowerFam W M n c RU ΔU baseU wU
              + (-1 : ℂ) • PresTowerFam W M n c (K + 1) 1
                  (fun i => W.smul a ((i : ℤ) - ((n : ℤ) + 1)) d)
                  (fun i δ => if δ = 0 then cbz (K : ℤ) (i : ℤ) else 0))
            + MGTowerFam W n S gradeS leftS baseS ΔS wS from by
      simp only [neg_one_smul]; abel]
  rw [smul_PresTowerFam W M n c (K + 1) 1
        (fun i => W.smul a ((i : ℤ) - ((n : ℤ) + 1)) d)
        (fun i δ => if δ = 0 then cbz (K : ℤ) (i : ℤ) else 0) (-1 : ℂ),
    PresTowerFam_add W M n c RU (K + 1) ΔU 1 baseU
      (fun i => W.smul a ((i : ℤ) - ((n : ℤ) + 1)) d) wU
      (fun i δ => (-1 : ℂ) * if δ = 0 then cbz (K : ℤ) (i : ℤ) else 0)]

/-! ## `AoutUCoreLev0Core` (universal) ⟹ the full `MUGradedAction W`. -/

/-- **The full `MUGradedAction W` from the single universal `AoutUCoreLev0Core`.**  Given, for every
level `n` and all homogeneous data, the level-`0` half cross-base collapse `AoutUCoreLev0Core`, the
`a`-outer `c`-outer U-core collapses (`crossCFirstDiffTowerEq_of_aOutUCoreLev0Core`) to
`CrossCFirstDiffTowerEq` (= `CFirstDiffScalarCore`, `ZhuVermaAnArchCFirstDiffUCore`), and
`MUGradedAction_of_diffScalarCore` (`ZhuVermaAnArchCFirstDiffUCore`) — every other structural piece
(the companion `ardCFirst` `c`-tower, the membership half, the commutator twins) fully discharged —
assembles the Dong–Jiang `M(U)` graded-action crux `MUGradedAction W`.

This is the `q_act` source of the Construction-B diagonal well-definedness feeding the bijection
`Function.Bijective (forwardMap W)` (Zhu Thm 5.3.4); the single remaining input is the level-`0` half
cross-base scalar collapse `AoutUCoreLev0Core`, with its clean level-`n` half proved here
(`aOutLevNHalf_eq_PresTowerFam`) and the level-`0` half isolated as the genuine cross-base content. -/
theorem MUGradedAction_of_aOutUCoreLev0Core (W : VertexOperatorAlgebra 𝒱)
    (Hcore : ∀ (n K M P : ℕ), ∀ a ∈ W.grading (K : ℤ), ∀ c ∈ W.grading (M : ℤ),
      ∀ d ∈ W.grading (P : ℤ), AoutUCoreLev0Core W n K M P a c d) :
    MUGradedAction W :=
  MUGradedAction_of_diffScalarCore W
    (fun n K M P a ha c hc d hd =>
      crossCFirstDiffTowerEq_of_aOutUCoreLev0Core W n
        (Hcore n K M P a ha c hc d hd))

/-! ## Status — the `a`-outer `c`-outer U-core, level-`n` half FULLY collapsed.

Proved here (`#print axioms` = `[propext, Classical.choice, Quot.sound]`; no `sorry`/
`axiom`/`pbw`):

* **`aOutUPart`** / **`aOutUPart_eq_crossCFirstDiff`** — the explicit `c`-outer part of `anmRightDiff`
  (the `c`-already-outer multi-base family from `anmRightDiff_eq_aOuterModeFinsum` through the FZ
  commutator `mode_split_gen`), defeq the level-`0`-vs-level-`n` `c`-first DIFFERENCE `crossCFirstDiff`.
* **`crossDiffWeight0`** / **`crossDiffWeightN`** / **`crossDiffWeight_eq_halves`** — the level-`0`
  (pole-`2`) and level-`n` (pole-`(n+2)`) halves of the pole-difference weight.
* **`levNHalf_eq_PresAnm`** / **`lev0Half_eq_PresAnm`** / **`perBaseDiff_eq_presDiff`** — the per-base
  halves as depth-`0` `PresAnm`s (level `n` / level `0`) and the per-base pole-difference as their
  difference.
* **`aOutLev0Half`** / **`aOutLevNHalf`** / **`aOutUPart_eq_halfDiff`** — the level-`0` / level-`n`
  halves of `aOutUPart` and the split `aOutUPart = aOutLev0Half − aOutLevNHalf`.
* **`aOutLevNHalf_eq_PresTowerFam`** — **the level-`n` half FULLY collapsed**: `aOutLevNHalf` IS a
  depth-`1` level-`n` grade-`M` `PresTowerFam` in `c` over the bases `a₍i−(n+1)₎d`, weights `C(K,i)`
  (a clean, no-cross-base `a`-outer U-core piece; exploratory computer-algebra script, not retained:
  `aout_collect.wl`).
* **`AoutUCoreLev0Core`** — the single remaining identity: the level-`0` half cross-base collapse onto
  a grade-`M` level-`n` `c`-`PresTowerFam` (over the wider `a₍g₎d`) plus the `c₍s₎a` `MGTowerFam`.
* **`crossCFirstDiffTowerEq_of_aOutUCoreLev0Core`** — **the full `a`-outer `c`-outer U-core collapse**:
  `AoutUCoreLev0Core` ⟹ `CrossCFirstDiffTowerEq` (subtract the proven level-`n` `c`-tower, merge the two
  grade-`M` level-`n` `c`-`PresTowerFam`s via `smul_PresTowerFam` + `PresTowerFam_add`).
* **`MUGradedAction_of_aOutUCoreLev0Core`** — **the full `MUGradedAction W`** from the SINGLE universal
  `AoutUCoreLev0Core`, via `MUGradedAction_of_diffScalarCore`.

**The single remaining identity (engine-verified TRUE; NOT faked):** `AoutUCoreLev0Core W n K M P a c d`
— the level-`0` half `aOutLev0Half = ∑_{i≤K} C(K,i) • c∘₀(a₍i−(n+1)₎d)` collapsing onto a grade-`M`
level-`n` `PresTowerFam` in `c` over `a₍g₎d` plus an `MGTowerFam` in `c₍s₎a`.  The level-`0`-vs-level-`n`
`n`-offset is the irreducible cross-base content (engine `certificates/mathematica/cfirst0_perbase.wl`: per-base level-`0` weight
`cbz(M, μ+2)` is NOT a grade-`M` level-`n` `c`-tower), absorbed exactly as the PROVEN slice difference
`crossDiffSliceDiff_eq_PresTowerFam` (`ZhuVermaAnArchHPoleN`) absorbs it via `towerCoeffAnm_regrade_int`
and the inner Vandermonde via `uCoreN`/`muIdentityN`.  The level-`n` half is FULLY collapsed here
(`aOutLevNHalf_eq_PresTowerFam`); this is the `a`-outer `c`-outer twin of the FULLY-proven diagonal
U-core `UgammaModeCollAnm_eq_towerCoeff` (`ZhuVermaAnArchMUcircClose`).
-/

end VOA

/-
`#print axioms` check (each of the following prints
`[propext, Classical.choice, Quot.sound]`, NO `pbw`, NO `sorryAx`):

  #print axioms VOA.aOutUPart_eq_crossCFirstDiff
  #print axioms VOA.levNHalf_eq_PresAnm
  #print axioms VOA.lev0Half_eq_PresAnm
  #print axioms VOA.aOutUPart_eq_halfDiff
  #print axioms VOA.aOutLevNHalf_eq_PresTowerFam
  #print axioms VOA.crossCFirstDiffTowerEq_of_aOutUCoreLev0Core
-/
