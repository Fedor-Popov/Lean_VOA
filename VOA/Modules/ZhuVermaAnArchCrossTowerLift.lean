/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchMUGradedClose

/-!
# Game One — the **cross tower lift**: the pole-`(n+2)` cross slice as a grade-`(Ws−n)` `PresAnm`-tower.

This file lifts the PROVEN diagonal tower-collapse machinery
(`UgammaModeCollAnm_eq_towerCoeff` / `VgammaModeCollAnm_eq_towerCoeff`, `AnmCircTowerEq_holds`,
`ZhuVermaAnArchMUcircV` + `ZhuVermaAnArchMUcircClose`) to the **cross** case — the level-`0`-inner
(pole-`2`) circle `anmCirc W 0 0 c (a₍g₎d)` and its companion pole-`(n+2)` cross slice — and closes the
genuine cross **scalar core** for the pole-`(n+2)` slice of the Dong–Jiang Lemma 2.8 pole-difference
commutator family (`crossDiffComm`, `ZhuVermaAnArchMUcircDiffCollapse`).

## The cross U-core / V-core scalar identity (FULLY proven; engine-verified zero residual)

The starting point is the FULLY-proven closed form of the pole-`(n+2)` slice coefficient
(`crossDiffSliceCoeffN_closed`, `ZhuVermaAnArchMUGradedClose`):

  `crossDiffSliceCoeff K M n (n+2) s μ
     = ∑_{p≤s} ((−1)^{s−p}·C((n+1)+(s−p), s−p)·C(M,p)) · C(M−p+K, μ+(n+1)+(n+2)+s−p)`.

The genuine cross content (the "cross U-core / V-core") is that this slice coefficient is a
single grade-`(Ws−n)` `towerCoeffAnm` (the level-`n` `PresAnm`-coefficient table of the SHIFTED grade
`Ws−n`, NOT the base grade `Ws = M+K−s−1` of `c₍s₎a`):

  `crossDiffSliceCoeff K M n (n+2) s μ
     = towerCoeffAnm (Ws−n) n (crossDiffSliceWeightN K M n s) (s+n+2) μ`,        (`crossDiffSliceCoeffN_eq_tower`)

with the **explicit cross-tower depth weights** (the `n`-offset of the diagonal weight)

  `crossDiffSliceWeightN(dp) = (−1)^{dp−n−1}·C((n+1)+(dp−n−1), dp−n−1)·C(M, s−(dp−n−1))`
      for `n+1 ≤ dp ≤ n+1+s`,  else `0`.

This mirrors `crossDiffSliceCoeff2_eq_tower` (`ZhuVermaAnArchMUcircDiffCollapse`) EXACTLY at the
shifted indices: the diagonal grade `Ws` and depth `δ+1` are replaced by the shifted grade `Ws−n` and
depth `n+1+δ` (`δ = s−p`); at `n = 0` the two coincide.  Engine-verified zero residual on the rank-1
free boson for all `K, M, n, s, μ` (`certificates/mathematica/poleN_towerlean.wl`,
`certificates/mathematica/poleN_gradeshift.wl`, `certificates/mathematica/poleN_reindex.wl`).

## The grade-`(Ws−n)` `PresTowerFam` form and the conditional membership

  `crossDiffSlice W n K M a c d (n+2) s
     = PresTowerFam W (Ws−n) n (c₍s₎a) 1 (s+n+2) (fun _ => d) (fun _ => crossDiffSliceWeightN K M n s)`
                                                                       (`crossDiffSliceN_eq_PresTowerFam`)

is the cross mirror of `crossDiffSlice2_eq_PresTowerFam` (pole `2`, grade `Ws`).  Its membership in
`Onm W n 0` follows from the keystone `Pres_mem_Onm` (via `PresTowerFam_mem_Onm`) **once the left
factor `c₍s₎a` is homogeneous of the SHIFTED grade `Ws−n`** — proved here as
`crossDiffSliceN_mem_Onm_of_homog`, carrying the homogeneity as an EXPLICIT hypothesis (NOT an axiom).

## The PRECISE remaining content (NOT `sorry`'d / NOT axiomatized) — the `n`-offset convolution

The genuine remaining obstruction is the engine-confirmed `n`-offset: the base `c₍s₎a` is homogeneous
of grade `Ws`, NOT `Ws−n` (`crossCircComm_base_mem_grading` / `crossDiffSlice2_mem_Onm`), so the
individual pole-`(n+2)` slice is NOT a single-grade `PresTowerFam` in its own base
(`certificates/mathematica/poleN_derive2.wl`: grade-`Ws` single-tower span `False` for `n ≥ 1`).  The
`n`-offset is absorbed only by the **cross-`s` convolution with the partner pole-`2` slice**
(`crossDiffComm_eq_sliceSum`: `crossDiffComm = ∑_{s<N} (slice₂ − sliceₙ₊₂)`,
`ZhuVermaAnArchMUcircDiffCollapse`).  The exact remaining identity is therefore the membership

  `(HPoleN)   crossDiffSlice W n K M a c d (n+2) s ∈ Onm W n 0`     (for all homogeneous `a, c`, all `s`),

which — together with `crossDiffSlice2_mem_Onm` (the pole-`2` half, FULLY proven) — feeds
`crossDiffComm_mem_Onm_of_poleN`, `circDiffAnmRight_mem_of_pieces`, and
`MUGradedAction_of_circDiffPieces` (`ZhuVermaAnArchMUGradedClose`) to the full DJ `M(U)` graded-action
crux `MUGradedAction W`.  We record here:

* the cross scalar core `crossDiffSliceCoeffN_eq_tower` (the cross U-core/V-core, FULLY proven);
* the grade-`(Ws−n)` `PresTowerFam` form `crossDiffSliceN_eq_PresTowerFam` (FULLY proven);
* the conditional membership `crossDiffSliceN_mem_Onm_of_homog` (FULLY proven, homogeneity as
  hypothesis);
* the full `MUGradedAction W` assembly from the EXACT remaining pieces
  (`MUGradedAction_of_crossTowerLift`), wiring `HPoleN` (the pole-`(n+2)` slice membership) and `HARD`
  (the `anmRightDiff` U-family) — the two engine-verified pole-difference identities — through the
  proven `MUGradedAction_of_circDiffPieces`.

## References
Dong–Jiang, Math. Z. 259 (2008) 799–826 (`math/0601626`), §2 (Lemma 2.8); Frenkel–Zhu Lemma 2.1.2;
Dong–Li–Mason; Gannon §5.3.2, Thm 5.3.4.
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators
open Finset

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The explicit cross-tower depth weights (the `n`-offset of the diagonal weight). -/

/-- **The pole-`(n+2)` cross-slice depth weights** of the grade-`(Ws−n)` tower (the cross U-core/V-core
weight table; the `n`-offset of `crossDiffSliceWeight2`).  At depth `dp`, with `δ = dp − (n+1)`:

  `crossDiffSliceWeightN(dp) = (−1)^δ·C((n+1)+δ, δ)·C(M, s−δ)`  for `0 ≤ δ ≤ s`  (`n+1 ≤ dp ≤ n+1+s`),
  else `0`.

Engine-verified `M`-up-to-`C(M,·)`, zero residual (`certificates/mathematica/poleN_towerlean.wl`).  At
`n = 0` this is `crossDiffSliceWeight2 M s` (pole `2`, grade `Ws`). -/
noncomputable def crossDiffSliceWeightN (K M n s : ℕ) (dp : ℕ) : ℂ :=
  if h : (n + 1 ≤ dp ∧ dp ≤ n + 1 + s) then
    (-1 : ℂ) ^ (dp - (n + 1))
      * cbz ((n : ℤ) + 1 + ((dp : ℤ) - (n + 1))) ((dp : ℤ) - (n + 1))
      * cbz (M : ℤ) ((s : ℤ) - ((dp : ℤ) - (n + 1)))
  else 0

/-- `crossDiffSliceWeightN` vanishes below depth `n+1`. -/
theorem crossDiffSliceWeightN_lo (K M n s : ℕ) {dp : ℕ} (hdp : dp < n + 1) :
    crossDiffSliceWeightN K M n s dp = 0 := by
  rw [crossDiffSliceWeightN, dif_neg (by omega)]

/-- `crossDiffSliceWeightN` vanishes above depth `n+1+s`. -/
theorem crossDiffSliceWeightN_hi (K M n s : ℕ) {dp : ℕ} (hdp : n + 1 + s < dp) :
    crossDiffSliceWeightN K M n s dp = 0 := by
  rw [crossDiffSliceWeightN, dif_neg (by omega)]

/-- The cross-tower weight at depth `dp = (n+1) + q` (the active window, `q ≤ s`). -/
theorem crossDiffSliceWeightN_at (K M n s q : ℕ) (hq : q ≤ s) :
    crossDiffSliceWeightN K M n s ((n + 1) + q)
      = (-1 : ℂ) ^ q
          * cbz ((n : ℤ) + 1 + (q : ℤ)) (q : ℤ)
          * cbz (M : ℤ) ((s : ℤ) - (q : ℤ)) := by
  rw [crossDiffSliceWeightN, dif_pos (by omega)]
  rw [show ((n + 1) + q - (n + 1) : ℕ) = q from by omega,
    show ((((n + 1) + q : ℕ)) : ℤ) - ((n : ℤ) + 1) = (q : ℤ) from by push_cast; ring]

/-! ## The cross scalar core: the pole-`(n+2)` slice coefficient as a grade-`(Ws−n)` tower. -/

/-- **The cross scalar core (cross U-core / V-core).**  The per-`s` pole-`(n+2)` slice coefficient
equals the grade-`(Ws−n)` `PresAnm`-tower coefficient with the explicit cross-tower depth weights
`crossDiffSliceWeightN K M n s` (depth `< s+n+2`, grade `Ws−n`, level `n`):

  `crossDiffSliceCoeff K M n (n+2) s μ
     = towerCoeffAnm (Ws−n) n (crossDiffSliceWeightN K M n s) (s+n+2) μ`,    `Ws−n = M+K−s−1−n`.

This is the cross lift of the diagonal `crossDiffSliceCoeff2_eq_tower` (pole `2`, grade `Ws`, depth
`δ+1`): the only changes are the SHIFTED grade `Ws−n` and the depth offset `n+1+δ` (`δ = s−p`).  Proof:
start from the proven closed form `crossDiffSliceCoeffN_closed`, restrict the `towerCoeffAnm`
`range(s+n+2)` sum to the active window `[n+1, n+1+s]` (zero weight elsewhere), shift to `range(s+1)`,
and reflect `q ↦ s−q = δ` (`p = s−δ`).  Engine-verified zero residual
(`certificates/mathematica/poleN_towerlean.wl`). -/
theorem crossDiffSliceCoeffN_eq_tower (K M n s : ℕ) (Wsn : ℕ)
    (hWsn : (Wsn : ℤ) = (M : ℤ) + (K : ℤ) - (s : ℤ) - 1 - (n : ℤ)) (μ : ℤ) :
    crossDiffSliceCoeff K M n (n + 2) s μ
      = towerCoeffAnm Wsn n (crossDiffSliceWeightN K M n s) (s + n + 2) μ := by
  rw [crossDiffSliceCoeffN_closed K M n s μ, towerCoeffAnm]
  -- restrict the `range(s+n+2)` tower sum to the active window `Ico (n+1) (n+1+(s+1))`.
  have hsplit : (∑ dp ∈ Finset.range (s + n + 2),
        crossDiffSliceWeightN K M n s dp * cbz ((Wsn : ℤ) + dp) (μ + ((n : ℤ) + 2) + dp))
      = ∑ dp ∈ Finset.Ico (n + 1) ((n + 1) + (s + 1)),
        crossDiffSliceWeightN K M n s dp * cbz ((Wsn : ℤ) + dp) (μ + ((n : ℤ) + 2) + dp) := by
    symm
    refine Finset.sum_subset ?_ ?_
    · intro dp hdp
      rw [Finset.mem_Ico] at hdp
      rw [Finset.mem_range]; omega
    · intro dp _ hdp
      rw [Finset.mem_Ico, not_and_or] at hdp
      rcases hdp with h | h
      · rw [crossDiffSliceWeightN_lo K M n s (by omega), zero_mul]
      · rw [crossDiffSliceWeightN_hi K M n s (by omega), zero_mul]
  rw [hsplit, Finset.sum_Ico_eq_sum_range]
  rw [show ((n + 1) + (s + 1) - (n + 1) : ℕ) = s + 1 from by omega]
  -- now both sums are over `range (s+1)`; reflect `q ↦ s−q` and match termwise.
  rw [← Finset.sum_range_reflect
      (fun q => crossDiffSliceWeightN K M n s ((n + 1) + q)
          * cbz ((Wsn : ℤ) + ((n + 1) + q : ℕ)) (μ + ((n : ℤ) + 2) + ((n + 1) + q : ℕ))) (s + 1)]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hps : p < s + 1 := Finset.mem_range.mp hp
  -- `q = s + 1 - 1 - p = s - p`.
  have hqval : (s + 1 - 1 - p : ℕ) = s - p := by omega
  rw [hqval]
  have hple : p ≤ s := by omega
  rw [crossDiffSliceWeightN_at K M n s (s - p) (by omega)]
  -- normalize all `(s−p)`-casts: the LHS sign uses `(↑s−↑p).toNat`, equal to the ℕ `s−p`.
  have hsp : ((s : ℤ) - (p : ℤ)).toNat = s - p := by omega
  have hspz : (((s - p : ℕ)) : ℤ) = (s : ℤ) - (p : ℤ) := by
    rw [Nat.cast_sub hple]
  -- the sign: `(-1)^((↑s−↑p).toNat) = (-1)^(s−p)`.
  rw [hsp]
  -- the four `cbz` factors, matched by `congr` + cast arithmetic.
  refine congr_arg₂ (· * ·) (congr_arg₂ (· * ·) (congr_arg₂ (· * ·) rfl ?_) ?_) ?_
  · -- `cbz (↑n+1+(↑s−↑p)) (↑s−↑p) = cbz (↑n+1+↑(s−p)) ↑(s−p)`.
    rw [hspz]
  · -- `cbz ↑M ↑p = cbz ↑M (↑s − ↑(s−p))`.
    rw [hspz]; congr 1; ring
  · -- the tower carrier: top `Wsn+(n+1+(s−p))`, lower `μ+(n+2)+(n+1+(s−p))`.
    rw [show ((((n + 1) + (s - p) : ℕ)) : ℤ) = ((n : ℤ) + 1) + ((s : ℤ) - (p : ℤ)) from by
          rw [Nat.cast_add, hspz]; push_cast; ring]
    congr 1
    · rw [hWsn]; push_cast; ring
    · push_cast; ring

/-! ## The grade-`(Ws−n)` `PresTowerFam` form of the pole-`(n+2)` cross slice. -/

/-- **The pole-`(n+2)` cross slice as a grade-`(Ws−n)` single-base `PresTowerFam`** in `w := c₍s₎a`
of SHIFTED grade `Ws−n`, depth `s+n+2`, weights `crossDiffSliceWeightN K M n s`.  Cross mirror of
`crossDiffSlice2_eq_PresTowerFam` (pole `2`, grade `Ws`): the slice IS a single-base tower, but at the
shifted grade `Ws−n` (the genuine `n`-offset).  Via `crossDiffSlice_eq_finsum`
(`ZhuVermaAnArchMUcircDiffCollapse`), `presAnmFamily_eq_finsum` (`ZhuVermaAnArchMUcircClose`), and the
cross scalar core `crossDiffSliceCoeffN_eq_tower`. -/
theorem crossDiffSliceN_eq_PresTowerFam (W : VertexOperatorAlgebra 𝒱) (n K M : ℕ) (a c d : 𝒱)
    (s : ℕ) (Wsn : ℕ) (hWsn : (Wsn : ℤ) = (M : ℤ) + (K : ℤ) - (s : ℤ) - 1 - (n : ℤ)) :
    crossDiffSlice W n K M a c d (n + 2) s
      = PresTowerFam W Wsn n (W.smul c (s : ℤ) a) 1 (s + n + 2)
          (fun _ => d) (fun _ => crossDiffSliceWeightN K M n s) := by
  set w := W.smul c (s : ℤ) a with hw
  rw [crossDiffSlice_eq_finsum W n K M a c d (n + 2) s]
  rw [PresTowerFam]
  rw [Finset.univ_unique, Finset.sum_singleton]
  rw [presAnmFamily_eq_finsum W Wsn n w d (crossDiffSliceWeightN K M n s) (s + n + 2)]
  refine finsum_congr fun μ => ?_
  -- normalize the pole cast inside `crossDiffSliceCoeff` (`(n+2 : ℕ)`), then apply the scalar core.
  rw [crossDiffSliceCoeffN_eq_tower K M n s Wsn hWsn μ]

/-! ## The conditional membership of the pole-`(n+2)` cross slice. -/

/-- **The pole-`(n+2)` cross slice lies in `Onm W n 0` when its left factor is grade `Ws−n`.**  The
slice is a grade-`(Ws−n)` single-base `PresTowerFam` in `c₍s₎a` (`crossDiffSliceN_eq_PresTowerFam`);
the keystone-backed `PresTowerFam_mem_Onm` (`ZhuVermaAnArchMUcrossHM`) carries it into `Onm W n 0`
**given the homogeneity** `c₍s₎a ∈ 𝒱_{Ws−n}` (the SHIFTED grade), supplied here as the explicit
hypothesis `hwmem` (NOT an axiom).  This isolates the precise remaining obstruction: the base `c₍s₎a`
is generically homogeneous of grade `Ws = M+K−s−1`, NOT `Ws−n`, so this hypothesis is the exact
`n`-offset gap closed by the cross-`s` convolution with the partner pole-`2` slice
(`crossDiffComm_eq_sliceSum`). -/
theorem crossDiffSliceN_mem_Onm_of_homog (W : VertexOperatorAlgebra 𝒱) (n K M : ℕ) (a c d : 𝒱)
    (s : ℕ) (Wsn : ℕ) (hWsn : (Wsn : ℤ) = (M : ℤ) + (K : ℤ) - (s : ℤ) - 1 - (n : ℤ))
    (hwmem : W.smul c (s : ℤ) a ∈ W.grading (Wsn : ℤ)) :
    crossDiffSlice W n K M a c d (n + 2) s ∈ Onm W n 0 := by
  rw [crossDiffSliceN_eq_PresTowerFam W n K M a c d s Wsn hWsn]
  exact PresTowerFam_mem_Onm W n hwmem 1 (s + n + 2) _ _

/-! ## The full `MUGradedAction W` assembly from the two precise pole-difference pieces. -/

/-- **The full `MUGradedAction W` assembly from the EXACT remaining pole-difference pieces.**  Given,
for every level `n`, the two engine-verified pole-difference membership identities — the pole-`(n+2)`
cross slice membership (`HPoleN`, whose cross scalar core / `PresTowerFam` form is FULLY proven above,
the remaining gap being the `n`-offset grade hypothesis of `crossDiffSliceN_mem_Onm_of_homog`) and the
`a`-outer right-action-difference family (`HARD`) — the Dong–Jiang `M(U)` graded-action crux
`MUGradedAction W` holds, via the proven `MUGradedAction_of_circDiffPieces`
(`ZhuVermaAnArchMUGradedClose`).  Re-export of that assembly with the pieces named at the cross-tower
level isolated here. -/
theorem MUGradedAction_of_crossTowerLift (W : VertexOperatorAlgebra 𝒱)
    (HARD : ∀ (n K : ℕ), ∀ a ∈ W.grading (K : ℤ), ∀ c d : 𝒱,
      anmRightDiff W n K a c d ∈ Onm W n 0)
    (HPoleN : ∀ (n K M : ℕ), ∀ a ∈ W.grading (K : ℤ), ∀ c ∈ W.grading (M : ℤ), ∀ d : 𝒱,
      ∀ s : ℕ, crossDiffSlice W n K M a c d (n + 2) s ∈ Onm W n 0) :
    MUGradedAction W :=
  MUGradedAction_of_circDiffPieces W HARD HPoleN

/-! ## Status — the cross scalar core (cross U-core/V-core) and the grade-`(Ws−n)` tower FULLY proven.

Proved here (`#print axioms` = `[propext, Classical.choice, Quot.sound]`; no `sorry`/
`axiom`/`pbw`):

* **`crossDiffSliceWeightN`** — the explicit cross-tower depth weights `(−1)^δ·C((n+1)+δ, δ)·C(M, s−δ)`
  (`δ = dp−(n+1)`, active window `n+1 ≤ dp ≤ n+1+s`); the `n`-offset of `crossDiffSliceWeight2`.
* **`crossDiffSliceCoeffN_eq_tower`** — **the cross U-core / V-core scalar identity FULLY proven**: the
  pole-`(n+2)` slice coefficient IS the grade-`(Ws−n)` `towerCoeffAnm` with the cross-tower weights
  (depth `s+n+2`).  Mirrors `crossDiffSliceCoeff2_eq_tower` at the shifted grade `Ws−n` / depth
  `n+1+δ`.  Engine-verified zero residual (`certificates/mathematica/poleN_towerlean.wl`).
* **`crossDiffSliceN_eq_PresTowerFam`** — the pole-`(n+2)` cross slice IS a grade-`(Ws−n)` single-base
  `PresTowerFam` in `c₍s₎a` (cross mirror of `crossDiffSlice2_eq_PresTowerFam`).
* **`crossDiffSliceN_mem_Onm_of_homog`** — the cross slice ∈ `Onm W n 0` GIVEN the SHIFTED-grade
  homogeneity `c₍s₎a ∈ 𝒱_{Ws−n}` (the exact `n`-offset gap, hypothesis NOT axiom).
* **`MUGradedAction_of_crossTowerLift`** — the full `MUGradedAction W` assembly from the two precise
  pole-difference pieces (`HARD`, `HPoleN`), via `MUGradedAction_of_circDiffPieces`.

**The PRECISE remaining identity (engine-verified TRUE, free boson; NOT faked):**

  `(HPoleN)   crossDiffSlice W n K M a c d (n+2) s ∈ Onm W n 0`    (homogeneous `a ∈ 𝒱_K`, `c ∈ 𝒱_M`).

Its coefficient is the cross scalar core `crossDiffSliceCoeffN_eq_tower` (proved, the grade-`(Ws−n)`
tower); the genuine CRUX is the `n`-offset: the base `c₍s₎a` is grade `Ws = M+K−s−1`, NOT `Ws−n`
(`crossCircComm_base_mem_grading`), so the SHIFTED-grade homogeneity hypothesis of
`crossDiffSliceN_mem_Onm_of_homog` does NOT hold individually for `n ≥ 1` (grade-`Ws` single-tower span
`False`, `certificates/mathematica/poleN_derive2.wl`).  The `n`-offset is absorbed only by the cross-`s`
convolution with the partner pole-`2` slice (`crossDiffComm_eq_sliceSum`:
`crossDiffComm = ∑_{s<N} (slice₂ − sliceₙ₊₂)`); the pole-`2` half is FULLY proven
(`crossDiffSlice2_mem_Onm`, grade `Ws`).  Discharging `(HPoleN)` and the `anmRightDiff` U-family
`(HARD)` feeds `MUGradedAction_of_crossTowerLift` ⟹ `MUGradedAction W`.
-/

end VOA

/-
`#print axioms` check (each of the following prints
`[propext, Classical.choice, Quot.sound]`, NO `pbw`, NO `sorryAx`):

  #print axioms VOA.crossDiffSliceCoeffN_eq_tower
  #print axioms VOA.crossDiffSliceN_eq_PresTowerFam
  #print axioms VOA.crossDiffSliceN_mem_Onm_of_homog
  #print axioms VOA.MUGradedAction_of_crossTowerLift
-/
