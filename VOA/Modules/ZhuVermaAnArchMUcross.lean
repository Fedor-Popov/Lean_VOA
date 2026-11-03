/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchAnmIdeal
import VOA.Modules.ZhuVermaAnArchRgen
import VOA.Modules.ZhuVermaAnArchMUcirc

/-!
# Dong–Jiang `A_{n,0}(𝒱)` **cross-level** closures — Game One (`MUGradedAction_of_gens`)

This file discharges the two `m = 0` **cross-level** generator families of the Dong–Jiang induced
module `M(U)` `V`-action well-definedness (`MUGradedAction_of_gens` in `ZhuVermaAnArchMU.lean`),
mirroring the proven `A_n(𝒱)` right-slot proofs (`leftProd_circ_right_mem_OnFull`, `hRgen_closed`)
lifted to the `A_{n,0}` setting:

* **(hcrossL)** `anmRight W n 0 a (anmLgen W 0 0 c) ∈ Onm W n 0` — the right slot is the *level-0*
  grading generator `anmLgen W 0 0 c = (L₋₁ + L₀)c` (the `O(𝒱) = O_{0,0}` `O^L` generator).
* **(hcrossCirc)** `anmRight W n 0 a (anmCirc W 0 0 c d) ∈ Onm W n 0` — the right slot is the
  *level-0* circle generator `anmCirc W 0 0 c d = resHom W 0 2 c d` (Zhu's `O`-generator).

Both are the `AnmCrossClosure W n` families (`AnmCrossClosure_of_gens`), the cross-level
well-definedness instance of `u_p` on `M(U)` (DJ Lemma 2.8 / lines 2087–2092).

## (hcrossL) — closed here (the right-slot grading-generator collapse)

At `m = 0`, `anmRight W n 0 a (·) = resHom W 0 (n+1) a (·)`.  For homogeneous `a ∈ 𝒱_K` the
second-slot `(L₋₁+L₀)c` expansion via `smul_Lgen_right` (`ZhuVermaAnArchRgen`) and a **shifted**
regrouping into the *level-`n`* grading generator `anmLgen W n 0 (a₍ₘ₎c)` (whose `L₀`-shift is
`−n`, not `0`) collapses the residual onto a single circle multiple:

  `resHom W 0 (n+1) a ((L₋₁+L₀)c) = [tower in OnmL W n 0] − (n+1) • anmCirc W n 0 a c`.

The per-mode scalar collapse is `crossL_abs_scalar`:
`(m+1+n−K)·C(K,m+n+1) + (m+n+2)·C(K,m+n+2) = 0`, which is exactly the lower absorption
`cbz_absorption K (m+n+2)` (`C(K,r)·r = C(K,r−1)·(K−r+1)`).  Engine-verified TRUE on the rank-1
free boson (`certificates/mathematica/mucross_check.wl`).

## (hcrossCirc) — reduced to ONE precise residue core (engine-verified, NOT faked)

`anmRight W n 0 a (anmCirc W 0 0 c d) = resHom W 0 (n+1) a (resHom W 0 2 c d)`.  This is the genuine
**cross-level residue-of-residue** core (the `m = 0`, mixed-level analogue of
`leftProd_circ_mem_On`/
`Pres_mem_On`); it is the inner-slot circle generator at level `0` (pole `2`) feeding the outer
level-`n` residue (pole `n+1`).  We record the bilinear reduction (`hcrossCirc` ⟸ the homogeneous
residue core `CrossCircCore`) and state the precise remaining identity; it is NOT an axiom/`sorry`.

## References
Dong–Jiang, Math. Z. 259 (2008) 799–826 (`math/0601626`), §2 (Lemma 2.8); Dong–Li–Mason,
J. Algebra 206 (1998) 67–96 (Lemma 2.2); Gannon §5.3.2, Thm 5.3.4.
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## Zero-slot helpers. -/

@[simp] theorem anmRight_zero_right' (W : VertexOperatorAlgebra 𝒱) (n m : ℕ) (a : 𝒱) :
    anmRight W n m a (0 : 𝒱) = 0 := by
  have h := anmRight_smul_right W n m (0 : ℂ) a (0 : 𝒱)
  rwa [zero_smul, zero_smul] at h

@[simp] theorem resHom_zero_left' (W : VertexOperatorAlgebra 𝒱) (s p : ℤ) (b : 𝒱) :
    resHom W s p (0 : 𝒱) b = 0 := by
  have h := resHom_smul_left W s p (0 : ℂ) (0 : 𝒱) b
  rwa [zero_smul, zero_smul] at h

/-! ## The per-mode cross-`L` absorption scalar (lower absorption). -/

/-- **The cross-level `m = 0` grading-generator per-mode scalar identity** (engine-verified):
`(m+1+n−K)·C(K,m+n+1) + (m+n+2)·C(K,m+n+2) = 0`, for `K n : ℕ`, `m : ℤ`.
Proof: lower absorption `cbz_absorption K (m+n+2)`:
`C(K,m+n+2)·(m+n+2) = C(K,m+n+1)·(K−(m+n+2)+1) = C(K,m+n+1)·(K−m−n−1)`,
i.e. `(m+n+2)·C(K,m+n+2) = −(m+1+n−K)·C(K,m+n+1)`. -/
theorem crossL_abs_scalar (K n : ℕ) (m : ℤ) :
    ((m : ℂ) + 1 + (n : ℂ) - (K : ℂ)) * cbz (K : ℤ) (m + n + 1)
        + ((m : ℂ) + n + 2) * cbz (K : ℤ) (m + n + 2) = 0 := by
  have ha := cbz_absorption K (m + n + 2)
  rw [show (m + (n : ℤ) + 2 - 1) = m + n + 1 from by ring] at ha
  push_cast at ha ⊢
  linear_combination ha

/-! ## Reindexing a `range`-indexed mode sum onto a common integer interval (local copy). -/

/-- Reindex `∑_{i ∈ range(P+1)} g i • T (i − s)` onto `Icc Lo Hi` (mode `m = i − s`).  Needs
`Icc (−s) (P−s) ⊆ Icc Lo Hi` and that `g (m+s)` vanishes on the extra modes.
(Local copy of `ZhuVermaAnArchAnmIdeal.reindexZeroToIcc`.) -/
private theorem reindexZeroToIcc' (P : ℕ) (s Lo Hi : ℤ) (g : ℤ → ℂ) (T : ℤ → 𝒱)
    (hsub : Finset.Icc (-s) ((P : ℤ) - s) ⊆ Finset.Icc Lo Hi)
    (hzero : ∀ mm ∈ Finset.Icc Lo Hi, mm ∉ Finset.Icc (-s) ((P : ℤ) - s) → g (mm + s) = 0) :
    ∑ i ∈ Finset.range (P + 1), g (i : ℤ) • T ((i : ℤ) - s)
      = ∑ mm ∈ Finset.Icc Lo Hi, g (mm + s) • T mm := by
  have h1 : ∑ i ∈ Finset.range (P + 1), g (i : ℤ) • T ((i : ℤ) - s)
      = ∑ mm ∈ Finset.Icc (-s) ((P : ℤ) - s), g (mm + s) • T mm := by
    refine Finset.sum_nbij' (i := fun i => (i : ℤ) - s) (j := fun mm => (mm + s).toNat)
      ?_ ?_ ?_ ?_ ?_
    · intro a ha; simp only [Finset.mem_range] at ha; simp only [Finset.mem_Icc]; omega
    · intro a ha; simp only [Finset.mem_Icc] at ha; simp only [Finset.mem_range]; omega
    · intro a ha; simp only [Finset.mem_range] at ha; simp only []
      rw [show ((a : ℤ) - s + s) = (a : ℤ) by ring, Int.toNat_natCast]
    · intro a ha; simp only [Finset.mem_Icc] at ha; simp only []
      rw [Int.toNat_of_nonneg (by omega)]; ring
    · intro a ha; simp only [Finset.mem_range] at ha; simp only []
      refine congr_arg₂ _ ?_ ?_
      · ring
      · ring
  rw [h1, ← Finset.sum_subset hsub]
  intro mm hm hmnot
  rw [hzero mm hm hmnot, zero_smul]

/-! ## (hcrossL) — the homogeneous tower / rest split.

For homogeneous `a ∈ 𝒱_K`, the second-slot `(L₋₁+L₀)c` expansion via `smul_Lgen_right_regroup`
(`ZhuVermaAnArchRgen`) at `m = 0` regroups each mode `a₍ₘ₎c` (slice `∈ 𝒱_{K+M−m−1}`) into the
*level-`n`* grading generator `anmLgen W n 0 (a₍ₘ₎c) = L₋₁(a₍ₘ₎c) + (K+M−m−1−n)·a₍ₘ₎c` plus a pure
mode residual.  We use `smul_Lgen_right` directly (the `M`-form) and split. -/

/-- The level-`n` grading-generator tower part of the `m = 0` `(L₋₁+L₀)` expansion: the residue sum
with each mode `a₍ₘ₎c` replaced by its level-`n` grading generator `anmLgen W n 0 (a₍ₘ₎c)`.  Each
summand lies in `OnmL W n 0 ⊆ Onm W n 0`. -/
noncomputable def crossLTower (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (K : ℕ) (a c : 𝒱) : 𝒱 :=
  ∑ i ∈ Finset.range ((K : ℤ).toNat + 1),
    cbz (K : ℤ) i • anmLgen W n 0 (W.smul a ((i : ℤ) - ((n : ℤ) + 1)) c)

/-- The pure-mode rest part of the `m = 0` `(L₋₁+L₀)` expansion (mode `m = i − n − 1`):
`(m+1+n−K)·a₍ₘ₎c + (m+1)·a₍ₘ₎c'`-style residual; here in the explicit per-`i` form. -/
noncomputable def crossLRest (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (K : ℕ) (a c : 𝒱) : 𝒱 :=
  ∑ i ∈ Finset.range ((K : ℤ).toNat + 1),
    cbz (K : ℤ) i •
      ((((i : ℤ) - ((n : ℤ) + 1)) + 1 + (n : ℤ) - (K : ℤ))
            • W.smul a ((i : ℤ) - ((n : ℤ) + 1)) c
        + (((i : ℤ) - ((n : ℤ) + 1)) : ℤ)
            • W.smul a ((i : ℤ) - ((n : ℤ) + 1) - 1) c)

/-- **Per-mode regroup at `m = 0`.**  For `a ∈ 𝒱_K`, `c ∈ 𝒱_M` and any mode `m`, the second-slot
`(L₋₁+L₀)c` rewrites as the level-`n` grading generator on the slice `a₍ₘ₎c` plus pure mode terms:
`a₍ₘ₎((L₋₁+L₀)c) = anmLgen W n 0 (a₍ₘ₎c) + (m+1+n−K)·a₍ₘ₎c + m·a₍ₘ₋₁₎c`. -/
theorem smul_Lgen_right_regroup_n0 (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {K M : ℤ} {a c : 𝒱}
    (ha : a ∈ W.grading K) (hc : c ∈ W.grading M) (m : ℤ) :
    W.smul a m (W.L (-1) c + W.L 0 c)
      = anmLgen W n 0 (W.smul a m c)
        + ((m : ℂ) + 1 + (n : ℂ) - K) • W.smul a m c + (m : ℂ) • W.smul a (m - 1) c := by
  rw [smul_Lgen_right W hc a m]
  -- a₍ₘ₎c ∈ 𝒱_{K+M-m-1}, so anmLgen W n 0 (a₍ₘ₎c) = L₋₁(a₍ₘ₎c) + (K+M-m-1-n)·a₍ₘ₎c
  have hmem : W.smul a m c ∈ W.grading (K + M - m - 1) := W.smul_mem_grading ha hc m
  rw [anmLgen, Nat.cast_zero, W.L_zero_grading _ hmem]
  push_cast
  module

/-- **Homogeneous split.**  For `a ∈ 𝒱_K`, `c ∈ 𝒱_M`,
`anmRight W n 0 a ((L₋₁+L₀)c) = crossLTower + crossLRest`. -/
theorem anmRight_zero_Lgen_right_homog (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {K M : ℕ}
    {a c : 𝒱} (ha : a ∈ W.grading (K : ℤ)) (hc : c ∈ W.grading (M : ℤ)) :
    anmRight W n 0 a (W.L (-1) c + W.L 0 c)
      = crossLTower W n K a c + crossLRest W n K a c := by
  rw [anmRight_zero, resHom_homogeneous W 0 ((n : ℤ) + 1) ha (W.L (-1) c + W.L 0 c)]
  simp only [add_zero]
  rw [crossLTower, crossLRest, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_Lgen_right_regroup_n0 W n ha hc ((i : ℤ) - ((n : ℤ) + 1)), ← smul_add]
  congr 1
  rw [← Int.cast_smul_eq_zsmul ℂ ((i : ℤ) - ((n : ℤ) + 1))]
  push_cast
  module

/-- **The tower part lands in `Onm W n 0`.**  Each inner summand is
`anmLgen W n 0 (a₍ₘ₎c) ∈ OnmL`. -/
theorem crossLTower_mem_Onm (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (K : ℕ) (a c : 𝒱) :
    crossLTower W n K a c ∈ Onm W n 0 := by
  rw [crossLTower]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
  exact anmLgen_mem_Onm W n 0 (W.smul a ((i : ℤ) - ((n : ℤ) + 1)) c)

/-! ## (hcrossL) — the rest part collapses to a single circle multiple.

The pure-mode residual `crossLRest` collapses onto `−(n+1) • anmCirc W n 0 a c`, via the per-mode
scalar identity `crossL_abs_scalar`.  We compute the two pieces on the common mode range
`Icc (−(n+2)) (K−1)` and apply the scalar collapse. -/

/-- The first (`(m+1+n−K)·a₍ₘ₎c`) summand of `crossLRest`, on the common mode range. -/
private theorem crossL0_term1 (W : VertexOperatorAlgebra 𝒱) (n K : ℕ) {a : 𝒱}
    (_ha : a ∈ W.grading (K : ℤ)) (c : 𝒱) :
    ∑ i ∈ Finset.range ((K : ℤ).toNat + 1),
        cbz (K : ℤ) i •
          ((((i : ℤ) - ((n : ℤ) + 1)) + 1 + (n : ℤ) - (K : ℤ))
            • W.smul a ((i : ℤ) - ((n : ℤ) + 1)) c)
      = ∑ mm ∈ Finset.Icc (-((n : ℤ) + 2)) ((K : ℤ) - 1),
          (((mm : ℤ) + 1 + (n : ℤ) - (K : ℤ)) * cbz (K : ℤ) ((mm : ℤ) + n + 1))
            • W.smul a mm c := by
  have hstep : ∀ i : ℕ,
      cbz (K : ℤ) i •
          ((((i : ℤ) - ((n : ℤ) + 1)) + 1 + (n : ℤ) - (K : ℤ))
            • W.smul a ((i : ℤ) - ((n : ℤ) + 1)) c)
        = (cbz (K : ℤ) i * (((i : ℤ) - ((n : ℤ) + 1)) + 1 + (n : ℤ) - (K : ℤ)))
            • W.smul a ((i : ℤ) - ((n : ℤ) + 1)) c := by
    intro i
    rw [← Int.cast_smul_eq_zsmul ℂ, smul_smul]
    push_cast
    ring_nf
  rw [Finset.sum_congr rfl (fun i _ => hstep i)]
  rw [reindexZeroToIcc' ((K : ℤ).toNat) ((n : ℤ) + 1)
      (-((n : ℤ) + 2)) ((K : ℤ) - 1)
      (fun i => cbz (K : ℤ) i * ((i - ((n : ℤ) + 1)) + 1 + (n : ℤ) - (K : ℤ)))
      (fun mm => W.smul a mm c)]
  · refine Finset.sum_congr rfl fun mm _ => ?_
    congr 1
    rw [show (mm + ((n : ℤ) + 1)) = mm + n + 1 by ring]
    push_cast; ring
  · rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ (K : ℤ) by positivity)]
    intro x hx; simp only [Finset.mem_Icc] at hx ⊢; omega
  · rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ (K : ℤ) by positivity)]
    intro mm hm hmnot
    simp only [Finset.mem_Icc] at hm hmnot
    have hnot : ¬ (-((n : ℤ) + 1) ≤ mm ∧ mm ≤ (K : ℤ) - ((n : ℤ) + 1)) := hmnot
    rcases lt_or_ge mm (-((n : ℤ) + 1)) with hlo | hge
    · rw [show (mm + ((n : ℤ) + 1)) = mm + n + 1 by ring, cbz_apply_neg _ (by omega), zero_mul]
    · have hub : (K : ℤ) - ((n : ℤ) + 1) < mm := by
        by_contra h; exact hnot ⟨hge, by omega⟩
      rw [show (mm + ((n : ℤ) + 1)) = mm + n + 1 by ring, cbz_lt (by positivity) (by omega),
        zero_mul]

/-- The second (`m·a₍ₘ₋₁₎c`) summand of `crossLRest`, on the common mode range (shift by 1). -/
private theorem crossL0_term2 (W : VertexOperatorAlgebra 𝒱) (n K : ℕ) {a : 𝒱}
    (_ha : a ∈ W.grading (K : ℤ)) (c : 𝒱) :
    ∑ i ∈ Finset.range ((K : ℤ).toNat + 1),
        cbz (K : ℤ) i •
          ((((i : ℤ) - ((n : ℤ) + 1)) : ℤ) • W.smul a ((i : ℤ) - ((n : ℤ) + 1) - 1) c)
      = ∑ mm ∈ Finset.Icc (-((n : ℤ) + 2)) ((K : ℤ) - 1),
          (((mm : ℤ) + 1) * cbz (K : ℤ) ((mm : ℤ) + n + 2)) • W.smul a mm c := by
  have hstep : ∀ i : ℕ,
      cbz (K : ℤ) i •
          ((((i : ℤ) - ((n : ℤ) + 1)) : ℤ) • W.smul a ((i : ℤ) - ((n : ℤ) + 1) - 1) c)
        = (cbz (K : ℤ) i * (((i : ℤ) - ((n : ℤ) + 1)) : ℤ))
            • W.smul a ((i : ℤ) - ((n : ℤ) + 2)) c := by
    intro i
    rw [← Int.cast_smul_eq_zsmul ℂ, smul_smul, show ((i : ℤ) - ((n : ℤ) + 1) - 1)
      = (i : ℤ) - ((n : ℤ) + 2) by ring]
  rw [Finset.sum_congr rfl (fun i _ => hstep i)]
  rw [reindexZeroToIcc' ((K : ℤ).toNat) ((n : ℤ) + 2)
      (-((n : ℤ) + 2)) ((K : ℤ) - 1)
      (fun i => cbz (K : ℤ) i * (((i : ℤ) - ((n : ℤ) + 1)) : ℤ))
      (fun mm => W.smul a mm c)]
  · refine Finset.sum_congr rfl fun mm _ => ?_
    congr 1
    rw [show (mm + ((n : ℤ) + 2)) = mm + n + 2 by ring]
    push_cast; ring
  · rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ (K : ℤ) by positivity)]
    intro x hx; simp only [Finset.mem_Icc] at hx ⊢; omega
  · rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ (K : ℤ) by positivity)]
    intro mm hm hmnot
    simp only [Finset.mem_Icc] at hm hmnot
    have hnot : ¬ (-((n : ℤ) + 2) ≤ mm ∧ mm ≤ (K : ℤ) - ((n : ℤ) + 2)) := hmnot
    rcases lt_or_ge mm (-((n : ℤ) + 2)) with hlo | hge
    · rw [show (mm + ((n : ℤ) + 2)) = mm + n + 2 by ring, cbz_apply_neg _ (by omega), zero_mul]
    · have hub : (K : ℤ) - ((n : ℤ) + 2) < mm := by
        by_contra h; exact hnot ⟨hge, by omega⟩
      rw [show (mm + ((n : ℤ) + 2)) = mm + n + 2 by ring, cbz_lt (by positivity) (by omega),
        zero_mul]

/-- The circle generator `anmCirc W n 0 a c = resHom W 0 (n+2) a c`, on the common mode range. -/
private theorem crossL0_circ (W : VertexOperatorAlgebra 𝒱) (n K : ℕ) {a : 𝒱}
    (ha : a ∈ W.grading (K : ℤ)) (c : 𝒱) :
    anmCirc W n 0 a c
      = ∑ mm ∈ Finset.Icc (-((n : ℤ) + 2)) ((K : ℤ) - 1),
          cbz (K : ℤ) ((mm : ℤ) + n + 2) • W.smul a mm c := by
  rw [anmCirc_zero, resHom_homogeneous W 0 ((n : ℤ) + 2) ha c]
  simp only [add_zero]
  rw [reindexZeroToIcc' ((K : ℤ).toNat) ((n : ℤ) + 2)
      (-((n : ℤ) + 2)) ((K : ℤ) - 1)
      (fun i => cbz (K : ℤ) i) (fun mm => W.smul a mm c)]
  · refine Finset.sum_congr rfl fun mm _ => ?_
    congr 2
    ring
  · rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ (K : ℤ) by positivity)]
    intro x hx; simp only [Finset.mem_Icc] at hx ⊢; omega
  · rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ (K : ℤ) by positivity)]
    intro mm hm hmnot
    simp only [Finset.mem_Icc] at hm hmnot
    have hnot : ¬ (-((n : ℤ) + 2) ≤ mm ∧ mm ≤ (K : ℤ) - ((n : ℤ) + 2)) := hmnot
    rcases lt_or_ge mm (-((n : ℤ) + 2)) with hlo | hge
    · rw [show ((mm : ℤ) + ((n : ℤ) + 2)) = mm + n + 2 by ring, cbz_apply_neg _ (by omega)]
    · have hub : (K : ℤ) - ((n : ℤ) + 2) < mm := by
        by_contra h; exact hnot ⟨hge, by omega⟩
      rw [show ((mm : ℤ) + ((n : ℤ) + 2)) = mm + n + 2 by ring, cbz_lt (by positivity) (by omega)]

/-- **The rest collapses to `−(n+1) • anmCirc`.**  For homogeneous `a ∈ 𝒱_K`,
`crossLRest W n K a c = (−(n+1)) • anmCirc W n 0 a c`, via the per-mode scalar
`crossL_abs_scalar`. -/
theorem crossLRest_eq (W : VertexOperatorAlgebra 𝒱) (n K : ℕ) {a : 𝒱}
    (ha : a ∈ W.grading (K : ℤ)) (c : 𝒱) :
    crossLRest W n K a c = (-((n : ℂ) + 1)) • anmCirc W n 0 a c := by
  rw [crossLRest]
  simp only [smul_add]
  rw [Finset.sum_add_distrib, crossL0_term1 W n K ha c, crossL0_term2 W n K ha c,
    crossL0_circ W n K ha c, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun mm _ => ?_
  rw [smul_smul, ← add_smul]
  congr 1
  have h := crossL_abs_scalar K n mm
  push_cast at h ⊢
  linear_combination h

/-! ## (hcrossL) — assembled. -/

/-- **(hcrossL), homogeneous.**  For `a ∈ 𝒱_K`, `c ∈ 𝒱_M`,
`anmRight W n 0 a ((L₋₁+L₀)c) ∈ Onm W n 0`. -/
theorem anmRight_zero_crossL_homog (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {K M : ℕ}
    {a c : 𝒱} (ha : a ∈ W.grading (K : ℤ)) (hc : c ∈ W.grading (M : ℤ)) :
    anmRight W n 0 a (W.L (-1) c + W.L 0 c) ∈ Onm W n 0 := by
  rw [anmRight_zero_Lgen_right_homog W n ha hc, crossLRest_eq W n K ha c]
  exact (Onm W n 0).add_mem (crossLTower_mem_Onm W n K a c)
    (Submodule.smul_mem _ _ (anmCirc_mem_Onm W n 0 a c))

/-- **(hcrossL).**  For arbitrary `a c : 𝒱`,
`anmRight W n 0 a (anmLgen W 0 0 c) ∈ Onm W n 0`.  Reduce both `a` and `c` to homogeneous slices
(`reduce_homogeneous`) and apply `anmRight_zero_crossL_homog`. -/
theorem anmRight_zero_crossL_mem_Onm (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (a c : 𝒱) :
    anmRight W n 0 a (anmLgen W 0 0 c) ∈ Onm W n 0 := by
  -- unfold the level-0 grading generator.
  have hgen : anmLgen W 0 0 c = W.L (-1) c + W.L 0 c := by
    simp only [anmLgen, Nat.cast_zero, sub_self, zero_smul, add_zero]
  rw [hgen]
  -- reduce `a` to homogeneous.
  refine reduce_homogeneous W
    (P := fun a => anmRight W n 0 a (W.L (-1) c + W.L 0 c) ∈ Onm W n 0) ?_ ?_ ?_ a
  · intro Ka a haK
    rcases le_or_gt 0 Ka with hKnn | hKneg
    · obtain ⟨K, rfl⟩ := Int.eq_ofNat_of_zero_le hKnn
      -- reduce `c` to homogeneous.
      refine reduce_homogeneous W
        (P := fun c => anmRight W n 0 a (W.L (-1) c + W.L 0 c) ∈ Onm W n 0) ?_ ?_ ?_ c
      · intro Mc c hcM
        rcases le_or_gt 0 Mc with hMnn | hMneg
        · obtain ⟨M, rfl⟩ := Int.eq_ofNat_of_zero_le hMnn
          exact anmRight_zero_crossL_homog W n haK hcM
        · -- `Mc < 0`: the grading is `⊥`, the piece is `0`.
          have hzero : c = 0 := by
            have : c ∈ (⊥ : Submodule ℂ 𝒱) := by rw [← W.positivity Mc hMneg]; exact hcM
            simpa using this
          rw [hzero, map_zero, map_zero, add_zero, anmRight_zero_right']
          exact (Onm W n 0).zero_mem
      · simp only [map_zero, add_zero, anmRight_zero_right']
        exact (Onm W n 0).zero_mem
      · intro x y hx hy
        rw [show W.L (-1) (x + y) + W.L 0 (x + y)
            = (W.L (-1) x + W.L 0 x) + (W.L (-1) y + W.L 0 y) from by simp only [map_add]; abel,
          anmRight_add_right]
        exact (Onm W n 0).add_mem hx hy
    · -- `Ka < 0`: the grading is `⊥`, the piece is `0`.
      have hzero : a = 0 := by
        have : a ∈ (⊥ : Submodule ℂ 𝒱) := by rw [← W.positivity Ka hKneg]; exact haK
        simpa using this
      rw [hzero, anmRight_zero_left']
      exact (Onm W n 0).zero_mem
  · simp only [anmRight_zero_left']
    exact (Onm W n 0).zero_mem
  · intro x y hx hy
    rw [anmRight_add_left]
    exact (Onm W n 0).add_mem hx hy

/-! ## (hcrossCirc) — reduction to the precise residue-of-residue core (NOT faked).

`anmRight W n 0 a (anmCirc W 0 0 c d) = resHom W 0 (n+1) a (resHom W 0 2 c d)`.  This is the
cross-level circle closure (the `m = 0`, mixed-level analogue of `leftProd_circ_mem_On`/
`Pres_mem_On`).  We record the bilinear reduction: by `reduce_homogeneous` in `a`, the membership
follows from the **homogeneous core** `CrossCircCore`, the precise remaining identity. -/

/-- **The precise (hcrossCirc) homogeneous residue-of-residue core.**  Stated as a `Prop`:
for homogeneous `a ∈ 𝒱_K` (`K : ℕ`) and any `c d : 𝒱`,
`resHom W 0 (n+1) a (resHom W 0 2 c d) ∈ Onm W n 0`, i.e.
`∑_{i≤K} C(K,i)·a₍i−n−1₎(∑_{j≤wt c} C(wt c, j)·c₍j−2₎d) ∈ Onm W n 0` (the cross-level circle
closure, engine-verified TRUE for `n = 1` on the rank-1 free boson, NOT an axiom). -/
def CrossCircCore (W : VertexOperatorAlgebra 𝒱) (n : ℕ) : Prop :=
  ∀ (K : ℕ) {a : 𝒱}, a ∈ W.grading (K : ℤ) → ∀ c d : 𝒱,
    resHom W 0 ((n : ℤ) + 1) a (resHom W 0 2 c d) ∈ Onm W n 0

/-- **(hcrossCirc), conditional on the residue core.**  Given `CrossCircCore W n`, the cross-level
circle closure `anmRight W n 0 a (anmCirc W 0 0 c d) ∈ Onm W n 0` holds for all `a c d : 𝒱`,
by reducing `a` to homogeneous slices (`reduce_homogeneous`). -/
theorem anmRight_zero_crossCirc_mem_Onm_of_core (W : VertexOperatorAlgebra 𝒱) (n : ℕ)
    (hcore : CrossCircCore W n) (a c d : 𝒱) :
    anmRight W n 0 a (anmCirc W 0 0 c d) ∈ Onm W n 0 := by
  rw [anmRight_zero, anmCirc_zero_zero]
  refine reduce_homogeneous W
    (P := fun a => resHom W 0 ((n : ℤ) + 1) a (resHom W 0 2 c d) ∈ Onm W n 0) ?_ ?_ ?_ a
  · intro Ka a haK
    rcases le_or_gt 0 Ka with hKnn | hKneg
    · obtain ⟨K, rfl⟩ := Int.eq_ofNat_of_zero_le hKnn
      exact hcore K haK c d
    · have hzero : a = 0 := by
        have : a ∈ (⊥ : Submodule ℂ 𝒱) := by rw [← W.positivity Ka hKneg]; exact haK
        simpa using this
      rw [hzero, resHom_zero_left']
      exact (Onm W n 0).zero_mem
  · simp only [resHom_zero_left']
    exact (Onm W n 0).zero_mem
  · intro x y hx hy
    rw [resHom_add_left]
    exact (Onm W n 0).add_mem hx hy

/-! ## Status — Game One cross families.

Proved here (`#print axioms` = `[propext, Classical.choice, Quot.sound]`; no `sorry`/
`axiom`/`pbw`):

* **(hcrossL) — closed outright.**  `anmRight_zero_crossL_mem_Onm`:
  `anmRight W n 0 a (anmLgen W 0 0 c) ∈ Onm W n 0`, for ALL `a c : 𝒱`.  Chain:
  `crossL_abs_scalar` (per-mode `cbz_absorption`), the homogeneous split
  `anmRight_zero_Lgen_right_homog` (`smul_Lgen_right_regroup_n0`), the tower-half discharge
  `crossLTower_mem_Onm`, and the rest collapse `crossLRest_eq` (`= −(n+1)•anmCirc`).
* **(hcrossCirc) — reduced to ONE precise core.**  `anmRight_zero_crossCirc_mem_Onm_of_core`
  reduces `anmRight W n 0 a (anmCirc W 0 0 c d) ∈ Onm W n 0` (all `a c d`) to the homogeneous
  residue-of-residue core `CrossCircCore W n`:
  `resHom W 0 (n+1) a (resHom W 0 2 c d) ∈ Onm W n 0` for homogeneous `a ∈ 𝒱_K`.

**Remaining core (engine-verified TRUE, free boson; NOT faked):** `CrossCircCore W n` — the
cross-level circle residue-of-residue membership.  This is the `m = 0`, mixed-level analogue of the
proven left-slot `leftProd_circ_mem_On` chain (`ZhuVermaAnDescent4`: `gen_jsum`/`gen_vandermonde`,
`Pres_mem_On`): the inner level-`0` circle (pole `2`) feeding the outer level-`n` residue (pole
`n+1`).  Discharging it closes (hcrossCirc) outright, and then
`MUGradedAction_of_gens W (hcirc …) (anmRight_zero_crossCirc_mem_Onm_of_core W · hcore …)
 (anmRight_zero_crossL_mem_Onm W)` supplies the full DJ `M(U)` `V`-action crux.
-/

end VOA
