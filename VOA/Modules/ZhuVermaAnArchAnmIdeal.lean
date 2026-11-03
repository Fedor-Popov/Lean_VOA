/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchAnm
import VOA.Modules.ZhuVermaAnArchABS

/-!
# Dong–Jiang `A_{n,m}(𝒱)` 2-sided bimodule — the `m = 0` grading-generator closure (DJ Lemma 2.8)

This file discharges the **`(L₋₁ + (L₀ − n))`-grading-generator** family of the Dong–Jiang Lemma 2.8
closures at `m = 0` (the case `M(U)` induces from, `math/0601626` §2), mirroring the proven
`A_n(𝒱)` absorption identity (`ZhuVermaAnArchABS.leftProd_Lgen_eq` / `leftProd_Lgen_mem_OnFull`).

## The `m = 0` absorption identity (ABS-analogue), engine-verified

At `m = 0` the Dong–Jiang right action is the single residue `u *^n_0 v = resHom W 0 (n+1) u v`
(`anmRight_zero`) and the circle generator is `u ∘^n_0 v = resHom W 0 (n+2) u v` (`anmCirc_zero`).
The grading generator is `(L₋₁ + (L₀ − n))u` (`anmLgen` at `m = 0`).  For homogeneous `u ∈ 𝒱_M` the
absorption collapses to a single **constant** scalar:

* `anmRight_zero_Lgen_eq` — `(L₋₁ u + (L₀ − n)u) *^n_0 v = (n + 1) • (u ∘^n_0 v)`.

The whole combinatorial content is the per-mode scalar identity (engine-verified symbolically and
numerically on `certificates/mathematica/heis_engine.wl`, free boson, and via `wolframscript` `FullSimplify`):

  `−(m+1)·C(M+1, m+n+2) + (M−n)·C(M, m+n+1) = (n+1)·C(M, m+n+2)`   (`anm_abs_scalar`)

which is **Pascal** (`cbz_pascal`) plus **lower absorption** (`cbz_absorption`).

## What is proved here (axiom-clean)

* `anm_abs_scalar` — the per-mode scalar collapse `(n+1)`.
* `anmRight_zero_Lgen_eq` — the homogeneous `m = 0` absorption identity (vector form).
* `anmRight_zero_Lgen_mem_Onm` — the general (non-homogeneous) `hL`-membership
  `(L₋₁ c + (L₀ − n)c) *^n_0 v ∈ O'_{n,0}(𝒱)`, i.e. the `hL` field of `AnmRightModule_of_gens`.
* `AnmRightModule_of_circ` — `AnmRightModule W n` reduced to its **single** remaining generator
  family `hcirc` (the circle-generator family), with `hL` discharged.

## What is OPEN (precise, NOT faked — see file end)

* `hcirc` for `AnmRightModule`: `(c ∘^n_0 d) *^n_0 v ∈ O'_{n,0}`, i.e.
  `resHom W 0 (n+1) (resHom W 0 (n+2) c d) v ∈ Onm W n 0` — the depth-`n` FZ residue-of-residue
  membership (the `m = 0` analogue of `Pres_mem_On`/`hLcirc_closed`).
* The cross closure `AnmCrossClosure W n` (`𝒱 *^n_0 O_{0,0} ⊆ O'_{n,0}`), both generator families.
* The bimodule composition `A_{p,n} ⊗_{A_n} A_{n,m} → A_{p,m}` for `M(U)`'s `V`-action.

## References
Dong–Jiang, Math. Z. 259 (2008) 799–826 (`math/0601626`), §2 (Lemma 2.8); Dong–Li–Mason,
J. Algebra 206 (1998) 67–96 (Lemma 2.2); Gannon §5.3.2, Thm 5.3.4.
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The per-mode `m = 0` absorption scalar (Pascal + lower absorption). -/

/-- **The `m = 0` ABS per-mode scalar identity** (engine-verified):
`−(m+1)·C(M+1, m+n+2) + (M−n)·C(M, m+n+1) = (n+1)·C(M, m+n+2)`, all `M n : ℕ`, `m : ℤ`.
Proof: Pascal `C(M+1,r) = C(M,r) + C(M,r−1)` (`cbz_pascal`) with `r = m+n+2`, then lower
absorption `C(M,r)·r = C(M,r−1)·(M−r+1)` (`cbz_absorption`) to clear the `r·C(M,r)` term. -/
theorem anm_abs_scalar (M n : ℕ) (m : ℤ) :
    -((m : ℂ) + 1) * cbz ((M : ℤ) + 1) (m + n + 2)
        + ((M : ℂ) - (n : ℂ)) * cbz (M : ℤ) (m + n + 1)
      = ((n : ℂ) + 1) * cbz (M : ℤ) (m + n + 2) := by
  -- Pascal on `cbz (M+1) (m+n+2)`.
  have hp := cbz_pascal ((M : ℤ) + 1) (m + n + 2)
  rw [show ((M : ℤ) + 1 - 1) = (M : ℤ) from by ring,
      show (m + (n : ℤ) + 2 - 1) = m + n + 1 from by ring] at hp
  -- Lower absorption with `i = m+n+2`:  cbz M (m+n+2)·(m+n+2) = cbz M (m+n+1)·(M-(m+n+2)+1).
  have ha := cbz_absorption M (m + n + 2)
  rw [show (m + (n : ℤ) + 2 - 1) = m + n + 1 from by ring] at ha
  -- now a pure ℂ-linear combination.
  rw [hp]
  push_cast at ha ⊢
  linear_combination -ha

/-! ## Reindexing a `range`-indexed mode sum onto a common integer interval (local copy). -/

/-- Reindex `∑_{i ∈ range(P+1)} g i • T (i − s)` onto `Icc Lo Hi` (mode `m = i − s`).  Needs
`Icc (−s) (P−s) ⊆ Icc Lo Hi` and that `g (m+s)` vanishes on the extra modes. -/
private theorem reindexZeroToIcc (P : ℕ) (s Lo Hi : ℤ) (g : ℤ → ℂ) (T : ℤ → 𝒱)
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

/-! ## The three `m = 0` pieces, on the common mode range `Icc (-(n+2)) (M-1)`. -/

/-- The `(L₋₁u)` summand of `resHom W 0 (n+1)`, on the common mode range.  After `smul_L_neg_one`,
`(L₋₁u)₍ₖ₎v = (−k)•u₍ₖ₋₁₎v`, so the coefficient of `u₍ₘ₎v` is `−(m+1)·C(M+1, m+n+2)`. -/
private theorem anm0_Lneg_piece (W : VertexOperatorAlgebra 𝒱) (n M : ℕ) {u : 𝒱}
    (_hu : u ∈ W.grading (M : ℤ)) (v : 𝒱) :
    ∑ i ∈ Finset.range (((M : ℤ) + 1).toNat + 1),
        cbz ((M : ℤ) + 1) i • W.smul (W.L (-1) u) ((i : ℤ) - ((n : ℤ) + 1)) v
      = ∑ mm ∈ Finset.Icc (-((n : ℤ) + 2)) ((M : ℤ) - 1),
          (-((mm : ℤ) + 1) * cbz ((M : ℤ) + 1) ((mm : ℤ) + n + 2)) • W.smul u mm v := by
  have hstep : ∀ i : ℕ,
      cbz ((M : ℤ) + 1) i • W.smul (W.L (-1) u) ((i : ℤ) - ((n : ℤ) + 1)) v
        = (cbz ((M : ℤ) + 1) i * (-((i : ℤ) - ((n : ℤ) + 1))))
            • W.smul u ((i : ℤ) - ((n : ℤ) + 1) - 1) v := by
    intro i
    rw [smul_L_neg_one, ← Int.cast_smul_eq_zsmul ℂ, smul_smul]
    congr 1
    push_cast; ring
  rw [Finset.sum_congr rfl (fun i _ => hstep i)]
  have hmode : ∀ i : ℤ, (i - ((n : ℤ) + 1) - 1) = i - ((n : ℤ) + 2) := by intro i; ring
  simp only [hmode]
  rw [reindexZeroToIcc (((M : ℤ) + 1).toNat) ((n : ℤ) + 2)
      (-((n : ℤ) + 2)) ((M : ℤ) - 1)
      (fun i => cbz ((M : ℤ) + 1) i * (-(i - ((n : ℤ) + 1))))
      (fun mm => W.smul u mm v)]
  · refine Finset.sum_congr rfl fun mm _ => ?_
    congr 1
    rw [show (mm + ((n : ℤ) + 2)) = mm + n + 2 by ring]
    push_cast; ring
  · rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ (M : ℤ) + 1 by positivity)]
    intro x hx; simp only [Finset.mem_Icc] at hx ⊢; omega
  · rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ (M : ℤ) + 1 by positivity)]
    intro mm hm hmnot
    simp only [Finset.mem_Icc] at hm hmnot
    have hnot : ¬ (-((n : ℤ) + 2) ≤ mm ∧ mm ≤ (M : ℤ) + 1 - ((n : ℤ) + 2)) := hmnot
    rcases lt_or_ge mm (-((n : ℤ) + 2)) with hlo | hge
    · rw [cbz_apply_neg _ (by omega), zero_mul]
    · have hub : (M : ℤ) + 1 - ((n : ℤ) + 2) < mm := by
        by_contra h; exact hnot ⟨hge, by omega⟩
      rw [cbz_lt (by positivity) (by omega), zero_mul]

/-- The `u` summand of `resHom W 0 (n+1)`, on the common mode range:
coefficient of `u₍ₘ₎v` is `C(M, m+n+1)`. -/
private theorem anm0_u_piece (W : VertexOperatorAlgebra 𝒱) (n M : ℕ) {u : 𝒱}
    (_hu : u ∈ W.grading (M : ℤ)) (v : 𝒱) :
    ∑ i ∈ Finset.range ((M : ℤ).toNat + 1),
        cbz (M : ℤ) i • W.smul u ((i : ℤ) - ((n : ℤ) + 1)) v
      = ∑ mm ∈ Finset.Icc (-((n : ℤ) + 2)) ((M : ℤ) - 1),
          cbz (M : ℤ) ((mm : ℤ) + n + 1) • W.smul u mm v := by
  rw [reindexZeroToIcc ((M : ℤ).toNat) ((n : ℤ) + 1)
      (-((n : ℤ) + 2)) ((M : ℤ) - 1)
      (fun i => cbz (M : ℤ) i) (fun mm => W.smul u mm v)]
  · refine Finset.sum_congr rfl fun mm _ => ?_
    congr 2
    ring
  · rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ (M : ℤ) by positivity)]
    intro x hx; simp only [Finset.mem_Icc] at hx ⊢; omega
  · rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ (M : ℤ) by positivity)]
    intro mm hm hmnot
    simp only [Finset.mem_Icc] at hm hmnot
    have hnot : ¬ (-((n : ℤ) + 1) ≤ mm ∧ mm ≤ (M : ℤ) - ((n : ℤ) + 1)) := hmnot
    rcases lt_or_ge mm (-((n : ℤ) + 1)) with hlo | hge
    · rw [show ((mm : ℤ) + ((n : ℤ) + 1)) = mm + n + 1 by ring, cbz_apply_neg _ (by omega)]
    · have hub : (M : ℤ) - ((n : ℤ) + 1) < mm := by
        by_contra h; exact hnot ⟨hge, by omega⟩
      rw [show ((mm : ℤ) + ((n : ℤ) + 1)) = mm + n + 1 by ring, cbz_lt (by positivity) (by omega)]

/-- The circle generator `resHom W 0 (n+2) u v = anmCirc W n 0 u v`, on the common mode range:
coefficient of `u₍ₘ₎v` is `C(M, m+n+2)`. -/
private theorem anm0_circ_piece (W : VertexOperatorAlgebra 𝒱) (n M : ℕ) {u : 𝒱}
    (hu : u ∈ W.grading (M : ℤ)) (v : 𝒱) :
    anmCirc W n 0 u v
      = ∑ mm ∈ Finset.Icc (-((n : ℤ) + 2)) ((M : ℤ) - 1),
          cbz (M : ℤ) ((mm : ℤ) + n + 2) • W.smul u mm v := by
  rw [anmCirc_zero, resHom_homogeneous W 0 ((n : ℤ) + 2) hu v]
  simp only [add_zero]
  rw [reindexZeroToIcc ((M : ℤ).toNat) ((n : ℤ) + 2)
      (-((n : ℤ) + 2)) ((M : ℤ) - 1)
      (fun i => cbz (M : ℤ) i) (fun mm => W.smul u mm v)]
  · refine Finset.sum_congr rfl fun mm _ => ?_
    congr 2
    ring
  · rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ (M : ℤ) by positivity)]
    intro x hx; simp only [Finset.mem_Icc] at hx ⊢; omega
  · rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ (M : ℤ) by positivity)]
    intro mm hm hmnot
    simp only [Finset.mem_Icc] at hm hmnot
    have hnot : ¬ (-((n : ℤ) + 2) ≤ mm ∧ mm ≤ (M : ℤ) - ((n : ℤ) + 2)) := hmnot
    rcases lt_or_ge mm (-((n : ℤ) + 2)) with hlo | hge
    · rw [show ((mm : ℤ) + ((n : ℤ) + 2)) = mm + n + 2 by ring, cbz_apply_neg _ (by omega)]
    · have hub : (M : ℤ) - ((n : ℤ) + 2) < mm := by
        by_contra h; exact hnot ⟨hge, by omega⟩
      rw [show ((mm : ℤ) + ((n : ℤ) + 2)) = mm + n + 2 by ring, cbz_lt (by positivity) (by omega)]

/-! ## The `m = 0` absorption identity (ABS-analogue), homogeneous and general. -/

/-- **(`m = 0` ABS) — the Dong–Jiang absorption identity at `m = 0`, vector form.**  For homogeneous
`u ∈ 𝒱_M`, `(L₋₁ u + (L₀ − n)u) *^n_0 v = (n + 1) • (u ∘^n_0 v)`.  Mirrors
`ZhuVermaAnArchABS.leftProd_Lgen_eq`; the per-mode collapse is `anm_abs_scalar`. -/
theorem anmRight_zero_Lgen_eq (W : VertexOperatorAlgebra 𝒱) (n M : ℕ) {u : 𝒱}
    (hu : u ∈ W.grading (M : ℤ)) (v : 𝒱) :
    anmRight W n 0 (W.L (-1) u + W.L 0 u + ((0 : ℂ) - (n : ℂ)) • u) v
      = ((n : ℂ) + 1) • anmCirc W n 0 u v := by
  have hLmem : W.L (-1) u ∈ W.grading ((M : ℤ) + 1) := L_neg_one_mem_grading_succ W hu
  -- collapse `*^n_0 = resHom 0 (n+1)`, split the left slot, and substitute `L₀u = M•u`.
  rw [anmRight_zero, resHom_add_left, resHom_add_left, L_zero_grading W u hu,
      resHom_smul_left, resHom_smul_left,
      show (((M : ℤ) : ℂ)) = (M : ℂ) from by push_cast; ring]
  -- the `(L₋₁u)` summand, homogeneous → Icc form.
  have hLfull : resHom W 0 ((n : ℤ) + 1) (W.L (-1) u) v
      = ∑ mm ∈ Finset.Icc (-((n : ℤ) + 2)) ((M : ℤ) - 1),
          (-((mm : ℤ) + 1) * cbz ((M : ℤ) + 1) ((mm : ℤ) + n + 2)) • W.smul u mm v := by
    rw [resHom_homogeneous W 0 ((n : ℤ) + 1) hLmem v]
    simp only [add_zero]
    rw [show (((M : ℤ) + 1).toNat) = ((M : ℤ) + 1).toNat from rfl]
    exact anm0_Lneg_piece W n M hu v
  -- the `u` summand, homogeneous → Icc form.
  have hUfull : resHom W 0 ((n : ℤ) + 1) u v
      = ∑ mm ∈ Finset.Icc (-((n : ℤ) + 2)) ((M : ℤ) - 1),
          cbz (M : ℤ) ((mm : ℤ) + n + 1) • W.smul u mm v := by
    rw [resHom_homogeneous W 0 ((n : ℤ) + 1) hu v]
    simp only [add_zero]
    exact anm0_u_piece W n M hu v
  rw [hLfull, hUfull, anm0_circ_piece W n M hu v]
  -- push all the leading scalars into the Icc-sums, combine, apply the per-mode scalar identity.
  simp only [Finset.smul_sum, smul_smul]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun mm _ => ?_
  rw [← add_smul, ← add_smul]
  congr 1
  have h := anm_abs_scalar M n mm
  push_cast at h ⊢
  linear_combination h

/-- `resHom` is additive over a finite sum in its (decomposed) left slot. -/
private theorem resHom_sum_left (W : VertexOperatorAlgebra 𝒱) (s p : ℤ) {ι : Type*}
    (t : Finset ι) (f : ι → 𝒱) (b : 𝒱) :
    resHom W s p (∑ k ∈ t, f k) b = ∑ k ∈ t, resHom W s p (f k) b := by
  classical
  induction t using Finset.induction with
  | empty =>
    simp only [Finset.sum_empty]
    have h0 : resHom W s p ((0 : ℂ) • (0 : 𝒱)) b = (0 : ℂ) • resHom W s p (0 : 𝒱) b :=
      resHom_smul_left W s p 0 0 b
    simpa using h0
  | insert k r hkr ih =>
    rw [Finset.sum_insert hkr, Finset.sum_insert hkr, resHom_add_left, ih]

/-- **`hL` — the `m = 0` grading-generator membership.**  For arbitrary `c v : 𝒱`,
`(L₋₁ c + (L₀ − n)c) *^n_0 v ∈ O'_{n,0}(𝒱)`.  Decompose `c` into homogeneous pieces and apply
`anmRight_zero_Lgen_eq` to each: every piece becomes `(n+1) • (cₖ ∘^n_0 v)`, a circle generator of
`Onm W n 0`.  This is the `hL` field of `AnmRightModule_of_gens`. -/
theorem anmRight_zero_Lgen_mem_Onm (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (c v : 𝒱) :
    anmRight W n 0 (anmLgen W n 0 c) v ∈ Onm W n 0 := by
  classical
  letI := DirectSum.IsInternal.chooseDecomposition W.grading W.isInternal
  -- unfold the grading generator at `m = 0`.
  have hgen : anmLgen W n 0 c = W.L (-1) c + W.L 0 c + ((0 : ℂ) - (n : ℂ)) • c := by
    simp only [anmLgen, Nat.cast_zero]
  rw [hgen]
  -- decompose `c = ∑_{k ∈ support} cₖ`.
  set s := (DirectSum.decompose W.grading c).support with hs
  have hdecomp : ∑ k ∈ s, ((DirectSum.decompose W.grading c k : W.grading k) : 𝒱) = c :=
    DirectSum.sum_support_decompose W.grading c
  -- rewrite the whole generator as a sum over the homogeneous pieces.
  have hsplit : W.L (-1) c + W.L 0 c + ((0 : ℂ) - (n : ℂ)) • c
      = ∑ k ∈ s, (W.L (-1) ((DirectSum.decompose W.grading c k : W.grading k) : 𝒱)
          + W.L 0 ((DirectSum.decompose W.grading c k : W.grading k) : 𝒱)
          + ((0 : ℂ) - (n : ℂ)) • ((DirectSum.decompose W.grading c k : W.grading k) : 𝒱)) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← map_sum, ← map_sum, ← Finset.smul_sum]
    simp only [hdecomp]
  rw [hsplit, anmRight_zero, resHom_sum_left]
  refine Submodule.sum_mem _ fun k _ => ?_
  have hk : ((DirectSum.decompose W.grading c k : W.grading k) : 𝒱) ∈ W.grading k :=
    (DirectSum.decompose W.grading c k).2
  rcases le_or_gt 0 k with hknn | hkneg
  · obtain ⟨M, rfl⟩ := Int.eq_ofNat_of_zero_le hknn
    -- `anmRight = resHom 0 (n+1)`; rewrite back to `anmRight` and apply the absorption identity.
    rw [← anmRight_zero, anmRight_zero_Lgen_eq W n M hk v]
    exact Submodule.smul_mem _ _ (anmCirc_mem_Onm W n 0 _ v)
  · -- `k < 0`: the grading is `⊥`, the piece is `0`, the product is `0`.
    have hzero : ((DirectSum.decompose W.grading c k : W.grading k) : 𝒱) = 0 := by
      have : ((DirectSum.decompose W.grading c k : W.grading k) : 𝒱) ∈ (⊥ : Submodule ℂ 𝒱) := by
        rw [← W.positivity k hkneg]; exact hk
      simpa using this
    rw [hzero, map_zero, map_zero, smul_zero, add_zero, add_zero,
        show (0 : 𝒱) = (0 : ℂ) • (0 : 𝒱) by simp, ← anmRight_zero,
        anmRight_smul_left, zero_smul]
    exact (Onm W n 0).zero_mem

/-! ## The `M(U)` right-module closure reduced to its single remaining `hcirc` family. -/

/-- **DJ Lemma 2.8 right-module closure, `hL`-discharged.**  `AnmRightModule W n`
(`O'_{n,0} *^n_0 𝒱 ⊆ O'_{n,0}`) reduced to its **single** remaining generator family `hcirc`:
the right action of a circle generator `c ∘^n_0 d` lands in `O'_{n,0}`.  The grading-generator
family is discharged unconditionally by `anmRight_zero_Lgen_mem_Onm` (the `m = 0` absorption
identity).  This isolates the genuine remaining FZ residue-of-residue content. -/
theorem AnmRightModule_of_circ (W : VertexOperatorAlgebra 𝒱) (n : ℕ)
    (hcirc : ∀ c d v : 𝒱, anmRight W n 0 (anmCirc W n 0 c d) v ∈ Onm W n 0) :
    AnmRightModule W n :=
  AnmRightModule_of_gens W n hcirc (fun c v => anmRight_zero_Lgen_mem_Onm W n c v)

/-! ## The precise OPEN Dong–Jiang Lemma 2.8 target (the `M(U)` `V`-action, NOT faked).

The grading-generator family of `AnmRightModule W n` is closed unconditionally
(`anmRight_zero_Lgen_mem_Onm`).  The remaining `m = 0` closures are:

* `hcirc` for `AnmRightModule`:  `(c ∘^n_0 d) *^n_0 v ∈ O'_{n,0}`, i.e.
  `resHom W 0 (n+1) (resHom W 0 (n+2) c d) v ∈ Onm W n 0` — the depth-`n` FZ residue-of-residue
  membership (the `m = 0`, shift-`0` analogue of `Pres_mem_On`/`hLcirc_closed`).
* `AnmCrossClosure W n` (`𝒱 *^n_0 O_{0,0} ⊆ O'_{n,0}`), both generator families
  (`AnmCrossClosure_of_gens`): the right slot carries an `O(𝒱)` generator into `O'_{n,0}`.
* The bimodule composition `A_{p,n}(𝒱) ⊗_{A_n(𝒱)} A_{n,m}(𝒱) → A_{p,m}(𝒱)` for `M(U)`'s `V`-action
  (DJ Thm 2.9 / Gannon Thm 5.3.4).

All are engine-verified TRUE (`n = 1`, free boson, `certificates/mathematica/heis_engine.wl`); none is an axiom or `sorry`. -/

end VOA
