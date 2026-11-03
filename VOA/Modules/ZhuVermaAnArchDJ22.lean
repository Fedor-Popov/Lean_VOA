/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchAnmFull
import VOA.Modules.ZhuVermaAnArchABS
import VOA.Modules.ZhuMuIdentity

/-!
# Dong–Jiang **Lemma 2.2** — the grading-generator absorption into the left bar product `∗̄^n_m`

This file proves, **following Dong–Jiang's published argument verbatim** (Dong–Jiang, *Bimodules
associated to vertex operator algebras*, Math. Z. 259 (2008) 799–826, `math/0601626`, p. 3,
lines 171–254):

> **Lemma 2.2.** For any `u, v ∈ V`, `u ∘^n_m v` lies in `O_n(V) ∗̄^n_m V`.

The content of the lemma is the **absorption identity** (DJ display, p. 3): for homogeneous
`u ∈ 𝒱_M`,
```
  (L(-1)u + L(0)u) ∗̄^n_m v = (n+m+1)·(-1)^n·C(n+m,m) · (u ∘^n_m v).
```
Since `L(-1)u + L(0)u ∈ O_n(V)` (the unshifted Dong–Li–Mason grading generator, `OnL`), this
exhibits the circle product `u ∘^n_m v` (up to the nonzero scalar `(n+m+1)·(-1)^n·C(n+m,m)`) as an
element of `O_n(V) ∗̄^n_m V`, which is exactly DJ Lemma 2.2.

## The proof (DJ verbatim, formalized)

Dong–Jiang compute `(L(-1)u) ∗̄^n_m v` as `∑_i (-1)^i C(m+i,i) Res_z (1+z)^{wt u + 1 + m}/z^{m+i+1}
(d/dz) Y(u,z)v`, integrate by parts in `z`, add `(L(0)u) ∗̄^n_m v`, and telescope the alternating
`i`-sum down to a single residue `(n+m+1)(-1)^n C(n+m,m) Res_z (1+z)^{wt u + m}/z^{n+m+2} Y(u,z)v`.

This is **exactly the structure of the already-proven Dong–Li–Mason absorption identity**
`leftProd_Lgen_eq` (`ZhuVermaAnArchABS.lean`), which does the **diagonal** `m = n` case (there the
bar product `∗̄^n_n` coincides with `leftProd W n = *^n_n`).  We generalize the shift `n` to `m`:

* `dj22_ibp_coeff` — the integration-by-parts per-pole coefficient identity (DJ "integration by
  parts in `z`"), the `m`-shift analogue of `abs_ibp_coeff`; reduces to `cbz_pascal_up`
  + `cbz_absorption`.
* `dj22_scalar` — the per-mode alternating-`i`-sum collapse (DJ "telescopes"), the `m`-shift
  analogue of `abs_scalar`; the telescoping sum `∑_i (D i − D (i+1)) = −D (n+1)` is closed by
  `cbz_upper_shift`, and the final coefficient `(n+1)·C(m+n+1,n+1) = (n+m+1)·C(n+m,m)` is again
  `cbz_upper_shift`.
* `Lneg_piece_bar` / `u_piece_bar` / `circ_piece_bar` — the three `Finset` reindexings onto the
  common integer mode interval `Icc (-(n+m+2)) (M-1)`, the `m`-shift analogues of
  `Lneg_piece`/`u_piece`/`circ_piece`, all via a copy of the `ZhuVermaAnArchABS` reindexing tool.

The headline `anmCirc_mem_OnBar` then matches the requested repo signature.

## What is proved here (axiom-clean)

* `anmCircBar_eq` — the homogeneous absorption identity (DJ Lemma 2.2's display):
  `(L(-1)u+L(0)u) ∗̄^n_m v = (n+m+1)(-1)^n C(n+m,m) • (u ∘^n_m v)` for homogeneous `u`.
* `anmCirc_mem_OnBar` — the requested signature (scalar • circle = bar-product of the grading
  generator), homogeneous.
* `anmGenBar_Lgen_mem_OnmFull` — the general (non-homogeneous) membership
  `(L(-1)c+L(0)c) ∗̄^n_m b ∈ O_{n,m}(𝒱)` (the DJ Lemma 2.2 conclusion, into the full ideal): every
  homogeneous piece is `scalar • (c_k ∘^n_m b) ∈ O'_{n,m} ⊆ O_{n,m}`.

## References
Dong–Jiang, Math. Z. 259 (2008) 799–826 (`math/0601626`), §2 Lemma 2.2; Dong–Li–Mason, J. Algebra
206 (1998) 67–96.
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The scalar combinatorics (DJ "integration by parts" + "telescopes"). -/

/-- **DJ Lemma 2.2 integration-by-parts coefficient (`m`-shift).**  The per-pole coefficient of the
`(L₋₁u)` summand plus the `(L₀u = M·u)` summand, after integration by parts in `z`, equals the
two-pole reorganized form.  This is the `m`-shift analogue of `abs_ibp_coeff`: reduce via
`cbz_pascal_up` on `C(M+1+m, ·)` and `cbz_absorption` on `C(M+m, ·)`. -/
theorem dj22_ibp_coeff (M m i : ℕ) (μ : ℤ) :
    -((μ : ℂ) + 1) * cbz ((M : ℤ) + 1 + m) (μ + m + i + 2)
        + (M : ℂ) * cbz ((M : ℤ) + m) (μ + m + i + 1)
      = (i : ℂ) * cbz ((M : ℤ) + m) (μ + m + i + 1)
        + ((m : ℂ) + i + 1) * cbz ((M : ℤ) + m) (μ + m + i + 2) := by
  have hp : cbz ((M : ℤ) + 1 + m) (μ + m + i + 2)
      = cbz ((M : ℤ) + m) (μ + m + i + 2) + cbz ((M : ℤ) + m) (μ + m + i + 1) := by
    have h := cbz_pascal_up ((M : ℤ) + m) (μ + m + i + 2)
    rw [show ((M : ℤ) + m + 1) = (M : ℤ) + 1 + m from by ring,
        show (μ + m + i + 2 - 1) = μ + m + i + 1 from by ring] at h
    exact h
  have ha : cbz ((M : ℤ) + m) (μ + m + i + 2) * (μ + (m : ℂ) + i + 2)
      = cbz ((M : ℤ) + m) (μ + m + i + 1) * ((M : ℂ) - μ - i - 1) := by
    have h := cbz_absorption (M + m) (μ + m + i + 2)
    rw [show (((M + m : ℕ) : ℤ)) = (M : ℤ) + m from by push_cast; ring,
        show (μ + (m : ℤ) + i + 2 - 1) = μ + m + i + 1 from by ring] at h
    push_cast at h
    linear_combination h
  linear_combination (norm := (push_cast; ring1)) (-((μ : ℂ) + 1)) * hp - ha

/-- **DJ Lemma 2.2 per-mode scalar collapse (`m`-shift).**  The full alternating `i`-sum coefficient
of `u₍μ₎v` in `(L₋₁u+L₀u) ∗̄^n_m v` collapses to that of `(n+m+1)(-1)^n C(n+m,m)•(u ∘^n_m v)`.

Proof (DJ "telescopes"): rewrite the per-`i` bracket via `dj22_ibp_coeff` (integration by parts),
then telescope with `D i := (-1)^i · i · C(m+i,i) · C(M+m, μ+m+i+1)`: each summand is
`D i − D (i+1)` by `cbz_upper_shift`, so the sum is `D 0 − D (n+1) = −D (n+1)`, and the final
coefficient `(n+1)C(m+n+1,n+1) = (n+m+1)C(n+m,m)` (again `cbz_upper_shift`) gives the result.  This
is the entire combinatorial content of DJ Lemma 2.2. -/
theorem dj22_scalar (M n m : ℕ) (μ : ℤ) :
    (∑ i ∈ Finset.range (n + 1), (-1 : ℂ) ^ i * cbz ((m : ℤ) + i) i *
        (-((μ : ℂ) + 1) * cbz ((M : ℤ) + 1 + m) (μ + m + i + 2)
          + (M : ℂ) * cbz ((M : ℤ) + m) (μ + m + i + 1)))
      = ((n : ℂ) + m + 1) * (-1 : ℂ) ^ n * cbz ((n : ℤ) + m) m
          * cbz ((M : ℤ) + m) (μ + n + m + 2) := by
  set D : ℕ → ℂ := fun i =>
    (-1 : ℂ) ^ i * (i : ℂ) * cbz ((m : ℤ) + i) i * cbz ((M : ℤ) + m) (μ + m + i + 1) with hD
  -- The single per-`i` `cbz` relation `(m+i+1)·C(m+i,i) = (i+1)·C(m+(i+1),i+1)` (`rel1`), obtained
  -- from `cbz_upper_shift (i+1) m` plus `cbz_symm` on both binomials.
  -- The single per-`i` `cbz` relation `(m+i+1)·C(m+i,i) = (i+1)·C(m+i+1,i+1)`, obtained from
  -- `cbz_upper_shift (i+1) m` plus `cbz_symm` on both binomials.  Stated entirely with `ℤ`-shifted
  -- integer binomial arguments so it lines up with the unfolded `D (i+1)`.
  have hrel : ∀ i : ℕ,
      ((m : ℤ) + i + 1) * cbz ((m : ℤ) + i) i
        = ((i : ℤ) + 1) * cbz ((m : ℤ) + ((i : ℤ) + 1)) ((i : ℤ) + 1) := by
    intro i
    have hsh := cbz_upper_shift (i + 1) m
    rw [show (((i + 1 : ℕ) : ℤ)) = (i : ℤ) + 1 from by push_cast; ring] at hsh
    rw [show ((i : ℤ) + 1 + m - 1) = (i : ℤ) + m from by ring] at hsh
    -- `cbz_upper_shift (i+1) m`: `(i+1)·C((i+1)+m, m) = ((i+1)+m)·C(i+m, m)`.
    -- `C((i+1)+m, m) = C((i+1)+m, i+1) = C(m+(i+1), i+1)` and `C(i+m, m) = C(i+m, i) = C(m+i, i)`.
    have hs1 : cbz ((i : ℤ) + 1 + m) m = cbz ((m : ℤ) + ((i : ℤ) + 1)) ((i : ℤ) + 1) := by
      have := ZhuMu.cbz_symm (i + 1 + m) (m : ℤ)
      rw [show (((i + 1 + m : ℕ) : ℤ)) = (i : ℤ) + 1 + m from by push_cast; ring,
          show (((i : ℤ) + 1 + m) - m) = (i : ℤ) + 1 from by ring] at this
      rw [this, show ((i : ℤ) + 1 + m) = (m : ℤ) + ((i : ℤ) + 1) from by ring]
    have hs2 : cbz ((i : ℤ) + m) m = cbz ((m : ℤ) + i) i := by
      have := ZhuMu.cbz_symm (i + m) (m : ℤ)
      rw [show (((i + m : ℕ) : ℤ)) = (i : ℤ) + m from by push_cast; ring,
          show (((i : ℤ) + m) - m) = (i : ℤ) from by ring] at this
      rw [this, show ((i : ℤ) + m) = (m : ℤ) + i from by ring]
    rw [← hs1, ← hs2]
    linear_combination (norm := (push_cast; ring1)) (-hsh)
  have hterm : ∀ i ∈ Finset.range (n + 1),
      (-1 : ℂ) ^ i * cbz ((m : ℤ) + i) i *
        (-((μ : ℂ) + 1) * cbz ((M : ℤ) + 1 + m) (μ + m + i + 2)
          + (M : ℂ) * cbz ((M : ℤ) + m) (μ + m + i + 1)) = D i - D (i + 1) := by
    intro i _
    rw [dj22_ibp_coeff M m i μ]
    have hr := hrel i
    simp only [hD, Nat.cast_add, Nat.cast_one, pow_succ]
    rw [show (μ + m + ((i : ℤ) + 1) + 1) = μ + m + i + 2 from by ring]
    linear_combination (norm := (push_cast; ring1))
      ((-1 : ℂ) ^ i * cbz ((M : ℤ) + m) (μ + m + i + 2)) * hr
  rw [Finset.sum_congr rfl hterm, Finset.sum_range_sub' D (n + 1)]
  -- `D 0 = 0` (factor `i`), so the telescope is `−D (n+1)`; close the final coefficient.
  -- Final: `−D (n+1) = (-1)^n·(n+1)·C(m+(n+1),n+1)·C(M+m,μ+n+m+2)` and
  -- `(n+1)·C(m+(n+1),n+1) = (n+m+1)·C(m+n,n) = (n+m+1)·C(n+m,m)`.
  have hr := hrel n
  have hsymF : cbz ((m : ℤ) + n) n = cbz ((n : ℤ) + m) m := by
    have := ZhuMu.cbz_symm (m + n) (n : ℤ)
    rw [show (((m + n : ℕ) : ℤ)) = (m : ℤ) + n from by push_cast; ring,
        show (((m : ℤ) + n) - n) = (m : ℤ) from by ring] at this
    rw [this, show ((n : ℤ) + m) = (m : ℤ) + n from by ring]
  simp only [hD, Nat.cast_add, Nat.cast_one, pow_succ]
  rw [show (μ + m + ((n : ℤ) + 1) + 1) = μ + n + m + 2 from by ring, ← hsymF]
  linear_combination (norm := (push_cast; ring1))
    (-((-1 : ℂ) ^ n * cbz ((M : ℤ) + m) (μ + n + m + 2))) * hr

/-! ## The `Finset` reindexing tool (a private copy of the `ZhuVermaAnArchABS` helper). -/

/-- Reindex `∑_{i ∈ range(P+1)} g i • T (i - s)` onto the common interval `Icc Lo Hi`, where the
mode is `μ = i - s` (so `i = μ + s`).  Needs `Icc (-s) (P-s) ⊆ Icc Lo Hi` and that the coefficient
`g (μ+s)` vanishes on the extra mode values.  Identical to the `ZhuVermaAnArchABS.reindexToIcc`
helper (re-stated here as that one is `private`). -/
private theorem reindexToIcc' (P : ℕ) (s Lo Hi : ℤ) (g : ℤ → ℂ) (T : ℤ → 𝒱)
    (hsub : Finset.Icc (-s) ((P : ℤ) - s) ⊆ Finset.Icc Lo Hi)
    (hzero : ∀ μ ∈ Finset.Icc Lo Hi, μ ∉ Finset.Icc (-s) ((P : ℤ) - s) → g (μ + s) = 0) :
    ∑ i ∈ Finset.range (P + 1), g (i : ℤ) • T ((i : ℤ) - s)
      = ∑ μ ∈ Finset.Icc Lo Hi, g (μ + s) • T μ := by
  have h1 : ∑ i ∈ Finset.range (P + 1), g (i : ℤ) • T ((i : ℤ) - s)
      = ∑ μ ∈ Finset.Icc (-s) ((P : ℤ) - s), g (μ + s) • T μ := by
    refine Finset.sum_nbij' (i := fun i => (i : ℤ) - s) (j := fun μ => (μ + s).toNat)
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
  intro μ hμ hμnot
  rw [hzero μ hμ hμnot, zero_smul]

/-! ## The three pieces, each rewritten onto the common mode range `Icc (-(n+m+2)) (M-1)`.

These are the `m`-shift analogues of `ZhuVermaAnArchABS.Lneg_piece`/`u_piece`/`circ_piece`: the bar
product `∗̄^n_m` uses shift `s = m`, binomial `C(m+i,i)`, pole `m+i+1` (vs the diagonal `n` of
`ABS`), and the circle generator `∘^n_m = resHom W m (n+m+2)` has pole `n+m+2`. -/

/-- The `(L₋₁u)` summand of `∗̄^n_m`, per `i`, on the common mode range.  After `smul_L_neg_one`
the inner sum becomes `∑_μ (-(μ+1))·C(M+1+m, μ+m+i+2) • u₍μ₎v`. -/
private theorem Lneg_piece_bar (W : VertexOperatorAlgebra 𝒱) (n m M : ℕ) {u : 𝒱}
    (_hu : u ∈ W.grading (M : ℤ)) (v : 𝒱) (i : ℕ) (hi : i ≤ n) :
    ∑ ℓ ∈ Finset.range (((M : ℤ) + 1 + (m : ℤ)).toNat + 1),
        cbz ((M : ℤ) + 1 + (m : ℤ)) ℓ •
          W.smul (W.L (-1) u) ((ℓ : ℤ) - ((m : ℤ) + (i : ℤ) + 1)) v
      = ∑ μ ∈ Finset.Icc (-((n : ℤ) + m + 2)) ((M : ℤ) - 1),
          (-((μ : ℤ) + 1) * cbz ((M : ℤ) + 1 + (m : ℤ)) ((μ : ℤ) + m + i + 2))
            • W.smul u μ v := by
  have hstep : ∀ ℓ : ℕ,
      cbz ((M : ℤ) + 1 + (m : ℤ)) ℓ •
          W.smul (W.L (-1) u) ((ℓ : ℤ) - ((m : ℤ) + (i : ℤ) + 1)) v
        = (cbz ((M : ℤ) + 1 + (m : ℤ)) ℓ *
            (-((ℓ : ℤ) - ((m : ℤ) + (i : ℤ) + 1))))
            • W.smul u ((ℓ : ℤ) - ((m : ℤ) + (i : ℤ) + 1) - 1) v := by
    intro ℓ
    rw [smul_L_neg_one, ← Int.cast_smul_eq_zsmul ℂ, smul_smul]
    congr 1
    push_cast; ring
  rw [Finset.sum_congr rfl (fun ℓ _ => hstep ℓ)]
  have hmode : ∀ ℓ : ℤ, (ℓ - ((m : ℤ) + (i : ℤ) + 1) - 1) = ℓ - ((m : ℤ) + i + 2) := by
    intro ℓ; ring
  simp only [hmode]
  rw [reindexToIcc' (((M : ℤ) + 1 + (m : ℤ)).toNat) ((m : ℤ) + i + 2)
      (-((n : ℤ) + m + 2)) ((M : ℤ) - 1)
      (fun ℓ => cbz ((M : ℤ) + 1 + (m : ℤ)) ℓ * (-(ℓ - ((m : ℤ) + (i : ℤ) + 1))))
      (fun μ => W.smul u μ v)]
  · refine Finset.sum_congr rfl fun μ _ => ?_
    congr 1
    rw [show (μ + ((m : ℤ) + i + 2)) = μ + m + i + 2 by ring]
    push_cast; ring
  · rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ (M : ℤ) + 1 + m by positivity)]
    intro x hx; simp only [Finset.mem_Icc] at hx ⊢; omega
  · rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ (M : ℤ) + 1 + m by positivity)]
    intro μ hμ hμnot
    simp only [Finset.mem_Icc] at hμ hμnot
    have hnot : ¬ (-((m : ℤ) + i + 2) ≤ μ ∧ μ ≤ (M : ℤ) + 1 + m - ((m : ℤ) + i + 2)) := hμnot
    rcases lt_or_ge μ (-((m : ℤ) + i + 2)) with hlo | hge
    · rw [cbz_apply_neg _ (by omega), zero_mul]
    · have hub : (M : ℤ) + 1 + m - ((m : ℤ) + i + 2) < μ := by
        by_contra h; exact hnot ⟨hge, by omega⟩
      rw [cbz_lt (by positivity) (by omega), zero_mul]

/-- The `u` summand of `∗̄^n_m`, per `i`, on the common mode range:
`∑_μ C(M+m, μ+m+i+1) • u₍μ₎v`. -/
private theorem u_piece_bar (W : VertexOperatorAlgebra 𝒱) (n m M : ℕ) {u : 𝒱}
    (_hu : u ∈ W.grading (M : ℤ)) (v : 𝒱) (i : ℕ) (hi : i ≤ n) :
    ∑ ℓ ∈ Finset.range (((M : ℤ) + (m : ℤ)).toNat + 1),
        cbz ((M : ℤ) + (m : ℤ)) ℓ • W.smul u ((ℓ : ℤ) - ((m : ℤ) + (i : ℤ) + 1)) v
      = ∑ μ ∈ Finset.Icc (-((n : ℤ) + m + 2)) ((M : ℤ) - 1),
          cbz ((M : ℤ) + (m : ℤ)) ((μ : ℤ) + m + i + 1) • W.smul u μ v := by
  rw [reindexToIcc' (((M : ℤ) + (m : ℤ)).toNat) ((m : ℤ) + i + 1)
      (-((n : ℤ) + m + 2)) ((M : ℤ) - 1)
      (fun ℓ => cbz ((M : ℤ) + (m : ℤ)) ℓ) (fun μ => W.smul u μ v)]
  · refine Finset.sum_congr rfl fun μ _ => ?_
    congr 2
    ring
  · rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ (M : ℤ) + m by positivity)]
    intro x hx; simp only [Finset.mem_Icc] at hx ⊢; omega
  · rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ (M : ℤ) + m by positivity)]
    intro μ hμ hμnot
    simp only [Finset.mem_Icc] at hμ hμnot
    have hnot : ¬ (-((m : ℤ) + i + 1) ≤ μ ∧ μ ≤ (M : ℤ) + m - ((m : ℤ) + i + 1)) := hμnot
    rcases lt_or_ge μ (-((m : ℤ) + i + 1)) with hlo | hge
    · rw [show ((μ : ℤ) + ((m : ℤ) + i + 1)) = μ + m + i + 1 by ring,
          cbz_apply_neg _ (by omega)]
    · have hub : (M : ℤ) + m - ((m : ℤ) + i + 1) < μ := by
        by_contra h; exact hnot ⟨hge, by omega⟩
      rw [show ((μ : ℤ) + ((m : ℤ) + i + 1)) = μ + m + i + 1 by ring,
          cbz_lt (by positivity) (by omega)]

/-- The circle product `∘^n_m`, on the common mode range: `∑_μ C(M+m, μ+n+m+2) • u₍μ₎v`. -/
private theorem circ_piece_bar (W : VertexOperatorAlgebra 𝒱) (n m M : ℕ) {u : 𝒱}
    (hu : u ∈ W.grading (M : ℤ)) (v : 𝒱) :
    anmCirc W n m u v
      = ∑ μ ∈ Finset.Icc (-((n : ℤ) + m + 2)) ((M : ℤ) - 1),
          cbz ((M : ℤ) + (m : ℤ)) ((μ : ℤ) + n + m + 2) • W.smul u μ v := by
  rw [anmCirc, resHom_homogeneous W (m : ℤ) ((n : ℤ) + (m : ℤ) + 2) hu v]
  rw [reindexToIcc' (((M : ℤ) + (m : ℤ)).toNat) ((n : ℤ) + m + 2)
      (-((n : ℤ) + m + 2)) ((M : ℤ) - 1)
      (fun ℓ => cbz ((M : ℤ) + (m : ℤ)) ℓ) (fun μ => W.smul u μ v)]
  · refine Finset.sum_congr rfl fun μ _ => ?_
    congr 2
    ring
  · rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ (M : ℤ) + m by positivity)]
    intro x hx; simp only [Finset.mem_Icc] at hx ⊢; omega
  · rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ (M : ℤ) + m by positivity)]
    intro μ hμ hμnot
    simp only [Finset.mem_Icc] at hμ hμnot
    have hge : -((n : ℤ) + m + 2) ≤ μ := hμ.1
    have hub : (M : ℤ) + m - ((n : ℤ) + m + 2) < μ := by
      by_contra h; exact hμnot ⟨hge, by omega⟩
    rw [show ((μ : ℤ) + ((n : ℤ) + m + 2)) = μ + n + m + 2 by ring,
        cbz_lt (by positivity) (by omega)]

/-! ## Bilinearity wrappers for the bar product (kept as `anmGenBar`, not unfolded). -/

private theorem anmGenBar_add_left (W : VertexOperatorAlgebra 𝒱) (n m : ℕ) (u₁ u₂ v : 𝒱) :
    anmGenBar W n m (u₁ + u₂) v = anmGenBar W n m u₁ v + anmGenBar W n m u₂ v := by
  simp only [anmGenBar, anmGen_add_left]

private theorem anmGenBar_smul_left (W : VertexOperatorAlgebra 𝒱) (n m : ℕ) (c : ℂ) (u v : 𝒱) :
    anmGenBar W n m (c • u) v = c • anmGenBar W n m u v := by
  simp only [anmGenBar, anmGen_smul_left]

/-! ## DJ Lemma 2.2 — the absorption identity (vector form). -/

/-- **DJ Lemma 2.2, homogeneous absorption identity.**  For homogeneous `u ∈ 𝒱_M`,
`(L(-1)u + L(0)u) ∗̄^n_m v = (n+m+1)·(-1)^n·C(n+m,m) • (u ∘^n_m v)`.  This is the display in DJ's
proof of Lemma 2.2 (`math/0601626`, p. 3): integrate by parts and telescope the alternating `i`-sum.

Proof scaffold (identical shape to `ZhuVermaAnArchABS.leftProd_Lgen_eq`, generalized from the
diagonal shift `n` to the bar-product shift `m`): split `(L₋₁u+L₀u) ∗̄^n_m v` into the `(L₋₁u)`- and
`(L₀u = M·u)`-summands, reduce each per-`i` term to the common integer mode range
`Icc (-(n+m+2)) (M-1)` (`Lneg_piece_bar`/`u_piece_bar`), swap the `i`- and mode-sums, and apply the
per-mode collapse `dj22_scalar`; recover `u ∘^n_m v` via `circ_piece_bar`. -/
theorem anmGenBar_Lgen_eq (W : VertexOperatorAlgebra 𝒱) (n m M : ℕ) {u : 𝒱}
    (hu : u ∈ W.grading (M : ℤ)) (v : 𝒱) :
    anmGenBar W n m (W.L (-1) u + W.L 0 u) v
      = (((n : ℂ) + m + 1) * (-1 : ℂ) ^ n * cbz ((n : ℤ) + (m : ℤ)) (m : ℤ))
          • anmCirc W n m u v := by
  set I := Finset.Icc (-((n : ℤ) + m + 2)) ((M : ℤ) - 1) with hI
  have hLmem : W.L (-1) u ∈ W.grading ((M : ℤ) + 1) := L_neg_one_mem_grading_succ W hu
  -- the `(L₋₁u)` summand, fully reduced to the Icc-mode form.
  have hLfull : anmGenBar W n m (W.L (-1) u) v
      = ∑ i ∈ Finset.range (n + 1),
          ((-1 : ℂ) ^ i * cbz ((m : ℤ) + i) i) •
            ∑ μ ∈ I, (-((μ : ℤ) + 1) * cbz ((M : ℤ) + 1 + (m : ℤ)) ((μ : ℤ) + m + i + 2))
              • W.smul u μ v := by
    rw [anmGenBar_eq]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [resHom_homogeneous W (m : ℤ) ((m : ℤ) + (i : ℤ) + 1) hLmem v,
        show ((M : ℤ) + 1 + (m : ℤ)) = ((M : ℤ) + 1) + (m : ℤ) from by ring]
    rw [show ((M : ℤ) + 1) + (m : ℤ) = (M : ℤ) + 1 + (m : ℤ) from by ring]
    rw [Lneg_piece_bar W n m M hu v i (by simpa using Finset.mem_range.mp hi)]
  -- the `u` summand, fully reduced.
  have hUfull : anmGenBar W n m u v
      = ∑ i ∈ Finset.range (n + 1),
          ((-1 : ℂ) ^ i * cbz ((m : ℤ) + i) i) •
            ∑ μ ∈ I, cbz ((M : ℤ) + (m : ℤ)) ((μ : ℤ) + m + i + 1) • W.smul u μ v := by
    rw [anmGenBar_eq]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [resHom_homogeneous W (m : ℤ) ((m : ℤ) + (i : ℤ) + 1) hu v]
    rw [u_piece_bar W n m M hu v i (by simpa using Finset.mem_range.mp hi)]
  -- `L₀ u = M • u`; split the bar product and substitute both reductions.
  rw [anmGenBar_add_left, L_zero_grading W u hu, anmGenBar_smul_left,
      show (((M : ℤ) : ℂ)) = (M : ℂ) from by push_cast; ring, hLfull, hUfull]
  rw [circ_piece_bar W n m M hu v]
  -- swap scaffold `∑_i s_i • ∑_μ c_i(μ) • T μ = ∑_μ (∑_i s_i · c_i(μ)) • T μ`.
  have swap : ∀ (c : ℕ → ℤ → ℂ),
      ∑ i ∈ Finset.range (n + 1),
          ((-1 : ℂ) ^ i * cbz ((m : ℤ) + i) i) •
            ∑ μ ∈ I, c i μ • W.smul u μ v
        = ∑ μ ∈ I, (∑ i ∈ Finset.range (n + 1),
            ((-1 : ℂ) ^ i * cbz ((m : ℤ) + i) i) * c i μ) • W.smul u μ v := by
    intro c
    rw [Finset.sum_congr rfl (fun i _ => by
          rw [Finset.smul_sum, Finset.sum_congr rfl (fun μ _ => by rw [smul_smul])])]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [Finset.sum_smul]
  rw [swap (fun i μ => -((μ : ℤ) + 1) * cbz ((M : ℤ) + 1 + (m : ℤ)) ((μ : ℤ) + m + i + 2))]
  -- distribute the `(M:ℂ)` factor over the `u`-summand into the per-mode coefficient.
  have hM : (M : ℂ) • ∑ i ∈ Finset.range (n + 1),
        ((-1 : ℂ) ^ i * cbz ((m : ℤ) + i) i) •
          ∑ μ ∈ I, cbz ((M : ℤ) + (m : ℤ)) ((μ : ℤ) + m + i + 1) • W.smul u μ v
      = ∑ i ∈ Finset.range (n + 1),
          ((-1 : ℂ) ^ i * cbz ((m : ℤ) + i) i) •
            ∑ μ ∈ I, ((M : ℂ) * cbz ((M : ℤ) + (m : ℤ)) ((μ : ℤ) + m + i + 1))
              • W.smul u μ v := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_comm, Finset.smul_sum]
    refine congrArg _ (Finset.sum_congr rfl fun μ _ => ?_)
    rw [smul_smul]
  rw [hM, swap (fun i μ => (M : ℂ) * cbz ((M : ℤ) + (m : ℤ)) ((μ : ℤ) + m + i + 1))]
  rw [Finset.smul_sum]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [smul_smul, ← add_smul]
  congr 1
  rw [← Finset.sum_add_distrib, ← dj22_scalar M n m μ]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- **DJ Lemma 2.2 — the requested repo signature** (homogeneous `u`).  Scalar times the circle
product equals the bar product of the grading generator:
`(n+m+1)·(-1)^n·C(n+m,m) • (u ∘^n_m v) = (L(-1)u+L(0)u) ∗̄^n_m v`. -/
theorem anmCirc_mem_OnBar (W : VertexOperatorAlgebra 𝒱) (n m : ℕ) {M : ℕ} {u : 𝒱}
    (hu : u ∈ W.grading (M : ℤ)) (v : 𝒱) :
    (((n : ℂ) + (m : ℂ) + 1) * ((-1 : ℂ)) ^ n * cbz ((n : ℤ) + (m : ℤ)) (m : ℤ))
        • anmCirc W n m u v
      = anmGenBar W n m (W.L (-1) u + W.L 0 u) v :=
  (anmGenBar_Lgen_eq W n m M hu v).symm

/-! ## DJ Lemma 2.2 — the general (non-homogeneous) membership. -/

/-- `anmGenBar` is additive in its first slot over a finite sum. -/
private theorem anmGenBar_sum_left (W : VertexOperatorAlgebra 𝒱) (n m : ℕ) {ι : Type*}
    (s : Finset ι) (f : ι → 𝒱) (b : 𝒱) :
    anmGenBar W n m (∑ k ∈ s, f k) b = ∑ k ∈ s, anmGenBar W n m (f k) b := by
  classical
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.sum_empty]
    have h0 : anmGenBar W n m ((0 : ℂ) • (0 : 𝒱)) b = (0 : ℂ) • anmGenBar W n m (0 : 𝒱) b :=
      anmGenBar_smul_left W n m 0 0 b
    simp only [zero_smul] at h0
    exact h0
  | insert k t hkt ih =>
    rw [Finset.sum_insert hkt, Finset.sum_insert hkt, anmGenBar_add_left, ih]

/-- **DJ Lemma 2.2 conclusion — `(L(-1)c+L(0)c) ∗̄^n_m b ∈ O_{n,m}(𝒱)`** (into the full Dong–Jiang
ideal).  Decompose `c` into homogeneous pieces and apply the absorption identity `anmGenBar_Lgen_eq`
to each: every piece becomes `scalar • (c_k ∘^n_m b) ∈ O'_{n,m} ⊆ O_{n,m}`.  This is the published
DJ Lemma 2.2 conclusion (`u ∘^n_m v ∈ O_n(V) ∗̄^n_m V`), here exhibited inside the full ideal. -/
theorem anmGenBar_Lgen_mem_OnmFull (W : VertexOperatorAlgebra 𝒱) (n m : ℕ) (c b : 𝒱) :
    anmGenBar W n m (W.L (-1) c + W.L 0 c) b ∈ OnmFull W n m := by
  classical
  letI := DirectSum.IsInternal.chooseDecomposition W.grading W.isInternal
  set s := (DirectSum.decompose W.grading c).support with hs
  have hdecomp : ∑ k ∈ s, ((DirectSum.decompose W.grading c k : W.grading k) : 𝒱) = c :=
    DirectSum.sum_support_decompose W.grading c
  have hsplit : W.L (-1) c + W.L 0 c
      = ∑ k ∈ s, (W.L (-1) ((DirectSum.decompose W.grading c k : W.grading k) : 𝒱)
          + W.L 0 ((DirectSum.decompose W.grading c k : W.grading k) : 𝒱)) := by
    rw [Finset.sum_add_distrib, ← map_sum, ← map_sum, hdecomp]
  rw [hsplit, anmGenBar_sum_left]
  refine Submodule.sum_mem _ fun k _ => ?_
  have hk : ((DirectSum.decompose W.grading c k : W.grading k) : 𝒱) ∈ W.grading k :=
    (DirectSum.decompose W.grading c k).2
  rcases le_or_gt 0 k with hknn | hkneg
  · obtain ⟨M, rfl⟩ := Int.eq_ofNat_of_zero_le hknn
    rw [anmGenBar_Lgen_eq W n m M hk b]
    exact Submodule.smul_mem _ _ (anmCirc_mem_OnmFull W n m _ b)
  · have hzero : ((DirectSum.decompose W.grading c k : W.grading k) : 𝒱) = 0 := by
      have : ((DirectSum.decompose W.grading c k : W.grading k) : 𝒱) ∈ (⊥ : Submodule ℂ 𝒱) := by
        rw [← W.positivity k hkneg]; exact hk
      simpa using this
    rw [hzero, map_zero, map_zero, add_zero,
        show (0 : 𝒱) = (0 : ℂ) • (0 : 𝒱) by simp, anmGenBar_smul_left, zero_smul]
    exact (OnmFull W n m).zero_mem

/-- **DJ Lemma 2.2 conclusion into the PARTIAL ideal `O'_{n,m} = Onm`** — `(L(-1)c+L(0)c) ∗̄^n_m b ∈
Onm W n m`.  Identical to `anmGenBar_Lgen_mem_OnmFull` but each homogeneous piece is `scalar •
(c_k ∘^n_m b) ∈ O'_{n,m}` via `anmCirc_mem_Onm` (the circle generator is already an `O'` element —
no `O''`/`O'''` needed).  This is the `anmGenBar` grading feeder for the `AnmComposeDescL` diagonal
grading slice (`anmLgen W p p c = L(-1)c+L(0)c`, `anmLgen_diag`). -/
theorem anmGenBar_Lgen_mem_Onm (W : VertexOperatorAlgebra 𝒱) (n m : ℕ) (c b : 𝒱) :
    anmGenBar W n m (W.L (-1) c + W.L 0 c) b ∈ Onm W n m := by
  classical
  letI := DirectSum.IsInternal.chooseDecomposition W.grading W.isInternal
  set s := (DirectSum.decompose W.grading c).support with hs
  have hdecomp : ∑ k ∈ s, ((DirectSum.decompose W.grading c k : W.grading k) : 𝒱) = c :=
    DirectSum.sum_support_decompose W.grading c
  have hsplit : W.L (-1) c + W.L 0 c
      = ∑ k ∈ s, (W.L (-1) ((DirectSum.decompose W.grading c k : W.grading k) : 𝒱)
          + W.L 0 ((DirectSum.decompose W.grading c k : W.grading k) : 𝒱)) := by
    rw [Finset.sum_add_distrib, ← map_sum, ← map_sum, hdecomp]
  rw [hsplit, anmGenBar_sum_left]
  refine Submodule.sum_mem _ fun k _ => ?_
  have hk : ((DirectSum.decompose W.grading c k : W.grading k) : 𝒱) ∈ W.grading k :=
    (DirectSum.decompose W.grading c k).2
  rcases le_or_gt 0 k with hknn | hkneg
  · obtain ⟨M, rfl⟩ := Int.eq_ofNat_of_zero_le hknn
    rw [anmGenBar_Lgen_eq W n m M hk b]
    exact Submodule.smul_mem _ _ (anmCirc_mem_Onm W n m _ b)
  · have hzero : ((DirectSum.decompose W.grading c k : W.grading k) : 𝒱) = 0 := by
      have : ((DirectSum.decompose W.grading c k : W.grading k) : 𝒱) ∈ (⊥ : Submodule ℂ 𝒱) := by
        rw [← W.positivity k hkneg]; exact hk
      simpa using this
    rw [hzero, map_zero, map_zero, add_zero,
        show (0 : 𝒱) = (0 : ℂ) • (0 : 𝒱) by simp, anmGenBar_smul_left, zero_smul]
    exact (Onm W n m).zero_mem

end VOA
