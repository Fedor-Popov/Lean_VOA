/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArch

/-!
# The **ABS vector assembly** (discharges `hLgen`).

This file proves the Dong–Li–Mason absorption identity (ABS) at the *vector* level and uses it to
discharge the `hLgen` hypothesis of `AnIdeal_of_gens` (`ZhuVermaAnArch.lean`):

* `leftProd_Lgen_eq` — for homogeneous `u ∈ 𝒱_M`,
  `leftProd W n ((L₋₁+L₀)u) v = (-1)^n · C(2n,n) · (2n+1) • (u ∘ₙ v)`.
* `leftProd_Lgen_mem_OnFull` — the general (non-homogeneous) membership
  `leftProd W n ((L₋₁+L₀)c) b ∈ OnFull W n`, i.e. the `hLgen` field.

The scalar core (`abs_scalar`, already proved in `ZhuVermaAnArch.lean`) collapses the alternating
`j`-sum.  Here we do the *Finset vector assembly*: rewrite both summands of
`leftProd W n (L₋₁u) v + M • leftProd W n u v` onto a common integer mode range, swap the `j`- and
mode-sums, apply `abs_scalar` per mode, and recover `u ∘ₙ v` via `circ_homogeneous`.

## References
Dong–Li–Mason, J. Algebra 206 (1998) 67–96; Gannon §5.3.2 Thm 5.3.4.
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## A reindexing tool: a `range`-indexed mode sum onto a common integer interval. -/

/-- Reindex `∑_{i ∈ range(P+1)} g i • T (i - s)` onto the common interval `Icc Lo Hi`, where the
mode is `m = i - s` (so `i = m + s`).  Needs `Icc (-s) (P-s) ⊆ Icc Lo Hi` and that the coefficient
`g (m+s)` vanishes on the extra mode values. -/
private theorem reindexToIcc (P : ℕ) (s Lo Hi : ℤ) (g : ℤ → ℂ) (T : ℤ → 𝒱)
    (hsub : Finset.Icc (-s) ((P : ℤ) - s) ⊆ Finset.Icc Lo Hi)
    (hzero : ∀ m ∈ Finset.Icc Lo Hi, m ∉ Finset.Icc (-s) ((P : ℤ) - s) → g (m + s) = 0) :
    ∑ i ∈ Finset.range (P + 1), g (i : ℤ) • T ((i : ℤ) - s)
      = ∑ m ∈ Finset.Icc Lo Hi, g (m + s) • T m := by
  have h1 : ∑ i ∈ Finset.range (P + 1), g (i : ℤ) • T ((i : ℤ) - s)
      = ∑ m ∈ Finset.Icc (-s) ((P : ℤ) - s), g (m + s) • T m := by
    refine Finset.sum_nbij' (i := fun i => (i : ℤ) - s) (j := fun m => (m + s).toNat)
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
  intro m hm hmnot
  rw [hzero m hm hmnot, zero_smul]

/-! ## The three pieces, each rewritten onto the common mode range `Icc (-(2n+2)) (M-1)`. -/

/-- The `(L₋₁u)` summand of `leftProd`, per `j`, on the common mode range.  After `smul_L_neg_one`
the inner sum becomes `∑_m (-(m+1))·C(M+1+n,m+n+j+2) • u₍ₘ₎v`. -/
private theorem Lneg_piece (W : VertexOperatorAlgebra 𝒱) (n M : ℕ) {u : 𝒱}
    (_hu : u ∈ W.grading (M : ℤ)) (v : 𝒱) (j : ℕ) (hj : j ≤ n) :
    ∑ i ∈ Finset.range (((M : ℤ) + 1 + (n : ℤ)).toNat + 1),
        cbz ((M : ℤ) + 1 + (n : ℤ)) i •
          W.smul (W.L (-1) u) ((i : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) v
      = ∑ m ∈ Finset.Icc (-(2 * (n : ℤ) + 2)) ((M : ℤ) - 1),
          (-((m : ℤ) + 1) * cbz ((M : ℤ) + 1 + (n : ℤ)) ((m : ℤ) + n + j + 2))
            • W.smul u m v := by
  -- rewrite (L₋₁u)₍k₎v = (-k) • u₍k-1₎v and merge scalars
  have hstep : ∀ i : ℕ,
      cbz ((M : ℤ) + 1 + (n : ℤ)) i •
          W.smul (W.L (-1) u) ((i : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) v
        = (cbz ((M : ℤ) + 1 + (n : ℤ)) i *
            (-((i : ℤ) - ((n : ℤ) + (j : ℤ) + 1))))
            • W.smul u ((i : ℤ) - ((n : ℤ) + (j : ℤ) + 1) - 1) v := by
    intro i
    rw [smul_L_neg_one, ← Int.cast_smul_eq_zsmul ℂ, smul_smul]
    congr 1
    push_cast; ring
  rw [Finset.sum_congr rfl (fun i _ => hstep i)]
  -- now apply reindexToIcc with s = n+j+2, g i = C(M+1+n,i)·(-(i-(n+j+1)))
  have hmode : ∀ i : ℤ, (i - ((n : ℤ) + (j : ℤ) + 1) - 1) = i - ((n : ℤ) + j + 2) := by
    intro i; ring
  simp only [hmode]
  rw [reindexToIcc (((M : ℤ) + 1 + (n : ℤ)).toNat) ((n : ℤ) + j + 2)
      (-(2 * (n : ℤ) + 2)) ((M : ℤ) - 1)
      (fun i => cbz ((M : ℤ) + 1 + (n : ℤ)) i * (-(i - ((n : ℤ) + (j : ℤ) + 1))))
      (fun m => W.smul u m v)]
  · refine Finset.sum_congr rfl fun m _ => ?_
    congr 1
    rw [show (m + ((n : ℤ) + j + 2)) = m + n + j + 2 by ring]
    push_cast; ring
  · -- containment
    rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ (M : ℤ) + 1 + n by positivity)]
    intro x hx; simp only [Finset.mem_Icc] at hx ⊢; omega
  · -- vanishing on extras
    rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ (M : ℤ) + 1 + n by positivity)]
    intro m hm hmnot
    simp only [Finset.mem_Icc] at hm hmnot
    have hnot : ¬ (-((n : ℤ) + j + 2) ≤ m ∧ m ≤ (M : ℤ) + 1 + n - ((n : ℤ) + j + 2)) := hmnot
    rcases lt_or_ge m (-((n : ℤ) + j + 2)) with hlo | hge
    · rw [cbz_apply_neg _ (by omega), zero_mul]
    · have hub : (M : ℤ) + 1 + n - ((n : ℤ) + j + 2) < m := by
        by_contra h; exact hnot ⟨hge, by omega⟩
      rw [cbz_lt (by positivity) (by omega), zero_mul]

/-- The `u` summand of `leftProd`, per `j`, on the common mode range:
`∑_m C(M+n,m+n+j+1) • u₍ₘ₎v`. -/
private theorem u_piece (W : VertexOperatorAlgebra 𝒱) (n M : ℕ) {u : 𝒱}
    (_hu : u ∈ W.grading (M : ℤ)) (v : 𝒱) (j : ℕ) (hj : j ≤ n) :
    ∑ i ∈ Finset.range (((M : ℤ) + (n : ℤ)).toNat + 1),
        cbz ((M : ℤ) + (n : ℤ)) i • W.smul u ((i : ℤ) - ((n : ℤ) + (j : ℤ) + 1)) v
      = ∑ m ∈ Finset.Icc (-(2 * (n : ℤ) + 2)) ((M : ℤ) - 1),
          cbz ((M : ℤ) + (n : ℤ)) ((m : ℤ) + n + j + 1) • W.smul u m v := by
  rw [reindexToIcc (((M : ℤ) + (n : ℤ)).toNat) ((n : ℤ) + j + 1)
      (-(2 * (n : ℤ) + 2)) ((M : ℤ) - 1)
      (fun i => cbz ((M : ℤ) + (n : ℤ)) i) (fun m => W.smul u m v)]
  · refine Finset.sum_congr rfl fun m _ => ?_
    congr 2
    ring
  · rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ (M : ℤ) + n by positivity)]
    intro x hx; simp only [Finset.mem_Icc] at hx ⊢; omega
  · rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ (M : ℤ) + n by positivity)]
    intro m hm hmnot
    simp only [Finset.mem_Icc] at hm hmnot
    have hnot : ¬ (-((n : ℤ) + j + 1) ≤ m ∧ m ≤ (M : ℤ) + n - ((n : ℤ) + j + 1)) := hmnot
    rcases lt_or_ge m (-((n : ℤ) + j + 1)) with hlo | hge
    · rw [show ((m : ℤ) + ((n : ℤ) + j + 1)) = m + n + j + 1 by ring,
          cbz_apply_neg _ (by omega)]
    · have hub : (M : ℤ) + n - ((n : ℤ) + j + 1) < m := by
        by_contra h; exact hnot ⟨hge, by omega⟩
      rw [show ((m : ℤ) + ((n : ℤ) + j + 1)) = m + n + j + 1 by ring,
          cbz_lt (by positivity) (by omega)]

/-- The circle product, on the common mode range: `∑_m C(M+n,m+2n+2) • u₍ₘ₎v`. -/
private theorem circ_piece (W : VertexOperatorAlgebra 𝒱) (n M : ℕ) {u : 𝒱}
    (hu : u ∈ W.grading (M : ℤ)) (v : 𝒱) :
    circ W n u v
      = ∑ m ∈ Finset.Icc (-(2 * (n : ℤ) + 2)) ((M : ℤ) - 1),
          cbz ((M : ℤ) + (n : ℤ)) ((m : ℤ) + 2 * n + 2) • W.smul u m v := by
  rw [circ_homogeneous W n hu v]
  have hmode : ∀ i : ℤ, (i - 2 * (n : ℤ) - 2) = i - (2 * (n : ℤ) + 2) := by intro i; ring
  simp only [hmode]
  rw [reindexToIcc (((M : ℤ) + (n : ℤ)).toNat) (2 * (n : ℤ) + 2)
      (-(2 * (n : ℤ) + 2)) ((M : ℤ) - 1)
      (fun i => cbz ((M : ℤ) + (n : ℤ)) i) (fun m => W.smul u m v)]
  · refine Finset.sum_congr rfl fun m _ => ?_
    congr 2
    ring
  · rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ (M : ℤ) + n by positivity)]
    intro x hx; simp only [Finset.mem_Icc] at hx ⊢; omega
  · rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ (M : ℤ) + n by positivity)]
    intro m hm hmnot
    simp only [Finset.mem_Icc] at hm hmnot
    have hge : -(2 * (n : ℤ) + 2) ≤ m := hm.1
    have hub : (M : ℤ) + n - (2 * (n : ℤ) + 2) < m := by
      by_contra h; exact hmnot ⟨hge, by omega⟩
    rw [show ((m : ℤ) + (2 * (n : ℤ) + 2)) = m + 2 * n + 2 by ring,
        cbz_lt (by positivity) (by omega)]

/-! ## The ABS vector identity. -/

/-- **(ABS) — the Dong–Li–Mason absorption identity, vector form.**  For homogeneous `u ∈ 𝒱_M`,
`leftProd W n ((L₋₁+L₀)u) v = (-1)^n · C(2n,n) · (2n+1) • (u ∘ₙ v)`. -/
theorem leftProd_Lgen_eq (W : VertexOperatorAlgebra 𝒱) (n M : ℕ) {u : 𝒱}
    (hu : u ∈ W.grading (M : ℤ)) (v : 𝒱) :
    leftProd W n (W.L (-1) u + W.L 0 u) v
      = ((-1 : ℂ) ^ n * cbz (2 * (n : ℤ)) n * (2 * (n : ℂ) + 1)) • circ W n u v := by
  set I := Finset.Icc (-(2 * (n : ℤ) + 2)) ((M : ℤ) - 1) with hI
  have hLmem : W.L (-1) u ∈ W.grading ((M : ℤ) + 1) := L_neg_one_mem_grading_succ W hu
  -- Step 1+2+3: the `(L₋₁u)` summand, fully reduced to the Icc-mode form.
  have hLfull : leftProd W n (W.L (-1) u) v
      = ∑ j ∈ Finset.range (n + 1),
          ((-1 : ℂ) ^ j * cbz ((j : ℤ) + n) n) •
            ∑ m ∈ I, (-((m : ℤ) + 1) * cbz ((M : ℤ) + 1 + (n : ℤ)) ((m : ℤ) + n + j + 2))
              • W.smul u m v := by
    rw [leftProd_homogeneous W n hLmem v]
    exact Finset.sum_congr rfl fun j hj => by
      rw [Lneg_piece W n M hu v j (by simpa using Finset.mem_range.mp hj)]
  -- the `u` summand, fully reduced.
  have hUfull : leftProd W n u v
      = ∑ j ∈ Finset.range (n + 1),
          ((-1 : ℂ) ^ j * cbz ((j : ℤ) + n) n) •
            ∑ m ∈ I, cbz ((M : ℤ) + (n : ℤ)) ((m : ℤ) + n + j + 1) • W.smul u m v := by
    rw [leftProd_homogeneous W n hu v]
    exact Finset.sum_congr rfl fun j hj => by
      rw [u_piece W n M hu v j (by simpa using Finset.mem_range.mp hj)]
  -- Step 1: L₀ u = M • u, split leftProd, substitute both reductions.
  rw [L_zero_grading W u hu, leftProd_add_left, leftProd_smul_left, hLfull, hUfull,
      show (((M : ℤ) : ℂ)) = (M : ℂ) from by push_cast; ring]
  -- Step 4: pull the scalars in, merge the two j-sums into one, swap j ↔ m, apply abs_scalar.
  rw [circ_piece W n M hu v]
  -- A general scaffold: ∑_j s_j • ∑_m c_j(m) • T m  =  ∑_m (∑_j s_j · c_j(m)) • T m.
  have swap : ∀ (c : ℕ → ℤ → ℂ),
      ∑ j ∈ Finset.range (n + 1),
          ((-1 : ℂ) ^ j * cbz ((j : ℤ) + n) n) •
            ∑ m ∈ I, c j m • W.smul u m v
        = ∑ m ∈ I, (∑ j ∈ Finset.range (n + 1),
            ((-1 : ℂ) ^ j * cbz ((j : ℤ) + n) n) * c j m) • W.smul u m v := by
    intro c
    -- distribute s_j • into the inner m-sum, making it a genuine double sum, then swap.
    rw [Finset.sum_congr rfl (fun j _ => by
          rw [Finset.smul_sum, Finset.sum_congr rfl (fun m _ => by rw [smul_smul])])]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.sum_smul]
  rw [swap (fun j m => -((m : ℤ) + 1) * cbz ((M : ℤ) + 1 + (n : ℤ)) ((m : ℤ) + n + j + 2))]
  -- distribute the (M:ℂ) over the u-term sum into the per-mode coefficient.
  have hM : (M : ℂ) • ∑ j ∈ Finset.range (n + 1),
        ((-1 : ℂ) ^ j * cbz ((j : ℤ) + n) n) •
          ∑ m ∈ I, cbz ((M : ℤ) + (n : ℤ)) ((m : ℤ) + n + j + 1) • W.smul u m v
      = ∑ j ∈ Finset.range (n + 1),
          ((-1 : ℂ) ^ j * cbz ((j : ℤ) + n) n) •
            ∑ m ∈ I, ((M : ℂ) * cbz ((M : ℤ) + (n : ℤ)) ((m : ℤ) + n + j + 1))
              • W.smul u m v := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_comm, Finset.smul_sum]
    refine congrArg _ (Finset.sum_congr rfl fun m _ => ?_)
    rw [smul_smul]
  rw [hM, swap (fun j m => (M : ℂ) * cbz ((M : ℤ) + (n : ℤ)) ((m : ℤ) + n + j + 1))]
  -- distribute the leading scalar on the RHS over the m-sum.
  rw [Finset.smul_sum]
  -- now combine the two ∑_m into one and recognise abs_scalar
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [smul_smul]
  rw [← add_smul]
  congr 1
  -- goal: ∑_j s_j·A_j(m) + ∑_j s_j·B'_j(m) = scalar · cbz(M+n, m+2n+2)
  rw [← Finset.sum_add_distrib]
  rw [← abs_scalar M n m]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-! ## The general (non-homogeneous) `hLgen` membership. -/

/-- `leftProd` is additive in its first slot over a finite sum. -/
private theorem leftProd_sum_left (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {ι : Type*}
    (s : Finset ι) (f : ι → 𝒱) (b : 𝒱) :
    leftProd W n (∑ k ∈ s, f k) b = ∑ k ∈ s, leftProd W n (f k) b := by
  classical
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.sum_empty]
    have h0 : leftProd W n ((0 : ℂ) • (0 : 𝒱)) b = (0 : ℂ) • leftProd W n (0 : 𝒱) b :=
      leftProd_smul_left W n 0 0 b
    simp only [zero_smul] at h0
    exact h0
  | insert k t hkt ih => rw [Finset.sum_insert hkt, Finset.sum_insert hkt, leftProd_add_left, ih]

/-- **`hLgen` — the `(L₋₁+L₀)` left-generator membership.**  For arbitrary `c b : 𝒱`,
`leftProd W n ((L₋₁+L₀)c) b ∈ OnFull W n`.  Decompose `c` into homogeneous pieces and apply
the absorption identity `leftProd_Lgen_eq` to each: every piece becomes `scalar • (cₖ ∘ₙ b)`. -/
theorem leftProd_Lgen_mem_OnFull (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (c b : 𝒱) :
    leftProd W n (W.L (-1) c + W.L 0 c) b ∈ OnFull W n := by
  classical
  letI := DirectSum.IsInternal.chooseDecomposition W.grading W.isInternal
  -- Decompose `c = ∑_{k ∈ support} cₖ`, with `cₖ ∈ W.grading k`.
  set s := (DirectSum.decompose W.grading c).support with hs
  have hdecomp : ∑ k ∈ s, ((DirectSum.decompose W.grading c k : W.grading k) : 𝒱) = c :=
    DirectSum.sum_support_decompose W.grading c
  -- Rewrite the whole `(L₋₁+L₀)c` generator as a sum over the pieces.
  have hsplit : W.L (-1) c + W.L 0 c
      = ∑ k ∈ s, (W.L (-1) ((DirectSum.decompose W.grading c k : W.grading k) : 𝒱)
          + W.L 0 ((DirectSum.decompose W.grading c k : W.grading k) : 𝒱)) := by
    rw [Finset.sum_add_distrib, ← map_sum, ← map_sum, hdecomp]
  rw [hsplit, leftProd_sum_left]
  -- Each piece lands in `Oₙ ⊆ OnFull` via the absorption identity.
  refine Submodule.sum_mem _ fun k _ => ?_
  have hk : ((DirectSum.decompose W.grading c k : W.grading k) : 𝒱) ∈ W.grading k :=
    (DirectSum.decompose W.grading c k).2
  rcases le_or_gt 0 k with hknn | hkneg
  · -- k ≥ 0: write k = (M:ℕ) and apply the absorption identity.
    obtain ⟨M, rfl⟩ := Int.eq_ofNat_of_zero_le hknn
    rw [leftProd_Lgen_eq W n M hk b]
    exact Submodule.smul_mem _ _ (circ_mem_OnFull W n _ b)
  · -- k < 0: the grading is `⊥` (VOA positivity), so the piece is `0` and the product is `0`.
    have hzero : ((DirectSum.decompose W.grading c k : W.grading k) : 𝒱) = 0 := by
      have : ((DirectSum.decompose W.grading c k : W.grading k) : 𝒱) ∈ (⊥ : Submodule ℂ 𝒱) := by
        rw [← W.positivity k hkneg]; exact hk
      simpa using this
    rw [hzero, map_zero, map_zero, add_zero,
        show (0 : 𝒱) = (0 : ℂ) • (0 : 𝒱) by simp, leftProd_smul_left, zero_smul]
    exact (OnFull W n).zero_mem

end VOA
