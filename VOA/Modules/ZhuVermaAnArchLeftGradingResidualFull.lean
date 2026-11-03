/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchMUcross
import VOA.Modules.ZhuVermaAnArchDJ27
import VOA.Modules.ZhuVermaAnArchDJ28Left

/-!
# `LeftGradingResidual W n 0 p` — the general right-slot grading absorption

The single remaining Half-B leaf of Zhu's bijection: the general-`p` right-slot grading absorption
`a ∗ⁿ_{0,p} (anmLgen W p 0 c) ∈ O_{n,0}(V)` (`LeftGradingResidual W n 0 p`, `ZhuVermaAnArchDJ28Left`).
DJ prove this unconditional (`math/0601626`, Lemma 2.5's right-factor half); the repo carried it as a
named residual `LeftGradingResidual`.  Here we discharge it.

## The closed identity (engine-verified, all `n p : ℕ`)

For homogeneous `a ∈ 𝒱_K`, `c ∈ 𝒱_M`,
```
a ∗ⁿ_{0,p} (anmLgen W p 0 c)
  = anmLgen W n 0 (a ∗ⁿ_{0,p} c)                     -- a grading generator, ∈ O_{n,0}
    + σ_p • (a ∘ⁿ_0 c)                                -- a circle generator, ∈ O_{n,0}
```
with `σ_p = (−1)^{p+1} (n+1) C(n, p)`.  Both summands lie in `O_{n,0} ⊆ O_{n,0}(V)` (full ideal), so the
target follows for homogeneous `a, c`, then for arbitrary `a, c` by `reduce_homogeneous`.

The mechanism is the per-mode regroup `a₍ₘ₎(anmLgen W p 0 c) = anmLgen W n 0 (a₍ₘ₎c) + (m+1+n−K−p)a₍ₘ₎c
+ m·a₍ₘ₋₁₎c` (a `−p` shift of `smul_Lgen_right_regroup_n0`), followed by the collapse of the pure-mode
residual onto `σ_p • anmCirc` via the per-mode scalar telescope `lgrfull_abs_scalar` (a right-slot
analogue of the proven `dj27_abs_scalar`, telescoped by `Finset.sum_range_sub'` +
`cbz_upper_shift_int` + `cbz_absorption`).

Axiom-clean (`[propext, Classical.choice, Quot.sound]`), pbw-free.

## References
Dong–Jiang, Math. Z. 259 (2008) 799–826 (`math/0601626`), §2 (Lemma 2.5, the right-factor grading
absorption `v ¯∗ₙₘ (L(−1)u + (L(0)+m−n)u) ∈ O'ₙₘ`); `ZhuVermaAnArchMUcross`
(`anmRight_zero_crossL_mem_Onm`, the `p = 0` template), `ZhuVermaAnArchDJ27` (`dj27_abs_scalar`,
`cbz_upper_shift_int`), `ZhuVermaAnArchDJ28Left` (`LeftGradingResidual`).
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The per-mode scalar telescope (right-slot analogue of `dj27_abs_scalar`). -/

/-- **The general-`p` right-slot grading-absorption per-mode scalar identity** (engine-verified).
For `n p K : ℕ` and `r : ℤ` (the mode of `a₍ᵣ₎c`), the alternating `i`-sum coefficient of `a₍ᵣ₎c` in the
pure-mode residual of `a ∗ⁿ_{0,p} (anmLgen W p 0 c)` collapses to `σ_p · C(K, r+n+2)`, the coefficient of
the circle generator, with `σ_p = (−1)^{p+1}(n+1)C(n,p)`.

Proof: each `i`-term equals `D i − D (i+1)` for `D i := −(−1)ⁱ·i·C(n−p+i, i)·C(K, r+n−p+i+1)` (via
`cbz_upper_shift_int` to reshape the front binomial and `cbz_absorption` to link the two `K`-binomials),
so `Finset.sum_range_sub'` telescopes the sum to `D 0 − D (p+1) = −D (p+1)`; a final
`cbz_upper_shift_int` turns `−D (p+1)` into `σ_p · C(K, r+n+2)`. -/
theorem lgrfull_abs_scalar (n p K : ℕ) (r : ℤ) :
    (∑ i ∈ Finset.range (p + 1),
        (-1 : ℂ) ^ i * cbz ((n : ℤ) - (p : ℤ) + i) (i : ℤ) *
          (((r : ℂ) + 1 + (n : ℂ) - (K : ℂ) - (p : ℂ)) * cbz (K : ℤ) (r + n - p + i + 1)
            + ((r : ℂ) + 1) * cbz (K : ℤ) (r + n - p + i + 2)))
      = (-1 : ℂ) ^ (p + 1) * ((n : ℂ) + 1) * cbz (n : ℤ) (p : ℤ) * cbz (K : ℤ) (r + n + 2) := by
  set D : ℕ → ℂ := fun i =>
    -((-1 : ℂ) ^ i * (i : ℂ) * cbz ((n : ℤ) - (p : ℤ) + i) (i : ℤ)
      * cbz (K : ℤ) (r + n - p + i + 1)) with hD
  have hterm : ∀ i ∈ Finset.range (p + 1),
      (-1 : ℂ) ^ i * cbz ((n : ℤ) - (p : ℤ) + i) (i : ℤ) *
        (((r : ℂ) + 1 + (n : ℂ) - (K : ℂ) - (p : ℂ)) * cbz (K : ℤ) (r + n - p + i + 1)
          + ((r : ℂ) + 1) * cbz (K : ℤ) (r + n - p + i + 2)) = D i - D (i + 1) := by
    intro i _
    -- (i+1)·C(n−p+i+1, i+1) = (n−p+i+1)·C(n−p+i, i)
    have hsh := cbz_upper_shift_int ((n : ℤ) - (p : ℤ) + i) i
    push_cast at hsh
    -- C(K, r+n−p+i+2)·(r+n−p+i+2) = C(K, r+n−p+i+1)·(K − (r+n−p+i+2) + 1)
    have hab := cbz_absorption K (r + n - p + i + 2)
    rw [show (r + (n : ℤ) - p + i + 2 - 1) = r + n - p + i + 1 from by ring] at hab
    push_cast at hab
    simp only [hD]
    rw [show (((i + 1 : ℕ) : ℤ)) = (i : ℤ) + 1 from by push_cast; ring,
        show ((n : ℤ) - p + ((i : ℤ) + 1)) = ((n : ℤ) - p + i) + 1 from by ring,
        show (r + (n : ℤ) - p + ((i : ℤ) + 1) + 1) = r + n - p + i + 2 from by ring]
    push_cast [pow_succ]
    linear_combination
      ((-1 : ℂ) ^ i * cbz (K : ℤ) (r + n - p + i + 2)) * hsh
        + ((-1 : ℂ) ^ i * cbz ((n : ℤ) - (p : ℤ) + i) (i : ℤ)) * hab
  rw [Finset.sum_congr rfl hterm, Finset.sum_range_sub' D (p + 1)]
  -- D 0 = 0, so the sum is −D (p+1); one more `cbz_upper_shift_int` gives the scalar.
  have hsh := cbz_upper_shift_int (n : ℤ) p
  simp only [hD]
  rw [show (((p + 1 : ℕ) : ℤ)) = (p : ℤ) + 1 from by push_cast; ring,
      show ((n : ℤ) - p + ((p : ℤ) + 1)) = (n : ℤ) + 1 from by ring,
      show (r + (n : ℤ) - p + ((p : ℤ) + 1) + 1) = r + n + 2 from by ring]
  push_cast [pow_succ] at hsh ⊢
  linear_combination (-((-1 : ℂ) ^ p * cbz (K : ℤ) (r + n + 2))) * hsh

/-! ## The per-mode regroup at `m = 0`, general `p` (a `−p` shift of `smul_Lgen_right_regroup_n0`). -/

/-- **Per-mode regroup at `m = 0`, general `p`.**  For `a ∈ 𝒱_K`, `c ∈ 𝒱_M` and any mode `m`, the
right-slot grading generator `anmLgen W p 0 c` rewrites as the level-`n` grading generator on the slice
`a₍ₘ₎c` plus pure mode terms:
`a₍ₘ₎(anmLgen W p 0 c) = anmLgen W n 0 (a₍ₘ₎c) + (m+1+n−K−p)·a₍ₘ₎c + m·a₍ₘ₋₁₎c`.
(The `−p` correction over `smul_Lgen_right_regroup_n0` comes from the `(0−p)·c` summand of
`anmLgen W p 0 c`.) -/
theorem smul_Lgen_right_regroup_gen (W : VertexOperatorAlgebra 𝒱) (n p : ℕ) {K M : ℤ} {a c : 𝒱}
    (ha : a ∈ W.grading K) (hc : c ∈ W.grading M) (m : ℤ) :
    W.smul a m (anmLgen W p 0 c)
      = anmLgen W n 0 (W.smul a m c)
        + ((m : ℂ) + 1 + (n : ℂ) - K - (p : ℂ)) • W.smul a m c + (m : ℂ) • W.smul a (m - 1) c := by
  have hexp : anmLgen W p 0 c = (W.L (-1) c + W.L 0 c) + ((0 : ℂ) - (p : ℂ)) • c := by
    rw [anmLgen, Nat.cast_zero]
  rw [hexp, PreVertexAlgebra.smul_add_right, PreVertexAlgebra.smul_smul_right,
      smul_Lgen_right_regroup_n0 W n ha hc m]
  push_cast
  module

/-! ## Reindexing a `range`-indexed mode sum onto a common integer interval (local copy). -/

/-- Reindex `∑_{i ∈ range(P+1)} g i • T (i − s)` onto `Icc Lo Hi` (mode `μ = i − s`).  Local copy of
`ZhuVermaAnArchDJ27.reindexToIcc27`. -/
private theorem reindexToIccLGR (P : ℕ) (s Lo Hi : ℤ) (g : ℤ → ℂ) (T : ℤ → 𝒱)
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

/-! ## The homogeneous tower / rest split (general `p`). -/

/-- The level-`n` grading-generator **tower** of the general-`p` `m = 0` `(anmLgen W p 0 c)` expansion:
the FZ double sum with each mode `a₍μ₎c` replaced by its level-`n` grading generator
`anmLgen W n 0 (a₍μ₎c)`.  Each summand lies in `Onm W n 0`. -/
noncomputable def crossLTowerFull (W : VertexOperatorAlgebra 𝒱) (n p K : ℕ) (a c : 𝒱) : 𝒱 :=
  ∑ i ∈ Finset.range (p + 1),
    ((-1 : ℂ) ^ i * cbz ((n : ℤ) - (p : ℤ) + i) (i : ℤ)) •
      ∑ ℓ ∈ Finset.range ((K : ℤ).toNat + 1),
        cbz (K : ℤ) (ℓ : ℤ) •
          anmLgen W n 0 (W.smul a ((ℓ : ℤ) - ((n : ℤ) - (p : ℤ) + i + 1)) c)

/-- The pure-mode **rest** of the general-`p` `m = 0` `(anmLgen W p 0 c)` expansion. -/
noncomputable def crossLRestFull (W : VertexOperatorAlgebra 𝒱) (n p K : ℕ) (a c : 𝒱) : 𝒱 :=
  ∑ i ∈ Finset.range (p + 1),
    ((-1 : ℂ) ^ i * cbz ((n : ℤ) - (p : ℤ) + i) (i : ℤ)) •
      ∑ ℓ ∈ Finset.range ((K : ℤ).toNat + 1),
        cbz (K : ℤ) (ℓ : ℤ) •
          ((((ℓ : ℤ) - ((n : ℤ) - (p : ℤ) + i + 1) : ℂ) + 1 + (n : ℂ) - (K : ℂ) - (p : ℂ)) •
              W.smul a ((ℓ : ℤ) - ((n : ℤ) - (p : ℤ) + i + 1)) c
            + (((ℓ : ℤ) - ((n : ℤ) - (p : ℤ) + i + 1)) : ℂ) •
              W.smul a ((ℓ : ℤ) - ((n : ℤ) - (p : ℤ) + i + 1) - 1) c)

/-- **Homogeneous split.**  For `a ∈ 𝒱_K`, `c ∈ 𝒱_M`,
`a ∗ⁿ_{0,p} (anmLgen W p 0 c) = crossLTowerFull + crossLRestFull`. -/
theorem anmGen_zero_Lgen_right_homog_gen (W : VertexOperatorAlgebra 𝒱) (n p : ℕ) {K M : ℕ}
    {a c : 𝒱} (ha : a ∈ W.grading (K : ℤ)) (hc : c ∈ W.grading (M : ℤ)) :
    anmGen W n 0 p a (anmLgen W p 0 c)
      = crossLTowerFull W n p K a c + crossLRestFull W n p K a c := by
  rw [anmGen, crossLTowerFull, crossLRestFull, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hinner : resHom W ((0 : ℕ) : ℤ) ((n : ℤ) - (p : ℤ) + i + 1) a (anmLgen W p 0 c)
      = (∑ ℓ ∈ Finset.range ((K : ℤ).toNat + 1),
          cbz (K : ℤ) (ℓ : ℤ) •
            anmLgen W n 0 (W.smul a ((ℓ : ℤ) - ((n : ℤ) - (p : ℤ) + i + 1)) c))
        + ∑ ℓ ∈ Finset.range ((K : ℤ).toNat + 1),
            cbz (K : ℤ) (ℓ : ℤ) •
              ((((ℓ : ℤ) - ((n : ℤ) - (p : ℤ) + i + 1) : ℂ) + 1 + (n : ℂ) - (K : ℂ) - (p : ℂ)) •
                  W.smul a ((ℓ : ℤ) - ((n : ℤ) - (p : ℤ) + i + 1)) c
                + (((ℓ : ℤ) - ((n : ℤ) - (p : ℤ) + i + 1)) : ℂ) •
                  W.smul a ((ℓ : ℤ) - ((n : ℤ) - (p : ℤ) + i + 1) - 1) c) := by
    rw [resHom_homogeneous W ((0 : ℕ) : ℤ) ((n : ℤ) - (p : ℤ) + i + 1) ha,
        show ((K : ℤ) + ((0 : ℕ) : ℤ)) = (K : ℤ) from by push_cast; ring, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    rw [smul_Lgen_right_regroup_gen W n p ha hc ((ℓ : ℤ) - ((n : ℤ) - (p : ℤ) + i + 1))]
    push_cast
    module
  rw [show ((0 : ℕ) : ℤ) + (n : ℤ) - (p : ℤ) + i = (n : ℤ) - (p : ℤ) + i from by push_cast; ring,
      hinner, smul_add]

/-- **The tower lands in `Onm W n 0`.**  Each inner summand is a grading generator
`anmLgen W n 0 (a₍μ₎c) ∈ OnmL ⊆ Onm`. -/
theorem crossLTowerFull_mem_Onm (W : VertexOperatorAlgebra 𝒱) (n p K : ℕ) (a c : 𝒱) :
    crossLTowerFull W n p K a c ∈ Onm W n 0 := by
  rw [crossLTowerFull]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
  refine Submodule.sum_mem _ fun ℓ _ => Submodule.smul_mem _ _ ?_
  exact anmLgen_mem_Onm W n 0 (W.smul a ((ℓ : ℤ) - ((n : ℤ) - (p : ℤ) + i + 1)) c)

/-! ## The pure-mode rest collapses to `σ_p • anmCirc`. -/

/-- **Per-`i` inner reindex.**  The `i`-th inner rest sum reindexes onto the common mode interval,
combining term1 (`s = P_i`) and term2 (`s = P_i + 1`), `P_i = n − p + i + 1`. -/
private theorem restInner_reindex (W : VertexOperatorAlgebra 𝒱) (n p : ℕ) {K : ℕ} {a : 𝒱}
    (ha : a ∈ W.grading (K : ℤ)) (c : 𝒱) (i : ℕ) (hip : i ≤ p) :
    (∑ ℓ ∈ Finset.range ((K : ℤ).toNat + 1),
        cbz (K : ℤ) (ℓ : ℤ) •
          ((((ℓ : ℤ) - ((n : ℤ) - (p : ℤ) + i + 1) : ℂ) + 1 + (n : ℂ) - (K : ℂ) - (p : ℂ)) •
              W.smul a ((ℓ : ℤ) - ((n : ℤ) - (p : ℤ) + i + 1)) c
            + (((ℓ : ℤ) - ((n : ℤ) - (p : ℤ) + i + 1)) : ℂ) •
              W.smul a ((ℓ : ℤ) - ((n : ℤ) - (p : ℤ) + i + 1) - 1) c))
      = ∑ ν ∈ Finset.Icc (-((n : ℤ) + 2)) ((K : ℤ) + (p : ℤ)),
          (cbz (K : ℤ) (ν + ((n : ℤ) - (p : ℤ) + i + 1))
                * ((ν : ℂ) + 1 + (n : ℂ) - (K : ℂ) - (p : ℂ))
            + cbz (K : ℤ) (ν + ((n : ℤ) - (p : ℤ) + i + 1) + 1) * ((ν : ℂ) + 1))
            • W.smul a ν c := by
  simp only [smul_add]
  rw [Finset.sum_add_distrib]
  -- term2: rewrite the mode/scalar into the `s = P_i + 1` shape.
  have ht2 : ∀ ℓ ∈ Finset.range ((K : ℤ).toNat + 1),
      cbz (K : ℤ) (ℓ : ℤ) •
          ((((ℓ : ℤ) - ((n : ℤ) - (p : ℤ) + i + 1)) : ℂ) •
            W.smul a ((ℓ : ℤ) - ((n : ℤ) - (p : ℤ) + i + 1) - 1) c)
        = cbz (K : ℤ) (ℓ : ℤ) •
          ((((ℓ : ℤ) - ((n : ℤ) - (p : ℤ) + i + 1 + 1)) : ℂ) + 1) •
            W.smul a ((ℓ : ℤ) - ((n : ℤ) - (p : ℤ) + i + 1 + 1)) c := by
    intro ℓ _
    rw [show ((ℓ : ℤ) - ((n : ℤ) - (p : ℤ) + i + 1) - 1)
          = ((ℓ : ℤ) - ((n : ℤ) - (p : ℤ) + i + 1 + 1)) from by ring]
    congr 2
    push_cast; ring
  rw [Finset.sum_congr rfl ht2]
  -- combine the `cbz` factor into the scalar (`smul_smul`) for both terms.
  simp only [smul_smul]
  -- reindex term1 (s = P_i) and term2 (s = P_i + 1).
  have hip' : (i : ℤ) ≤ (p : ℤ) := by exact_mod_cast hip
  rw [reindexToIccLGR ((K : ℤ).toNat) ((n : ℤ) - (p : ℤ) + i + 1) (-((n : ℤ) + 2)) ((K : ℤ) + (p : ℤ))
        (fun t => cbz (K : ℤ) t * (((t - ((n : ℤ) - (p : ℤ) + i + 1) : ℂ)) + 1 + (n : ℂ) - (K : ℂ)
          - (p : ℂ))) (fun ν => W.smul a ν c)
        (by rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ (K : ℤ) by positivity)]
            intro x hx; simp only [Finset.mem_Icc] at hx ⊢; omega)
        (by
          rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ (K : ℤ) by positivity)]
          intro μ _ hμnot; simp only [Finset.mem_Icc, not_and, not_le] at hμnot
          simp only []
          rcases lt_or_ge (μ + ((n : ℤ) - (p : ℤ) + i + 1)) 0 with hlo | hge
          · rw [cbz_apply_neg (K : ℤ) hlo, zero_mul]
          · have hgt : (K : ℤ) < μ + ((n : ℤ) - (p : ℤ) + i + 1) := by
              have := hμnot (by omega); omega
            rw [cbz_lt (by positivity) hgt, zero_mul])]
  rw [reindexToIccLGR ((K : ℤ).toNat) ((n : ℤ) - (p : ℤ) + i + 1 + 1) (-((n : ℤ) + 2))
        ((K : ℤ) + (p : ℤ))
        (fun t => cbz (K : ℤ) t * (((t - ((n : ℤ) - (p : ℤ) + i + 1 + 1) : ℂ)) + 1))
        (fun ν => W.smul a ν c)
        (by rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ (K : ℤ) by positivity)]
            intro x hx; simp only [Finset.mem_Icc] at hx ⊢; omega)
        (by
          rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ (K : ℤ) by positivity)]
          intro μ _ hμnot; simp only [Finset.mem_Icc, not_and, not_le] at hμnot
          simp only []
          rcases lt_or_ge (μ + ((n : ℤ) - (p : ℤ) + i + 1 + 1)) 0 with hlo | hge
          · rw [cbz_apply_neg (K : ℤ) hlo, zero_mul]
          · have hgt : (K : ℤ) < μ + ((n : ℤ) - (p : ℤ) + i + 1 + 1) := by
              have := hμnot (by omega); omega
            rw [cbz_lt (by positivity) hgt, zero_mul])]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [← add_smul,
      show (ν + ((n : ℤ) - (p : ℤ) + i + 1 + 1)) = (ν + ((n : ℤ) - (p : ℤ) + i + 1) + 1) from by ring]
  congr 1
  push_cast; ring

/-- **The circle generator, reindexed** onto the common interval `Icc (−(n+2)) (K+p)`
(mode `ν = ℓ − (n+2)`). -/
private theorem circ_reindex (W : VertexOperatorAlgebra 𝒱) (n p : ℕ) {K : ℕ} {a : 𝒱}
    (ha : a ∈ W.grading (K : ℤ)) (c : 𝒱) :
    anmCirc W n 0 a c
      = ∑ ν ∈ Finset.Icc (-((n : ℤ) + 2)) ((K : ℤ) + (p : ℤ)),
          cbz (K : ℤ) (ν + (n : ℤ) + 2) • W.smul a ν c := by
  rw [anmCirc_zero, resHom_homogeneous W 0 ((n : ℤ) + 2) ha c]
  simp only [add_zero]
  rw [reindexToIccLGR ((K : ℤ).toNat) ((n : ℤ) + 2) (-((n : ℤ) + 2)) ((K : ℤ) + (p : ℤ))
        (fun t => cbz (K : ℤ) t) (fun ν => W.smul a ν c)
        (by rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ (K : ℤ) by positivity)]
            intro x hx; simp only [Finset.mem_Icc] at hx ⊢; omega)
        (by rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ (K : ℤ) by positivity)]
            intro μ _ hμnot; simp only [Finset.mem_Icc, not_and, not_le] at hμnot
            simp only []
            rcases lt_or_ge (μ + ((n : ℤ) + 2)) 0 with hlo | hge
            · rw [cbz_apply_neg (K : ℤ) hlo]
            · have hgt : (K : ℤ) < μ + ((n : ℤ) + 2) := by have := hμnot (by omega); omega
              rw [cbz_lt (by positivity) hgt])]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [show (ν + ((n : ℤ) + 2)) = (ν + (n : ℤ) + 2) from by ring]

/-- **The rest collapses to `σ_p • anmCirc`.**  For `a ∈ 𝒱_K`,
`crossLRestFull W n p K a c = ((−1)^{p+1}(n+1)C(n,p)) • anmCirc W n 0 a c`, via `restInner_reindex`,
`Finset.sum_comm`, and the per-mode telescope `lgrfull_abs_scalar`. -/
theorem crossLRestFull_eq (W : VertexOperatorAlgebra 𝒱) (n p : ℕ) {K : ℕ} {a : 𝒱}
    (ha : a ∈ W.grading (K : ℤ)) (c : 𝒱) :
    crossLRestFull W n p K a c
      = ((-1 : ℂ) ^ (p + 1) * ((n : ℂ) + 1) * cbz (n : ℤ) (p : ℤ)) • anmCirc W n 0 a c := by
  rw [crossLRestFull]
  -- reindex each inner sum onto the common interval and pull the outer weight inside.
  have h1 : ∀ i ∈ Finset.range (p + 1),
      ((-1 : ℂ) ^ i * cbz ((n : ℤ) - (p : ℤ) + i) (i : ℤ)) •
          (∑ ℓ ∈ Finset.range ((K : ℤ).toNat + 1),
            cbz (K : ℤ) (ℓ : ℤ) •
              ((((ℓ : ℤ) - ((n : ℤ) - (p : ℤ) + i + 1) : ℂ) + 1 + (n : ℂ) - (K : ℂ) - (p : ℂ)) •
                  W.smul a ((ℓ : ℤ) - ((n : ℤ) - (p : ℤ) + i + 1)) c
                + (((ℓ : ℤ) - ((n : ℤ) - (p : ℤ) + i + 1)) : ℂ) •
                  W.smul a ((ℓ : ℤ) - ((n : ℤ) - (p : ℤ) + i + 1) - 1) c))
        = ∑ ν ∈ Finset.Icc (-((n : ℤ) + 2)) ((K : ℤ) + (p : ℤ)),
            (((-1 : ℂ) ^ i * cbz ((n : ℤ) - (p : ℤ) + i) (i : ℤ)) *
              (cbz (K : ℤ) (ν + ((n : ℤ) - (p : ℤ) + i + 1))
                    * ((ν : ℂ) + 1 + (n : ℂ) - (K : ℂ) - (p : ℂ))
                + cbz (K : ℤ) (ν + ((n : ℤ) - (p : ℤ) + i + 1) + 1) * ((ν : ℂ) + 1)))
              • W.smul a ν c := by
    intro i hi
    rw [restInner_reindex W n p ha c i (by simp only [Finset.mem_range] at hi; omega),
        Finset.smul_sum]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [smul_smul]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm, circ_reindex W n p ha c, Finset.smul_sum]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [← Finset.sum_smul, smul_smul]
  congr 1
  -- the per-mode telescope.
  rw [← lgrfull_abs_scalar n p K ν]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show (ν + ((n : ℤ) - (p : ℤ) + i + 1)) = (ν + (n : ℤ) - (p : ℤ) + i + 1) from by ring,
      show (ν + (n : ℤ) - (p : ℤ) + i + 1 + 1) = (ν + (n : ℤ) - (p : ℤ) + i + 2) from by ring]
  ring

/-! ## Assembly — the general right-slot grading absorption. -/

/-- Convenience zero lemmas for the bilinear reduction. -/
private theorem anmGen_zero_left0 (W : VertexOperatorAlgebra 𝒱) (n m p : ℕ) (w : 𝒱) :
    anmGen W n m p 0 w = 0 := by
  have := anmGen_smul_left W n m p (0 : ℂ) 0 w; simpa using this

private theorem anmGen_zero_right0 (W : VertexOperatorAlgebra 𝒱) (n m p : ℕ) (u : 𝒱) :
    anmGen W n m p u 0 = 0 := by
  have := anmGen_smul_right W n m p (0 : ℂ) u 0; simpa using this

private theorem anmLgen_zero0 (W : VertexOperatorAlgebra 𝒱) (p : ℕ) :
    anmLgen W p 0 (0 : 𝒱) = 0 := by
  simp only [anmLgen, map_zero, smul_zero, add_zero]

private theorem anmLgen_add0 (W : VertexOperatorAlgebra 𝒱) (p : ℕ) (x y : 𝒱) :
    anmLgen W p 0 (x + y) = anmLgen W p 0 x + anmLgen W p 0 y := by
  simp only [anmLgen, map_add, smul_add]; abel

/-- **The homogeneous right-slot grading absorption.**  For `a ∈ 𝒱_K`, `c ∈ 𝒱_M`,
`a ∗ⁿ_{0,p} (anmLgen W p 0 c) ∈ O_{n,0}`. -/
theorem anmGen_zero_crossL_homog_gen (W : VertexOperatorAlgebra 𝒱) (n p : ℕ) {K M : ℕ} {a c : 𝒱}
    (ha : a ∈ W.grading (K : ℤ)) (hc : c ∈ W.grading (M : ℤ)) :
    anmGen W n 0 p a (anmLgen W p 0 c) ∈ Onm W n 0 := by
  rw [anmGen_zero_Lgen_right_homog_gen W n p ha hc, crossLRestFull_eq W n p ha c]
  exact (Onm W n 0).add_mem (crossLTowerFull_mem_Onm W n p K a c)
    (Submodule.smul_mem _ _ (anmCirc_mem_Onm W n 0 a c))

/-- **The general right-slot grading absorption.**  For arbitrary `a c : 𝒱`,
`a ∗ⁿ_{0,p} (anmLgen W p 0 c) ∈ O_{n,0}` — reduce `a` and `c` to homogeneous slices. -/
theorem anmGen_zero_crossL_mem_Onm (W : VertexOperatorAlgebra 𝒱) (n p : ℕ) (a c : 𝒱) :
    anmGen W n 0 p a (anmLgen W p 0 c) ∈ Onm W n 0 := by
  refine reduce_homogeneous W
    (P := fun a => anmGen W n 0 p a (anmLgen W p 0 c) ∈ Onm W n 0) ?_ ?_ ?_ a
  · intro Ka a haK
    rcases le_or_gt 0 Ka with hKnn | hKneg
    · obtain ⟨K, rfl⟩ := Int.eq_ofNat_of_zero_le hKnn
      refine reduce_homogeneous W
        (P := fun c => anmGen W n 0 p a (anmLgen W p 0 c) ∈ Onm W n 0) ?_ ?_ ?_ c
      · intro Mc c hcM
        rcases le_or_gt 0 Mc with hMnn | hMneg
        · obtain ⟨M, rfl⟩ := Int.eq_ofNat_of_zero_le hMnn
          exact anmGen_zero_crossL_homog_gen W n p haK hcM
        · have hzero : c = 0 := by
            have : c ∈ (⊥ : Submodule ℂ 𝒱) := by rw [← W.positivity Mc hMneg]; exact hcM
            simpa using this
          rw [hzero, anmLgen_zero0, anmGen_zero_right0]
          exact (Onm W n 0).zero_mem
      · show anmGen W n 0 p a (anmLgen W p 0 0) ∈ Onm W n 0
        rw [anmLgen_zero0, anmGen_zero_right0]; exact (Onm W n 0).zero_mem
      · intro x y hx hy
        rw [anmLgen_add0, anmGen_add_right]
        exact (Onm W n 0).add_mem hx hy
    · have hzero : a = 0 := by
        have : a ∈ (⊥ : Submodule ℂ 𝒱) := by rw [← W.positivity Ka hKneg]; exact haK
        simpa using this
      rw [hzero, anmGen_zero_left0]; exact (Onm W n 0).zero_mem
  · show anmGen W n 0 p 0 (anmLgen W p 0 c) ∈ Onm W n 0
    rw [anmGen_zero_left0]; exact (Onm W n 0).zero_mem
  · intro x y hx hy
    rw [anmGen_add_left]; exact (Onm W n 0).add_mem hx hy

/-- **the general right-slot grading absorption `LeftGradingResidual W n 0 p`, discharged**
(all `n p : ℕ`, unconditional).  This is the single remaining Half-B leaf of Zhu's bijection: DJ Lemma
2.5's right-factor half, `V ∗ⁿ_{0,p} O'_{p,0} ⊆ O_{n,0}`.  It unblocks `oFull`/`oFull_comp` (the M(U)
𝒱-action well-definedness) and thence the whole `MUFull → Zhu 5.3.4` bijection. -/
theorem leftGradingResidual_zero_gen (W : VertexOperatorAlgebra 𝒱) (n p : ℕ) :
    LeftGradingResidual W n 0 p :=
  ⟨fun a c => Onm_le_OnmFull W n 0 (anmGen_zero_crossL_mem_Onm W n p a c)⟩

end VOA
