/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchGradedModeVanish

/-!
# Closing the **freeness circle vanishing** `hcirc` — the depth-`n` analogue of `oMod_zhuMul_lowest`

`Modules.ZhuVermaAnArchGradedModeVanish` reduces the freeness side of Zhu Theorem 5.3.4 to a single
carried datum: the **homogeneous circle vanishing** `hcirc` consumed by
`InducedAssignment.GradedModeVanish.ofCircHomog` / `.ofCirc`,

`gMode N n (anmCirc W n 0 c d) x = 0`   for homogeneous `c ∈ 𝒱_M` and `x ∈ N_h`.

This file **proves** it: the depth-`n` analogue of the proven `n = 0`
`ZeroModeMult.oMod_zhuMul_lowest` (Gannon 5.3.9a), for any lowest-weight `𝒱`-module `N`.

## The computation (engine-mapped `certificates/mathematica/gmode_checks.wl`, `certificates/mathematica/gmode_circ_fb_depthn.wl`)

`anmCirc W n 0 c d = resHom W 0 (n+2) c d`.  On homogeneous `c ∈ 𝒱_M`, `resHom_homogeneous` gives
`anmCirc W n 0 c d = ∑_{i=0}^{M} C(M,i) · c₍ᵢ₋ₙ₋₂₎ d` (`resHom` shift `s = 0`, pole `p = n+2`).  Each
piece `c₍ᵢ₋ₙ₋₂₎ d` is homogeneous of grade `Gᵢ = M + β + (n+1) − i` (with `d ∈ 𝒱_β`), so the depth-`n`
graded mode `gMode N n` reads its slice at index `Gᵢ − 1 − n = M + β − i`:

`gMode N n (anmCirc W n 0 c d) x = ∑_{i=0}^{M} C(M,i) · (c₍ᵢ₋ₙ₋₂₎ d)₍M+β−i₎ x`.

Expand each iterate `(c₍ℓ₎ d)₍N₎ x` (with `ℓ = i−n−2`, `N = M+β−i`) by the **module iterate**
`Translation.module_iterate0`:
`(c₍ℓ₎ d)₍N₎ x = ∑ⱼ (−1)ʲ C(ℓ,j) ( c₍ℓ₋ⱼ₎ d₍N+j₎ x − (−1)^ℓ d₍ℓ+N−j₎ c₍ⱼ₎ x )`.

On the lowest-weight bottom `x ∈ N_h` (`mode_lowering_vanish`):
* **First term** `c₍ℓ₋ⱼ₎ d₍N+j₎ x` vanishes for *every* `i, j`: `d₍N+j₎ x = 0` needs `N + j ≥ β`,
  i.e. `j ≥ i − M` (after `N = M+β−i`), but `i ≤ M` forces `i − M ≤ 0 ≤ j`, so the inner `d`-mode is
  always a lowering at the realized bottom — killed **termwise** (the depth-`n` `S₁` analogue: here it
  is identically zero, no leading survivor, since the circle pole `n+2 > 1` strictly raises the order).
* **Second term** `d₍ℓ+N−j₎ c₍ⱼ₎ x`: the inner `c₍ⱼ₎ x = 0` for `j ≥ M`, leaving `0 ≤ j < M`; the
  outer index `ℓ + N − j = M + β − (n+2) − j` is **independent of `i`**.  Grouping by `j`, the `i`-sum
  coefficient is exactly `∑ᵢ (−1)ⁱ C(M,i) C(i−(n+2), j)` = `altShift_vanish (n+2) (j < M)` (`= 0`,
  proved in `ZhuVermaAnArchGradedModeVanish`).  This kills the whole second term.

Both halves match the `oMod_zhuMul_lowest` template (`S₁`/`S₂`) at depth `n`; the only new scalar input
is `altShift_vanish` (shift `c = n+2`) in place of `alt_shiftBinom_vanish` (shift `1`).

## What is proved here (axiom-clean)

* **`gMode_anmCirc_expand`** — the homogeneous expansion of `gMode N n (anmCirc W n 0 c d) x` into the
  `i`-sum of graded-mode iterates (the `oMod_zhuMul_expand` analogue).
* **`circIterate_on_lowest`** — each iterate's `M_h`-collapse to the finite `Finset.Ico 0 (M+1)`
  `i`-sum minus first/second split (`iterate_on_lowest` analogue).
* **`circS1_vanish`** — the **first** iterate term vanishes identically on `N_h` (the depth-`n`/circle
  `S₁` analogue — here *zero*, not a leading survivor).
* **`circS2_vanish`** — the **second** iterate term vanishes on `N_h` by `altShift_vanish`
  (`S2_vanish` analogue).
* **`gMode_anmCirc_homogeneous_lowest`** — `hcirc` for homogeneous `c` and `d` (the keystone).
* **`gMode_anmCirc_lowest`** — `hcirc` for homogeneous `c` and *arbitrary* `d` (drop `d`-homogeneity by
  `anmCirc`-right additivity).
* **`GradedModeVanish.ofBottom`** — the `GradedModeVanish β` constructor from the single explicit
  bottom-landing hypothesis `β u ∈ N_h` (carried, never an axiom): both per-generator vanishings are
  *proved* (circle here, grading already in `gMode_anmLgen_vanish`).  This makes the freeness side
  fully term-level.

## References
Dong–Jiang, Math. Z. 259 (2008) (`math/0601626`); DLM3 §4; H. Li hep-th/9406211 §2; Gannon §5.3.2,
Thm 5.3.4, 5.3.9a; Frenkel–Zhu Lemma 2.1.2.  `ZeroModeMult` (`oMod_zhuMul_lowest`,
`mode_lowering_vanish`, `iterate_on_lowest`, `S2_vanish`, `IsLowestWeight`), `Translation`
(`module_iterate0`), `ZhuVermaAnArchAnm` (`anmCirc`), `ZhuVermaAnBimodule` (`resHom`,
`resHom_homogeneous`), `ZhuVermaAnArchGradedModeVanish` (`gMode`, `altShift_vanish`,
`GradedModeVanish.ofCircHomog`).
-/

namespace VOA

open scoped BigOperators
open VertexOperatorAlgebra
open Module (End)

universe u v

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace InducedAssignment

namespace GradedModeVanish

section CircleVanish

variable {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M]
variable (N : OrdVModule W M)

/-! ## (A) The homogeneous expansion of the circle graded mode. -/

/-- **The homogeneous circle expansion.** For homogeneous `c ∈ 𝒱_Mc`, the depth-`n` graded mode of
the circle generator `anmCirc W n 0 c d = resHom W 0 (n+2) c d` expands as
`∑_{i=0}^{Mc} C(Mc,i) · (c₍ᵢ₋ₙ₋₂₎ d)₍Mc+β−i₎ x` whenever `d ∈ 𝒱_β`, because each piece
`c₍ᵢ₋ₙ₋₂₎ d` is homogeneous of grade `Mc+β+n+1−i`, whose depth-`n` graded mode reads its
`(Mc+β−i)`-slice.  The depth-`n`/circle analogue of `oMod_zhuMul_expand`. -/
theorem gMode_anmCirc_expand (n : ℕ) {Mc β : ℤ} {c d : 𝒱}
    (hc : c ∈ W.grading Mc) (hd : d ∈ W.grading β) (x : M) :
    gMode N n (anmCirc W n 0 c d) x
      = ∑ i ∈ Finset.range (Mc.toNat + 1),
          cbz Mc i • mode (N.YM (W.smul c ((i : ℤ) - n - 2) d)) (Mc + β - i) x := by
  unfold anmCirc
  simp only [Nat.cast_zero, add_zero]
  rw [resHom_homogeneous W (0 : ℤ) ((n : ℤ) + 2) hc d]
  -- Simplify the index/range to `s = 0`, pole `n+2`.
  simp only [add_zero, Nat.cast_zero]
  rw [map_sum, LinearMap.coeFn_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_smul, LinearMap.smul_apply]
  congr 1
  -- `c₍ᵢ₋(ₙ₊₂)₎ d ∈ 𝒱_{Mc+β−(i−n−2)−1} = 𝒱_{Mc+β+n+1−i}`, graded mode slice `= Mc+β−i`.
  have hmem : W.smul c ((i : ℤ) - ((n : ℤ) + 2)) d ∈ W.grading (Mc + β + n + 1 - i) := by
    have := W.smul_mem_grading hc hd ((i : ℤ) - ((n : ℤ) + 2))
    rwa [show (Mc + β - ((i : ℤ) - ((n : ℤ) + 2)) - 1) = Mc + β + n + 1 - i from by ring] at this
  rw [gMode_homogeneous N n hmem,
    show (Mc + β + (n : ℤ) + 1 - i - 1 - (n : ℤ)) = Mc + β - i from by ring]
  congr 1
  push_cast; ring

/-! ## (B) The iterate summands (mirrors `itT1`/`itT2`). -/

/-- The first circle-iterate summand (`c₍·₎ d₍·₎` term), at outer index `i`, inner index `j`,
with `ℓ = i−n−2`, `N = Mc+β−i`. -/
private noncomputable def cT1 (n : ℕ) (Mc β : ℤ) (c d : 𝒱) (x : M) (i j : ℤ) : M :=
  (negOnePow j * cbz ((i : ℤ) - n - 2) j) •
    mode (N.YM c) ((i : ℤ) - n - 2 - j) (mode (N.YM d) (Mc + β - i + j) x)

/-- The second circle-iterate summand (`d₍·₎ c₍·₎` term, with its sign), at outer index `i`,
inner index `j`. -/
private noncomputable def cT2 (n : ℕ) (Mc β : ℤ) (c d : 𝒱) (x : M) (i j : ℤ) : M :=
  (negOnePow j * cbz ((i : ℤ) - n - 2) j) •
    (negOnePow ((i : ℤ) - n - 2) •
      mode (N.YM d) (((i : ℤ) - n - 2) + (Mc + β - i) - j) (mode (N.YM c) j x))

/-! ## (C) The iterate collapse on the bottom. -/

variable {N}

/-- **The circle iterate's `M_h`-collapse.** For `x ∈ N_h` and homogeneous `c ∈ 𝒱_Mc`,
`d ∈ 𝒱_β`, the iterate `(c₍ᵢ₋ₙ₋₂₎ d)₍Mc+β−i₎ x` collapses to the finite `Finset.Ico 0 (Mc+1)`
`j`-sum of `cT1 − cT2`.  Mirrors `iterate_on_lowest`; here the inner `j`-support is `[0, Mc)` (the
`c₍ⱼ₎ x` lowering bound) on the second term, and the first term is identically zero on the bottom. -/
theorem circIterate_on_lowest {h : ℂ} (hcw : IsLowestWeight N h)
    {Mc β : ℤ} {c d : 𝒱} (hc : c ∈ W.grading Mc) (hd : d ∈ W.grading β)
    {x : M} (hx : x ∈ N.weight h) (hMc : 0 ≤ Mc) (n : ℕ) {i : ℤ} (hi0 : 0 ≤ i) (hiMc : i ≤ Mc) :
    mode (N.YM (W.smul c ((i : ℤ) - n - 2) d)) (Mc + β - i) x
      = ∑ j ∈ Finset.Ico (0 : ℤ) (Mc + 1),
          (cT1 N n Mc β c d x i j - cT2 N n Mc β c d x i j) := by
  rw [module_iterate0 N.toWeakModule c d x ((i : ℤ) - n - 2) (Mc + β - i)]
  -- The `module_iterate0` summand is *definitionally* `cT1 − cT2` (just `smul_sub`).
  have hbody : ∀ j : ℤ,
      (negOnePow j * cbz ((i : ℤ) - n - 2) j) •
        (mode (N.YM c) ((i : ℤ) - n - 2 - j) (mode (N.YM d) (Mc + β - i + j) x)
          - negOnePow ((i : ℤ) - n - 2) •
              mode (N.YM d) (((i : ℤ) - n - 2) + (Mc + β - i) - j) (mode (N.YM c) j x))
        = cT1 N n Mc β c d x i j - cT2 N n Mc β c d x i j := by
    intro j; unfold cT1 cT2; rw [smul_sub]
  rw [finsum_congr hbody]
  -- Bound the support of `cT1 − cT2` by `Ico 0 (Mc+1)`.
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.Ico (0 : ℤ) (Mc + 1)) ?_]
  intro j hj
  simp only [Function.mem_support] at hj
  simp only [Finset.coe_Ico, Set.mem_Ico]
  by_contra hcon
  push_neg at hcon
  apply hj
  rcases lt_or_ge j 0 with hjneg | hjpos
  · unfold cT1 cT2
    rw [cbz_apply_neg ((i : ℤ) - n - 2) hjneg, mul_zero, zero_smul, zero_smul, sub_zero]
  · -- `j ≥ Mc+1`: both first-term inner `d`-mode and second-term inner `c₍ⱼ₎ x` vanish.
    have hjMc : Mc + 1 ≤ j := hcon hjpos
    have hT1 : mode (N.YM d) (Mc + β - i + j) x = 0 := by
      apply mode_lowering_vanish N hcw hd hx; omega
    have hT2 : mode (N.YM c) j x = 0 := by
      apply mode_lowering_vanish N hcw hc hx; omega
    unfold cT1 cT2
    rw [hT1, map_zero, hT2, map_zero, smul_zero, smul_zero, smul_zero, sub_zero]

/-! ## (D) The two term-vanishings. -/

/-- **The first circle-iterate term vanishes identically on `N_h`.** For every `i ≤ Mc` and every
`j ≥ 0`, the inner `d₍Mc+β−i+j₎ x` is a lowering at the bottom (`Mc+β−i+j ≥ β` since `j ≥ i − Mc`
and `i ≤ Mc`), hence `= 0`.  The depth-`n`/circle analogue of the `S₁` term — here *zero* (no leading
survivor, because the circle pole `n+2 > 1` strictly raises the inner `d`-mode index). -/
theorem circS1_vanish {h : ℂ} (hcw : IsLowestWeight N h)
    {Mc β : ℤ} {c d : 𝒱} (hc : c ∈ W.grading Mc) (hd : d ∈ W.grading β)
    {x : M} (hx : x ∈ N.weight h) (hMc : 0 ≤ Mc) (n : ℕ) :
    ∑ i ∈ Finset.range (Mc.toNat + 1),
        cbz Mc i • ∑ j ∈ Finset.Ico (0 : ℤ) (Mc + 1), cT1 N n Mc β c d x i j = 0 := by
  refine Finset.sum_eq_zero (fun i hi => ?_)
  simp only [Finset.mem_range] at hi
  have hiMc : (i : ℤ) ≤ Mc := by
    have : (i : ℤ) < (Mc.toNat : ℤ) + 1 := by exact_mod_cast hi
    rw [Int.toNat_of_nonneg hMc] at this; omega
  rw [Finset.sum_eq_zero (fun j hj => ?_), smul_zero]
  simp only [Finset.mem_Ico] at hj
  unfold cT1
  -- `d₍Mc+β−i+j₎ x = 0`: index `≥ β`.
  have hvan : mode (N.YM d) (Mc + β - i + j) x = 0 := by
    apply mode_lowering_vanish N hcw hd hx; omega
  rw [hvan, map_zero, smul_zero]

/-- **The second circle-iterate term vanishes on `N_h`** by `altShift_vanish`.  The inner `c₍ⱼ₎ x`
forces `0 ≤ j < Mc`; the outer `d`-index `ℓ + N − j = Mc + β − (n+2) − j` is **independent of `i`**, so
grouping by `j` leaves the pure scalar `i`-sum `∑ᵢ (−1)ⁱ C(Mc,i) C(i−(n+2), j)`, which is
`altShift_vanish (n+2)` (`= 0` for `j < Mc`).  The depth-`n`/circle analogue of `S2_vanish`. -/
theorem circS2_vanish {h : ℂ} (hcw : IsLowestWeight N h)
    {Mc β : ℤ} {c d : 𝒱} (hc : c ∈ W.grading Mc) (hd : d ∈ W.grading β)
    {x : M} (hx : x ∈ N.weight h) (hMc : 0 ≤ Mc) (n : ℕ) :
    ∑ i ∈ Finset.range (Mc.toNat + 1),
        cbz Mc i • ∑ j ∈ Finset.Ico (0 : ℤ) (Mc + 1), cT2 N n Mc β c d x i j = 0 := by
  -- Pull `cbz Mc i` inside; drop the `j = Mc` term (`c₍Mc₎ x = 0`); rewrite outer `d`-index.
  have hrw : ∀ i ∈ Finset.range (Mc.toNat + 1),
      cbz Mc i • ∑ j ∈ Finset.Ico (0 : ℤ) (Mc + 1), cT2 N n Mc β c d x i j
        = ∑ j ∈ Finset.Ico (0 : ℤ) Mc,
            (cbz Mc i * (negOnePow j * cbz ((i : ℤ) - n - 2) j)
              * negOnePow ((i : ℤ) - n - 2)) •
              mode (N.YM d) (Mc + β - (n + 2) - j) (mode (N.YM c) j x) := by
    intro i hi
    rw [Finset.smul_sum]
    rw [show Finset.Ico (0 : ℤ) (Mc + 1) = insert Mc (Finset.Ico (0 : ℤ) Mc) from by
      ext k; simp only [Finset.mem_Ico, Finset.mem_insert]; omega]
    rw [Finset.sum_insert (by simp)]
    have hcMc : mode (N.YM c) Mc x = 0 := mode_lowering_vanish N hcw hc hx (le_refl Mc)
    have hzero : cbz Mc i • cT2 N n Mc β c d x i Mc = 0 := by
      unfold cT2
      rw [hcMc, map_zero, smul_zero, smul_zero, smul_zero]
    rw [hzero, zero_add]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    unfold cT2
    rw [smul_smul, smul_smul,
      show (((i : ℤ) - n - 2) + (Mc + β - i) - j) = Mc + β - (n + 2) - j from by push_cast; ring]
  rw [Finset.sum_congr rfl hrw]
  -- Swap the order of summation: outer `j`, inner `i`.
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero (fun j hj => ?_)
  simp only [Finset.mem_Ico] at hj
  rw [← Finset.sum_smul]
  -- The `i`-sum coefficient factors as `± · (∑ᵢ (−1)ⁱ C(Mc,i) C(i−(n+2), j))`.
  have hscal : (∑ i ∈ Finset.range (Mc.toNat + 1),
      cbz Mc i * (negOnePow j * cbz ((i : ℤ) - n - 2) j) * negOnePow ((i : ℤ) - n - 2))
      = (negOnePow j * negOnePow (-(n : ℤ) - 2)) *
          ∑ i ∈ Finset.range (Mc.toNat + 1),
            negOnePow (i : ℤ) * cbz Mc i * cbz ((i : ℤ) - ((n : ℤ) + 2)) j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    -- `(−1)^{i−n−2} = (−1)^i · (−1)^{−n−2}`.
    have hsplit : negOnePow ((i : ℤ) - n - 2) = negOnePow (i : ℤ) * negOnePow (-(n : ℤ) - 2) := by
      rw [show ((i : ℤ) - n - 2) = (i : ℤ) + (-(n : ℤ) - 2) from by ring, negOnePow_add]
    rw [hsplit, show ((i : ℤ) - (n : ℤ) - 2) = (i : ℤ) - ((n : ℤ) + 2) from by ring]
    ring
  rw [hscal]
  -- The bracketed `i`-sum is `altShift_vanish` (shift `c = n+2`) at `j < Mc`.
  have hjMc : j < Mc := hj.2
  have hkey : (∑ i ∈ Finset.range (Mc.toNat + 1),
      negOnePow (i : ℤ) * cbz Mc i * cbz ((i : ℤ) - ((n : ℤ) + 2)) j) = 0 := by
    have hcast : Mc = (Mc.toNat : ℤ) := (Int.toNat_of_nonneg hMc).symm
    have hjcast : j = (j.toNat : ℤ) := (Int.toNat_of_nonneg hj.1).symm
    have hav := altShift_vanish ((n : ℤ) + 2) (M := Mc.toNat) (j := j.toNat)
      (by rw [hcast, hjcast] at hjMc; exact_mod_cast hjMc)
    -- Re-cast the sum back to the `ℤ`-indexed `Mc`, `j`.
    rw [← hcast] at hav
    -- The `cbz … j.toNat` in `hav` must be rewritten to `cbz … j`.
    rw [show (j.toNat : ℤ) = j from hjcast.symm] at hav
    convert hav using 2
  rw [hkey, mul_zero, zero_smul]

/-! ## (E) The homogeneous circle vanishing (the keystone `hcirc`). -/

/-- **The homogeneous circle vanishing — `hcirc`.** For homogeneous `c ∈ 𝒱_Mc`, `d ∈ 𝒱_β`
(`Mc, β ≥ 0`) and `x` in the lowest-weight bottom `N_h` (`IsLowestWeight N h`),
`gMode N n (anmCirc W n 0 c d) x = 0`.  The depth-`n`/circle analogue of `oMod_zhuMul_lowest`:
expand (`gMode_anmCirc_expand`), collapse each iterate on the bottom (`circIterate_on_lowest`),
split into the two terms — `circS1_vanish` kills the first (identically), `circS2_vanish` kills the
second (via `altShift_vanish`). -/
theorem gMode_anmCirc_homogeneous_lowest {h : ℂ} (hcw : IsLowestWeight N h)
    {Mc β : ℤ} {c d : 𝒱} (hc : c ∈ W.grading Mc) (hd : d ∈ W.grading β)
    {x : M} (hx : x ∈ N.weight h) (hMc : 0 ≤ Mc) (n : ℕ) :
    gMode N n (anmCirc W n 0 c d) x = 0 := by
  rw [gMode_anmCirc_expand N n hc hd x]
  have hstep : ∀ i ∈ Finset.range (Mc.toNat + 1),
      cbz Mc i • mode (N.YM (W.smul c ((i : ℤ) - n - 2) d)) (Mc + β - i) x
        = cbz Mc i • ∑ j ∈ Finset.Ico (0 : ℤ) (Mc + 1), cT1 N n Mc β c d x i j
          - cbz Mc i • ∑ j ∈ Finset.Ico (0 : ℤ) (Mc + 1), cT2 N n Mc β c d x i j := by
    intro i hi
    simp only [Finset.mem_range] at hi
    have hi0 : (0 : ℤ) ≤ i := Int.ofNat_nonneg i
    have hiMc : (i : ℤ) ≤ Mc := by
      have : (i : ℤ) < (Mc.toNat : ℤ) + 1 := by exact_mod_cast hi
      rw [Int.toNat_of_nonneg hMc] at this; omega
    rw [circIterate_on_lowest hcw hc hd hx hMc n hi0 hiMc,
      Finset.sum_sub_distrib, smul_sub]
  rw [Finset.sum_congr rfl hstep, Finset.sum_sub_distrib,
    circS1_vanish hcw hc hd hx hMc n, circS2_vanish hcw hc hd hx hMc n, sub_zero]

/-- **The homogeneous-`c` circle vanishing for arbitrary `d`.**  Drops homogeneity of `d` from
`gMode_anmCirc_homogeneous_lowest` by `iSup`-induction over the grade decomposition of `d`
(`anmCirc` is right-additive/homogeneous and `gMode` is ℂ-linear).  This is exactly the homogeneous
datum `hcirc` consumed by `GradedModeVanish.ofCircHomog`. -/
theorem gMode_anmCirc_lowest {h : ℂ} (hcw : IsLowestWeight N h)
    {Mc : ℤ} {c : 𝒱} (hc : c ∈ W.grading Mc) {x : M} (hx : x ∈ N.weight h)
    (hMc : 0 ≤ Mc) (n : ℕ) (d : 𝒱) :
    gMode N n (anmCirc W n 0 c d) x = 0 := by
  have hdtop : d ∈ ⨆ i, W.grading i := by
    rw [W.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
  refine Submodule.iSup_induction W.grading
    (motive := fun d => gMode N n (anmCirc W n 0 c d) x = 0) hdtop ?_ ?_ ?_
  · -- homogeneous `y ∈ 𝒱_β`; the homogeneous lemma needs no sign of `β` (mode-lowering only uses
    -- `β ≤ index`, valid for any integer `β`).
    intro β y hy
    exact gMode_anmCirc_homogeneous_lowest hcw hc hy hx hMc n
  · change gMode N n (anmCirc W n 0 c (0 : 𝒱)) x = 0
    have h0 : anmCirc W n 0 c (0 : 𝒱) = 0 := by
      have := anmCirc_smul_right W n 0 (0 : ℂ) c (0 : 𝒱)
      rwa [zero_smul, zero_smul] at this
    rw [h0, map_zero, LinearMap.zero_apply]
  · intro y z hy hz
    change gMode N n (anmCirc W n 0 c (y + z)) x = 0
    rw [anmCirc_add_right, map_add, LinearMap.add_apply, hy, hz, add_zero]

end CircleVanish

/-! ## (F) The `GradedModeVanish` constructor from the bottom-landing hypothesis. -/

variable {W : VertexOperatorAlgebra 𝒱}

/-- **`GradedModeVanish β` from the single bottom-landing hypothesis.**  Given a bottom map
`β : U.carrier →ₗ[ℂ] P.carrier` that lands in the realized bottom `P_h` (the single explicit
hypothesis `hβ : ∀ u, β u ∈ P.isMod.weight P.h`, carried — never an axiom), this assembles a full
`GradedModeVanish β`.

Both per-generator vanishings are **proved** (no carried `hcirc`):
* the **circle** field is `gMode_anmCirc_lowest` (this file), the depth-`n` analogue of
  `oMod_zhuMul_lowest`, applied through `ofCircHomog` after reducing `c` to homogeneous; and
* the **grading** field is the unconditional `gMode_anmLgen_vanish`.

This closes the freeness circle vanishing and makes the freeness side fully term-level: the only datum
that remains carried anywhere is the realization `β u ∈ P_h`, which holds by construction of the bottom
embedding (`LWModule.realized`). -/
def ofBottom {U : AMod W} {P : LWModule W} (β : U.carrier →ₗ[ℂ] P.carrier)
    (hβ : ∀ u : U.carrier, β u ∈ P.isMod.weight P.h) :
    GradedModeVanish β :=
  ofCircHomog β (fun n k c d hc u => by
    rcases lt_or_ge k 0 with hkneg | hkpos
    · -- `k < 0`: VOA positivity gives `𝒱_k = ⊥`, so `c = 0` and the circle generator is `0`
      -- (exactly the `W.positivity` collapse used in `oMod_zhuMul_lowest_all`).
      rw [W.positivity k hkneg, Submodule.mem_bot] at hc
      subst hc
      have h0 : anmCirc W n 0 (0 : 𝒱) d = 0 := by
        have := anmCirc_smul_left W n 0 (0 : ℂ) (0 : 𝒱) d
        rwa [zero_smul, zero_smul] at this
      rw [h0, map_zero, LinearMap.zero_apply]
    · exact gMode_anmCirc_lowest P.isLow hc (hβ u) (by omega) n d)

end GradedModeVanish

end InducedAssignment

end VOA

-- Axiom check (axiom-clean: [propext, Classical.choice, Quot.sound]).
