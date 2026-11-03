/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchZeroModeLaw
import VOA.Modules.ZhuVermaAnArchCollapseAssoc

/-!
# B1 — the annihilation half of the `(0,0)` gate, unconditionally

`PHASE4_PLAN` §2 splits the Dong–Jiang gate `O_{0,0}(𝒱) ≤ O(𝒱)` into B1 (annihilation), B2
(realization) and B3 (regular-module instantiation), and `PHASE4_PLAN` C-7 reduces B1 to the two
sharp statements

* **(B1-assoc)** `X₍wt X − 1 − p₃₎ w = 0` for `X = assocInner W p₁ p₂ p₃ a b c` and `w` a bottom
  vector, and
* **(B1-level)** `Z₍wt Z − 1 + p₎` annihilates every level-`p` vector, for `Z = a *⁰_{p,p} g` with
  `g ∈ O_p(𝒱)`.

This file **proves both**, and with them the whole of B1: `gateAnnihilationLev_holds`.

## The route

`ZhuVermaAnArchZeroModeLaw` proved the zero-mode law on the bottom `Ω(M)` of a *weak* module, and
recorded that the law and Dong–Jiang **Lemma 4.1** (`DJCompositionLev`) are different statements,
coinciding only at `n = m = 0` (`djCompositionLev_base`): the law is a `D = 0` statement whose inner
mode is `v₍wt v − 1 − (p−n)₎`, whereas Lemma 4.1 is a `D = m − n` statement on `M(m)` whose inner
mode is `v₍wt v − 1 + m − p₎`.

The gap is closed here.  The `u`-outside expansion `oLevW_resHom_uOutside` was *already* proved at
general `(D, s, m)` in `ZhuVermaAnArchGate`; what blocked the level-`m` law was only that the two
scalar collapses of `ZhuVermaAnArchZeroModeLaw` were stated with the hypothesis `0 ≤ d` on the
`u`-mode offset, whereas on `M(m)` the surviving offsets are `d ≥ D − m = −n`.  Both collapses are
re-proved here on exactly that larger range:

* `zeroModeCoeff_collapse_range` — `0 ≤ d` is replaced by a *range* hypothesis on the inner
  summation window (the window `Ico 0 (m+s−q+2−D)` produced by `oLevW_resHom_uOutside` covers the
  `cbz`-support precisely when `d ≥ D − m`);
* `zeroModeOuter_collapse_low` — `0 ≤ d` is replaced by the sharp `e − p ≤ d`, i.e. `−n ≤ d`.

Beyond that range the second collapse is **false** (e.g. `m = n = p = 0`, `d = −1` gives `1 ≠ 0`),
which is exactly why the level-`m` law needs `w ∈ M(m)` and not merely `w ∈ Ω(M)`.

## Main results (all proved, no `sorry`, no axiom, no carried hypothesis)

* `oLevW_resHom_law_lev` — the level-`m` residue law: for `0 ≤ m ≤ s`, `D ≤ m` and `w ∈ M(m)`,
  `o_D(Res_z (1+z)^{wt u+s} z^{−q} Y(u,z)v) w = ∑_{d ≥ D−m} C(s−d, s−q+1−d) u₍k−1+d₎ v₍l−1−d+D₎ w`.
* `oLevW_anmGen_law_lev` — **Dong–Jiang Lemma 4.1** (`refs/dj.txt`:1187):
  `o_{n,m}(a *ⁿ_{m,p} b) w = o_{n,p}(a) o_{p,m}(b) w` for `w ∈ M(m)`, with
  `o_{n,m}(u) w = u₍wt u + m − n − 1₎ w`.  Its two specialisations `p = m` and `p = n` are
  **Dong–Jiang Corollary 4.2** (`oLevW_anmRight_law_lev`, `oLevW_anmGenBar_law_lev`).
* `djCompositionLev_holds : DJCompositionLev W` — the named hypothesis of `ZhuVermaAnArchGate`
  is a THEOREM.  Consequently `djComposition_holds : DJComposition W`.
* `b1AssocInner_holds : B1AssocInner W` and `b1Level_holds : B1Level W` — the two sharp
  statements of `PHASE4_PLAN` C-7, at every depth `p₃` (the `p₃ = 0` case is not special here).
* `gateAnnihilationLev_holds : GateAnnihilationLev W` — **B1**, unconditional:
  every element of the full Dong–Jiang ideal `O_{0,0}(𝒱)` has zero mode annihilating the bottom
  level of every non-negatively levelled weak module.  Hence `gateAnnihilation_holds`.
* `gate_of_dlm3` / `downstream_of_dlm3` — the `(0,0)` gate rests on **two** named inputs
  (`BottomProjection` and `DefectPairsToZero`, both Dong–Li–Mason §4 at `n = 0`) instead of three:
  `DJCompositionLev` has been discharged.

## What is NOT claimed

The gate itself is **not** proved: B2 (`BottomProjection` + `DefectPairsToZero`) is untouched.  Nothing here uses PBW, `finrank`, `L₀`-semisimplicity, or any
grading of the module beyond the bare `AdmLev` level family.
-/

namespace VOA

open VertexOperatorAlgebra
open Module (End)
open scoped BigOperators

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## (1) The two scalar collapses on the enlarged offset range

Both are the `ZhuVermaAnArchZeroModeLaw` collapses with the hypothesis `0 ≤ d` removed.  The proofs
are the same Vandermonde convolutions; only the support bookkeeping changes. -/

/-- **First Vandermonde collapse, range form.**  For *every* offset `d` — no sign condition — the
inner `i`-sum of the `u`-outside expansion collapses to the single generalized binomial
`C(s−d, s−q+1−d)`, provided the summation window `Ico 0 E` covers the `cbz`-support, i.e.
`E ≥ s − q + 2 − d`.  (`zeroModeCoeff_collapse` is the case `E = s − q + 2`, `0 ≤ d`.) -/
theorem zeroModeCoeff_collapse_range {k s : ℤ} (hk : 0 ≤ k) (hs : 0 ≤ s) (q : ℤ) {d E : ℤ}
    (hE : s - q + 2 - d ≤ E) :
    (∑ i ∈ Finset.Ico (0 : ℤ) E,
        cbz (k + s) (d + (q + i + k - 1)) * (negOnePow i * cbz (d + (q + i + k - 1) - q) i))
      = cbz (s - d) (s - q + 1 - d) := by
  classical
  have hks : (0 : ℤ) ≤ k + s := by omega
  have hcast : (((k + s).toNat : ℕ) : ℤ) = k + s := Int.toNat_of_nonneg hks
  have hterm : ∀ i : ℤ,
      cbz (k + s) (d + (q + i + k - 1)) * (negOnePow i * cbz (d + (q + i + k - 1) - q) i)
        = cbz (-k - d) i * cbz (k + s) ((s - q + 1 - d) - i) := by
    intro i
    rcases lt_or_ge i 0 with hi | hi
    · rw [cbz_apply_neg _ hi, cbz_apply_neg (-k - d) hi, mul_zero, zero_mul, mul_zero]
    · obtain ⟨I, rfl⟩ : ∃ I : ℕ, i = (I : ℤ) := ⟨i.toNat, by omega⟩
      have halt : negOnePow (I : ℤ) * cbz (d + (q + (I : ℤ) + k - 1) - q) (I : ℤ)
          = cbz (-k - d) (I : ℤ) := by
        rw [negOnePow_natCast, show d + (q + (I : ℤ) + k - 1) - q = (k - 1 + d) + (I : ℤ) from by
          ring, alt_cbz_eq (k - 1 + d) I, show -(k - 1 + d) - 1 = -k - d from by ring]
      rw [halt, show cbz (k + s) (d + (q + (I : ℤ) + k - 1))
            = cbz (((k + s).toNat : ℕ) : ℤ) (d + (q + (I : ℤ) + k - 1)) from by rw [hcast],
        ZhuMu.cbz_symm, hcast,
        show k + s - (d + (q + (I : ℤ) + k - 1)) = (s - q + 1 - d) - (I : ℤ) from by ring, mul_comm]
  rw [Finset.sum_congr rfl (fun i _ => hterm i)]
  have hsupp : (Function.support
      (fun i : ℤ => cbz (-k - d) i * cbz (k + s) ((s - q + 1 - d) - i)))
        ⊆ ↑(Finset.Ico (0 : ℤ) E) := by
    intro i hi
    simp only [Function.mem_support] at hi
    simp only [Finset.coe_Ico, Set.mem_Ico]
    constructor
    · by_contra h
      exact hi (by rw [cbz_apply_neg (-k - d) (by omega), zero_mul])
    · by_contra h
      exact hi (by rw [cbz_apply_neg (k + s) (by omega), mul_zero])
  rw [← finsum_eq_sum_of_support_subset _ hsupp,
    show (∑ᶠ i : ℤ, cbz (-k - d) i * cbz (k + s) ((s - q + 1 - d) - i))
      = cbzConvol (-k - d) (k + s) (s - q + 1 - d) from rfl,
    cbz_vandermonde, show -k - d + (k + s) = s - d from by ring]

/-- **Second Vandermonde collapse, sharp low bound.**  The outer Dong–Jiang weights sum to the
Kronecker delta `C(e−1−d, e−d)` for every offset `d ≥ e − p`; with `e = p − n` this is exactly
`d ≥ −n`, the range of offsets that survive on the level-`m` piece.

The bound is SHARP: at `m = e = p = 0` and `d = −1` the left-hand side is `1` while
`C(e−1−d, e−d) = C(0,1) = 0`. -/
theorem zeroModeOuter_collapse_low {m e : ℤ} (p : ℕ) {d : ℤ} (hd : e - (p : ℤ) ≤ d) :
    (∑ t ∈ Finset.range (p + 1),
        ((-1 : ℂ) ^ t * cbz (m - e + (t : ℤ)) (t : ℤ)) * cbz (m - d) (e - (t : ℤ) - d))
      = cbz (e - 1 - d) (e - d) := by
  classical
  have hterm : ∀ t : ℕ,
      ((-1 : ℂ) ^ t * cbz (m - e + (t : ℤ)) (t : ℤ)) * cbz (m - d) (e - (t : ℤ) - d)
        = cbz (e - m - 1) (t : ℤ) * cbz (m - d) ((e - d) - (t : ℤ)) := by
    intro t
    rw [alt_cbz_eq (m - e) t, show -(m - e) - 1 = e - m - 1 from by ring,
      show e - (t : ℤ) - d = (e - d) - (t : ℤ) from by ring]
  rw [Finset.sum_congr rfl (fun t _ => hterm t),
    range_sum_eq_finsumZ (p + 1) (fun t : ℤ => cbz (e - m - 1) t * cbz (m - d) ((e - d) - t))
      (by
        intro x hx
        dsimp only
        rcases hx with hx | hx
        · rw [cbz_apply_neg (e - m - 1) hx, zero_mul]
        · have hxp : ((p + 1 : ℕ) : ℤ) = (p : ℤ) + 1 := by push_cast; ring
          rw [cbz_apply_neg (m - d) (by omega : e - d - x < 0), mul_zero]),
    show (∑ᶠ t : ℤ, cbz (e - m - 1) t * cbz (m - d) ((e - d) - t))
      = cbzConvol (e - m - 1) (m - d) (e - d) from rfl,
    cbz_vandermonde, show e - m - 1 + (m - d) = e - 1 - d from by ring]

/-! ## (2) Reindexing with an arbitrary lower cut -/

/-- **The reindexing step with a lower cut.**  The `ZhuVermaAnArchZeroModeLaw` reindexing
(`sum_reindex_cbz`) with the vanishing threshold `0` replaced by an arbitrary `Lo`: on the level-`m`
piece the offsets die only below `D − m`, not below `0`. -/
private theorem sum_reindex_cbz_lo {N : Type*} [AddCommMonoid N] [Module ℂ N] {P : ℤ} (hP : 0 ≤ P)
    (c Lo E : ℤ) (f : ℤ → ℂ) (T : ℤ → N) (hT : ∀ d : ℤ, d < Lo → T d = 0)
    (hhi : ∀ d : ℤ, E ≤ d → P < d + c) :
    (∑ j ∈ Finset.range (P.toNat + 1), (cbz P (j : ℤ) * f (j : ℤ)) • T ((j : ℤ) - c))
      = ∑ d ∈ Finset.Ico Lo E, (cbz P (d + c) * f (d + c)) • T d := by
  classical
  have hcast : ((P.toNat : ℕ) : ℤ) = P := Int.toNat_of_nonneg hP
  rw [range_sum_eq_finsumZ (P.toNat + 1) (fun j : ℤ => (cbz P j * f j) • T (j - c)) (by
      intro x hx
      dsimp only
      rcases hx with hx | hx
      · rw [cbz_apply_neg P hx, zero_mul, zero_smul]
      · have : ((P.toNat + 1 : ℕ) : ℤ) = P + 1 := by push_cast [hcast]; ring
        rw [cbz_lt hP (by omega : P < x), zero_mul, zero_smul]),
    ← finsumZ_shift (fun j : ℤ => (cbz P j * f j) • T (j - c)) c,
    show (fun d : ℤ => (cbz P (d + c) * f (d + c)) • T (d + c - c))
        = (fun d : ℤ => (cbz P (d + c) * f (d + c)) • T d) from
      funext (fun d => by rw [add_sub_cancel_right])]
  refine finsum_eq_sum_of_support_subset _ ?_
  intro d hd
  simp only [Function.mem_support] at hd
  simp only [Finset.coe_Ico, Set.mem_Ico]
  constructor
  · by_contra h
    exact hd (by rw [hT d (by omega), smul_zero])
  · by_contra h
    exact hd (by rw [cbz_lt hP (hhi d (by omega)), zero_mul, zero_smul])

/-! ## (3) The level-`m` residue law and Dong–Jiang Lemma 4.1 -/

section Lemma41

variable {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M]
variable {A : WeakModule W M}

/-- **The residue law on the level-`m` piece.**  For `0 ≤ m ≤ s`, every level shift `D`,
homogeneous `u ∈ 𝒱ₖ` (`k ≥ 0`), `v ∈ 𝒱ₗ` and `w ∈ M(m)`,

`o_D(Res_z (1+z)^{wt u+s} z^{−q} Y(u,z)v) w = ∑_{d ≥ D−m} C(s−d, s−q+1−d) · u₍ₖ₋₁₊d₎ v₍ₗ₋₁₋d₊D₎ w`.

The whole `v`-outside Jacobi family has already cancelled in `oLevW_resHom_uOutside` (proved, at
general `(D,s,m)`); the `u`-outside family Vandermonde-collapses offset by offset by
`zeroModeCoeff_collapse_range`.  Offsets `d < D − m` are absent because their `v`-mode index
`l−1−d+D` reaches `l + m`, which kills `M(m)`.

This is the exact level-`m` mirror of `oOmega_resHom_law`, which is its `(m, D) = (0,0)` case. -/
theorem oLevW_resHom_law_lev (L : AdmLev W A) (D s m : ℤ) (hm0 : 0 ≤ m) (hms : m ≤ s)
    (q : ℤ) {k l : ℤ} (hk : 0 ≤ k) {u v : 𝒱} (hu : u ∈ W.grading k)
    (hv : v ∈ W.grading l) {w : M} (hw : w ∈ L.lev m) :
    oLevW A D (resHom W s q u v) w
      = ∑ d ∈ Finset.Ico (D - m) (s - q + 2),
          cbz (s - d) (s - q + 1 - d) •
            mode (A.YM u) (k - 1 + d) (mode (A.YM v) (l - 1 - d + D) w) := by
  classical
  rw [oLevW_resHom_uOutside L D s m hm0 hms q hk hu hv hw, Finset.sum_comm]
  have hstep : ∀ i ∈ Finset.Ico (0 : ℤ) (m + s - q + 2 - D),
      (∑ j ∈ Finset.range ((k + s).toNat + 1),
          (cbz (k + s) (j : ℤ) * (negOnePow i * cbz ((j : ℤ) - q) i)) •
            mode (A.YM u) ((j : ℤ) - q - i)
              (mode (A.YM v) (k + l - ((j : ℤ) - q) - 2 + D + i) w))
        = ∑ d ∈ Finset.Ico (D - m) (s - q + 2),
            (cbz (k + s) (d + (q + i + k - 1)) *
                (negOnePow i * cbz (d + (q + i + k - 1) - q) i)) •
              mode (A.YM u) (k - 1 + d) (mode (A.YM v) (l - 1 - d + D) w) := by
    intro i hi
    simp only [Finset.mem_Ico] at hi
    have hkey := sum_reindex_cbz_lo (P := k + s) (by omega) (q + i + k - 1) (D - m) (s - q + 2)
      (fun x : ℤ => negOnePow i * cbz (x - q) i)
      (fun d : ℤ => mode (A.YM u) (k - 1 + d) (mode (A.YM v) (l - 1 - d + D) w))
      (fun d hd => by
        dsimp only
        rw [modeW_vanish_of_lev L hv hw (n := l - 1 - d + D) (by omega), map_zero])
      (fun d hd => by omega)
    refine Eq.trans ?_ hkey
    refine Finset.sum_congr rfl (fun j _ => ?_)
    dsimp only
    rw [show k - 1 + ((j : ℤ) - (q + i + k - 1)) = (j : ℤ) - q - i from by ring,
      show l - 1 - ((j : ℤ) - (q + i + k - 1)) + D
        = k + l - ((j : ℤ) - q) - 2 + D + i from by ring]
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  simp only [Finset.mem_Ico] at hd
  rw [← Finset.sum_smul, zeroModeCoeff_collapse_range hk (by omega) q (by omega)]

/-- **Dong–Jiang Lemma 4.1, homogeneous slots** (`math/0601626`, p. 15).  For `w ∈ M(m)`,

`o_{n,m}(u *ⁿ_{m,p} v) w = u₍ₖ₋₁₊(p−n)₎ v₍ₗ₋₁₊(m−p)₎ w`.

The outer Dong–Jiang weights collapse to a Kronecker delta at the offset `d = e = p − n`
(`zeroModeOuter_collapse_low`, applicable because every surviving offset satisfies
`d ≥ D − m = −n = e − p`). -/
theorem oLevW_anmGen_law_lev_homog (L : AdmLev W A) (n m p : ℕ) {k l : ℤ} (hk : 0 ≤ k) {u v : 𝒱}
    (hu : u ∈ W.grading k) (hv : v ∈ W.grading l) {w : M} (hw : w ∈ L.lev (m : ℤ)) :
    oLevW A ((m : ℤ) - (n : ℤ)) (anmGen W n m p u v) w
      = mode (A.YM u) (k - 1 + ((p : ℤ) - (n : ℤ)))
          (mode (A.YM v) (l - 1 + ((m : ℤ) - (p : ℤ))) w) := by
  classical
  set e : ℤ := (p : ℤ) - (n : ℤ) with he
  set Tf : ℤ → M := fun d =>
    mode (A.YM u) (k - 1 + d) (mode (A.YM v) (l - 1 - d + ((m : ℤ) - (n : ℤ))) w) with hTf
  rw [anmGen, map_sum, LinearMap.coe_sum, Finset.sum_apply]
  have hterm : ∀ t ∈ Finset.range (p + 1),
      (oLevW A ((m : ℤ) - (n : ℤ))
          (((-1 : ℂ) ^ t * cbz ((m : ℤ) + (n : ℤ) - (p : ℤ) + (t : ℤ)) (t : ℤ))
            • resHom W (m : ℤ) ((m : ℤ) + (n : ℤ) - (p : ℤ) + (t : ℤ) + 1) u v)) w
        = ∑ d ∈ Finset.Ico (-(n : ℤ)) (e + 1),
            (((-1 : ℂ) ^ t * cbz ((m : ℤ) - e + (t : ℤ)) (t : ℤ))
              * cbz ((m : ℤ) - d) (e - (t : ℤ) - d)) • Tf d := by
    intro t _
    rw [map_smul, LinearMap.smul_apply,
      oLevW_resHom_law_lev L ((m : ℤ) - (n : ℤ)) (m : ℤ) (m : ℤ) (Int.natCast_nonneg m) le_rfl
        ((m : ℤ) + (n : ℤ) - (p : ℤ) + (t : ℤ) + 1) hk hu hv hw,
      show (m : ℤ) - (n : ℤ) - (m : ℤ) = -(n : ℤ) from by ring,
      show (m : ℤ) - ((m : ℤ) + (n : ℤ) - (p : ℤ) + (t : ℤ) + 1) + 2 = e - (t : ℤ) + 1 from by
        rw [he]; ring,
      Finset.smul_sum]
    have hcoef : ∀ d : ℤ,
        ((-1 : ℂ) ^ t * cbz ((m : ℤ) + (n : ℤ) - (p : ℤ) + (t : ℤ)) (t : ℤ)) •
            (cbz ((m : ℤ) - d)
              ((m : ℤ) - ((m : ℤ) + (n : ℤ) - (p : ℤ) + (t : ℤ) + 1) + 1 - d) • Tf d)
          = (((-1 : ℂ) ^ t * cbz ((m : ℤ) - e + (t : ℤ)) (t : ℤ))
              * cbz ((m : ℤ) - d) (e - (t : ℤ) - d)) • Tf d := by
      intro d
      rw [smul_smul,
        show (m : ℤ) - ((m : ℤ) + (n : ℤ) - (p : ℤ) + (t : ℤ) + 1) + 1 - d
          = e - (t : ℤ) - d from by rw [he]; ring,
        show (m : ℤ) + (n : ℤ) - (p : ℤ) + (t : ℤ) = (m : ℤ) - e + (t : ℤ) from by rw [he]; ring]
    rw [Finset.sum_congr rfl (fun d _ => hcoef d)]
    refine Finset.sum_subset (Finset.Ico_subset_Ico le_rfl (by omega)) (fun d hd hd' => ?_)
    simp only [Finset.mem_Ico, not_and, not_lt] at hd hd'
    rw [cbz_apply_neg ((m : ℤ) - d) (by omega : e - (t : ℤ) - d < 0), mul_zero, zero_smul]
  rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
  have hcollapse : ∀ d ∈ Finset.Ico (-(n : ℤ)) (e + 1),
      (∑ t ∈ Finset.range (p + 1),
        (((-1 : ℂ) ^ t * cbz ((m : ℤ) - e + (t : ℤ)) (t : ℤ))
          * cbz ((m : ℤ) - d) (e - (t : ℤ) - d)) • Tf d)
        = cbz (e - 1 - d) (e - d) • Tf d := by
    intro d hd
    simp only [Finset.mem_Ico] at hd
    rw [← Finset.sum_smul, zeroModeOuter_collapse_low p (by rw [he]; omega)]
  rw [Finset.sum_congr rfl hcollapse,
    Finset.sum_eq_single_of_mem e (by simp only [Finset.mem_Ico]; rw [he]; omega)
      (fun b hb hbe => ?_)]
  · rw [show e - 1 - e = -1 from by ring, show e - e = (0 : ℤ) from by ring, cbz_zero, one_smul,
      hTf]
    dsimp only
    rw [show l - 1 - e + ((m : ℤ) - (n : ℤ)) = l - 1 + ((m : ℤ) - (p : ℤ)) from by rw [he]; ring]
  · simp only [Finset.mem_Ico] at hb
    rw [cbz_lt (by omega : (0 : ℤ) ≤ e - 1 - b) (by omega : e - 1 - b < e - b), zero_smul]

/-- **Dong–Jiang Lemma 4.1, all slots.**  `o_{n,m}(a *ⁿ_{m,p} b) w = o_{n,p}(a) o_{p,m}(b) w`
for every `w ∈ M(m)` and arbitrary (not necessarily homogeneous) `a, b`.  Both sides are
`ℂ`-bilinear, so the homogeneous case extends by the grade decomposition of each slot. -/
theorem oLevW_anmGen_law_lev (L : AdmLev W A) (n m p : ℕ) (u v : 𝒱) {w : M}
    (hw : w ∈ L.lev (m : ℤ)) :
    oLevW A ((m : ℤ) - (n : ℤ)) (anmGen W n m p u v) w
      = oLevW A ((p : ℤ) - (n : ℤ)) u (oLevW A ((m : ℤ) - (p : ℤ)) v w) := by
  have hzeroL : ∀ y : 𝒱, anmGen W n m p (0 : 𝒱) y = 0 := by
    intro y
    have := anmGen_smul_left W n m p (0 : ℂ) (0 : 𝒱) y
    rwa [zero_smul, zero_smul] at this
  have hzeroR : ∀ y : 𝒱, anmGen W n m p y (0 : 𝒱) = 0 := by
    intro y
    have := anmGen_smul_right W n m p (0 : ℂ) y (0 : 𝒱)
    rwa [zero_smul, zero_smul] at this
  have key : ∀ (k : ℤ) (u' : 𝒱), u' ∈ W.grading k → ∀ v' : 𝒱,
      oLevW A ((m : ℤ) - (n : ℤ)) (anmGen W n m p u' v') w
        = oLevW A ((p : ℤ) - (n : ℤ)) u' (oLevW A ((m : ℤ) - (p : ℤ)) v' w) := by
    intro k u' hu' v'
    rcases lt_or_ge k 0 with hneg | hpos
    · rw [W.positivity k hneg, Submodule.mem_bot] at hu'
      subst hu'
      simp only [hzeroL, map_zero, LinearMap.zero_apply]
    · have hvtop : v' ∈ ⨆ i, W.grading i := by
        rw [W.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
      refine Submodule.iSup_induction W.grading
        (motive := fun v' => oLevW A ((m : ℤ) - (n : ℤ)) (anmGen W n m p u' v') w
          = oLevW A ((p : ℤ) - (n : ℤ)) u' (oLevW A ((m : ℤ) - (p : ℤ)) v' w)) hvtop ?_ ?_ ?_
      · intro i y hy
        rw [oLevW_anmGen_law_lev_homog L n m p hpos hu' hy hw, oLevW_homogeneous A _ hu',
          oLevW_homogeneous A _ hy]
      · change oLevW A ((m : ℤ) - (n : ℤ)) (anmGen W n m p u' 0) w = _
        simp only [hzeroR, map_zero, LinearMap.zero_apply]
      · intro y z hy hz
        change oLevW A ((m : ℤ) - (n : ℤ)) (anmGen W n m p u' (y + z)) w = _
        rw [anmGen_add_right, map_add, LinearMap.add_apply, hy, hz, map_add, LinearMap.add_apply,
          map_add]
  have hutop : u ∈ ⨆ i, W.grading i := by
    rw [W.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
  refine Submodule.iSup_induction W.grading
    (motive := fun u => oLevW A ((m : ℤ) - (n : ℤ)) (anmGen W n m p u v) w
      = oLevW A ((p : ℤ) - (n : ℤ)) u (oLevW A ((m : ℤ) - (p : ℤ)) v w)) hutop ?_ ?_ ?_
  · intro i y hy
    exact key i y hy v
  · change oLevW A ((m : ℤ) - (n : ℤ)) (anmGen W n m p 0 v) w = _
    simp only [hzeroL, map_zero, LinearMap.zero_apply]
  · intro y z hy hz
    change oLevW A ((m : ℤ) - (n : ℤ)) (anmGen W n m p (y + z) v) w = _
    rw [anmGen_add_left, map_add, LinearMap.add_apply, hy, hz, map_add, LinearMap.add_apply]

/-- **Dong–Jiang Corollary 4.2, first half** (`refs/dj.txt`:1282):
`o_{n,m}(u *ⁿ_m v) w = o_{n,m}(u) o_{m,m}(v) w` — the case `p = m` of Lemma 4.1, where the general
product is the repo right action `anmRight`. -/
theorem oLevW_anmRight_law_lev (L : AdmLev W A) (n m : ℕ) (u v : 𝒱) {w : M}
    (hw : w ∈ L.lev (m : ℤ)) :
    oLevW A ((m : ℤ) - (n : ℤ)) (anmRight W n m u v) w
      = oLevW A ((m : ℤ) - (n : ℤ)) u (oLevW A 0 v w) := by
  rw [← anmGen_eq_anmRight, oLevW_anmGen_law_lev L n m m u v hw, sub_self]

/-- **Dong–Jiang Corollary 4.2, second half** (`refs/dj.txt`:1282):
`o_{n,m}(u ∗̄ⁿ_m v) w = o_{n,n}(u) o_{n,m}(v) w` — the case `p = n` of Lemma 4.1, where the general
product is the left action `anmGenBar`. -/
theorem oLevW_anmGenBar_law_lev (L : AdmLev W A) (n m : ℕ) (u v : 𝒱) {w : M}
    (hw : w ∈ L.lev (m : ℤ)) :
    oLevW A ((m : ℤ) - (n : ℤ)) (anmGenBar W n m u v) w
      = oLevW A 0 u (oLevW A ((m : ℤ) - (n : ℤ)) v w) := by
  rw [anmGenBar, oLevW_anmGen_law_lev L n m n u v hw, sub_self]

end Lemma41

/-- **`DJCompositionLev` is a THEOREM.**  The named hypothesis on which the whole
`ZhuVermaAnArchGate` reduction rested — Dong–Jiang **Lemma 4.1** over the `AdmLev` interface — is
discharged unconditionally.  No PBW, no `finrank`, no `L₀`, no internal grading of the module. -/
theorem djCompositionLev_holds (W : VertexOperatorAlgebra 𝒱) : DJCompositionLev W := by
  intro M _ _ A L n m p a b w hw
  exact oLevW_anmGen_law_lev L n m p a b hw

/-- **`DJComposition` is a THEOREM** — the `OrdVModule` phrasing of Lemma 4.1
(`ZhuVermaAnArchGateB1.DJComposition`), via `djComposition_of_djCompositionLev`. -/
theorem djComposition_holds (W : VertexOperatorAlgebra 𝒱) : DJComposition W :=
  djComposition_of_djCompositionLev (djCompositionLev_holds W)

/-! ## (4) The two sharp statements of `PHASE4_PLAN` C-7 -/

/-- **(B1-assoc)**, as a `Prop`: for every non-negatively levelled weak module and every bottom
vector `w`, the depth-`p₃` mode `X₍wt X − 1 − p₃₎` of the inner bare associator
`X = assocInner W p₁ p₂ p₃ a b c` annihilates `w`.

The depth is **matched** to `p₃`: `PHASE4_PLAN` C-7 records that the mismatched depth `p₃ + 1` is
nonzero in 2370/4096 free-boson and 1910/3375 Virasoro instances, so this statement cannot be
strengthened. -/
def B1AssocInner (W : VertexOperatorAlgebra 𝒱) : Prop :=
  ∀ {M : Type u} [AddCommGroup M] [Module ℂ M] (A : WeakModule W M) (L : AdmLev W A)
    (p₁ p₂ p₃ : ℕ) (a b c : 𝒱) {w : M}, w ∈ L.lev 0 →
      oLevW A (((0 : ℕ) : ℤ) - (p₃ : ℤ)) (assocInner W p₁ p₂ p₃ a b c) w = 0

/-- **(B1-level)**, as a `Prop`: for `Z = a *⁰_{p,p} g` with `g ∈ O_p(𝒱)`, the mode
`Z₍wt Z − 1 + p₎` annihilates every level-`p` vector.

The hypothesis `g ∈ O_p(𝒱)` is **necessary**: `PHASE4_PLAN` C-7 records that for generic `g` the
statement fails in 84–196 of 196 instances per level `p`. -/
def B1Level (W : VertexOperatorAlgebra 𝒱) : Prop :=
  ∀ {M : Type u} [AddCommGroup M] [Module ℂ M] (A : WeakModule W M) (L : AdmLev W A)
    (p : ℕ) (a g : 𝒱), g ∈ Onm W p p → ∀ {y : M}, y ∈ L.lev (p : ℤ) →
      oLevW A ((p : ℤ) - ((0 : ℕ) : ℤ)) (anmGen W 0 p p a g) y = 0

section Sharp

variable {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M]
variable {A : WeakModule W M}

/-- **(B1-assoc), proved at every depth `p₃`.**  Three applications of Lemma 4.1 turn each half of
the bare associator into the same triple composite `o_{p₃,p₂}(a) o_{p₂,p₁}(b) o_{p₁,0}(c) w`; the
level bookkeeping `oLevW_mem_level` supplies the intermediate level-`p₁` vector.

`p₃ = 0` is not special: it is the case in which the outer wrap of `assocDefect` happens to be the
Zhu product, but the inner cancellation is the same at every depth. -/
theorem oLevW_assocInner_vanish (L : AdmLev W A) (p₁ p₂ p₃ : ℕ) (a b c : 𝒱) {w : M}
    (hw : w ∈ L.lev 0) :
    oLevW A (((0 : ℕ) : ℤ) - (p₃ : ℤ)) (assocInner W p₁ p₂ p₃ a b c) w = 0 := by
  have hw0 : w ∈ L.lev ((0 : ℕ) : ℤ) := by simpa using hw
  have hyw : oLevW A (((0 : ℕ) : ℤ) - (p₁ : ℤ)) c w ∈ L.lev (p₁ : ℤ) :=
    oLevW_mem_level L 0 p₁ c hw0
  rw [assocInner, map_sub, LinearMap.sub_apply,
    oLevW_anmGen_law_lev L p₃ 0 p₁ (anmGen W p₃ p₁ p₂ a b) c hw0,
    oLevW_anmGen_law_lev L p₃ p₁ p₂ a b hyw,
    oLevW_anmGen_law_lev L p₃ 0 p₂ a (anmGen W p₂ 0 p₁ b c) hw0,
    oLevW_anmGen_law_lev L p₂ 0 p₁ b c hw0, sub_self]

/-- **(B1-assoc) holds.** -/
theorem b1AssocInner_holds (W : VertexOperatorAlgebra 𝒱) : B1AssocInner W := by
  intro M _ _ A L p₁ p₂ p₃ a b c w hw
  exact oLevW_assocInner_vanish L p₁ p₂ p₃ a b c hw

/-- **(B1-level).**  One application of Lemma 4.1 peels `o_{0,p}(a *⁰_{p,p} g)` into
`o_{0,p}(a) · o_{p,p}(g)`, and the inner factor dies by the **already proved**
`OnmW_annihilates_diag` (= Dong–Jiang Theorem 4.3 on the graded pieces). -/
theorem oLevW_anmGen_diag_ideal_vanish (L : AdmLev W A) (p : ℕ) (a g : 𝒱) (hg : g ∈ Onm W p p)
    {y : M} (hy : y ∈ L.lev (p : ℤ)) :
    oLevW A ((p : ℤ) - ((0 : ℕ) : ℤ)) (anmGen W 0 p p a g) y = 0 := by
  rw [oLevW_anmGen_law_lev L 0 p p a g hy, OnmW_annihilates_diag L p hg hy, map_zero]

/-- **(B1-level) holds.** -/
theorem b1Level_holds (W : VertexOperatorAlgebra 𝒱) : B1Level W := by
  intro M _ _ A L p a g hg y hy
  exact oLevW_anmGen_diag_ideal_vanish L p a g hg hy

end Sharp

/-! ## (5) B1, unconditional -/

section B1

variable {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M]
variable {A : WeakModule W M}

/-- **The `O''_{0,0}` (associator-defect) generators annihilate the bottom** — unconditional. -/
theorem oLevW_assocDefect_vanish_uncond (L : AdmLev W A) (p₁ p₂ p₃ : ℕ) (a b c u : 𝒱) {w : M}
    (hw : w ∈ L.lev 0) : oLevW A 0 (assocDefect W 0 0 p₁ p₂ p₃ a b c u) w = 0 :=
  oLevW_assocDefect_vanish (djCompositionLev_holds W) L p₁ p₂ p₃ a b c u hw

/-- **The `O'''_{0,0}` (level-mixing) generators annihilate the bottom** — unconditional. -/
theorem oLevW_levelMix_vanish_uncond (L : AdmLev W A) (p : ℕ) (a v g : 𝒱) (hg : g ∈ Onm W p p)
    {w : M} (hw : w ∈ L.lev 0) : oLevW A 0 (levelMix W 0 0 p a g v) w = 0 :=
  oLevW_levelMix_vanish (djCompositionLev_holds W) L p a v g hg hw

/-- **B1**: every element of the *full* Dong–Jiang ideal `O_{0,0}(𝒱)` — circle
generators, shifted grading generators, associator defects at every internal depth, and level-mixing
generators through every level-`p` ideal `O_p(𝒱)` — has zero mode annihilating the bottom level of
every non-negatively levelled weak `𝒱`-module.

This is the annihilation half of the `(0,0)` gate, with no carried hypothesis. -/
theorem oLevW_OnmFull_zero_zero_vanish (L : AdmLev W A) {x : 𝒱} (hx : x ∈ OnmFull W 0 0) {w : M}
    (hw : w ∈ L.lev 0) : oLevW A 0 x w = 0 :=
  gateAnnihilationLev_of_djCompositionLev (djCompositionLev_holds W) A L x hx hw

end B1

/-- **`GateAnnihilationLev` is a THEOREM** — B1, in the reusable form the gate assembly
consumes. -/
theorem gateAnnihilationLev_holds (W : VertexOperatorAlgebra 𝒱) : GateAnnihilationLev W :=
  gateAnnihilationLev_of_djCompositionLev (djCompositionLev_holds W)

/-- **`GateAnnihilation` is a THEOREM** — B1 in the `OrdVModule` phrasing of
`ZhuVermaAnArchGateB1`. -/
theorem gateAnnihilation_holds (W : VertexOperatorAlgebra 𝒱) : GateAnnihilation W :=
  gateAnnihilation_of_gateAnnihilationLev (gateAnnihilationLev_holds W)

/-! ## (6) The gate rests on TWO named inputs, not three -/

section Consumers

variable {W : VertexOperatorAlgebra 𝒱}

open VHat VHat.DLM3

/-- **The `(0,0)` gate reduced to exactly the two Dong–Li–Mason inputs.**  `gate_of_dj_and_dlm3`
needed three; `DJCompositionLev` is discharged, so only B2 remains:

1. `BottomProjection (parabolicRepOfAMod W (regularAMod W))` — DLM3's bottom-injectivity step, as
   an explicit assumption; the companion `voaPBWBottomProjection` supplies this instance from the
   generic relative-induction field of the theorem `VOA.pbw : PBWPrinciple`;
2. `DefectPairsToZero Pr` — DLM3's `U(V̂)W ⊆ J` (their Props 4.3 + 4.6).

This is **not** a proof of the gate; it is the sharpened conditional reduction. -/
theorem gate_of_dlm3 (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W)))
    (hdef : DefectPairsToZero Pr) : OnmFull W 0 0 = O W :=
  gate_of_dj_and_dlm3 (djCompositionLev_holds W) Pr hdef

/-- **The whole downstream package from the two DLM3 inputs.** -/
theorem downstream_of_dlm3 (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W)))
    (hdef : DefectPairsToZero Pr) :
    OnmFull W 0 0 = O W ∧ DJAnnEqAn W 0 ∧ OnmFull W 0 0 = OnFull W 0 :=
  downstream_of_dj_and_dlm3 (djCompositionLev_holds W) Pr hdef

end Consumers

/-! ## (7) Consistency anchors

Two independently proved statements are re-derived from Lemma 4.1, pinning every index and sign. -/

section Anchors

variable {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M]
variable {A : WeakModule W M}

/-- **Anchor 1** — at `(n,m,p) = (0,0,0)` Lemma 4.1 is Zhu's `o(u ∗ v) = o(u) o(v)` on the bottom,
which `ZhuVermaAnArchGate` proves independently (`oLevW_zhuMul_lev_zero`). -/
theorem oLevW_zhuMul_lev_zero_of_lemma41 (L : AdmLev W A) (u v : 𝒱) {w : M} (hw : w ∈ L.lev 0) :
    oLevW A 0 (zhuMul W u v) w = oLevW A 0 u (oLevW A 0 v w) := by
  have hw0 : w ∈ L.lev ((0 : ℕ) : ℤ) := by simpa using hw
  have h := oLevW_anmGen_law_lev L 0 0 0 u v hw0
  rw [anmGen_zero_zero_zero] at h
  simpa using h

/-- **Anchor 2** — at `(n,m) = (0,0)` Lemma 4.1 reproduces the zero-mode law's own base case
`djCompositionLev_base`, proved in `ZhuVermaAnArchZeroModeLaw` from `Ω(M)` alone. -/
theorem djCompositionLev_base_of_lemma41 (L : AdmLev W A) (p : ℕ) (u v : 𝒱) {w : M}
    (hw : w ∈ L.lev ((0 : ℕ) : ℤ)) :
    oLevW A (((0 : ℕ) : ℤ) - ((0 : ℕ) : ℤ)) (anmGen W 0 0 p u v) w
      = oLevW A ((p : ℤ) - ((0 : ℕ) : ℤ)) u (oLevW A (((0 : ℕ) : ℤ) - (p : ℤ)) v w) :=
  oLevW_anmGen_law_lev L 0 0 p u v hw

/-- **Anchor 3** — the circle generator's vanishing on `M(p)` (`oLevW_anmCirc_vanish`, proved in
`ZhuVermaAnArchGate` from the high-pole law `oLevW_resHom_vanish`) is, from the present angle, the
statement that the offset window of `oLevW_resHom_law_lev` is **empty**: at `D = 0`, `s = m = p`,
`q = 2p + 2` the range `Ico (D − m) (s − q + 2)` is `Ico (−p) (−p) = ∅`.  Every offset that could
contribute carries a `v`-mode index at or above the level ceiling. -/
theorem oLevW_anmCirc_vanish_of_law (L : AdmLev W A) (p : ℕ) {k l : ℤ} (hk : 0 ≤ k) {u v : 𝒱}
    (hu : u ∈ W.grading k) (hv : v ∈ W.grading l) {w : M} (hw : w ∈ L.lev (p : ℤ)) :
    oLevW A 0 (anmCirc W p p u v) w = 0 := by
  rw [anmCirc, oLevW_resHom_law_lev L 0 (p : ℤ) (p : ℤ) (Int.natCast_nonneg p) le_rfl
      ((p : ℤ) + (p : ℤ) + 2) hk hu hv hw,
    show Finset.Ico ((0 : ℤ) - (p : ℤ)) ((p : ℤ) - ((p : ℤ) + (p : ℤ) + 2) + 2)
      = (∅ : Finset ℤ) from Finset.Ico_eq_empty (by omega), Finset.sum_empty]

end Anchors

end VOA
