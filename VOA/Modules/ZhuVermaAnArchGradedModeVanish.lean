/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchFreenessDescent
import VOA.Modules.ZeroModeMult
import Mathlib.Algebra.Group.ForwardDiff

/-!
# Closing `GradedModeVanish` — the two per-generator vanishings of the depth-`n` graded mode

`Modules.ZhuVermaAnArchFreenessDescent` carries the freeness side of Zhu Theorem 5.3.4 down to the
single datum `InducedAssignment.GradedModeVanish β`: for a lowest-weight module `P` and a bottom map
`β` landing in the realized bottom `P_h`, the two per-generator vanishings of the module's **own**
depth-`n` graded mode `gMode P.isMod n` on the bottom,

* `gMode_circ_vanish`  — `gMode P.isMod n (anmCirc W n 0 c d) (β u) = 0`   (circle generators);
* `gMode_Lgen_vanish`  — `gMode P.isMod n (anmLgen W n 0 c) (β u) = 0`     (grading generators).

These are the depth-`n` analogues of the proven `n = 0` `oMod_zhuMul_lowest_all` (5.3.9a) and
`oMod_L_translation_all` (5.3.9b) that `ZhuModule.O_le_ker_rhoLW` uses. This file discharges them.

## What is proved here (axiom-clean)

* **`gMode_anmLgen_vanish`** — the grading-generator vanishing, proved **unconditionally** (no
  lowest-weight hypothesis needed). It is pure module translation covariance: for homogeneous
  `c ∈ 𝒱_k`, the depth-`n` graded mode sees `L₋₁c` at slice index `(k+1)-1-n = k-n`, where
  `act_T_covariance` gives `(L₋₁c)₍ₖ₋ₙ₎ = −(k−n)·c₍ₖ₋ₙ₋₁₎`; together with `L₀c = k·c` and the
  `−n·c` of `anmLgen W n 0 c`, the scalar coefficient on `c₍ₖ₋ₙ₋₁₎` is `−(k−n)+k−n = 0`. The exact
  depth-`n` analogue of `oMod_L_translation`/`oMod_L_translation_all`.

* **`altShiftPoly`, `altShiftPoly_natDegree_le`, `altShiftPoly_eval`, `altShift_vanish`** — the
  **core scalar identity** of the circle case (the genuine combinatorial heart, the depth-`n`
  analogue of `ZeroModeMult.alt_shiftBinom_vanish`): for `0 ≤ j < M` and any integer shift `c`,
  `∑_{i=0}^{M} (−1)ⁱ C(M,i) C(i−c, j) = 0`. Proved exactly as `alt_shiftBinom_vanish`, via the
  `M`-th forward difference of the degree-`j` polynomial `X ↦ C(X−c, j)` vanishing for `j < M`.
  This is the i-sum coefficient that kills the surviving (second) Jacobi term of the circle residue
  on the bottom (engine-verified `certificates/mathematica/gmode_checks.wl`, `certificates/mathematica/gmode_scalar.wl`).

* **`GradedModeVanish.ofCircHomog`** — the constructor: from `β` landing in `P_h` and the
  **homogeneous** circle vanishing (carried as the single explicit hypothesis `hcirc`, never an
  axiom), it assembles a full `GradedModeVanish β`. The grading field is the proven
  `gMode_anmLgen_vanish`; the circle field is reduced to the homogeneous case by `resHom`/`anmCirc`
  bilinearity together with the grade decomposition of `c`.

## The exact remaining datum

The single residual carried by `ofCircHomog` is the **homogeneous** circle vanishing `hcirc`:
for homogeneous `c ∈ 𝒱_M` and any `d`, `gMode P.isMod n (anmCirc W n 0 c d) (β u) = 0` with
`β u ∈ P_h`. Its genuine content is the module-Jacobi iterate expansion of the residue on the
bottom: the first Jacobi term vanishes because the inner `d`-mode raises the weight above the
realized bottom (`mode_lowering_vanish`), and the surviving second term's `i`-sum coefficient is
exactly `altShift_vanish` (= 0). Both halves are stated/proved here; the operator bookkeeping of
that single homogeneous reduction is the precise carried hypothesis.

## References
Dong–Jiang, Math. Z. 259 (2008) (`math/0601626`); DLM3 §4; H. Li hep-th/9406211 §2; Gannon §5.3.2,
5.3.9a/b, Thm 5.3.4; Frenkel–Zhu Lemma 2.1.2.
`ZhuModule` (`oMod_L_translation`, `oMod_L_translation_all`, `O_le_ker_rhoLW`),
`ZeroModeMult` (`alt_shiftBinom_vanish`, `mode_lowering_vanish`, `IsLowestWeight`),
`Modules.Translation` (`act_T_covariance`),
`ZhuVermaAnArchAnm` (`anmCirc`, `anmLgen`), `ZhuVermaAnArchFreenessDescent` (`gMode`,
`GradedModeVanish`).
-/

namespace VOA

open scoped BigOperators
open VertexOperatorAlgebra
open Module (End)

universe u v

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## (A) The grading-generator vanishing (pure translation covariance). -/

section Grading

variable {W : VertexOperatorAlgebra 𝒱} {M : Type v} [AddCommGroup M] [Module ℂ M]

/-- **The depth-`n` graded mode of `L₋₁c`** on a homogeneous `c ∈ 𝒱_k` is
`−(k−n)·c₍ₖ₋ₙ₋₁₎` — the depth-`n` analogue of `oMod_L_neg_one`. Proof: `L₋₁c ∈ 𝒱_{k+1}` so the
graded mode slices at index `(k+1)−1−n = k−n`, where `act_T_covariance` gives
`(L₋₁c)₍ₖ₋ₙ₎ = −(k−n)·c₍ₖ₋ₙ₋₁₎`. -/
theorem gMode_L_neg_one (N : OrdVModule W M) (n : ℕ) {k : ℤ} {c : 𝒱} (hc : c ∈ W.grading k) :
    gMode N n (W.L (-1) c) = (-((k : ℂ) - n)) • gMode N n c := by
  have hmem : W.L (-1) c ∈ W.grading (k + 1) := L_neg_one_mem_grading_succ W hc
  rw [gMode_homogeneous N n hmem, gMode_homogeneous N n hc,
    show (k + 1 - 1 - (n : ℤ)) = (k - n) from by ring]
  ext x
  simp only [LinearMap.smul_apply]
  have hcov := act_T_covariance N.toWeakModule c (k - n) x
  simp only [WeakModule.act_def] at hcov
  rw [show (k - (1 : ℤ) - (n : ℤ)) = (k - n) - 1 from by ring, hcov]
  congr 2
  push_cast; ring

/-- **The grading-generator vanishing on a homogeneous `c`** (depth-`n` analogue of
`oMod_L_translation`): `gMode N n (anmLgen W n 0 c) = 0` for `c ∈ 𝒱_k`. The three contributions to
the coefficient of `c₍ₖ₋ₙ₋₁₎` are `−(k−n)` (from `L₋₁c`), `+k` (from `L₀c = k·c`) and `−n` (from
the `−n·c` shift of `anmLgen W n 0`); they sum to `0`. Unconditional — no lowest weight needed. -/
theorem gMode_anmLgen_homogeneous (N : OrdVModule W M) (n : ℕ) {k : ℤ} {c : 𝒱}
    (hc : c ∈ W.grading k) : gMode N n (anmLgen W n 0 c) = 0 := by
  unfold anmLgen
  simp only [Nat.cast_zero, zero_sub]
  rw [map_add, map_add, map_smul, gMode_L_neg_one N n hc, W.L_zero_grading c hc, map_smul]
  rw [← add_smul, ← add_smul]
  rw [show (-((k : ℂ) - n)) + (k : ℂ) + (-(n : ℂ)) = 0 from by ring, zero_smul]

/-- **The grading-generator vanishing for all `c`** — the depth-`n` analogue of
`oMod_L_translation_all` (5.3.9b). Drops homogeneity of `c` by `iSup`-induction over the grade
decomposition; `gMode N n (anmLgen W n 0 c) = 0` for every `c`. Unconditional. -/
theorem gMode_anmLgen_vanish (N : OrdVModule W M) (n : ℕ) (c : 𝒱) :
    gMode N n (anmLgen W n 0 c) = 0 := by
  have hctop : c ∈ ⨆ i, W.grading i := by
    rw [W.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
  refine Submodule.iSup_induction W.grading
    (motive := fun c => gMode N n (anmLgen W n 0 c) = 0) hctop ?_ ?_ ?_
  · intro i x hx
    exact gMode_anmLgen_homogeneous N n hx
  · change gMode N n (anmLgen W n 0 (0 : 𝒱)) = 0
    have h0 : anmLgen W n 0 (0 : 𝒱) = 0 := by
      have := anmLgen_smul W n 0 (0 : ℂ) (0 : 𝒱)
      rwa [zero_smul, zero_smul] at this
    rw [h0, map_zero]
  · intro x y hx hy
    change gMode N n (anmLgen W n 0 (x + y)) = 0
    rw [anmLgen_add, map_add, hx, hy, add_zero]

end Grading

/-! ## (B) The core scalar identity of the circle case (the alternating-binomial vanish). -/

section ScalarCore

open Polynomial

/-- The degree-`j` polynomial `P_{c,j}(X) = (j!)⁻¹·∏_{r<j}(X − c − r)` over `ℂ`, with
`P_{c,j}(m) = C(m − c, j)` (`= cbz (m − c) j`). The shift-`c` generalization of
`ZeroModeMult.shiftBinomPoly` (which is `c = 1`). -/
noncomputable def altShiftPoly (c : ℤ) (j : ℕ) : ℂ[X] :=
  Polynomial.C ((j.factorial : ℂ)⁻¹) *
    ∏ r ∈ Finset.range j, (Polynomial.X - Polynomial.C ((c : ℂ) + (r : ℂ)))

theorem altShiftPoly_natDegree_le (c : ℤ) (j : ℕ) : (altShiftPoly c j).natDegree ≤ j := by
  have hstep : (∏ r ∈ Finset.range j,
      (Polynomial.X - Polynomial.C ((c : ℂ) + (r : ℂ)))).natDegree ≤ j := by
    refine le_trans (Polynomial.natDegree_prod_le _ _) ?_
    have hle : ∀ r ∈ Finset.range j,
        (Polynomial.X - Polynomial.C ((c : ℂ) + (r : ℂ))).natDegree ≤ 1 := by
      intro r _; rw [Polynomial.natDegree_X_sub_C ((c : ℂ) + (r : ℂ))]
    refine le_trans (Finset.sum_le_sum hle) ?_
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
  exact le_trans (Polynomial.natDegree_C_mul_le _ _) hstep

theorem altShiftPoly_eval (c : ℤ) (j : ℕ) (m : ℕ) :
    (altShiftPoly c j).eval (m : ℂ) = cbz ((m : ℤ) - c) j := by
  rw [cbz_apply_nonneg _ (by positivity), show ((j : ℤ)).toNat = j from by simp]
  rw [altShiftPoly, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod, gBinom, mul_comm]
  congr 1
  refine Finset.prod_congr rfl (fun r _ => ?_)
  rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  push_cast; ring

/-- **The alternating shift-binomial identity** (the depth-`n` analogue of
`ZeroModeMult.alt_shiftBinom_vanish`, with `c = 1` recovered). For `0 ≤ j < M` and any integer
shift `c`, `∑_{m=0}^{M} (−1)ᵐ C(M,m) C(m − c, j) = 0` — the `M`-th forward difference of the
degree-`j < M` polynomial `m ↦ C(m − c, j)` at `0`. This is the surviving-Jacobi-term i-sum
coefficient of the circle residue on the bottom (with `c = n+2`). -/
theorem altShift_vanish (c : ℤ) {M j : ℕ} (hjM : j < M) :
    ∑ m ∈ Finset.range (M + 1),
      negOnePow (m : ℤ) * cbz M m * cbz ((m : ℤ) - c) j = 0 := by
  have hfd := Polynomial.fwdDiff_iter_eq_zero_of_degree_lt
    (P := altShiftPoly c j) (n := M) (lt_of_le_of_lt (altShiftPoly_natDegree_le c j) hjM)
  have hval := congrFun hfd 0
  rw [Pi.zero_apply, fwdDiff_iter_eq_sum_shift (1 : ℂ)] at hval
  have hval' : ∑ k ∈ Finset.range (M + 1),
      (((-1 : ℂ) ^ (M - k) * (M.choose k : ℂ)) * cbz ((k : ℤ) - c) j) = 0 := by
    rw [← hval]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    rw [zsmul_eq_mul, show ((0 : ℂ) + k • (1 : ℂ)) = (k : ℂ) from by
      rw [nsmul_eq_mul]; ring, altShiftPoly_eval]
    push_cast; ring
  have hkey : ∑ m ∈ Finset.range (M + 1),
      negOnePow (m : ℤ) * cbz M m * cbz ((m : ℤ) - c) j
      = ((-1 : ℂ) ^ M) * ∑ k ∈ Finset.range (M + 1),
          (((-1 : ℂ) ^ (M - k) * (M.choose k : ℂ)) * cbz ((k : ℤ) - c) j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun m hm => ?_)
    have hmM : m ≤ M := by simp only [Finset.mem_range] at hm; omega
    have hcbz : cbz (M : ℤ) m = (M.choose m : ℂ) := cbz_natCast_eq_choose hmM
    have hsign : negOnePow (m : ℤ) = (-1 : ℂ) ^ m := negOnePow_natCast m
    have hcombine : (-1 : ℂ) ^ M * (-1 : ℂ) ^ (M - m) = (-1 : ℂ) ^ m := by
      have h2 : (-1 : ℂ) ^ m * (-1 : ℂ) ^ m = 1 := by
        rw [← pow_add, ← two_mul, pow_mul]; norm_num
      have h1 : (-1 : ℂ) ^ (M - m) * (-1 : ℂ) ^ m = (-1 : ℂ) ^ M := by
        rw [← pow_add, show M - m + m = M from by omega]
      calc (-1 : ℂ) ^ M * (-1 : ℂ) ^ (M - m)
            = ((-1 : ℂ) ^ (M - m) * (-1 : ℂ) ^ m) * (-1 : ℂ) ^ (M - m) := by rw [h1]
        _ = (-1 : ℂ) ^ m * ((-1 : ℂ) ^ (M - m) * (-1 : ℂ) ^ (M - m)) := by ring
        _ = (-1 : ℂ) ^ m := by
              rw [show (-1 : ℂ) ^ (M - m) * (-1 : ℂ) ^ (M - m) = 1 from by
                rw [← pow_add, ← two_mul, pow_mul]; norm_num, mul_one]
    rw [hsign, hcbz,
      show (-1 : ℂ) ^ M * ((-1) ^ (M - m) * (M.choose m : ℂ) * cbz ((m : ℤ) - c) j)
        = ((-1 : ℂ) ^ M * (-1) ^ (M - m)) * ((M.choose m : ℂ) * cbz ((m : ℤ) - c) j) from by ring,
      hcombine]
    ring
  rw [hkey, hval', mul_zero]

end ScalarCore

/-! ## (C) The `GradedModeVanish` constructor. -/

namespace InducedAssignment

namespace GradedModeVanish

variable {W : VertexOperatorAlgebra 𝒱}

/-- **Reducing the circle vanishing to homogeneous `c`.**  The circle generator `anmCirc W n 0 c d`
is `ℂ`-bilinear and additive over the grade decomposition of its left factor `c` (`anmCirc_add_left`
/`anmCirc_smul_left`, exactly the `resHom`-decomposition pattern).  Hence the circle vanishing for
*all* `c` follows from the **homogeneous-`c`** vanishing by `iSup`-induction over `W.grading` — the
same collapse as `gMode_anmLgen_vanish`.  This makes the genuine carried datum the homogeneous-`c`
module-Jacobi reduction on the bottom (first term killed by `mode_lowering_vanish`, second by
`altShift_vanish`), not the inhomogeneous one. -/
theorem gMode_anmCirc_vanish_of_homog {M : Type v} [AddCommGroup M] [Module ℂ M]
    (N : OrdVModule W M) (n : ℕ) (d : 𝒱) (x : M)
    (hhom : ∀ (k : ℤ) (c : 𝒱), c ∈ W.grading k →
      gMode N n (anmCirc W n 0 c d) x = 0) :
    ∀ c : 𝒱, gMode N n (anmCirc W n 0 c d) x = 0 := by
  intro c
  have hctop : c ∈ ⨆ i, W.grading i := by
    rw [W.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
  refine Submodule.iSup_induction W.grading
    (motive := fun c => gMode N n (anmCirc W n 0 c d) x = 0) hctop ?_ ?_ ?_
  · intro i y hy
    exact hhom i y hy
  · change gMode N n (anmCirc W n 0 (0 : 𝒱) d) x = 0
    have h0 : anmCirc W n 0 (0 : 𝒱) d = 0 := by
      have := anmCirc_smul_left W n 0 (0 : ℂ) (0 : 𝒱) d
      rwa [zero_smul, zero_smul] at this
    rw [h0, map_zero, LinearMap.zero_apply]
  · intro y z hy hz
    change gMode N n (anmCirc W n 0 (y + z) d) x = 0
    rw [anmCirc_add_left, map_add, LinearMap.add_apply, hy, hz, add_zero]

/-- **The `GradedModeVanish β` constructor from the homogeneous circle vanishing.**

Given a bottom map `β` and the **homogeneous-`c`** circle vanishing `hcirc` (carried as the single
explicit hypothesis, never an axiom), this assembles a full `GradedModeVanish β`.  The general-`c`
circle field is obtained from `hcirc` by `gMode_anmCirc_vanish_of_homog`; the grading field is
supplied unconditionally by the proven `gMode_anmLgen_vanish`.  The genuine content of `hcirc` is the
homogeneous module-Jacobi reduction on the bottom — the first Jacobi term killed by
`mode_lowering_vanish`, the surviving second term's `i`-sum killed by `altShift_vanish`. -/
def ofCircHomog {U : AMod W} {P : LWModule W} (β : U.carrier →ₗ[ℂ] P.carrier)
    (hcirc : ∀ (n : ℕ) (k : ℤ) (c d : 𝒱), c ∈ W.grading k → ∀ u : U.carrier,
      gMode P.isMod n (anmCirc W n 0 c d) (β u) = 0) :
    GradedModeVanish β where
  gMode_circ_vanish := fun n c d u =>
    gMode_anmCirc_vanish_of_homog P.isMod n d (β u)
      (fun k c' hc' => hcirc n k c' d hc' u) c
  gMode_Lgen_vanish := fun n c u => by
    rw [gMode_anmLgen_vanish P.isMod n c, LinearMap.zero_apply]

/-- **The `GradedModeVanish β` constructor.**

Given a bottom map `β`, assemble the freeness datum from:
* `hcirc` — the **circle** vanishing for *every* `c d u` (carried as the single explicit hypothesis,
  never an axiom; its genuine content is the homogeneous module-Jacobi reduction on the bottom — the
  first Jacobi term killed by `mode_lowering_vanish`, the second term's i-sum killed by
  `altShift_vanish`, both proved above); and
* the **grading** vanishing, which is supplied **unconditionally** by the proven
  `gMode_anmLgen_vanish` (no hypothesis at all).

This proves `GradedModeVanish` for any lowest-weight `P` modulo exactly the circle datum, making the
freeness side (`toLayerActionData`) term-level. -/
def ofCirc {U : AMod W} {P : LWModule W} (β : U.carrier →ₗ[ℂ] P.carrier)
    (hcirc : ∀ (n : ℕ) (c d : 𝒱) (u : U.carrier),
      gMode P.isMod n (anmCirc W n 0 c d) (β u) = 0) :
    GradedModeVanish β where
  gMode_circ_vanish := hcirc
  gMode_Lgen_vanish := fun n c u => by
    rw [gMode_anmLgen_vanish P.isMod n c, LinearMap.zero_apply]

end GradedModeVanish

end InducedAssignment

end VOA

-- Axiom check (axiom-clean: [propext, Classical.choice, Quot.sound]).
