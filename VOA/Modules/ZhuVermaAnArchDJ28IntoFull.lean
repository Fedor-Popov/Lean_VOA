/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchDJ28Final
import VOA.Modules.ZhuVermaAnArchHinge
import VOA.Core.Identities

/-!
# Dong–Jiang Lemma 2.8 into the FULL ideal — unconditional — and the collapse-only hinge

This file discharges the published **Dong–Jiang Lemma 2.8** hypothesis `DJ28IntoFull W`
(`ZhuVermaAnArchHingeCollapse`) as an **unconditional, axiom-clean term**, removing it from the
faithful Zhu bijection's dependency surface.

## The key bridge `anmCirc00_vac`

`anmLgen W 0 0 c = anmCirc W 0 0 c 𝟙` for ALL `c` (engine-verified, `certificates/mathematica/lgen_check.wl`):
the level-`(0,0)` grading generator `L₋₁c + L₀c` is the level-`(0,0)` circle generator on the vacuum
`resHom W 0 2 c 𝟙`.  Only the `i = 0` mode (`c₍₋₂₎𝟙 = L₋₁c`) and `i = 1` mode (`c₍₋₁₎𝟙 = c`, weight
`cbz K 1 = K = L₀`) survive; `i ≥ 2` gives `c₍≥0₎𝟙 = 0` (creation theorem).  This rewrites the
`crossL` family into a `crossCirc`, closeable by the unconditional `circCross_mem`.

## `DJ28IntoFull W`, unconditional

* `circ` — `O'_{n,0} *^n_0 𝒱 ⊆ OnmFull` via `anmGen_OnmFull_right_unconditional` (DJ 2.8 right).
* `crossCirc` — `𝒱 *^n_0 (c ∘^0_0 d) ⊆ OnmFull` via the unconditional `circCross_mem`.
* `crossL`    — `𝒱 *^n_0 (L₋₁c+L₀c) ⊆ OnmFull` via `anmCirc00_vac` + `circCross_mem`.

Consequently the faithful Zhu bijection does not rest on DJ Lemma 2.8: `phase4_of_collapse`
takes only the **collapse** `∀ n, OnmCollapses W n` (the DJ 2.6/2.7 into-`O'` content) plus the
generalized-Verma `M(U)` data (`A`/`hirr`/`F`/`hiso`/`G`).

## References
Dong–Jiang, Math. Z. 259 (2008) 799–826 (`math/0601626`), §2 (Lemma 2.8); Gannon §5.3.2, Thm 5.3.4.
-/

open scoped BigOperators

namespace VOA

open VertexOperatorAlgebra

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- For homogeneous `c ∈ 𝒱_K`, the level-`(0,0)` circle generator on the vacuum is the grading
generator: `anmCirc W 0 0 c 𝟙 = resHom W 0 2 c 𝟙 = L₋₁c + L₀c = anmLgen W 0 0 c`.  Only the `i = 0`
mode (`c₍₋₂₎𝟙 = L₋₁c`) and `i = 1` mode (`c₍₋₁₎𝟙 = c`, weight `cbz K 1 = K = L₀`) survive; `i ≥ 2`
gives `c₍≥0₎𝟙 = 0`. -/
theorem anmCirc00_vac_homog (W : VertexOperatorAlgebra 𝒱) {K : ℕ} {c : 𝒱}
    (hc : c ∈ W.grading (K : ℤ)) :
    anmCirc W 0 0 c W.vacuum = anmLgen W 0 0 c := by
  have hT2 : W.smul c (-2) W.vacuum = W.L (-1) c := by
    rw [← PreVertexAlgebra.T_apply, T_eq_Lneg1]
  have hcbz1 : cbz (K : ℤ) ((1 : ℕ) : ℤ) = (K : ℂ) := by
    rw [cbz_apply_nonneg _ (by positivity)]
    simp [gBinom]
  rw [anmCirc_zero_zero, resHom_homogeneous W 0 2 hc W.vacuum]
  simp only [add_zero, Int.toNat_natCast]
  rw [show (∑ i ∈ Finset.range (K + 1), cbz (K : ℤ) i • W.smul c ((i : ℤ) - 2) W.vacuum)
        = ∑ i ∈ Finset.range (K + 1),
            ((if i = 0 then W.L (-1) c else 0) + (if i = 1 then (K : ℂ) • c else 0)) from
      Finset.sum_congr rfl fun i _ => ?_]
  · -- sum the two indicator families.
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq' (Finset.range (K + 1)) 0,
        Finset.sum_ite_eq' (Finset.range (K + 1)) 1,
        if_pos (Finset.mem_range.mpr (Nat.succ_pos K))]
    have hL0 : W.L 0 c = (K : ℂ) • c := W.L0_grading c hc
    rw [anmLgen, hL0]
    rcases Nat.eq_zero_or_pos K with hK | hK
    · subst hK; simp
    · rw [if_pos (Finset.mem_range.mpr (by omega))]; simp
  · -- the per-`i` term computation.
    rcases Nat.lt_or_ge i 2 with hi | hi
    · interval_cases i
      · rw [Nat.cast_zero, cbz_zero, one_smul, show (0 : ℤ) - 2 = -2 from by ring, hT2,
          if_pos rfl, if_neg (by omega : (0 : ℕ) ≠ 1), add_zero]
      · rw [show ((1 : ℕ) : ℤ) - 2 = -1 from by norm_num,
          PreVertexAlgebra.smul_vacuum_neg_one, hcbz1, if_neg (by omega : (1 : ℕ) ≠ 0),
          if_pos rfl, zero_add]
    · rw [PreVertexAlgebra.smul_vacuum_nonneg _ c (by omega : (0 : ℤ) ≤ (i : ℤ) - 2), smul_zero,
        if_neg (by omega), if_neg (by omega), add_zero]

/-- resHom distributes over a finite sum in the left slot (local; the repo's is private). -/
theorem resHom_sum_left' (W : VertexOperatorAlgebra 𝒱) (s p : ℤ) {ι : Type*}
    (t : Finset ι) (f : ι → 𝒱) (b : 𝒱) :
    resHom W s p (∑ i ∈ t, f i) b = ∑ i ∈ t, resHom W s p (f i) b := by
  classical
  induction t using Finset.induction with
  | empty => simp only [Finset.sum_empty]; exact resHom_zero_left' W s p b
  | insert x t hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, resHom_add_left, ih]

/-- **`anmCirc W 0 0 c 𝟙 = anmLgen W 0 0 c` for ALL `c`** (the homogeneous identity extended by the
grade decomposition).  The key bridge that closes the `crossL` family of DJ Lemma 2.8 into the
full ideal via the unconditional `circCross_mem` (with `d = 𝟙`). -/
theorem anmCirc00_vac (W : VertexOperatorAlgebra 𝒱) (c : 𝒱) :
    anmCirc W 0 0 c W.vacuum = anmLgen W 0 0 c := by
  classical
  letI := DirectSum.IsInternal.chooseDecomposition W.grading W.isInternal
  set dc := DirectSum.decompose W.grading c with hdc
  have hdecomp : ∑ k ∈ dc.support, ((dc k : W.grading k) : 𝒱) = c :=
    DirectSum.sum_support_decompose W.grading c
  rw [anmLgen_diag]
  conv_lhs => rw [anmCirc_zero_zero, ← hdecomp]
  conv_rhs => rw [← hdecomp]
  rw [resHom_sum_left', map_sum, map_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rcases le_or_gt 0 k with hk | hk
  · obtain ⟨K, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    have h := anmCirc00_vac_homog W (dc (K : ℤ)).2
    rwa [anmCirc_zero_zero, anmLgen_diag] at h
  · have hzero : ((dc k : W.grading k) : 𝒱) = 0 := by
      have hmem : ((dc k : W.grading k) : 𝒱) ∈ (⊥ : Submodule ℂ 𝒱) := by
        rw [← W.positivity k hk]; exact (dc k).2
      simpa using hmem
    rw [hzero, resHom_zero_left', map_zero, map_zero, add_zero]

/-! ## DJ Lemma 2.8 into the FULL ideal — unconditional. -/

/-- **`DJ28IntoFull W`, unconditional.**  All three `m = 0` DJ-2.8 `𝒱`-action families land in the
full ideal `OnmFull W n 0` as closed terms:
* `circ` — `O'_{n,0} *^n_0 𝒱 ⊆ OnmFull` via `anmGen_OnmFull_right_unconditional` (right inclusion);
* `crossCirc` — `𝒱 *^n_0 (c ∘^0_0 d) ⊆ OnmFull` via the unconditional `circCross_mem`;
* `crossL` — the cross-grading `𝒱 *^n_0 (L₋₁c+L₀c)`, rewritten by `anmCirc00_vac`
  (`anmLgen W 0 0 c = anmCirc W 0 0 c 𝟙`) into a cross-circle, then `circCross_mem`.
This DISCHARGES the published DJ Lemma 2.8 hypothesis of `phase4_of_dj28_full` outright. -/
theorem dj28IntoFull_unconditional (W : VertexOperatorAlgebra 𝒱) : DJ28IntoFull W where
  circ n c d v := by
    rw [← anmGen_eq_anmRight]
    exact anmGen_OnmFull_right_unconditional W n 0 0 v (anmCirc W n 0 c d)
      (anmCirc_mem_OnmFull W n 0 c d)
  crossCirc n a c d := by
    rw [← anmGen_eq_anmRight]
    exact circCross_mem W n 0 0 a d c
  crossL n a c := by
    rw [← anmGen_eq_anmRight, ← anmCirc00_vac]
    exact circCross_mem W n 0 0 a W.vacuum c

/-! ## `NeededSliceMems` tightened from three families to two (via `anmCirc00_vac`). -/

/-- **`neededSliceMems_of_two`** — the `M(U)` `𝒱`-action slice (`NeededSliceMems W`, the gate of
`mUGradedAction_of_neededSlice`) needs only TWO of its three families: `circ` and `crossCirc`.  The
third, `crossL` (`anmRight W n 0 a (anmLgen W 0 0 c) ∈ Onm`), is derived from `crossCirc` (with
`d = 𝟙`) via the identity `anmLgen W 0 0 c = anmCirc W 0 0 c 𝟙` (`anmCirc00_vac`).  This shrinks the
remaining `MUGradedAction`/collapse FZ-residue obligation surface (each family is a shift-`0` `Onm`
membership, the `m = 0` analogue of `Pres_mem_On`). -/
theorem neededSliceMems_of_two (W : VertexOperatorAlgebra 𝒱)
    (hcirc : ∀ (n : ℕ) (c d v : 𝒱), anmRight W n 0 (anmCirc W n 0 c d) v ∈ Onm W n 0)
    (hcrossCirc : ∀ (n : ℕ) (a c d : 𝒱), anmRight W n 0 a (anmCirc W 0 0 c d) ∈ Onm W n 0) :
    NeededSliceMems W where
  circ := hcirc
  crossCirc := hcrossCirc
  crossL n a c := by
    rw [← anmCirc00_vac]
    exact hcrossCirc n a c W.vacuum

/-! ## The collapse-only hinge — DJ Lemma 2.8 discharged. -/

/-- **`phase4_of_collapse` — the faithful Zhu 5.3.4 bijection, DJ Lemma 2.8 discharged.**
`phase4_of_dj28_full` fed the unconditional `dj28IntoFull_unconditional`; the only remaining
mathematical inputs are the collapse `∀ n, OnmCollapses W n` (the DJ 2.6/2.7 into-`O'` content) and
the generalized-Verma `M(U)` construction data (`A`/`hirr`/`F`/`hiso`/`G`). -/
theorem phase4_of_collapse {W : VertexOperatorAlgebra 𝒱}
    (hcol : ∀ n : ℕ, OnmCollapses W n)
    (A : InducedAssignment W) (hirr : A.RealizeIrreducible)
    (F : InducedAssignment.LUFamily W)
    (hiso : ∀ U₁ U₂ : AMod W,
      Nonempty (AModEquiv W U₁ U₂) → LWModule.Iso W (F.K U₁) (F.K U₂))
    (G : InducedAssignment.GenFromBottomGFamily F) :
    Function.Bijective (forwardMapIrr W) :=
  phase4_of_dj28_full (dj28IntoFull_unconditional W) hcol A hirr F hiso G

end VOA

-- Axiom check (axiom-clean: [propext, Classical.choice, Quot.sound]; NO sorryAx/pbw).
