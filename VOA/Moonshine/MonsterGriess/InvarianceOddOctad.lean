/-
Ported from AxiomMath/CFSG (Apache-2.0), https://github.com/AxiomMath/CFSG,
commit 69cb972f587a3ecc035e092253167ff2e303c962 (source toolchain Lean v4.35.0-rc3 with the
module system), file:
  CFSG/Monster/Griess/Invariance/OddOctad.lean
Original authors (from the `@misc{axiom-cfsg}` citation, "Lean formalization of the
classification of finite simple groups", 2026):
  Cureton, Dean and Ilin, Vasily and Mehta, Bhavik and Voss, Niels and Cabral, Rafael and
  Defant, Colin and Gregory, Erik and Hill, Aaron and Hong, Letong and Hu, Qinheping and Jamner,
  Dustin and Jiang, Albert and Jordan, Tadeusz and Kurghinyan, Andranik and Lau, Kenny and
  Laurent, Jonathan and Liang, David and Limperg, Jannis and Mahns, Simon and Nugent, Brian and
  Olson, Connor and Ono, Ken and Paul, Eric and Rajan, Dhruv and Ram, Karun and Ray, Charlie and
  Siu, Ho Chung and Swaminathan, Ashvin A. and Thorner, Jesse and Tsaplin, Aleksey and Wang,
  Chenkai.
Port to Lean 4.30.0 / Mathlib v4.30.0 for LeanVOA by Fedor K. Popov (with Claude).
Released under the Apache 2.0 license.  Modifications relative to the source are listed in the
"Port notes" section of the module docstring below.
-/
import VOA.Moonshine.MonsterGriess.InvarianceOddValues

/-!
# Axiom's Monster port: triality invariance on (odd, odd, octad) triples

Using the closed forms of `InvarianceOddValues.lean` and the character sums of `oddBr` against
`sgn (bd d x ·)` (`sum_same_in`, `sum_same_out`, `sum_pair_in`, `sum_pair_out`), the trilinear
form is `tauB`- and `tauB.symm`-invariant on `sectSpan k × sectSpan k × octSpan` for each slot
`k` (and its permutations).  Summary: `triality_Griess_odd_octad_invariance`.

## Port notes
* Namespace `CFSG.Monster.Griess` ↦ `VOA.Moonshine.MonsterGriess` (as in the earlier ports).
  Module-system syntax, `@[expose]` and the source's `attribute [-instance] …` line dropped.
  Bodies verbatim.
* Short name also declared elsewhere in `VOA/` in another namespace (no clash, not renamed):
  the private `OctadInv.sgn_add_one` (`DeligneAudit/DeligneCharacterD4Functional.lean`).
-/

set_option linter.style.longLine false
set_option linter.style.show false

namespace VOA.Moonshine.MonsterGriess

open VOA.Moonshine.MonsterGriess VOA.Moonshine.MonsterGriess.Code VOA.Moonshine.MonsterGriess.Spin VOA.Moonshine.MonsterGriess.SpinLattice Matrix Module

namespace OctadInv

private theorem two_eq_zero' : (2 : ZMod 2) = 0 := rfl

private theorem sgn_add_one (y : ZMod 2) : sgn (y + 1) = -sgn y := by
  rw [sgn_add, show sgn 1 = -1 from rfl, mul_neg_one]

theorem oddBr_same_in {i : Fin 24} {d : OctadWord} (hi : i ∈ octSupp d)
    (w : Octad.EvenQuot (octSupp d)) : oddBr i i d w = 0 := by
  rw [oddBr, uQ_mul_uQ_oct, if_pos rfl, if_pos hi]
  have h := sgn_mul_self (Octad.ind (octRep d w) i)
  linear_combination (-(1 : ℚ) / 8) * h

theorem oddBr_same_out {i : Fin 24} {d : OctadWord} (hi : i ∉ octSupp d)
    (w : Octad.EvenQuot (octSupp d)) : oddBr i i d w = 1 / 8 := by
  rw [oddBr, uQ_mul_uQ_oct, if_pos rfl, if_neg hi]
  ring

theorem oddBr_pair_in {i j : Fin 24} {d : OctadWord} (hij : i ≠ j) (hi : i ∈ octSupp d)
    (hj : j ∈ octSupp d) (w : Octad.EvenQuot (octSupp d)) :
    oddBr i j d w = -sgn (bd d w (Octad.cls (octSupp d) {i, j})) / 8 := by
  rw [oddBr, uQ_mul_uQ_oct, if_neg hij, if_pos hi, if_pos hj,
    bd_pair d w hij hi hj, sgn_add]
  ring

theorem oddBr_pair_out {i j : Fin 24} {d : OctadWord} (hij : i ≠ j)
    (hout : ¬(i ∈ octSupp d ∧ j ∈ octSupp d)) (w : Octad.EvenQuot (octSupp d)) :
    oddBr i j d w = 0 := by
  rw [oddBr, uQ_mul_uQ_oct, if_neg hij]
  by_cases hi : i ∈ octSupp d
  · rw [if_neg (fun hj => hout ⟨hi, hj⟩)]
    ring
  · rw [if_neg hi]
    ring

theorem sum_same_in {i : Fin 24} {d : OctadWord} (hi : i ∈ octSupp d)
    (x : Octad.EvenQuot (octSupp d)) : ∑ w, sgn (bd d x w) * oddBr i i d w = 0 := by
  simp only [oddBr_same_in hi, mul_zero, Finset.sum_const_zero]

theorem sum_same_out {i : Fin 24} {d : OctadWord} (hi : i ∉ octSupp d)
    (x : Octad.EvenQuot (octSupp d)) :
    ∑ w, sgn (bd d x w) * oddBr i i d w = if x = 0 then 8 else 0 := by
  simp only [oddBr_same_out hi]
  rw [← Finset.sum_mul, sum_sgn_bd]
  split_ifs <;> norm_num

theorem sum_pair_in {i j : Fin 24} {d : OctadWord} (hij : i ≠ j) (hi : i ∈ octSupp d)
    (hj : j ∈ octSupp d) (x : Octad.EvenQuot (octSupp d)) :
    ∑ w, sgn (bd d x w) * oddBr i j d w =
      if x + Octad.cls (octSupp d) {i, j} = 0 then -8 else 0 := by
  have e : ∀ w, sgn (bd d x w) * oddBr i j d w =
      -(8 : ℚ)⁻¹ * sgn (bd d (x + Octad.cls (octSupp d) {i, j}) w) := by
    intro w
    rw [oddBr_pair_in hij hi hj, map_add (bd d) x, LinearMap.add_apply,
      bd_comm d (Octad.cls (octSupp d) {i, j}) w, sgn_add]
    ring
  rw [Finset.sum_congr rfl fun w _ => e w, ← Finset.mul_sum, sum_sgn_bd]
  split_ifs <;> norm_num

theorem sum_pair_out {i j : Fin 24} {d : OctadWord} (hij : i ≠ j)
    (hout : ¬(i ∈ octSupp d ∧ j ∈ octSupp d)) (x : Octad.EvenQuot (octSupp d)) :
    ∑ w, sgn (bd d x w) * oddBr i j d w = 0 := by
  simp only [oddBr_pair_out hij hout, mul_zero, Finset.sum_const_zero]

theorem tauB_sect0 (a : C₀) (i : Fin 24) : tauB (sectVec a i 0) = sectVec a i 1 :=
  tauB_sectVec a i 0

theorem tauB_symm_sect0 (a : C₀) (i : Fin 24) : tauB.symm (sectVec a i 0) = sectVec a i 2 :=
  tauB_symm_sectVec a i 2

theorem T_tauB_sect0_eq (a b : C₀) (i j : Fin 24) (d : OctadWord)
    (v : Octad.EvenQuot (octSupp d)) :
    T (tauB (sectVec a i 0)) (tauB (sectVec b j 0)) (tauB (octVec ⟨d, v⟩)) =
      if (a : C) + b = d + μ₀ d • ΩC then
        (8 : ℚ)⁻¹ * sgn (((a : C) : Fin 24 → ZMod 2) i + ((b : C) : Fin 24 → ZMod 2) j +
          μ₀ (d : C) + θ (d : C) (b : C)) *
          ∑ w, sgn (bd d (v + etaOf b d) w) * oddBr i j d w
      else 0 := by
  rw [tauB_sect0, tauB_sect0, tauB_octVec, map_sum (T (sectVec a i 1) (sectVec b j 1))]
  simp only [map_smul, smul_eq_mul, T_sect1_sect1_oct]
  by_cases hc : (a : C) + b = d + μ₀ d • ΩC
  · rw [if_pos hc, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [if_pos hc, octHD_apply, map_add (bd d) v (etaOf b d), LinearMap.add_apply]
    have e : bd d v w + qd d w + (((a : C) : Fin 24 → ZMod 2) i + ((b : C) : Fin 24 → ZMod 2) j +
        μ₀ (d : C) + qd d w + θ (d : C) (b : C) + bd d (etaOf b d) w) =
        (((a : C) : Fin 24 → ZMod 2) i + ((b : C) : Fin 24 → ZMod 2) j + μ₀ (d : C) +
          θ (d : C) (b : C)) + (bd d v w + bd d (etaOf b d) w) := by
      linear_combination (qd d w) * two_eq_zero'
    have e2 := congrArg sgn e
    simp only [sgn_add] at e2 ⊢
    linear_combination (8 : ℚ)⁻¹ * oddBr i j d w * e2
  · rw [if_neg hc]
    refine Finset.sum_eq_zero fun w _ => ?_
    rw [if_neg hc, zero_mul, mul_zero]

theorem T_tauB_symm_sect0_eq (a b : C₀) (i j : Fin 24) (d : OctadWord)
    (v : Octad.EvenQuot (octSupp d)) :
    T (tauB.symm (sectVec a i 0)) (tauB.symm (sectVec b j 0)) (tauB.symm (octVec ⟨d, v⟩)) =
      if (a : C) + b = d + μ₀ d • ΩC then
        (8 : ℚ)⁻¹ * sgn (qd d v + P ((a : C) : Fin 24 → ZMod 2) + P ((b : C) : Fin 24 → ZMod 2) +
          θ (d : C) (b : C)) * ∑ w, sgn (bd d (v + etaOf b d) w) * oddBr i j d w
      else 0 := by
  rw [tauB_symm_sect0, tauB_symm_sect0, tauB_symm_octVec,
    map_sum (T (sectVec a i 2) (sectVec b j 2))]
  simp only [map_smul, smul_eq_mul, T_sect2_sect2_oct]
  by_cases hc : (a : C) + b = d + μ₀ d • ΩC
  · rw [if_pos hc, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [if_pos hc, octHD_apply, map_add (bd d) v (etaOf b d), LinearMap.add_apply,
      bd_comm d w v]
    simp only [sgn_add]
    ring
  · rw [if_neg hc]
    refine Finset.sum_eq_zero fun w _ => ?_
    rw [if_neg hc, zero_mul, mul_zero]

theorem T_tauB_sect0 (a b : C₀) (i j : Fin 24) (d : OctadWord)
    (v : Octad.EvenQuot (octSupp d)) :
    T (tauB (sectVec a i 0)) (tauB (sectVec b j 0)) (tauB (octVec ⟨d, v⟩)) =
      T (sectVec a i 0) (sectVec b j 0) (octVec ⟨d, v⟩) := by
  rw [T_tauB_sect0_eq, T_sect0_sect0_oct, oddOctVal]
  by_cases hc : (a : C) + b = d + μ₀ d • ΩC
  · rw [if_pos hc, if_pos hc, θ_oct_odd' hc]
    have hd := coord_of_cond hc
    by_cases hij : i = j
    · subst hij
      rw [if_neg (show ¬(i ≠ i ∧ i ∈ octSupp d ∧ i ∈ octSupp d ∧
        v = etaOf b d + Octad.cls (octSupp d) {i, i}) from fun h => h.1 rfl)]
      by_cases hi : i ∈ octSupp d
      · rw [sum_same_in hi, mul_zero, if_neg (show ¬(i = i ∧ i ∉ octSupp d ∧
          v = etaOf b d) from fun h => h.2.1 hi)]
      · rw [sum_same_out hi]
        by_cases hv : v = etaOf b d
        · rw [if_pos (show v + etaOf b d = 0 from by rw [hv, add_self_F2]),
            if_pos (show i = i ∧ i ∉ octSupp d ∧ v = etaOf b d from ⟨rfl, hi, hv⟩)]
          have e : ((a : C) : Fin 24 → ZMod 2) i + ((b : C) : Fin 24 → ZMod 2) i + μ₀ (d : C) +
              θ (d : C) (a : C) = θ (d : C) (a : C) := by
            have hdi := hd i
            rw [coe_apply_eq_zero hi] at hdi
            linear_combination -hdi
          rw [e]
          ring
        · rw [if_neg (show ¬(v + etaOf b d = 0) from fun h =>
            hv ((eq_iff_add_eq_zero_F2 v (etaOf b d)).2 h)),
            if_neg (show ¬(i = i ∧ i ∉ octSupp d ∧ v = etaOf b d) from fun h => hv h.2.2)]
          ring
    · rw [if_neg (show ¬(i = j ∧ i ∉ octSupp d ∧ v = etaOf b d) from fun h => hij h.1)]
      by_cases hin : i ∈ octSupp d ∧ j ∈ octSupp d
      · rw [sum_pair_in hij hin.1 hin.2]
        by_cases hv : v = etaOf b d + Octad.cls (octSupp d) {i, j}
        · rw [if_pos (show v + etaOf b d + Octad.cls (octSupp d) {i, j} = 0 from by
            rw [hv, add_assoc, add_self_F2]),
            if_pos (show i ≠ j ∧ i ∈ octSupp d ∧ j ∈ octSupp d ∧
              v = etaOf b d + Octad.cls (octSupp d) {i, j} from ⟨hij, hin.1, hin.2, hv⟩)]
          have e : θ (d : C) (a : C) + ((b : C) : Fin 24 → ZMod 2) i +
              ((b : C) : Fin 24 → ZMod 2) j =
              ((a : C) : Fin 24 → ZMod 2) i + ((b : C) : Fin 24 → ZMod 2) j + μ₀ (d : C) +
                θ (d : C) (a : C) + 1 := by
            have hdi := hd i
            rw [coe_apply_eq_one hin.1] at hdi
            linear_combination -hdi - (((a : C) : Fin 24 → ZMod 2) i + μ₀ (d : C)) * two_eq_zero'
          rw [e, sgn_add_one]
          ring
        · rw [if_neg (show ¬(v + etaOf b d + Octad.cls (octSupp d) {i, j} = 0) from
            fun h => hv (add_add_eq_zero_iff_F2.1 (by rwa [add_comm v] at h))),
            if_neg (show ¬(i ≠ j ∧ i ∈ octSupp d ∧ j ∈ octSupp d ∧
              v = etaOf b d + Octad.cls (octSupp d) {i, j}) from fun h => hv h.2.2.2)]
          ring
      · rw [sum_pair_out hij hin, mul_zero, if_neg (show ¬(i ≠ j ∧ i ∈ octSupp d ∧
          j ∈ octSupp d ∧ v = etaOf b d + Octad.cls (octSupp d) {i, j}) from
            fun h => hin ⟨h.2.1, h.2.2.1⟩)]
  · rw [if_neg hc, if_neg hc]

theorem T_tauB_symm_sect0 (a b : C₀) (i j : Fin 24) (d : OctadWord)
    (v : Octad.EvenQuot (octSupp d)) :
    T (tauB.symm (sectVec a i 0)) (tauB.symm (sectVec b j 0)) (tauB.symm (octVec ⟨d, v⟩)) =
      T (sectVec a i 0) (sectVec b j 0) (octVec ⟨d, v⟩) := by
  rw [T_tauB_symm_sect0_eq, T_sect0_sect0_oct, oddOctVal]
  by_cases hc : (a : C) + b = d + μ₀ d • ΩC
  · rw [if_pos hc, if_pos hc, θ_oct_odd' hc]
    by_cases hij : i = j
    · subst hij
      rw [if_neg (show ¬(i ≠ i ∧ i ∈ octSupp d ∧ i ∈ octSupp d ∧
        v = etaOf b d + Octad.cls (octSupp d) {i, i}) from fun h => h.1 rfl)]
      by_cases hi : i ∈ octSupp d
      · rw [sum_same_in hi, mul_zero, if_neg (show ¬(i = i ∧ i ∉ octSupp d ∧
          v = etaOf b d) from fun h => h.2.1 hi)]
      · rw [sum_same_out hi]
        by_cases hv : v = etaOf b d
        · rw [if_pos (show v + etaOf b d = 0 from by rw [hv, add_self_F2]),
            if_pos (show i = i ∧ i ∉ octSupp d ∧ v = etaOf b d from ⟨rfl, hi, hv⟩)]
          have e : qd d v + P ((a : C) : Fin 24 → ZMod 2) + P ((b : C) : Fin 24 → ZMod 2) +
              θ (d : C) (a : C) = θ (d : C) (a : C) := by
            rw [hv, qd_etaOf hc]
            linear_combination (P ((a : C) : Fin 24 → ZMod 2) + P ((b : C) : Fin 24 → ZMod 2)) *
              two_eq_zero'
          rw [e]
          ring
        · rw [if_neg (show ¬(v + etaOf b d = 0) from fun h =>
            hv ((eq_iff_add_eq_zero_F2 v (etaOf b d)).2 h)),
            if_neg (show ¬(i = i ∧ i ∉ octSupp d ∧ v = etaOf b d) from fun h => hv h.2.2)]
          ring
    · rw [if_neg (show ¬(i = j ∧ i ∉ octSupp d ∧ v = etaOf b d) from fun h => hij h.1)]
      by_cases hin : i ∈ octSupp d ∧ j ∈ octSupp d
      · rw [sum_pair_in hij hin.1 hin.2]
        by_cases hv : v = etaOf b d + Octad.cls (octSupp d) {i, j}
        · rw [if_pos (show v + etaOf b d + Octad.cls (octSupp d) {i, j} = 0 from by
            rw [hv, add_assoc, add_self_F2]),
            if_pos (show i ≠ j ∧ i ∈ octSupp d ∧ j ∈ octSupp d ∧
              v = etaOf b d + Octad.cls (octSupp d) {i, j} from ⟨hij, hin.1, hin.2, hv⟩)]
          have e : θ (d : C) (a : C) + ((b : C) : Fin 24 → ZMod 2) i +
              ((b : C) : Fin 24 → ZMod 2) j =
              qd d v + P ((a : C) : Fin 24 → ZMod 2) + P ((b : C) : Fin 24 → ZMod 2) +
                θ (d : C) (a : C) + 1 := by
            rw [hv, qd_add, qd_etaOf hc, qd_pair hij hin.1 hin.2,
              bd_etaOf_pair b d hij hin.1 hin.2]
            linear_combination (-(P ((a : C) : Fin 24 → ZMod 2) + P ((b : C) : Fin 24 → ZMod 2) +
              1)) * two_eq_zero'
          rw [e, sgn_add_one]
          ring
        · rw [if_neg (show ¬(v + etaOf b d + Octad.cls (octSupp d) {i, j} = 0) from
            fun h => hv (add_add_eq_zero_iff_F2.1 (by rwa [add_comm v] at h))),
            if_neg (show ¬(i ≠ j ∧ i ∈ octSupp d ∧ j ∈ octSupp d ∧
              v = etaOf b d + Octad.cls (octSupp d) {i, j}) from fun h => hv h.2.2.2)]
          ring
      · rw [sum_pair_out hij hin, mul_zero, if_neg (show ¬(i ≠ j ∧ i ∈ octSupp d ∧
          j ∈ octSupp d ∧ v = etaOf b d + Octad.cls (octSupp d) {i, j}) from
            fun h => hin ⟨h.2.1, h.2.2.1⟩)]
  · rw [if_neg hc, if_neg hc]

theorem tauB_symm_tauB_symm (x : SpaceB) : tauB.symm (tauB.symm x) = tauB x := by
  conv_lhs => rw [← tauB_tauB_tauB x]
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]

theorem T_tauB_sector0 {u v w : SpaceB} (hu : u ∈ sectSpan 0) (hv : v ∈ sectSpan 0)
    (hw : w ∈ octSpan) : T (tauB u) (tauB v) (tauB w) = T u v w := by
  refine T_comp_eq_of_span (tauB : SpaceB →ₗ[ℚ] SpaceB) ?_ hu hv hw
  rintro _ ⟨⟨a, i⟩, rfl⟩ _ ⟨⟨b, j⟩, rfl⟩ _ ⟨⟨d, x⟩, rfl⟩
  exact T_tauB_sect0 a b i j d x

theorem T_tauB_symm_sector0 {u v w : SpaceB} (hu : u ∈ sectSpan 0) (hv : v ∈ sectSpan 0)
    (hw : w ∈ octSpan) : T (tauB.symm u) (tauB.symm v) (tauB.symm w) = T u v w := by
  refine T_comp_eq_of_span (tauB.symm : SpaceB →ₗ[ℚ] SpaceB) ?_ hu hv hw
  rintro _ ⟨⟨a, i⟩, rfl⟩ _ ⟨⟨b, j⟩, rfl⟩ _ ⟨⟨d, x⟩, rfl⟩
  exact T_tauB_symm_sect0 a b i j d x

theorem T_tauB_sector1 {u v w : SpaceB} (hu : u ∈ sectSpan 1) (hv : v ∈ sectSpan 1)
    (hw : w ∈ octSpan) :
    T (tauB u) (tauB v) (tauB w) = T u v w ∧
      T (tauB.symm u) (tauB.symm v) (tauB.symm w) = T u v w := by
  have hu0 : tauB.symm u ∈ sectSpan 0 := tauB_symm_mem_sectSpan (k := 0) hu
  have hv0 : tauB.symm v ∈ sectSpan 0 := tauB_symm_mem_sectSpan (k := 0) hv
  have hw0 : tauB.symm w ∈ octSpan := tauB_symm_mem_octSpan hw
  have hP := T_tauB_sector0 hu0 hv0 hw0
  have hQ := T_tauB_symm_sector0 hu0 hv0 hw0
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply] at hP
  refine ⟨?_, hP.symm⟩
  rw [← tauB_symm_tauB_symm u, ← tauB_symm_tauB_symm v, ← tauB_symm_tauB_symm w, hQ]
  exact hP.symm

theorem T_tauB_sector2 {u v w : SpaceB} (hu : u ∈ sectSpan 2) (hv : v ∈ sectSpan 2)
    (hw : w ∈ octSpan) :
    T (tauB u) (tauB v) (tauB w) = T u v w ∧
      T (tauB.symm u) (tauB.symm v) (tauB.symm w) = T u v w := by
  have hu0 : tauB u ∈ sectSpan 0 := tauB_mem_sectSpan (k := 2) hu
  have hv0 : tauB v ∈ sectSpan 0 := tauB_mem_sectSpan (k := 2) hv
  have hw0 : tauB w ∈ octSpan := tauB_mem_octSpan hw
  have hP := T_tauB_sector0 hu0 hv0 hw0
  have hQ := T_tauB_symm_sector0 hu0 hv0 hw0
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply,
    LinearEquiv.symm_apply_apply] at hQ
  refine ⟨hQ.symm, ?_⟩
  rw [← tauB_tauB u, ← tauB_tauB v, ← tauB_tauB w, hP]
  exact hQ.symm

end OctadInv

open OctadInv

theorem triality_Griess_odd_octad_invariance :
    (∀ (k : Fin 3), ∀ u ∈ sectSpan k, ∀ v ∈ sectSpan k, ∀ w ∈ octSpan,
      (T (tauB u) (tauB v) (tauB w) = T u v w ∧
        T (tauB.symm u) (tauB.symm v) (tauB.symm w) = T u v w) ∧
      (T (tauB u) (tauB w) (tauB v) = T u w v ∧
        T (tauB.symm u) (tauB.symm w) (tauB.symm v) = T u w v) ∧
      (T (tauB w) (tauB u) (tauB v) = T w u v ∧
        T (tauB.symm w) (tauB.symm u) (tauB.symm v) = T w u v)) ∧
    (∀ (a b : C₀) (i j : Fin 24) (d : OctadWord) (v : Octad.EvenQuot (octSupp d)),
      T (sectVec a i 0) (sectVec b j 0) (octVec ⟨d, v⟩) = oddOctVal a b i j d v) := by
  have main : ∀ (k : Fin 3), ∀ u ∈ sectSpan k, ∀ v ∈ sectSpan k, ∀ w ∈ octSpan,
      T (tauB u) (tauB v) (tauB w) = T u v w ∧
        T (tauB.symm u) (tauB.symm v) (tauB.symm w) = T u v w := by
    intro k u hu v hv w hw
    fin_cases k
    · exact ⟨T_tauB_sector0 hu hv hw, T_tauB_symm_sector0 hu hv hw⟩
    · exact T_tauB_sector1 hu hv hw
    · exact T_tauB_sector2 hu hv hw
  refine ⟨fun k u hu v hv w hw => ?_, T_sect0_sect0_oct⟩
  obtain ⟨h1, h2⟩ := main k u hu v hv w hw
  refine ⟨⟨h1, h2⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [← T_swap23 (tauB u) (tauB v) (tauB w), h1, T_swap23 u v w]
  · rw [← T_swap23 (tauB.symm u) (tauB.symm v) (tauB.symm w), h2, T_swap23 u v w]
  · rw [T_cycle (tauB w) (tauB u) (tauB v), h1, T_cycle w u v]
  · rw [T_cycle (tauB.symm w) (tauB.symm u) (tauB.symm v), h2, T_cycle w u v]

end VOA.Moonshine.MonsterGriess
