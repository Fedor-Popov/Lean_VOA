/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.LevelOneUnitaryIntegrable
import VOA.Examples.BGPackageBFactor

/-!
# Unitarity of `L_1(sl₂)`

`bUnitary : ConcreteHodge.Unitary bForm bRealStructure` — **the simple level-one affine VOA
`L_1(sl₂)`, with its normalized canonical invariant form and the descended compact conjugation,
is unitary**: `B(ρx, x)` is a positive real for every nonzero homogeneous `x`.

## Proof (Kac's Casimir argument, specialized)

Work in the universal module `V^1(sl₂)` with `h(x, y) = B(ρx, y)` and the maximal ideal `I`.
For a joint vector `y` of energy `E` and `h₀`-charge `μ`, the Hermitian Sugawara identity
(`IsCompactRealStructure.sugawara_sesq`) and `[e₀, f₀] = h₀` give (`sugawara_charge`)

  `(6E - μ - μ²/2) h(y,y) = 2 h(e₀y, e₀y) + Σ_c Σ_{1≤m≤E} 2 w_c h(J^c_m y, J^c_m y)`.

Every vector on the right has lower energy, or the same energy and charge `μ + 2`.  The
coefficient is positive whenever `y ∉ I` and `μ ≥ 0`, by the charge bound `μ² ≤ 4E`
(`charge_sq_le`, which is where integrability of `L_1` enters) and `μ ≤ 2E`.  So by induction on
the energy, and downward on the charge (`np_joint`), `h(y,y)` is a nonnegative real vanishing only
on `I` (`NP`); vanishing forces all positive modes into `I` and then `y ∈ I`
(`mem_maxIdeal_of_pos_kill`).  Negative charges follow by the compact conjugation.  Distinct
charges are `h`-orthogonal, so the statement extends to whole weight spaces (`np_grading`), and
descends to the quotient.

No hypothesis: everything is proved.
-/

namespace VOA.LevelOneUnitary

open AffineVOA AffineVOA.Inst AffineSl2GeneralRigidity AffineSl2BelowCritical Sl2Sing
open VOA.ConcreteHodge Sl2CosetConcrete
open Module (End)

noncomputable section

section Positivity

variable {hk : (1 : ℂ) + 2 ≠ 0} {R : RealStructure (universal 1 hk)}

local notation "Imax" => QuotVOA.maxGradedIdeal (universal 1 hk)
local notation "hf" => sesqForm (universalForm 1 hk) R

variable (R) in
/-- **Nonnegative norm, vanishing only on the maximal ideal.** -/
def NP (y : WakModule 1) : Prop :=
  (hf y y).im = 0 ∧ 0 ≤ (hf y y).re ∧ ((hf y y).re = 0 → y ∈ Imax)

theorem np_of_mem {y : WakModule 1} (hy : y ∈ Imax) : NP R y := by
  have h0 : hf y y = 0 := by
    rw [sesqForm_apply, form_eq_zero_of_mem_right hk hy]
  refine ⟨by rw [h0]; rfl, by rw [h0]; rfl, fun _ => hy⟩

theorem np_zero_energy {μ : ℤ} {y : WakModule 1} (hy : y ∈ jointSpace 1 hk 0 μ) : NP R y := by
  have hy0 := joint_le_grading hk hy
  rw [(universal 1 hk).vacuum_grade, Submodule.mem_span_singleton] at hy0
  obtain ⟨c, rfl⟩ := hy0
  have hval : hf (c • (universal 1 hk).vacuum) (c • (universal 1 hk).vacuum) =
      ((Complex.normSq c : ℝ) : ℂ) := by
    rw [sesqForm_smul_left, sesqForm_smul_right, sesqForm_apply, R.map_vacuum,
      (universalForm_normalized 1 hk), Complex.normSq_eq_conj_mul_self]
    ring
  refine ⟨by rw [hval, Complex.ofReal_im],
    by rw [hval, Complex.ofReal_re]; exact Complex.normSq_nonneg c, fun h => ?_⟩
  rw [hval, Complex.ofReal_re, Complex.normSq_eq_zero] at h
  rw [h, zero_smul]
  exact Submodule.zero_mem _

variable (hR : IsCompactRealStructure R)
include hR

theorem adjF (x z : WakModule 1) : hf (J 1 colF 0 x) z = hf x (J 1 colE 0 z) := by
  have h := hR.sesq_J_adj colF 0 x z
  rw [neg_zero] at h
  exact h

theorem adjF' (x z : WakModule 1) : hf x (J 1 colF 0 z) = hf (J 1 colE 0 x) z := by
  have h := hR.sesq_J_adj' colF 0 x z
  rw [neg_zero] at h
  exact h

theorem adjH (x z : WakModule 1) : hf (J 1 colH 0 x) z = hf x (J 1 colH 0 z) := by
  have h := hR.sesq_J_adj colH 0 x z
  rw [neg_zero] at h
  exact h

/-- **The Sugawara identity on a joint space**, with the `f₀` term rewritten through
`[e₀, f₀] = h₀`. -/
theorem sugawara_charge {E : ℕ} {μ : ℤ} {y : WakModule 1} (hy : y ∈ jointSpace 1 hk E μ) :
    ((6 * (E : ℝ) - μ - (μ : ℝ) ^ 2 / 2 : ℝ) : ℂ) * hf y y =
      2 * hf (J 1 colE 0 y) (J 1 colE 0 y) +
        ∑ c : Fin 3, ∑ m ∈ Finset.Icc 1 E, ((2 * sugawaraWeight c : ℝ) : ℂ) *
          hf (J 1 c (m : ℤ) y) (J 1 c (m : ℤ) y) := by
  have hs := hR.sugawara_sesq (joint_le_grading hk hy)
  simp only [Int.toNat_natCast] at hs
  have hH : J 1 colH 0 y = (μ : ℂ) • y := ((mem_jointSpace_iff 1 hk E μ y).mp hy).2
  have hfn : hf (J 1 colF 0 y) (J 1 colF 0 y) =
      hf (J 1 colE 0 y) (J 1 colE 0 y) + (μ : ℂ) * hf y y := by
    rw [adjF hR, EFz 1 0 0 (by norm_num) y, sesqForm_add_right, sesqForm_add_right,
      adjF' hR, hH, sesqForm_smul_right, sesqForm_smul_right]
    push_cast
    ring
  have hhn : hf (J 1 colH 0 y) (J 1 colH 0 y) = (μ : ℂ) ^ 2 * hf y y := by
    rw [hH, sesqForm_smul_left, sesqForm_smul_right, map_intCast]
    ring
  have hz : (∑ c : Fin 3, (sugawaraWeight c : ℂ) * hf (J 1 c 0 y) (J 1 c 0 y)) =
      2 * hf (J 1 colE 0 y) (J 1 colE 0 y) + ((μ : ℂ) + (μ : ℂ) ^ 2 / 2) * hf y y := by
    rw [Fin.sum_univ_three]
    change (sugawaraWeight 0 : ℂ) * hf (J 1 colE 0 y) (J 1 colE 0 y) +
        (sugawaraWeight 1 : ℂ) * hf (J 1 colF 0 y) (J 1 colF 0 y) +
        (sugawaraWeight 2 : ℂ) * hf (J 1 colH 0 y) (J 1 colH 0 y) = _
    rw [hfn, hhn]
    simp only [sugawaraWeight, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    push_cast
    ring
  rw [hz] at hs
  push_cast
  push_cast at hs
  linear_combination hs

/-- **The positivity step** at a joint vector of positive energy and nonnegative charge. -/
theorem np_step {E : ℕ} (hE : 1 ≤ E) {μ : ℤ} {y : WakModule 1}
    (hy : y ∈ jointSpace 1 hk E μ) (hc : 0 < 6 * (E : ℝ) - μ - (μ : ℝ) ^ 2 / 2)
    (h0 : NP R (J 1 colE 0 y))
    (hpos : ∀ (c : Fin 3), ∀ m ∈ Finset.Icc 1 E, NP R (J 1 c (m : ℤ) y)) : NP R y := by
  have hsug := sugawara_charge hR hy
  set c : ℝ := 6 * (E : ℝ) - μ - (μ : ℝ) ^ 2 / 2 with hcdef
  set T : ℂ := 2 * hf (J 1 colE 0 y) (J 1 colE 0 y) +
    ∑ c : Fin 3, ∑ m ∈ Finset.Icc 1 E, ((2 * sugawaraWeight c : ℝ) : ℂ) *
      hf (J 1 c (m : ℤ) y) (J 1 c (m : ℤ) y) with hT
  have hyT : hf y y = ((c⁻¹ : ℝ) : ℂ) * T := by
    rw [← hsug, ← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ hc.ne', Complex.ofReal_one,
      one_mul]
  have h2im : ∀ z : ℂ, (2 * z).im = 2 * z.im := fun z => by simp [Complex.mul_im]
  have h2re : ∀ z : ℂ, (2 * z).re = 2 * z.re := fun z => by simp [Complex.mul_re]
  have hTim : T.im = 0 := by
    rw [hT, Complex.add_im, Complex.im_sum, h2im, h0.1, mul_zero, zero_add]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [Complex.im_sum]
    refine Finset.sum_eq_zero fun m hm => ?_
    rw [Complex.im_ofReal_mul, (hpos a m hm).1, mul_zero]
  have hTre : T.re = 2 * (hf (J 1 colE 0 y) (J 1 colE 0 y)).re +
      ∑ a : Fin 3, ∑ m ∈ Finset.Icc 1 E, (2 * sugawaraWeight a) *
        (hf (J 1 a (m : ℤ) y) (J 1 a (m : ℤ) y)).re := by
    rw [hT, Complex.add_re, Complex.re_sum, h2re]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Complex.re_ofReal_mul]
  have hterm : ∀ a : Fin 3, ∀ m ∈ Finset.Icc 1 E, 0 ≤ (2 * sugawaraWeight a) *
      (hf (J 1 a (m : ℤ) y) (J 1 a (m : ℤ) y)).re := fun a m hm =>
    mul_nonneg (by have := sugawaraWeight_pos a; positivity) (hpos a m hm).2.1
  have hsum_nonneg : 0 ≤ ∑ a : Fin 3, ∑ m ∈ Finset.Icc 1 E, (2 * sugawaraWeight a) *
      (hf (J 1 a (m : ℤ) y) (J 1 a (m : ℤ) y)).re :=
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg (hterm a)
  have h0re : 0 ≤ 2 * (hf (J 1 colE 0 y) (J 1 colE 0 y)).re := by
    have := h0.2.1; positivity
  have hTre_nonneg : 0 ≤ T.re := by rw [hTre]; exact add_nonneg h0re hsum_nonneg
  have hcinv : 0 < c⁻¹ := inv_pos.mpr hc
  refine ⟨by rw [hyT, Complex.im_ofReal_mul, hTim, mul_zero],
    by rw [hyT, Complex.re_ofReal_mul]; exact mul_nonneg hcinv.le hTre_nonneg, fun hzero => ?_⟩
  rw [hyT, Complex.re_ofReal_mul] at hzero
  have hT0 : T.re = 0 := (mul_eq_zero.mp hzero).resolve_left hcinv.ne'
  rw [hTre] at hT0
  have hsum0 := ((add_eq_zero_iff_of_nonneg h0re hsum_nonneg).mp hT0).2
  have hkill : ∀ a : Fin 3, ∀ m ∈ Finset.Icc 1 E, J 1 a (m : ℤ) y ∈ Imax := by
    intro a m hm
    have hin := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => Finset.sum_nonneg (hterm a))).mp
      hsum0 a (Finset.mem_univ a)
    have hcm := (Finset.sum_eq_zero_iff_of_nonneg (hterm a)).mp hin m hm
    have hw : (2 * sugawaraWeight a) ≠ 0 := by have := sugawaraWeight_pos a; positivity
    exact (hpos a m hm).2.2 ((mul_eq_zero.mp hcm).resolve_left hw)
  apply mem_maxIdeal_of_pos_kill hk (E := (E : ℤ)) (by omega) (joint_le_grading hk hy)
  intro a m hm
  by_cases hmE : m ≤ E
  · exact hkill a m (Finset.mem_Icc.mpr ⟨hm, hmE⟩)
  · have hg := J_mem_grading hk a (m : ℤ) (joint_le_grading hk hy)
    rw [eq_zero_of_grading_neg hk (by omega) hg]
    exact Submodule.zero_mem _

variable (hρI : ∀ y ∈ QuotVOA.maxGradedIdeal (universal 1 hk),
    R.rho y ∈ QuotVOA.maxGradedIdeal (universal 1 hk)) (hρρ : ∀ y, R.rho (R.rho y) = y)
include hρI hρρ

/-- **Positivity on every joint space** of `V^1(sl₂)`, modulo the maximal ideal. -/
theorem np_joint : ∀ (E : ℕ) (μ : ℤ) (y : WakModule 1), y ∈ jointSpace 1 hk E μ → NP R y := by
  intro E
  induction E using Nat.strong_induction_on with
  | _ E ihE => ?_
  rcases Nat.eq_zero_or_pos E with hE0 | hEpos
  · subst hE0
    intro μ y hy
    exact np_zero_energy (by simpa using hy)
  have hbound := charge_sq_le hR hρI hρρ
  have hnn : ∀ d : ℕ, ∀ μ : ℤ, 0 ≤ μ → 2 * (E : ℤ) < μ + d →
      ∀ y, y ∈ jointSpace 1 hk E μ → NP R y := by
    intro d
    induction d with
    | zero =>
        intro μ _ hμ y hy
        rw [joint_eq_zero_of_charge hk (Or.inr (by omega)) hy]
        exact np_of_mem (Submodule.zero_mem _)
    | succ d ihd =>
        intro μ hμ0 hμd y hy
        by_cases hyI : y ∈ Imax
        · exact np_of_mem hyI
        have hb := hbound E μ y hy hyI
        have hne : y ≠ 0 := fun h => hyI (h ▸ Submodule.zero_mem _)
        have hw := charge_window_of_ne hk hy hne
        apply np_step hR hEpos hy
        · have hb' : (μ : ℝ) ^ 2 ≤ 4 * E := by exact_mod_cast hb
          have hw' : (μ : ℝ) ≤ 2 * E := by exact_mod_cast hw.2
          have hE1 : (1 : ℝ) ≤ E := by exact_mod_cast hEpos
          nlinarith
        · have h := J_E_mem_joint hk 0 hy
          rw [sub_zero] at h
          exact ihd (μ + 2) (by omega) (by push_cast at hμd ⊢; omega) _ h
        · intro c m hm
          obtain ⟨μ', hμ'⟩ := exists_J_mem_joint hk c (m : ℤ) hy
          have hmE := Finset.mem_Icc.mp hm
          have hcast : ((E : ℤ) - (m : ℤ)) = ((E - m : ℕ) : ℤ) := by
            rw [Nat.cast_sub hmE.2]
          rw [hcast] at hμ'
          exact ihE (E - m) (by omega) μ' _ hμ'
  intro μ y hy
  rcases le_or_gt 0 μ with hμ | hμ
  · exact hnn ((2 * (E : ℤ) + 1 - μ).toNat) μ hμ (by omega) y hy
  · have hρy := rho_mem_joint hk hR hy
    have hnp := hnn ((2 * (E : ℤ) + 1 + μ).toNat) (-μ) (by omega) (by omega) _ hρy
    have hsame : hf (R.rho y) (R.rho y) = hf y y := by
      rw [sesqForm_apply, sesqForm_apply, hρρ, ConcreteHodge.universalForm_isSymmetric 1 hk]
    obtain ⟨h1, h2, h3⟩ := hnp
    rw [hsame] at h1 h2 h3
    exact ⟨h1, h2, fun h => by simpa [hρρ] using hρI _ (h3 h)⟩

/-- **Positivity on every weight space** of `V^1(sl₂)`, modulo the maximal ideal: distinct
charges are orthogonal. -/
theorem np_grading (N : ℕ) {y : WakModule 1} (hy : y ∈ (universal 1 hk).grading N) :
    NP R y := by
  rw [universal_grading_eq_joint_sum 1 hk N, Submodule.mem_iSup_finset_iff_exists_sum] at hy
  obtain ⟨z, rfl⟩ := hy
  have hnp : ∀ c, NP R (z c : WakModule 1) := fun c => np_joint hR hρI hρρ N (2 * c) _ (z c).2
  have horth : ∀ c d, c ≠ d → hf (z c) (z d) = 0 := by
    intro c d hcd
    have hc := ((mem_jointSpace_iff 1 hk N (2 * c) _).mp (z c).2).2
    have hd := ((mem_jointSpace_iff 1 hk N (2 * d) _).mp (z d).2).2
    have h := adjH hR (z c) (z d)
    rw [hc, hd, sesqForm_smul_left, sesqForm_smul_right, map_intCast] at h
    have hne : ((2 * c : ℤ) : ℂ) ≠ ((2 * d : ℤ) : ℂ) := by
      exact_mod_cast (by omega : 2 * c ≠ 2 * d)
    have h' : (((2 * c : ℤ) : ℂ) - ((2 * d : ℤ) : ℂ)) * hf (z c) (z d) = 0 := by
      rw [sub_mul, h, sub_self]
    exact (mul_eq_zero.mp h').resolve_left (sub_ne_zero.mpr hne)
  have hexp : hf (∑ c ∈ chargeWindow N, (z c : WakModule 1))
      (∑ c ∈ chargeWindow N, (z c : WakModule 1)) =
        ∑ c ∈ chargeWindow N, hf (z c) (z c) := by
    have h1 : hf (∑ c ∈ chargeWindow N, (z c : WakModule 1))
        (∑ c ∈ chargeWindow N, (z c : WakModule 1)) =
          ∑ c ∈ chargeWindow N, ∑ d ∈ chargeWindow N, hf (z c) (z d) := by
      simp only [sesqForm_apply, map_sum, LinearMap.coe_sum, Finset.sum_apply]
      exact Finset.sum_comm
    rw [h1]
    refine Finset.sum_congr rfl fun c hc => ?_
    exact Finset.sum_eq_single c (fun d _ hdc => horth c d (Ne.symm hdc))
      (fun h => absurd hc h)
  refine ⟨?_, ?_, fun h0 => ?_⟩
  · rw [hexp, Complex.im_sum]
    exact Finset.sum_eq_zero fun c _ => (hnp c).1
  · rw [hexp, Complex.re_sum]
    exact Finset.sum_nonneg fun c _ => (hnp c).2.1
  · rw [hexp, Complex.re_sum] at h0
    have hz := (Finset.sum_eq_zero_iff_of_nonneg fun c _ => (hnp c).2.1).mp h0
    exact Submodule.sum_mem _ fun c hc => (hnp c).2.2 (hz c hc)

end Positivity

/-! ### The concrete pair `(bForm, bRealStructure)` -/

/-- The universal compact conjugation at level one (the one descended to `bRealStructure`). -/
abbrev levelOneRealStructure : RealStructure (universal 1 bNoncritical) :=
  compactRealStructure bLevel_real bNoncritical

theorem levelOneRealStructure_rho (x : WakModule 1) :
    levelOneRealStructure.rho x = bUniversalConj x := rfl

theorem levelOne_isCompact : IsCompactRealStructure levelOneRealStructure :=
  compactRealStructure_isCompact bLevel_real bNoncritical

theorem levelOne_rho_maxIdeal :
    ∀ y ∈ QuotVOA.maxGradedIdeal (universal 1 bNoncritical),
      levelOneRealStructure.rho y ∈ QuotVOA.maxGradedIdeal (universal 1 bNoncritical) :=
  fun _ hy => bUniversalConj_maxIdeal_stable hy

theorem levelOne_rho_rho (y : WakModule 1) :
    levelOneRealStructure.rho (levelOneRealStructure.rho y) = y := bUniversalConj_sq y

/-- **Unitarity of `L_1(sl₂)`** for its normalized canonical invariant form and the descended
compact conjugation.  Proved outright: no hypothesis. -/
theorem bUnitary : ConcreteHodge.Unitary bForm bRealStructure := by
  intro n x _ hx0
  obtain ⟨y, hy, hxy⟩ := Submodule.mem_map.mp x.2
  have hval : gradedSesq bForm bRealStructure n x x =
      sesqForm (universalForm 1 bNoncritical) levelOneRealStructure y y := by
    rw [gradedSesq_apply, ← hxy, bRealStructure_rho, Submodule.mkQ_apply, ← Submodule.mkQ_apply,
      bConj_mkQ]
    exact simpleForm_mkQ 1 bNoncritical _ _
  have hyI : y ∉ QuotVOA.maxGradedIdeal (universal 1 bNoncritical) := by
    intro h
    apply hx0
    apply Subtype.ext
    rw [← hxy, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).mpr h]
    rfl
  rcases lt_or_ge n 0 with hn | hn
  · exact absurd (by rw [eq_zero_of_grading_neg bNoncritical hn hy]; exact Submodule.zero_mem _)
      hyI
  obtain ⟨N, rfl⟩ := Int.eq_ofNat_of_zero_le hn
  have hnp := np_grading levelOne_isCompact levelOne_rho_maxIdeal levelOne_rho_rho N hy
  refine ⟨(sesqForm (universalForm 1 bNoncritical) levelOneRealStructure y y).re,
    lt_of_le_of_ne hnp.2.1 (fun h => hyI (hnp.2.2 h.symm)), ?_⟩
  rw [hval]
  apply Complex.ext
  · simp
  · rw [Complex.ofReal_im]; exact hnp.1

end

end VOA.LevelOneUnitary
