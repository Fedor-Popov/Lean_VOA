/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Huang.AndersonMooreMLDE
import VOA.Huang.AndersonMooreForms
import VOA.Huang.AndersonMooreODE
import VOA.Huang.AndersonMooreRigidity
import VOA.Huang.AndersonMooreGalois
import VOA.Huang.AndersonMooreEchelon

/-!
# The Anderson–Moore core theorem: Galois transport and rigidity (steps 4–6)

`rat_of_sClosed`: let `F_j = q^{ν_j} U_j` (`j < n`) with `U_j` convergent on the unit disc
with **rational** coefficients, `U_j(0) ≠ 0`, the `ν_j` pairwise distinct, and the family closed
under `S`.  Then every `ν_j ∈ ℚ`.

Proof (Anderson–Moore 1988; Gannon, arXiv:1310.4458, Prop. 3.5).  Fix `σ : ℂ →+* ℂ`.

1. `exists_mlde`: `B · ϑⁿ F_j = Σ_r A_r · ϑ^r F_j` with level-one holomorphic forms `B ≢ 0`, `A_r`.
2. Comparing `q`-expansions (`eq_of_amEval_eq`): `qB · ϑ̂ⁿ(ν_j, U_j) = Σ_r qA_r · ϑ̂^r(ν_j, U_j)` in
   `ℂ⟦q⟧`, where `ϑ̂` is the formal Serre iterate.
3. Apply `σ` coefficientwise.  The formal Serre iterate commutes with `σ` up to `ν ↦ σν`
   (`map_amSerreF`; the Eisenstein coefficients and the `U_j` are rational), and the conjugates
   `σB`, `σA_r` are again level-one forms (`exists_modularForm_qExpansion_map`).  So the family
   `F^σ_j = q^{σν_j} U_j` solves the conjugate MLDE.
4. The conjugate MLDE is `S`-invariant, and its solution space is spanned by the `F^σ_j`
   (`exists_eq_sum_of_serreODE`; the Wronskian of `F^σ` is `≢ 0` by `exists_wr_ne_zero`), so
   `F^σ` is `S`-closed.
5. `F^σ_i(z) = e^{2πi(σν_i − ν_i)z} F_i(z)`; along `z₀ + k` the two `S`-laws give exponential
   polynomials related by the factor `e^{−2πiδ/(z₀+k)}`, so `δ = 0`
   (`eq_zero_of_expPoly_eq_exp_mul`).
6. `σν_i = ν_i` for every `σ` forces `ν_i ∈ ℚ` (`exists_rat_eq_of_forall_ringHom`).

## Status
No `sorry`, no new axioms.  General (VOA-free).
-/

open Complex Filter Topology Matrix UpperHalfPlane ModularForm
open scoped MatrixGroups

noncomputable section

namespace VOA.Huang.AndersonMoore

open VOA

/-! ## Level-one forms as `q`-series -/

theorem modularForm_eq_amEval {k : ℤ} (F : ModularForm 𝒮ℒ k) {z : ℂ} (hz : z ∈ imGT 0) :
    F (ofComplex z) = amEval 0 (qExpansion 1 F) z := by
  have h := hasSum_qExpansion one_pos
    (SlashInvariantFormClass.periodic_comp_ofComplex F one_mem_strictPeriods_SL)
    (ModularFormClass.holo F) (ModularFormClass.bdd_at_infty F) (ofComplex z)
  rw [← h.tsum_eq, amEval_zero_left]
  refine tsum_congr fun m => ?_
  rw [smul_eq_mul, Function.Periodic.qParam, ← Complex.exp_nat_mul, ofComplex_apply_of_im_pos hz]
  congr 2
  push_cast
  ring

theorem qExpansion_mem_subexpPS {k : ℤ} (F : ModularForm 𝒮ℒ k) : qExpansion 1 F ∈ SubexpPS := by
  intro r hr
  -- evaluate at `τ = iy` with `e^{−2πy} = 1/r`
  set y : ℝ := Real.log r / (2 * Real.pi) with hy
  have hr0 : 0 < r := by linarith
  have hy0 : 0 < y := div_pos (Real.log_pos hr) (by positivity)
  have hz : Complex.I * (y : ℂ) ∈ imGT 0 := I_mul_mem_imGT hy0
  have h := hasSum_qExpansion one_pos
    (SlashInvariantFormClass.periodic_comp_ofComplex F one_mem_strictPeriods_SL)
    (ModularFormClass.holo F) (ModularFormClass.bdd_at_infty F) (ofComplex (Complex.I * y))
  have hq : Function.Periodic.qParam 1 (ofComplex (Complex.I * (y : ℂ))) = ((r⁻¹ : ℝ) : ℂ) := by
    rw [Function.Periodic.qParam, ofComplex_apply_of_im_pos hz]
    change Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (Complex.I * (y : ℂ)) / ((1 : ℝ) : ℂ)) = _
    rw [Complex.ofReal_inv, ← Real.exp_log hr0, Complex.ofReal_exp, ← Complex.exp_neg]
    congr 1
    rw [hy]
    push_cast
    field_simp
    rw [Complex.I_sq]
    ring
  have hlim := h.summable.tendsto_cofinite_zero
  rw [hq] at hlim
  obtain ⟨C, hC⟩ : ∃ C, ∀ n, ‖PowerSeries.coeff n (qExpansion 1 F) • ((r⁻¹ : ℝ) : ℂ) ^ n‖ ≤ C := by
    obtain ⟨C, hC⟩ := hlim.norm.bddAbove_range_of_cofinite
    exact ⟨C, fun n => hC ⟨n, rfl⟩⟩
  refine ⟨C, fun n => ?_⟩
  have h1 := hC n
  rw [norm_smul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hr0.le)] at h1
  have hrn : 0 < r ^ n := pow_pos hr0 n
  calc ‖PowerSeries.coeff n (qExpansion 1 F)‖
      = ‖PowerSeries.coeff n (qExpansion 1 F)‖ * r⁻¹ ^ n * r ^ n := by
        rw [inv_pow, mul_assoc, inv_mul_cancel₀ hrn.ne', mul_one]
    _ ≤ C * r ^ n := mul_le_mul_of_nonneg_right h1 hrn.le

/-! ## Formal bookkeeping -/

theorem amEval_zeroSeries_eq (ν z : ℂ) : amEval ν 0 z = 0 := by simp [amEval]

theorem amEval_finset_sum {ι : Type*} (s : Finset ι) {ν : ℂ} {P : ι → PowerSeries ℂ}
    (hP : ∀ i, P i ∈ SubexpPS) {z : ℂ} (hz : z ∈ imGT 0) :
    amEval ν (∑ i ∈ s, P i) z = ∑ i ∈ s, amEval ν (P i) z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [amEval_zeroSeries_eq]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      amEval_add (hP a) (Subalgebra.sum_mem _ fun i _ => hP i) hz, ih]

theorem coeff_serreF (k : ℤ) (ν : ℂ) (P : PowerSeries ℂ) (m : ℕ) :
    PowerSeries.coeff m (serreF k ν P)
      = (ν + m) * PowerSeries.coeff m P + (k : ℂ) * PowerSeries.coeff m (G1ser * P) := by
  rw [serreF, map_add, coeff_thetaNu, PowerSeries.coeff_smul, smul_eq_mul]

theorem map_G1ser (σ : ℂ →+* ℂ) : PowerSeries.map σ G1ser = G1ser := by
  ext m
  rw [PowerSeries.coeff_map, G1ser, PowerSeries.coeff_mk]
  by_cases hm : m = 0
  · subst hm; rw [zhuG_one_zero]; simp [map_ofNat]
  · rw [zhuG_of_ne_zero 1 hm, lambertCoeff]
    simp [map_sum, map_ofNat]

theorem map_serreF (σ : ℂ →+* ℂ) (k : ℤ) (ν : ℂ) (P : PowerSeries ℂ) :
    PowerSeries.map σ (serreF k ν P) = serreF k (σ ν) (PowerSeries.map σ P) := by
  ext m
  rw [PowerSeries.coeff_map, coeff_serreF, coeff_serreF, map_add, map_mul, map_mul, map_add,
    map_natCast, map_intCast, ← PowerSeries.coeff_map, ← PowerSeries.coeff_map, map_mul,
    map_G1ser]

theorem map_amSerreF (σ : ℂ →+* ℂ) (ν : ℂ) (m : ℕ) (P : PowerSeries ℂ) :
    PowerSeries.map σ (amSerreF ν m P) = amSerreF (σ ν) m (PowerSeries.map σ P) := by
  induction m with
  | zero => rfl
  | succ m ih => rw [amSerreF_succ, amSerreF_succ, map_serreF, ih]

/-! ## Analytic bookkeeping -/

/-- The chain rule for `ϑ^m` and `z ↦ −1/z`, for a single analytic function. -/
theorem amSerreIter_negInv (m : ℕ) {f : ℂ → ℂ} (hf : ∀ z ∈ imGT 0, AnalyticAt ℂ f z)
    {z : ℂ} (hz : z ∈ imGT 0) :
    amSerreIter m f (-1 / z) = z ^ (2 * m) * amSerreIter m (fun w => f (-1 / w)) z := by
  induction m generalizing z with
  | zero => simp
  | succ m ih =>
    have hz0 : z ≠ 0 := ne_zero_of_mem_imGT hz
    have hslash : ∀ w ∈ imGT 0,
        slashC (2 * (m : ℤ)) ModularGroup.S (amSerreIter m f) w
          = amSerreIter m (fun w => f (-1 / w)) w := by
      intro w hw
      have hw0 : w ≠ 0 := ne_zero_of_mem_imGT hw
      rw [slashC, mobiusC_S, denomC_S, ih hw, mul_comm, ← mul_assoc,
        show (w : ℂ) ^ (-(2 * (m : ℤ))) * w ^ (2 * m) = 1 from by
          rw [_root_.zpow_neg, show (2 * (m : ℤ)) = ((2 * m : ℕ) : ℤ) from by push_cast; ring,
            zpow_natCast, inv_mul_cancel₀ (pow_ne_zero _ hw0)], one_mul]
    have hdiff : DifferentiableAt ℂ (amSerreIter m f) (mobiusC ModularGroup.S z) :=
      (analyticAt_amSerreIter m hf (mobiusC_mem_imGT _ hz)).differentiableAt
    have hkey := serreDerivC_slashC (2 * (m : ℤ)) ModularGroup.S (amSerreIter m f) hz hdiff
    have hev : slashC (2 * (m : ℤ)) ModularGroup.S (amSerreIter m f)
        =ᶠ[𝓝 z] amSerreIter m (fun w => f (-1 / w)) := by
      filter_upwards [(isOpen_imGT 0).mem_nhds hz] with w hw
      exact hslash w hw
    rw [serreDerivC_congr_of_eventuallyEq _ hev, slashC, mobiusC_S, denomC_S] at hkey
    rw [amSerreIter_succ, amSerreIter_succ, ← hkey,
      show ((2 * (m : ℤ) + 2)) = ((2 * (m + 1) : ℕ) : ℤ) from by push_cast; ring, _root_.zpow_neg,
      zpow_natCast]
    field_simp

theorem analyticAt_comp_negInv {f : ℂ → ℂ} (hf : ∀ z ∈ imGT 0, AnalyticAt ℂ f z) :
    ∀ z ∈ imGT 0, AnalyticAt ℂ (fun w => f (-1 / w)) z := by
  intro z hz
  have hz0 : z ≠ 0 := ne_zero_of_mem_imGT hz
  have h1 : AnalyticAt ℂ (fun w : ℂ => -1 / w) z := analyticAt_const.div analyticAt_id hz0
  exact (hf _ (neg_one_div_mem_imGT hz)).comp h1

/-- Two analytic functions on the upper half-plane, each nonzero somewhere, are simultaneously
nonzero somewhere. -/
theorem exists_common_ne_zero {f g : ℂ → ℂ} (hf : ∀ z ∈ imGT 0, AnalyticAt ℂ f z)
    (hg : ∀ z ∈ imGT 0, AnalyticAt ℂ g z) {a b : ℂ} (ha : a ∈ imGT 0) (hfa : f a ≠ 0)
    (hb : b ∈ imGT 0) (hgb : g b ≠ 0) : ∃ z ∈ imGT 0, f z ≠ 0 ∧ g z ≠ 0 := by
  by_contra hcon
  push Not at hcon
  -- `g = 0` near `a`, hence everywhere
  have hfa' : ∀ᶠ w in 𝓝 a, f w ≠ 0 := (hf a ha).continuousAt.eventually_ne hfa
  have hloc : g =ᶠ[𝓝 a] 0 := by
    filter_upwards [hfa', (isOpen_imGT 0).mem_nhds ha] with w hw hwm
    exact hcon w hwm hw
  have hgan : AnalyticOnNhd ℂ g (imGT 0) := fun z hz => hg z hz
  have := hgan.eqOn_zero_of_preconnected_of_eventuallyEq_zero (isPreconnected_imGT 0) ha hloc hb
  exact hgb this

theorem amEval_add_nat_mul (ν : ℂ) (U : PowerSeries ℂ) (z : ℂ) (k : ℕ) :
    amEval ν U (z + k) = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ν) ^ k * amEval ν U z := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.cast_succ, ← add_assoc, amEval_add_one, ih, pow_succ]
    ring

theorem eq_zero_of_map_eq_zero (σ : ℂ →+* ℂ) {P : PowerSeries ℂ} (h : PowerSeries.map σ P = 0) :
    P = 0 := by
  ext m
  have := congrArg (PowerSeries.coeff m) h
  rw [PowerSeries.coeff_map, map_zero] at this
  rw [map_zero]
  exact (map_eq_zero_iff σ σ.injective).mp this

/-! ## Steps 2–3: Galois transport of the MLDE -/

/-- **The conjugate family solves the conjugate MLDE**, and the conjugate family is again
`S`-closed. -/
theorem exists_sClosed_conj {n : ℕ} {ν : Fin n → ℂ} {U : Fin n → PowerSeries ℂ}
    (hU : ∀ j, U j ∈ SubexpPS) (hUr : ∀ j, RatCoeffs (U j)) (hν : Function.Injective ν)
    (hU0 : ∀ j, PowerSeries.coeff 0 (U j) ≠ 0) (S : Matrix (Fin n) (Fin n) ℂ)
    (hS : ∀ i, ∀ z ∈ imGT 0, famF ν U i (-1 / z) = ∑ j, S i j * famF ν U j z)
    (σ : ℂ →+* ℂ) :
    ∃ S' : Matrix (Fin n) (Fin n) ℂ, ∀ i, ∀ z ∈ imGT 0,
      famF (fun j => σ (ν j)) U i (-1 / z) = ∑ j, S' i j * famF (fun j => σ (ν j)) U j z := by
  classical
  obtain ⟨k, B, A, ⟨z₁, hz₁, hB₁⟩, hode⟩ := exists_mlde hU hν hU0 S hS
  have hqB : qExpansion 1 B ∈ SubexpPS := qExpansion_mem_subexpPS B
  have hqA : ∀ r, qExpansion 1 (A r) ∈ SubexpPS := fun r => qExpansion_mem_subexpPS (A r)
  have hP : ∀ (μ : ℂ) (m : ℕ) j, amSerreF μ m (U j) ∈ SubexpPS := fun μ m j =>
    amSerreF_mem μ m (hU j)
  -- the formal identity
  have hformal : ∀ j, qExpansion 1 B * amSerreF (ν j) n (U j)
      = ∑ r : Fin n, qExpansion 1 (A r) * amSerreF (ν j) r (U j) := by
    intro j
    refine eq_of_amEval_eq (ν := ν j) (SubexpPS.mul_mem hqB (hP _ _ j))
      (Subalgebra.sum_mem _ fun r _ => SubexpPS.mul_mem (hqA r) (hP _ _ j)) fun z hz => ?_
    rw [← amEval_mul hqB (hP _ _ j) _ hz,
      amEval_finset_sum _ (fun r => SubexpPS.mul_mem (hqA r) (hP _ _ j)) hz,
      ← modularForm_eq_amEval B hz, ← amSerreIter_amEval _ n (hU j) hz]
    have h1 := hode j z hz
    simp only [famF] at h1
    rw [h1]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [← amEval_mul (hqA r) (hP _ _ j) _ hz, ← modularForm_eq_amEval (A r) hz,
      amSerreIter_amEval _ r (hU j) hz]
  -- the conjugate forms
  obtain ⟨B', hB'⟩ := exists_modularForm_qExpansion_map σ _ B
  choose A' hA' using fun r => exists_modularForm_qExpansion_map σ _ (A r)
  set ν' : Fin n → ℂ := fun j => σ (ν j) with hν'def
  have hν' : Function.Injective ν' := σ.injective.comp hν
  have hqB' : qExpansion 1 B' ∈ SubexpPS := qExpansion_mem_subexpPS B'
  have hqA' : ∀ r, qExpansion 1 (A' r) ∈ SubexpPS := fun r => qExpansion_mem_subexpPS (A' r)
  have hformal' : ∀ j, qExpansion 1 B' * amSerreF (ν' j) n (U j)
      = ∑ r : Fin n, qExpansion 1 (A' r) * amSerreF (ν' j) r (U j) := by
    intro j
    have h := congrArg (PowerSeries.map σ) (hformal j)
    rw [map_mul, map_sum, map_amSerreF, (hUr j).map_eq σ, ← hB'] at h
    rw [h]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [map_mul, map_amSerreF, (hUr j).map_eq σ, ← hA' r]
  have hode' : ∀ j, ∀ z ∈ imGT 0, B' (ofComplex z) * amSerreIter n (famF ν' U j) z
      = ∑ r : Fin n, A' r (ofComplex z) * amSerreIter r (famF ν' U j) z := by
    intro j z hz
    simp only [famF]
    rw [modularForm_eq_amEval B' hz, amSerreIter_amEval _ n (hU j) hz,
      amEval_mul hqB' (hP _ _ j) _ hz, hformal' j,
      amEval_finset_sum _ (fun r => SubexpPS.mul_mem (hqA' r) (hP _ _ j)) hz]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [modularForm_eq_amEval (A' r) hz, amSerreIter_amEval _ r (hU j) hz,
      amEval_mul (hqA' r) (hP _ _ j) _ hz]
  -- `B'` is not identically zero
  have hB'ne : ∃ z ∈ imGT 0, B' (ofComplex z) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have h0 : PowerSeries.map σ (qExpansion 1 B) = 0 := by
      rw [← hB']
      refine eq_zero_of_amEval_zero hqB' fun y hy => ?_
      rw [← modularForm_eq_amEval B' (I_mul_mem_imGT hy)]
      exact hcon _ (I_mul_mem_imGT hy)
    have h0' := eq_zero_of_map_eq_zero σ h0
    apply hB₁
    rw [modularForm_eq_amEval B hz₁, h0', amEval_zeroSeries_eq]
  have hf' := analyticAt_famF ν' hU
  obtain ⟨b, hb, hWb⟩ := exists_wr_ne_zero hU hν' hU0
  obtain ⟨a, ha, hBa⟩ := hB'ne
  obtain ⟨z₀, hz₀, hB₀, hW₀⟩ := exists_common_ne_zero
    (fun z hz => analyticAt_slashInv B' hz) (fun z hz => analyticAt_wr hf' hz) ha hBa hb hWb
  -- each conjugate function, composed with `S`, lies in the span
  have hspan : ∀ i, ∃ c : Fin n → ℂ, ∀ z ∈ imGT 0,
      famF ν' U i (-1 / z) = ∑ j, c j * famF ν' U j z := by
    intro i
    refine exists_eq_sum_of_serreODE (fun z => B' (ofComplex z)) (fun r z => A' r (ofComplex z))
      (famF ν' U) (fun z => famF ν' U i (-1 / z))
      (fun z hz => analyticAt_slashInv B' hz) (fun r z hz => analyticAt_slashInv (A' r) hz)
      hf' (analyticAt_comp_negInv (hf' i)) hode' ?_ hz₀ hB₀ hW₀
    intro z hz
    have hz0 : z ≠ 0 := ne_zero_of_mem_imGT hz
    have hm := neg_one_div_mem_imGT hz
    have h := hode' i (-1 / z) hm
    rw [slashInv_S_apply B' hz, amSerreIter_negInv n (hf' i) hz] at h
    have hsum : ∀ r : Fin n, A' r (ofComplex (-1 / z)) * amSerreIter r (famF ν' U i) (-1 / z)
        = z ^ k * z ^ (2 * n) *
          (A' r (ofComplex z) * amSerreIter r (fun w => famF ν' U i (-1 / w)) z) := by
      intro r
      rw [slashInv_S_apply (A' r) hz, amSerreIter_negInv r (hf' i) hz, zpow_natCast]
      have : z ^ (k + 2 * (n - (r : ℕ))) * z ^ (2 * (r : ℕ)) = z ^ k * z ^ (2 * n) := by
        rw [← pow_add, ← pow_add]; congr 1; have := r.isLt; omega
      linear_combination (A' r (ofComplex z) *
        amSerreIter r (fun w => famF ν' U i (-1 / w)) z) * this
    rw [Finset.sum_congr rfl fun r _ => hsum r, ← Finset.mul_sum, zpow_natCast] at h
    have hne : z ^ k * z ^ (2 * n) ≠ 0 := mul_ne_zero (pow_ne_zero _ hz0) (pow_ne_zero _ hz0)
    apply mul_left_cancel₀ hne
    linear_combination h
  choose S' hS' using hspan
  exact ⟨Matrix.of S', fun i z hz => by simpa using hS' i z hz⟩

/-! ## Steps 5–6: rigidity and the Galois conclusion -/

theorem famF_conj_eq {n : ℕ} (ν : Fin n → ℂ) (U : Fin n → PowerSeries ℂ) (σ : ℂ →+* ℂ)
    (i : Fin n) (x : ℂ) :
    famF (fun j => σ (ν j)) U i x
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * x * (σ (ν i) - ν i)) * famF ν U i x := by
  simp only [famF]
  rw [amEval_eq_exp_mul, amEval_eq_exp_mul (ν i), ← mul_assoc, ← Complex.exp_add]
  congr 2
  ring

/-- **Every exponent is fixed by every field endomorphism of `ℂ`.** -/
theorem conj_fixed_of_sClosed {n : ℕ} {ν : Fin n → ℂ} {U : Fin n → PowerSeries ℂ}
    (hU : ∀ j, U j ∈ SubexpPS) (hUr : ∀ j, RatCoeffs (U j)) (hν : Function.Injective ν)
    (hU0 : ∀ j, PowerSeries.coeff 0 (U j) ≠ 0) (S : Matrix (Fin n) (Fin n) ℂ)
    (hS : ∀ i, ∀ z ∈ imGT 0, famF ν U i (-1 / z) = ∑ j, S i j * famF ν U j z)
    (σ : ℂ →+* ℂ) (i : Fin n) : σ (ν i) = ν i := by
  classical
  obtain ⟨S', hS'⟩ := exists_sClosed_conj hU hUr hν hU0 S hS σ
  set ν' : Fin n → ℂ := fun j => σ (ν j) with hν'def
  -- a point where `F_i ≠ 0`
  obtain ⟨y, hy, hy0⟩ := (((tendsto_amEval_zero (hU i)).eventually_ne (hU0 i)).and
    (eventually_gt_atTop (0 : ℝ))).exists
  set z₁ : ℂ := Complex.I * y
  have hz₁ : z₁ ∈ imGT 0 := I_mul_mem_imGT hy0
  have hF₁ : famF ν U i z₁ ≠ 0 := by
    simp only [famF]; rw [amEval_eq_exp_mul]
    exact mul_ne_zero (Complex.exp_ne_zero _) hy
  set w : ℂ := -1 / z₁
  have hw : w ∈ imGT 0 := neg_one_div_mem_imGT hz₁
  have hww : -1 / w = z₁ := by
    have := ne_zero_of_mem_imGT hz₁
    simp only [w]; field_simp
  have hwk : ∀ k : ℕ, w + k ∈ imGT 0 := fun k => by
    change (0 : ℝ) < (w + k).im
    simpa using hw
  have hδ := eq_zero_of_expPoly_eq_exp_mul (fun j => S i j * famF ν U j w) (tvec ν)
    (fun j => S' i j * famF ν' U j w) (tvec ν') (fun _ => Complex.exp_ne_zero _)
    (fun _ => Complex.exp_ne_zero _) (w := w) (δ := σ (ν i) - ν i) hw
    (by rw [← hS i w hw, hww]; exact hF₁) (fun k => ?_)
  · exact sub_eq_zero.mp hδ
  · have h1 : ∑ j, S' i j * famF ν' U j w * tvec ν' j ^ k = famF ν' U i (-1 / (w + k)) := by
      rw [hS' i _ (hwk k)]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [famF, tvec]
      rw [amEval_add_nat_mul]; ring
    have h2 : ∑ j, S i j * famF ν U j w * tvec ν j ^ k = famF ν U i (-1 / (w + k)) := by
      rw [hS i _ (hwk k)]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [famF, tvec]
      rw [amEval_add_nat_mul]; ring
    rw [h1, h2, famF_conj_eq ν U σ i]
    congr 2
    have hne : w + k ≠ 0 := ne_zero_of_mem_imGT (hwk k)
    field_simp

/-- **The Anderson–Moore core theorem**: an `S`-closed `q^ν`-family with rational
coefficients, distinct exponents and nonzero leading coefficients has rational exponents. -/
theorem rat_of_sClosed {n : ℕ} {ν : Fin n → ℂ} {U : Fin n → PowerSeries ℂ}
    (hU : ∀ j, U j ∈ SubexpPS) (hUr : ∀ j, RatCoeffs (U j)) (hν : Function.Injective ν)
    (hU0 : ∀ j, PowerSeries.coeff 0 (U j) ≠ 0) (S : Matrix (Fin n) (Fin n) ℂ)
    (hS : ∀ i, ∀ z ∈ imGT 0, famF ν U i (-1 / z) = ∑ j, S i j * famF ν U j z) (i : Fin n) :
    ∃ q : ℚ, (q : ℂ) = ν i :=
  exists_rat_eq_of_forall_ringHom fun σ => conj_fixed_of_sClosed hU hUr hν hU0 S hS σ i

end VOA.Huang.AndersonMoore
