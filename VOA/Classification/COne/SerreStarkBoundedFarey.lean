/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.SerreStarkBoundedMean

/-!
# Serre–Stark S5-2b: the Farey-arc majorant and its integral

For `0 < y ≤ 1/4` and `Q = ⌊y^{-1/2}⌋`, every `x ∈ [0, 1]` lies within `1/Q` (in the sense
`|cx − a| ≤ 1/Q`) of a fraction `a/c` with `1 ≤ c ≤ Q` (Dirichlet), and then
`nf f (x + iy) ≤ K √y / max(|cx − a|, cy)` (`nf_le_farey`). The majorant

`Σ_{c ≤ Q} Σ_{0 ≤ a ≤ c} 1[|cx − a| ≤ 1/Q] / max(|cx − a|, cy)`

has integral `O(y^{-1/2})` over `[0, 1]` (`integral_fareySum_le`: the pieces give
`(2/c)(1 + log (1/(Q c y)))`, and `Σ_{c ≤ Q} log (Q/c) = log (Q^Q / Q!) ≤ Q`).
-/

open Complex MeasureTheory Set
open scoped MatrixGroups UpperHalfPlane

noncomputable section

namespace VOA.Classification.COne

namespace SSHecke

/-! ## Elementary integrals -/

theorem continuous_inv_max_abs {ε : ℝ} (hε : 0 < ε) :
    Continuous fun u : ℝ => 1 / max |u| ε := by
  refine Continuous.div continuous_const (continuous_abs.max continuous_const) fun u => ?_
  exact (lt_of_lt_of_le hε (le_max_right _ _)).ne'

theorem integral_inv_max_pos {ε R : ℝ} (hε : 0 < ε) (hεR : ε ≤ R) :
    ∫ u in (0 : ℝ)..R, 1 / max |u| ε = 1 + Real.log (R / ε) := by
  have hc := continuous_inv_max_abs hε
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := ε)
    (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  have h1 : ∫ u in (0 : ℝ)..ε, 1 / max |u| ε = ∫ u in (0 : ℝ)..ε, 1 / ε := by
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [uIcc_of_le hε.le] at hu
    rw [abs_of_nonneg hu.1, max_eq_right hu.2]
  have h2 : ∫ u in ε..R, 1 / max |u| ε = ∫ u in ε..R, u⁻¹ := by
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [uIcc_of_le hεR] at hu
    rw [abs_of_nonneg (hε.le.trans hu.1), max_eq_left hu.1, one_div]
  rw [h1, h2, integral_inv_of_pos hε (lt_of_lt_of_le hε hεR)]
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  field_simp

theorem integral_inv_max_symm {ε R : ℝ} (hε : 0 < ε) (hεR : ε ≤ R) :
    ∫ u in (-R)..R, 1 / max |u| ε = 2 * (1 + Real.log (R / ε)) := by
  have hc := continuous_inv_max_abs hε
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0)
    (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  have hneg : ∫ u in (-R)..0, 1 / max |u| ε = ∫ u in (0 : ℝ)..R, 1 / max |u| ε := by
    have := intervalIntegral.integral_comp_neg (a := 0) (b := R) (fun u : ℝ => 1 / max |u| ε)
    simp only [abs_neg, neg_zero] at this
    rw [this]
  rw [hneg, integral_inv_max_pos hε hεR]
  ring

/-- The integral of one Farey piece over its arc. -/
theorem integral_farey_arc {c y R a : ℝ} (hc : 0 < c) (hy : 0 < y) (hεR : c * y ≤ R) :
    ∫ x in ((a - R) / c)..((a + R) / c), 1 / max |c * x - a| (c * y) =
      2 / c * (1 + Real.log (R / (c * y))) := by
  have hcy : 0 < c * y := mul_pos hc hy
  rw [intervalIntegral.integral_comp_mul_sub (fun u => 1 / max |u| (c * y)) hc.ne' a]
  have e1 : c * ((a - R) / c) - a = -R := by field_simp; ring
  have e2 : c * ((a + R) / c) - a = R := by field_simp; ring
  rw [e1, e2, integral_inv_max_symm hcy hεR, smul_eq_mul]
  field_simp

/-- An indicator integral over `[0, 1]` is at most the integral over the support interval. -/
theorem integral_indicator_le {α β : ℝ} (hαβ : α ≤ β) {g : ℝ → ℝ} (hg : Continuous g)
    (hg0 : ∀ x, 0 ≤ g x) :
    ∫ x in (0 : ℝ)..1, (Icc α β).indicator g x ≤ ∫ x in α..β, g x := by
  have hint : Integrable ((Icc α β).indicator g) :=
    (hg.continuousOn.integrableOn_Icc).integrable_indicator measurableSet_Icc
  rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le hαβ,
    ← integral_Icc_eq_integral_Ioc (x := α)]
  calc ∫ x in Ioc (0 : ℝ) 1, (Icc α β).indicator g x ≤ ∫ x, (Icc α β).indicator g x :=
        setIntegral_le_integral hint (Filter.Eventually.of_forall fun x =>
          Set.indicator_nonneg (fun x _ => hg0 x) x)
    _ = ∫ x in Icc α β, g x := integral_indicator measurableSet_Icc


/-! ## The Farey majorant -/

/-- `Q = ⌊y^{-1/2}⌋`. -/
def fareyQ (y : ℝ) : ℕ := ⌊(Real.sqrt y)⁻¹⌋₊

/-- One Farey piece `1[|cx − a| ≤ 1/Q] / max(|cx − a|, cy)`. -/
def fareyPiece (Q : ℕ) (y : ℝ) (c : ℕ) (a : ℤ) (x : ℝ) : ℝ :=
  (Icc (((a : ℝ) - 1 / Q) / c) (((a : ℝ) + 1 / Q) / c)).indicator
    (fun x => 1 / max |(c : ℝ) * x - a| (c * y)) x

/-- The Farey majorant `Σ_{1 ≤ c ≤ Q} Σ_{0 ≤ a ≤ c}` of the pieces. -/
def fareySum (y : ℝ) (x : ℝ) : ℝ :=
  ∑ c ∈ Finset.Icc 1 (fareyQ y), ∑ a ∈ Finset.Icc (0 : ℤ) c, fareyPiece (fareyQ y) y c a x

theorem fareyPiece_nonneg (Q : ℕ) {y : ℝ} (hy : 0 < y) {c : ℕ} (hc : 1 ≤ c) (a : ℤ) (x : ℝ) :
    0 ≤ fareyPiece Q y c a x := by
  unfold fareyPiece
  refine Set.indicator_nonneg (fun x _ => ?_) x
  have : 0 < (c : ℝ) * y := mul_pos (by exact_mod_cast hc) hy
  positivity

theorem fareySum_nonneg {y : ℝ} (hy : 0 < y) (x : ℝ) : 0 ≤ fareySum y x :=
  Finset.sum_nonneg fun c hc => Finset.sum_nonneg fun a _ =>
    fareyPiece_nonneg _ hy (Finset.mem_Icc.1 hc).1 a x

/-- Elementary facts about `Q = ⌊y^{-1/2}⌋` for `0 < y ≤ 1/4`. -/
theorem fareyQ_facts {y : ℝ} (hy0 : 0 < y) (hy : y ≤ 1 / 4) :
    1 ≤ fareyQ y ∧ (fareyQ y : ℝ) * Real.sqrt y ≤ 1 ∧ (Real.sqrt y)⁻¹ ≤ 2 * fareyQ y := by
  have hs : 0 < Real.sqrt y := Real.sqrt_pos.2 hy0
  have hs2 : Real.sqrt y ≤ 1 / 2 := by
    rw [show (1 / 2 : ℝ) = Real.sqrt (1 / 4) by
      rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hy
  have hinv : 2 ≤ (Real.sqrt y)⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hs]; linarith
  have hfl := Nat.floor_le (a := (Real.sqrt y)⁻¹) (by positivity)
  have hlt := Nat.lt_floor_add_one (a := (Real.sqrt y)⁻¹)
  unfold fareyQ
  refine ⟨?_, ?_, ?_⟩
  · have : (1 : ℝ) < ⌊(Real.sqrt y)⁻¹⌋₊ + 1 := by linarith
    exact_mod_cast (show (1 : ℝ) ≤ ⌊(Real.sqrt y)⁻¹⌋₊ by
      have h1 : (1 : ℝ) ≤ ⌊(Real.sqrt y)⁻¹⌋₊ := by
        have := Nat.le_floor (n := 1) (a := (Real.sqrt y)⁻¹) (by push_cast; linarith)
        exact_mod_cast this
      exact h1)
  · calc (⌊(Real.sqrt y)⁻¹⌋₊ : ℝ) * Real.sqrt y ≤ (Real.sqrt y)⁻¹ * Real.sqrt y :=
          mul_le_mul_of_nonneg_right hfl hs.le
      _ = 1 := inv_mul_cancel₀ hs.ne'
  · linarith


/-! ## The pointwise Farey bound -/

/-- Dirichlet approximation by a reduced fraction `a/c`, `1 ≤ c ≤ Q`, `0 ≤ a ≤ c`. -/
theorem exists_farey_frac {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) {Q : ℕ} (hQ : 1 ≤ Q) :
    ∃ (c : ℕ) (a : ℤ), 1 ≤ c ∧ c ≤ Q ∧ 0 ≤ a ∧ a ≤ c ∧ |(c : ℝ) * x - a| ≤ 1 / Q ∧
      IsCoprime a (c : ℤ) := by
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  obtain ⟨j, k, hk0, hkQ, hjk⟩ := Real.exists_int_int_abs_mul_sub_le x (n := Q) hQ
  have hgpos : 0 < Int.gcd j k := Int.gcd_pos_of_ne_zero_right j hk0.ne'
  obtain ⟨d, a, c₀, hd0, hgcd, hjd, hkd⟩ := Int.exists_gcd_one' hgpos
  have hc₀pos : 0 < c₀ := by
    by_contra h
    push Not at h
    have : k ≤ 0 := by rw [hkd]; exact mul_nonpos_of_nonpos_of_nonneg h (by positivity)
    omega
  have hc₀k : c₀ ≤ k := by
    rw [hkd]; exact le_mul_of_one_le_right hc₀pos.le (by exact_mod_cast hd0)
  have hcop : IsCoprime a c₀ := Int.isCoprime_iff_gcd_eq_one.2 hgcd
  set c : ℕ := c₀.toNat with hcdef
  have hcc : (c : ℤ) = c₀ := Int.toNat_of_nonneg hc₀pos.le
  have hcR : (c : ℝ) = (c₀ : ℝ) := by exact_mod_cast hcc
  -- the approximation
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd0
  have e : (k : ℝ) * x - j = d * ((c : ℝ) * x - a) := by
    rw [hkd, hjd, hcR]; push_cast; ring
  rw [e, abs_mul, abs_of_pos (by positivity)] at hjk
  have happ : |(c : ℝ) * x - a| ≤ 1 / (Q + 1) :=
    (le_mul_of_one_le_left (abs_nonneg _) hdR).trans hjk
  have hQ1 : 1 / ((Q : ℝ) + 1) ≤ 1 / 2 := by
    have : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
    exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hcx : 0 ≤ (c : ℝ) * x := mul_nonneg (by positivity) hx.1
  have hcx1 : (c : ℝ) * x ≤ c := mul_le_of_le_one_right (by positivity) hx.2
  have h2 : 1 / ((Q : ℝ) + 1) ≤ 1 / Q := one_div_le_one_div_of_le hQR (by linarith)
  obtain ⟨hl, hr⟩ := abs_le.1 happ
  have ha0 : 0 ≤ a := by
    have : (-1 : ℝ) < a := by linarith
    have : (-1 : ℤ) < a := by exact_mod_cast this
    omega
  have hac : a ≤ c := by
    have : (a : ℝ) < (c : ℝ) + 1 := by linarith
    have : a < (c : ℤ) + 1 := by exact_mod_cast this
    omega
  refine ⟨c, a, by omega, by omega, ha0, hac, abs_le.2 ⟨by linarith, by linarith⟩, ?_⟩
  rwa [hcc]

/-- A matrix in `SL₂(ℤ)` with bottom row `(c, -a)` for coprime `a, c`. -/
theorem exists_SL_bottom {a c : ℤ} (h : IsCoprime a c) :
    ∃ g : SL(2, ℤ), g 1 0 = c ∧ g 1 1 = -a := by
  obtain ⟨u, v, huv⟩ := h
  exact ⟨⟨!![-u, -v; c, -a], by rw [Matrix.det_fin_two_of]; linear_combination huv⟩, rfl, rfl⟩

theorem norm_denom_sq {c a x y : ℝ} :
    ‖(c : ℂ) * ((x : ℂ) + (y : ℂ) * I) - a‖ ^ 2 = (c * x - a) ^ 2 + (c * y) ^ 2 := by
  have : (c : ℂ) * ((x : ℂ) + (y : ℂ) * I) - a = ((c * x - a : ℝ) : ℂ) + ((c * y : ℝ) : ℂ) * I := by
    push_cast; ring
  rw [this, ← Complex.normSq_eq_norm_sq, Complex.normSq_add_mul_I]

/-- **Pointwise Farey bound**: `nf f (x + iy) ≤ K √y · fareySum y x` for `x ∈ [0,1]`,
`0 < y ≤ 1/4`, given the uniform cusp bound `nf f (g w) ≤ K √(Im w)` (`Im w ≥ 1/5`). -/
theorem nf_le_fareySum {f : ℂ → ℂ} {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ g : SL(2, ℤ), ∀ w : ℂ, 1 / 5 ≤ w.im → nf f (mobius g w) ≤ K * Real.sqrt w.im)
    {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hy0 : 0 < y) (hy : y ≤ 1 / 4) :
    nf f ((x : ℂ) + (y : ℂ) * I) ≤ K * Real.sqrt y * fareySum y x := by
  obtain ⟨hQ1, hQs, hQinv⟩ := fareyQ_facts hy0 hy
  obtain ⟨c, a, hc1, hcQ, ha0, hac, happ, hcop⟩ := exists_farey_frac hx hQ1
  obtain ⟨g, g10, g11⟩ := exists_SL_bottom hcop
  have hQR : (0 : ℝ) < fareyQ y := by exact_mod_cast hQ1
  have hs : 0 < Real.sqrt y := Real.sqrt_pos.2 hy0
  have hcR : (1 : ℝ) ≤ c := by exact_mod_cast hc1
  have hcQR : (c : ℝ) ≤ fareyQ y := by exact_mod_cast hcQ
  set τ : ℂ := (x : ℂ) + (y : ℂ) * I with hτdef
  have hτ : 0 < τ.im := by simp [hτdef, hy0]
  have hτy : τ.im = y := by simp [hτdef]
  have hden : (g 1 0 : ℂ) * τ + g 1 1 = ((c : ℝ) : ℂ) * τ - ((a : ℝ) : ℂ) := by
    rw [g10, g11]; push_cast; ring
  have hDsq : ‖(g 1 0 : ℂ) * τ + g 1 1‖ ^ 2 = ((c : ℝ) * x - a) ^ 2 + ((c : ℝ) * y) ^ 2 := by
    rw [hden, hτdef, norm_denom_sq]
  set D := ‖(g 1 0 : ℂ) * τ + g 1 1‖ with hDdef
  have hD0 : 0 ≤ D := norm_nonneg _
  have hDre : |(c : ℝ) * x - a| ≤ D := by
    have h1 : ((c : ℝ) * x - a) ^ 2 ≤ D ^ 2 := by rw [hDsq]; nlinarith
    exact abs_le.2 (abs_le_of_sq_le_sq' h1 hD0)
  have hDim : (c : ℝ) * y ≤ D := by
    have h1 : ((c : ℝ) * y) ^ 2 ≤ D ^ 2 := by rw [hDsq]; nlinarith
    exact abs_le_of_sq_le_sq' h1 hD0 |>.2
  have hcy : 0 < (c : ℝ) * y := by positivity
  have hDpos : 0 < D := lt_of_lt_of_le hcy hDim
  -- `Im (g τ) ≥ 1/5`
  have h1 : ((c : ℝ) * x - a) ^ 2 ≤ 4 * y := by
    have h2 : ((c : ℝ) * x - a) ^ 2 ≤ (1 / fareyQ y) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) happ 2
    have h3 : (1 / (fareyQ y : ℝ)) ≤ 2 * Real.sqrt y := by
      rw [div_le_iff₀ hQR]
      have := mul_le_mul_of_nonneg_left hQinv hs.le
      rw [mul_inv_cancel₀ hs.ne'] at this
      linarith
    have h4 : (1 / (fareyQ y : ℝ)) ^ 2 ≤ (2 * Real.sqrt y) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h3 2
    rw [mul_pow, Real.sq_sqrt hy0.le] at h4
    linarith
  have h5 : ((c : ℝ) * y) ^ 2 ≤ y := by
    have h6 : (c : ℝ) * Real.sqrt y ≤ 1 := (mul_le_mul_of_nonneg_right hcQR hs.le).trans hQs
    have h7 : ((c : ℝ) * Real.sqrt y) ^ 2 ≤ 1 := pow_le_one₀ (by positivity) h6
    have e : ((c : ℝ) * y) ^ 2 = ((c : ℝ) * Real.sqrt y) ^ 2 * y := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hy0.le]; ring
    rw [e]
    calc ((c : ℝ) * Real.sqrt y) ^ 2 * y ≤ 1 * y := mul_le_mul_of_nonneg_right h7 hy0.le
      _ = y := one_mul y
  have hw : 1 / 5 ≤ (mobius g τ).im := by
    rw [im_mobius_eq g hτ, ← hDdef, hτy, le_div_iff₀ (by positivity), hDsq]
    linarith
  -- transport back
  have hτback : mobius g⁻¹ (mobius g τ) = τ := by
    rw [← mobius_mul _ _ hτ, inv_mul_cancel, mobius_one]
  have hb := hK g⁻¹ (mobius g τ) hw
  rw [hτback] at hb
  have hsq : Real.sqrt (mobius g τ).im = Real.sqrt y / D := by
    rw [im_mobius_eq g hτ, ← hDdef, Real.sqrt_div' _ (by positivity), Real.sqrt_sq hD0, hτy]
  rw [hsq] at hb
  -- the chosen piece
  have hmax : 0 < max |(c : ℝ) * x - a| ((c : ℝ) * y) :=
    lt_of_lt_of_le hcy (le_max_right _ _)
  have hpiece : fareyPiece (fareyQ y) y c a x = 1 / max |(c : ℝ) * x - a| ((c : ℝ) * y) := by
    unfold fareyPiece
    rw [Set.indicator_of_mem]
    have hc0 : (0 : ℝ) < c := by linarith
    rw [abs_le] at happ
    constructor
    · rw [div_le_iff₀ hc0]; linarith
    · rw [le_div_iff₀ hc0]; linarith
  have hle_sum : fareyPiece (fareyQ y) y c a x ≤ fareySum y x := by
    unfold fareySum
    refine le_trans ?_ (Finset.single_le_sum (f := fun c : ℕ => ∑ a ∈ Finset.Icc (0 : ℤ) (c : ℤ),
      fareyPiece (fareyQ y) y c a x) (fun c hc => Finset.sum_nonneg fun a _ =>
        fareyPiece_nonneg _ hy0 (Finset.mem_Icc.1 hc).1 a x)
      (Finset.mem_Icc.2 ⟨hc1, hcQ⟩))
    exact Finset.single_le_sum (f := fun a => fareyPiece (fareyQ y) y c a x)
      (fun a _ => fareyPiece_nonneg _ hy0 hc1 a x) (Finset.mem_Icc.2 ⟨ha0, hac⟩)
  calc nf f τ ≤ K * (Real.sqrt y / D) := hb
    _ ≤ K * (Real.sqrt y / max |(c : ℝ) * x - a| ((c : ℝ) * y)) := by
        refine mul_le_mul_of_nonneg_left ?_ hK0
        exact div_le_div_of_nonneg_left hs.le hmax (max_le hDre hDim)
    _ = K * Real.sqrt y * fareyPiece (fareyQ y) y c a x := by rw [hpiece]; ring
    _ ≤ K * Real.sqrt y * fareySum y x :=
        mul_le_mul_of_nonneg_left hle_sum (by positivity)


/-! ## The integral of the majorant -/

/-- `Σ_{c=1}^{Q} log (Q/c) = log (Q^Q / Q!) ≤ Q`. -/
theorem sum_log_div_le (Q : ℕ) :
    ∑ c ∈ Finset.Icc 1 Q, Real.log ((Q : ℝ) / c) ≤ Q := by
  rcases Nat.eq_zero_or_pos Q with rfl | hQ
  · simp
  have hne : ∀ c ∈ Finset.Icc 1 Q, ((Q : ℝ) / c) ≠ 0 := by
    intro c hc
    have := (Finset.mem_Icc.1 hc).1
    have : (0 : ℝ) < c := by exact_mod_cast this
    have : (0 : ℝ) < Q := by exact_mod_cast hQ
    positivity
  rw [← Real.log_prod hne]
  have hprod : ∏ c ∈ Finset.Icc 1 Q, ((Q : ℝ) / c) = (Q : ℝ) ^ Q / (Q.factorial : ℝ) := by
    rw [Finset.prod_div_distrib, Finset.prod_const, Nat.card_Icc, Nat.add_sub_cancel]
    congr 1
    rw [← Finset.Ico_add_one_right_eq_Icc, ← Nat.cast_prod (f := fun c => c),
      Finset.prod_Ico_id_eq_factorial]
  rw [hprod]
  have hpos : 0 < (Q : ℝ) ^ Q / (Q.factorial : ℝ) := by
    have : (0 : ℝ) < Q := by exact_mod_cast hQ
    positivity
  calc Real.log ((Q : ℝ) ^ Q / (Q.factorial : ℝ)) ≤ Real.log (Real.exp Q) :=
        Real.log_le_log hpos (Real.pow_div_factorial_le_exp (Q : ℝ) (by positivity) Q)
    _ = Q := Real.log_exp _

theorem continuous_farey (c y a : ℝ) (hcy : 0 < c * y) :
    Continuous fun x : ℝ => 1 / max |c * x - a| (c * y) :=
  (continuous_inv_max_abs hcy).comp ((continuous_const.mul continuous_id).sub continuous_const)

theorem integrable_fareyPiece (Q : ℕ) {y : ℝ} (hy : 0 < y) {c : ℕ} (hc : 1 ≤ c) (a : ℤ) :
    Integrable (fareyPiece Q y c a) := by
  have hcy : 0 < (c : ℝ) * y := mul_pos (by exact_mod_cast hc) hy
  exact ((continuous_farey (c : ℝ) y a hcy).continuousOn.integrableOn_Icc).integrable_indicator
    measurableSet_Icc

theorem integral_fareyPiece_le {Q : ℕ} (hQ : 1 ≤ Q) {y : ℝ} (hy : 0 < y) {c : ℕ} (hc : 1 ≤ c)
    (hcy : (c : ℝ) * y ≤ 1 / Q) (a : ℤ) :
    ∫ x in (0 : ℝ)..1, fareyPiece Q y c a x ≤ 2 / c * (1 + Real.log ((1 / Q) / (c * y))) := by
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hcy0 : 0 < (c : ℝ) * y := mul_pos hcR hy
  have hab : ((a : ℝ) - 1 / Q) / c ≤ ((a : ℝ) + 1 / Q) / c :=
    div_le_div_of_nonneg_right (by
      have : (0 : ℝ) < 1 / Q := by positivity
      linarith) hcR.le
  unfold fareyPiece
  refine (integral_indicator_le hab (continuous_farey _ _ _ hcy0) (fun x => ?_)).trans ?_
  · positivity
  · rw [integral_farey_arc hcR hy hcy]

/-- **The Farey majorant integrates to `O(y^{-1/2})`.** -/
theorem integral_fareySum_le {y : ℝ} (hy0 : 0 < y) (hy : y ≤ 1 / 4) :
    ∫ x in (0 : ℝ)..1, fareySum y x ≤ 4 * (2 + Real.log 4) * (Real.sqrt y)⁻¹ := by
  obtain ⟨hQ1, hQs, hQinv⟩ := fareyQ_facts hy0 hy
  set Q := fareyQ y with hQdef
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ1
  have hs : 0 < Real.sqrt y := Real.sqrt_pos.2 hy0
  have hQle : (Q : ℝ) ≤ (Real.sqrt y)⁻¹ := by
    calc (Q : ℝ) = Q * Real.sqrt y * (Real.sqrt y)⁻¹ := by field_simp
      _ ≤ 1 * (Real.sqrt y)⁻¹ := mul_le_mul_of_nonneg_right hQs (inv_nonneg.2 hs.le)
      _ = (Real.sqrt y)⁻¹ := one_mul _
  -- `Q y ≤ 1/Q` and `1/(Q y) ≤ 4 Q`
  have hQy : (Q : ℝ) * y ≤ 1 / Q := by
    rw [le_div_iff₀ hQR]
    have : (Q : ℝ) * Real.sqrt y * ((Q : ℝ) * Real.sqrt y) ≤ 1 :=
      by nlinarith [mul_nonneg hQR.le hs.le]
    calc (Q : ℝ) * y * Q = (Q : ℝ) * Real.sqrt y * ((Q : ℝ) * Real.sqrt y) := by
          rw [show (Q : ℝ) * Real.sqrt y * ((Q : ℝ) * Real.sqrt y) =
            (Q : ℝ) ^ 2 * (Real.sqrt y) ^ 2 by ring, Real.sq_sqrt hy0.le]; ring
      _ ≤ 1 := this
  have hinvy : 1 / ((Q : ℝ) * y) ≤ 4 * Q := by
    have h1 : 1 / y ≤ (2 * (Q : ℝ)) ^ 2 := by
      have := pow_le_pow_left₀ (by positivity) hQinv 2
      rwa [inv_pow, Real.sq_sqrt hy0.le, ← one_div] at this
    rw [div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ hy0] at h1
    nlinarith
  -- integrate termwise
  unfold fareySum
  rw [← hQdef]
  have hint : ∀ c ∈ Finset.Icc 1 Q, IntervalIntegrable
      (fun x => ∑ a ∈ Finset.Icc (0 : ℤ) c, fareyPiece Q y c a x) MeasureTheory.volume 0 1 :=
    fun c hc => (integrable_finset_sum _ fun a _ =>
      integrable_fareyPiece Q hy0 (Finset.mem_Icc.1 hc).1 a).intervalIntegrable
  rw [intervalIntegral.integral_finsetSum hint]
  have hterm : ∀ c ∈ Finset.Icc 1 Q, ∫ x in (0 : ℝ)..1, ∑ a ∈ Finset.Icc (0 : ℤ) c,
      fareyPiece Q y c a x ≤ 4 * (1 + Real.log 4 + Real.log ((Q : ℝ) / c)) := by
    intro c hc
    obtain ⟨hc1, hcQ⟩ := Finset.mem_Icc.1 hc
    have hcR : (1 : ℝ) ≤ c := by exact_mod_cast hc1
    have hcQR : (c : ℝ) ≤ Q := by exact_mod_cast hcQ
    have hcy : (c : ℝ) * y ≤ 1 / Q :=
      (mul_le_mul_of_nonneg_right hcQR hy0.le).trans hQy
    rw [intervalIntegral.integral_finsetSum fun a _ =>
      (integrable_fareyPiece Q hy0 hc1 a).intervalIntegrable]
    refine (Finset.sum_le_sum fun a _ => integral_fareyPiece_le hQ1 hy0 hc1 hcy a).trans ?_
    rw [Finset.sum_const, Int.card_Icc, sub_zero, nsmul_eq_mul]
    have hcard : ((((c : ℤ) + 1).toNat : ℕ) : ℝ) = c + 1 := by
      have : ((c : ℤ) + 1).toNat = c + 1 := by omega
      rw [this]; push_cast; ring
    rw [hcard]
    -- the logarithm
    have hL0 : 0 ≤ Real.log ((1 / Q) / (c * y)) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ (by positivity)]; linarith
    have hL : Real.log ((1 / Q) / (c * y)) ≤ Real.log 4 + Real.log ((Q : ℝ) / c) := by
      rw [← Real.log_mul (by norm_num) (by positivity)]
      apply Real.log_le_log (by positivity)
      have e : (1 / (Q : ℝ)) / (c * y) = (1 / ((Q : ℝ) * y)) / c := by field_simp
      rw [e, div_le_iff₀ (by positivity)]
      calc 1 / ((Q : ℝ) * y) ≤ 4 * Q := hinvy
        _ = 4 * ((Q : ℝ) / c) * c := by field_simp
    have hc2 : ((c : ℝ) + 1) * (2 / c) ≤ 4 := by
      rw [show ((c : ℝ) + 1) * (2 / c) = 2 + 2 / c by field_simp]
      have : 2 / (c : ℝ) ≤ 2 := by rw [div_le_iff₀ (by positivity)]; linarith
      linarith
    calc ((c : ℝ) + 1) * (2 / c * (1 + Real.log ((1 / Q) / (c * y))))
        = (((c : ℝ) + 1) * (2 / c)) * (1 + Real.log ((1 / Q) / (c * y))) := by ring
      _ ≤ 4 * (1 + Real.log ((1 / Q) / (c * y))) :=
          mul_le_mul_of_nonneg_right hc2 (by linarith)
      _ ≤ 4 * (1 + Real.log 4 + Real.log ((Q : ℝ) / c)) := by linarith
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_congr rfl (fun c _ => (mul_add (4 : ℝ) (1 + Real.log 4) _)),
    Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul,
    ← Finset.mul_sum]
  have hsum := sum_log_div_le Q
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  calc (Q : ℝ) * (4 * (1 + Real.log 4)) + 4 * ∑ c ∈ Finset.Icc 1 Q, Real.log ((Q : ℝ) / c)
      ≤ (Q : ℝ) * (4 * (1 + Real.log 4)) + 4 * Q := by linarith
    _ = 4 * (2 + Real.log 4) * Q := by ring
    _ ≤ 4 * (2 + Real.log 4) * (Real.sqrt y)⁻¹ :=
        mul_le_mul_of_nonneg_left hQle (by positivity)

end SSHecke

end VOA.Classification.COne
