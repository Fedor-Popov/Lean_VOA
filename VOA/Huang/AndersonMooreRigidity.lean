/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import Mathlib

/-!
# Rigidity of exponential polynomials under a slowly varying phase

This file proves an elementary rigidity statement about *exponential polynomials*
`x_k = Σ_i α_i u_i ^ k` (finitely many nonzero complex bases `u_i`), used in the
Anderson–Moore rationality argument.

## Main statements

* `coeff_eq_zero_of_tendsto_unimodular` (Lemma L0, indexed form) and
  `coeff_eq_zero_of_tendsto_unimodular'` (`Finset ℂ` form): if `Σ_{c ∈ s} γ(c) c^k → 0`
  with all `c` distinct and unimodular, then every `γ(c) = 0`. Proof by Cesàro averaging
  against `conj(c₀)^k = c₀⁻ᵏ`.
* `coeff_eq_zero_of_tendsto_div_pow` (Lemma C): if `(Σ_{c ∈ s} γ(c) c^k) / R^k → 0` with
  `R > 0`, then `γ(c) = 0` for every `c ∈ s` with `R ≤ ‖c‖`.
* `eq_zero_of_expPoly_eq_exp_mul` (headline): if
  `Σ_j β_j v_j^k = exp(-2πiδ/(w+k)) · Σ_i α_i u_i^k` for all `k : ℕ`, with nonzero bases,
  `Im w > 0` and `Σ_i α_i ≠ 0`, then `δ = 0`.

All statements are unconditional (no hypotheses beyond those displayed) and use only Mathlib.
-/

open Filter Topology Finset

namespace VOA.Huang.AndersonMoore

/-! ### Lemma L0: unimodular exponential polynomials tending to zero -/

/-- Cesàro means of a nontrivial unimodular geometric sequence tend to zero. -/
lemma tendsto_cesaro_geom {v : ℂ} (hv1 : ‖v‖ = 1) (hv : v ≠ 1) :
    Tendsto (fun n : ℕ => (n⁻¹ : ℝ) • ∑ k ∈ range n, v ^ k) atTop (𝓝 0) := by
  have hv' : v - 1 ≠ 0 := sub_ne_zero.mpr hv
  have hpos : 0 < ‖v - 1‖ := norm_pos_iff.mpr hv'
  have hlim : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * (2 / ‖v - 1‖)) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const (2 / ‖v - 1‖)
  refine squeeze_zero_norm (fun n => ?_) hlim
  rw [norm_smul, geom_sum_eq hv, norm_div, Real.norm_of_nonneg (inv_nonneg.mpr n.cast_nonneg)]
  gcongr
  calc ‖v ^ n - 1‖ ≤ ‖v ^ n‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_pow, hv1]; norm_num

/-- **Lemma L0** (indexed form). If `z` is injective on `s`, takes unimodular values there,
and `Σ_{i ∈ s} γ i * z i ^ k → 0`, then `γ i = 0` for every `i ∈ s`. -/
theorem coeff_eq_zero_of_tendsto_unimodular {ι : Type*} (s : Finset ι) (z γ : ι → ℂ)
    (hinj : Set.InjOn z s) (hz : ∀ i ∈ s, ‖z i‖ = 1)
    (h : Tendsto (fun k : ℕ => ∑ i ∈ s, γ i * z i ^ k) atTop (𝓝 0)) :
    ∀ i ∈ s, γ i = 0 := by
  classical
  intro i0 hi0
  have hz0 : z i0 ≠ 0 := by
    intro h0; have := hz i0 hi0; rw [h0, norm_zero] at this; exact zero_ne_one this
  -- the twisted sequence `y k = Σ γ i (z i / z i0)^k`
  have hy : Tendsto (fun k : ℕ => ∑ i ∈ s, γ i * (z i / z i0) ^ k) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hn := (tendsto_zero_iff_norm_tendsto_zero.mp h)
    refine hn.congr (fun k => ?_)
    have : ∑ i ∈ s, γ i * (z i / z i0) ^ k = (∑ i ∈ s, γ i * z i ^ k) * (z i0 ^ k)⁻¹ := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [div_pow, div_eq_mul_inv, mul_assoc]
    rw [this, norm_mul, norm_inv, norm_pow, hz i0 hi0, one_pow, inv_one, mul_one]
  have h1 := hy.cesaro_smul
  -- the Cesàro means of the twisted sequence tend to `γ i0`
  set g : ι → ℕ → ℂ := fun i n => (n⁻¹ : ℝ) • ∑ k ∈ range n, (z i / z i0) ^ k with hg
  have hgi : ∀ i ∈ s, Tendsto (g i) atTop (𝓝 (if i = i0 then 1 else 0)) := by
    intro i hi
    by_cases hii : i = i0
    · subst hii
      rw [if_pos rfl]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ne_atTop 0] with n hn
      simp only [hg, div_self hz0, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        mul_one]
      rw [Complex.real_smul]
      push_cast
      rw [inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hn)]
    · rw [if_neg hii]
      have hne : z i / z i0 ≠ 1 := by
        intro h'
        exact hii (hinj hi hi0 ((div_eq_one_iff_eq hz0).mp h'))
      have hn1 : ‖z i / z i0‖ = 1 := by rw [norm_div, hz i hi, hz i0 hi0, div_one]
      exact tendsto_cesaro_geom hn1 hne
  have h2 : Tendsto (fun n : ℕ => (n⁻¹ : ℝ) • ∑ k ∈ range n, ∑ i ∈ s, γ i * (z i / z i0) ^ k)
      atTop (𝓝 (γ i0)) := by
    have := tendsto_finsetSum s (fun i hi => (hgi i hi).const_mul (γ i))
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', if_pos hi0] at this
    refine this.congr (fun n => ?_)
    rw [Finset.sum_comm, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [hg]
    rw [mul_smul_comm, Finset.mul_sum]
  exact tendsto_nhds_unique h2 h1

/-- **Lemma L0** (`Finset ℂ` form). If `s` is a finite set of unimodular complex numbers and
`Σ_{c ∈ s} γ c * c ^ k → 0`, then `γ c = 0` for every `c ∈ s`. -/
theorem coeff_eq_zero_of_tendsto_unimodular' (s : Finset ℂ) (γ : ℂ → ℂ)
    (hs : ∀ c ∈ s, ‖c‖ = 1)
    (h : Tendsto (fun k : ℕ => ∑ c ∈ s, γ c * c ^ k) atTop (𝓝 0)) :
    ∀ c ∈ s, γ c = 0 :=
  coeff_eq_zero_of_tendsto_unimodular s id γ (Set.injOn_id _) hs h

/-! ### Lemma C: decay relative to `R^k` kills the coefficients on `‖c‖ ≥ R` -/

/-- **Lemma C.** If `(Σ_{c ∈ s} γ c * c ^ k) / R ^ k → 0` with `R > 0`, then `γ c = 0` for every
`c ∈ s` with `R ≤ ‖c‖`. -/
theorem coeff_eq_zero_of_tendsto_div_pow {s : Finset ℂ} {γ : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (h : Tendsto (fun k : ℕ => (∑ c ∈ s, γ c * c ^ k) / (R : ℂ) ^ k) atTop (𝓝 0)) :
    ∀ c ∈ s, R ≤ ‖c‖ → γ c = 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨c0, hc0, hc0R, hc0γ⟩ := hcon
  set t := s.filter (fun c => R ≤ ‖c‖ ∧ γ c ≠ 0) with ht
  have htne : t.Nonempty := ⟨c0, by simp [ht, hc0, hc0R, hc0γ]⟩
  obtain ⟨cm, hcm, hmax⟩ := t.exists_max_image (fun c => ‖c‖) htne
  rw [ht, Finset.mem_filter] at hcm
  set R' := ‖cm‖ with hR'def
  have hR' : 0 < R' := lt_of_lt_of_le hR hcm.2.1
  have hR'ne : (R' : ℂ) ≠ 0 := by exact_mod_cast hR'.ne'
  have hRne : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have hy : Tendsto (fun k : ℕ => ∑ c ∈ s, γ c * (c / (R' : ℂ)) ^ k) atTop (𝓝 0) := by
    have heq : (fun k : ℕ => ∑ c ∈ s, γ c * (c / (R' : ℂ)) ^ k) =
        fun k => ((∑ c ∈ s, γ c * c ^ k) / (R : ℂ) ^ k) * ((R : ℂ) / R') ^ k := by
      funext k
      rw [Finset.sum_div, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun c _ => ?_)
      rw [div_pow, div_pow]
      field_simp
    rw [heq]
    refine squeeze_zero_norm (a := fun k => ‖(∑ c ∈ s, γ c * c ^ k) / (R : ℂ) ^ k‖)
      (fun k => ?_) (tendsto_zero_iff_norm_tendsto_zero.mp h)
    rw [norm_mul]
    refine mul_le_of_le_one_right (norm_nonneg _) ?_
    rw [norm_pow]
    refine pow_le_one₀ (norm_nonneg _) ?_
    rw [norm_div, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hR.le,
      Real.norm_of_nonneg hR'.le]
    exact (div_le_one hR').mpr hcm.2.1
  have hrest : Tendsto (fun k : ℕ => ∑ c ∈ s.filter (fun c => ¬ ‖c‖ = R'),
      γ c * (c / (R' : ℂ)) ^ k) atTop (𝓝 0) := by
    rw [show (0 : ℂ) = ∑ c ∈ s.filter (fun c => ¬ ‖c‖ = R'), (0 : ℂ) by simp]
    refine tendsto_finsetSum _ (fun c hc => ?_)
    rw [Finset.mem_filter] at hc
    by_cases hγ : γ c = 0
    · simp [hγ]
    · have hlt : ‖c‖ < R' := by
        rcases le_or_gt R ‖c‖ with h1 | h1
        · have hct : c ∈ t := by simp [ht, hc.1, h1, hγ]
          exact lt_of_le_of_ne (hmax c hct) hc.2
        · exact lt_of_lt_of_le h1 hcm.2.1
      have hn : ‖c / (R' : ℂ)‖ < 1 := by
        rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hR'.le]
        exact (div_lt_one hR').mpr hlt
      simpa using (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hn).const_mul (γ c)
  have hs1 : Tendsto (fun k : ℕ => ∑ c ∈ s.filter (fun c => ‖c‖ = R'),
      γ c * (c / (R' : ℂ)) ^ k) atTop (𝓝 0) := by
    have := hy.sub hrest
    rw [sub_zero] at this
    refine this.congr (fun k => ?_)
    rw [← Finset.sum_filter_add_sum_filter_not s (fun c => ‖c‖ = R')]
    ring
  have hzero := coeff_eq_zero_of_tendsto_unimodular (s.filter (fun c => ‖c‖ = R'))
    (fun c => c / (R' : ℂ)) γ
    (fun a _ b _ hab => (div_left_inj' hR'ne).mp hab)
    (fun c hc => by
      rw [Finset.mem_filter] at hc
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hR'.le, hc.2, div_self hR'.ne'])
    hs1 cm (by simp [hcm.1, hR'def])
  exact hcm.2.2 hzero

/-! ### Auxiliary lemmas -/

/-- Regrouping an exponential polynomial by distinct bases. -/
lemma sum_eq_sum_group {ι : Type*} [Fintype ι] (α u : ι → ℂ) (U : Finset ℂ)
    (hU : ∀ i, u i ∈ U) (k : ℕ) :
    ∑ i, α i * u i ^ k = ∑ c ∈ U, (∑ i ∈ Finset.univ.filter (fun i => u i = c), α i) * c ^ k := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := u) (t := U) (fun i _ => hU i)]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [(Finset.mem_filter.mp hi).2]

/-- `k z^k → 0` for `‖z‖ < 1`. -/
lemma tendsto_natCast_mul_pow {z : ℂ} (hz : ‖z‖ < 1) :
    Tendsto (fun k : ℕ => (k : ℂ) * z ^ k) atTop (𝓝 0) := by
  refine squeeze_zero_norm (fun k => le_of_eq ?_)
    (tendsto_self_mul_const_pow_of_lt_one (norm_nonneg z) hz)
  rw [norm_mul, norm_pow, Complex.norm_natCast]

/-- `k (exp(L/(w+k)) - 1) → L` when `Im w > 0` and `L ≠ 0`. -/
lemma tendsto_natCast_mul_exp_div_sub_one {w : ℂ} (hw : 0 < w.im) {L : ℂ} (hL : L ≠ 0) :
    Tendsto (fun k : ℕ => (k : ℂ) * (Complex.exp (L / (w + k)) - 1)) atTop (𝓝 L) := by
  have hwk : ∀ k : ℕ, w + (k : ℂ) ≠ 0 := by
    intro k h0
    have := congrArg Complex.im h0
    simp at this
    linarith
  have hkz : Tendsto (fun k : ℕ => (k : ℂ) * (L / (w + k))) atTop (𝓝 L) := by
    have := (tendsto_natCast_div_add_atTop w).const_mul L
    rw [mul_one] at this
    refine this.congr (fun k => ?_)
    rw [add_comm (k : ℂ) w]
    ring
  have hz0 : Tendsto (fun k : ℕ => L / (w + k)) atTop (𝓝 0) := by
    have := hkz.mul (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℂ))
    rw [mul_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_ne_atTop 0] with k hk
    have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk
    field_simp
  have hzw : Tendsto (fun k : ℕ => L / (w + k)) atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hz0, Eventually.of_forall fun k => div_ne_zero hL (hwk k)⟩
  have hslope : Tendsto (fun x : ℂ => (Complex.exp x - 1) / x) (𝓝[≠] 0) (𝓝 1) := by
    have := hasDerivAt_iff_tendsto_slope.mp (Complex.hasDerivAt_exp 0)
    have e : slope Complex.exp 0 = fun x : ℂ => (Complex.exp x - 1) / x := by
      funext x; simp [slope_def_field, Complex.exp_zero]
    rw [e, Complex.exp_zero] at this
    exact this
  have := hkz.mul (hslope.comp hzw)
  rw [mul_one] at this
  refine this.congr (fun k => ?_)
  have hz := div_ne_zero hL (hwk k)
  have hwk' := hwk k
  simp only [Function.comp]
  field_simp

/-- Core of the headline argument, with an abstract phase `ε k` satisfying
`k (ε k - 1) → L ≠ 0`. -/
theorem false_of_expPoly_eq_mul {ι κ : Type*} [Fintype ι] [Fintype κ]
    (α u : ι → ℂ) (β v : κ → ℂ) (hu : ∀ i, u i ≠ 0) (hv : ∀ j, v j ≠ 0)
    (ha0 : ∑ i, α i ≠ 0) (ε : ℕ → ℂ) {L : ℂ} (hL : L ≠ 0)
    (hlim : Tendsto (fun k : ℕ => (k : ℂ) * (ε k - 1)) atTop (𝓝 L))
    (h : ∀ k : ℕ, ∑ j, β j * v j ^ k = ε k * ∑ i, α i * u i ^ k) : False := by
  classical
  set U : Finset ℂ := Finset.univ.image u ∪ Finset.univ.image v with hUdef
  have huU : ∀ i, u i ∈ U := fun i => by simp [hUdef]
  have hvU : ∀ j, v j ∈ U := fun j => by simp [hUdef]
  have hU0 : ∀ c ∈ U, c ≠ 0 := by
    intro c hc
    rw [hUdef, Finset.mem_union, Finset.mem_image, Finset.mem_image] at hc
    rcases hc with ⟨i, _, rfl⟩ | ⟨j, _, rfl⟩
    · exact hu i
    · exact hv j
  set γa : ℂ → ℂ := fun c => ∑ i ∈ Finset.univ.filter (fun i => u i = c), α i with hγa
  set γb : ℂ → ℂ := fun c => ∑ j ∈ Finset.univ.filter (fun j => v j = c), β j with hγb
  have ha : ∀ k : ℕ, ∑ i, α i * u i ^ k = ∑ c ∈ U, γa c * c ^ k :=
    sum_eq_sum_group α u U huU
  have hb : ∀ k : ℕ, ∑ j, β j * v j ^ k = ∑ c ∈ U, γb c * c ^ k :=
    sum_eq_sum_group β v U hvU
  -- a nonzero grouped coefficient of `a`
  have hex : ∃ c ∈ U, γa c ≠ 0 := by
    have h0 := ha 0
    simp only [pow_zero, mul_one] at h0
    rw [h0] at ha0
    exact Finset.exists_ne_zero_of_sum_ne_zero ha0
  obtain ⟨c0, hc0U, hc0⟩ := hex
  set ta := U.filter (fun c => γa c ≠ 0) with hta
  have htane : ta.Nonempty := ⟨c0, by simp [hta, hc0U, hc0]⟩
  obtain ⟨cm, hcm, hmax⟩ := ta.exists_max_image (fun c => ‖c‖) htane
  rw [hta, Finset.mem_filter] at hcm
  set R := ‖cm‖ with hRdef
  have hR : 0 < R := norm_pos_iff.mpr (hU0 cm hcm.1)
  have hRne : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have hmaxa : ∀ c ∈ U, γa c ≠ 0 → ‖c‖ ≤ R := fun c hc hγ =>
    hmax c (by simp [hta, hc, hγ])
  -- `ε k - 1 → 0`
  have heps : Tendsto (fun k : ℕ => ε k - 1) atTop (𝓝 0) := by
    have := hlim.mul (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℂ))
    rw [mul_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_ne_atTop 0] with k hk
    have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk
    field_simp
  -- boundedness of `a_k / R^k`
  set M : ℝ := ∑ c ∈ U, ‖γa c‖ with hM
  have hAeq : ∀ k : ℕ, (∑ c ∈ U, γa c * c ^ k) / (R : ℂ) ^ k =
      ∑ c ∈ U, γa c * (c / (R : ℂ)) ^ k := by
    intro k
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [div_pow, mul_div_assoc]
  have hAbd : ∀ k : ℕ, ‖(∑ c ∈ U, γa c * c ^ k) / (R : ℂ) ^ k‖ ≤ M := by
    intro k
    rw [hAeq k]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun c hc => ?_))
    by_cases hγ : γa c = 0
    · simp [hγ]
    · rw [norm_mul, norm_pow]
      refine mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) ?_)
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hR.le]
      exact (div_le_one hR).mpr (hmaxa c hc hγ)
  -- the difference sequence `c_k = b_k - a_k = (ε_k - 1) a_k`
  have hCeq : ∀ k : ℕ, ∑ c ∈ U, (γb c - γa c) * c ^ k =
      (ε k - 1) * ∑ c ∈ U, γa c * c ^ k := by
    intro k
    have h1 := h k
    rw [ha k, hb k] at h1
    simp only [sub_mul, Finset.sum_sub_distrib]
    rw [h1]
    ring
  have hC1 : Tendsto (fun k : ℕ => (∑ c ∈ U, (γb c - γa c) * c ^ k) / (R : ℂ) ^ k)
      atTop (𝓝 0) := by
    have hlim0 : Tendsto (fun k : ℕ => ‖ε k - 1‖ * M) atTop (𝓝 0) := by
      simpa using heps.norm.mul_const M
    refine squeeze_zero_norm (fun k => ?_) hlim0
    rw [hCeq k, mul_div_assoc, norm_mul]
    exact mul_le_mul_of_nonneg_left (hAbd k) (norm_nonneg _)
  have hCcoef := coeff_eq_zero_of_tendsto_div_pow (s := U) (γ := fun c => γb c - γa c) hR hC1
  -- hence `k c_k / R^k → 0`
  have hC2 : Tendsto (fun k : ℕ => (k : ℂ) * ((∑ c ∈ U, (γb c - γa c) * c ^ k) / (R : ℂ) ^ k))
      atTop (𝓝 0) := by
    have heq : ∀ k : ℕ, (k : ℂ) * ((∑ c ∈ U, (γb c - γa c) * c ^ k) / (R : ℂ) ^ k) =
        ∑ c ∈ U, (γb c - γa c) * ((k : ℂ) * (c / (R : ℂ)) ^ k) := by
      intro k
      rw [Finset.sum_div, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun c _ => ?_)
      rw [div_pow]
      ring
    simp only [heq]
    rw [show (0 : ℂ) = ∑ c ∈ U, (0 : ℂ) by simp]
    refine tendsto_finsetSum _ (fun c hc => ?_)
    rcases le_or_gt R ‖c‖ with h1 | h1
    · have h0 : γb c - γa c = 0 := hCcoef c hc h1
      simp [h0]
    · have hn : ‖c / (R : ℂ)‖ < 1 := by
        rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hR.le]
        exact (div_lt_one hR).mpr h1
      simpa using (tendsto_natCast_mul_pow hn).const_mul (γb c - γa c)
  -- therefore `a_k / R^k → 0`
  have hA : Tendsto (fun k : ℕ => (∑ c ∈ U, γa c * c ^ k) / (R : ℂ) ^ k) atTop (𝓝 0) := by
    have := hC2.div hlim hL
    rw [zero_div] at this
    refine this.congr' ?_
    filter_upwards [hlim.eventually_ne hL] with k hk
    simp only [Pi.div_apply]
    rw [hCeq k, div_eq_iff hk]
    ring
  exact hcm.2 (coeff_eq_zero_of_tendsto_div_pow hR hA cm hcm.1 le_rfl)

/-! ### The headline theorem -/

/-- **Rigidity.** If `Σ_j β_j v_j^k = exp(-2πiδ/(w+k)) · Σ_i α_i u_i^k` for every `k : ℕ`, with
all bases nonzero, `Im w > 0` and `Σ_i α_i ≠ 0`, then `δ = 0`. -/
theorem eq_zero_of_expPoly_eq_exp_mul {ι κ : Type*} [Fintype ι] [Fintype κ]
    (α u : ι → ℂ) (β v : κ → ℂ) (hu : ∀ i, u i ≠ 0) (hv : ∀ j, v j ≠ 0) {w δ : ℂ}
    (hw : 0 < w.im)
    (ha0 : ∑ i, α i ≠ 0)
    (h : ∀ k : ℕ, ∑ j, β j * v j ^ k =
      Complex.exp (-(2 * Real.pi * Complex.I * δ) / (w + k)) * ∑ i, α i * u i ^ k) :
    δ = 0 := by
  by_contra hδ
  have hL : -(2 * (Real.pi : ℂ) * Complex.I * δ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero, hδ]
  exact false_of_expPoly_eq_mul α u β v hu hv ha0 _ hL
    (tendsto_natCast_mul_exp_div_sub_one hw hL) h

end VOA.Huang.AndersonMoore
