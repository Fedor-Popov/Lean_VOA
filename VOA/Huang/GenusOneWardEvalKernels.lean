import VOA.Huang.GenusOneWardSwap
import VOA.Huang.GenusTwoPointSepCuspKernels

/-!
# Spatial evaluation of `ℂ⟦u⟧⟦t⟧` with `q` left formal

The coefficient of `u^n t^k` multiplies `q^n t₀^{k−n}`. For a series whose
rows are absolutely convergent at `t₀`, `evF t₀ s f` is the `q`-series whose
`n`-th coefficient is `s^n Σ_k c2 f n k t₀^k`; with `s = ρ/t₀` this is the
evaluation at `t = t₀` followed by the rescaling `q ↦ ρ q`. It is additive and
multiplicative on convergent series (absolute Cauchy products). The kernels
`eis` and `piK` evaluate to the library's cusp kernels.
-/
noncomputable section
namespace VOA.Huang.GenusOneWard
open VOA PowerSeries
open VOA.Huang.GenusTwoPoint.Separate
open VOA.Huang.GenusTwoPoint.QEquation (ellipticCoeff)
open scoped BigOperators

/-- Every row is absolutely convergent at `t₀`. -/
def Conv (t₀ : ℂ) (f : R2) : Prop := ∀ n, SpatialSummable t₀ (PowerSeries.coeff n f)

/-- Spatial evaluation with rescaled formal `q`. -/
def evF (t₀ s : ℂ) (f : R2) : PowerSeries ℂ :=
  PowerSeries.mk fun n => s ^ n * ∑' k, c2 f n k * t₀ ^ k

theorem coeff_evF (t₀ s : ℂ) (f : R2) (n : ℕ) :
    PowerSeries.coeff n (evF t₀ s f) = s ^ n * ∑' k, c2 f n k * t₀ ^ k := by
  simp [evF]

theorem rowEval_eq {t₀ : ℂ} {f : R2} (hf : Conv t₀ f) (n : ℕ) :
    ∑' k, c2 f n k * t₀ ^ k = spatialEval t₀ ⟨PowerSeries.coeff n f, hf n⟩ := rfl

theorem Conv.add {t₀ : ℂ} {f g : R2} (hf : Conv t₀ f) (hg : Conv t₀ g) : Conv t₀ (f + g) :=
  fun n => by simpa only [map_add] using (hf n).add (hg n)

theorem Conv.smul {t₀ : ℂ} {f : R2} (hf : Conv t₀ f) (a : ℂ) : Conv t₀ (a • f) := fun n => by
  have h := (spatialConvergent t₀).smul_mem (show PowerSeries.coeff n f ∈ spatialConvergent t₀
    from hf n) a
  simpa only [map_smul] using h

theorem Conv.neg {t₀ : ℂ} {f : R2} (hf : Conv t₀ f) : Conv t₀ (-f) := by
  simpa only [neg_one_smul] using hf.smul (-1)

theorem Conv.sub {t₀ : ℂ} {f g : R2} (hf : Conv t₀ f) (hg : Conv t₀ g) : Conv t₀ (f - g) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem Conv.mul {t₀ : ℂ} {f g : R2} (hf : Conv t₀ f) (hg : Conv t₀ g) : Conv t₀ (f * g) :=
  fun n => by
    rw [PowerSeries.coeff_mul]
    exact (spatialConvergent t₀).sum_mem fun p _ =>
      (spatialConvergent t₀).mul_mem (show PowerSeries.coeff p.1 f ∈ spatialConvergent t₀
        from hf p.1) (show PowerSeries.coeff p.2 g ∈ spatialConvergent t₀ from hg p.2)

theorem conv_zero (t₀ : ℂ) : Conv t₀ 0 := fun n => by
  simpa using spatialSummable_C t₀ 0

theorem Conv.sum {t₀ : ℂ} {ι : Type*} (s : Finset ι) {f : ι → R2}
    (h : ∀ i ∈ s, Conv t₀ (f i)) : Conv t₀ (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using conv_zero t₀
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem evF_add {t₀ s : ℂ} {f g : R2} (hf : Conv t₀ f) (hg : Conv t₀ g) :
    evF t₀ s (f + g) = evF t₀ s f + evF t₀ s g := by
  ext n
  rw [map_add, coeff_evF, coeff_evF, coeff_evF, rowEval_eq (hf.add hg), rowEval_eq hf,
    rowEval_eq hg, ← mul_add, ← map_add]
  rfl

theorem evF_smul {t₀ s : ℂ} (a : ℂ) (f : R2) : evF t₀ s (a • f) = a • evF t₀ s f := by
  ext n
  simp only [coeff_evF, c2_smul, PowerSeries.coeff_smul, smul_eq_mul, mul_assoc, tsum_mul_left]
  ring

theorem evF_zero {t₀ s : ℂ} : evF t₀ s 0 = 0 := by
  ext n; simp [coeff_evF]

theorem evF_neg {t₀ s : ℂ} (f : R2) : evF t₀ s (-f) = -evF t₀ s f := by
  rw [← neg_one_smul ℂ f, evF_smul, neg_one_smul]

theorem evF_sub {t₀ s : ℂ} {f g : R2} (hf : Conv t₀ f) (hg : Conv t₀ g) :
    evF t₀ s (f - g) = evF t₀ s f - evF t₀ s g := by
  rw [sub_eq_add_neg, evF_add hf hg.neg, evF_neg, ← sub_eq_add_neg]

theorem evF_sum {t₀ s : ℂ} {ι : Type*} (S : Finset ι) {f : ι → R2}
    (h : ∀ i ∈ S, Conv t₀ (f i)) : evF t₀ s (∑ i ∈ S, f i) = ∑ i ∈ S, evF t₀ s (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [evF_zero]
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      evF_add (h a (Finset.mem_insert_self a S))
        (Conv.sum S fun i hi => h i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => h i (Finset.mem_insert_of_mem hi)]

theorem evF_mul {t₀ s : ℂ} {f g : R2} (hf : Conv t₀ f) (hg : Conv t₀ g) :
    evF t₀ s (f * g) = evF t₀ s f * evF t₀ s g := by
  ext n
  have hrow : (⟨PowerSeries.coeff n (f * g), (hf.mul hg) n⟩ : spatialConvergent t₀) =
      ∑ p ∈ Finset.antidiagonal n, (⟨PowerSeries.coeff p.1 f, hf p.1⟩ : spatialConvergent t₀) *
        ⟨PowerSeries.coeff p.2 g, hg p.2⟩ := by
    apply Subtype.ext
    change PowerSeries.coeff n (f * g) = _
    rw [PowerSeries.coeff_mul]
    push_cast
    rfl
  rw [coeff_evF, rowEval_eq (hf.mul hg), hrow, map_sum, Finset.mul_sum]
  conv_rhs => rw [PowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro p hp
  rw [map_mul, coeff_evF, coeff_evF, rowEval_eq hf, rowEval_eq hg,
    ← Finset.mem_antidiagonal.mp hp, pow_add]
  ring

/-! ## Kernels -/

theorem conv_algebraMap (t₀ a : ℂ) : Conv t₀ (algebraMap ℂ R2 a) := by
  intro n
  have h : PowerSeries.coeff n (algebraMap ℂ R2 a) = PowerSeries.C (if n = 0 then a else 0) := by
    ext k
    rw [show PowerSeries.coeff k (PowerSeries.coeff n (algebraMap ℂ R2 a)) =
      c2 (algebraMap ℂ R2 a) n k from rfl, c2_algebraMap, PowerSeries.coeff_C]
    split_ifs <;> simp_all
  rw [h]
  exact spatialSummable_C t₀ _

theorem evF_algebraMap (t₀ s a : ℂ) : evF t₀ s (algebraMap ℂ R2 a) = PowerSeries.C a := by
  ext n
  rw [coeff_evF, PowerSeries.coeff_C]
  simp only [c2_algebraMap]
  by_cases hn : n = 0
  · subst hn
    rw [if_pos rfl, tsum_eq_single 0 (fun k hk => by simp [hk])]
    simp
  · simp [hn]

/-- A row with finitely many nonzero coefficients is convergent everywhere. -/
theorem spatialSummable_of_finite (t₀ : ℂ) (F : PowerSeries ℂ) (B : ℕ)
    (h : ∀ k, B ≤ k → PowerSeries.coeff k F = 0) : SpatialSummable t₀ F := by
  unfold SpatialSummable
  apply summable_of_ne_finset_zero (s := Finset.range B)
  intro k hk
  rw [Finset.mem_range, not_lt] at hk
  rw [h k hk, zero_mul, norm_zero]

theorem conv_eis (t₀ : ℂ) (j : ℕ) : Conv t₀ (eis j) := by
  intro n
  apply spatialSummable_of_finite t₀ _ (n + 1)
  intro k hk
  show c2 (eis j) n k = 0
  simp only [eis, c2_mk2]
  rw [if_neg (by omega)]

theorem evF_eis {t₀ : ℂ} (ht : t₀ ≠ 0) (rho : ℂ) (j : ℕ) :
    evF t₀ (rho * t₀⁻¹) (eis j) = PowerSeries.rescale rho (PowerSeries.mk (zhuG j)) := by
  ext n
  rw [coeff_evF, PowerSeries.coeff_rescale, PowerSeries.coeff_mk,
    tsum_eq_single n (fun k hk => by simp only [eis, c2_mk2]; rw [if_neg (Ne.symm hk), zero_mul])]
  simp only [eis, c2_mk2, if_true]
  rw [mul_pow, inv_pow]
  field_simp

theorem conv_piK {t₀ : ℂ} (ht : ‖t₀‖ < 1) (m : ℕ) : Conv t₀ (piK m) := by
  intro n
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    unfold SpatialSummable
    have hs := (summable_pow_mul_geometric_of_norm_lt_one m (show ‖(‖t₀‖ : ℝ)‖ < 1 by
      rwa [Real.norm_of_nonneg (norm_nonneg _)])).mul_left (1 / (m.factorial : ℝ))
    refine hs.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_)
    show ‖c2 (piK m) 0 k * t₀ ^ k‖ ≤ _
    rw [c2_piK]
    by_cases hk : 0 < k
    · rw [if_pos ⟨hk, dvd_zero _⟩, if_neg (by omega), sub_zero, norm_mul, norm_div, norm_pow,
        norm_pow, Nat.sub_zero, Complex.norm_natCast, Complex.norm_natCast]
      apply le_of_eq
      ring
    · rw [if_neg (by omega), if_neg (by omega), sub_zero, zero_mul, norm_zero]
      positivity
  · apply spatialSummable_of_finite t₀ _ (2 * n + 1)
    intro k hk
    show c2 (piK m) n k = 0
    rw [c2_piK, if_neg (fun h => by
      obtain ⟨h1, h2⟩ := h
      have := Nat.le_of_dvd hpos h2
      omega), if_neg (by omega), sub_zero]

theorem dvd_sub_one_sub_iff {n i : ℕ} (hi : i < n) : (i + 1 ∣ n - 1 - i) ↔ (i + 1 ∣ n) := by
  have h : n = (n - 1 - i) + (i + 1) := by omega
  conv_rhs => rw [h]
  exact Nat.dvd_add_self_right.symm

/-- The positive rows of `piK` are the rescaled Lambert coefficients. -/
theorem row_piK_pos {t₀ : ℂ} (ht0 : t₀ ≠ 0) (rho : ℂ) (m : ℕ) {n : ℕ} (hn : 0 < n) :
    (rho * t₀⁻¹) ^ n * ∑' k, c2 (piK m) n k * t₀ ^ k =
      (1 / (m.factorial : ℂ)) * ∑ i ∈ Finset.range n,
        (if i + 1 ∣ n then rho ^ n * ellipticCoeff m t₀ i else 0) := by
  rw [tsum_eq_sum (s := Finset.range (2 * n + 1)) (fun k hk => by
    rw [Finset.mem_range, not_lt] at hk
    rw [c2_piK, if_neg (fun h => by
      obtain ⟨h1, h2⟩ := h
      have := Nat.le_of_dvd hn h2
      omega), if_neg (by omega), sub_zero, zero_mul])]
  simp only [c2_piK, sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul]
  have hA : ∑ k ∈ Finset.range (2 * n + 1),
      (if n < k ∧ k - n ∣ n then ((k - n : ℕ) : ℂ) ^ m / (m.factorial : ℂ) * t₀ ^ k else 0) =
      ∑ i ∈ Finset.range n, (if i + 1 ∣ n then ((i + 1 : ℕ) : ℂ) ^ m / (m.factorial : ℂ) *
        t₀ ^ (n + 1 + i) else 0) := by
    rw [show 2 * n + 1 = (n + 1) + n by ring, Finset.sum_range_add]
    rw [Finset.sum_eq_zero (fun k hk => by
      rw [Finset.mem_range] at hk; rw [if_neg (by omega)]), zero_add]
    apply Finset.sum_congr rfl
    intro i hi
    rw [show n + 1 + i - n = i + 1 by omega]
    by_cases hd : i + 1 ∣ n
    · rw [if_pos ⟨by omega, hd⟩, if_pos hd]
    · rw [if_neg (fun h => hd h.2), if_neg hd]
  have hB : ∑ k ∈ Finset.range (2 * n + 1),
      (if k < n ∧ n - k ∣ k then (-((n - k : ℕ) : ℂ)) ^ m / (m.factorial : ℂ) * t₀ ^ k else 0) =
      ∑ i ∈ Finset.range n, (if i + 1 ∣ n then (-((i + 1 : ℕ) : ℂ)) ^ m / (m.factorial : ℂ) *
        t₀ ^ (n - 1 - i) else 0) := by
    rw [show 2 * n + 1 = n + (n + 1) by ring, Finset.sum_range_add]
    rw [Finset.sum_eq_zero (s := Finset.range (n + 1)) (fun k hk => by rw [if_neg (by omega)]),
      add_zero, ← Finset.sum_range_reflect]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    rw [show n - (n - 1 - i) = i + 1 by omega]
    by_cases hd : i + 1 ∣ n
    · rw [if_pos ⟨by omega, (dvd_sub_one_sub_iff hi).mpr hd⟩, if_pos hd]
    · rw [if_neg (fun h => hd ((dvd_sub_one_sub_iff hi).mp h.2)), if_neg hd]
  rw [hA, hB, ← Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  by_cases hd : i + 1 ∣ n
  · rw [if_pos hd, if_pos hd, if_pos hd, ellipticCoeff]
    have hp1 : t₀ ^ (n + 1 + i) = t₀ ^ n * t₀ ^ (i + 1) := by rw [← pow_add]; ring_nf
    have hp2 : t₀ ^ (n - 1 - i) * t₀ ^ (i + 1) = t₀ ^ n := by rw [← pow_add]; congr 1; omega
    have hinv : t₀ ^ (n - 1 - i) = t₀ ^ n * t₀⁻¹ ^ (i + 1) := by
      rw [← hp2, inv_pow, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ ht0), mul_one]
    have hn1 : t₀ ^ n * t₀⁻¹ ^ n = 1 := by rw [← mul_pow, mul_inv_cancel₀ ht0, one_pow]
    rw [hp1, hinv, neg_pow]
    push_cast
    field_simp
    linear_combination (rho ^ n * t₀ * t₀ ^ i * ((m.factorial : ℂ))⁻¹ -
      rho ^ n * t₀⁻¹ * t₀⁻¹ ^ i * ((m.factorial : ℂ))⁻¹ * (-1) ^ m) * hn1
  · rw [if_neg hd, if_neg hd, if_neg hd]
    ring

theorem evF_piK {t₀ : ℂ} (ht0 : t₀ ≠ 0) (ht : ‖t₀‖ < 1) (rho : ℂ) (m : ℕ) :
    evF t₀ (rho * t₀⁻¹) (piK m) = (1 / (m.factorial : ℂ)) •
      (PowerSeries.C (∑' k : ℕ, (k + 1 : ℂ) ^ m * t₀ ^ (k + 1)) +
        lambertCuspSeries (ellipticCoeff m t₀) rho) := by
  ext n
  rw [coeff_evF, PowerSeries.coeff_smul, map_add, PowerSeries.coeff_C,
    coeff_lambertCuspSeries, smul_eq_mul]
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    simp only [pow_zero, one_mul, if_true, Finset.range_zero, Finset.sum_empty, add_zero]
    have hsum : Summable fun k => c2 (piK m) 0 k * t₀ ^ k := (conv_piK ht m 0).of_norm
    rw [hsum.tsum_eq_zero_add, ← tsum_mul_left]
    rw [c2_piK, if_neg (by omega), if_neg (by omega), sub_zero, zero_mul, zero_add]
    apply tsum_congr
    intro k
    rw [c2_piK, if_pos ⟨by omega, dvd_zero _⟩, if_neg (by omega), sub_zero, Nat.sub_zero]
    push_cast
    ring
  · rw [if_neg (by omega), zero_add, row_piK_pos ht0 rho m hpos]

end VOA.Huang.GenusOneWard
