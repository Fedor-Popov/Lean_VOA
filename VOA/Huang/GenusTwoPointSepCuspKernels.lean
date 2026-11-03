import VOA.Huang.GenusTwoPointSepCuspConvergence
import VOA.Huang.GenusTwoPointSepEllipticModels

/-!
# Explicit rescaled Lambert coefficients on the closed admissible radius

The positive-q coefficients are finite divisor sums. The bounds include the
boundary scale rho = z₂/z₁. No trace Ward identity is asserted here.
-/
noncomputable section
namespace VOA.Huang.GenusTwoPoint.Separate
open VOA QEquation
open scoped BigOperators

/-- The positive-q Lambert series, with q replaced by rho*q.
The coefficient at zero is zero, including when rho is zero. -/
def lambertCuspSeries (c : ℕ → ℂ) (rho : ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun n => ∑ k ∈ Finset.range n,
    if k + 1 ∣ n then rho ^ n * c k else 0

@[simp] theorem coeff_lambertCuspSeries (c : ℕ → ℂ) (rho : ℂ) (n : ℕ) :
    PowerSeries.coeff n (lambertCuspSeries c rho) =
      ∑ k ∈ Finset.range n, if k + 1 ∣ n then rho ^ n * c k else 0 := by
  simp [lambertCuspSeries]

/-- Extra q powers can only decrease the bound. -/
theorem rescaled_power_bound {rho x : ℂ} (hr : ‖rho‖ ≤ 1)
    (hx : ‖rho‖ * ‖x‖ ≤ 1) {k n : ℕ} (hkn : k ≤ n) :
    ‖rho ^ n * x ^ k‖ ≤ 1 := by
  rw [norm_mul, norm_pow, norm_pow, ← Nat.sub_add_cancel hkn, pow_add]
  have h : ‖rho‖ ^ (n - k) * (‖rho‖ * ‖x‖) ^ k ≤ 1 :=
    mul_le_one₀ (pow_le_one₀ (norm_nonneg _) hr) (by positivity)
      (pow_le_one₀ (by positivity) hx)
  simpa only [mul_pow, mul_assoc] using h

/-- A polynomial bound for both oriented elliptic numerators. -/
theorem rescaled_ellipticCoeff_bound (d : ℕ) {rho x : ℂ}
    (hr : ‖rho‖ ≤ 1) (hx : ‖rho‖ * ‖x‖ ≤ 1)
    (hxi : ‖rho‖ * ‖x⁻¹‖ ≤ 1) {k n : ℕ} (hkn : k + 1 ≤ n) :
    ‖rho ^ n * ellipticCoeff d x k‖ ≤ 2 * (n : ℝ) ^ d := by
  have h₁ := rescaled_power_bound hr hx hkn
  have h₂ := rescaled_power_bound hr hxi hkn
  have he : rho ^ n * ellipticCoeff d x k =
      (k + 1 : ℂ) ^ d *
        (rho ^ n * x ^ (k + 1) - (-1 : ℂ) ^ d * (rho ^ n * (x⁻¹) ^ (k + 1))) := by
    unfold ellipticCoeff
    ring
  rw [he, norm_mul, norm_pow,
    show ‖(k + 1 : ℂ)‖ = (k + 1 : ℝ) by
      simpa only [Nat.cast_add, Nat.cast_one] using Complex.norm_natCast (k + 1)]
  have hb : ‖rho ^ n * x ^ (k + 1) -
      (-1 : ℂ) ^ d * (rho ^ n * (x⁻¹) ^ (k + 1))‖ ≤ 2 := by
    have h := norm_sub_le (rho ^ n * x ^ (k + 1))
      ((-1 : ℂ) ^ d * (rho ^ n * (x⁻¹) ^ (k + 1)))
    simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul] at h h₁ h₂ ⊢
    linarith
  calc
    _ ≤ (k + 1 : ℝ) ^ d * 2 := mul_le_mul_of_nonneg_left hb (by positivity)
    _ ≤ (n : ℝ) ^ d * 2 := by
      gcongr
      exact_mod_cast hkn
    _ = _ := by ring

/-- The full divisor sum has only polynomial growth even at the boundary scale. -/
theorem coeff_ellipticCusp_bound (d : ℕ) {rho x : ℂ}
    (hr : ‖rho‖ ≤ 1) (hx : ‖rho‖ * ‖x‖ ≤ 1)
    (hxi : ‖rho‖ * ‖x⁻¹‖ ≤ 1) (n : ℕ) :
    ‖PowerSeries.coeff n (lambertCuspSeries (ellipticCoeff d x) rho)‖ ≤
      2 * (n : ℝ) ^ (d + 1) := by
  rw [coeff_lambertCuspSeries]
  calc
    _ ≤ ∑ k ∈ Finset.range n,
        ‖if k + 1 ∣ n then rho ^ n * ellipticCoeff d x k else 0‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ Finset.range n, 2 * (n : ℝ) ^ d := by
      apply Finset.sum_le_sum
      intro k hk
      split_ifs
      · exact rescaled_ellipticCoeff_bound d hr hx hxi (by
          have := Finset.mem_range.mp hk; omega)
      · simp only [norm_zero]; positivity
    _ = _ := by simp [pow_succ]; ring

theorem ellipticCusp_mem_subexp (d : ℕ) {rho x : ℂ}
    (hr : ‖rho‖ ≤ 1) (hx : ‖rho‖ * ‖x‖ ≤ 1)
    (hxi : ‖rho‖ * ‖x⁻¹‖ ≤ 1) :
    lambertCuspSeries (ellipticCoeff d x) rho ∈ SubexpPS :=
  Subexponential.of_le (coeff_ellipticCusp_bound d hr hx hxi)
    ((subexponential_pow (d + 1)).const_mul (by norm_num))

/-- Specialization to the natural two-point annulus, including its boundary
rescaling. The independent unit-disc condition follows from the spatial order. -/
theorem annulus_kernel_conditions {z₁ z₂ rho : ℂ} (hz₂ : z₂ ≠ 0)
    (hz : ‖z₂‖ < ‖z₁‖) (hr : ‖rho‖ ≤ ‖z₂ / z₁‖) :
    ‖rho‖ ≤ 1 ∧ ‖rho‖ * ‖z₂ / z₁‖ ≤ 1 ∧
      ‖rho‖ * ‖(z₂ / z₁)⁻¹‖ ≤ 1 := by
  have hz₁ : z₁ ≠ 0 := norm_pos_iff.mp ((norm_nonneg _).trans_lt hz)
  have hx₀ : 0 < ‖z₂ / z₁‖ := norm_pos_iff.mpr (div_ne_zero hz₂ hz₁)
  have hx₁ : ‖z₂ / z₁‖ < 1 := by
    rw [norm_div, div_lt_one (norm_pos_iff.mpr hz₁)]
    exact hz
  refine ⟨hr.trans hx₁.le, ?_, ?_⟩
  · exact mul_le_one₀ (hr.trans hx₁.le) (norm_nonneg _) hx₁.le
  · rw [norm_inv]
    calc
      _ ≤ ‖z₂ / z₁‖ * ‖z₂ / z₁‖⁻¹ := mul_le_mul_of_nonneg_right hr (by positivity)
      _ = 1 := mul_inv_cancel₀ hx₀.ne'

theorem ellipticCusp_mem_subexp_annulus (d : ℕ) {z₁ z₂ rho : ℂ}
    (hz₂ : z₂ ≠ 0) (hz : ‖z₂‖ < ‖z₁‖) (hr : ‖rho‖ ≤ ‖z₂ / z₁‖) :
    lambertCuspSeries (ellipticCoeff d (z₂ / z₁)) rho ∈ SubexpPS := by
  obtain ⟨h₁, h₂, h₃⟩ := annulus_kernel_conditions hz₂ hz hr
  exact ellipticCusp_mem_subexp d h₁ h₂ h₃

/-- The reverse orientation satisfies the same bound. -/
theorem ellipticCusp_inv_mem_subexp_annulus (d : ℕ) {z₁ z₂ rho : ℂ}
    (hz₂ : z₂ ≠ 0) (hz : ‖z₂‖ < ‖z₁‖) (hr : ‖rho‖ ≤ ‖z₂ / z₁‖) :
    lambertCuspSeries (ellipticCoeff d (z₂ / z₁)⁻¹) rho ∈ SubexpPS := by
  obtain ⟨h₁, h₂, h₃⟩ := annulus_kernel_conditions hz₂ hz hr
  exact ellipticCusp_mem_subexp d h₁ h₃ (by simpa using h₂)

/-- Coefficientwise collection of the geometric denominators. Every coefficient
has finite support in the mode index; this is an identity of formal kernels. -/
theorem coeff_lambertCuspSeries_geometric (c : ℕ → ℂ) (rho : ℂ) (n : ℕ) :
    PowerSeries.coeff n (lambertCuspSeries c rho) =
      ∑ᶠ k : ℕ, PowerSeries.coeff n (PowerSeries.rescale rho
        (PowerSeries.C (c k) * PowerSeries.X ^ (k + 1) * geometricDenominator (k + 1))) := by
  have he (k : ℕ) : PowerSeries.coeff n (PowerSeries.rescale rho
      (PowerSeries.C (c k) * PowerSeries.X ^ (k + 1) * geometricDenominator (k + 1))) =
      if k < n then (if k + 1 ∣ n then rho ^ n * c k else 0) else 0 := by
    rw [PowerSeries.coeff_rescale, mul_assoc, PowerSeries.coeff_C_mul,
      PowerSeries.coeff_X_pow_mul']
    by_cases hk : k < n
    · have hkn : k + 1 ≤ n := by omega
      rw [if_pos hkn, coeff_geometricDenominator (by omega), if_pos hk]
      have hd : k + 1 ∣ n - (k + 1) ↔ k + 1 ∣ n :=
        Nat.dvd_sub_iff_left hkn (dvd_refl _)
      simp only [hd]
      split_ifs <;> ring
    · simp [hk, show ¬k + 1 ≤ n by omega]
  rw [coeff_lambertCuspSeries]
  symm
  calc
    _ = ∑ k ∈ Finset.range n, PowerSeries.coeff n (PowerSeries.rescale rho
        (PowerSeries.C (c k) * PowerSeries.X ^ (k + 1) * geometricDenominator (k + 1))) := by
      apply finsum_eq_sum_of_support_subset
      intro k hk
      simp only [Function.mem_support, Finset.mem_coe, Finset.mem_range] at *
      by_contra hn
      exact hk (by rw [he, if_neg hn])
    _ = _ := Finset.sum_congr rfl fun k hk => by rw [he, if_pos (Finset.mem_range.mp hk)]

/-- Rescaling preserves the coefficient algebra on every closed subdisc. -/
theorem rescale_mem_subexp {f : PowerSeries ℂ} (hf : f ∈ SubexpPS)
    {rho : ℂ} (hr : ‖rho‖ ≤ 1) : PowerSeries.rescale rho f ∈ SubexpPS := by
  apply Subexponential.of_le _ hf
  intro n
  rw [PowerSeries.coeff_rescale, norm_mul, norm_pow]
  exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hr)

/-- The actual Eisenstein q-expansion in the rescaled variable. -/
def eisensteinCuspSeries (j : ℕ) (rho : ℂ) : PowerSeries ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I) ^ (2 * j) •
    PowerSeries.rescale rho (PowerSeries.mk (zhuG j))

theorem eisensteinCusp_mem_subexp (j : ℕ) {rho : ℂ} (hr : ‖rho‖ ≤ 1) :
    eisensteinCuspSeries j rho ∈ SubexpPS :=
  SubexpPS.smul_mem (rescale_mem_subexp (mk_zhuG_mem_subexpPS j) hr) _

/-- Fourier model for wp_(d+1). The additive difference t is needed only for
wp₁. The constant sum is used below only for |x|<1, where it converges. -/
def wpCuspSeries (d : ℕ) (x t rho : ℂ) : PowerSeries ℂ :=
  ((-1 : ℂ) ^ (d + 1) * (2 * (Real.pi : ℂ) * Complex.I) ^ (d + 1) /
    (d.factorial : ℂ)) •
      (PowerSeries.C (∑' k : ℕ, (k + 1 : ℂ) ^ d * x ^ (k + 1)) +
        lambertCuspSeries (ellipticCoeff d x) rho) +
    if d = 0 then t • eisensteinCuspSeries 1 rho - PowerSeries.C ((Real.pi : ℂ) * Complex.I)
    else if d = 1 then -eisensteinCuspSeries 1 rho else 0

theorem wpCusp_mem_subexp (d : ℕ) {rho x : ℂ} (t : ℂ)
    (hr : ‖rho‖ ≤ 1) (hx : ‖rho‖ * ‖x‖ ≤ 1)
    (hxi : ‖rho‖ * ‖x⁻¹‖ ≤ 1) : wpCuspSeries d x t rho ∈ SubexpPS := by
  unfold wpCuspSeries
  apply SubexpPS.add_mem
  · exact SubexpPS.smul_mem (SubexpPS.add_mem (SubexpPS.algebraMap_mem _)
      (ellipticCusp_mem_subexp d hr hx hxi)) _
  · split_ifs
    · exact SubexpPS.sub_mem (SubexpPS.smul_mem (eisensteinCusp_mem_subexp 1 hr) _)
        (SubexpPS.algebraMap_mem _)
    · exact SubexpPS.neg_mem (eisensteinCusp_mem_subexp 1 hr)
    · exact SubexpPS.zero_mem

/-- A concrete family of both oriented minus-two kernels. The right orientation
uses the parity of wp_(m+2), rather than a divergent constant series at x⁻¹. -/
def cuspWardKernels {z₁ z₂ rho : ℂ} (hz₂ : z₂ ≠ 0)
    (hz : ‖z₂‖ < ‖z₁‖) (hr : ‖rho‖ ≤ ‖z₂ / z₁‖) : Kernels ↥SubexpPS where
  G k := ⟨eisensteinCuspSeries (k + 2) rho,
    eisensteinCusp_mem_subexp _ (annulus_kernel_conditions hz₂ hz hr).1⟩
  Pleft m := ⟨wpCuspSeries (m + 1) (z₂ / z₁) 0 rho,
    wpCusp_mem_subexp _ _ (annulus_kernel_conditions hz₂ hz hr).1
      (annulus_kernel_conditions hz₂ hz hr).2.1
      (annulus_kernel_conditions hz₂ hz hr).2.2⟩
  Pright m := (-1) ^ (m + 2) *
    ⟨wpCuspSeries (m + 1) (z₂ / z₁) 0 rho,
      wpCusp_mem_subexp _ _ (annulus_kernel_conditions hz₂ hz hr).1
        (annulus_kernel_conditions hz₂ hz hr).2.1
        (annulus_kernel_conditions hz₂ hz hr).2.2⟩

end VOA.Huang.GenusTwoPoint.Separate
