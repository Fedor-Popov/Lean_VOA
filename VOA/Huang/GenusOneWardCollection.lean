import VOA.Huang.GenusOneWardGeneral

/-!
# The two collected minus-two Ward identities on the actual raw cusp trace

The formal identities `leftLHS_evZero` and `rightLHS_evZero` are evaluated at
`t = z₂/z₁` with `q` formal and rescaled by `ρ`. Huang's mode factors
`huangModeScale m = (2πi)^{−(m+1)}` combine with the powers of `2πi` in the cusp
kernels to a single overall factor `2πi`, so the evaluated identities are
exactly the first two clauses of `RawCuspCoordinateCollection`.
-/
noncomputable section
namespace VOA.Huang.GenusOneWard
open VOA Module
open VOA.Huang.GenusTwoPoint.Separate
open VOA.Huang.GenusTwoPoint (moduleWeightExp moduleWeightExp_of_weight moduleWeightExp_add
  moduleWeightExp_zero logTwoPiI)
open VOA.Huang.GenusTwoPoint.QEquation (TailBound exists_tailBound ellipticCoeff Kernels)
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  {P₁ P₂ N Q : LWModule W}

/-! ## Powers of `2πi` -/

theorem huangModeScale_mul_pow (m : ℕ) :
    huangModeScale (m : ℤ) * (2 * (Real.pi : ℂ) * Complex.I) ^ (m + 2) =
      2 * (Real.pi : ℂ) * Complex.I := by
  rw [← exp_logTwoPiI, huangModeScale, ← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem huangModeScale_neg_two : huangModeScale (-2) = 2 * (Real.pi : ℂ) * Complex.I := by
  rw [huangModeScale, ← exp_logTwoPiI]
  congr 1
  push_cast
  ring

/-- The Eisenstein kernel with its mode factor. -/
theorem eisCusp_scale {t₀ : ℂ} (ht0 : t₀ ≠ 0) (rho : ℂ) (k : ℕ) :
    huangModeScale ((2 * k + 2 : ℕ) : ℤ) • eisensteinCuspSeries (k + 2) rho =
      (2 * (Real.pi : ℂ) * Complex.I) • evF t₀ (rho * t₀⁻¹) (eis (k + 2)) := by
  rw [evF_eis ht0, eisensteinCuspSeries, smul_smul]
  congr 1
  rw [show 2 * (k + 2) = (2 * k + 2) + 2 by ring, huangModeScale_mul_pow]

/-- The Weierstrass kernel with its mode factor and sign. -/
theorem wpCusp_scale {t₀ : ℂ} (ht0 : t₀ ≠ 0) (ht : ‖t₀‖ < 1) (rho : ℂ) (m : ℕ) :
    huangModeScale (m : ℤ) •
        ((-1 : PowerSeries ℂ) ^ m * ((m : PowerSeries ℂ) + 1) * wpCuspSeries (m + 1) t₀ 0 rho) =
      (2 * (Real.pi : ℂ) * Complex.I) • evF t₀ (rho * t₀⁻¹)
        (((m + 1 : ℕ) : ℂ) • piK (m + 1) - if m = 0 then eis 1 else 0) := by
  have hc : Conv t₀ (((m + 1 : ℕ) : ℂ) • piK (m + 1)) := (conv_piK ht _).smul _
  have hd : Conv t₀ (if m = 0 then eis 1 else 0) := by
    split_ifs
    · exact conv_eis t₀ 1
    · exact conv_zero t₀
  rw [evF_sub hc hd, evF_smul, evF_piK ht0 ht, apply_ite (evF t₀ (rho * t₀⁻¹)), evF_eis ht0,
    evF_zero]
  have hscale := huangModeScale_mul_pow m
  have hsign : ((-1 : ℂ) ^ m) * (-1 : ℂ) ^ (m + 1 + 1) = 1 := by
    rw [← pow_add, show m + (m + 1 + 1) = 2 * (m + 1) by ring, pow_mul]; norm_num
  have hm1 : ((m : PowerSeries ℂ) + 1) = PowerSeries.C ((m : ℂ) + 1) := by simp
  have hneg : ((-1 : PowerSeries ℂ) ^ m) = PowerSeries.C ((-1 : ℂ) ^ m) := by simp
  set E := 2 * (Real.pi : ℂ) * Complex.I with hE
  set A := PowerSeries.C (∑' k : ℕ, (k + 1 : ℂ) ^ (m + 1) * t₀ ^ (k + 1)) +
    lambertCuspSeries (ellipticCoeff (m + 1) t₀) rho with hA
  have hwp : wpCuspSeries (m + 1) t₀ 0 rho =
      ((-1 : ℂ) ^ (m + 1 + 1) * E ^ (m + 1 + 1) / ((m + 1).factorial : ℂ)) • A +
        (if m = 0 then -eisensteinCuspSeries 1 rho else 0) := by
    rw [wpCuspSeries, if_neg (by omega)]
    by_cases h0 : m = 0
    · rw [if_pos (by omega), if_pos h0]
    · rw [if_neg (by omega), if_neg h0]
  rw [hwp, hm1, hneg, ← map_mul]
  by_cases h0 : m = 0
  · subst h0
    simp only [if_true, eisensteinCuspSeries]
    simp only [pow_zero, Nat.cast_zero, zero_add, Nat.factorial_one, Nat.cast_one,
      map_one, one_mul] at hscale ⊢
    ext n
    simp only [PowerSeries.coeff_smul, map_add, map_neg, map_sub, smul_eq_mul]
    set a := PowerSeries.coeff n A
    set r := PowerSeries.coeff n (PowerSeries.rescale rho (PowerSeries.mk (zhuG 1)))
    linear_combination (a - r) * hscale
  · simp only [if_neg h0, add_zero, sub_zero]
    ext n
    simp only [PowerSeries.coeff_smul, PowerSeries.coeff_C_mul, smul_eq_mul]
    set a := PowerSeries.coeff n A
    rw [div_eq_mul_inv, div_eq_mul_inv, one_mul]
    push_cast
    linear_combination (((m : ℂ) + 1) * a * ((((m + 1).factorial : ℕ) : ℂ))⁻¹ *
        ((-1) ^ m * (-1) ^ (m + 1 + 1))) * hscale +
      (((m : ℂ) + 1) * a * ((((m + 1).factorial : ℕ) : ℂ))⁻¹ * E) * hsign

/-! ## Evaluation of the formal expressions -/

theorem conv_kernel_ite (t₀ : ℂ) (m : ℕ) : Conv t₀ (if m = 0 then eis 1 else 0) := by
  split_ifs
  · exact conv_eis t₀ 1
  · exact conv_zero t₀

section Expand
variable (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
  (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)

theorem evF_leftLHS {t₀ s : ℂ} (ht : ‖t₀‖ < 1) (hΦ : ∀ v w, Conv t₀ (Phi Y₁ Y₂ v w))
    (b : V) (x : P₁.carrier) (y : P₂.carrier) (K : ℕ) :
    evF t₀ s (leftLHS Y₁ Y₂ b x y K) =
      evF t₀ s (Phi Y₁ Y₂ (GenusOne.SquareModule.sqMode P₁.isMod (-2) b x) y) +
      ∑ m ∈ Finset.range K, ((2 * m + 3 : ℕ) : ℂ) • (evF t₀ s (eis (m + 2)) *
        evF t₀ s (Phi Y₁ Y₂ (GenusOne.SquareModule.sqMode P₁.isMod ((2 * m + 2 : ℕ) : ℤ) b x) y)) +
      ∑ m ∈ Finset.range K, evF t₀ s (((m + 1 : ℕ) : ℂ) • piK (m + 1) -
          if m = 0 then eis 1 else 0) *
        evF t₀ s (Phi Y₁ Y₂ x (GenusOne.SquareModule.sqMode P₂.isMod (m : ℤ) b y)) := by
  have hk : ∀ m : ℕ, Conv t₀ (((m + 1 : ℕ) : ℂ) • piK (m + 1) - if m = 0 then eis 1 else 0) :=
    fun m => ((conv_piK ht _).smul _).sub (conv_kernel_ite t₀ m)
  have h1 : Conv t₀ (∑ m ∈ Finset.range K, ((2 * m + 3 : ℕ) : ℂ) • (eis (m + 2) *
      Phi Y₁ Y₂ (GenusOne.SquareModule.sqMode P₁.isMod ((2 * m + 2 : ℕ) : ℤ) b x) y)) :=
    Conv.sum _ fun m _ => ((conv_eis t₀ _).mul (hΦ _ _)).smul _
  have h2 : Conv t₀ (∑ m ∈ Finset.range K, (((m + 1 : ℕ) : ℂ) • piK (m + 1) -
      if m = 0 then eis 1 else 0) *
        Phi Y₁ Y₂ x (GenusOne.SquareModule.sqMode P₂.isMod (m : ℤ) b y)) :=
    Conv.sum _ fun m _ => (hk m).mul (hΦ _ _)
  unfold leftLHS
  rw [evF_add ((hΦ _ _).add h1) h2, evF_add (hΦ _ _) h1,
    evF_sum _ fun m _ => ((conv_eis t₀ _).mul (hΦ _ _)).smul _,
    evF_sum _ fun m _ => (hk m).mul (hΦ _ _)]
  congr 2
  · apply Finset.sum_congr rfl
    intro m _
    rw [evF_smul, evF_mul (conv_eis t₀ _) (hΦ _ _)]
  · funext m
    rw [evF_mul (hk m) (hΦ _ _)]

theorem evF_rightLHS {t₀ s : ℂ} (ht : ‖t₀‖ < 1) (hΦ : ∀ v w, Conv t₀ (Phi Y₁ Y₂ v w))
    (b : V) (x : P₁.carrier) (y : P₂.carrier) (K : ℕ) :
    evF t₀ s (rightLHS Y₁ Y₂ b x y K) =
      evF t₀ s (Phi Y₁ Y₂ x (GenusOne.SquareModule.sqMode P₂.isMod (-2) b y)) +
      ∑ m ∈ Finset.range K, ((2 * m + 3 : ℕ) : ℂ) • (evF t₀ s (eis (m + 2)) *
        evF t₀ s (Phi Y₁ Y₂ x (GenusOne.SquareModule.sqMode P₂.isMod ((2 * m + 2 : ℕ) : ℤ) b y))) +
      ∑ m ∈ Finset.range K, evF t₀ s (((m + 1 : ℕ) : ℂ) • (((-1 : ℂ) ^ (m + 1 + 1)) • piK (m + 1)) -
          if m = 0 then eis 1 else 0) *
        evF t₀ s (Phi Y₁ Y₂ (GenusOne.SquareModule.sqMode P₁.isMod (m : ℤ) b x) y) := by
  have hk : ∀ m : ℕ, Conv t₀ (((m + 1 : ℕ) : ℂ) • (((-1 : ℂ) ^ (m + 1 + 1)) • piK (m + 1)) -
      if m = 0 then eis 1 else 0) :=
    fun m => (((conv_piK ht _).smul _).smul _).sub (conv_kernel_ite t₀ m)
  have h1 : Conv t₀ (∑ m ∈ Finset.range K, ((2 * m + 3 : ℕ) : ℂ) • (eis (m + 2) *
      Phi Y₁ Y₂ x (GenusOne.SquareModule.sqMode P₂.isMod ((2 * m + 2 : ℕ) : ℤ) b y))) :=
    Conv.sum _ fun m _ => ((conv_eis t₀ _).mul (hΦ _ _)).smul _
  have h2 : Conv t₀ (∑ m ∈ Finset.range K, (((m + 1 : ℕ) : ℂ) •
      (((-1 : ℂ) ^ (m + 1 + 1)) • piK (m + 1)) - if m = 0 then eis 1 else 0) *
        Phi Y₁ Y₂ (GenusOne.SquareModule.sqMode P₁.isMod (m : ℤ) b x) y) :=
    Conv.sum _ fun m _ => (hk m).mul (hΦ _ _)
  unfold rightLHS
  rw [evF_add ((hΦ _ _).add h1) h2, evF_add (hΦ _ _) h1,
    evF_sum _ fun m _ => ((conv_eis t₀ _).mul (hΦ _ _)).smul _,
    evF_sum _ fun m _ => (hk m).mul (hΦ _ _)]
  congr 2
  · apply Finset.sum_congr rfl
    intro m _
    rw [evF_smul, evF_mul (conv_eis t₀ _) (hΦ _ _)]
  · funext m
    rw [evF_mul (hk m) (hΦ _ _)]

end Expand

end VOA.Huang.GenusOneWard
