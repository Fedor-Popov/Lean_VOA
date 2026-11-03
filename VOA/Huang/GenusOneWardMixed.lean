import VOA.Huang.GenusOneWardMixedFormal
import VOA.Huang.ZhuModData

/-!
# The mixed omega clause of `RawCuspCoordinateCollection`

Huang's `U(1)` sends `ω` to `(2πi)² (ω − c/24)`. The evaluated minus-one
identity for `ω − c/24`, the zero-mode relation, and the explicit `P₁` kernel
(whose `πi` and logarithmic terms combine to `piK 0 + 1/2`) give the third
clause.
-/
noncomputable section
namespace VOA.Huang.GenusOneWard
open VOA Module
open VOA.Huang.GenusTwoPoint.Separate
open VOA.Huang.GenusTwoPoint (moduleWeightExp moduleWeightExp_of_weight moduleWeightExp_add
  moduleWeightExp_zero logTwoPiI)
open VOA.Huang.GenusTwoPoint.QEquation (TailBound exists_tailBound ellipticCoeff Kernels)
open VOA.Huang.GenusOne.SquareModule (shiftedOmega)
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  {P₁ P₂ N Q : LWModule W}

theorem huangStateU_conformal :
    huangStateU W W.conformalVector =
      ((2 * (Real.pi : ℂ) * Complex.I) ^ 2) • shiftedOmega W := by
  change normalizedStateChange W
    (moduleWeightExp (adjointModule W) logTwoPiI W.conformalVector) = _
  have hmem : W.conformalVector ∈ (adjointModule W).weight ((2 : ℕ) : ℂ) := by
    rw [ZhuModData.adjointModule_weight_nat]; exact W.conformal_mem
  rw [moduleWeightExp_of_weight _ _ hmem, map_smul, normalizedStateChange_conformalVector,
    shiftedOmega, ← exp_logTwoPiI, ← Complex.exp_nat_mul]
  congr 2
  push_cast
  ring

theorem huangModeScale_mul_pow_succ (m : ℕ) :
    huangModeScale (m : ℤ) * (2 * (Real.pi : ℂ) * Complex.I) ^ (m + 1) = 1 := by
  rw [← exp_logTwoPiI, huangModeScale, ← Complex.exp_nat_mul, ← Complex.exp_add]
  rw [show -logTwoPiI * (((m : ℤ) : ℂ) + 1) + ((m + 1 : ℕ) : ℂ) * logTwoPiI = 0 by
    push_cast; ring, Complex.exp_zero]

theorem huangModeScale_neg_one : huangModeScale (-1) = 1 := by
  rw [huangModeScale]; norm_num

theorem thetaShift_evF (lam t₀ s : ℂ) (f : R2) :
    FuchsianODE.thetaShift lam (evF t₀ s f) = evF t₀ s (thetaR2 lam f) := by
  ext n
  rw [FuchsianODE.coeff_thetaShift, coeff_evF, coeff_evF]
  simp only [thetaR2, c2_mk2, mul_assoc, tsum_mul_left]
  ring

/-- The mixed Weierstrass kernels with their mode factor and the conformal weight. -/
theorem wpCusp_scale_mixed {t₀ : ℂ} (ht0 : t₀ ≠ 0) (ht : ‖t₀‖ < 1) (rho : ℂ) (m : ℕ) :
    huangModeScale ((m + 1 : ℕ) : ℤ) • ((2 * (Real.pi : ℂ) * Complex.I) ^ 2 •
        ((-1 : PowerSeries ℂ) ^ (m + 1) * wpCuspSeries (m + 1) t₀ 0 rho)) =
      (2 * (Real.pi : ℂ) * Complex.I) ^ 2 • ((if m = 0 then evF t₀ (rho * t₀⁻¹) (eis 1) else 0) -
        evF t₀ (rho * t₀⁻¹) (piK (m + 1))) := by
  rw [evF_piK ht0 ht, evF_eis ht0]
  have hscale := huangModeScale_mul_pow_succ (m + 1)
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
  have hneg : ((-1 : PowerSeries ℂ) ^ (m + 1)) = PowerSeries.C ((-1 : ℂ) ^ (m + 1)) := by simp
  rw [hwp, hneg]
  have hsign : ((-1 : ℂ) ^ (m + 1)) * (-1 : ℂ) ^ (m + 1 + 1) = -1 := by
    rw [← pow_add, show m + 1 + (m + 1 + 1) = 2 * (m + 1) + 1 by ring, pow_succ, pow_mul]
    norm_num
  by_cases h0 : m = 0
  · subst h0
    simp only [if_true, eisensteinCuspSeries]
    simp only [zero_add, Nat.factorial_one, Nat.cast_one] at hscale hsign ⊢
    ext n
    simp only [PowerSeries.coeff_smul, map_add, map_neg, map_sub, smul_eq_mul,
      PowerSeries.coeff_C_mul, div_one]
    set a := PowerSeries.coeff n A
    set r := PowerSeries.coeff n (PowerSeries.rescale rho (PowerSeries.mk (zhuG 1)))
    push_cast at hscale ⊢
    linear_combination (E ^ 2 * (((-1 : ℂ) ^ 1 * (-1) ^ (1 + 1)) * a + r)) * hscale +
      E ^ 2 * a * hsign
  · simp only [if_neg h0, add_zero, zero_sub]
    ext n
    simp only [PowerSeries.coeff_smul, PowerSeries.coeff_C_mul, smul_eq_mul, map_neg]
    set a := PowerSeries.coeff n A
    rw [div_eq_mul_inv, div_eq_mul_inv, one_mul]
    push_cast at hscale ⊢
    linear_combination (E ^ 2 * a * ((((m + 1).factorial : ℕ) : ℂ))⁻¹ *
        ((-1) ^ (m + 1) * (-1) ^ (m + 1 + 1))) * hscale +
      (E ^ 2 * a * ((((m + 1).factorial : ℕ) : ℂ))⁻¹) * hsign

/-- The energy kernel `P₁` with its logarithmic and `πi` constant. -/
theorem cuspEnergyP1_val {z₁ z₂ rho : ℂ} (hz₂ : z₂ ≠ 0) (hz : ‖z₂‖ < ‖z₁‖)
    (hr : ‖rho‖ ≤ ‖z₂ / z₁‖) :
    ((cuspEnergyP1 hz₂ hz hr : SubexpPS) : PowerSeries ℂ) =
      (2 * (Real.pi : ℂ) * Complex.I) •
        (PowerSeries.C (Complex.log z₂ - Complex.log z₁) *
            evF (z₂ / z₁) (rho * (z₂ / z₁)⁻¹) (eis 1) -
          evF (z₂ / z₁) (rho * (z₂ / z₁)⁻¹) (piK 0) - PowerSeries.C (1 / 2)) := by
  have hz₁ : z₁ ≠ 0 := norm_pos_iff.mp ((norm_nonneg _).trans_lt hz)
  have ht0 : z₂ / z₁ ≠ 0 := div_ne_zero hz₂ hz₁
  have ht : ‖z₂ / z₁‖ < 1 := by
    rw [norm_div, div_lt_one (norm_pos_iff.mpr hz₁)]; exact hz
  have hE : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero))
      Complex.I_ne_zero
  change wpCuspSeries 0 (z₂ / z₁) (cuspLogCoordinate z₂ - cuspLogCoordinate z₁) rho = _
  rw [wpCuspSeries, if_pos rfl, evF_piK ht0 ht, evF_eis ht0, eisensteinCuspSeries,
    ← PowerSeries.smul_eq_C_mul]
  ext n
  simp only [cuspLogCoordinate, map_add, map_sub, PowerSeries.coeff_smul, smul_eq_mul,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_C, Nat.factorial_zero, Nat.cast_one, div_one,
    zero_add, pow_one, pow_zero, mul_one]
  field_simp
  split_ifs <;> ring

section Expand
variable (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
  (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)

/-- Evaluation of the formal ω̃ identity, with the first terms of both sums split off. -/
theorem evF_mixedLHS {t₀ s : ℂ} (ht : ‖t₀‖ < 1) (hΦ : ∀ v w, Conv t₀ (Phi Y₁ Y₂ v w))
    (x : P₁.carrier) (y : P₂.carrier) (K : ℕ) :
    evF t₀ s (mixedLHS Y₁ Y₂ x y (K + 1)) =
      evF t₀ s (Phi Y₁ Y₂ (GenusOne.SquareModule.sqMode P₁.isMod (-1) (shiftedOmega W) x) y) -
      (evF t₀ s (thetaR2 (N.h - W.centralCharge / 24) (Phi Y₁ Y₂ x y)) +
        (∑ k ∈ Finset.range K, evF t₀ s (eis (k + 2)) * evF t₀ s (Phi Y₁ Y₂
          (GenusOne.SquareModule.sqMode P₁.isMod ((2 * (k + 1) + 1 : ℕ) : ℤ) (shiftedOmega W) x) y) +
          evF t₀ s (eis 1) * evF t₀ s (Phi Y₁ Y₂
            (GenusOne.SquareModule.sqMode P₁.isMod ((1 : ℕ) : ℤ) (shiftedOmega W) x) y)) +
        (∑ k ∈ Finset.range K, evF t₀ s (piK (k + 1)) * evF t₀ s (Phi Y₁ Y₂ x
          (GenusOne.SquareModule.sqMode P₂.isMod ((k + 1 : ℕ) : ℤ) (shiftedOmega W) y)) +
          (evF t₀ s (piK 0) + PowerSeries.C (1 / 2)) * evF t₀ s (Phi Y₁ Y₂ x
            (GenusOne.SquareModule.sqMode P₂.isMod ((0 : ℕ) : ℤ) (shiftedOmega W) y)))) := by
  have hθ : Conv t₀ (thetaR2 (N.h - W.centralCharge / 24) (Phi Y₁ Y₂ x y)) := by
    intro n
    have h := (spatialConvergent t₀).smul_mem (show PowerSeries.coeff n (Phi Y₁ Y₂ x y) ∈
      spatialConvergent t₀ from hΦ x y n) (N.h - W.centralCharge / 24 + n)
    convert h using 1
    ext k
    change c2 (thetaR2 _ _) n k = _
    rw [thetaR2, c2_mk2]
    simp [c2]
  have hk : ∀ m : ℕ, Conv t₀ (piK m + if m = 0 then algebraMap ℂ R2 (1 / 2) else 0) := by
    intro m
    refine (conv_piK ht m).add ?_
    split_ifs
    · exact conv_algebraMap t₀ _
    · exact conv_zero t₀
  have h1 : Conv t₀ (∑ m ∈ Finset.range (K + 1), eis (m + 1) * Phi Y₁ Y₂
      (GenusOne.SquareModule.sqMode P₁.isMod ((2 * m + 1 : ℕ) : ℤ) (shiftedOmega W) x) y) :=
    Conv.sum _ fun m _ => (conv_eis t₀ _).mul (hΦ _ _)
  have h2 : Conv t₀ (∑ m ∈ Finset.range (K + 1),
      (piK m + if m = 0 then algebraMap ℂ R2 (1 / 2) else 0) *
        Phi Y₁ Y₂ x (GenusOne.SquareModule.sqMode P₂.isMod (m : ℤ) (shiftedOmega W) y)) :=
    Conv.sum _ fun m _ => (hk m).mul (hΦ _ _)
  unfold mixedLHS
  rw [evF_sub (hΦ _ _) ((hθ.add h1).add h2), evF_add (hθ.add h1) h2, evF_add hθ h1,
    evF_sum _ fun m _ => (conv_eis t₀ _).mul (hΦ _ _),
    evF_sum _ fun m _ => (hk m).mul (hΦ _ _),
    Finset.sum_range_succ', Finset.sum_range_succ']
  have hk' : ∀ k : ℕ, (piK (k + 1) + if k + 1 = 0 then algebraMap ℂ R2 (1 / 2) else 0) =
      piK (k + 1) := by
    intro k
    rw [if_neg (by omega), add_zero]
  simp only [hk', if_true]
  simp only [evF_mul (conv_eis t₀ _) (hΦ _ _), evF_mul (conv_piK ht _) (hΦ _ _),
    evF_mul ((conv_piK ht 0).add (conv_algebraMap t₀ _)) (hΦ _ _)]
  rw [evF_add (conv_piK ht 0) (conv_algebraMap t₀ _), evF_algebraMap]

end Expand

end VOA.Huang.GenusOneWard
