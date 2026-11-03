import VOA.Classification.COne.QExpThetaProgressions

/-! # Matching the theta Lambert series to the existing weight-one coefficients -/

open Complex Nat
open scoped UpperHalfPlane

noncomputable section
namespace VOA.Classification.COne.SSHecke

theorem theta_negative_residue {N : ℕ} (hN : 0 < N) (a : Fin N) (t : ℕ) :
    (t + a.val) % N = 0 ↔ t % N = (N - a.val) % N := by
  rw [Nat.add_mod, Nat.mod_eq_of_lt a.isLt]
  by_cases ha : a.val = 0
  · simp [ha]
  · have haN : N - a.val < N := by omega
    rw [Nat.mod_eq_of_lt haN]
    have ht := Nat.mod_lt t hN
    by_cases hs : t % N + a.val < N
    · rw [Nat.mod_eq_of_lt hs]
      omega
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      omega

theorem thetaResidueDivisor_summable (N a : ℕ) {u q : ℂ}
    (hu : ‖u‖ = 1) (hq : ‖q‖ < 1) :
    Summable (fun n : ℕ+ => thetaResidueDivisor N a u n * q ^ (n : ℕ)) := by
  have hs : Summable (fun n : ℕ => (n : ℝ) * ‖q‖ ^ n) := by
    simpa using summable_norm_pow_mul_geometric_of_norm_lt_one 1 (r := ‖q‖) (by simpa using hq)
  apply (hs.subtype (fun n : ℕ => 0 < n)).of_norm_bounded
  intro n
  rw [norm_mul, norm_pow]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  calc
    ‖thetaResidueDivisor N a u n‖ ≤ ∑ _ ∈ (n : ℕ).divisors, (1 : ℝ) := by
      apply norm_sum_le_of_le
      intro d _
      split_ifs <;> simp [norm_pow, hu]
    _ = ((n : ℕ).divisors.card : ℝ) := by simp
    _ ≤ (n : ℕ) := by exact_mod_cast Nat.card_divisors_le_self (n : ℕ)

theorem weightOneDivisorCoeff_eq_residue {N : ℕ} (hN : 0 < N) (ζ : ℂ)
    (a b : Fin N) (n : ℕ) :
    weightOneDivisorCoeff N ζ a b n =
      thetaResidueDivisor N a.val (ζ ^ b.val) n -
        thetaResidueDivisor N ((N - a.val) % N) (ζ ^ (N - b.val)) n := by
  unfold weightOneDivisorCoeff thetaResidueDivisor
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d _
  simp only [theta_negative_residue hN a d]
  simp only [← pow_mul, Nat.mul_comm b.val (n / d), Nat.mul_comm (N - b.val) (n / d)]

/-- The existing q-series as two residue Lambert sums and its exact constant. -/
theorem weightOneQSeries_eq_residueLambert {N : ℕ} (hN : 0 < N) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ N) (a b : Fin N) (hab : ¬(a.val = 0 ∧ b.val = 0)) (τ : ℍ) :
    let q := Function.Periodic.qParam (N : ℝ) τ
    weightOneQSeries N ζ a b τ = weightOneIntegralCoeff N ζ a b 0 +
      weightOneScale N ζ a b * (thetaResidueLambert N a.val (ζ ^ b.val) q -
        thetaResidueLambert N ((N - a.val) % N) (ζ ^ (N - b.val)) q) := by
  dsimp only
  have hq := norm_qParam_nat_lt_one hN τ
  have hu : ‖ζ ^ b.val‖ = 1 := by rw [norm_pow, hζ.norm'_eq_one hN.ne', one_pow]
  have hv : ‖ζ ^ (N - b.val)‖ = 1 := by rw [norm_pow, hζ.norm'_eq_one hN.ne', one_pow]
  rw [thetaResidueLambert_eq_divisors N a.val hu hq,
    thetaResidueLambert_eq_divisors N ((N - a.val) % N) hv hq]
  have hs := (hasSum_weightOneQSeries hN hζ a b τ).summable
  simp only [smul_eq_mul] at hs
  rw [weightOneQSeries, ← tsum_zero_pnat_eq_tsum_nat hs]
  simp only [pow_zero, mul_one]
  congr 1
  rw [← (thetaResidueDivisor_summable N a.val hu hq).tsum_sub
      (thetaResidueDivisor_summable N ((N - a.val) % N) hv hq), ← tsum_mul_left]
  apply tsum_congr
  intro n
  simp only [weightOneIntegralCoeff, hab, if_false, n.ne_zero,
    weightOneDivisorCoeff_eq_residue hN]
  ring

/-- Matching both exponential conventions, including the width-N local parameter. -/
theorem thetaExp_torsion_parameter (N a b : ℕ) (τ : ℍ) :
    thetaExp ((a : ℂ) / N * τ + (b : ℂ) / N) =
      weightOneStandardRoot N ^ b * Function.Periodic.qParam (N : ℝ) τ ^ a := by
  rw [weightOneStandardRoot, ← Complex.exp_nat_mul, qParam_nat_pow_exp, ← Complex.exp_add,
    thetaExp]
  congr 1
  push_cast
  ring

theorem thetaExp_tau_qParam {N : ℕ} (hN : 0 < N) (τ : ℍ) :
    thetaExp τ = Function.Periodic.qParam (N : ℝ) τ ^ N := by
  have hn : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  simpa [hn] using thetaExp_torsion_parameter N N 0 τ

theorem thetaExp_complement_parameter {N : ℕ} (hN : 0 < N) (a b : Fin N) (τ : ℍ) :
    thetaExp ((τ : ℂ) - ((a.val : ℂ) / N * τ + (b.val : ℂ) / N)) =
      weightOneStandardRoot N ^ (N - b.val) *
        Function.Periodic.qParam (N : ℝ) τ ^ (N - a.val) := by
  rw [← thetaExp_torsion_parameter]
  have hn : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have he : ((N - a.val : ℕ) : ℂ) / N * τ + ((N - b.val : ℕ) : ℂ) / N =
      ((τ : ℂ) - ((a.val : ℂ) / N * τ + (b.val : ℂ) / N)) + 1 := by
    rw [Nat.cast_sub a.isLt.le, Nat.cast_sub b.isLt.le]
    field_simp
    ring
  rw [he, thetaExp_add, (thetaExp_eq_one_iff 1).mpr ⟨1, by simp⟩, mul_one]

/-- The explicit Lambert-to-divisor Fourier identity for every positive level. -/
theorem weightOneLambertFourier {N : ℕ} (hN : 0 < N) : WeightOneLambertFourier N := by
  intro a b hab τ
  dsimp only
  let q := Function.Periodic.qParam (N : ℝ) τ
  let ζ := weightOneStandardRoot N
  let u := ζ ^ b.val
  let v := ζ ^ (N - b.val)
  have hζ : IsPrimitiveRoot ζ N := Complex.isPrimitiveRoot_exp N hN.ne'
  have hq : ‖q‖ < 1 := norm_qParam_nat_lt_one hN τ
  have hQ : ‖q ^ N‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg q) hq hN.ne'
  have hd : 0 < N - a.val := by omega
  have hneg := thetaResidueLambert_eq_thetaLambert hN hd (Nat.sub_le N a.val) v q
  have hbase := weightOneQSeries_eq_residueLambert hN hζ a b hab τ
  dsimp only at hbase
  change weightOneQSeries N ζ a b τ = weightOneIntegralCoeff N ζ a b 0 +
    weightOneScale N ζ a b * (thetaResidueLambert N a.val u q -
      thetaResidueLambert N ((N - a.val) % N) v q) at hbase
  rw [thetaExp_torsion_parameter, thetaExp_complement_parameter hN,
    thetaExp_tau_qParam hN]
  change weightOneQSeries N ζ a b τ = weightOneScale N ζ a b *
    (1 / 2 - (a.val : ℂ) / N + thetaLambert (q ^ N) (u * q ^ a.val) -
      thetaLambert (q ^ N) (v * q ^ (N - a.val)))
  have hn : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  by_cases ha : a.val = 0
  · have hb : b.val ≠ 0 := by tauto
    have hu : u ≠ 1 := by
      intro he
      have hdiv := (hζ.pow_eq_one_iff_dvd b.val).mp he
      exact hb (Nat.eq_zero_of_dvd_of_lt hdiv b.isLt)
    have hpos : thetaResidueLambert N a.val u q = thetaLambert (q ^ N) (u * q ^ N) := by
      rw [ha]
      simpa using thetaResidueLambert_eq_thetaLambert hN hN (le_refl N) u q
    have hc := weightOne_boundary_constant hN a b ha hb
    rw [thetaExp_div_nat] at hc
    change weightOneIntegralCoeff N ζ a b 0 / weightOneScale N ζ a b =
      (1 + u) / (2 * (1 - u)) at hc
    have hc' : weightOneIntegralCoeff N ζ a b 0 =
        weightOneScale N ζ a b * ((1 + u) / (2 * (1 - u))) := by
      simpa only [mul_comm] using (div_eq_iff (weightOneScale_ne_zero hN hζ a b)).mp hc
    rw [hbase, hpos, hneg, hc', ha]
    simp only [Nat.cast_zero, zero_div, sub_zero, pow_zero, mul_one]
    rw [thetaLambert_boundary hQ hu]
    ring
  · have ha0 : 0 < a.val := by omega
    have hpos := thetaResidueLambert_eq_thetaLambert hN ha0 a.isLt.le u q
    rw [Nat.mod_eq_of_lt a.isLt] at hpos
    have hc : weightOneIntegralCoeff N ζ a b 0 =
        weightOneScale N ζ a b * (1 / 2 - (a.val : ℂ) / N) := by
      simp [weightOneIntegralCoeff, weightOneScale, ha]
      field_simp
    rw [hbase, hpos, hneg, hc]
    ring

theorem weightOneLambertFourier24 : WeightOneLambertFourier24 :=
  fun _ hN _ => weightOneLambertFourier hN

/-- The unchanged theta Fourier input, with no remaining analytic hypothesis. -/
theorem weightOneThetaFourier {N : ℕ} (hN : 0 < N) : WeightOneThetaFourier N :=
  weightOneThetaFourier_of_lambert hN (weightOneLambertFourier hN)

theorem weightOneThetaFourier24 : WeightOneThetaFourier24 :=
  fun _ hN _ => weightOneThetaFourier hN

theorem fullLevelWeightOneSlash24 : FullLevelWeightOneSlash24 :=
  fullLevelWeightOneSlash24_of_thetaFourier weightOneThetaFourier24

/-- Only the independent weight-two Sturm-matching input remains. -/
theorem qExpPrinciple24Away_two_of_sturmMatching
    (hmatch : FullLevelWeightTwoSturmMatching24) : QExpPrinciple24Away 2 :=
  qExpPrinciple24Away_two_of_thetaFourier_and_sturmMatching weightOneThetaFourier24 hmatch

end VOA.Classification.COne.SSHecke
