import VOA.Huang.GenusTwoPointSepCuspKernels

/-! # Analytic identification of the rescaled formal Lambert kernels -/
noncomputable section
namespace VOA.Huang.GenusTwoPoint.Separate
open VOA QEquation
open scoped BigOperators

set_option maxHeartbeats 600000 in
-- The finite-support rows, geometric columns, and double-series reindexing
-- together exceed the default elaboration heartbeat budget.
/-- Absolute summability justifies collecting the Fourier mode and q degree.
This is a kernel identity, not an exchange of trace sums. -/
theorem hasSum_ellipticCusp (d : ℕ) {rho x q : ℂ}
    (hr : ‖rho‖ ≤ 1) (hx : ‖rho‖ * ‖x‖ ≤ 1)
    (hxi : ‖rho‖ * ‖x⁻¹‖ ≤ 1) (hq : ‖q‖ < 1) :
    HasSum (fun n => PowerSeries.coeff n
      (lambertCuspSeries (ellipticCoeff d x) rho) * q ^ n)
      (lambertTail (ellipticCoeff d x) (rho * q)) := by
  let f : ℕ → ℕ → ℂ := fun n k =>
    if k < n ∧ k + 1 ∣ n then (rho ^ n * ellipticCoeff d x k) * q ^ n else 0
  have hfzero (n k : ℕ) (hk : k ∉ Finset.range n) : f n k = 0 := by
    simp only [Finset.mem_range] at hk
    simp [f, hk]
  have hfn (n : ℕ) : (Function.support (f n)).Finite := by
    apply (Finset.range n).finite_toSet.subset
    intro k hk
    by_contra hn
    exact hk (hfzero n k hn)
  have hnorm (n : ℕ) : (∑' k, ‖f n k‖) ≤ 2 * (n : ℝ) ^ (d + 1) * ‖q‖ ^ n := by
    rw [tsum_eq_sum (s := Finset.range n) (fun k hk => by rw [hfzero n k hk, norm_zero])]
    calc
      _ ≤ ∑ _k ∈ Finset.range n, (2 * (n : ℝ) ^ d) * ‖q‖ ^ n := by
        apply Finset.sum_le_sum
        intro k hk
        dsimp [f]
        split_ifs
        · rw [norm_mul, norm_pow]
          exact mul_le_mul_of_nonneg_right
            (rescaled_ellipticCoeff_bound d hr hx hxi (by
              have := Finset.mem_range.mp hk; omega)) (by positivity)
        · simp only [norm_zero]; positivity
      _ = _ := by simp [pow_succ]; ring
  have hsum : Summable (fun p : ℕ × ℕ => f p.1 p.2) := by
    apply Summable.of_norm
    apply (summable_prod_of_nonneg (fun _ => norm_nonneg _)).mpr
    refine ⟨fun n => (summable_of_hasFiniteSupport (hfn n)).norm, ?_⟩
    apply Summable.of_nonneg_of_le (fun n => tsum_nonneg (fun _ => norm_nonneg _)) hnorm
    have hp := (summable_pow_mul_geometric_of_norm_lt_one (r := ‖q‖) (d + 1)
      (by simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg q)] using hq)).mul_left 2
    simpa only [mul_assoc] using hp
  have hrow (n : ℕ) : (∑' k, f n k) =
      PowerSeries.coeff n (lambertCuspSeries (ellipticCoeff d x) rho) * q ^ n := by
    rw [tsum_eq_sum (hfzero n), coeff_lambertCuspSeries, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [f, Finset.mem_range.mp hk, true_and]
    split_ifs <;> simp
  have hrq : ‖rho * q‖ < 1 := by
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg q) hr).trans_lt hq
  have hcol (k : ℕ) : HasSum (fun n => f n k)
      (ellipticCoeff d x k * (rho * q) ^ (k + 1) / (1 - (rho * q) ^ (k + 1))) := by
    let g : ℕ → ℕ := fun j => (k + 1) * (j + 1)
    have hg : Function.Injective g := by
      intro j l h
      dsimp [g] at h
      nlinarith
    have hzero : ∀ n, n ∉ Set.range g → f n k = 0 := by
      intro n hn
      dsimp [f]
      split_ifs with h
      · exfalso
        obtain ⟨l, hl⟩ := h.2
        have hl0 : 0 < l := by nlinarith [h.1]
        exact hn ⟨l - 1, by dsimp [g]; rw [Nat.sub_add_cancel hl0]; exact hl.symm⟩
      · rfl
    apply (hg.hasSum_iff hzero).mp
    have hp : ‖(rho * q) ^ (k + 1)‖ < 1 := by
      rw [norm_pow]
      exact pow_lt_one₀ (norm_nonneg _) hrq (by omega)
    have he (j : ℕ) : f (g j) k =
        (ellipticCoeff d x k * (rho * q) ^ (k + 1)) *
          ((rho * q) ^ (k + 1)) ^ j := by
      have hlt : k < g j := by dsimp [g]; nlinarith
      have hdvd : k + 1 ∣ g j := dvd_mul_right _ _
      simp only [f, hlt, hdvd, and_self, if_true, g]
      simp only [pow_mul, pow_succ, mul_pow]
      ring
    change HasSum (fun j => f (g j) k) _
    simp_rw [he]
    simpa only [div_eq_mul_inv] using
      (hasSum_geometric_of_norm_lt_one hp).mul_left
        (ellipticCoeff d x k * (rho * q) ^ (k + 1))
  have he : (∑' n, PowerSeries.coeff n
      (lambertCuspSeries (ellipticCoeff d x) rho) * q ^ n) =
      lambertTail (ellipticCoeff d x) (rho * q) := by
    calc
      _ = ∑' n, ∑' k, f n k := tsum_congr fun n => (hrow n).symm
      _ = ∑' k, ∑' n, f n k := hsum.tsum_comm.symm
      _ = _ := tsum_congr fun k => (hcol k).tsum_eq
  rw [← he]
  exact (hsum.prod.congr hrow).hasSum

/-- Evaluation of the actual rescaled Eisenstein expansion. -/
theorem hasSum_eisensteinCusp (j : ℕ) {rho q : ℂ}
    (hr : ‖rho‖ ≤ 1) (hq : ‖q‖ < 1) :
    HasSum (fun n => PowerSeries.coeff n (eisensteinCuspSeries j rho) * q ^ n)
      (huangEisensteinQ j (rho * q)) := by
  have hrq : ‖rho * q‖ < 1 := by
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg q) hr).trans_lt hq
  have hs : Summable (fun n => zhuG j n * (rho * q) ^ n) := by
    apply Summable.of_norm
    simpa only [norm_mul, norm_pow] using summable_of_subexponential
      (fun n => norm_nonneg (zhuG j n)) (subexponential_zhuG j)
      (norm_nonneg _) hrq
  convert hs.hasSum.mul_left ((2 * (Real.pi : ℂ) * Complex.I) ^ (2 * j)) using 1
  funext n
  simp only [eisensteinCuspSeries, PowerSeries.coeff_smul, PowerSeries.coeff_rescale,
    PowerSeries.coeff_mk, smul_eq_mul, mul_pow]
  ring

private theorem hasSum_constantCusp (c q : ℂ) :
    HasSum (fun n => PowerSeries.coeff n (PowerSeries.C c) * q ^ n) c := by
  convert (hasSum_ite_eq 0 c : HasSum (fun n : ℕ => if n = 0 then c else 0) c) using 1
  funext n
  by_cases hn : n = 0 <;> simp [PowerSeries.coeff_C, hn]

/-- The even Fourier model is the evaluation of the concrete formal kernel. -/
theorem hasSum_wpTwoCusp {rho x q : ℂ} (hr : ‖rho‖ ≤ 1)
    (hx : ‖rho‖ * ‖x‖ ≤ 1) (hxi : ‖rho‖ * ‖x⁻¹‖ ≤ 1)
    (hx₁ : ‖x‖ < 1) (hq : ‖q‖ < 1) :
    HasSum (fun n => PowerSeries.coeff n (wpCuspSeries 1 x 0 rho) * q ^ n)
      (wpTwoQ x (rho * q)) := by
  have h := hasSum_ellipticCusp 1 hr hx hxi hq
  have hconst : HasSum (fun n => PowerSeries.coeff n
      (PowerSeries.C (x / (1 - x) ^ 2)) * q ^ n) (x / (1 - x) ^ 2) := by
    convert (hasSum_ite_eq 0 (x / (1 - x) ^ 2) :
      HasSum (fun n : ℕ => if n = 0 then x / (1 - x) ^ 2 else 0) _) using 1
    funext n
    by_cases hn : n = 0 <;> simp [PowerSeries.coeff_C, hn]
  have hg := hasSum_eisensteinCusp 1 hr hq
  convert ((hconst.add h).mul_left ((2 * (Real.pi : ℂ) * Complex.I) ^ 2)).sub hg using 1
  · funext n
    simp only [wpCuspSeries, elliptic_constant_one hx₁]
    norm_num [map_add, map_sub, PowerSeries.coeff_smul, smul_eq_mul]
    ring

/-- The odd Fourier model retains its factorial normalization. -/
theorem hasSum_wpThreeCusp {rho x q : ℂ} (hr : ‖rho‖ ≤ 1)
    (hx : ‖rho‖ * ‖x‖ ≤ 1) (hxi : ‖rho‖ * ‖x⁻¹‖ ≤ 1)
    (hx₁ : ‖x‖ < 1) (hq : ‖q‖ < 1) :
    HasSum (fun n => PowerSeries.coeff n (wpCuspSeries 2 x 0 rho) * q ^ n)
      (wpThreeQ x (rho * q)) := by
  have h := hasSum_ellipticCusp 2 hr hx hxi hq
  have hconst := hasSum_constantCusp (x * (1 + x) / (1 - x) ^ 3) q
  convert (hconst.add h).mul_left (-((2 * (Real.pi : ℂ) * Complex.I) ^ 3 / 2)) using 1
  funext n
  simp only [wpCuspSeries, elliptic_constant_two hx₁]
  norm_num [map_add, PowerSeries.coeff_smul, smul_eq_mul]
  ring

/-- The wp₁ correction has the same admissible radius; the additive coordinate
and the constant -pi*i are included. -/
theorem hasSum_wpOneCusp {rho x q : ℂ} (t : ℂ) (hr : ‖rho‖ ≤ 1)
    (hx : ‖rho‖ * ‖x‖ ≤ 1) (hxi : ‖rho‖ * ‖x⁻¹‖ ≤ 1)
    (hx₁ : ‖x‖ < 1) (hq : ‖q‖ < 1) :
    HasSum (fun n => PowerSeries.coeff n (wpCuspSeries 0 x t rho) * q ^ n)
      (-(2 * (Real.pi : ℂ) * Complex.I) *
        (x / (1 - x) + lambertTail (ellipticCoeff 0 x) (rho * q)) +
        t * huangEisensteinQ 1 (rho * q) - (Real.pi : ℂ) * Complex.I) := by
  have hc : (∑' k : ℕ, (k + 1 : ℂ) ^ 0 * x ^ (k + 1)) = x / (1 - x) := by
    simpa only [pow_zero, one_mul, pow_succ', div_eq_mul_inv] using
      ((hasSum_geometric_of_norm_lt_one hx₁).mul_left x).tsum_eq
  have h := (hasSum_constantCusp (x / (1 - x)) q).add
    (hasSum_ellipticCusp 0 hr hx hxi hq)
  have hg := (hasSum_eisensteinCusp 1 hr hq).mul_left t
  convert ((h.mul_left (-(2 * (Real.pi : ℂ) * Complex.I))).add hg).sub
    (hasSum_constantCusp ((Real.pi : ℂ) * Complex.I) q) using 1
  funext n
  simp only [wpCuspSeries, hc]
  norm_num [map_add, map_sub, PowerSeries.coeff_smul, smul_eq_mul]
  ring

end VOA.Huang.GenusTwoPoint.Separate
