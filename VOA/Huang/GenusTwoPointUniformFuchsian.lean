import VOA.Huang.GenusTwoPointUniformMajorant

/-!
# A uniform Fuchsian estimate controlled by a finite initial jet

The equation, exponent and radius determine a cutoff N. A solution is bounded
by the sum of its first N coefficient norms times a geometric sequence. Thus a
uniform initial-jet bound gives a uniform bound for any family of solutions.
This does not assert a common equation or a bounded jet for VOA trace levels.
-/
namespace VOA.Huang.GenusTwoPoint
open VOA Filter PowerSeries FuchsianODE
open scoped BigOperators

/-- The norm recursion with the solution-independent indicial divisor and kernel.
This is the inequality used inside the existing indicial convergence proof. -/
theorem indicial_majorant_inequality {χ : ℕ → ℂ} (lam : ℂ) (s : ℕ)
    (g : ℕ → ℕ → ℂ)
    (hrec : ∀ n : ℕ, indicialP lam s g n * χ n =
      - ∑ m ∈ Finset.range n, ∑ i ∈ Finset.range s,
        g i (n - m) * (lam + (m : ℂ)) ^ i * χ m) (n : ℕ) :
    indicialDivisor lam s g n * ‖χ n‖ ≤
      ∑ m ∈ Finset.range n, indicialKernel s g (n - m) * ‖χ m‖ := by
  classical
  set B : ℝ := max ‖lam‖ 1 with hB
  have hB1 : (1 : ℝ) ≤ B := le_max_right _ _
  have hBlam : ‖lam‖ ≤ B := le_max_left _ _
  have hBn : ∀ n : ℕ, (1 : ℝ) ≤ B + (n : ℝ) := fun n => by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hBnpos : ∀ n : ℕ, (0 : ℝ) < (B + (n : ℝ)) ^ (s - 1) := fun n =>
    pow_pos (by linarith [hBn n]) _
  -- bound the right-hand side of the recursion
  have hnorm : ‖indicialP lam s g n‖ * ‖χ n‖
      ≤ (B + (n : ℝ)) ^ (s - 1) * ∑ m ∈ Finset.range n, indicialKernel s g (n - m) * ‖χ m‖ := by
    have h1 : ‖indicialP lam s g n‖ * ‖χ n‖
        = ‖∑ m ∈ Finset.range n, ∑ i ∈ Finset.range s,
            g i (n - m) * (lam + (m : ℂ)) ^ i * χ m‖ := by
      rw [← norm_mul, hrec n, norm_neg]
    rw [h1]
    refine le_trans (norm_sum_le _ _) ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun m hm => ?_
    have hmn : m < n := Finset.mem_range.mp hm
    refine le_trans (norm_sum_le _ _) ?_
    have hterm : ∀ i ∈ Finset.range s,
        ‖g i (n - m) * (lam + (m : ℂ)) ^ i * χ m‖
          ≤ (B + (n : ℝ)) ^ (s - 1) * (‖g i (n - m)‖ * ‖χ m‖) := by
      intro i hi
      have his : i ≤ s - 1 := by
        have := Finset.mem_range.mp hi
        omega
      have hlm : ‖lam + (m : ℂ)‖ ≤ B + (n : ℝ) := by
        refine le_trans (norm_add_le _ _) ?_
        have : ‖(m : ℂ)‖ = (m : ℝ) := by simp
        rw [this]
        have : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast le_of_lt hmn
        linarith
      have hpow : ‖lam + (m : ℂ)‖ ^ i ≤ (B + (n : ℝ)) ^ (s - 1) := by
        refine le_trans (pow_le_pow_left₀ (norm_nonneg _) hlm i) ?_
        exact pow_le_pow_right₀ (hBn n) his
      rw [norm_mul, norm_mul, norm_pow]
      calc ‖g i (n - m)‖ * ‖lam + (m : ℂ)‖ ^ i * ‖χ m‖
          ≤ ‖g i (n - m)‖ * (B + (n : ℝ)) ^ (s - 1) * ‖χ m‖ := by
            refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
            exact mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
        _ = (B + (n : ℝ)) ^ (s - 1) * (‖g i (n - m)‖ * ‖χ m‖) := by ring
    refine le_trans (Finset.sum_le_sum hterm) (le_of_eq ?_)
    rw [← Finset.mul_sum, indicialKernel, Finset.sum_mul]
  -- divide by the positive factor
  rw [indicialDivisor, div_mul_eq_mul_div, div_le_iff₀ (hBnpos n)]
  calc ‖indicialP lam s g n‖ * ‖χ n‖
      ≤ (B + (n : ℝ)) ^ (s - 1) * ∑ m ∈ Finset.range n, indicialKernel s g (n - m) * ‖χ m‖ :=
        hnorm
    _ = (∑ m ∈ Finset.range n, indicialKernel s g (n - m) * ‖χ m‖) * (B + (n : ℝ)) ^ (s - 1) := by
        ring


/-- Uniform propagation of any geometric initial-jet bound for a FIXED equation.
Resonant coefficients are included below N; no nonresonance assumption is used. -/
theorem uniform_fuchsian_cutoff (lam : ℂ) (s : ℕ) (c : ℕ → PowerSeries ℂ)
    (hc : ∀ i < s, c i ∈ SubexpPS) {r : ℝ} (hr : 1 < r) :
    ∃ N : ℕ, ∀ (G : PowerSeries ℂ) (B : ℝ), FuchsianEq lam s c G → 0 ≤ B →
      (∀ n < N, ‖coeff n G‖ ≤ B * r ^ n) → ∀ n, ‖coeff n G‖ ≤ B * r ^ n := by
  classical
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · refine ⟨0, fun G B hG hB _ n => ?_⟩
    have hz : G = 0 := by simpa [FuchsianEq] using hG
    simp only [hz, map_zero, norm_zero]
    positivity
  let g : ℕ → ℕ → ℂ := fun i n => coeff n (c i)
  have hg : Subexponential (indicialKernel s g) :=
    Subexponential.finsetSum (Finset.range s) (fun i n => ‖g i n‖)
      (fun i hi => hc i (Finset.mem_range.mp hi))
  obtain ⟨N, _, hN⟩ := uniform_majorant_cutoff (indicialKernel_nonneg s g) hg
    (tendsto_indicialDivisor_atTop lam hs g) 0 hr
  refine ⟨N, fun G B hG hB hinit => hN (fun n => ‖coeff n G‖) B
    (fun n => norm_nonneg _) hB ?_ hinit⟩
  intro n _
  exact indicial_majorant_inequality lam s g (indicial_recursion_of_fuchsianEq hG) n

/-- The multiplicative constant is explicitly the norm-sum of a finite initial
jet. The cutoff is uniform over ALL solutions of this fixed equation. -/
theorem uniform_fuchsian_initial_bound (lam : ℂ) (s : ℕ) (c : ℕ → PowerSeries ℂ)
    (hc : ∀ i < s, c i ∈ SubexpPS) {r : ℝ} (hr : 1 < r) :
    ∃ N : ℕ, ∀ G : PowerSeries ℂ, FuchsianEq lam s c G → ∀ n,
      ‖coeff n G‖ ≤ (∑ j ∈ Finset.range N, ‖coeff j G‖) * r ^ n := by
  obtain ⟨N, hN⟩ := uniform_fuchsian_cutoff lam s c hc hr
  refine ⟨N, fun G hG => hN G _ hG (Finset.sum_nonneg fun _ _ => norm_nonneg _) ?_⟩
  intro n hn
  exact (Finset.single_le_sum (fun j _ => norm_nonneg (coeff j G))
    (Finset.mem_range.mpr hn)).trans
    (le_mul_of_one_le_right (Finset.sum_nonneg fun _ _ => norm_nonneg _)
      (one_le_pow₀ hr.le))

/-- In radius notation, a common finite-jet bound C gives the requested
coefficient estimate C times R to the negative n, uniformly over the family. -/
theorem uniform_fuchsian_family_radius_bound {ι : Type*}
    (lam : ℂ) (s : ℕ) (c : ℕ → PowerSeries ℂ)
    (hc : ∀ i < s, c i ∈ SubexpPS) {R : ℝ} (hR0 : 0 < R) (hR1 : R < 1) :
    ∃ K : ℕ, ∀ (G : ι → PowerSeries ℂ) (C : ℝ),
      (∀ i, FuchsianEq lam s c (G i)) →
      (∀ i, (∑ j ∈ Finset.range K, ‖coeff j (G i)‖) ≤ C) →
      ∀ i n, ‖coeff n (G i)‖ ≤ C * (R ^ n)⁻¹ := by
  obtain ⟨K, hK⟩ := uniform_fuchsian_initial_bound lam s c hc ((one_lt_inv₀ hR0).2 hR1)
  refine ⟨K, fun G C heq hinit i n => ?_⟩
  have h := (hK (G i) (heq i) n).trans
    (mul_le_mul_of_nonneg_right (hinit i) (pow_nonneg (inv_nonneg.mpr hR0.le) n))
  simpa only [inv_pow] using h

/-- A finite initial jet determines a formal solution of a fixed Fuchsian
equation, including resonant equations. -/
theorem fuchsian_finite_jet_determines (lam : ℂ) (s : ℕ) (c : ℕ → PowerSeries ℂ)
    (hc : ∀ i < s, c i ∈ SubexpPS) :
    ∃ N : ℕ, ∀ G : PowerSeries ℂ, FuchsianEq lam s c G →
      (∀ j < N, coeff j G = 0) → G = 0 := by
  obtain ⟨N, hN⟩ := uniform_fuchsian_cutoff lam s c hc (r := 2) (by norm_num)
  refine ⟨N, fun G hG hz => ?_⟩
  have hb := hN G 0 hG le_rfl (fun j hj => by simp [hz j hj])
  ext n
  have := hb n
  simpa using norm_eq_zero.mp (le_antisymm (by simpa using this) (norm_nonneg _))

/-- A common fixed scalar Fuchsian equation cannot annihilate all monomials.
This prevents replacing weight-dependent ODEs by a single equation without proof. -/
theorem no_fixed_fuchsian_for_all_monomials (lam : ℂ) (s : ℕ)
    (c : ℕ → PowerSeries ℂ) (hc : ∀ i < s, c i ∈ SubexpPS) :
    ¬ ∀ n : ℕ, FuchsianEq lam s c (X ^ n) := by
  intro hall
  obtain ⟨N, hN⟩ := fuchsian_finite_jet_determines lam s c hc
  have hz := hN (X ^ N) (hall N) (fun j hj => by
    simp only [coeff_X_pow, if_neg (ne_of_lt hj)])
  have he := congrArg (coeff N) hz
  simp at he

/-- Constant solutions already show why an equation alone gives no uniform
amplitude bound. This is a statement about the Euler equation θG = 0. -/
theorem no_uniform_fuchsian_amplitude :
    ¬ ∃ B : ℝ, ∀ G : PowerSeries ℂ, FuchsianEq 0 1 (fun _ => 0) G → ‖coeff 0 G‖ ≤ B := by
  rintro ⟨B, hB⟩
  let z : ℂ := (max B 0 + 1 : ℝ)
  have he : FuchsianEq 0 1 (fun _ => 0) (PowerSeries.C z) := by
    simp only [FuchsianEq, Function.iterate_one, zero_mul, Finset.sum_const_zero, add_zero]
    ext n
    simp only [coeff_thetaShift, zero_add, coeff_C, map_zero]
    split_ifs with hn
    · simp [hn]
    · simp
  have hb := hB (PowerSeries.C z) he
  have hpos : 0 ≤ max B 0 + 1 := by linarith [le_max_right B 0]
  simp only [coeff_zero_C, z, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hpos] at hb
  linarith [le_max_left B 0]

end VOA.Huang.GenusTwoPoint
