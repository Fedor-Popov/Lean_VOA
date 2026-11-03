import VOA.Huang.FuchsianODE

/-!
# Uniform majorants with explicit initial data

For a fixed kernel and divisor, the cutoff in the geometric majorant argument
is independent of the solution. The multiplicative bound still depends on the
initial coefficients. This distinction is essential when applying an ODE to a
family of matrix coefficients. No assertion about VOA sewing is made here.
-/
namespace VOA.Huang.GenusTwoPoint
open VOA Filter
open scoped BigOperators

/-- A uniform cutoff for a homogeneous convolution inequality. Once the first
N coefficients satisfy a geometric bound, that SAME bound holds at every index.
N depends on the recurrence and the radius, but not on χ or B. -/
theorem uniform_majorant_cutoff {a p : ℕ → ℝ}
    (ha0 : ∀ n, 0 ≤ a n) (ha : Subexponential a)
    (hp : Tendsto p atTop atTop) (N₀ : ℕ) {r : ℝ} (hr : 1 < r) :
    ∃ N : ℕ, N₀ ≤ N ∧ ∀ (χ : ℕ → ℝ) (B : ℝ),
      (∀ n, 0 ≤ χ n) → 0 ≤ B →
      (∀ n, N₀ ≤ n → p n * χ n ≤ ∑ m ∈ Finset.range n, a (n - m) * χ m) →
      (∀ n < N, χ n ≤ B * r ^ n) → ∀ n, χ n ≤ B * r ^ n := by
  classical
  have hr0 : 0 < r := lt_trans zero_lt_one hr
  obtain ⟨σ, hσ1, hσr⟩ := exists_between hr
  have hσ0 : 0 < σ := lt_trans zero_lt_one hσ1
  obtain ⟨D, hD⟩ := ha σ hσ1
  have hD0 : 0 ≤ D := le_trans (ha0 0) (by simpa using hD 0)
  let t : ℝ := σ / r
  have ht0 : 0 < t := div_pos hσ0 hr0
  have ht1 : t < 1 := (div_lt_one hr0).mpr hσr
  let θ : ℝ := t / (1 - t)
  have hθ0 : 0 ≤ θ := le_of_lt (div_pos ht0 (by linarith))
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp (hp.eventually_ge_atTop (D * θ + 1))
  refine ⟨max N₀ N₁, le_max_left _ _, ?_⟩
  intro χ B hχ hB hrec hinit n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn : n < max N₀ N₁
    · exact hinit n hn
    have hn' : max N₀ N₁ ≤ n := Nat.le_of_not_gt hn
    have hpn : D * θ + 1 ≤ p n := hN₁ n (le_trans (le_max_right _ _) hn')
    have hpn0 : 0 < p n := by nlinarith
    have hsum : (∑ m ∈ Finset.range n, a (n - m) * χ m) ≤ D * B * θ * r ^ n := by
      calc
        (∑ m ∈ Finset.range n, a (n - m) * χ m) ≤
            ∑ m ∈ Finset.range n, (D * σ ^ (n - m)) * (B * r ^ m) := by
          refine Finset.sum_le_sum fun m hm => ?_
          exact mul_le_mul (hD _) (ih m (Finset.mem_range.mp hm)) (hχ m)
            (le_trans (ha0 _) (hD _))
        _ = D * B * r ^ n * ∑ m ∈ Finset.range n, t ^ (n - m) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun m hm => ?_
          have hmn : m ≤ n := (Finset.mem_range.mp hm).le
          have he : r ^ (n - m) * r ^ m = r ^ n := by
            rw [← pow_add, Nat.sub_add_cancel hmn]
          have hne : r ^ (n - m) ≠ 0 := ne_of_gt (pow_pos hr0 _)
          rw [show t = σ / r from rfl, div_pow, ← he]
          field_simp
        _ ≤ D * B * r ^ n * θ :=
          mul_le_mul_of_nonneg_left (sum_geom_shift_le ht0 ht1 n) (by positivity)
        _ = D * B * θ * r ^ n := by ring
    apply le_of_mul_le_mul_left (a := p n) _ hpn0
    calc
      p n * χ n ≤ ∑ m ∈ Finset.range n, a (n - m) * χ m :=
        hrec n (le_trans (le_max_left _ _) hn')
      _ ≤ D * B * θ * r ^ n := hsum
      _ ≤ p n * (B * r ^ n) := by nlinarith [mul_nonneg hB (pow_nonneg hr0.le n)]

/-- Uniformity for an arbitrary family, assuming a uniform bound on its finite
initial strip. This theorem does not infer that initial bound from the ODE. -/
theorem uniform_majorant_family {ι : Type*} {a p : ℕ → ℝ}
    (ha0 : ∀ n, 0 ≤ a n) (ha : Subexponential a)
    (hp : Tendsto p atTop atTop) (N₀ : ℕ) {r : ℝ} (hr : 1 < r) :
    ∃ N : ℕ, ∀ (χ : ι → ℕ → ℝ) (B : ι → ℝ),
      (∀ i n, 0 ≤ χ i n) → (∀ i, 0 ≤ B i) →
      (∀ i n, N₀ ≤ n → p n * χ i n ≤ ∑ m ∈ Finset.range n, a (n - m) * χ i m) →
      (∀ i n, n < N → χ i n ≤ B i * r ^ n) →
      ∀ i n, χ i n ≤ B i * r ^ n := by
  obtain ⟨N, _, hN⟩ := uniform_majorant_cutoff ha0 ha hp N₀ hr
  exact ⟨N, fun χ B hχ hB hrec hinit i => hN (χ i) (B i) (hχ i) (hB i)
    (hrec i) (hinit i)⟩

end VOA.Huang.GenusTwoPoint
