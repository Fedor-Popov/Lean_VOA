import VOA.Huang.HuangODEThreeGrowth

/-! # Two-index convergence from a radial Fuchsian coefficient equation

The Euler operator is `λ + x∂x + y∂y`; its eigenvalue on the `(m,n)`
coefficient is `λ+m+n`. The definition below is the exact coefficient
recursion after the constant coefficients have been moved to the left.
It allows indicial resonances. No slice-dependent constants occur.

For a local sewing chart one first rescales into a bidisc avoiding all other
collision divisors. An equation in one variable after fixing the other does
not by itself instantiate this simultaneous coefficient recurrence.
-/

noncomputable section
namespace VOA.Huang.HuangODEThree
open VOA Filter
open scoped BigOperators

/-- Coefficient form of a monic equation in the radial twisted Euler operator.
Here `g k i j` is the `(i,j)` coefficient of the coefficient of `θ^k`.
Only the constant coefficients enter the indicial polynomial. -/
def RadialFuchsian (lam : ℂ) (s : ℕ) (g : ℕ → ℕ → ℕ → ℂ)
    (c : ℕ → ℕ → ℂ) : Prop :=
  ∀ m n, indicialP lam s (fun k _ => g k 0 0) (m + n) * c m n =
    - ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1),
      if i + j < m + n then
        ∑ k ∈ Finset.range s, g k (m - i) (n - j) *
          (lam + ((i + j : ℕ) : ℂ)) ^ k * c i j else 0

/-- Extract a joint norm recurrence from a monic radial equation. -/
theorem radialRecurrence_of_fuchsian {lam : ℂ} {s : ℕ} (hs : 1 ≤ s)
    {g : ℕ → ℕ → ℕ → ℂ} {c : ℕ → ℕ → ℂ} {b : ℕ → ℝ}
    (hb₀ : ∀ l, 0 ≤ b l) (hb : Subexponential b)
    (hg : ∀ k < s, ∀ i j, ‖g k i j‖ ≤ b (i + j))
    (heq : RadialFuchsian lam s g c) : RadialRecurrence c := by
  classical
  let B : ℝ := max ‖lam‖ 1
  have hB₁ : 1 ≤ B := le_max_right _ _
  have hBl : ‖lam‖ ≤ B := le_max_left _ _
  have hBn : ∀ l : ℕ, 1 ≤ B + l := fun l =>
    le_trans hB₁ (le_add_of_nonneg_right (Nat.cast_nonneg l))
  have hpos : ∀ l : ℕ, 0 < (B + l) ^ (s - 1) := fun l =>
    pow_pos (by linarith [hBn l]) _
  refine ⟨fun l => (s : ℝ) * b l,
    indicialDivisor lam s (fun k _ => g k 0 0), 0,
    (fun _ => mul_nonneg (Nat.cast_nonneg _) (hb₀ _)),
    hb.const_mul (Nat.cast_nonneg s), tendsto_indicialDivisor_atTop lam hs _, ?_⟩
  intro m n _
  have hnorm : ‖indicialP lam s (fun k _ => g k 0 0) (m + n)‖ * ‖c m n‖ ≤
      (B + (m + n : ℕ)) ^ (s - 1) *
        ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1),
          if i + j < m + n then ((s : ℝ) * b (m + n - (i + j))) * ‖c i j‖ else 0 := by
    rw [← norm_mul, heq, norm_neg]
    refine le_trans (norm_sum_le _ _) ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    refine le_trans (norm_sum_le _ _) ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j hj => ?_
    have him : i ≤ m := by simpa using hi
    have hjn : j ≤ n := by simpa using hj
    split_ifs with hij
    · have hdiff : m - i + (n - j) = m + n - (i + j) := by omega
      have hl : ‖lam + ((i + j : ℕ) : ℂ)‖ ≤ B + (m + n : ℕ) := by
        refine le_trans (norm_add_le _ _) ?_
        rw [Complex.norm_natCast]
        have hh : ((i + j : ℕ) : ℝ) ≤ (m + n : ℕ) := by exact_mod_cast hij.le
        linarith
      have hterm : ∀ k ∈ Finset.range s,
          ‖g k (m - i) (n - j) * (lam + ((i + j : ℕ) : ℂ)) ^ k * c i j‖ ≤
            (B + (m + n : ℕ)) ^ (s - 1) * (b (m + n - (i + j)) * ‖c i j‖) := by
        intro k hk
        have hk' := Finset.mem_range.mp hk
        have hpow : ‖lam + ((i + j : ℕ) : ℂ)‖ ^ k ≤ (B + (m + n : ℕ)) ^ (s - 1) :=
          le_trans (pow_le_pow_left₀ (norm_nonneg _) hl k)
            (pow_le_pow_right₀ (hBn _) (by omega))
        have hg' := hg k hk' (m - i) (n - j)
        rw [hdiff] at hg'
        simp only [norm_mul, norm_pow]
        calc
          _ ≤ b (m + n - (i + j)) * (B + (m + n : ℕ)) ^ (s - 1) * ‖c i j‖ := by
            gcongr
            exact hb₀ _
          _ = _ := by ring
      refine le_trans (norm_sum_le _ _) (le_trans (Finset.sum_le_sum hterm) ?_)
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      exact le_of_eq (by ring)
    · simp
  rw [indicialDivisor, div_mul_eq_mul_div, div_le_iff₀ (hpos (m + n))]
  exact hnorm.trans_eq (mul_comm _ _)

/-- Convergence of every formal solution of the displayed two-index equation,
including resonant indicial parameters, on the bidisc of coefficient convergence. -/
theorem summable_of_radialFuchsian {lam : ℂ} {s : ℕ} (hs : 1 ≤ s)
    {g : ℕ → ℕ → ℕ → ℂ} {c : ℕ → ℕ → ℂ} {b : ℕ → ℝ}
    (hb₀ : ∀ l, 0 ≤ b l) (hb : Subexponential b)
    (hg : ∀ k < s, ∀ i j, ‖g k i j‖ ≤ b (i + j))
    (heq : RadialFuchsian lam s g c) {x y : ℂ} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) :
    Summable (fun q : ℕ × ℕ => ‖c q.1 q.2 * x ^ q.1 * y ^ q.2‖) :=
  summable_of_radialRecurrence (radialRecurrence_of_fuchsian hs hb₀ hb hg heq) hx hy

end VOA.Huang.HuangODEThree
