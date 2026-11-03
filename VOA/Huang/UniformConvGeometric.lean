import VOA.Huang.UniformConvSeparate

/-!
# Separate Fuchsian systems with coefficients holomorphic on a polydisc

`SeparateSystem c R₁ R₂` packages two separate monic Euler-type equations for the array
`c`, whose coefficient series are bounded by `G R₁^i R₂^j` (holomorphic on the polydisc
of radii `1/R₁`, `1/R₂`), with eigenvalues of linear growth and joint dominance.

Proved here:
* `diagonalFuchsian_rescale` — rescaling both variables preserves the equation form;
* `SeparateSystem.geometric_bound` — `‖c i j‖ ≤ K (a R₁)^i (a R₂)^j` for every `a > 1`;
* `dominance_of_linear`, `growth_of_linear` — two Euler operators with integer linear
  eigenvalue forms of nonzero determinant satisfy the growth and dominance conditions;
* `LocalSeparateSolution.localJointGrowth` — the separate-equation analogue of
  `LocalRadialSolution.localJointGrowth`.
-/

noncomputable section
namespace VOA.Huang.UniformConv
open VOA Filter VOA.Huang.HuangODEThree
open scoped BigOperators

/-- Rescaling both variables by nonzero factors preserves the coefficient equation. -/
theorem diagonalFuchsian_rescale {e : ℕ → ℕ → ℂ} {s : ℕ} {g : ℕ → ℕ → ℕ → ℂ}
    {c : ℕ → ℕ → ℂ} {u₁ u₂ : ℂ} (h₁ : u₁ ≠ 0) (h₂ : u₂ ≠ 0)
    (heq : DiagonalFuchsian e s g c) :
    DiagonalFuchsian e s (fun k i j => g k i j / (u₁ ^ i * u₂ ^ j))
      (fun i j => c i j / (u₁ ^ i * u₂ ^ j)) := by
  intro m n
  have h := heq m n
  have hW : u₁ ^ m * u₂ ^ n ≠ 0 := mul_ne_zero (pow_ne_zero _ h₁) (pow_ne_zero _ h₂)
  simp only [pow_zero, mul_one, div_one]
  rw [← mul_div_assoc, h, Finset.sum_div]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun j hj => ?_
  have him : i ≤ m := by simpa [Nat.lt_succ_iff] using hi
  have hjn : j ≤ n := by simpa [Nat.lt_succ_iff] using hj
  split_ifs with hij
  · have hsplit : u₁ ^ m * u₂ ^ n = (u₁ ^ (m - i) * u₂ ^ (n - j)) * (u₁ ^ i * u₂ ^ j) := by
      rw [mul_mul_mul_comm, ← pow_add, ← pow_add, Nat.sub_add_cancel him,
        Nat.sub_add_cancel hjn]
    have hA : u₁ ^ (m - i) * u₂ ^ (n - j) ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ h₁) (pow_ne_zero _ h₂)
    have hB : u₁ ^ i * u₂ ^ j ≠ 0 := mul_ne_zero (pow_ne_zero _ h₁) (pow_ne_zero _ h₂)
    rw [hsplit, Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    field_simp
  · simp

/-- Two separate monic Euler-type equations for the array `c`, with coefficient series
bounded by `G R₁^i R₂^j`, eigenvalues of linear growth and joint dominance. -/
structure SeparateSystem (c : ℕ → ℕ → ℂ) (R₁ R₂ : ℝ) where
  e₁ : ℕ → ℕ → ℂ
  e₂ : ℕ → ℕ → ℂ
  s₁ : ℕ
  s₂ : ℕ
  g₁ : ℕ → ℕ → ℕ → ℂ
  g₂ : ℕ → ℕ → ℕ → ℂ
  G : ℝ
  B : ℝ
  κ : ℝ
  D : ℝ
  hs₁ : 1 ≤ s₁
  hs₂ : 1 ≤ s₂
  hB : 1 ≤ B
  hκ : 0 < κ
  he₁ : ∀ i j, ‖e₁ i j‖ ≤ B * (1 + ((i + j : ℕ) : ℝ))
  he₂ : ∀ i j, ‖e₂ i j‖ ≤ B * (1 + ((i + j : ℕ) : ℝ))
  hdom : ∀ m n, κ * ((m + n : ℕ) : ℝ) ≤ ‖e₁ m n‖ + D ∨
    κ * ((m + n : ℕ) : ℝ) ≤ ‖e₂ m n‖ + D
  hg₁ : ∀ k < s₁, ∀ i j, ‖g₁ k i j‖ ≤ G * R₁ ^ i * R₂ ^ j
  hg₂ : ∀ k < s₂, ∀ i j, ‖g₂ k i j‖ ≤ G * R₁ ^ i * R₂ ^ j
  eq₁ : DiagonalFuchsian e₁ s₁ g₁ c
  eq₂ : DiagonalFuchsian e₂ s₂ g₂ c

/-- **Geometric joint bound from a separate system.** The rates are those of the
coefficient polydisc, enlarged by an arbitrary `a > 1`. -/
theorem SeparateSystem.geometric_bound {c : ℕ → ℕ → ℂ} {R₁ R₂ : ℝ}
    (hR₁ : 0 < R₁) (hR₂ : 0 < R₂) (S : SeparateSystem c R₁ R₂) :
    ∀ a : ℝ, 1 < a → ∃ K : ℝ, 0 ≤ K ∧
      ∀ i j, ‖c i j‖ ≤ K * (a * R₁) ^ i * (a * R₂) ^ j := by
  intro a ha
  have hu₁ : ((R₁ : ℂ)) ≠ 0 := by exact_mod_cast hR₁.ne'
  have hu₂ : ((R₂ : ℂ)) ≠ 0 := by exact_mod_cast hR₂.ne'
  have hnorm : ∀ i j : ℕ, ‖((R₁ : ℂ)) ^ i * ((R₂ : ℂ)) ^ j‖ = R₁ ^ i * R₂ ^ j := by
    intro i j
    rw [norm_mul, norm_pow, norm_pow, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg hR₁.le, Real.norm_of_nonneg hR₂.le]
  have hpos : ∀ i j : ℕ, 0 < R₁ ^ i * R₂ ^ j := fun i j => by positivity
  set G' : ℝ := max S.G 0
  have hgr : ∀ (g : ℕ → ℕ → ℕ → ℂ) (s : ℕ),
      (∀ k < s, ∀ i j, ‖g k i j‖ ≤ S.G * R₁ ^ i * R₂ ^ j) →
      ∀ k < s, ∀ i j, ‖g k i j / ((R₁ : ℂ) ^ i * (R₂ : ℂ) ^ j)‖ ≤
        (fun _ : ℕ => G') (i + j) := by
    intro g s hg k hk i j
    rw [norm_div, hnorm, div_le_iff₀ (hpos i j)]
    calc ‖g k i j‖ ≤ S.G * R₁ ^ i * R₂ ^ j := hg k hk i j
      _ ≤ G' * (R₁ ^ i * R₂ ^ j) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) (hpos i j).le
  have hJ := jointSubexponential_of_separate (b := fun _ => G') S.hs₁ S.hs₂
    (fun _ => le_max_right _ _) (subexponential_const G') (hgr S.g₁ S.s₁ S.hg₁)
    (hgr S.g₂ S.s₂ S.hg₂) S.hB S.he₁ S.he₂ S.hκ S.hdom
    (diagonalFuchsian_rescale hu₁ hu₂ S.eq₁) (diagonalFuchsian_rescale hu₁ hu₂ S.eq₂)
  obtain ⟨K, hK⟩ := hJ a ha
  have hK0 : 0 ≤ K := by
    have := hK 0 0
    simp only [pow_zero, mul_one, div_one, add_zero] at this
    exact le_trans (norm_nonneg _) this
  refine ⟨K, hK0, fun i j => ?_⟩
  have h := hK i j
  rw [norm_div, hnorm, div_le_iff₀ (hpos i j)] at h
  calc ‖c i j‖ ≤ K * a ^ (i + j) * (R₁ ^ i * R₂ ^ j) := h
    _ = K * (a * R₁) ^ i * (a * R₂) ^ j := by rw [pow_add, mul_pow, mul_pow]; ring

/-- Integer linear eigenvalue forms grow at most linearly. -/
theorem growth_of_linear (lam : ℂ) (a b : ℤ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ i j : ℕ,
      ‖lam + ((a * i + b * j : ℤ) : ℂ)‖ ≤ B * (1 + ((i + j : ℕ) : ℝ)) := by
  refine ⟨‖lam‖ + |(a : ℝ)| + |(b : ℝ)| + 1, ?_, fun i j => ?_⟩
  · have := norm_nonneg lam; have := abs_nonneg (a : ℝ); have := abs_nonneg (b : ℝ)
    linarith
  refine le_trans (norm_add_le _ _) ?_
  rw [Complex.norm_intCast]
  push_cast
  have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have h1 : |(a : ℝ) * i + b * j| ≤ |(a : ℝ)| * i + |(b : ℝ)| * j := by
    refine le_trans (abs_add_le _ _) ?_
    rw [abs_mul, abs_mul, abs_of_nonneg hi, abs_of_nonneg hj]
  have hl := norm_nonneg lam
  have ha := abs_nonneg (a : ℝ)
  have hb := abs_nonneg (b : ℝ)
  nlinarith

/-- Two Euler operators with integer linear eigenvalue forms of nonzero determinant
jointly dominate the total degree. -/
theorem dominance_of_linear (lam mu : ℂ) (a₁ b₁ a₂ b₂ : ℤ) (hdet : a₁ * b₂ - a₂ * b₁ ≠ 0) :
    ∃ κ D : ℝ, 0 < κ ∧ ∀ m n : ℕ,
      κ * ((m + n : ℕ) : ℝ) ≤ ‖lam + ((a₁ * m + b₁ * n : ℤ) : ℂ)‖ + D ∨
      κ * ((m + n : ℕ) : ℝ) ≤ ‖mu + ((a₂ * m + b₂ * n : ℤ) : ℂ)‖ + D := by
  set M : ℝ := |(a₁ : ℝ)| + |(b₁ : ℝ)| + |(a₂ : ℝ)| + |(b₂ : ℝ)| + 1 with hM
  have hM1 : 1 ≤ M := by
    have := abs_nonneg (a₁ : ℝ); have := abs_nonneg (b₁ : ℝ)
    have := abs_nonneg (a₂ : ℝ); have := abs_nonneg (b₂ : ℝ)
    linarith
  refine ⟨1 / (2 * M), ‖lam‖ + ‖mu‖, by positivity, fun m n => ?_⟩
  set x₁ : ℝ := (a₁ : ℝ) * m + b₁ * n
  set x₂ : ℝ := (a₂ : ℝ) * m + b₂ * n
  set δ : ℝ := (a₁ : ℝ) * b₂ - a₂ * b₁
  have hδ : 1 ≤ |δ| := by
    have hz : (a₁ * b₂ - a₂ * b₁ : ℤ) ≠ 0 := hdet
    have : (1 : ℤ) ≤ |a₁ * b₂ - a₂ * b₁| := Int.one_le_abs hz
    have h' : (1 : ℝ) ≤ |((a₁ * b₂ - a₂ * b₁ : ℤ) : ℝ)| := by exact_mod_cast this
    simpa [δ] using h'
  have hm : δ * m = b₂ * x₁ - b₁ * x₂ := by simp only [δ, x₁, x₂]; ring
  have hn : δ * n = a₁ * x₂ - a₂ * x₁ := by simp only [δ, x₁, x₂]; ring
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  -- `m + n ≤ M (|x₁| + |x₂|)`
  have hmn : (m : ℝ) + n ≤ M * (|x₁| + |x₂|) := by
    have e1 : (m : ℝ) ≤ |δ * m| := by
      rw [abs_mul, abs_of_nonneg hm0]; nlinarith
    have e2 : (n : ℝ) ≤ |δ * n| := by
      rw [abs_mul, abs_of_nonneg hn0]; nlinarith
    have f1 : |δ * m| ≤ |(b₂ : ℝ)| * |x₁| + |(b₁ : ℝ)| * |x₂| := by
      rw [hm]; refine le_trans (abs_sub _ _) ?_; rw [abs_mul, abs_mul]
    have f2 : |δ * n| ≤ |(a₁ : ℝ)| * |x₂| + |(a₂ : ℝ)| * |x₁| := by
      rw [hn]; refine le_trans (abs_sub _ _) ?_; rw [abs_mul, abs_mul]
    have g1 := abs_nonneg x₁
    have g2 := abs_nonneg x₂
    have := abs_nonneg (a₁ : ℝ); have := abs_nonneg (b₁ : ℝ)
    have := abs_nonneg (a₂ : ℝ); have := abs_nonneg (b₂ : ℝ)
    nlinarith
  have hn1 : |x₁| - ‖lam‖ ≤ ‖lam + ((a₁ * m + b₁ * n : ℤ) : ℂ)‖ := by
    have h : ‖(((a₁ * m + b₁ * n : ℤ) : ℂ))‖ ≤ ‖lam + ((a₁ * m + b₁ * n : ℤ) : ℂ)‖ + ‖lam‖ := by
      calc _ = ‖(lam + ((a₁ * m + b₁ * n : ℤ) : ℂ)) - lam‖ := by ring_nf
        _ ≤ _ := norm_sub_le _ _
    rw [Complex.norm_intCast] at h
    simp only [x₁]
    push_cast at h ⊢
    linarith
  have hn2 : |x₂| - ‖mu‖ ≤ ‖mu + ((a₂ * m + b₂ * n : ℤ) : ℂ)‖ := by
    have h : ‖(((a₂ * m + b₂ * n : ℤ) : ℂ))‖ ≤ ‖mu + ((a₂ * m + b₂ * n : ℤ) : ℂ)‖ + ‖mu‖ := by
      calc _ = ‖(mu + ((a₂ * m + b₂ * n : ℤ) : ℂ)) - mu‖ := by ring_nf
        _ ≤ _ := norm_sub_le _ _
    rw [Complex.norm_intCast] at h
    simp only [x₂]
    push_cast at h ⊢
    linarith
  have hcast : ((m + n : ℕ) : ℝ) = (m : ℝ) + n := by push_cast; ring
  rw [hcast]
  have hM0 : 0 < M := by linarith
  have hkey : 1 / (2 * M) * ((m : ℝ) + n) ≤ (|x₁| + |x₂|) / 2 := by
    rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hl := norm_nonneg lam
  have hu := norm_nonneg mu
  by_cases h : |x₂| ≤ |x₁|
  · left; linarith
  · right; have h' := le_of_lt (not_le.mp h); linarith

/-- A local rescaling of a formal solution of two separate equations. -/
def LocalSeparateSolution (t : ℕ → ℕ → ℂ) : Prop :=
  ∃ (c : ℕ → ℕ → ℂ) (x y : ℂ) (R₁ R₂ : ℝ), 0 < R₁ ∧ 0 < R₂ ∧
    R₁ * ‖x‖ < 1 ∧ R₂ * ‖y‖ < 1 ∧ Nonempty (SeparateSystem c R₁ R₂) ∧
    ∀ m n, t m n = c m n * x ^ m * y ^ n

/-- **Separate local equations give the local joint growth used by the tensor-category
construction.** -/
theorem LocalSeparateSolution.localJointGrowth {t : ℕ → ℕ → ℂ}
    (ht : LocalSeparateSolution t) : LocalJointGrowth t := by
  obtain ⟨c, x, y, R₁, R₂, hR₁, hR₂, hx, hy, ⟨S⟩, ht⟩ := ht
  -- a margin `a > 1` with `a R₁ ‖x‖ < 1`, `a R₂ ‖y‖ < 1`
  set τ : ℝ := max (R₁ * ‖x‖) (R₂ * ‖y‖)
  have hτ0 : 0 ≤ τ := le_trans (by positivity) (le_max_left _ _)
  have hτ1 : τ < 1 := max_lt hx hy
  obtain ⟨σ, hτσ, hσ1⟩ := exists_between hτ1
  have hσ0 : 0 < σ := lt_of_le_of_lt hτ0 hτσ
  set a : ℝ := 1 / σ
  have ha : 1 < a := by rw [one_lt_div hσ0]; exact hσ1
  have haτ : a * τ < 1 := by
    rw [div_mul_eq_mul_div, one_mul, div_lt_one hσ0]; exact hτσ
  obtain ⟨K, hK0, hK⟩ := S.geometric_bound hR₁ hR₂ a ha
  have ha0 : 0 < a := by linarith
  set u₁ : ℝ := a * R₁
  set u₂ : ℝ := a * R₂
  have hu₁ : 0 < u₁ := by positivity
  have hu₂ : 0 < u₂ := by positivity
  have hu₁' : (u₁ : ℂ) ≠ 0 := by exact_mod_cast hu₁.ne'
  have hu₂' : (u₂ : ℂ) ≠ 0 := by exact_mod_cast hu₂.ne'
  refine ⟨fun i j => c i j / ((u₁ : ℂ) ^ i * (u₂ : ℂ) ^ j), (u₁ : ℂ) * x, (u₂ : ℂ) * y,
    ?_, ?_, ?_, ?_⟩
  · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hu₁.le]
    have : R₁ * ‖x‖ ≤ τ := le_max_left _ _
    calc u₁ * ‖x‖ = a * (R₁ * ‖x‖) := by ring
      _ ≤ a * τ := mul_le_mul_of_nonneg_left this ha0.le
      _ < 1 := haτ
  · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hu₂.le]
    have : R₂ * ‖y‖ ≤ τ := le_max_right _ _
    calc u₂ * ‖y‖ = a * (R₂ * ‖y‖) := by ring
      _ ≤ a * τ := mul_le_mul_of_nonneg_left this ha0.le
      _ < 1 := haτ
  · intro R hR
    refine ⟨K, fun m n => ?_⟩
    have hpos : 0 < u₁ ^ m * u₂ ^ n := by positivity
    rw [norm_div, norm_mul, norm_pow, norm_pow, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg hu₁.le, Real.norm_of_nonneg hu₂.le, div_le_iff₀ hpos]
    calc ‖c m n‖ ≤ K * u₁ ^ m * u₂ ^ n := hK m n
      _ = K * 1 * (u₁ ^ m * u₂ ^ n) := by ring
      _ ≤ K * R ^ (m + n) * (u₁ ^ m * u₂ ^ n) := by
        gcongr
        exact one_le_pow₀ hR.le
  · intro m n
    rw [ht m n, mul_pow, mul_pow]
    field_simp

end VOA.Huang.UniformConv
