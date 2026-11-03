import VOA.Huang.UniformConvGeometric

/-!
# One regular equation plus row bounds gives a joint geometric bound

Huang's regularity theorem for products of `n` intertwining operators (math/0206206,
Thm 2.5) is stated for singular divisors given by ONE equation (`zᵢ = 0`, `zᵢ = ∞`,
`zᵢ = zⱼ`); his convergence proof (Thm 3.5) uses the equation in the innermost variable
with coefficients analytic in the remaining variables, plus convergence of the
coefficients of the innermost expansion (fewer intertwiners). This file is the
coefficient-array form of that argument.

* `boundedArray_of_rowFuchsian` — if the array `c` satisfies a monic Euler-type equation
  in the SECOND index only (`DiagonalFuchsian (fun _ n => μ + n)`), with coefficients
  `≤ G t₁^i t₂^j` (`t₁, t₂ < 1`), and every row `m ↦ c m n` is bounded, then `c` is
  bounded. At large `n` the indicial factor `~ nˢ` beats the right side `~ nˢ⁻¹`; the
  finitely many remaining rows are bounded by hypothesis. No equation in the first index
  is used.
* `geometric_of_rowFuchsian` — the rescaled form: polydisc coefficient bounds
  `G R₁^i R₂^j` and rows of rate `ρ₁ > R₁` give `‖c m n‖ ≤ K ρ₁^m ρ₂^n` for every
  `ρ₂ > R₂`.
* `localJointGrowth_iff_geometric`, `LocalJointGrowth.add`, `LocalJointGrowth.sum`,
  `LocalJointGrowth.transpose` — the consumer predicate in geometric form.
-/

noncomputable section
namespace VOA.Huang.FivePointSep
open VOA Filter VOA.Huang.HuangODEThree VOA.Huang.UniformConv
open scoped BigOperators

theorem geometric_reverse_le {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t < 1) (m : ℕ) :
    ∑ i ∈ Finset.range (m + 1), t ^ (m - i) ≤ (1 - t)⁻¹ := by
  have he : (∑ i ∈ Finset.range (m + 1), t ^ (m - i)) =
      ∑ i ∈ Finset.range (m + 1), t ^ i := by
    simpa using (Finset.sum_range_reflect (fun i => t ^ i) (m + 1))
  rw [he, ← tsum_geometric_of_lt_one ht₀ ht₁]
  exact (summable_geometric_of_lt_one ht₀ ht₁).sum_le_tsum _ (fun _ _ => pow_nonneg ht₀ _)

/-- The double geometric box sum. -/
theorem geometric_box_le {t₁ t₂ : ℝ} (h₁₀ : 0 ≤ t₁) (h₁₁ : t₁ < 1) (h₂₀ : 0 ≤ t₂)
    (h₂₁ : t₂ < 1) (m n : ℕ) :
    ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1), t₁ ^ (m - i) * t₂ ^ (n - j) ≤
      (1 - t₁)⁻¹ * (1 - t₂)⁻¹ := by
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]
  exact mul_le_mul (geometric_reverse_le h₁₀ h₁₁ m) (geometric_reverse_le h₂₀ h₂₁ n)
    (Finset.sum_nonneg fun _ _ => pow_nonneg h₂₀ _) (inv_nonneg.mpr (by linarith))

/-- Finitely many row bounds have a common bound. -/
theorem exists_common_row_bound {c : ℕ → ℕ → ℂ}
    (hrow : ∀ n, ∃ K : ℝ, ∀ m, ‖c m n‖ ≤ K) (N : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n < N, ∀ m, ‖c m n‖ ≤ K := by
  induction N with
  | zero => exact ⟨0, le_rfl, fun n hn => absurd hn (Nat.not_lt_zero _)⟩
  | succ N ih =>
    obtain ⟨K, hK0, hK⟩ := ih
    obtain ⟨K', hK'⟩ := hrow N
    refine ⟨max K K', le_trans hK0 (le_max_left _ _), fun n hn m => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hn with h | rfl
    · exact le_trans (hK n h m) (le_max_left _ _)
    · exact le_trans (hK' m) (le_max_right _ _)

/-- Large eigenvalues: `|μ+n| ≥ max 1 C` and `|μ| + n ≤ 2|μ+n|` for `n ≫ 0`. -/
theorem exists_large_index (μ : ℂ) (C : ℝ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      1 ≤ ‖μ + (n : ℂ)‖ ∧ C ≤ ‖μ + (n : ℂ)‖ ∧ ‖μ‖ + n ≤ 2 * ‖μ + (n : ℂ)‖ := by
  obtain ⟨N, hN⟩ := exists_nat_ge (3 * ‖μ‖ + |C| + 1)
  refine ⟨N, fun n hn => ?_⟩
  have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
  have htri : (n : ℝ) - ‖μ‖ ≤ ‖μ + (n : ℂ)‖ := by
    have h := norm_sub_norm_le ((n : ℂ)) (-μ)
    have e1 : ‖(n : ℂ)‖ = n := by simp
    have e2 : ‖-μ‖ = ‖μ‖ := norm_neg μ
    have e3 : (n : ℂ) - -μ = μ + n := by ring
    rw [e1, e2, e3] at h
    exact h
  have hμ := norm_nonneg μ
  have hC := le_abs_self C
  have hCa := abs_nonneg C
  refine ⟨by linarith, by linarith, by linarith⟩

/-- **One regular equation in the second index plus bounded rows give a bounded
array.** The equation's coefficients decay geometrically in both indices. -/
theorem boundedArray_of_rowFuchsian {c : ℕ → ℕ → ℂ} {μ : ℂ} {s : ℕ}
    {g : ℕ → ℕ → ℕ → ℂ} {G t₁ t₂ : ℝ} (hs : 1 ≤ s) (hG : 0 ≤ G)
    (ht₁₀ : 0 ≤ t₁) (ht₁₁ : t₁ < 1) (ht₂₀ : 0 ≤ t₂) (ht₂₁ : t₂ < 1)
    (hg : ∀ k < s, ∀ i j, ‖g k i j‖ ≤ G * t₁ ^ i * t₂ ^ j)
    (heq : DiagonalFuchsian (fun _ n => μ + n) s g c)
    (hrow : ∀ n, ∃ K : ℝ, ∀ m, ‖c m n‖ ≤ K) :
    ∃ K : ℝ, ∀ m n, ‖c m n‖ ≤ K := by
  set S : ℝ := (1 - t₁)⁻¹ * (1 - t₂)⁻¹ with hSdef
  have hS0 : 0 ≤ S := mul_nonneg (inv_nonneg.mpr (by linarith)) (inv_nonneg.mpr (by linarith))
  -- `C` absorbs all constants
  set C : ℝ := 2 * (s : ℝ) * G + 2 ^ (s + 1) * (s : ℝ) * G * S + 1 with hCdef
  obtain ⟨N, hN⟩ := exists_large_index μ C
  obtain ⟨K, hK0, hK⟩ := exists_common_row_bound hrow N
  refine ⟨K, ?_⟩
  -- strong induction on `n`, then on `m`
  intro m n
  induction n using Nat.strong_induction_on generalizing m with
  | _ n IHn =>
  induction m using Nat.strong_induction_on with
  | _ m IHm =>
  by_cases hnN : n < N
  · exact hK n hnN m
  replace hnN := not_lt.mp hnN
  obtain ⟨hE1, hEC, hET⟩ := hN n hnN
  set E : ℂ := μ + (n : ℂ) with hEdef
  set T : ℝ := ‖μ‖ + n with hTdef
  have hT1 : 1 ≤ T := by
    have : 1 ≤ ‖E‖ := hE1
    have h2 : ‖E‖ ≤ ‖μ‖ + n := by
      rw [hEdef]; refine le_trans (norm_add_le _ _) ?_; simp
    linarith
  -- lower bound of the indicial factor
  have hP := half_pow_le_norm_indicial hs (g := fun k => g k 0 0) (G := G)
    (fun k hk => by simpa using hg k hk 0 0) hE1 (by
      have : 2 * (s : ℝ) * G ≤ C := by
        have : 0 ≤ 2 ^ (s + 1) * (s : ℝ) * G * S := by positivity
        linarith
      linarith)
  -- upper bound of the right-hand side
  have hrhs : ‖(E ^ s - ∑ k ∈ Finset.range s, g k 0 0 * E ^ k) * c m n‖ ≤
      (s : ℝ) * G * T ^ (s - 1) * S * K := by
    have h := heq m n
    simp only at h
    rw [h]
    have hterm : ∀ i ∈ Finset.range (m + 1), ∀ j ∈ Finset.range (n + 1),
        ‖if i + j < m + n then
            ∑ k ∈ Finset.range s, g k (m - i) (n - j) * (μ + (j : ℂ)) ^ k * c i j
          else 0‖ ≤ (s : ℝ) * G * T ^ (s - 1) * K * (t₁ ^ (m - i) * t₂ ^ (n - j)) := by
      intro i hi j hj
      have him : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      split_ifs with hij
      · have hcij : ‖c i j‖ ≤ K := by
          rcases lt_or_eq_of_le hjn with hlt | rfl
          · exact IHn j hlt i
          · exact IHm i (by omega)
        have hej : ‖μ + (j : ℂ)‖ ≤ T := by
          refine le_trans (norm_add_le _ _) ?_
          have : (j : ℝ) ≤ n := by exact_mod_cast hjn
          simpa [hTdef] using this
        refine le_trans (norm_sum_le _ _) ?_
        have hk : ∀ k ∈ Finset.range s, ‖g k (m - i) (n - j) * (μ + (j : ℂ)) ^ k * c i j‖ ≤
            G * T ^ (s - 1) * K * (t₁ ^ (m - i) * t₂ ^ (n - j)) := by
          intro k hk
          have hk' := Finset.mem_range.mp hk
          rw [norm_mul, norm_mul, norm_pow]
          have h1 := hg k hk' (m - i) (n - j)
          have h2 : ‖μ + (j : ℂ)‖ ^ k ≤ T ^ (s - 1) :=
            le_trans (pow_le_pow_left₀ (norm_nonneg _) hej k)
              (pow_le_pow_right₀ hT1 (by omega))
          have hpos : 0 ≤ t₁ ^ (m - i) * t₂ ^ (n - j) := by positivity
          calc ‖g k (m - i) (n - j)‖ * ‖μ + (j : ℂ)‖ ^ k * ‖c i j‖
              ≤ (G * t₁ ^ (m - i) * t₂ ^ (n - j)) * T ^ (s - 1) * K := by
                gcongr
              _ = _ := by ring
        refine le_trans (Finset.sum_le_sum hk) (le_of_eq ?_)
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring
      · simp only [norm_zero]
        have : 0 ≤ T ^ (s - 1) := by positivity
        positivity
    refine le_trans (norm_sum_le _ _) ?_
    refine le_trans (Finset.sum_le_sum fun i hi => le_trans (norm_sum_le _ _)
      (Finset.sum_le_sum fun j hj => hterm i hi j hj)) ?_
    have hbox := geometric_box_le ht₁₀ ht₁₁ ht₂₀ ht₂₁ m n
    have hc0 : 0 ≤ (s : ℝ) * G * T ^ (s - 1) * K := by
      have : 0 ≤ T ^ (s - 1) := by positivity
      positivity
    have hfac : ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1),
        (s : ℝ) * G * T ^ (s - 1) * K * (t₁ ^ (m - i) * t₂ ^ (n - j)) =
        (s : ℝ) * G * T ^ (s - 1) * K * ∑ i ∈ Finset.range (m + 1),
          ∑ j ∈ Finset.range (n + 1), t₁ ^ (m - i) * t₂ ^ (n - j) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]
    rw [hfac]
    calc (s : ℝ) * G * T ^ (s - 1) * K * ∑ i ∈ Finset.range (m + 1),
          ∑ j ∈ Finset.range (n + 1), t₁ ^ (m - i) * t₂ ^ (n - j)
        ≤ (s : ℝ) * G * T ^ (s - 1) * K * S := mul_le_mul_of_nonneg_left hbox hc0
      _ = _ := by ring
  rw [norm_mul] at hrhs
  -- combine: `‖E‖^s/2 ‖c‖ ≤ s G T^(s-1) S K ≤ ‖E‖^s/2 K`
  have hEs : 0 < ‖E‖ ^ s := by
    have : 0 < ‖E‖ := by linarith
    positivity
  have hTE : T ^ (s - 1) ≤ 2 ^ (s - 1) * ‖E‖ ^ (s - 1) := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by linarith) hET _
  have hkey : (s : ℝ) * G * T ^ (s - 1) * S * K ≤ ‖E‖ ^ s / 2 * K := by
    have hEsplit : ‖E‖ ^ s = ‖E‖ * ‖E‖ ^ (s - 1) := by
      rw [← pow_succ']; congr 1; omega
    have hCE : 2 ^ (s + 1) * (s : ℝ) * G * S ≤ ‖E‖ := by
      have : 0 ≤ 2 * (s : ℝ) * G := by positivity
      linarith
    have hpow : (2 : ℝ) ^ (s + 1) = 2 * 2 * 2 ^ (s - 1) := by
      rw [show s + 1 = (s - 1) + 2 by omega, pow_add]; ring
    have hE0 : 0 ≤ ‖E‖ ^ (s - 1) := by positivity
    have h2 : (0 : ℝ) ≤ 2 ^ (s - 1) := by positivity
    calc (s : ℝ) * G * T ^ (s - 1) * S * K
        ≤ (s : ℝ) * G * (2 ^ (s - 1) * ‖E‖ ^ (s - 1)) * S * K := by gcongr
      _ = (2 ^ (s - 1) * (s : ℝ) * G * S) * ‖E‖ ^ (s - 1) * K := by ring
      _ ≤ (‖E‖ / 4) * ‖E‖ ^ (s - 1) * K := by
        gcongr
        rw [hpow] at hCE
        linarith
      _ ≤ ‖E‖ ^ s / 2 * K := by
        rw [hEsplit]
        have : 0 ≤ ‖E‖ * ‖E‖ ^ (s - 1) * K := by
          have : 0 ≤ ‖E‖ := norm_nonneg _
          positivity
        nlinarith
  have hfin : ‖E‖ ^ s / 2 * ‖c m n‖ ≤ ‖E‖ ^ s / 2 * K :=
    le_trans (mul_le_mul_of_nonneg_right hP (norm_nonneg _)) (le_trans hrhs hkey)
  exact le_of_mul_le_mul_left hfin (by positivity)

/-- **Geometric joint bound from one equation in the second index and row bounds.**
Coefficients holomorphic on the polydisc of radii `1/R₁`, `1/R₂`; each row grows at most
like `ρ₁^m` with `ρ₁ > R₁`. Then every `ρ₂ > R₂` is a joint rate. -/
theorem geometric_of_rowFuchsian {c : ℕ → ℕ → ℂ} {μ : ℂ} {s : ℕ}
    {g : ℕ → ℕ → ℕ → ℂ} {G R₁ R₂ ρ₁ ρ₂ : ℝ} (hs : 1 ≤ s)
    (hR₁ : 0 ≤ R₁) (hR₂ : 0 ≤ R₂) (h₁ : R₁ < ρ₁) (h₂ : R₂ < ρ₂)
    (hg : ∀ k < s, ∀ i j, ‖g k i j‖ ≤ G * R₁ ^ i * R₂ ^ j)
    (heq : DiagonalFuchsian (fun _ n => μ + n) s g c)
    (hrow : ∀ n, ∃ K : ℝ, ∀ m, ‖c m n‖ ≤ K * ρ₁ ^ m) :
    ∃ K : ℝ, ∀ m n, ‖c m n‖ ≤ K * ρ₁ ^ m * ρ₂ ^ n := by
  have hρ₁ : 0 < ρ₁ := lt_of_le_of_lt hR₁ h₁
  have hρ₂ : 0 < ρ₂ := lt_of_le_of_lt hR₂ h₂
  have hu₁ : ((ρ₁ : ℂ)) ≠ 0 := by exact_mod_cast hρ₁.ne'
  have hu₂ : ((ρ₂ : ℂ)) ≠ 0 := by exact_mod_cast hρ₂.ne'
  have hnorm : ∀ i j : ℕ, ‖((ρ₁ : ℂ)) ^ i * ((ρ₂ : ℂ)) ^ j‖ = ρ₁ ^ i * ρ₂ ^ j := by
    intro i j
    rw [norm_mul, norm_pow, norm_pow, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg hρ₁.le, Real.norm_of_nonneg hρ₂.le]
  have hpos : ∀ i j : ℕ, 0 < ρ₁ ^ i * ρ₂ ^ j := fun i j => by positivity
  have heq' := diagonalFuchsian_rescale hu₁ hu₂ heq
  set G' := max G 0
  have hg' : ∀ k < s, ∀ i j, ‖g k i j / ((ρ₁ : ℂ) ^ i * (ρ₂ : ℂ) ^ j)‖ ≤
      G' * (R₁ / ρ₁) ^ i * (R₂ / ρ₂) ^ j := by
    intro k hk i j
    rw [norm_div, hnorm, div_le_iff₀ (hpos i j), div_pow, div_pow]
    have := hg k hk i j
    have hG : G ≤ G' := le_max_left _ _
    have e : G' * (R₁ ^ i / ρ₁ ^ i) * (R₂ ^ j / ρ₂ ^ j) * (ρ₁ ^ i * ρ₂ ^ j) =
        G' * R₁ ^ i * R₂ ^ j := by
      field_simp
    rw [e]
    calc ‖g k i j‖ ≤ G * R₁ ^ i * R₂ ^ j := this
      _ ≤ G' * R₁ ^ i * R₂ ^ j := by gcongr
  have hrow' : ∀ n, ∃ K : ℝ, ∀ m,
      ‖c m n / ((ρ₁ : ℂ) ^ m * (ρ₂ : ℂ) ^ n)‖ ≤ K := by
    intro n
    obtain ⟨K, hK⟩ := hrow n
    refine ⟨K / ρ₂ ^ n, fun m => ?_⟩
    rw [norm_div, hnorm, div_le_div_iff₀ (hpos m n) (by positivity)]
    calc ‖c m n‖ * ρ₂ ^ n ≤ K * ρ₁ ^ m * ρ₂ ^ n := by
          gcongr
          exact hK m
      _ = K * (ρ₁ ^ m * ρ₂ ^ n) := by ring
  obtain ⟨K, hK⟩ := boundedArray_of_rowFuchsian hs (le_max_right G 0)
    (div_nonneg hR₁ hρ₁.le) ((div_lt_one hρ₁).mpr h₁)
    (div_nonneg hR₂ hρ₂.le) ((div_lt_one hρ₂).mpr h₂) hg' heq' hrow'
  refine ⟨K, fun m n => ?_⟩
  have h := hK m n
  rw [norm_div, hnorm, div_le_iff₀ (hpos m n)] at h
  calc ‖c m n‖ ≤ K * (ρ₁ ^ m * ρ₂ ^ n) := h
    _ = K * ρ₁ ^ m * ρ₂ ^ n := by ring

/-! ## The consumer predicate in geometric form -/

/-- `LocalJointGrowth` is exactly a geometric bound with both rates below one. -/
theorem localJointGrowth_of_geometric {t : ℕ → ℕ → ℂ} {K a b : ℝ} (ha₀ : 0 ≤ a)
    (ha : a < 1) (hb₀ : 0 ≤ b) (hb : b < 1)
    (h : ∀ m n, ‖t m n‖ ≤ K * a ^ m * b ^ n) : LocalJointGrowth t := by
  set x : ℝ := (1 + a) / 2
  set y : ℝ := (1 + b) / 2
  have hx0 : 0 < x := by positivity
  have hy0 : 0 < y := by positivity
  have hx1 : x < 1 := by simp only [x]; linarith
  have hy1 : y < 1 := by simp only [y]; linarith
  have hax : a ≤ x := by simp only [x]; linarith
  have hby : b ≤ y := by simp only [y]; linarith
  have hxc : ((x : ℂ)) ≠ 0 := by exact_mod_cast hx0.ne'
  have hyc : ((y : ℂ)) ≠ 0 := by exact_mod_cast hy0.ne'
  have hK0 : 0 ≤ K := by
    have := h 0 0
    simp only [pow_zero, mul_one] at this
    exact le_trans (norm_nonneg _) this
  refine ⟨fun m n => t m n / ((x : ℂ) ^ m * (y : ℂ) ^ n), x, y, ?_, ?_, ?_, ?_⟩
  · rw [Complex.norm_real, Real.norm_of_nonneg hx0.le]; exact hx1
  · rw [Complex.norm_real, Real.norm_of_nonneg hy0.le]; exact hy1
  · intro R hR
    refine ⟨K, fun m n => ?_⟩
    have hpos : 0 < x ^ m * y ^ n := by positivity
    rw [norm_div, norm_mul, norm_pow, norm_pow, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg hx0.le, Real.norm_of_nonneg hy0.le, div_le_iff₀ hpos]
    calc ‖t m n‖ ≤ K * a ^ m * b ^ n := h m n
      _ ≤ K * x ^ m * y ^ n := by gcongr
      _ = K * 1 * (x ^ m * y ^ n) := by ring
      _ ≤ K * R ^ (m + n) * (x ^ m * y ^ n) := by
        gcongr
        exact one_le_pow₀ hR.le
  · intro m n
    field_simp

theorem geometric_of_localJointGrowth {t : ℕ → ℕ → ℂ} (ht : LocalJointGrowth t) :
    ∃ K a b : ℝ, 0 ≤ a ∧ a < 1 ∧ 0 ≤ b ∧ b < 1 ∧
      ∀ m n, ‖t m n‖ ≤ K * a ^ m * b ^ n := by
  obtain ⟨c, x, y, hx, hy, hc, ht⟩ := ht
  set τ : ℝ := max ‖x‖ ‖y‖
  have hτ1 : τ < 1 := max_lt hx hy
  have hτ0 : 0 ≤ τ := le_trans (norm_nonneg _) (le_max_left _ _)
  obtain ⟨R, hR1, hRτ⟩ : ∃ R : ℝ, 1 < R ∧ R * τ < 1 := by
    refine ⟨2 / (1 + τ), ?_, ?_⟩
    · rw [lt_div_iff₀ (by linarith)]; linarith
    · rw [div_mul_eq_mul_div, div_lt_one (by linarith)]; linarith
  obtain ⟨K, hK⟩ := hc R hR1
  have hR0 : 0 < R := by linarith
  refine ⟨K, R * ‖x‖, R * ‖y‖, by positivity,
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left (le_max_left _ _) hR0.le) hRτ,
    by positivity,
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left (le_max_right _ _) hR0.le) hRτ, fun m n => ?_⟩
  rw [ht m n, norm_mul, norm_mul, norm_pow, norm_pow]
  calc ‖c m n‖ * ‖x‖ ^ m * ‖y‖ ^ n ≤ K * R ^ (m + n) * ‖x‖ ^ m * ‖y‖ ^ n := by
        gcongr
        exact hK m n
    _ = K * (R * ‖x‖) ^ m * (R * ‖y‖) ^ n := by rw [pow_add, mul_pow, mul_pow]; ring

theorem localJointGrowth_iff_geometric (t : ℕ → ℕ → ℂ) :
    LocalJointGrowth t ↔ ∃ K a b : ℝ, 0 ≤ a ∧ a < 1 ∧ 0 ≤ b ∧ b < 1 ∧
      ∀ m n, ‖t m n‖ ≤ K * a ^ m * b ^ n := by
  constructor
  · exact geometric_of_localJointGrowth
  · rintro ⟨K, a, b, ha₀, ha, hb₀, hb, h⟩
    exact localJointGrowth_of_geometric ha₀ ha hb₀ hb h

theorem LocalJointGrowth.zero : LocalJointGrowth (fun _ _ => 0) :=
  localJointGrowth_of_geometric (K := 0) (a := 0) (b := 0) le_rfl one_pos le_rfl one_pos
    (fun m n => by simp)

theorem LocalJointGrowth.add {t t' : ℕ → ℕ → ℂ} (ht : LocalJointGrowth t)
    (ht' : LocalJointGrowth t') : LocalJointGrowth (fun m n => t m n + t' m n) := by
  obtain ⟨K, a, b, ha₀, ha, hb₀, hb, h⟩ := geometric_of_localJointGrowth ht
  obtain ⟨K', a', b', ha₀', ha', hb₀', hb', h'⟩ := geometric_of_localJointGrowth ht'
  have hK : 0 ≤ K := by
    have := h 0 0; simp only [pow_zero, mul_one] at this; exact le_trans (norm_nonneg _) this
  have hK' : 0 ≤ K' := by
    have := h' 0 0; simp only [pow_zero, mul_one] at this; exact le_trans (norm_nonneg _) this
  refine localJointGrowth_of_geometric (K := K + K') (a := max a a') (b := max b b')
    (le_trans ha₀ (le_max_left _ _)) (max_lt ha ha') (le_trans hb₀ (le_max_left _ _))
    (max_lt hb hb') fun m n => ?_
  refine le_trans (norm_add_le _ _) ?_
  have e1 : K * a ^ m * b ^ n ≤ K * max a a' ^ m * max b b' ^ n := by
    gcongr <;> simp
  have e2 : K' * a' ^ m * b' ^ n ≤ K' * max a a' ^ m * max b b' ^ n := by
    gcongr <;> simp
  linarith [h m n, h' m n]

theorem LocalJointGrowth.smul {t : ℕ → ℕ → ℂ} (ht : LocalJointGrowth t) (z : ℂ) :
    LocalJointGrowth (fun m n => z * t m n) := by
  obtain ⟨K, a, b, ha₀, ha, hb₀, hb, h⟩ := geometric_of_localJointGrowth ht
  refine localJointGrowth_of_geometric (K := ‖z‖ * K) ha₀ ha hb₀ hb fun m n => ?_
  rw [norm_mul, mul_assoc, mul_assoc]
  exact mul_le_mul_of_nonneg_left (by simpa [mul_assoc] using h m n) (norm_nonneg _)

theorem LocalJointGrowth.sum {ι : Type*} (S : Finset ι) {t : ι → ℕ → ℕ → ℂ}
    (ht : ∀ i ∈ S, LocalJointGrowth (t i)) :
    LocalJointGrowth (fun m n => ∑ i ∈ S, t i m n) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using LocalJointGrowth.zero
  | insert a S ha IH =>
    simp only [Finset.sum_insert ha]
    exact LocalJointGrowth.add (ht a (Finset.mem_insert_self _ _))
      (IH fun i hi => ht i (Finset.mem_insert_of_mem hi))

theorem LocalJointGrowth.transpose {t : ℕ → ℕ → ℂ} (ht : LocalJointGrowth t) :
    LocalJointGrowth (fun m n => t n m) := by
  obtain ⟨K, a, b, ha₀, ha, hb₀, hb, h⟩ := geometric_of_localJointGrowth ht
  exact localJointGrowth_of_geometric hb₀ hb ha₀ ha fun m n => by
    have := h n m; linarith [mul_right_comm K (a ^ n) (b ^ m)]

theorem LocalJointGrowth.congr {t t' : ℕ → ℕ → ℂ} (ht : LocalJointGrowth t)
    (h : ∀ m n, t' m n = t m n) : LocalJointGrowth t' := by
  have : t' = t := funext fun m => funext fun n => h m n
  rwa [this]

end VOA.Huang.FivePointSep
