import VOA.Huang.GenusOneG1bTransport

/-!
# Geometric bounds on the transported kernels

If the rational kernels `Cf f g ∈ ℂ⟦u⟧⟦t⟧` have coefficients `O(μ^{p+k})` (true for every
`μ > 1` by `Sub2` membership) and their rows times `(1−t)^E` are polynomials of degree
`≤ c p + d`, then the transported kernels `kerOf Pol E c d a f g p` have weighted `ℓ¹` norm
`≤ A (μ^{3c+3})^p` at radius `r = 1 − μ⁻¹` (`kerOf_normLe`). As `μ → 1` the rate
`μ^{3c+3} → 1`, while the spatial radius `r` shrinks — exactly the trade-off allowed by
`IterateModeGrowth` (the `k`-rate may depend on the `q`-rate).
-/
noncomputable section
namespace VOA.Huang.GenusOneG1b
open VOA
open scoped BigOperators
open VOA.Huang.GenusOneWard (pc coeff_pc omt c2 R2)

theorem one_add_one_sub_inv_le {μ : ℝ} (hμ : 1 < μ) : 1 + (1 - μ⁻¹) ≤ μ := by
  have hμ0 : 0 < μ := by linarith
  have : μ⁻¹ * μ = 1 := inv_mul_cancel₀ hμ0.ne'
  nlinarith [sq_nonneg (μ - 1), inv_pos.mpr hμ0]

theorem one_sub_one_sub_inv {μ : ℝ} (hμ : 1 < μ) : (1 - (1 - μ⁻¹))⁻¹ = μ := by
  rw [sub_sub_cancel, inv_inv]

/-- A polynomial in `p` is `O(μ^p)` for every `μ > 1`. -/
theorem exists_linear_le_pow (c d : ℕ) {μ : ℝ} (hμ : 1 < μ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : ℕ, ((c * p + d + 1 : ℕ) : ℝ) ≤ C * μ ^ p := by
  have hs : Subexponential (fun p : ℕ => (c : ℝ) * (p : ℝ) ^ 1 + (d + 1 : ℝ)) :=
    ((subexponential_pow 1).const_mul (by positivity)).add (subexponential_const _)
  obtain ⟨C, hC⟩ := hs μ hμ
  have hC0 : 0 ≤ C := by
    have := hC 0
    simp only [pow_zero, mul_one, Nat.cast_zero, zero_pow one_ne_zero, mul_zero, zero_add]
      at this
    linarith
  refine ⟨C, hC0, fun p => ?_⟩
  have := hC p
  push_cast
  simpa [pow_one, add_assoc] using this

theorem sum_coeff_le {P : Polynomial ℂ} {E : ℕ} {F : PowerSeries ℂ} {μ D : ℝ} (hμ : 1 < μ)
    (hP : omt ^ E * F = pc P) (p : ℕ)
    (hF : ∀ k, ‖PowerSeries.coeff k F‖ ≤ D * μ ^ (p + k)) :
    ∑ i ∈ Finset.range (P.natDegree + 1), ‖P.coeff i‖ ≤
      (P.natDegree + 1 : ℕ) * (2 ^ E * D * μ ^ (p + P.natDegree)) := by
  have hμ0 : 0 < μ := by linarith
  have hw0 : 0 < μ⁻¹ := inv_pos.mpr hμ0
  have hw1 : μ⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hμ.le
  have hFw : ∀ k, ‖PowerSeries.coeff k F‖ * μ⁻¹ ^ k ≤ D * μ ^ p := by
    intro k
    have hk : 0 < μ ^ k := pow_pos hμ0 k
    calc ‖PowerSeries.coeff k F‖ * μ⁻¹ ^ k ≤ D * μ ^ (p + k) * μ⁻¹ ^ k :=
          mul_le_mul_of_nonneg_right (hF k) (by positivity)
      _ = D * μ ^ p := by rw [pow_add, inv_pow]; field_simp
  have hi : ∀ i, ‖P.coeff i‖ ≤ 2 ^ E * D * μ ^ (p + i) := by
    intro i
    have h := coeff_numerator_le hw0 hw1 hP hFw i
    have hk : 0 < μ ^ i := pow_pos hμ0 i
    rw [inv_pow] at h
    have h' : ‖P.coeff i‖ ≤ 2 ^ E * (D * μ ^ p) * μ ^ i := by
      rwa [← div_eq_mul_inv, div_le_iff₀ hk] at h
    rw [pow_add]; linarith [h']
  calc ∑ i ∈ Finset.range (P.natDegree + 1), ‖P.coeff i‖
      ≤ ∑ _i ∈ Finset.range (P.natDegree + 1), 2 ^ E * D * μ ^ (p + P.natDegree) := by
        refine Finset.sum_le_sum fun i hi' => (hi i).trans ?_
        rw [Finset.mem_range] at hi'
        have hD : 0 ≤ D := by
          have := (norm_nonneg (PowerSeries.coeff 0 F)).trans (hF 0)
          exact nonneg_of_mul_nonneg_left this (pow_pos hμ0 _)
        exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hμ.le (by omega)) (by positivity)
    _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

section
variable {κ : Type*} [Fintype κ]

/-- **Geometric bound on the transported kernels.** -/
theorem kerOf_normLe {Pol : κ → κ → ℕ → Polynomial ℂ} {E c d : ℕ} (a : κ → ℕ)
    {Cf : κ → κ → R2} (hdeg : ∀ f g p, (Pol f g p).natDegree ≤ c * p + d)
    (hnum : ∀ f g p, omt ^ E * PowerSeries.coeff p (Cf f g) = pc (Pol f g p))
    {μ D : ℝ} (hμ : 1 < μ) (hD0 : 0 ≤ D)
    (hD : ∀ f g p k, ‖c2 (Cf f g) p k‖ ≤ D * μ ^ (p + k)) :
    ∃ A : ℝ, ∀ f g p, NormLe (1 - μ⁻¹) (kerOf Pol E c d a f g p) (A * (μ ^ (3 * c + 3)) ^ p) := by
  have hμ0 : 0 < μ := by linarith
  have hμ1 : 1 ≤ μ := hμ.le
  set r := 1 - μ⁻¹ with hr
  have hr0 : 0 ≤ r := by rw [hr]; linarith [inv_le_one_of_one_le₀ hμ1]
  have hr1 : r < 1 := by rw [hr]; linarith [inv_pos.mpr hμ0]
  have h1r : 1 + r ≤ μ := one_add_one_sub_inv_le hμ
  have hinv : (1 - r)⁻¹ = μ := one_sub_one_sub_inv hμ
  obtain ⟨C', hC'0, hC'⟩ := exists_linear_le_pow c d hμ
  set At := aTot a with hAt
  refine ⟨C' * (2 ^ E * D) * μ ^ (E + 3 * d + 3 * At), fun f g p => ?_⟩
  refine (normLe_transKer (Pol f g p) (degOf E c d a f g p) (negOf c d a p) hr0 hr1).mono ?_
  rw [hinv]
  have hdeg' := hdeg f g p
  have hsum := sum_coeff_le hμ (hnum f g p) p (fun k => hD f g p k)
  -- bound the coefficient sum
  have hs1 : ∑ i ∈ Finset.range ((Pol f g p).natDegree + 1), ‖(Pol f g p).coeff i‖ ≤
      (C' * μ ^ p) * (2 ^ E * D * μ ^ (p + (c * p + d))) := by
    refine hsum.trans ?_
    have hn : ((Pol f g p).natDegree + 1 : ℕ) ≤ ((c * p + d + 1 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : (Pol f g p).natDegree + 1 ≤ c * p + d + 1)
    have hpow : μ ^ (p + (Pol f g p).natDegree) ≤ μ ^ (p + (c * p + d)) :=
      pow_le_pow_right₀ hμ1 (by omega)
    exact mul_le_mul (hn.trans (hC' p)) (mul_le_mul_of_nonneg_left hpow (by positivity))
      (by positivity) (by positivity)
  have hm : (1 + r) ^ degOf E c d a f g p ≤ μ ^ (E + (c * p + d + At) + p + At) := by
    refine (pow_le_pow_left₀ (by linarith) h1r _).trans (pow_le_pow_right₀ hμ1 ?_)
    have hag := le_aTot a g
    simp only [degOf, negOf, ← hAt]
    omega
  rw [show negOf c d a p = c * p + d + At from rfl]
  have hS0 : 0 ≤ ∑ i ∈ Finset.range ((Pol f g p).natDegree + 1), ‖(Pol f g p).coeff i‖ :=
    Finset.sum_nonneg fun i _ => norm_nonneg _
  calc (∑ i ∈ Finset.range ((Pol f g p).natDegree + 1), ‖(Pol f g p).coeff i‖) *
        (1 + r) ^ degOf E c d a f g p * μ ^ (c * p + d + At)
      ≤ ((C' * μ ^ p) * (2 ^ E * D * μ ^ (p + (c * p + d)))) *
          μ ^ (E + (c * p + d + At) + p + At) * μ ^ (c * p + d + At) := by
        gcongr
    _ = C' * (2 ^ E * D) * μ ^ (E + 3 * d + 3 * At) * (μ ^ (3 * c + 3)) ^ p := by
        rw [← pow_mul]
        ring
end

end VOA.Huang.GenusOneG1b
