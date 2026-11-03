import VOA.Huang.HuangODEThreeC1

/-! # Total-level normalization for five external slots

The coordinates are `x = z₂/z₁`, `y = z₃/z₂`. Both boundary
vanishing statements below are uniform in the external homogeneous vectors
and their levels. The normalization uses their total level, including the
output level. These results do not assert finite generation or regularity.
-/

noncomputable section
namespace VOA.Huang.HuangODEThree
open VOA VOA.Huang.FusionTop PowerSeries
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable {M₀ M₁ M₂ M₃ M₄ M₅ M₆ : Type u}
  [AddCommGroup M₀] [Module ℂ M₀] [AddCommGroup M₁] [Module ℂ M₁]
  [AddCommGroup M₂] [Module ℂ M₂] [AddCommGroup M₃] [Module ℂ M₃]
  [AddCommGroup M₄] [Module ℂ M₄] [AddCommGroup M₅] [Module ℂ M₅]
  [AddCommGroup M₆] [Module ℂ M₆]
variable {A₀ : OrdVModule W M₀} {A₁ : OrdVModule W M₁}
  {A₂ : OrdVModule W M₂} {A₃ : OrdVModule W M₃} {A₄ : OrdVModule W M₄}
  {A₅ : OrdVModule W M₅} {A₆ : OrdVModule W M₆}
variable {Y₁ : IntertwiningModes M₁ M₆ M₀} {Y₂ : IntertwiningModes M₂ M₅ M₆}
  {Y₃ : IntertwiningModes M₃ M₄ M₅}

/-- A simultaneous base for both intermediate levels, with arbitrary extra
nonnegative total level. This is a vector vanishing condition, not a bound
on an already summed scalar function. -/
def UniformTwoBase (A₂ : OrdVModule W M₂) (A₃ : OrdVModule W M₃)
    (A₄ : OrdVModule W M₄) (Y₂ : IntertwiningModes M₂ M₅ M₆)
    (Y₃ : IntertwiningModes M₃ M₄ M₅) (h₂ h₃ h₄ ν μ : ℂ) : Prop :=
  ∀ (N₂ N₃ N₄ s : ℕ), N₂ + N₃ + N₄ ≤ s →
    ∀ (w₂ : M₂) (w₃ : M₃) (w₄ : M₄),
      w₂ ∈ A₂.weight (h₂ + N₂) → w₃ ∈ A₃.weight (h₃ + N₃) →
      w₄ ∈ A₄.weight (h₄ + N₄) → ∀ m n : ℤ, m < 0 ∨ n < 0 →
        Y₂ (ν - μ - m + n) w₂ (Y₃ (μ + s - n) w₃ w₄) = 0

/-- Boundedness below gives simultaneous uniform bases on any prescribed
pair of complex cosets. No irreducibility or cofiniteness is needed. -/
theorem exists_uniformTwoBase
    (hY₂ : IsIntertwiningOperator A₂ A₅ A₆ Y₂)
    (hY₃ : IsIntertwiningOperator A₃ A₄ A₅ Y₃)
    (h₂ h₃ h₄ ν₀ μ₀ : ℂ) :
    ∃ K L : ℕ, UniformTwoBase A₂ A₃ A₄ Y₂ Y₃ h₂ h₃ h₄ (ν₀ + K) (μ₀ + L) := by
  obtain ⟨B₅, hB₅⟩ := A₅.boundedBelow
  obtain ⟨B₆, hB₆⟩ := A₆.boundedBelow
  obtain ⟨K, hK⟩ := exists_nat_gt ((h₂ + h₃ + h₄ - ν₀ - 2).re - B₆)
  obtain ⟨L, hL⟩ := exists_nat_gt ((h₃ + h₄ - μ₀ - 1).re - B₅)
  refine ⟨K, L, ?_⟩
  intro N₂ N₃ N₄ s hs w₂ w₃ w₄ hw₂ hw₃ hw₄ m n hmn
  have hs' : (N₂ : ℝ) + N₃ + N₄ ≤ s := by exact_mod_cast hs
  have hv₅ := mem_weight hY₃ hw₃ hw₄ (μ₀ + L + s - n)
  have hv₆ := mem_weight hY₂ hw₂ hv₅ (ν₀ + K - (μ₀ + L) - m + n)
  rcases hmn with hm | hn
  · by_contra he
    have hb := hB₆ _ (fun hb => he (by rw [hb, Submodule.mem_bot] at hv₆; exact hv₆))
    have hm' : (m : ℝ) < 0 := by exact_mod_cast hm
    simp only [Complex.add_re, Complex.sub_re, Complex.natCast_re,
      Complex.intCast_re, Complex.one_re] at hb hK
    norm_num at hK
    linarith
  · have hz : Y₃ (μ₀ + L + s - n) w₃ w₄ = 0 := by
      by_contra he
      have hb := hB₅ _ (fun hb => he (by rw [hb, Submodule.mem_bot] at hv₅; exact hv₅))
      have hn' : (n : ℝ) < 0 := by exact_mod_cast hn
      have hN₂ : (0 : ℝ) ≤ N₂ := Nat.cast_nonneg _
      simp only [Complex.add_re, Complex.sub_re, Complex.natCast_re,
        Complex.intCast_re, Complex.one_re] at hb hL
      linarith
    rw [hz, map_zero]

/-- The normalized coefficient, extended to arbitrary complex offsets so that
all shifts can be stated without truncated natural subtraction. At total
level `s`, the sum of its three mode indices is `c+s-2*N₀`. -/
def normalizedCoeff (Y₁ : IntertwiningModes M₁ M₆ M₀)
    (Y₂ : IntertwiningModes M₂ M₅ M₆) (Y₃ : IntertwiningModes M₃ M₄ M₅)
    (c ν μ : ℂ) (f : M₀ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) (w₄ : M₄)
    (N₀ s : ℕ) (m n : ℂ) : ℂ :=
  productCoeff Y₁ Y₂ Y₃ f w₁ w₂ w₃ w₄
    (c - ν - 2 * N₀ + m) (ν - μ - m + n) (μ + s - n)

/-- The total-level-normalized actual five-slot series. -/
def normalizedSeries (Y₁ : IntertwiningModes M₁ M₆ M₀)
    (Y₂ : IntertwiningModes M₂ M₅ M₆) (Y₃ : IntertwiningModes M₃ M₄ M₅)
    (c ν μ : ℂ) (f : M₀ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) (w₄ : M₄)
    (N₀ s : ℕ) : PowerSeries (PowerSeries ℂ) :=
  PowerSeries.mk fun m => PowerSeries.mk fun n =>
    normalizedCoeff Y₁ Y₂ Y₃ c ν μ f w₁ w₂ w₃ w₄ N₀ s m n

@[simp] theorem coeff_normalizedSeries (c ν μ : ℂ) (f : M₀ →ₗ[ℂ] ℂ)
    (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) (w₄ : M₄) (N₀ s m n : ℕ) :
    coeff n (coeff m (normalizedSeries Y₁ Y₂ Y₃ c ν μ f w₁ w₂ w₃ w₄ N₀ s)) =
      normalizedCoeff Y₁ Y₂ Y₃ c ν μ f w₁ w₂ w₃ w₄ N₀ s m n := by
  simp [normalizedSeries]

/-- Both negative boundary strips vanish before pairing with the output. -/
theorem normalizedCoeff_eq_zero_of_negative {h₂ h₃ h₄ ν μ : ℂ}
    (hB : UniformTwoBase A₂ A₃ A₄ Y₂ Y₃ h₂ h₃ h₄ ν μ)
    {N₂ N₃ N₄ s : ℕ} (hs : N₂ + N₃ + N₄ ≤ s)
    {w₂ : M₂} {w₃ : M₃} {w₄ : M₄}
    (hw₂ : w₂ ∈ A₂.weight (h₂ + N₂)) (hw₃ : w₃ ∈ A₃.weight (h₃ + N₃))
    (hw₄ : w₄ ∈ A₄.weight (h₄ + N₄))
    (c : ℂ) (f : M₀ →ₗ[ℂ] ℂ) (w₁ : M₁) (N₀ : ℕ)
    (m n : ℤ) (hmn : m < 0 ∨ n < 0) :
    normalizedCoeff Y₁ Y₂ Y₃ c ν μ f w₁ w₂ w₃ w₄ N₀ s m n = 0 := by
  unfold normalizedCoeff productCoeff
  rw [hB N₂ N₃ N₄ s hs w₂ w₃ w₄ hw₂ hw₃ hw₄ m n hmn, map_zero, map_zero]

/-- Exact coefficient formula for monomial multiplication, including both
boundary strips. It is the reindexing needed in normalized C₁ relations. -/
theorem coeff_monomial_normalizedSeries {h₂ h₃ h₄ ν μ : ℂ}
    (hB : UniformTwoBase A₂ A₃ A₄ Y₂ Y₃ h₂ h₃ h₄ ν μ)
    {N₂ N₃ N₄ s : ℕ} (hs : N₂ + N₃ + N₄ ≤ s)
    {w₂ : M₂} {w₃ : M₃} {w₄ : M₄}
    (hw₂ : w₂ ∈ A₂.weight (h₂ + N₂)) (hw₃ : w₃ ∈ A₃.weight (h₃ + N₃))
    (hw₄ : w₄ ∈ A₄.weight (h₄ + N₄))
    (c : ℂ) (f : M₀ →ₗ[ℂ] ℂ) (w₁ : M₁) (N₀ a b m n : ℕ) :
    coeff n (coeff m (X ^ a * PowerSeries.C (X ^ b) *
      normalizedSeries Y₁ Y₂ Y₃ c ν μ f w₁ w₂ w₃ w₄ N₀ s)) =
        normalizedCoeff Y₁ Y₂ Y₃ c ν μ f w₁ w₂ w₃ w₄ N₀ s
          ((m : ℂ) - a) ((n : ℂ) - b) := by
  rw [mul_assoc, coeff_X_pow_mul']
  split_ifs with hm
  · rw [coeff_C_mul, coeff_X_pow_mul']
    split_ifs with hn
    · rw [coeff_normalizedSeries, Nat.cast_sub hm, Nat.cast_sub hn]
    · rw [← Int.cast_natCast m, ← Int.cast_natCast a, ← Int.cast_sub,
        ← Int.cast_natCast n, ← Int.cast_natCast b, ← Int.cast_sub]
      symm
      exact normalizedCoeff_eq_zero_of_negative hB hs hw₂ hw₃ hw₄ c f w₁ N₀ _ _
        (Or.inr (by omega))
  · rw [map_zero]
    rw [← Int.cast_natCast m, ← Int.cast_natCast a, ← Int.cast_sub,
      ← Int.cast_natCast n, ← Int.cast_natCast b, ← Int.cast_sub]
    symm
    exact normalizedCoeff_eq_zero_of_negative hB hs hw₂ hw₃ hw₄ c f w₁ N₀ _ _
      (Or.inl (by omega))

/-- On homogeneous external data, only the selected output weight matters;
there is no restriction on the functional away from that weight. -/
theorem normalizedCoeff_congr_functional
    (hY₁ : IsIntertwiningOperator A₁ A₆ A₀ Y₁)
    (hY₂ : IsIntertwiningOperator A₂ A₅ A₆ Y₂)
    (hY₃ : IsIntertwiningOperator A₃ A₄ A₅ Y₃)
    {h₀ h₁ h₂ h₃ h₄ ν μ : ℂ} {N₀ N₁ N₂ N₃ N₄ : ℕ}
    {w₁ : M₁} {w₂ : M₂} {w₃ : M₃} {w₄ : M₄}
    (hw₁ : w₁ ∈ A₁.weight (h₁ + N₁)) (hw₂ : w₂ ∈ A₂.weight (h₂ + N₂))
    (hw₃ : w₃ ∈ A₃.weight (h₃ + N₃)) (hw₄ : w₄ ∈ A₄.weight (h₄ + N₄))
    {f g : M₀ →ₗ[ℂ] ℂ} (hf : f.domRestrict (A₀.weight (h₀ + N₀)) =
      g.domRestrict (A₀.weight (h₀ + N₀))) (m n : ℂ) :
    normalizedCoeff Y₁ Y₂ Y₃ (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ f w₁ w₂ w₃ w₄
      N₀ (N₀ + N₁ + N₂ + N₃ + N₄) m n =
    normalizedCoeff Y₁ Y₂ Y₃ (h₁ + h₂ + h₃ + h₄ - h₀ - 3) ν μ g w₁ w₂ w₃ w₄
      N₀ (N₀ + N₁ + N₂ + N₃ + N₄) m n := by
  have hw := product_mem_weight hY₁ hY₂ hY₃ hw₁ hw₂ hw₃ hw₄
    (h₁ + h₂ + h₃ + h₄ - h₀ - 3 - ν - 2 * N₀ + m)
    (ν - μ - m + n) (μ + (N₀ + N₁ + N₂ + N₃ + N₄ : ℕ) - n)
  have e : (h₁ + N₁) + (h₂ + N₂) + (h₃ + N₃) + (h₄ + N₄) -
      (h₁ + h₂ + h₃ + h₄ - h₀ - 3 - ν - 2 * N₀ + m) -
      (ν - μ - m + n) - (μ + (N₀ + N₁ + N₂ + N₃ + N₄ : ℕ) - n) - 3 = h₀ + N₀ := by
    push_cast
    ring
  rw [e] at hw
  exact LinearMap.congr_fun hf ⟨_, hw⟩

/-- The innermost translation is a regular Euler operation on the normalized
array. It controls the second index, not the radial sum of both indices. -/
theorem normalizedCoeff_Lm1_third
    (hY₃ : IsIntertwiningOperator A₃ A₄ A₅ Y₃)
    (c ν μ : ℂ) (f : M₀ →ₗ[ℂ] ℂ)
    (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) (w₄ : M₄) (N₀ s : ℕ) (m n : ℂ) :
    normalizedCoeff Y₁ Y₂ Y₃ c ν μ f w₁ w₂ (A₃.Lm1 w₃) w₄ N₀ (s + 1) m n =
      (n - (μ + s + 1)) * normalizedCoeff Y₁ Y₂ Y₃ c ν μ f w₁ w₂ w₃ w₄ N₀ s m n := by
  unfold normalizedCoeff
  rw [productCoeff_Lm1_third hY₃]
  have he : μ + ((s + 1 : ℕ) : ℂ) - n - 1 = μ + s - n := by push_cast; ring
  rw [he]
  congr 1
  push_cast
  ring

/-- Identification with the original two-intermediate-level series. The two
monomial shifts are independent; boundary vanishing uses the actual lowest
weights of both intermediate modules. -/
theorem normalizedSeries_eq_shift_productSeries
    (hY₂ : IsIntertwiningOperator A₂ A₅ A₆ Y₂)
    (hY₃ : IsIntertwiningOperator A₃ A₄ A₅ Y₃)
    {h₀ h₁ h₂ h₃ h₄ h₅ h₆ : ℂ}
    (hl₅ : IsLowestWeight A₅ h₅) (hl₆ : IsLowestWeight A₆ h₆)
    (N₀ N₁ N₂ N₃ N₄ K L : ℕ) (f : M₀ →ₗ[ℂ] ℂ) (w₁ : M₁)
    {w₂ : M₂} {w₃ : M₃} {w₄ : M₄}
    (hw₂ : w₂ ∈ A₂.weight (h₂ + N₂)) (hw₃ : w₃ ∈ A₃.weight (h₃ + N₃))
    (hw₄ : w₄ ∈ A₄.weight (h₄ + N₄)) :
    normalizedSeries Y₁ Y₂ Y₃ (h₁ + h₂ + h₃ + h₄ - h₀ - 3)
      (h₂ + h₃ + h₄ - h₆ - 2 - N₀ - N₁ + K)
      (h₃ + h₄ - h₅ - 1 - N₀ - N₁ - N₂ + L)
      f w₁ w₂ w₃ w₄ N₀ (N₀ + N₁ + N₂ + N₃ + N₄) =
    X ^ K * PowerSeries.C (X ^ L) * productSeries Y₁ Y₂ Y₃ f w₁ w₂ w₃ w₄
      (h₀ + N₀) (h₁ + N₁) (h₂ + N₂) (h₃ + N₃) (h₄ + N₄) h₅ h₆ := by
  ext m n
  rw [coeff_normalizedSeries, mul_assoc, coeff_X_pow_mul']
  unfold normalizedCoeff
  have er : h₃ + h₄ - h₅ - 1 - N₀ - N₁ - N₂ + L +
      ((N₀ + N₁ + N₂ + N₃ + N₄ : ℕ) : ℂ) - n =
      (h₃ + N₃) + (h₄ + N₄) - h₅ - ((n : ℂ) - L) - 1 := by push_cast; ring
  have eq : h₂ + h₃ + h₄ - h₆ - 2 - N₀ - N₁ + K -
      (h₃ + h₄ - h₅ - 1 - N₀ - N₁ - N₂ + L) - m + n =
      (h₂ + N₂) + h₅ + ((n : ℂ) - L) - h₆ - ((m : ℂ) - K) - 1 := by ring
  have ep : h₁ + h₂ + h₃ + h₄ - h₀ - 3 -
      (h₂ + h₃ + h₄ - h₆ - 2 - N₀ - N₁ + K) - 2 * N₀ + m =
      (h₁ + N₁) + h₆ + ((m : ℂ) - K) - (h₀ + N₀) - 1 := by ring
  rw [ep, eq, er]
  split_ifs with hm
  · rw [coeff_C_mul, coeff_X_pow_mul']
    split_ifs with hn
    · rw [coeff_productSeries, Nat.cast_sub hm, Nat.cast_sub hn]
    · have hz := HuangODEProduct.eq_zero_of_mem_weight_neg hl₅
        (mem_weight hY₃ hw₃ hw₄ ((h₃ + N₃) + (h₄ + N₄) - h₅ - ((n : ℂ) - L) - 1))
        (j := (n : ℤ) - L) (by push_cast; ring) (by omega)
      simp [productCoeff, hz]
  · have hw := mem_weight hY₂ hw₂
      (mem_weight hY₃ hw₃ hw₄ ((h₃ + N₃) + (h₄ + N₄) - h₅ - ((n : ℂ) - L) - 1))
      ((h₂ + N₂) + h₅ + ((n : ℂ) - L) - h₆ - ((m : ℂ) - K) - 1)
    have hz := HuangODEProduct.eq_zero_of_mem_weight_neg hl₆ hw
      (j := (m : ℤ) - K) (by push_cast; ring) (by omega)
    simp [productCoeff, hz]

/-- Translation in the middle insertion shifts the second normalized index.
Thus the third-insertion Euler identity alone cannot be relabelled radial. -/
theorem normalizedCoeff_Lm1_second
    (hY₂ : IsIntertwiningOperator A₂ A₅ A₆ Y₂)
    (c ν μ : ℂ) (f : M₀ →ₗ[ℂ] ℂ)
    (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) (w₄ : M₄) (N₀ s : ℕ) (m n : ℂ) :
    normalizedCoeff Y₁ Y₂ Y₃ c ν μ f w₁ (A₂.Lm1 w₂) w₃ w₄ N₀ (s + 1) m n =
      -(ν - μ - m + n) *
        normalizedCoeff Y₁ Y₂ Y₃ c ν μ f w₁ w₂ w₃ w₄ N₀ s m (n - 1) := by
  unfold normalizedCoeff
  rw [productCoeff_Lm1_second hY₂]
  push_cast
  ring_nf

/-- Translation in the first insertion shifts both normalized indices. -/
theorem normalizedCoeff_Lm1_first
    (hY₁ : IsIntertwiningOperator A₁ A₆ A₀ Y₁)
    (c ν μ : ℂ) (f : M₀ →ₗ[ℂ] ℂ)
    (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) (w₄ : M₄) (N₀ s : ℕ) (m n : ℂ) :
    normalizedCoeff Y₁ Y₂ Y₃ c ν μ f (A₁.Lm1 w₁) w₂ w₃ w₄ N₀ (s + 1) m n =
      -(c - ν - 2 * N₀ + m) *
        normalizedCoeff Y₁ Y₂ Y₃ c ν μ f w₁ w₂ w₃ w₄ N₀ s (m - 1) (n - 1) := by
  unfold normalizedCoeff
  rw [productCoeff_Lm1_first hY₁]
  push_cast
  ring_nf

end VOA.Huang.HuangODEThree
