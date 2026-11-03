import VOA.Huang.HuangODEThreeSepInduction

/-!
# Geometric bounds for products of three intertwining operators

`productCoeff_geometric`: for lowest-weight external modules with graded `C₁` data and
arbitrary intermediate modules, the coefficient array of a product of three intertwining
operators along its weight plane,

  `(i, j) ↦ f(𝒴₁(w₁)_{a+i} 𝒴₂(w₂)_{b-i+j} 𝒴₃(w₃)_{c-j} w₄)`,

(`i` = level in the outer intermediate module, power of `x = z₂/z₁`; `j` = level in the
inner intermediate module, power of `y = z₃/z₂`) satisfies `‖·‖ ≤ K ρ₁^i ρ₂^j` for every
`ρ₂ > 1`, provided every row (fixed `j`, also the shifted rows below the base) grows at most
like `ρ₁^i`, `ρ₁ > 1`. The inner direction comes from the regular inner equation
(`innerRegular_normalizedSeries`), the outer one from the rows; this is Huang's convergence
argument (math/0206206, Thm 3.5) in coefficient form. No outer equation is used.
-/

noncomputable section
namespace VOA.Huang.FivePointSep
open VOA VOA.Huang.FusionTop PowerSeries VOA.Huang.HuangODEThree
open VOA.Huang.HuangODEProduct VOA.Huang.UniformConv
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

/-- Row growth of the coefficient array, including the rows shifted below the base. -/
def ProductRowBound (Y₁ : IntertwiningModes M₁ M₆ M₀) (Y₂ : IntertwiningModes M₂ M₅ M₆)
    (Y₃ : IntertwiningModes M₃ M₄ M₅) (f : M₀ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃)
    (w₄ : M₄) (a b c : ℂ) (ρ₁ : ℝ) : Prop :=
  ∀ (k : ℕ) (j : ℤ), ∃ K : ℝ, ∀ m : ℕ,
    ‖productCoeff Y₁ Y₂ Y₃ f w₁ w₂ w₃ w₄ (a - k + m) (b + k - m + j) (c - j)‖ ≤ K * ρ₁ ^ m

theorem exists_between_one {ρ₁ ρ₂ : ℝ} (h₁ : 1 < ρ₁) (h₂ : 1 < ρ₂) :
    ∃ R : ℝ, 1 < R ∧ R < ρ₁ ∧ R < ρ₂ := by
  refine ⟨min ((1 + ρ₁) / 2) ((1 + ρ₂) / 2), lt_min (by linarith) (by linarith),
    lt_of_le_of_lt (min_le_left _ _) (by linarith),
    lt_of_le_of_lt (min_le_right _ _) (by linarith)⟩

/-- **Joint geometric bound for a product of three intertwining operators.** -/
theorem productCoeff_geometric
    (hY₁ : IsIntertwiningOperator A₁ A₆ A₀ Y₁)
    (hY₂ : IsIntertwiningOperator A₂ A₅ A₆ Y₂)
    (hY₃ : IsIntertwiningOperator A₃ A₄ A₅ Y₃)
    {h₀ h₁ h₂ h₃ h₄ : ℂ} {B₀ B₁ B₂ B₃ B₄ : ℕ}
    (hl₀ : IsLowestWeight A₀ h₀) (hl₁ : IsLowestWeight A₁ h₁)
    (hl₂ : IsLowestWeight A₂ h₂) (hl₃ : IsLowestWeight A₃ h₃) (hl₄ : IsLowestWeight A₄ h₄)
    (hD₀ : DualC1Graded A₀ h₀ B₀) (hC₁ : C1Graded A₁ h₁ B₁) (hC₂ : C1Graded A₂ h₂ B₂)
    (hC₃ : C1Graded A₃ h₃ B₃) (hC₄ : C1Graded A₄ h₄ B₄)
    {α₁ α₂ α₃ α₄ : ℂ} {w₁ : M₁} {w₂ : M₂} {w₃ : M₃} {w₄ : M₄}
    (hw₁ : w₁ ∈ A₁.weight α₁) (hw₂ : w₂ ∈ A₂.weight α₂)
    (hw₃ : w₃ ∈ A₃.weight α₃) (hw₄ : w₄ ∈ A₄.weight α₄)
    (f : M₀ →ₗ[ℂ] ℂ) (a b c : ℂ) {ρ₁ ρ₂ : ℝ} (hρ₁ : 1 < ρ₁) (hρ₂ : 1 < ρ₂)
    (hrow : ProductRowBound Y₁ Y₂ Y₃ f w₁ w₂ w₃ w₄ a b c ρ₁) :
    ∃ K : ℝ, ∀ i j : ℕ,
      ‖productCoeff Y₁ Y₂ Y₃ f w₁ w₂ w₃ w₄ (a + i) (b - i + j) (c - j)‖ ≤
        K * ρ₁ ^ i * ρ₂ ^ j := by
  classical
  -- degenerate weight spaces give the zero array
  by_cases z₁ : A₁.weight α₁ = ⊥
  · have : w₁ = 0 := by rw [z₁] at hw₁; exact (Submodule.mem_bot ℂ).mp hw₁
    subst this
    exact ⟨0, fun i j => by simp [productCoeff]⟩
  by_cases z₂ : A₂.weight α₂ = ⊥
  · have : w₂ = 0 := by rw [z₂] at hw₂; exact (Submodule.mem_bot ℂ).mp hw₂
    subst this
    exact ⟨0, fun i j => by simp [productCoeff]⟩
  by_cases z₃ : A₃.weight α₃ = ⊥
  · have : w₃ = 0 := by rw [z₃] at hw₃; exact (Submodule.mem_bot ℂ).mp hw₃
    subst this
    exact ⟨0, fun i j => by simp [productCoeff]⟩
  by_cases z₄ : A₄.weight α₄ = ⊥
  · have : w₄ = 0 := by rw [z₄] at hw₄; exact (Submodule.mem_bot ℂ).mp hw₄
    subst this
    exact ⟨0, fun i j => by simp [productCoeff]⟩
  set α₀ : ℂ := α₁ + α₂ + α₃ + α₄ - (a + b + c) - 3 with hα₀
  have hvec : ∀ (i j : ℕ), Y₁ (a + i) w₁ (Y₂ (b - i + j) w₂ (Y₃ (c - j) w₃ w₄)) ∈
      A₀.weight α₀ := by
    intro i j
    have h := product_mem_weight hY₁ hY₂ hY₃ hw₁ hw₂ hw₃ hw₄ (a + i) (b - i + j) (c - j)
    convert h using 2
    rw [hα₀]; ring
  by_cases z₀ : A₀.weight α₀ = ⊥
  · refine ⟨0, fun i j => ?_⟩
    have h := hvec i j
    rw [z₀] at h
    rw [productCoeff, (Submodule.mem_bot ℂ).mp h]
    simp
  obtain ⟨N₁, rfl⟩ := hl₁ α₁ z₁
  obtain ⟨N₂, rfl⟩ := hl₂ α₂ z₂
  obtain ⟨N₃, rfl⟩ := hl₃ α₃ z₃
  obtain ⟨N₄, rfl⟩ := hl₄ α₄ z₄
  obtain ⟨N₀, hN₀⟩ := hl₀ α₀ z₀
  set C := h₁ + h₂ + h₃ + h₄ - h₀ - 3 with hC
  set s := N₀ + N₁ + N₂ + N₃ + N₄ with hs
  set ν₀ : ℂ := C - 2 * N₀ - a with hν₀
  set μ₀ : ℂ := ν₀ - b with hμ₀
  obtain ⟨K, L, hB⟩ := exists_uniformTwoBase hY₂ hY₃ h₂ h₃ h₄ ν₀ μ₀
  set Q := normalizedSeries Y₁ Y₂ Y₃ C (ν₀ + K) (μ₀ + L) f w₁ w₂ w₃ w₄ N₀ s with hQ
  have hcoef : ∀ m n : ℕ, c2 Q m n =
      productCoeff Y₁ Y₂ Y₃ f w₁ w₂ w₃ w₄ (a - K + m) (b + K - m + (((n : ℤ) - L : ℤ) : ℂ))
        (c - (((n : ℤ) - L : ℤ) : ℂ)) := by
    intro m n
    rw [hQ, c2_normalizedSeries]
    unfold normalizedCoeff
    congr 1
    · rw [hν₀]; ring
    · rw [hν₀, hμ₀]; push_cast; ring
    · have e : (α₀ : ℂ) = h₀ + N₀ := hN₀
      rw [hα₀] at e
      rw [hμ₀, hν₀, hs, hC]; push_cast
      linear_combination e
  -- the inner regular equation
  obtain ⟨sdeg, g, hs1, hgb, heq⟩ := innerRegular_normalizedSeries hY₁ hY₂ hY₃ hl₀ hl₁ hl₂
    hl₃ hl₄ hB hD₀ hC₁ hC₂ hC₃ hC₄ f hw₁ hw₂ hw₃ hw₄ 0
  obtain ⟨R, hR1, hRρ₁, hRρ₂⟩ := exists_between_one hρ₁ hρ₂
  obtain ⟨G, hG⟩ := hgb R hR1
  have hg' : ∀ k < sdeg, ∀ i j, ‖g k i j‖ ≤ max G 0 * R ^ i * R ^ j := by
    intro k hk i j
    refine le_trans (hG k hk i j) ?_
    have : 0 ≤ R ^ i * R ^ j := by positivity
    rw [mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) this
  have hrows : ∀ n, ∃ K' : ℝ, ∀ m, ‖c2 Q m n‖ ≤ K' * ρ₁ ^ m := by
    intro n
    obtain ⟨K', hK'⟩ := hrow K ((n : ℤ) - L)
    exact ⟨K', fun m => by rw [hcoef]; exact hK' m⟩
  have heq' : DiagonalFuchsian (fun _ n => (0 : ℂ) + n) sdeg g (c2 Q) := heq
  obtain ⟨K₀, hK₀⟩ := geometric_of_rowFuchsian hs1 (by linarith) (by linarith) hRρ₁ hRρ₂
    hg' heq' hrows
  refine ⟨K₀ * ρ₁ ^ K * ρ₂ ^ L, fun i j => ?_⟩
  have e := hcoef (i + K) (j + L)
  have e' : productCoeff Y₁ Y₂ Y₃ f w₁ w₂ w₃ w₄ (a + i) (b - i + j) (c - j) =
      c2 Q (i + K) (j + L) := by
    rw [e]
    congr 1
    · push_cast; ring
    · push_cast; ring
    · push_cast; ring
  rw [e']
  calc ‖c2 Q (i + K) (j + L)‖ ≤ K₀ * ρ₁ ^ (i + K) * ρ₂ ^ (j + L) := hK₀ _ _
    _ = K₀ * ρ₁ ^ K * ρ₂ ^ L * ρ₁ ^ i * ρ₂ ^ j := by rw [pow_add, pow_add]; ring

end VOA.Huang.FivePointSep
