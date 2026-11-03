import VOA.Huang.GenusOneQEquationSepEquations

/-!
# The local iterate-chart regularity obligation

Absolute convergence of the *equation coefficients* at a polyradius gives the
geometric coefficient bounds for the separate-system consumer. The q-radius
can approach one while the collision-coordinate radius shrinks. No regularity
at the collision is inferred from product-chart regularity.
-/
noncomputable section
namespace VOA.Huang.GenusTwoPoint.Separate
open VOA VOA.Huang.UniformConv
open scoped BigOperators

/-- Regularity on a specified closed polyradius, for a coefficient series. -/
def CoefficientSummable (ρ₁ ρ₂ : ℝ) (a : BiSeries) : Prop :=
  Summable (fun p : ℕ × ℕ => ‖coeff a p.1 p.2‖ * ρ₁ ^ p.1 * ρ₂ ^ p.2)

/-- A monic Euler equation whose coefficients are regular at the chosen
polyradius. This includes regularity at the collision coordinate zero. -/
def LocalMonicEquation (ρ₁ ρ₂ : ℝ) (e : ℕ → ℕ → ℂ) (f : BiSeries) : Prop :=
  ∃ (s : ℕ) (a : ℕ → BiSeries), 0 < s ∧
    (∀ k < s, CoefficientSummable ρ₁ ρ₂ (a k)) ∧
    (euler e)^[s] f = ∑ k ∈ Finset.range s, a k * (euler e)^[k] f

/-- Finite families of absolutely convergent coefficient series have a common
geometric constant. No convergence of the unknown solution is used. -/
theorem local_family_bound {ρ₁ ρ₂ : ℝ} (hρ₁ : 0 < ρ₁) (hρ₂ : 0 < ρ₂)
    (s : ℕ) (a : ℕ → BiSeries)
    (ha : ∀ k < s, CoefficientSummable ρ₁ ρ₂ (a k)) :
    ∃ G : ℝ, 0 ≤ G ∧ ∀ k < s, ∀ i j,
      ‖coeff (a k) i j‖ ≤ G * ρ₁⁻¹ ^ i * ρ₂⁻¹ ^ j := by
  let mass := fun k => ∑' p : ℕ × ℕ, ‖coeff (a k) p.1 p.2‖ * ρ₁ ^ p.1 * ρ₂ ^ p.2
  have hm : ∀ k, 0 ≤ mass k := fun k => tsum_nonneg (fun p => by positivity)
  refine ⟨∑ k ∈ Finset.range s, mass k, Finset.sum_nonneg (fun k _ => hm k),
    fun k hk i j => ?_⟩
  have hle : mass k ≤ ∑ k ∈ Finset.range s, mass k :=
    Finset.single_le_sum (fun k _ => hm k) (Finset.mem_range.mpr hk)
  exact (coeff_bound_of_summable hρ₁ hρ₂ (ha k hk) i j).trans (by
    change mass k * ρ₁⁻¹ ^ i * ρ₂⁻¹ ^ j ≤ _
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hle (by positivity)) (by positivity))

theorem separateSystem_of_localMonic {f : BiSeries} {ρ₁ ρ₂ : ℝ}
    (hρ₁ : 0 < ρ₁) (hρ₂ : 0 < ρ₂) (lam mu : ℂ) (a₁ b₁ a₂ b₂ : ℤ)
    (hdet : a₁ * b₂ - a₂ * b₁ ≠ 0)
    (h₁ : LocalMonicEquation ρ₁ ρ₂
      (fun i j => lam + ((a₁ * i + b₁ * j : ℤ) : ℂ)) f)
    (h₂ : LocalMonicEquation ρ₁ ρ₂
      (fun i j => mu + ((a₂ * i + b₂ * j : ℤ) : ℂ)) f) :
    Nonempty (SeparateSystem (coeff f) ρ₁⁻¹ ρ₂⁻¹) := by
  obtain ⟨s₁, a, hs₁, ha, heq₁⟩ := h₁
  obtain ⟨s₂, b, hs₂, hb, heq₂⟩ := h₂
  obtain ⟨A, hA0, hA⟩ := local_family_bound hρ₁ hρ₂ s₁ a ha
  obtain ⟨B, hB0, hB⟩ := local_family_bound hρ₁ hρ₂ s₂ b hb
  apply separateSystem_of_linear lam mu a₁ b₁ a₂ b₂ hdet hs₁ hs₂
    (G := max A B) (g₁ := fun k => coeff (a k)) (g₂ := fun k => coeff (b k))
  · intro k hk i j
    exact (hA k hk i j).trans (by
      gcongr
      exact le_max_left A B)
  · intro k hk i j
    exact (hB k hk i j).trans (by
      gcongr
      exact le_max_right A B)
  · exact diagonalFuchsian_of_series heq₁
  · exact diagonalFuchsian_of_series heq₂

section Consumers
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  {P₁ P₂ N Q : LWModule W}

/-- The actual iterate trace must have two monic equations regular at the
collision. For every q-rate the second radius is positive and may shrink.
This is an explicit residual, not an unconditional VOA theorem. -/
def IterateEulerEquations (Y₃ : IntertwiningOperator Q.isMod N.isMod N.isMod)
    (Y₄ : IntertwiningOperator P₁.isMod P₂.isMod Q.isMod)
    (w₁ : P₁.carrier) (w₂ : P₂.carrier) (α₁ α₂ : ℂ) : Prop :=
  let f := ofArray (iterateLevelCoeff Y₃ Y₄ w₁ w₂ α₁ α₂)
  ∀ r : ℝ, 1 < r → ∃ (ρ : ℝ) (lam mu : ℂ), 0 < ρ ∧
    LocalMonicEquation r⁻¹ ρ (fun n _ => lam + n) f ∧
    LocalMonicEquation r⁻¹ ρ (fun _ k => mu + k) f

/-- The local regular equations imply the exact existing iterate input. -/
theorem iterateSeparateFuchsian_of_eulerEquations
    (Y₃ : IntertwiningOperator Q.isMod N.isMod N.isMod)
    (Y₄ : IntertwiningOperator P₁.isMod P₂.isMod Q.isMod)
    (w₁ : P₁.carrier) (w₂ : P₂.carrier) (α₁ α₂ : ℂ)
    (h : IterateEulerEquations Y₃ Y₄ w₁ w₂ α₁ α₂) :
    IterateSeparateFuchsian Y₃ Y₄ w₁ w₂ α₁ α₂ := by
  intro r hr
  obtain ⟨ρ, lam, mu, hρ, h₁, h₂⟩ := h r hr
  refine ⟨ρ⁻¹, inv_pos.mpr hρ, ?_⟩
  have hs := separateSystem_of_localMonic (inv_pos.mpr (by linarith : 0 < r)) hρ
    lam mu 1 0 0 1 (by norm_num)
    (f := ofArray (iterateLevelCoeff Y₃ Y₄ w₁ w₂ α₁ α₂))
    (by simpa using h₁) (by simpa using h₂)
  simpa only [inv_inv, coeff_ofArray_fun] using hs

end Consumers
end VOA.Huang.GenusTwoPoint.Separate
