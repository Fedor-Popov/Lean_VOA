import VOA.Huang.GenusTwoPointGrowth
import VOA.Huang.FivePointSepAnalytic

/-!
# A single collision equation suffices for local iterate sewing

The one-point theorem supplies every fixed-intermediate-level row bound.
Only a coupled regular equation in the intermediate level is required to make
these bounds uniform. Its existence is an explicit, unproved hypothesis here.
No equation in the traced level and no `SeparateSystem` are assumed or produced.
-/

noncomputable section
namespace VOA.Huang.GenusTwoPoint.Separate
open VOA
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  {P₁ P₂ Q N : LWModule W}

/-- The remaining regular collision equation on the ACTUAL iterate array.
Its coefficient convolution may mix both levels. For each q-margin the
coefficient series have a positive collision radius. Existence is not asserted. -/
def IterateCollisionEquation
    (Y₃ : IntertwiningOperator Q.isMod N.isMod N.isMod)
    (Y₄ : IntertwiningOperator P₁.isMod P₂.isMod Q.isMod)
    (w₁ : P₁.carrier) (w₂ : P₂.carrier) (α₁ α₂ : ℂ) : Prop :=
  ∀ R : ℝ, 1 < R → ∃ (R₂ : ℝ) (μ : ℂ) (s : ℕ)
    (g : ℕ → ℕ → ℕ → ℂ) (G : ℝ),
    0 < R₂ ∧ 1 ≤ s ∧
    (∀ k < s, ∀ i j, ‖g k i j‖ ≤ G * R ^ i * R₂ ^ j) ∧
    UniformConv.DiagonalFuchsian (fun _ k => μ + k) s g
      (iterateLevelCoeff Y₃ Y₄ w₁ w₂ α₁ α₂)

/-- A single collision equation upgrades the proved one-point row estimates
to a uniform two-level estimate. It is not necessary to supply a q-equation. -/
theorem iterateModeGrowth_of_collisionEquation
    (hC2 : C2Cofinite W) (iQ : Q.IsIrreducibleLW)
    (Y₃ : IntertwiningOperator Q.isMod N.isMod N.isMod)
    (Y₄ : IntertwiningOperator P₁.isMod P₂.isMod Q.isMod)
    {w₁ : P₁.carrier} {w₂ : P₂.carrier} {α₁ α₂ : ℂ}
    (h₁ : w₁ ∈ P₁.isMod.weight α₁) (h₂ : w₂ ∈ P₂.isMod.weight α₂)
    (heq : IterateCollisionEquation Y₃ Y₄ w₁ w₂ α₁ α₂) :
    IterateModeGrowth Y₃ Y₄ w₁ w₂ α₁ α₂ := by
  intro a ha
  obtain ⟨R₂, μ, s, g, G, hR₂, hs, hg, hf⟩ := heq ((1 + a) / 2) (by linarith)
  obtain ⟨B, _, hB⟩ := exists_iterate_row_bounds hC2 iQ Y₃ Y₄ h₁ h₂ ha
  obtain ⟨C, hC⟩ := FivePointSep.geometric_of_rowFuchsian hs
    (by linarith : 0 ≤ (1 + a) / 2) hR₂.le
    (by linarith : (1 + a) / 2 < a) (by linarith : R₂ < R₂ + 1)
    hg hf (fun k => ⟨B k, fun n => hB n k⟩)
  refine ⟨C, R₂ + 1, ?_, by linarith, hC⟩
  have h := hC 0 0
  simp only [pow_zero, mul_one] at h
  exact le_trans (norm_nonneg _) h

/-- The resulting collision sewing disc is nonempty at every fixed τ.
Its radius is allowed to depend on τ. -/
theorem exists_iterateSewingRadius_of_collisionEquation
    (hC2 : C2Cofinite W) (iQ : Q.IsIrreducibleLW)
    (Y₃ : IntertwiningOperator Q.isMod N.isMod N.isMod)
    (Y₄ : IntertwiningOperator P₁.isMod P₂.isMod Q.isMod)
    {w₁ : P₁.carrier} {w₂ : P₂.carrier} {α₁ α₂ : ℂ}
    (h₁ : w₁ ∈ P₁.isMod.weight α₁) (h₂ : w₂ ∈ P₂.isMod.weight α₂)
    (heq : IterateCollisionEquation Y₃ Y₄ w₁ w₂ α₁ α₂) (τ : UpperHalfPlane) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ z₀ z₂ : ℂ, z₀ ≠ 0 → z₂ ≠ 0 →
      ‖z₀ / z₂‖ < δ → IterateSewingSummable Y₃ Y₄ w₁ w₂ α₁ α₂ z₀ z₂ τ :=
  exists_iterateSewingRadius_of_modeGrowth Y₃ Y₄ w₁ w₂ α₁ α₂
    (iterateModeGrowth_of_collisionEquation hC2 iQ Y₃ Y₄ h₁ h₂ heq) τ

/-- A finite family of collision equations has one positive sewing radius.
The empty family is included without imposing a nonempty-channel hypothesis. -/
theorem exists_common_iterateSewingRadius_of_collisionEquation
    (hC2 : C2Cofinite W) {r : ℕ} (R : Fin r → LWModule W)
    (iR : ∀ j, (R j).IsIrreducibleLW)
    (Y₃ : ∀ j, IntertwiningOperator (R j).isMod N.isMod N.isMod)
    (Y₄ : ∀ j, IntertwiningOperator P₁.isMod P₂.isMod (R j).isMod)
    {w₁ : P₁.carrier} {w₂ : P₂.carrier} {α₁ α₂ : ℂ}
    (h₁ : w₁ ∈ P₁.isMod.weight α₁) (h₂ : w₂ ∈ P₂.isMod.weight α₂)
    (heq : ∀ j, IterateCollisionEquation (Y₃ j) (Y₄ j) w₁ w₂ α₁ α₂)
    (τ : UpperHalfPlane) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ z₀ z₂ : ℂ, z₀ ≠ 0 → z₂ ≠ 0 →
      ‖z₀ / z₂‖ < δ →
      ∀ j, IterateSewingSummable (Y₃ j) (Y₄ j) w₁ w₂ α₁ α₂ z₀ z₂ τ := by
  classical
  choose δ hδ hδ₁ hδs using fun j =>
    exists_iterateSewingRadius_of_collisionEquation hC2 (iR j) (Y₃ j) (Y₄ j)
      h₁ h₂ (heq j) τ
  have hfinite : ∀ s : Finset (Fin r), ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∀ j ∈ s, ε ≤ δ j := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨1, zero_lt_one, le_rfl, by simp⟩
    | @insert j s hj ih =>
      obtain ⟨ε, hε, hε₁, hs⟩ := ih
      refine ⟨min ε (δ j), lt_min hε (hδ j), (min_le_left _ _).trans hε₁, ?_⟩
      intro k hk
      rcases Finset.mem_insert.mp hk with rfl | hk
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hs k hk)
  obtain ⟨ε, hε, hε₁, hs⟩ := hfinite Finset.univ
  exact ⟨ε, hε, hε₁, fun z₀ z₂ hz₀ hz₂ hz j =>
    hδs j z₀ z₂ hz₀ hz₂ (hz.trans_le (hs j (Finset.mem_univ _)))⟩

/-- Coefficient associativity and the one collision equation for each channel
give a convergent product q-trace near the diagonal. This says nothing about
absolute summability of the raw product's double mode expansion. -/
theorem product_qTrace_local_of_collisionEquations
    (hC2 : C2Cofinite W) {r : ℕ} (R : Fin r → LWModule W)
    (iR : ∀ j, (R j).IsIrreducibleLW)
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    (Y₃ : ∀ j, IntertwiningOperator (R j).isMod N.isMod N.isMod)
    (Y₄ : ∀ j, IntertwiningOperator P₁.isMod P₂.isMod (R j).isMod)
    {w₁ : P₁.carrier} {w₂ : P₂.carrier} {α₁ α₂ : ℂ}
    (h₁ : w₁ ∈ P₁.isMod.weight α₁) (h₂ : w₂ ∈ P₂.isMod.weight α₂)
    (hcollision : ∀ j, IterateCollisionEquation (Y₃ j) (Y₄ j) w₁ w₂ α₁ α₂)
    (τ : UpperHalfPlane) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ z₁ z₂ : ℂ, z₁ - z₂ ≠ 0 → z₂ ≠ 0 →
      ‖(z₁ - z₂) / z₂‖ < δ →
      (∀ β, productCoeff Y₁ Y₂ w₁ w₂ α₁ α₂ β z₁ z₂ =
        ∑ j, iterateCoeff (Y₃ j) (Y₄ j) w₁ w₂ α₁ α₂ β (z₁ - z₂) z₂) →
      ProductQSummable Y₁ Y₂ w₁ w₂ α₁ α₂ z₁ z₂ τ ∧
      qTrace N (fun β => productCoeff Y₁ Y₂ w₁ w₂ α₁ α₂ β z₁ z₂) τ =
        ∑ j, qTrace N (fun β => iterateCoeff (Y₃ j) (Y₄ j) w₁ w₂ α₁ α₂ β
          (z₁ - z₂) z₂) τ := by
  obtain ⟨δ, hδ, hδ₁, hs⟩ := exists_common_iterateSewingRadius_of_collisionEquation
    hC2 R iR Y₃ Y₄ h₁ h₂ hcollision τ
  exact ⟨δ, hδ, hδ₁, fun z₁ z₂ hz₀ hz₂ hz heq =>
    product_qTrace_eq_of_coefficients R Y₁ Y₂ Y₃ Y₄ w₁ w₂ α₁ α₂ z₁ z₂ τ
      heq (hs (z₁ - z₂) z₂ hz₀ hz₂ hz)⟩

end VOA.Huang.GenusTwoPoint.Separate
