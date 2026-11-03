import VOA.Huang.GenusTwoPointCoefficients
import VOA.Classification.COne.AssociativityFinal

/-!
# Associativity of fixed-weight trace coefficients

The same finite family works at every traced weight. This is the coefficientwise
part of genus-one associativity, for unmodified plane-coordinate traces on the
real overlap. It neither exchanges infinite q-sums nor asserts modular closure.
-/
namespace VOA.Huang.GenusTwoPoint
open VOA Module MatrixCoeff AssocTarget
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}

/-- A finite iterate decomposition, uniform in input vectors and traced weight. -/
def CoefficientAssociativity (W : VertexOperatorAlgebra V) : Prop :=
  ∀ (P₁ P₂ N Q : LWModule W), P₁.IsIrreducibleLW → P₂.IsIrreducibleLW →
    N.IsIrreducibleLW → Q.IsIrreducibleLW →
  ∀ (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod),
  ∃ (r : ℕ) (R : Fin r → LWModule W), (∀ j, (R j).IsIrreducibleLW) ∧
    ∃ (Y₃ : ∀ j, IntertwiningOperator (R j).isMod N.isMod N.isMod)
      (Y₄ : ∀ j, IntertwiningOperator P₁.isMod P₂.isMod (R j).isMod),
    ∀ (α₁ α₂ : ℂ) (w₁ : P₁.carrier) (w₂ : P₂.carrier),
      w₁ ∈ P₁.isMod.weight α₁ → w₂ ∈ P₂.isMod.weight α₂ →
    ∀ (β : ℂ) (z₁ z₂ : ℝ), 0 < z₁ - z₂ → z₁ - z₂ < z₂ →
      productCoeff Y₁ Y₂ w₁ w₂ α₁ α₂ β z₁ z₂ =
        ∑ j, iterateCoeff (Y₃ j) (Y₄ j) w₁ w₂ α₁ α₂ β (z₁ - z₂) z₂

/-- Passing genus-zero associativity through a finite-dimensional weight trace. -/
theorem coefficientAssociativity_of_assoc (hV : StronglyRational W)
    (hassoc : AssociativityInput W) : CoefficientAssociativity W := by
  intro P₁ P₂ N Q i₁ i₂ iN iQ Y₁ Y₂
  obtain ⟨r, R, iR, Z₃, Z₄, h₃, h₄, heq⟩ :=
    hassoc P₁ P₂ N N Q i₁ i₂ iN iN iQ Y₁.val Y₂.val Y₁.property Y₂.property
  let Y₃ : ∀ j, IntertwiningOperator (R j).isMod N.isMod N.isMod := fun j => ⟨Z₃ j, h₃ j⟩
  let Y₄ : ∀ j, IntertwiningOperator P₁.isMod P₂.isMod (R j).isMod := fun j => ⟨Z₄ j, h₄ j⟩
  refine ⟨r, R, iR, Y₃, Y₄, ?_⟩
  intro α₁ α₂ w₁ w₂ hw₁ hw₂ β z₁ z₂ hz₀ hz
  classical
  letI := N.isMod.finrank β
  let b := Module.finBasis ℂ (N.isMod.weight β)
  have hz₂ : 0 < z₂ := lt_trans hz₀ hz
  have hz₁ : 0 < z₁ := by linarith
  have hp : ‖(z₂ : ℂ)‖ < ‖(z₁ : ℂ)‖ := by
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hz₁, abs_of_pos hz₂]
    linarith
  have hi : ‖((z₁ - z₂ : ℝ) : ℂ)‖ < ‖(z₂ : ℂ)‖ := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hz₀, abs_of_pos hz₂] using hz
  have hn₂ : (z₂ : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hz₂
  have hn₀ : ((z₁ - z₂ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hz₀
  push_cast at hi hn₀
  rw [productCoeff_eq_sum_prodValue hV i₁ i₂ iN Y₁ Y₂ hw₁ hw₂ β b hn₂ hp]
  simp_rw [iterateCoeff_eq_sum_iterValue hV i₁ i₂ iN _ _ hw₁ hw₂ β b hn₀ hi]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [add_sub_cancel_right, Complex.ofReal_sub] using
    heq α₁ α₂ β β w₁ w₂ (b i) (weightFunctional N.isMod β b i)
      hw₁ hw₂ (b i).property (supportedAt_weightFunctional N.isMod β b i) z₁ z₂ hz₀ hz

/-- Strong rationality supplies associativity; only the existing PBW witness is used. -/
theorem coefficientAssociativity_of_stronglyRational_pbw (hV : StronglyRational W) :
    CoefficientAssociativity W :=
  coefficientAssociativity_of_assoc hV
    (VOA.Classification.COne.associativityInput_of_stronglyRational_pbw hV)

end VOA.Huang.GenusTwoPoint
