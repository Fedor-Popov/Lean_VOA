import VOA.Huang.GenusTwoPointAssociativity
import VOA.Huang.AssocConverseUniqueness

/-!
# Every genus-one iterate trace coefficient is a finite sum of product coefficients

The converse of `GenusTwoPoint.coefficientAssociativity_of_stronglyRational_pbw`: for a
strongly rational `W`, every iterate channel `Tr_N Y₃(Y₄(w₁, z₁ − z₂) w₂, z₂)` at each
fixed traced weight `β` equals, on the real overlap `z₁ > z₂ > z₁ − z₂ > 0`, a finite sum
of product channels `Tr_N Y₁ʲ(w₁, z₁) Y₂ʲ(w₂, z₂)` with irreducible intermediate modules,
the same finite family serving every traced weight and every pair of homogeneous
insertions. This is step 1 of the iterate-transport argument: an iterate channel is the
single-channel iterate side of
a product sum, so the product Euler system can be transported to it without separating
channels.
-/
namespace VOA.Huang.GenusTwoPoint
open VOA Module MatrixCoeff AssocTarget
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}

/-- The converse coefficient decomposition, uniform in inputs and traced weight. -/
def CoefficientAssociativityConverse (W : VertexOperatorAlgebra V) : Prop :=
  ∀ (P₁ P₂ N Q : LWModule W), P₁.IsIrreducibleLW → P₂.IsIrreducibleLW →
    N.IsIrreducibleLW → Q.IsIrreducibleLW →
  ∀ (Y₃ : IntertwiningOperator Q.isMod N.isMod N.isMod)
    (Y₄ : IntertwiningOperator P₁.isMod P₂.isMod Q.isMod),
  ∃ (r : ℕ) (R : Fin r → LWModule W), (∀ j, (R j).IsIrreducibleLW) ∧
    ∃ (Y₁ : ∀ j, IntertwiningOperator P₁.isMod (R j).isMod N.isMod)
      (Y₂ : ∀ j, IntertwiningOperator P₂.isMod N.isMod (R j).isMod),
    ∀ (α₁ α₂ : ℂ) (w₁ : P₁.carrier) (w₂ : P₂.carrier),
      w₁ ∈ P₁.isMod.weight α₁ → w₂ ∈ P₂.isMod.weight α₂ →
    ∀ (β : ℂ) (z₁ z₂ : ℝ), 0 < z₁ - z₂ → z₁ - z₂ < z₂ →
      iterateCoeff Y₃ Y₄ w₁ w₂ α₁ α₂ β (z₁ - z₂) z₂ =
        ∑ j, productCoeff (Y₁ j) (Y₂ j) w₁ w₂ α₁ α₂ β z₁ z₂

/-- Passing the converse of genus-zero associativity through a finite-dimensional trace. -/
theorem coefficientAssociativityConverse_of_converse (hV : StronglyRational W)
    (hconv : AssociativityConverse W) : CoefficientAssociativityConverse W := by
  intro P₁ P₂ N Q i₁ i₂ iN iQ Y₃ Y₄
  obtain ⟨r, R, iR, Z₁, Z₂, h₁, h₂, heq⟩ :=
    hconv P₁ P₂ N N Q i₁ i₂ iN iN iQ Y₃.val Y₄.val Y₃.property Y₄.property
  let Y₁ : ∀ j, IntertwiningOperator P₁.isMod (R j).isMod N.isMod := fun j => ⟨Z₁ j, h₁ j⟩
  let Y₂ : ∀ j, IntertwiningOperator P₂.isMod N.isMod (R j).isMod := fun j => ⟨Z₂ j, h₂ j⟩
  refine ⟨r, R, iR, Y₁, Y₂, ?_⟩
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
  rw [iterateCoeff_eq_sum_iterValue hV i₁ i₂ iN Y₃ Y₄ hw₁ hw₂ β b hn₀ hi]
  simp_rw [productCoeff_eq_sum_prodValue hV i₁ i₂ iN _ _ hw₁ hw₂ β b hn₂ hp]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [add_sub_cancel_right, Complex.ofReal_sub] using
    heq α₁ α₂ β β w₁ w₂ (b i) (weightFunctional N.isMod β b i)
      hw₁ hw₂ (b i).property (supportedAt_weightFunctional N.isMod β b i) z₁ z₂ hz₀ hz

/-- **Strong rationality supplies the converse coefficient decomposition.** -/
theorem coefficientAssociativityConverse_of_stronglyRational_pbw (hV : StronglyRational W) :
    CoefficientAssociativityConverse W :=
  coefficientAssociativityConverse_of_converse hV
    (VOA.Huang.AssocConverse.associativityConverse_of_stronglyRational_pbw hV)

end VOA.Huang.GenusTwoPoint
