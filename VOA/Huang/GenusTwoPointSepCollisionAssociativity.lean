import VOA.Huang.GenusTwoPointSepIterateCollision
import VOA.Huang.GenusTwoPointAssociativity

/-!
# Genus-zero associativity supplies the finite channels for local q-convergence

The channels are chosen by the proved PBW associativity theorem, before weights,
insertions or τ. The single collision equation for each channel remains explicit.
The conclusion is local q-summability, not raw product double-series summability.
-/

noncomputable section
namespace VOA.Huang.GenusTwoPoint.Separate
open VOA
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}

/-- Finite PBW associativity channels with conditional analytic sewing.
The only new analytic premise is `IterateCollisionEquation` on each actual channel. -/
theorem exists_local_qTrace_associativity_pbw
    (hV : StronglyRational W) (P₁ P₂ N Q : LWModule W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW)
    (iN : N.IsIrreducibleLW) (iQ : Q.IsIrreducibleLW)
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod) :
    ∃ (r : ℕ) (R : Fin r → LWModule W), (∀ j, (R j).IsIrreducibleLW) ∧
      ∃ (Y₃ : ∀ j, IntertwiningOperator (R j).isMod N.isMod N.isMod)
        (Y₄ : ∀ j, IntertwiningOperator P₁.isMod P₂.isMod (R j).isMod),
      ∀ (α₁ α₂ : ℂ) (w₁ : P₁.carrier) (w₂ : P₂.carrier),
        w₁ ∈ P₁.isMod.weight α₁ → w₂ ∈ P₂.isMod.weight α₂ →
        (∀ j, IterateCollisionEquation (Y₃ j) (Y₄ j) w₁ w₂ α₁ α₂) →
      ∀ τ : UpperHalfPlane, ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      ∀ z₁ z₂ : ℝ, 0 < z₁ - z₂ → z₁ - z₂ < δ * z₂ →
        ProductQSummable Y₁ Y₂ w₁ w₂ α₁ α₂ z₁ z₂ τ ∧
        qTrace N (fun β => productCoeff Y₁ Y₂ w₁ w₂ α₁ α₂ β z₁ z₂) τ =
          ∑ j, qTrace N (fun β => iterateCoeff (Y₃ j) (Y₄ j) w₁ w₂ α₁ α₂ β
            (z₁ - z₂) z₂) τ := by
  obtain ⟨r, R, iR, Y₃, Y₄, heq⟩ :=
    coefficientAssociativity_of_stronglyRational_pbw hV P₁ P₂ N Q i₁ i₂ iN iQ Y₁ Y₂
  refine ⟨r, R, iR, Y₃, Y₄, ?_⟩
  intro α₁ α₂ w₁ w₂ h₁ h₂ hc τ
  obtain ⟨δ, hδ, hδ₁, hs⟩ := product_qTrace_local_of_collisionEquations
    hV.c2Cofinite R iR Y₁ Y₂ Y₃ Y₄ h₁ h₂ hc τ
  refine ⟨δ, hδ, hδ₁, ?_⟩
  intro z₁ z₂ hz₀ hz
  have hz₂ : 0 < z₂ := by nlinarith
  have hover : z₁ - z₂ < z₂ := by nlinarith
  have hn₀ : (z₁ : ℂ) - z₂ ≠ 0 := by
    rw [← Complex.ofReal_sub]
    exact_mod_cast hz₀.ne'
  have hn₂ : (z₂ : ℂ) ≠ 0 := by exact_mod_cast hz₂.ne'
  have hratio : ‖((z₁ : ℂ) - z₂) / z₂‖ < δ := by
    rw [← Complex.ofReal_sub, norm_div, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hz₀, abs_of_pos hz₂]
    exact (div_lt_iff₀ hz₂).2 hz
  exact hs z₁ z₂ hn₀ hn₂ hratio (fun β => heq α₁ α₂ w₁ w₂ h₁ h₂ β z₁ z₂ hz₀ hover)

end VOA.Huang.GenusTwoPoint.Separate
