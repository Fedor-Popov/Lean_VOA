import VOA.Huang.GenusOneQEquationSepLocal
import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# Actual spatial derivative laws for two-point coefficients

Translation of the first insertion acts by a falling factorial of the spatial
Euler eigenvalue. The insertion-weight parameter must be shifted along with
the translated vector. These are unconditional mode identities, not equations
obtained by assuming trace descent.
-/
noncomputable section
namespace VOA.Huang.GenusTwoPoint.Separate
open VOA
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  {P₁ P₂ N Q : LWModule W}

/-- Translation of the first raw product insertion; its changed weight is
essential to keep the traced/intermediate-level indices fixed. -/
theorem productLevelCoeff_Lm1
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    (w₁ : P₁.carrier) (w₂ : P₂.carrier) (α₁ α₂ : ℂ) (n k : ℕ) :
    productLevelCoeff Y₁ Y₂ (P₁.isMod.Lm1 w₁) w₂ (α₁ + 1) α₂ n k =
      (N.h - Q.h - α₁ + n - k) * productLevelCoeff Y₁ Y₂ w₁ w₂ α₁ α₂ n k := by
  unfold productLevelCoeff productModeTrace
  rw [Y₁.property.L_neg_one, LinearMap.smul_comp, gradedTraceOp_smul, Pi.smul_apply]
  simp only [smul_eq_mul]
  rw [show (α₁ + 1 + α₂ - 2) - (α₂ + N.h + n - 1 - Q.h) + k - 1 =
    (α₁ + α₂ - 2) - (α₂ + N.h + n - 1 - Q.h) + k by ring]
  congr 1
  ring

/-- The corresponding collision-coordinate law for the actual iterate array. -/
theorem iterateLevelCoeff_Lm1
    (Y₃ : IntertwiningOperator Q.isMod N.isMod N.isMod)
    (Y₄ : IntertwiningOperator P₁.isMod P₂.isMod Q.isMod)
    (w₁ : P₁.carrier) (w₂ : P₂.carrier) (α₁ α₂ : ℂ) (n k : ℕ) :
    iterateLevelCoeff Y₃ Y₄ (P₁.isMod.Lm1 w₁) w₂ (α₁ + 1) α₂ n k =
      (Q.h - α₁ - α₂ + k) * iterateLevelCoeff Y₃ Y₄ w₁ w₂ α₁ α₂ n k := by
  unfold iterateLevelCoeff iterateModeTrace
  rw [Y₄.property.L_neg_one, LinearMap.smul_apply, map_smul, gradedTraceOp_smul,
    Pi.smul_apply]
  simp only [smul_eq_mul]
  rw [show (α₁ + 1 + α₂ - 1 - Q.h) - k - 1 =
    (α₁ + α₂ - 1 - Q.h) - k by ring,
    show (α₁ + 1 + α₂ - 2) - (α₁ + 1 + α₂ - 1 - Q.h) + k =
    (α₁ + α₂ - 2) - (α₁ + α₂ - 1 - Q.h) + k by ring]
  congr 1
  ring

/-- Every translated product insertion has the expected falling-factorial
eigenvalue. This fixes the constant shifts needed in the monic conversion. -/
theorem productLevelCoeff_Lm1_iterate
    (Y₁ : IntertwiningOperator P₁.isMod Q.isMod N.isMod)
    (Y₂ : IntertwiningOperator P₂.isMod N.isMod Q.isMod)
    (w₁ : P₁.carrier) (w₂ : P₂.carrier) (α₁ α₂ : ℂ) (j n k : ℕ) :
    productLevelCoeff Y₁ Y₂ ((P₁.isMod.Lm1)^[j] w₁) w₂ (α₁ + j) α₂ n k =
      (descPochhammer ℂ j).eval (N.h - Q.h - α₁ + n - k) *
        productLevelCoeff Y₁ Y₂ w₁ w₂ α₁ α₂ n k := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', Nat.cast_add, Nat.cast_one, ← add_assoc,
      productLevelCoeff_Lm1, ih, descPochhammer_succ_right]
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_natCast]
    ring

/-- The iterate spatial eigenvalue is independent of the traced level. A
separate q-equation is still needed to control that level. -/
theorem iterateLevelCoeff_Lm1_iterate
    (Y₃ : IntertwiningOperator Q.isMod N.isMod N.isMod)
    (Y₄ : IntertwiningOperator P₁.isMod P₂.isMod Q.isMod)
    (w₁ : P₁.carrier) (w₂ : P₂.carrier) (α₁ α₂ : ℂ) (j n k : ℕ) :
    iterateLevelCoeff Y₃ Y₄ ((P₁.isMod.Lm1)^[j] w₁) w₂ (α₁ + j) α₂ n k =
      (descPochhammer ℂ j).eval (Q.h - α₁ - α₂ + k) *
        iterateLevelCoeff Y₃ Y₄ w₁ w₂ α₁ α₂ n k := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', Nat.cast_add, Nat.cast_one, ← add_assoc,
      iterateLevelCoeff_Lm1, ih, descPochhammer_succ_right]
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_natCast]
    ring

end VOA.Huang.GenusTwoPoint.Separate
