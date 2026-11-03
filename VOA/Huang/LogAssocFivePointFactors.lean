import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-! Literal exponential factors of true logarithmic point blocks split into
constant profiles and geometric level factors. Imaginary branch choices are
retained; the norm formulas use only the real parts of the chosen branches. -/
namespace VOA.Huang.LogAssocFivePoint

/-- Genuine three-field chain factors along the actual progression weights
have the two geometric ratios used by product and middle joint convergence. -/
theorem chain_progression_factor (e₁ e₂ e₃ a b c d β h h' : ℂ) (m n : ℕ) :
    Complex.exp (e₁*(β-a-(h'+m)))*Complex.exp (e₂*((h'+m)-b-(h+n)))*
      Complex.exp (e₃*((h+n)-c-d))=
    (Complex.exp (e₁*(β-a-h'))*Complex.exp (e₂*(h'-b-h))*Complex.exp (e₃*(h-c-d)))*
      Complex.exp (e₂-e₁)^m*Complex.exp (e₃-e₂)^n := by
  rw [← Complex.exp_nat_mul,← Complex.exp_nat_mul]
  repeat rw [← Complex.exp_add]
  congr 1
  ring

/-- The actual pair-tree rectangle embeds in the generic triangular pair
array at total level m+n and first-cluster level m. -/
theorem pair_progression_factor (e₁ e₂ e₃ a b c d β h h' : ℂ) (m n : ℕ) :
    Complex.exp (e₁*(β-(h+m)-(h'+n)))*Complex.exp (e₂*((h'+n)-c-d))*
      Complex.exp (e₃*((h+m)-a-b))=
    (Complex.exp (e₁*(β-h-h'))*Complex.exp (e₂*(h'-c-d))*Complex.exp (e₃*(h-a-b)))*
      Complex.exp (e₂-e₁)^(m+n)*Complex.exp (e₃-e₂)^m := by
  rw [← Complex.exp_nat_mul,← Complex.exp_nat_mul]
  repeat rw [← Complex.exp_add]
  push_cast
  congr 1
  ring

/-- Branch imaginary parts do not change the actual geometric norm ratio. -/
theorem norm_exp_sub_of_realParts {e₁ e₂ : ℂ} {r s : ℝ}
    (hr : 0<r) (hs : 0<s) (h₁ : e₁.re=Real.log r) (h₂ : e₂.re=Real.log s) :
    ‖Complex.exp (e₁-e₂)‖=r/s := by
  rw [Complex.norm_exp,Complex.sub_re,h₁,h₂,Real.exp_sub,Real.exp_log hr,Real.exp_log hs]

/-- The actual pair level map is injective, so restriction preserves summability. -/
theorem pairLevel_injective : Function.Injective (fun p : ℕ × ℕ => (p.1+p.2,p.1)) := by
  rintro ⟨m,n⟩ ⟨i,j⟩ he
  have hmi : m=i := congrArg Prod.snd he
  have hmn : m+n=i+j := congrArg Prod.fst he
  apply Prod.ext
  · exact hmi
  · omega

end VOA.Huang.LogAssocFivePoint
