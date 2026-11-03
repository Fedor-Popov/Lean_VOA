/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Core.PolynomialMinimumSymbol

/-!
# A nonzero leading component for any signed polynomial weight

Finite support supplies a minimum even with infinitely many variables and
arbitrary integer weights. Its nonzero homogeneous component is a genuine
symbol, so multiplication by it preserves monomial independence in the
domain of complex polynomials.
-/
namespace VOA.PolynomialMinimum
noncomputable section
open Classical MvPolynomial
variable {σ : Type*}

/-- Every nonzero polynomial admits a nonzero minimum signed-weight symbol.
No sign restriction or finite variable alphabet is required. -/
theorem exists_nonzero_symbol (w : σ → ℤ) (P : MvPolynomial σ ℂ) (hP : P≠0) :
    ∃ d : ℤ,∃ Q : MvPolynomial σ ℂ,Q≠0 ∧ Symbol w d P Q := by
  have hs : P.support.Nonempty := Finset.nonempty_iff_ne_empty.mpr (by
    intro he; exact hP (support_eq_empty.mp he))
  let t := P.support.image (Finsupp.weight w)
  have ht : t.Nonempty := hs.image _
  let d := t.min' ht
  obtain ⟨e,he,hed⟩ := Finset.mem_image.mp (Finset.min'_mem t ht)
  let Q := weightedHomogeneousComponent w d P
  have hmin (f) (hf : coeff f P≠0) : d≤Finsupp.weight w f :=
    Finset.min'_le t _ (Finset.mem_image.mpr ⟨f,mem_support_iff.mpr hf,rfl⟩)
  have hQ : Q≠0 := by
    intro hz
    have hh := congrArg (coeff e) hz
    apply mem_support_iff.mp he
    simpa only [Q,coeff_weightedHomogeneousComponent,hed,d,if_pos rfl,coeff_zero] using hh
  refine ⟨d,Q,hQ,weightedHomogeneousComponent_isWeightedHomogeneous d P,?_⟩
  apply (mem_iff _).mpr
  intro f hf
  rw [coeff_sub] at hf
  change coeff f P-coeff f (weightedHomogeneousComponent w d P)≠0 at hf
  rw [coeff_weightedHomogeneousComponent] at hf
  by_cases hd : Finsupp.weight w f=d
  · simp [hd] at hf
  · simp only [if_neg hd,sub_zero] at hf
    have := hmin f hf
    omega

/-- Multiplication by a fixed nonzero polynomial preserves independence
of the full monomial family; no normalization of the polynomial is needed. -/
theorem monomials_mul_independent (Q : MvPolynomial σ ℂ) (hQ : Q≠0) :
    LinearIndependent ℂ (fun e : σ →₀ ℕ => monomial e (1 : ℂ)*Q) := by
  have hi : Function.Injective (LinearMap.mulRight ℂ Q) := by
    intro A B he
    exact mul_right_cancel₀ hQ he
  exact (basisMonomials σ ℂ).linearIndependent.map' (LinearMap.mulRight ℂ Q)
    (LinearMap.ker_eq_bot.mpr hi)

end
end VOA.PolynomialMinimum
