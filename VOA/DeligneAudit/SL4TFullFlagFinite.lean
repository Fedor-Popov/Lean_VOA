import VOA.DeligneAudit.SL4TRemainderShift
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic

/-! # Finite-dimensionality and universal maps of the truncated full flag -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

/-- Evaluation at the quotient roots is the canonical quotient projection. -/
theorem fullFlag_aeval (B N : ℕ) :
    MvPolynomial.aeval (fullFlagRoot B N) =
      Ideal.Quotient.mkₐ ℂ (fullFlagTruncationIdeal B N) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [MvPolynomial.aeval_X]
  rfl

/-- The quotient roots generate the whole truncated full-flag algebra. -/
theorem fullFlag_adjoin_roots (B N : ℕ) :
    Algebra.adjoin ℂ (Set.range (fullFlagRoot B N)) = ⊤ := by
  rw [Algebra.adjoin_range_eq_range_aeval, fullFlag_aeval, AlgHom.range_eq_top]
  exact Ideal.Quotient.mkₐ_surjective ℂ _

/-- Every full-flag quotient is finite-dimensional for every common cutoff. -/
theorem fullFlag_finite (B N : ℕ) : FiniteDimensional ℂ (FullFlagRing B N) := by
  have hi : ∀ x ∈ Set.range (fullFlagRoot B N), IsIntegral ℂ x := by
    rintro x ⟨i, rfl⟩
    refine ⟨Polynomial.X ^ N, Polynomial.monic_X_pow N, ?_⟩
    simpa only [Polynomial.eval₂_pow, Polynomial.eval₂_X] using fullFlagRoot_pow B N i
  have hf := fg_adjoin_of_finite (Set.finite_range (fullFlagRoot B N)) hi
  rw [fullFlag_adjoin_roots, Algebra.top_toSubmodule] at hf
  exact Module.Finite.of_fg_top hf

variable {A : Type*} [CommRing A] [Algebra ℂ A]

/-- The elementary relations vanish under evaluation at any coinvariant alphabet. -/
theorem fullFlagSymmetricIdeal_le_ker (B : ℕ) (x : Fin B → A)
    (he : D4Levi.ksEPoly (List.ofFn x) = 1) :
    fullFlagSymmetricIdeal B ≤ RingHom.ker (MvPolynomial.aeval x).toRingHom := by
  apply Ideal.span_le.mpr
  rintro p ⟨s, hs, rfl⟩
  have hm := alphabetElementary_map (MvPolynomial.aeval x).toRingHom
    (List.ofFn fun i : Fin B => (MvPolynomial.X i : MvPolynomial (Fin B) ℂ))
  simp only [List.map_ofFn, Function.comp_def, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, MvPolynomial.aeval_X] at hm
  have hc := congrArg (fun p : Polynomial A => p.coeff s) (hm.trans he)
  dsimp only at hc
  rw [Polynomial.coeff_map, elementaryProduct_coeff] at hc
  simp only [map_mul, map_pow, map_neg, map_one, Polynomial.coeff_one,
    if_neg (Nat.ne_of_gt hs)] at hc
  change MvPolynomial.aeval x (MvPolynomial.esymm (Fin B) ℂ s) = 0
  exact (IsUnit.mul_right_eq_zero (isUnit_neg_one.pow s)).mp hc

/-- The concrete full-flag presentation maps to any alphabet with the same relations. -/
def fullFlagLift (B N : ℕ) (x : Fin B → A)
    (he : D4Levi.ksEPoly (List.ofFn x) = 1) (hx : ∀ i, x i ^ N = 0) :
    FullFlagRing B N →ₐ[ℂ] A :=
  Ideal.Quotient.liftₐ _ (MvPolynomial.aeval x) (by
    refine sup_le (fullFlagSymmetricIdeal_le_ker B x he) ?_
    apply Ideal.span_le.mpr
    rintro p ⟨i, rfl⟩
    change MvPolynomial.aeval x (MvPolynomial.X i ^ N : MvPolynomial (Fin B) ℂ) = 0
    simpa only [map_pow, MvPolynomial.aeval_X] using hx i)

theorem fullFlagLift_surjective (B N : ℕ) (x : Fin B → A)
    (he : D4Levi.ksEPoly (List.ofFn x) = 1) (hx : ∀ i, x i ^ N = 0)
    (hg : Function.Surjective
      (MvPolynomial.aeval x : MvPolynomial (Fin B) ℂ →ₐ[ℂ] A)) :
    Function.Surjective (fullFlagLift B N x he hx) := by
  intro a
  obtain ⟨p, rfl⟩ := hg a
  exact ⟨Ideal.Quotient.mk _ p, rfl⟩

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.fullFlag_aeval
#print axioms VOA.DeligneAudit.SL4T.fullFlag_adjoin_roots
#print axioms VOA.DeligneAudit.SL4T.fullFlag_finite
#print axioms VOA.DeligneAudit.SL4T.fullFlagSymmetricIdeal_le_ker
#print axioms VOA.DeligneAudit.SL4T.fullFlagLift
#print axioms VOA.DeligneAudit.SL4T.fullFlagLift_surjective
