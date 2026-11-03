import VOA.DeligneAudit.D4LeviKSRzGeneralSpan

/-! Orbit monomials span orbit sums of arbitrary mode polynomials. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial

noncomputable def rzOrbitMonomialSpan (σ : Type*) [Fintype σ] :
    Submodule ℂ (MvPolynomial σ ℂ) :=
  Submodule.span ℂ {Q | ∃ d : σ → ℕ,
    Q = rzOrbitSum σ (∏ i : σ, X i ^ d i)}

theorem rzOrbitSum_smul (σ : Type*) [Fintype σ]
    (t : ℂ) (P : MvPolynomial σ ℂ) :
    rzOrbitSum σ (t • P) = t • rzOrbitSum σ P := by
  classical
  simp [rzOrbitSum, Finset.smul_sum]

theorem rzOrbitSum_add (σ : Type*) [Fintype σ]
    (P Q : MvPolynomial σ ℂ) :
    rzOrbitSum σ (P + Q) = rzOrbitSum σ P + rzOrbitSum σ Q := by
  classical
  simp [rzOrbitSum, Finset.sum_add_distrib]

theorem rzOrbitSum_eq_card_smul_of_symmetric
    (σ : Type*) [Fintype σ] (P : MvPolynomial σ ℂ)
    (hP : P ∈ symmetricSubalgebra σ ℂ) :
    rzOrbitSum σ P = (Nat.card (Equiv.Perm σ) : ℂ) • P := by
  classical
  have hs : P.IsSymmetric := hP
  calc
    rzOrbitSum σ P = ∑ _e : Equiv.Perm σ, P := by
      apply Finset.sum_congr rfl
      intro e he
      exact hs e
    _ = (Nat.card (Equiv.Perm σ) : ℂ) • P := by
      simp [Nat.card_eq_fintype_card, MvPolynomial.smul_eq_C_mul]

theorem rzOrbitSum_mem_monomialSpan (σ : Type*) [Fintype σ]
    (P : MvPolynomial σ ℂ) :
    rzOrbitSum σ P ∈ rzOrbitMonomialSpan σ := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial a t =>
      have hp : (monomial a t : MvPolynomial σ ℂ) =
          t • ∏ i : σ, X i ^ a i := by
        rw [MvPolynomial.prod_X_pow]
        have hfs : Finsupp.indicator Finset.univ
            (fun i _ => a i) = a := by
          ext i
          simp [Finsupp.indicator]
        rw [hfs]
        simp only [smul_monomial, smul_eq_mul, mul_one]
      rw [hp]
      have hgen : rzOrbitSum σ (∏ i : σ, X i ^ a i) ∈
          rzOrbitMonomialSpan σ :=
        Submodule.subset_span ⟨(fun i => a i), rfl⟩
      convert (rzOrbitMonomialSpan σ).smul_mem t hgen using 1
      simp [rzOrbitSum, Finset.smul_sum]
  | add P Q hP hQ =>
      have hsum : rzOrbitSum σ (P + Q) =
          rzOrbitSum σ P + rzOrbitSum σ Q := by
        simp [rzOrbitSum, Finset.sum_add_distrib]
      rw [hsum]
      exact (rzOrbitMonomialSpan σ).add_mem hP hQ

theorem rz_symmetric_mem_orbitMonomialSpan
    (σ : Type*) [Fintype σ] (P : MvPolynomial σ ℂ)
    (hP : P ∈ symmetricSubalgebra σ ℂ) :
    P ∈ rzOrbitMonomialSpan σ := by
  classical
  have hs : P.IsSymmetric := hP
  have horbit : rzOrbitSum σ P =
      (Nat.card (Equiv.Perm σ) : ℂ) • P := by
    calc
      rzOrbitSum σ P = ∑ _e : Equiv.Perm σ, P := by
        apply Finset.sum_congr rfl
        intro e he
        exact hs e
      _ = (Nat.card (Equiv.Perm σ) : ℂ) • P := by
        simp [Nat.card_eq_fintype_card, MvPolynomial.smul_eq_C_mul]
  have hc : (Nat.card (Equiv.Perm σ) : ℂ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt Nat.card_pos)
  have hm : (Nat.card (Equiv.Perm σ) : ℂ) • P ∈
      rzOrbitMonomialSpan σ := by
    rw [← horbit]
    exact rzOrbitSum_mem_monomialSpan σ P
  have hm' := (rzOrbitMonomialSpan σ).smul_mem
    (Nat.card (Equiv.Perm σ) : ℂ)⁻¹ hm
  simpa [smul_smul, inv_mul_cancel₀ hc] using hm'

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.rzOrbitSum_mem_monomialSpan
#print axioms VOA.DeligneAudit.D4Levi.rz_symmetric_mem_orbitMonomialSpan
#print axioms VOA.DeligneAudit.D4Levi.rzOrbitSum_smul
#print axioms VOA.DeligneAudit.D4Levi.rzOrbitSum_add
#print axioms VOA.DeligneAudit.D4Levi.rzOrbitSum_eq_card_smul_of_symmetric
