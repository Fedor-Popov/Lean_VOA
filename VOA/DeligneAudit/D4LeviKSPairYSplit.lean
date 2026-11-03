import VOA.DeligneAudit.D4LeviKSPairYEmbedding

/-! Split the PAIR source polynomial into Y coefficients and XZ polynomials. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial

def pairSplitVariables (a b c : ℕ) :
    PairSource a b c ≃ Fin b ⊕ PairXZ a b c where
  toFun
    | Sum.inl x => Sum.inr (Sum.inl x)
    | Sum.inr (Sum.inl y) => Sum.inl y
    | Sum.inr (Sum.inr z) => Sum.inr (Sum.inr z)
  invFun
    | Sum.inl y => Sum.inr (Sum.inl y)
    | Sum.inr (Sum.inl x) => Sum.inl x
    | Sum.inr (Sum.inr z) => Sum.inr (Sum.inr z)
  left_inv := by
    intro t
    rcases t with x | (y | z) <;> rfl
  right_inv := by
    intro t
    rcases t with y | (x | z) <;> rfl

noncomputable def pairSplitAlgebra (a b c : ℕ) :
    MvPolynomial (PairSource a b c) ℂ ≃ₐ[ℂ]
      MvPolynomial (Fin b) (MvPolynomial (PairXZ a b c) ℂ) :=
  (renameEquiv ℂ (pairSplitVariables a b c)).trans
    (sumAlgEquiv ℂ (Fin b) (PairXZ a b c))

theorem pairSplitAlgebra_y (a b c : ℕ) (y : Fin b) :
    pairSplitAlgebra a b c (X (Sum.inr (Sum.inl y))) = X y := by
  simp [pairSplitAlgebra, pairSplitVariables, sumToIter_Xl]

theorem pairSplitAlgebra_xz (a b c : ℕ)
    (Q : MvPolynomial (PairXZ a b c) ℂ) :
    pairSplitAlgebra a b c (rename (pairXZSource a b c) Q) =
      MvPolynomial.C Q := by
  have hC (z : ℂ) :
      pairSplitAlgebra a b c
          (rename (pairXZSource a b c) (MvPolynomial.C z)) =
        MvPolynomial.C (MvPolynomial.C z) := by
    simp [pairSplitAlgebra]
  have hX (t : PairXZ a b c) :
      pairSplitAlgebra a b c
          (rename (pairXZSource a b c) (X t)) =
        MvPolynomial.C (X t) := by
    rcases t with (y | x) | z <;>
      simp [pairSplitAlgebra, pairXZSource, pairSplitVariables,
        sumToIter_Xr]
  have hC' (z : ℂ) :
      pairSplitAlgebra a b c (MvPolynomial.C z) =
        MvPolynomial.C (MvPolynomial.C z) := by
    simpa only [rename_C] using hC z
  have hX' (t : PairXZ a b c) :
      pairSplitAlgebra a b c (X (pairXZSource a b c t)) =
        MvPolynomial.C (X t) := by
    simpa only [rename_X] using hX t
  induction Q using MvPolynomial.induction_on' with
  | monomial d z =>
      simp [monomial_eq, hC', hX']
  | add Q R ihQ ihR => simp [ihQ, ihR]

noncomputable def pairYFinsuppMonomial (a b c : ℕ) (d : Fin b →₀ ℕ) :
    MvPolynomial (PairSource a b c) ℂ :=
  rename (fun y : Fin b => (Sum.inr (Sum.inl y) : PairSource a b c))
    (monomial d 1)

theorem pairSplitAlgebra_y_monomial (a b c : ℕ) (d : Fin b →₀ ℕ) :
    pairSplitAlgebra a b c (pairYFinsuppMonomial a b c d) =
      monomial d (1 : MvPolynomial (PairXZ a b c) ℂ) := by
  simp [pairYFinsuppMonomial, monomial_eq, pairSplitAlgebra_y]

theorem pairSplitAlgebra_y_xz (a b c : ℕ) (d : Fin b →₀ ℕ)
    (Q : MvPolynomial (PairXZ a b c) ℂ) :
    pairSplitAlgebra a b c
        (pairYFinsuppMonomial a b c d * rename (pairXZSource a b c) Q) =
      monomial d Q := by
  rw [map_mul, pairSplitAlgebra_y_monomial, pairSplitAlgebra_xz]
  rw [mul_comm, C_mul_monomial]
  simp

/-- Every labelled PAIR source polynomial is a finite sum of Y monomials
    with polynomial coefficients in the X and Z slots. -/
theorem pairY_decomposition (a b c : ℕ)
    (P : MvPolynomial (PairSource a b c) ℂ) :
    P = ∑ d ∈ (pairSplitAlgebra a b c P).support,
      pairYFinsuppMonomial a b c d *
        rename (pairXZSource a b c)
          (coeff d (pairSplitAlgebra a b c P)) := by
  apply (pairSplitAlgebra a b c).injective
  simp_rw [map_sum, pairSplitAlgebra_y_xz]
  exact as_sum (pairSplitAlgebra a b c P)

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.pairSplitAlgebra_y
#print axioms VOA.DeligneAudit.D4Levi.pairSplitAlgebra_xz
#print axioms VOA.DeligneAudit.D4Levi.pairSplitAlgebra_y_monomial
#print axioms VOA.DeligneAudit.D4Levi.pairSplitAlgebra_y_xz
#print axioms VOA.DeligneAudit.D4Levi.pairY_decomposition
