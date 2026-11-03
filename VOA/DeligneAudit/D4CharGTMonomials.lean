import VOA.DeligneAudit.D4CharEPieri

/-! Laurent monomial coordinates for GT branching, over an arbitrary coefficient ring. -/

namespace VOA.DeligneAudit.D4Char

open scoped BigOperators

noncomputable section

variable {R : Type*} [CommRing R]

/-- Extend a finite weight by zero in the countable Laurent lattice. -/
def gtExponent {N : ℕ} (lam : Fin N → ℤ) : ℕ →₀ ℤ :=
  ∑ i, Finsupp.single i.val (lam i)

@[simp] theorem gtExponent_apply {N : ℕ} (lam : Fin N → ℤ) (i : Fin N) :
    gtExponent lam i.val = lam i := by
  classical
  simp [gtExponent, Finsupp.single_apply, Fin.val_inj]

@[simp] theorem gtExponent_outside {N : ℕ} (lam : Fin N → ℤ) {i : ℕ} (hi : N ≤ i) :
    gtExponent lam i = 0 := by
  classical
  simp only [gtExponent, Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro j _
  exact Finsupp.single_eq_of_ne (by omega)

/-- Sum of the first k Laurent exponents. -/
def gtPrefix (a : ℕ →₀ ℤ) (k : ℕ) : ℤ := ∑ i ∈ Finset.range k, a i

@[simp] theorem gtPrefix_zero (a : ℕ →₀ ℤ) : gtPrefix a 0 = 0 := by
  simp [gtPrefix]

@[simp] theorem gtPrefix_succ (a : ℕ →₀ ℤ) (k : ℕ) :
    gtPrefix a (k + 1) = gtPrefix a k + a k := Finset.sum_range_succ ..

@[simp] theorem gtPrefix_add (a b : ℕ →₀ ℤ) (k : ℕ) :
    gtPrefix (a + b) k = gtPrefix a k + gtPrefix b k := by
  simp [gtPrefix, Finset.sum_add_distrib]

@[simp] theorem gtPrefix_neg (a : ℕ →₀ ℤ) (k : ℕ) :
    gtPrefix (-a) k = -gtPrefix a k := by simp [gtPrefix]

@[simp] theorem gtPrefix_single_of_le (i k : ℕ) (d : ℤ) (h : k ≤ i) :
    gtPrefix (Finsupp.single i d) k = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro j hj
  exact Finsupp.single_eq_of_ne (by simp only [Finset.mem_range] at hj; omega)

@[simp] theorem gtPrefix_exponent {N : ℕ} (lam : Fin N → ℤ) :
    gtPrefix (gtExponent lam) N = ∑ i, lam i := by
  rw [gtPrefix, ← Fin.sum_univ_eq_sum_range]
  simp

/-- GT recursion written using single Laurent monomials. -/
def gtPoly (q : R) : (N : ℕ) → (Fin N → ℤ) → AddMonoidAlgebra R (ℕ →₀ ℤ)
  | 0, _ => 1
  | N + 1, lam => ∑ μ ∈ gtRows lam,
      AddMonoidAlgebra.single (Finsupp.single N ((∑ i, lam i) - ∑ i, μ i))
        (gtPsi q lam μ) * gtPoly q N μ

/-- The coefficient of a branch is a translated coefficient of its shorter row. -/
theorem gtPoly_coeff_succ (q : R) (N : ℕ) (lam : Fin (N + 1) → ℤ) (a : ℕ →₀ ℤ) :
    gtPoly q (N + 1) lam a = ∑ μ ∈ gtRows lam,
      gtPsi q lam μ * gtPoly q N μ
        (-Finsupp.single N ((∑ i, lam i) - ∑ i, μ i) + a) := by
  classical
  change (gtPoly q (N + 1) lam).coeff a = _
  simp only [gtPoly, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  simp only [AddMonoidAlgebra.coeff, AddMonoidAlgebra.single_mul_apply]

/-- A formal Laurent variable over any coefficient ring. -/
def gtLaurentVariable (R : Type*) [CommRing R] (i : ℕ) :
    (AddMonoidAlgebra R (ℕ →₀ ℤ))ˣ where
  val := AddMonoidAlgebra.single (Finsupp.single i 1) 1
  inv := AddMonoidAlgebra.single (Finsupp.single i (-1)) 1
  val_inv := by simp [AddMonoidAlgebra.single_mul_single]; rfl
  inv_val := by simp [AddMonoidAlgebra.single_mul_single]; rfl

theorem gtLaurentVariable_zpow (i : ℕ) (d : ℤ) :
    (((gtLaurentVariable R i) ^ d : (AddMonoidAlgebra R (ℕ →₀ ℤ))ˣ) :
      AddMonoidAlgebra R (ℕ →₀ ℤ)) =
        AddMonoidAlgebra.single (Finsupp.single i d) 1 := by
  cases d with
  | ofNat n => simp [gtLaurentVariable, AddMonoidAlgebra.single_pow]
  | negSucc n =>
      rw [show Int.negSucc n = -((n + 1 : ℕ) : ℤ) by omega, zpow_neg, zpow_natCast,
        ← inv_pow]
      change (AddMonoidAlgebra.single (Finsupp.single i (-1)) (1 : R)) ^ (n + 1) = _
      rw [AddMonoidAlgebra.single_pow, one_pow]
      congr 1
      ext j
      simp only [Finsupp.smul_apply, Finsupp.single_apply, nsmul_eq_mul]
      split_ifs <;> simp

/-- This monomial recursion is the existing GT evaluation, without a change of definition. -/
theorem gtPoly_eq_gtEval (q : R) (N : ℕ) (lam : Fin N → ℤ) :
    gtPoly q N lam = gtEval (AddMonoidAlgebra.single 0 q)
      (gtLaurentVariable R) N lam := by
  induction N with
  | zero => rfl
  | succ N ih =>
      rw [gtPoly, gtEval]
      apply Finset.sum_congr rfl
      intro μ _
      rw [ih, gtLaurentVariable_zpow]
      have h : gtPsi (AddMonoidAlgebra.single 0 q : AddMonoidAlgebra R (ℕ →₀ ℤ))
          lam μ = AddMonoidAlgebra.single 0 (gtPsi q lam μ) := by
        symm
        exact (show _ from map_prod
          (AddMonoidAlgebra.singleZeroRingHom : R →+* AddMonoidAlgebra R (ℕ →₀ ℤ))
          _ _).trans (by simp [gtPsi, A2.map_qbinom])
      rw [h, AddMonoidAlgebra.single_mul_single, zero_add, mul_one]

/-- Specialization identifies the monomial recursion with the original `gtP`. -/
theorem gtPoly_X_eq_gtP (N : ℕ) (lam : Fin N → ℤ) :
    gtPoly (Polynomial.X : Polynomial ℤ) N lam = gtP N lam :=
  gtPoly_eq_gtEval _ _ _

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.gtPoly_coeff_succ
#print axioms VOA.DeligneAudit.D4Char.gtPoly_eq_gtEval
#print axioms VOA.DeligneAudit.D4Char.gtPoly_X_eq_gtP
