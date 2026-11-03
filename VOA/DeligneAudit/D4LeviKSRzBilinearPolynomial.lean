import VOA.DeligneAudit.D4LeviKSRzBilinearKernel

/-! Polynomial formula for finite bilinear sums of Rz orbit generators. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial

theorem rzXSeed_finsupp (a b : ℕ)
    (p : Fin b ⊕ Fin a →₀ ℕ) :
    rzXSeed a b (fun i => p i) = monomial p (1 : ℂ) := by
  classical
  rw [rzXSeed, MvPolynomial.prod_X_pow]
  have hfs : Finsupp.indicator Finset.univ
      (fun i _ => p i) = p := by
    ext i
    simp [Finsupp.indicator]
  rw [hfs]

theorem rzZSeed_finsupp (k l s : ℕ) (q : Fin l →₀ ℕ) :
    rzZSeed k l s (fun j => q j) =
      rename (Fin.castAdd l) (hsymm (Fin k) ℂ s) *
        rename (Fin.natAdd k) (monomial q (1 : ℂ)) := by
  classical
  rw [rzZSeed]
  have hfs : Finsupp.indicator Finset.univ
      (fun i _ => q i) = q := by
    ext i
    simp [Finsupp.indicator]
  have hp : (∏ j : Fin l, X (Fin.natAdd k j) ^ q j :
      MvPolynomial (Fin (k + l)) ℂ) =
      rename (Fin.natAdd k) (∏ j : Fin l, X j ^ q j) := by
    simp
  rw [hp, MvPolynomial.prod_X_pow, hfs]

theorem rzOrbitSum_sum (σ ι : Type*) [Fintype σ]
    (s : Finset ι) (f : ι → MvPolynomial σ ℂ) :
    rzOrbitSum σ (∑ i ∈ s, f i) =
      ∑ i ∈ s, rzOrbitSum σ (f i) := by
  classical
  calc
    rzOrbitSum σ (∑ i ∈ s, f i) =
        ∑ e : Equiv.Perm σ, ∑ i ∈ s, rename e (f i) := by
      simp only [rzOrbitSum, map_sum]
    _ = ∑ i ∈ s, ∑ e : Equiv.Perm σ, rename e (f i) :=
      Finset.sum_comm
    _ = ∑ i ∈ s, rzOrbitSum σ (f i) := rfl

theorem rzBilinearTarget_polynomial (a b k l s : ℕ)
    (P : MvPolynomial (Fin b ⊕ Fin a) ℂ)
    (R : MvPolynomial (Fin l) ℂ) :
    (rzBilinearTarget a b k l s P R :
      MvPolynomial (PairTarget a b (k + l)) ℂ) =
      rename (rzXTarget a b (k + l))
          (rzOrbitSum _ P) *
        rename (fun z : Fin (k + l) =>
          (Sum.inr (Sum.inr z) : PairTarget a b (k + l)))
          (rzOrbitSum _
            (rename (Fin.castAdd l) (hsymm (Fin k) ℂ s) *
              rename (Fin.natAdd k) R)) := by
  classical
  conv_rhs => rw [P.as_sum, R.as_sum]
  change (Subalgebra.val (pairTargetSymmetric a b (k + l)))
      (rzBilinearTarget a b k l s P R) = _
  simp only [rzBilinearTarget, rzOrbitSum_sum, map_sum,
    Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  have hX : monomial p (P.coeff p) =
      P.coeff p • rzXSeed a b (fun i => p i) := by
    rw [rzXSeed_finsupp]
    simp only [smul_monomial, smul_eq_mul, mul_one]
  have hR : monomial q (R.coeff q) =
      R.coeff q • monomial q (1 : ℂ) := by
    simp only [smul_monomial, smul_eq_mul, mul_one]
  rw [hX, hR]
  simp only [map_smul, rzOrbitSum_smul, map_smul,
    mul_smul_comm, smul_mul_assoc]
  rw [← rzZSeed_finsupp k l s q]
  rw [smul_smul, mul_comm (R.coeff q) (P.coeff p)]
  exact congrArg ((P.coeff p * R.coeff q) • ·)
    (rzTargetGenerator_polynomial a b k l s
      (fun i => p i) (fun j => q j))

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.rzXSeed_finsupp
#print axioms VOA.DeligneAudit.D4Levi.rzZSeed_finsupp
#print axioms VOA.DeligneAudit.D4Levi.rzOrbitSum_sum
#print axioms VOA.DeligneAudit.D4Levi.rzBilinearTarget_polynomial
