/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Commutative.BoundaryAuxiliaryInitial

/-! # Ordinary coefficient pairing and the auxiliary relation diagonals

The coefficient at a labeled particle exponent tuple is the value of a linear functional
on the literal product of the corresponding jet generators. Coinciding particle coordinates
sums these coefficients over ordered exponent tuples. The resulting sum is exactly adjoint
to a coefficient of the product of universal current series, including all multiplicities.
-/

namespace VOA.GordonFunctionalCoefficients

open scoped BigOperators
open MvPolynomial VOA.InfiniteJet VOA.BoundaryAuxiliary

noncomputable section

variable {K : Type*} [Field K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Ordinary labeled particle coefficient, with an arbitrary polynomial spectator. -/
def particleCoefficient (L : VOA.BoundaryAuxiliary.JetPoly K →ₗ[K] K)
    (color : ι → Fin 3) (spectator : VOA.BoundaryAuxiliary.JetPoly K) (r : ι →₀ ℕ) : K :=
  L (spectator * ∏ i, X (color i, r i))

/-- Same-species permutations preserve the literal ordinary particle coefficients. -/
theorem particleCoefficient_permute
    (L : VOA.BoundaryAuxiliary.JetPoly K →ₗ[K] K) (color : ι → Fin 3)
    (spectator : VOA.BoundaryAuxiliary.JetPoly K) (r : ι →₀ ℕ)
    (e : Equiv.Perm ι) (he : ∀ i, color (e i) = color i) :
    particleCoefficient L color spectator (r.comapDomain e e.injective.injOn) =
      particleCoefficient L color spectator r := by
  unfold particleCoefficient
  congr 2
  apply Fintype.prod_equiv e
  intro i
  simp only [Finsupp.comapDomain_apply, he]

/-- Coefficient after all the displayed particles coincide at one coordinate. -/
def diagonalCoefficient (L : VOA.BoundaryAuxiliary.JetPoly K →ₗ[K] K)
    (color : ι → Fin 3) (spectator : VOA.BoundaryAuxiliary.JetPoly K) (n : ℕ) : K :=
  ∑ r ∈ Finset.finsuppAntidiag (Finset.univ : Finset ι) n,
    particleCoefficient L color spectator r

/-- The ordinary coefficient pairing turns a literal diagonal into multiplication
by an actual coefficient of the current product. -/
theorem diagonalCoefficient_eq_relationCoefficient
    (L : VOA.BoundaryAuxiliary.JetPoly K →ₗ[K] K) (color : ι → Fin 3)
    (spectator : VOA.BoundaryAuxiliary.JetPoly K) (n : ℕ) :
    diagonalCoefficient L color spectator n =
      L (spectator * relationCoefficient (∏ i, (X (color i) : BasePoly K)) n) := by
  simp only [relationCoefficient, map_prod, aeval_X]
  rw [PowerSeries.coeff_prod]
  simp only [coeff_generatorSeries, Finset.mul_sum, map_sum]
  rfl

/-- One distinguished particle of species `i`, together with `m` e-particles and
`m` f-particles, is the actual auxiliary relation. -/
abbrev RelationSlots (m : ℕ) := Unit ⊕ (Fin m ⊕ Fin m)

def relationColor (m : ℕ) (i : Fin 3) : RelationSlots m → Fin 3 :=
  Sum.elim (fun _ ↦ i) (Sum.elim (fun _ ↦ 0) (fun _ ↦ 2))

theorem relationColor_product (m : ℕ) (i : Fin 3) :
    (∏ j : RelationSlots m, (X (relationColor m i j) : BasePoly K)) =
      auxiliaryRelation m i := by
  simp [relationColor, Fintype.prod_sum_type, auxiliaryRelation, mul_pow]

/-- Literal relation-diagonal coefficients are adjoint to the defining auxiliary
relations, with no factorial rescaling. -/
theorem relation_diagonal_adjoint (m : ℕ) (i : Fin 3)
    (L : VOA.BoundaryAuxiliary.JetPoly K →ₗ[K] K)
    (spectator : VOA.BoundaryAuxiliary.JetPoly K) (n : ℕ) :
    diagonalCoefficient L (relationColor m i) spectator n =
      L (spectator * relationCoefficient (auxiliaryRelation m i) n) := by
  rw [diagonalCoefficient_eq_relationCoefficient, relationColor_product]

/-- Every functional descending to the actual auxiliary arc quotient satisfies
the three relation diagonals, even after arbitrary spectator multiplication. -/
theorem diagonal_eq_zero_of_annihilates (m : ℕ)
    (L : VOA.BoundaryAuxiliary.JetPoly K →ₗ[K] K)
    (hL : ∀ p ∈ auxiliaryIdeal (R := K) m, L p = 0)
    (i : Fin 3) (spectator : VOA.BoundaryAuxiliary.JetPoly K) (n : ℕ) :
    diagonalCoefficient L (relationColor m i) spectator n = 0 := by
  rw [relation_diagonal_adjoint]
  apply hL
  apply Ideal.mul_mem_left
  exact relationCoefficient_mem_coefficientIdeal _ _ (Set.mem_range_self i) n

/-- Conversely, all literal relation diagonals characterize the annihilator of
the actual coefficient ideal. The spectator is arbitrary, so ideal multiples are covered. -/
theorem annihilates_iff_diagonals (m : ℕ)
    (L : VOA.BoundaryAuxiliary.JetPoly K →ₗ[K] K) :
    (∀ p ∈ auxiliaryIdeal (R := K) m, L p = 0) ↔
      ∀ i spectator n, diagonalCoefficient L (relationColor m i) spectator n = 0 := by
  constructor
  · exact diagonal_eq_zero_of_annihilates m L
  · intro h p hp
    have hall : ∀ p ∈ auxiliaryIdeal (R := K) m,
        ∀ q : VOA.BoundaryAuxiliary.JetPoly K, L (q * p) = 0 := by
      intro p hp
      induction hp using Submodule.span_induction with
      | mem p hp =>
        obtain ⟨f, ⟨i, rfl⟩, n, rfl⟩ := hp
        intro q
        exact (relation_diagonal_adjoint m i L q n).symm.trans (h i q n)
      | zero => intro q; simp
      | add p q hp hq ihp ihq => intro r; simp [mul_add, ihp, ihq]
      | smul a p hp ih => intro q; simpa [smul_eq_mul, mul_assoc] using ih (q * a)
    simpa using hall p hp 1

/-- A functional on the actual auxiliary quotient gives a functional on jet polynomials. -/
def pullbackDual (m : ℕ) (L : Auxiliary (R := K) m →ₗ[K] K) :
    VOA.BoundaryAuxiliary.JetPoly K →ₗ[K] K :=
  L.comp (Ideal.Quotient.mkₐ K (auxiliaryIdeal (R := K) m)).toLinearMap

/-- Every ordinary quotient-dual coefficient family satisfies the concrete relation diagonals. -/
theorem pullbackDual_diagonal_eq_zero (m : ℕ) (L : Auxiliary (R := K) m →ₗ[K] K)
    (i : Fin 3) (spectator : VOA.BoundaryAuxiliary.JetPoly K) (n : ℕ) :
    diagonalCoefficient (pullbackDual m L) (relationColor m i) spectator n = 0 := by
  apply diagonal_eq_zero_of_annihilates
  intro p hp
  change L (Ideal.Quotient.mk (auxiliaryIdeal (R := K) m) p) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hp, map_zero]

end
end VOA.GordonFunctionalCoefficients
