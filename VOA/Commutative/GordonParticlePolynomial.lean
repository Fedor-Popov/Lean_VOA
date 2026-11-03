/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Commutative.GordonFunctionalCoefficients
import VOA.Commutative.MvPolynomialFiniteHomogeneous

/-! # Polynomial realization of ordinary particle coefficients in fixed degree -/

namespace VOA.GordonParticlePolynomial

open scoped BigOperators
open MvPolynomial VOA.GordonFunctionalCoefficients

noncomputable section

variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

/-- The finite set of labeled exponent tuples of total derivative degree `D`. -/
def degreeFiber (D : ℕ) : Finset (ι →₀ ℕ) :=
  ((Finsupp.finite_of_degree_le D).subset (show
    {r : ι →₀ ℕ | r.degree = D} ⊆ {r : ι →₀ ℕ | r.degree ≤ D}
    from fun _ h ↦ h.le)).toFinset

@[simp] theorem mem_degreeFiber (D : ℕ) (r : ι →₀ ℕ) :
    r ∈ degreeFiber (ι := ι) D ↔ r.degree = D := by
  simp [degreeFiber]

/-- The actual homogeneous particle polynomial attached to an ordinary jet functional. -/
def particlePolynomial (D : ℕ) (L : VOA.BoundaryAuxiliary.JetPoly K →ₗ[K] K)
    (color : ι → Fin 3) : MvPolynomial ι K :=
  ∑ r ∈ degreeFiber D, monomial r (particleCoefficient L color 1 r)

@[simp] theorem coeff_particlePolynomial (D : ℕ)
    (L : VOA.BoundaryAuxiliary.JetPoly K →ₗ[K] K) (color : ι → Fin 3) (r : ι →₀ ℕ) :
    coeff r (particlePolynomial D L color) =
      if r.degree = D then L (∏ i, X (color i, r i)) else 0 := by
  classical
  simp [particlePolynomial, coeff_sum, coeff_monomial, particleCoefficient]

theorem particlePolynomial_homogeneous (D : ℕ)
    (L : VOA.BoundaryAuxiliary.JetPoly K →ₗ[K] K) (color : ι → Fin 3) :
    (particlePolynomial D L color).IsHomogeneous D := by
  apply IsHomogeneous.sum
  intro r hr
  exact isHomogeneous_monomial _ ((mem_degreeFiber D r).mp hr)

/-- The polynomial coefficient at a tuple changes equivariantly under relabeling. -/
theorem modeProduct_mapDomain (color : ι → Fin 3) (r : ι →₀ ℕ)
    (e : Equiv.Perm ι) (he : ∀ i, color (e i) = color i) :
    (∏ i, (X (color i, r.mapDomain e i) : VOA.BoundaryAuxiliary.JetPoly K)) =
      ∏ i, X (color i, r i) := by
  symm
  apply Fintype.prod_equiv e
  intro i
  simp [Finsupp.mapDomain_apply, he]

/-- The polynomial realization is separately symmetric, in the literal sense of
invariance under every color-preserving permutation of the labeled particles. -/
theorem particlePolynomial_rename (D : ℕ)
    (L : VOA.BoundaryAuxiliary.JetPoly K →ₗ[K] K) (color : ι → Fin 3)
    (e : Equiv.Perm ι) (he : ∀ i, color (e i) = color i) :
    rename e (particlePolynomial D L color) = particlePolynomial D L color := by
  apply MvPolynomial.ext
  intro r
  obtain ⟨s, rfl⟩ := (Finsupp.mapDomain_surjective e.surjective) r
  rw [coeff_rename_mapDomain e e.injective]
  simp only [coeff_particlePolynomial, Finsupp.degree_mapDomain,
    modeProduct_mapDomain color s e he]

/-- Changing the finite particle-label type preserves the literal polynomial realization. -/
theorem particlePolynomial_rename_equiv {κ : Type*} [Fintype κ] [DecidableEq κ]
    (D : ℕ) (L : VOA.BoundaryAuxiliary.JetPoly K →ₗ[K] K)
    (color : ι → Fin 3) (other : κ → Fin 3) (e : ι ≃ κ)
    (he : ∀ i, other (e i) = color i) :
    rename e (particlePolynomial D L color) = particlePolynomial D L other := by
  apply MvPolynomial.ext
  intro r
  obtain ⟨s, rfl⟩ := (Finsupp.mapDomain_surjective e.surjective) r
  rw [coeff_rename_mapDomain e e.injective]
  simp only [coeff_particlePolynomial, Finsupp.degree_mapDomain]
  congr 2
  apply Fintype.prod_equiv e
  intro i
  simp [he]

/-- The actual ordinary polynomial realization is linear in the functional. -/
def particlePolynomialLinear (D : ℕ) (color : ι → Fin 3) :
    (VOA.BoundaryAuxiliary.JetPoly K →ₗ[K] K) →ₗ[K] MvPolynomial ι K where
  toFun L := particlePolynomial D L color
  map_add' L M := by
    ext r
    simp only [coeff_particlePolynomial, LinearMap.add_apply, coeff_add]
    split_ifs <;> simp
  map_smul' c L := by
    ext r
    simp only [coeff_particlePolynomial, LinearMap.smul_apply, coeff_smul]
    split_ifs <;> simp

/-- The exponent fiber is exactly the ordered antidiagonal used in ordinary series products. -/
theorem degreeFiber_eq_finsuppAntidiag (D : ℕ) :
    degreeFiber (ι := ι) D = Finset.finsuppAntidiag Finset.univ D := by
  ext r
  simp only [mem_degreeFiber, Finset.mem_finsuppAntidiag, Finset.subset_univ, and_true]
  change r.sum (fun _ n ↦ n) = D ↔ _
  rw [Finsupp.sum_fintype]
  intro _; rfl

/-- Identifying every particle coordinate produces the literal ordered diagonal coefficient. -/
theorem particlePolynomial_fullDiagonal (D : ℕ)
    (L : VOA.BoundaryAuxiliary.JetPoly K →ₗ[K] K) (color : ι → Fin 3) :
    eval₂Hom Polynomial.C (fun _ : ι ↦ Polynomial.X) (particlePolynomial D L color) =
      Polynomial.C (diagonalCoefficient L color 1 D) * Polynomial.X ^ D := by
  unfold particlePolynomial
  rw [map_sum]
  have hterm : ∀ r ∈ degreeFiber (ι := ι) D,
      eval₂Hom Polynomial.C (fun _ : ι ↦ Polynomial.X)
        (monomial r (particleCoefficient L color 1 r)) =
      Polynomial.C (particleCoefficient L color 1 r) * Polynomial.X ^ D := by
    intro r hr
    rw [eval₂Hom_monomial]
    congr 1
    rw [Finsupp.prod, Finset.prod_pow_eq_pow_sum]
    congr 1
    exact (mem_degreeFiber D r).mp hr
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, ← map_sum]
  rw [degreeFiber_eq_finsuppAntidiag]
  rfl

/-- Actual particle polynomials coming from the auxiliary quotient vanish on each
of the three defining coincidence diagonals when there are no spectator variables. -/
theorem quotient_particlePolynomial_relationDiagonal (m D : ℕ)
    (L : VOA.BoundaryAuxiliary.Auxiliary (R := K) m →ₗ[K] K) (i : Fin 3) :
    eval₂Hom Polynomial.C (fun _ : RelationSlots m ↦ Polynomial.X)
      (particlePolynomial D (pullbackDual m L) (relationColor m i)) = 0 := by
  rw [particlePolynomial_fullDiagonal, pullbackDual_diagonal_eq_zero, map_zero, zero_mul]

end
end VOA.GordonParticlePolynomial
