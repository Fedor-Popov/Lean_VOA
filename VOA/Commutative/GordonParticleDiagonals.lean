/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Commutative.GordonParticlePolynomial

/-! # Actual relation diagonals with arbitrary spectator variables -/

namespace VOA.GordonParticleDiagonals

noncomputable section
open VOA.GordonFunctionalCoefficients VOA.GordonParticlePolynomial VOA.BoundaryAuxiliary
open MvPolynomial
open scoped BigOperators
variable {K α β : Type*} [Field K]
theorem sumToIter_monomial_sumElim_aux (r : α →₀ ℕ) (s : β →₀ ℕ) (c : K) :
  sumToIter K α β (monomial (r.mapDomain Sum.inl + s.mapDomain Sum.inr) c) =
    monomial r (monomial s c) := by
  classical
  have hl (p : MvPolynomial α K) : sumToIter K α β (rename Sum.inl p) = map MvPolynomial.C p := by
    have hh : (sumToIter K α β).comp (rename Sum.inl).toRingHom =
        (map MvPolynomial.C : MvPolynomial α K →+* MvPolynomial α (MvPolynomial β K)) := by
      apply MvPolynomial.ringHom_ext
      · intro c; simp
      · intro i; simp
    exact DFunLike.congr_fun hh p
  have hr (p : MvPolynomial β K) : sumToIter K α β (rename Sum.inr p) = MvPolynomial.C p := by
    have hh : (sumToIter K α β).comp (rename Sum.inr).toRingHom =
        (MvPolynomial.C : MvPolynomial β K →+* MvPolynomial α (MvPolynomial β K)) := by
      apply MvPolynomial.ringHom_ext
      · intro c; simp
      · intro i; simp
    exact DFunLike.congr_fun hh p
  have hm : monomial (r.mapDomain Sum.inl + s.mapDomain Sum.inr) c =
      rename Sum.inl (monomial r (1 : K)) * rename Sum.inr (monomial s c) := by
    simp [rename_monomial, monomial_mul]
  rw [hm, map_mul, hl, hr, map_monomial]
  simp only [map_one]
  change monomial r 1 * monomial 0 (monomial s c) = _
  rw [monomial_mul]
  simp

theorem coeff_coeff_sumToIter (p : MvPolynomial (α ⊕ β) K) (r : α →₀ ℕ) (s : β →₀ ℕ) :
    coeff s (coeff r (sumToIter K α β p)) = coeff (r.sumElim s) p := by
  classical
  have heq (r₁ r₂ : α →₀ ℕ) (s₁ s₂ : β →₀ ℕ) :
      r₁.sumElim s₁ = r₂.sumElim s₂ ↔ r₁ = r₂ ∧ s₁ = s₂ := by
    constructor
    · intro h
      constructor
      · simpa using congrArg (fun d : α ⊕ β →₀ ℕ ↦ d.comapDomain Sum.inl Sum.inl_injective.injOn) h
      · simpa using congrArg (fun d : α ⊕ β →₀ ℕ ↦ d.comapDomain Sum.inr Sum.inr_injective.injOn) h
    · rintro ⟨rfl, rfl⟩; rfl
  induction p using MvPolynomial.induction_on' with
  | monomial d c =>
    let d₁ := d.comapDomain Sum.inl Sum.inl_injective.injOn
    let d₂ := d.comapDomain Sum.inr Sum.inr_injective.injOn
    have hd : d = d₁.sumElim d₂ := (Finsupp.comapDomain_sumElim_comapDomain d).symm
    rw [hd, Finsupp.sumElim_eq_add, sumToIter_monomial_sumElim_aux]
    rw [← Finsupp.sumElim_eq_add]
    simp only [coeff_monomial, heq]
    split_ifs <;> simp_all
  | add p q hp hq => simp [hp, hq]

variable [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- Multiply by a fixed spectator before applying the jet functional. -/
def spectatorFunctional (L : VOA.BoundaryAuxiliary.JetPoly K →ₗ[K] K)
    (q : VOA.BoundaryAuxiliary.JetPoly K) : VOA.BoundaryAuxiliary.JetPoly K →ₗ[K] K where
  toFun p := L (q * p)
  map_add' p r := by simp [mul_add]
  map_smul' c p := by simp [mul_smul_comm]

/-- Taking one spectator coefficient leaves the ordinary polynomial for the remaining
particles, at exactly the residual derivative degree. -/
theorem particlePolynomial_coefficientSlice (D : ℕ)
    (L : VOA.BoundaryAuxiliary.JetPoly K →ₗ[K] K)
    (a : α → Fin 3) (b : β → Fin 3) (r : α →₀ ℕ) :
    coeff r (sumToIter K α β (particlePolynomial D L (Sum.elim a b))) =
      if r.degree ≤ D then
        particlePolynomial (D - r.degree)
          (spectatorFunctional L (∏ i, X (a i, r i))) b else 0 := by
  classical
  ext s
  rw [coeff_coeff_sumToIter, coeff_particlePolynomial]
  have hdeg : (r.sumElim s).degree = r.degree + s.degree := by
    rw [Finsupp.sumElim_eq_add, map_add, Finsupp.degree_mapDomain, Finsupp.degree_mapDomain]
  rw [hdeg]
  simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr,
    Finsupp.sumElim_inl, Finsupp.sumElim_inr]
  by_cases hr : r.degree ≤ D
  · rw [if_pos hr, coeff_particlePolynomial]
    have heq : r.degree + s.degree = D ↔ s.degree = D - r.degree := by omega
    simp only [heq, spectatorFunctional, LinearMap.coe_mk, AddHom.coe_mk]
  · rw [if_neg hr, coeff_zero]
    have hn : r.degree + s.degree ≠ D := by omega
    rw [if_neg hn]

/-- Literal partial diagonal: relation variables coincide, while every spectator remains
an independent variable. -/
def relationDiagonalEval (m : ℕ) :
    MvPolynomial (α ⊕ RelationSlots m) K →+* MvPolynomial α (Polynomial K) :=
  (MvPolynomial.map (eval₂Hom Polynomial.C (fun _ : RelationSlots m ↦ Polynomial.X))).comp
    (sumToIter K α (RelationSlots m))

/-- Every fixed-degree ordinary particle polynomial dual to the auxiliary quotient
vanishes on each defining partial diagonal, with arbitrary spectator variables. -/
theorem particlePolynomial_relationDiagonal_eq_zero (m D : ℕ)
    (L : VOA.BoundaryAuxiliary.JetPoly K →ₗ[K] K)
    (hL : ∀ p ∈ auxiliaryIdeal (R := K) m, L p = 0)
    (a : α → Fin 3) (i : Fin 3) :
    relationDiagonalEval (α := α) m
      (particlePolynomial D L (Sum.elim a (relationColor m i))) = 0 := by
  ext r
  simp only [relationDiagonalEval, RingHom.comp_apply, coeff_map, coeff_zero]
  rw [particlePolynomial_coefficientSlice]
  split_ifs with hr
  · rw [particlePolynomial_fullDiagonal]
    have hzero : diagonalCoefficient
        (spectatorFunctional L (∏ i, X (a i, r i))) (relationColor m i) 1
        (D - r.degree) = 0 := by
      apply diagonal_eq_zero_of_annihilates
      intro p hp
      apply hL
      exact Ideal.mul_mem_left _ _ hp
    rw [hzero, map_zero, zero_mul]
  · simp

/-- The partial-diagonal vanishing statement for the actual quotient dual. -/
theorem quotient_particlePolynomial_relationDiagonal (m D : ℕ)
    (L : Auxiliary (R := K) m →ₗ[K] K) (a : α → Fin 3) (i : Fin 3) :
    relationDiagonalEval (α := α) m
      (particlePolynomial D (pullbackDual m L) (Sum.elim a (relationColor m i))) = 0 := by
  apply particlePolynomial_relationDiagonal_eq_zero
  intro p hp
  change L (Ideal.Quotient.mk (auxiliaryIdeal (R := K) m) p) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hp, map_zero]

/-- Vanishing on the literal partial diagonal persists under arbitrary assignments
of the spectator coordinates and of the common collision coordinate. -/
theorem eval_eq_zero_of_relationDiagonal {A : Type*} [CommRing A] [Algebra K A]
    (m : ℕ) (F : MvPolynomial (α ⊕ RelationSlots m) K)
    (hF : relationDiagonalEval (α := α) m F = 0) (a : α → A) (t : A) :
    aeval (Sum.elim a (fun _ : RelationSlots m ↦ t)) F = 0 := by
  let E : MvPolynomial α (Polynomial K) →+* A :=
    eval₂Hom (Polynomial.eval₂RingHom (algebraMap K A) t) a
  have hhom : (aeval (Sum.elim a (fun _ : RelationSlots m ↦ t))).toRingHom =
      E.comp (relationDiagonalEval (α := α) m) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [E, relationDiagonalEval]
    · intro j
      cases j <;> simp [E, relationDiagonalEval]
  change (aeval (Sum.elim a (fun _ : RelationSlots m ↦ t))).toRingHom F = 0
  rw [hhom, RingHom.comp_apply, hF, map_zero]

end
end VOA.GordonParticleDiagonals
