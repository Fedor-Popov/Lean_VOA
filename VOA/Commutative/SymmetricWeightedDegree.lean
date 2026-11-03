/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Commutative.MvPolynomialFiniteHomogeneous
import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem

/-! # Grading in the actual fundamental theorem of symmetric polynomials -/
namespace VOA.SymmetricWeightedDegree
open MvPolynomial
noncomputable section
variable {K I J : Type*} [Field K]

/-- Substitution of homogeneous generators respects their assigned weights. -/
theorem aeval_weightedHomogeneous (w : I → ℕ) (f : I → MvPolynomial J K)
    (hf : ∀ i, (f i).IsHomogeneous (w i)) (p : MvPolynomial I K) (d : ℕ)
    (hp : p.IsWeightedHomogeneous w d) : (aeval f p).IsHomogeneous d := by
  induction hp using IsWeightedHomogeneous.induction_on with
  | zero => simpa using (isHomogeneous_zero J K d)
  | add p q hp hq ihp ihq => simpa using ihp.add ihq
  | monomial e c he =>
    rw [aeval_monomial]
    apply IsHomogeneous.C_mul
    have hh := IsHomogeneous.prod e.support (fun i => f i ^ e i)
      (fun i => w i * e i) (fun i _ => (hf i).pow (e i))
    convert hh using 1
    simpa [Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul, Nat.mul_comm] using he.symm

/-- Extracting weighted degree before substitution is the same as extracting
ordinary degree afterwards. -/
theorem homogeneousComponent_aeval (w : I → ℕ) (f : I → MvPolynomial J K)
    (hf : ∀ i, (f i).IsHomogeneous (w i)) (p : MvPolynomial I K) (d : ℕ) :
    homogeneousComponent d (aeval f p) = aeval f (weightedHomogeneousComponent w d p) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | add p q ihp ihq => simp only [map_add, ihp, ihq]
  | monomial e c =>
    have hp := isWeightedHomogeneous_monomial w e c rfl
    rw [homogeneousComponent_of_mem
      (aeval_weightedHomogeneous w f hf _ _ hp), weightedHomogeneousComponent_of_mem hp]
    split_ifs <;> simp

/-- An injective homogeneous substitution reflects the specified degree. -/
theorem weightedHomogeneous_of_aeval (w : I → ℕ) (f : I → MvPolynomial J K)
    (hf : ∀ i, (f i).IsHomogeneous (w i)) (hinj : Function.Injective (aeval f : MvPolynomial I K →ₐ[K] MvPolynomial J K))
    (p : MvPolynomial I K) (d : ℕ) (hp : (aeval f p).IsHomogeneous d) :
    p.IsWeightedHomogeneous w d := by
  have he := homogeneousComponent_aeval w f hf p d
  rw [homogeneousComponent_of_mem hp, if_pos rfl] at he
  have he' := hinj he
  rw [he']
  exact weightedHomogeneousComponent_isWeightedHomogeneous d p

/-- Elementary symmetric generators have their actual ordinary degrees. -/
theorem esymm_isHomogeneous [Fintype I] (d : ℕ) :
    (esymm I K d).IsHomogeneous d := by
  classical
  apply IsHomogeneous.sum
  intro s hs
  have hcard := (Finset.mem_powersetCard.mp hs).2
  have hh := IsHomogeneous.prod s (fun i : I => X i : I → MvPolynomial I K)
    (fun _ => 1) (fun i _ => isHomogeneous_X K i)
  simpa [hcard] using hh

/-- The elementary-symmetric presentation is graded when its ith source
variable has weight i+1. -/
theorem esymmAlgHom_homogeneous_iff [Fintype I] (n : ℕ) (hn : Fintype.card I = n)
    (p : MvPolynomial (Fin n) K) (d : ℕ) :
    ((esymmAlgHom I K n p).val).IsHomogeneous d ↔
      p.IsWeightedHomogeneous (fun i : Fin n => i.val + 1) d := by
  rw [esymmAlgHom_apply]
  constructor
  · apply weightedHomogeneous_of_aeval
      (fun i : Fin n => i.val + 1) (fun i => esymm I K (i.val + 1))
      (fun i => esymm_isHomogeneous _)
    intro p q hpq
    apply (esymmAlgEquiv I K hn).injective
    apply Subtype.ext
    simpa only [esymmAlgEquiv_apply, esymmAlgHom_apply] using hpq
  · exact aeval_weightedHomogeneous _ _ (fun i => esymm_isHomogeneous _) p d

/-- Symmetric polynomials of one specified ordinary degree. -/
def symmetricPiece [Fintype I] (d : ℕ) : Submodule K (MvPolynomial I K) :=
  (symmetricSubalgebra I K).toSubmodule ⊓ homogeneousSubmodule I K d

/-- The fundamental theorem restricted to one degree is an actual linear
isomorphism, with source generator weights 1 through n. -/
def esymmDegreeEquiv [Fintype I] (n : ℕ) (hn : Fintype.card I = n) (d : ℕ) :
    weightedHomogeneousSubmodule K (fun i : Fin n => i.val + 1) d ≃ₗ[K]
      symmetricPiece (K := K) (I := I) d where
  toFun p := ⟨(esymmAlgHom I K n p.val).val,
    (esymmAlgHom I K n p.val).property,
    (esymmAlgHom_homogeneous_iff n hn p.val d).mpr p.property⟩
  invFun p := ⟨(esymmAlgEquiv I K hn).symm ⟨p.val, p.property.1⟩, by
    apply (esymmAlgHom_homogeneous_iff n hn _ d).mp
    change ((esymmAlgEquiv I K hn)
      ((esymmAlgEquiv I K hn).symm ⟨p.val, p.property.1⟩)).val.IsHomogeneous d
    rw [AlgEquiv.apply_symm_apply]
    exact p.property.2⟩
  left_inv p := by
    apply Subtype.ext
    exact (esymmAlgEquiv I K hn).symm_apply_apply p.val
  right_inv p := by
    apply Subtype.ext
    simpa only [esymmAlgEquiv_apply] using
      congrArg (fun t : symmetricSubalgebra I K => t.val)
        ((esymmAlgEquiv I K hn).apply_symm_apply ⟨p.val, p.property.1⟩)
  map_add' p q := by apply Subtype.ext; simp
  map_smul' c p := by apply Subtype.ext; simp

/-- Weighted polynomial dimension equals the number of monomials of that
weight; no invariant-ring presentation is assumed. -/
theorem weightedPiece_finrank [Finite I] (w : I → ℕ) (hw : ∀ i, w i ≠ 0) (d : ℕ) :
    Module.finrank K (weightedHomogeneousSubmodule K w d) =
      Nat.card {e : I →₀ ℕ // Finsupp.weight w e = d} := by
  letI : Fintype ↥({e : I →₀ ℕ | Finsupp.weight w e = d} : Set (I →₀ ℕ)) :=
    (MvPolynomialFiniteHomogeneous.finite_weightFiber w hw d).fintype
  rw [weightedHomogeneousSubmodule_eq_finsupp_supported]
  exact (Finsupp.supportedEquivFinsupp (M := K) (R := K)
    {e : I →₀ ℕ | Finsupp.weight w e = d}).finrank_eq.trans
      (by
        rw [Module.finrank_finsupp_self]
        exact (Nat.card_eq_fintype_card
          (α := ↥({e : I →₀ ℕ | Finsupp.weight w e = d} : Set (I →₀ ℕ)))).symm)

/-- Symmetric degree-d dimension is the number of weighted generator
monomials of weight d, with weights 1,...,n. -/
theorem symmetricPiece_finrank [Fintype I] (n : ℕ) (hn : Fintype.card I = n) (d : ℕ) :
    Module.finrank K (symmetricPiece (K := K) (I := I) d) =
      Nat.card {e : Fin n →₀ ℕ // Finsupp.weight (fun i : Fin n => i.val + 1) e = d} := by
  rw [← (esymmDegreeEquiv (K := K) (I := I) n hn d).finrank_eq]
  exact weightedPiece_finrank _ (fun i => by omega) d

end
end VOA.SymmetricWeightedDegree
