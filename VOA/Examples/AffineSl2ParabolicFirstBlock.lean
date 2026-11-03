/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2ParabolicDeterminantBasis
import VOA.Examples.AffineSl2ReflectionFirstForm
import VOA.Examples.AffineSl2KacParabolicCoefficient

/-! # Actual first determinant coefficient for every finite-horizontal quotient -/
namespace VOA.AffineVOA.HighestModule
open Polynomial Matrix
noncomputable section
local instance parabolicFirstFintype (n : ℕ) (c : ℤ) :
    Fintype (Wak.Charged.JointIndex n c) := Wak.Charged.jointIndexFintype n c
local instance parabolicFirstDecidable (n : ℕ) (c : ℤ) :
    DecidableEq (Wak.Charged.JointIndex n c) := Classical.decEq _
local instance parabolicFirstAdaptedDecidable (d n : ℕ) (c : ℤ) :
    DecidableEq (ParabolicAdaptedIndex d n c) := Classical.decEq _

private theorem determinant_decidable_irrel {ι : Type*} [Fintype ι]
    {R : Type*} [CommRing R] (d₁ d₂ : DecidableEq ι) (M : Matrix ι ι R) :
    @Matrix.det ι d₁ _ R _ M = @Matrix.det ι d₂ _ R _ M := by
  have hd : d₁ = d₂ := Subsingleton.elim _ _
  cases hd
  rfl

/-- Center the true adapted Gram matrix at its horizontal singular weight. -/
def parabolicCenteredGram (k : ℂ) (d n : ℕ) (c : ℤ) :
    Matrix (ParabolicAdaptedIndex d n c) (ParabolicAdaptedIndex d n c) ℂ[X] :=
  (parabolicAdaptedGram k d n c).map (fun p => p.comp (X+Polynomial.C (d : ℂ)))

/-- Its constant left block is the actual quotient form in the chosen lifted basis. -/
def parabolicQuotientGram (k : ℂ) (d n : ℕ) (c : ℤ) :
    Matrix (Fin (Module.finrank ℂ (parabolicJointSpace 1 d n c)))
      (Fin (Module.finrank ℂ (parabolicJointSpace 1 d n c))) ℂ :=
  fun i j => contravariant k d (parabolicAdaptedFamilyBasis k d d n c (Sum.inl i))
    (parabolicAdaptedFamilyBasis k d d n c (Sum.inl j))

theorem parabolicCenteredGram_eval (k h : ℂ) (d n : ℕ) (c : ℤ)
    (i j : ParabolicAdaptedIndex d n c) :
    (parabolicCenteredGram k d n c i j).eval h =
      contravariant k (h+(d : ℂ))
        (parabolicAdaptedFamilyBasis k (h+(d : ℂ)) d n c i)
        (parabolicAdaptedFamilyBasis k (h+(d : ℂ)) d n c j) := by
  simp only [parabolicCenteredGram,Matrix.map_apply,eval_comp,eval_add,eval_X,eval_C]
  exact parabolicAdaptedGram_eval k _ d n c i j

/-- Every reflected row vanishes to order at least one. -/
theorem parabolicCenteredGram_row_zero (k : ℂ) (d n : ℕ) (c : ℤ)
    (i : Wak.Charged.JointIndex n (c+(d : ℤ)+1)) (j : ParabolicAdaptedIndex d n c) :
    (parabolicCenteredGram k d n c (Sum.inr i) j).coeff 0 = 0 := by
  rw [coeff_zero_eq_eval_zero,parabolicCenteredGram_eval]
  rw [show (0 : ℂ)+(d : ℂ)=(d : ℂ) from zero_add _]
  rw [parabolicAdaptedFamilyBasis_right,← horizontalReflection_indexedWord,
    horizontalReflection_radical]
  rfl

theorem parabolicCenteredGram_cross_zero (k : ℂ) (d n : ℕ) (c : ℤ)
    (i : Fin (Module.finrank ℂ (parabolicJointSpace 1 d n c)))
    (j : Wak.Charged.JointIndex n (c+(d : ℤ)+1)) :
    (parabolicCenteredGram k d n c (Sum.inl i) (Sum.inr j)).coeff 0 = 0 := by
  rw [coeff_zero_eq_eval_zero,parabolicCenteredGram_eval]
  rw [show (0 : ℂ)+(d : ℂ)=(d : ℂ) from zero_add _]
  rw [contravariant_symm,parabolicAdaptedFamilyBasis_right,
    ← horizontalReflection_indexedWord,horizontalReflection_radical]
  rfl

/-- The polynomial right block is precisely the centered reflected pairing. -/
theorem parabolicCenteredGram_right (k : ℂ) (d n : ℕ) (c : ℤ)
    (i j : Wak.Charged.JointIndex n (c+(d : ℤ)+1)) :
    parabolicCenteredGram k d n c (Sum.inr i) (Sum.inr j) =
      reflectionPairPolynomial k d i.val.toMultiset.toList
        ((j.val.toMultiset.toList ++ List.replicate (d+1) (1,0)).map Wak.Charged.lowerLetter) := by
  apply Polynomial.funext
  intro h
  rw [parabolicCenteredGram_eval,reflectionPairPolynomial_eval,
    parabolicAdaptedFamilyBasis_right,parabolicAdaptedFamilyBasis_right]
  rfl

/-- Exact first-order reflected Gram block, with its factorial multiplier. -/
theorem parabolicCenteredGram_first (k : ℂ) (d n : ℕ) (c : ℤ)
    (i j : Wak.Charged.JointIndex n (c+(d : ℤ)+1)) :
    (parabolicCenteredGram k d n c (Sum.inr i) (Sum.inr j)).coeff 1 =
      reflectionNormScale d * gramMatrix k (-(d : ℂ)-2) n (c+(d : ℤ)+1) i j := by
  rw [parabolicCenteredGram_right,reflectionPairPolynomial_first]
  simp only [gramMatrix,occupationBasis_apply]
  rfl

set_option maxHeartbeats 800000 in
/-- Genuine block extraction: no determinant is defined by a predicted product. -/
theorem parabolicCenteredGram_first_determinant (k : ℂ) (d n : ℕ) (c : ℤ) :
    (parabolicCenteredGram k d n c).det.coeff
        (Fintype.card (Wak.Charged.JointIndex n (c+(d : ℤ)+1))) =
      (parabolicQuotientGram k d n c).det *
        (reflectionNormScale d ^ Fintype.card (Wak.Charged.JointIndex n (c+(d : ℤ)+1)) *
          (weightDeterminant k n (c+(d : ℤ)+1)).eval (-(d : ℂ)-2)) := by
  have hb := PolynomialBlock.det_first_radical_coefficient _
    (parabolicCenteredGram_row_zero k d n c) (parabolicCenteredGram_cross_zero k d n c)
  have hb' : (parabolicCenteredGram k d n c).det.coeff
      (Fintype.card (Wak.Charged.JointIndex n (c+(d : ℤ)+1))) =
      Matrix.det (fun i j => (parabolicCenteredGram k d n c (Sum.inl i) (Sum.inl j)).coeff 0) *
      Matrix.det (fun i j => (parabolicCenteredGram k d n c (Sum.inr i) (Sum.inr j)).coeff 1) := by
    convert hb using 1
    exact congrArg (fun p : ℂ[X] => p.coeff _) (determinant_decidable_irrel _ _ _)
  rw [hb']
  have hl : (fun i j => (parabolicCenteredGram k d n c (Sum.inl i) (Sum.inl j)).coeff 0) =
      parabolicQuotientGram k d n c := by
    ext i j
    rw [coeff_zero_eq_eval_zero,parabolicCenteredGram_eval]
    rw [show (0 : ℂ)+(d : ℂ)=(d : ℂ) from zero_add _]
    rfl
  have hr : (fun i j => (parabolicCenteredGram k d n c (Sum.inr i) (Sum.inr j)).coeff 1) =
      reflectionNormScale d • gramMatrix k (-(d : ℂ)-2) n (c+(d : ℤ)+1) := by
    ext i j
    exact parabolicCenteredGram_first k d n c i j
  rw [hl,hr,Matrix.det_smul]
  congr 2
  change _ = Polynomial.evalRingHom (-(d : ℂ)-2) (weightGramPolynomial k n (c+(d : ℤ)+1)).det
  rw [RingHom.map_det]
  change _ = ((weightGramPolynomial k n (c+(d : ℤ)+1)).map (Polynomial.eval (-(d : ℂ)-2))).det
  rw [weightGramPolynomial_eval]

/-- The actual normalized Verma coefficient equals the actual quotient
form determinant times the full reflected Verma determinant. -/
theorem weightDeterminant_parabolic_block_coefficient (k : ℂ) (d n : ℕ) (c : ℤ) :
    parabolicDeterminantScale d n c *
      ((weightDeterminant k n c).comp (X+Polynomial.C (d : ℂ))).coeff
        (Fintype.card (Wak.Charged.JointIndex n (c+(d : ℤ)+1))) =
      (parabolicQuotientGram k d n c).det *
        (reflectionNormScale d ^ Fintype.card (Wak.Charged.JointIndex n (c+(d : ℤ)+1)) *
          (weightDeterminant k n (c+(d : ℤ)+1)).eval (-(d : ℂ)-2)) := by
  have he := parabolicCenteredGram_first_determinant k d n c
  have hd : (parabolicCenteredGram k d n c).det =
      (parabolicAdaptedGram k d n c).det.comp (X+Polynomial.C (d : ℂ)) :=
    ((Polynomial.compRingHom (X+Polynomial.C (d : ℂ))).map_det _).symm
  rw [hd,parabolicAdaptedGram_det,mul_comp,C_comp,coeff_C_mul] at he
  exact he

/-- Complete scalar cancellation identity against the explicit Kac product. -/
theorem parabolic_determinant_identity (k : ℂ) (d n : ℕ) (c : ℤ) :
    (parabolicQuotientGram k d n c).det *
        (reflectionNormScale d ^ Fintype.card (Wak.Charged.JointIndex n (c+(d : ℤ)+1)) *
          (weightDeterminant k n (c+(d : ℤ)+1)).eval (-(d : ℂ)-2)) =
      parabolicDeterminantScale d n c *
        ((Wak.Charged.affineLeadingPolynomial n c).eval k *
          (Wak.Charged.affineParabolicProduct d n c).eval k) := by
  rw [← weightDeterminant_parabolic_block_coefficient]
  congr 1
  simpa only [Nat.cast_add,Nat.cast_one,add_assoc] using
    Wak.Charged.weightDeterminant_parabolic_coefficient_all k d n c

end
end VOA.AffineVOA.HighestModule
