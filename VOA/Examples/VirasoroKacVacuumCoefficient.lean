/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroTranslationFirstForm
import VOA.Examples.VirasoroKacSmallLabels

/-!
# Removing the universal translation factor from the Kac product

The (1,1) highest weight is identically zero. At level n+1 its factor is
exactly X to the number of level-n Verma partitions. Removing it gives a
finite scalar product for the first possible determinant coefficient.
The actual determinant comparison is conditional here on ordinary singular
existence; the singular states are constructed in `VirasoroScreeningKacRoots.lean`.
-/
namespace VOA.InverseDS.VirasoroVerma
open VirModule Polynomial
open scoped Classical

/-- The Kac product with the universal (1,1) translation label removed. -/
noncomputable def kacWithoutTranslation (t : ℂ) (n : ℕ) : ℂ[X] :=
  ∏ i ∈ (kacLabels (n+1)).erase (0,0),
    (X - Polynomial.C (fusionKacWeight (i.1.val+1) (i.2.val+1) t)) ^
      Fintype.card (VermaPartitions (n+1-(i.1.val+1)*(i.2.val+1)))

/-- The ordinary scalar remaining after the universal translation factor
is removed and the highest-weight variable is set to zero. -/
noncomputable def kacVacuumScalar (t : ℂ) (n : ℕ) : ℂ :=
  ∏ i ∈ (kacLabels (n+1)).erase (0,0),
    (-fusionKacWeight (i.1.val+1) (i.2.val+1) t) ^
      Fintype.card (VermaPartitions (n+1-(i.1.val+1)*(i.2.val+1)))

/-- The translation label is present at every positive level. -/
theorem kacLabels_translation_mem (n : ℕ) :
    (0,0) ∈ kacLabels (n+1) := by
  simp [kacLabels]

/-- The removed label has identically zero weight, so its entire factor
is exactly the universal power of the highest-weight variable. -/
theorem kacWeightProduct_translation_factor (t : ℂ) (n : ℕ) :
    kacWeightProduct t (n+1) =
      X ^ Fintype.card (VermaPartitions n) * kacWithoutTranslation t n := by
  have he := Finset.mul_prod_erase (kacLabels (n+1))
    (fun i => (X - Polynomial.C (fusionKacWeight (i.1.val+1) (i.2.val+1) t)) ^
      Fintype.card (VermaPartitions (n+1-(i.1.val+1)*(i.2.val+1))))
    (kacLabels_translation_mem n)
  simpa [kacWeightProduct, kacWithoutTranslation, fusionKacWeight] using he.symm

/-- The constant coefficient of the reduced polynomial is its explicit
finite product of negative Kac weights. -/
theorem kacWithoutTranslation_zero (t : ℂ) (n : ℕ) :
    (kacWithoutTranslation t n).coeff 0 = kacVacuumScalar t n := by
  simp [coeff_zero_eq_eval_zero, kacWithoutTranslation, kacVacuumScalar, eval_prod]

/-- Extracting the first possible coefficient discards exactly the
universal translation factor and no other label or multiplicity. -/
theorem kacWeightProduct_first_coefficient (t : ℂ) (n : ℕ) :
    (kacWeightProduct t (n+1)).coeff (Fintype.card (VermaPartitions n)) =
      kacVacuumScalar t n := by
  rw [kacWeightProduct_translation_factor]
  simpa using (coeff_X_pow_mul (kacWithoutTranslation t n)
    (Fintype.card (VermaPartitions n)) 0).trans (kacWithoutTranslation_zero t n)

/-- A full Kac identity on nonreal parameters extends to every nonzero
parameter by continuity of the ACTUAL Gram entries. Colliding nullities are
never added; it is the already established finite polynomial identity that
is specialized. -/
theorem vermaWeightDeterminant_kac_extend (n : ℕ)
    (hs : ∀ z : ℂ, z.im ≠ 0 →
      (vermaWeightGramPolynomial (vermaBSACharge z) n).det =
        Polynomial.C (∏ w : VermaPartitions n, vermaDiagonalContraction w.val) *
          kacWeightProduct z n)
    (t : ℂ) (ht : t ≠ 0) :
    (vermaWeightGramPolynomial (vermaBSACharge t) n).det =
      Polynomial.C (∏ w : VermaPartitions n, vermaDiagonalContraction w.val) *
        kacWeightProduct t n := by
  apply Polynomial.funext
  intro h
  rw [vermaWeightDeterminant_eval, eval_mul, eval_C]
  haveI := mem_closure_iff_nhdsWithin_neBot.mp (VirasoroWardTopology.nonreal_dense t)
  apply tendsto_nhds_unique_of_eventuallyEq (l := nhdsWithin t {z : ℂ | z.im ≠ 0})
    ((vermaKacGramDet_continuousAt n h t ht).tendsto.mono_left nhdsWithin_le_nhds)
    ((continuousAt_const.mul (kacWeightProduct_eval_continuousAt n h t ht)).tendsto.mono_left
      nhdsWithin_le_nhds)
  filter_upwards [self_mem_nhdsWithin] with z hz
  have he := congrArg (Polynomial.eval h) (hs z hz)
  simpa only [vermaWeightDeterminant_eval, eval_mul, eval_C] using he

/-- Once the ordinary Kac polynomial identity is available, its first
coefficient gives the normalized actual vacuum determinant relation. This
uses the proved translation form, not a vacuum character assumption. -/
theorem vacuumDeterminant_kac_coefficient (t : ℂ) (n : ℕ)
    (hk : (vermaWeightGramPolynomial (vermaBSACharge t) (n+1)).det =
      Polynomial.C (∏ w : VermaPartitions (n+1), vermaDiagonalContraction w.val) *
        kacWeightProduct t (n+1)) :
    (2 : ℂ) ^ Fintype.card (VermaPartitions n) *
      ((VirDeformModes.NormalOrdering.partitionGramPolynomial (n+1)).map
        (Polynomial.eval (vermaBSACharge t))).det *
      (vermaGramMatrix (vermaBSACharge t) 1 n).det =
        (∏ w : VermaPartitions (n+1), vermaDiagonalContraction w.val) *
          kacVacuumScalar t n := by
  rw [← vermaWeightDeterminant_vacuum_coefficient, hk, coeff_C_mul,
    kacWeightProduct_first_coefficient]

end VOA.InverseDS.VirasoroVerma
