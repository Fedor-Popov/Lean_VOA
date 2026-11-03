/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2CentralContractions

/-!
# The ordinary joint affine determinant's candidate leading coefficient

Every column has the PBW-length level-degree bound. The candidate determinant
leading coefficient is therefore a finite determinant of column-top entries.
Those entries vanish for shorter rows, while equal-length entries are computed
exactly by central contractions, including the weight-one adjoint sign. The
nonzero diagonal product and the admissible root factors remain separate tasks.
-/
namespace VOA.AffineVOA.NormalOrdering
open Polynomial

/-- Each actual mode can raise the weighted filtration by at most one, so
a finite prefix raises it by at most its length. No sign condition is needed. -/
theorem applyNormal_mem_contractionFiltration (u : List (Fin 3 × ℤ))
    {d : ℕ} {f : NormalForm} (hf : f ∈ contractionFiltration d) :
    applyNormal u f ∈ contractionFiltration (d+u.length) := by
  induction u with
  | nil => simpa [applyNormal] using hf
  | cons a u ih =>
    simpa only [applyNormal, LinearMap.comp_apply, List.length_cons, Nat.add_assoc] using
      actNormal_mem_contractionFiltration a.1 a.2 ih

/-- A vacuum polynomial coefficient vanishes if its doubled central degree
exceeds the total number of original current letters. -/
theorem pairing_coeff_zero_of_total_length (u : List (Fin 3 × ℤ))
    (v : List (Fin 3 × ℕ)) (r : ℕ) (hr : v.length+u.length < 2*r) :
    (wordPolynomial (u ++ v.map (fun i => (i.1,-(i.2:ℤ)-1)))).coeff r = 0 := by
  unfold wordPolynomial
  rw [← applyNormal_wordNormal, wordNormal_creation]
  exact centralPolynomial_coeff_zero_of_weight
    (applyNormal_mem_contractionFiltration u
      (single_mem_contractionFiltration (0,v) 1 (by simp))) r hr

end VOA.AffineVOA.NormalOrdering
namespace VOA.AffineSl2GeneralRigidity
open AffineVOA Polynomial
open AffineSl2PBWWakimotoReduction
open scoped Classical

/-- Adjoint literal modes of a joint PBW word are all strictly positive.
Their colours are unchanged; the separate Gram sign is not absorbed here. -/
theorem jointWord_adjoint_nonnegative (n h : ℤ) (i : JointIndex n h) :
    ∀ a ∈ adjointIndices (jointWord n h i), 0 ≤ a.2 := by
  intro a ha
  simp only [adjointIndices, jointWord, List.mem_map, List.mem_reverse] at ha
  obtain ⟨b,⟨c,hc,rfl⟩,rfl⟩ := ha
  dsimp
  omega

/-- The number of literal modes equals the number of PBW creation letters. -/
theorem jointWord_length (n h : ℤ) (i : JointIndex n h) :
    (jointWord n h i).length = (orderedPBWColorWord i.val).length := by
  simp only [jointWord, List.length_map]

/-- The level degree of an actual joint Gram entry is bounded by the length
of its column word, since each central factor consumes a creation mode. -/
theorem jointGramPolynomial_natDegree_le (n h : ℤ)
    (i : JointIndex n h) (j : JointIndex n (-h)) :
    (jointGramPolynomial n h i j).natDegree ≤ (orderedPBWColorWord j.val).length := by
  apply (natDegree_smul_le _ _).trans
  apply NormalOrdering.centralPolynomial_natDegree_le
  exact NormalOrdering.wordNormal_prefix_mem _ _ (jointWord_adjoint_nonnegative n h i)

/-- Column lengths for the square block, using its explicit opposite-charge
bijection. The bound is attached to the actual column word. -/
noncomputable def jointColumnLength (n h : ℤ) (j : JointIndex n h) : ℕ :=
  (orderedPBWColorWord (jointChargeEquiv n h j).val).length

/-- Every square-block entry obeys its column's level-degree bound. -/
theorem jointGramSquare_natDegree_le (n h : ℤ) (i j : JointIndex n h) :
    (jointGramSquare n h i j).natDegree ≤ jointColumnLength n h j :=
  jointGramPolynomial_natDegree_le n h i (jointChargeEquiv n h j)

/-- The ordinary joint determinant degree is at most the total length of
its fixed PBW columns. This bound alone does not imply a root or sharpness. -/
theorem jointDeterminant_natDegree_le (n h : ℤ) :
    (jointDeterminant n h).natDegree ≤ ∑ j, jointColumnLength n h j := by
  classical
  rw [jointDeterminant, Matrix.det_apply]
  apply natDegree_sum_le_of_forall_le
  intro σ hσ
  apply (natDegree_smul_le _ _).trans
  exact (natDegree_prod_le _ _).trans
    (Finset.sum_le_sum (fun j _ => jointGramSquare_natDegree_le n h (σ j) j))

/-- The matrix of coefficients at each column's largest permitted level
power. It is defined even when a column fails to attain that degree. -/
noncomputable def jointTopMatrix (n h : ℤ) : Matrix (JointIndex n h) (JointIndex n h) ℂ :=
  fun i j => (jointGramSquare n h i j).coeff (jointColumnLength n h j)

/-- The determinant coefficient at the total column-length bound equals the
determinant of the column-top matrix. No nonvanishing assumption is used. -/
theorem jointDeterminant_top_coeff (n h : ℤ) :
    (jointDeterminant n h).coeff (∑ j, jointColumnLength n h j) =
      (jointTopMatrix n h).det := by
  classical
  exact VirDeformModes.NormalOrdering.coeff_det_sum_column_bounds
    _ _ (jointGramSquare_natDegree_le n h)

/-- A top entry is zero when its row is shorter than its column. The full
weighted filtration proves this without assuming symmetry of the form. -/
theorem jointTopMatrix_zero_of_shorter_row (n h : ℤ) (i j : JointIndex n h)
    (hlt : (orderedPBWColorWord i.val).length < jointColumnLength n h j) :
    jointTopMatrix n h i j = 0 := by
  have hz := NormalOrdering.pairing_coeff_zero_of_total_length
    (adjointIndices (jointWord n h i))
    (orderedPBWColorWord (jointChargeEquiv n h j).val) (jointColumnLength n h j)
    (by simpa only [adjointIndices, List.length_map, List.length_reverse,
        jointWord_length, jointColumnLength] using (show
          jointColumnLength n h j + (orderedPBWColorWord i.val).length <
            2*jointColumnLength n h j by omega))
  simpa only [jointTopMatrix, jointGramSquare, jointGramPolynomial, wordGramMatrix,
    wordGramPolynomial, coeff_smul, jointWord, hz, smul_zero, smul_eq_mul, mul_zero] using
    congrArg (fun z : ℂ => ((-1:ℂ)^(jointWord n h i).length) * z) hz

/-- At equal row and column lengths, the actual top Gram coefficient is
exactly the finite central-contraction result times the adjoint sign. Every
noncentral sl2 bracket contribution has been proved lower order. -/
theorem jointTopMatrix_eq_contractions (n h : ℤ) (i j : JointIndex n h)
    (hlen : (orderedPBWColorWord i.val).length = jointColumnLength n h j) :
    jointTopMatrix n h i j = ((-1:ℂ)^(jointWord n h i).length) *
      (NormalOrdering.centralPolynomial
        (NormalOrdering.applyContractions (adjointIndices (jointWord n h i))
          (Finsupp.single (0,orderedPBWColorWord (jointChargeEquiv n h j).val) 1))).coeff
            (jointColumnLength n h j) := by
  have he := NormalOrdering.equal_length_pairing_top_contractions
    (adjointIndices (jointWord n h i)) (orderedPBWColorWord (jointChargeEquiv n h j).val)
    (jointWord_adjoint_nonnegative n h i)
    (by simpa only [adjointIndices, List.length_map, List.length_reverse,
        jointWord_length, jointColumnLength] using hlen)
  exact congrArg (fun z : ℂ => ((-1:ℂ)^(jointWord n h i).length) * z) he

end VOA.AffineSl2GeneralRigidity
