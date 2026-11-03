/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2ContractionMultiset

/-!
# The diagonal top coefficients of affine joint Gram blocks

PBW multiplicities determine creation multisets. The e/f index involution
therefore gives exactly the opposite multiset, even though it does not preserve
sorted word order. Central-contraction support proves diagonal equal-length
blocks and evaluates their nonzero entries.
-/
namespace VOA.AffineSl2GeneralRigidity
open AffineVOA AffineSl2PBWWakimotoReduction Sl2NonLisse NormalOrdering Polynomial

/-- The number of occurrences of a letter in the PBW word is exactly its
prescribed multiplicity. This also handles absent letters. -/
theorem orderedPBW_count (mu : CurrentIndex) (a : NormalOrdering.Letter) :
    (orderedPBWColorWord mu : Multiset NormalOrdering.Letter).count a = mu (toLex a) := by
  classical
  letI : BEq NormalOrdering.Letter := instBEqOfDecidableEq
  rw [orderedPBWColorWord, Multiset.coe_count, List.count_flatMap]
  simp only [Function.comp_def, List.count_replicate, beq_iff_eq, Prod.mk.eta]
  have heq (q : Fin 3 ×ₗ ℕ) : ofLex q=a ↔ q=toLex a := by
    constructor
    · intro he; exact congrArg toLex he
    · intro he; subst q; rfl
  simp only [heq]
  rw [← List.sum_toFinset _ (Finset.sort_nodup _ _)]
  simp only [Finset.sort_toFinset]
  by_cases ha : toLex a ∈ mu.support
  · simp [Finset.sum_ite_eq', ha]
  · simp [ha, Finsupp.notMem_support_iff.mp ha]

/-- The creation multiset completely recovers its PBW multiplicity index. -/
theorem orderedPBW_multiset_injective : Function.Injective
    (fun mu : CurrentIndex => (orderedPBWColorWord mu : Multiset NormalOrdering.Letter)) := by
  intro mu nu h
  ext q
  have he := congrArg (fun s : Multiset NormalOrdering.Letter => s.count (ofLex q)) h
  simpa only [orderedPBW_count, toLex_ofLex] using he

/-- The opposite index swaps precisely the creation multiset, without making
any assertion about the sorted order of the resulting word. -/
theorem orderedPBW_flip_multiset (mu : CurrentIndex) :
    (orderedPBWColorWord (flipCurrentIndex mu) : Multiset NormalOrdering.Letter) =
      (orderedPBWColorWord mu : Multiset NormalOrdering.Letter).map oppositeLetter := by
  classical
  apply Multiset.ext.mpr
  intro a
  rw [orderedPBW_count]
  have he := Multiset.count_map_eq_count' oppositeLetter
    (orderedPBWColorWord mu : Multiset NormalOrdering.Letter) oppositeLetter_involutive.injective
    (oppositeLetter a)
  rw [oppositeLetter_involutive, orderedPBW_count] at he
  rw [he]
  change (Finsupp.mapDomain flipCurrentLetter mu) (toLex a) = _
  have hx : toLex a = flipCurrentLetter (toLex (oppositeLetter a)) := by
    simp [flipCurrentLetter, oppositeLetter]
  rw [hx, Finsupp.mapDomain_apply flipCurrentLetter_involutive.injective]

/-- Swapping colours preserves word length as well as energy and charge sign. -/
theorem orderedPBW_flip_length (mu : CurrentIndex) :
    (orderedPBWColorWord (flipCurrentIndex mu)).length = (orderedPBWColorWord mu).length := by
  simpa using congrArg Multiset.card (orderedPBW_flip_multiset mu)

/-- Each column has the same length as its unflipped index word. -/
theorem jointColumnLength_eq (n h : ℤ) (j : JointIndex n h) :
    jointColumnLength n h j = (orderedPBWColorWord j.val).length :=
  orderedPBW_flip_length j.val

/-- Adjoint creation words are exactly the positive-depth annihilators in
reverse order, as required by the order-independent contraction formula. -/
theorem jointWord_adjoint_eq (n h : ℤ) (i : JointIndex n h) :
    adjointIndices (jointWord n h i) =
      (orderedPBWColorWord i.val).reverse.map (fun a => (a.1,(a.2 : ℤ)+1)) := by
  simp [adjointIndices, jointWord, List.map_map, Function.comp_def, add_comm]

/-- At equal lengths a top coefficient can be nonzero only on the diagonal:
a complete central matching recovers the entire PBW index. -/
theorem jointTopMatrix_zero_of_ne_equal_length (n h : ℤ) (i j : JointIndex n h)
    (hne : i ≠ j) (hlen : (orderedPBWColorWord i.val).length = jointColumnLength n h j) :
    jointTopMatrix n h i j = 0 := by
  rw [jointTopMatrix_eq_contractions n h i j hlen, jointWord_adjoint_eq]
  have hz := contractions_vacuum_zero (orderedPBWColorWord i.val)
    (orderedPBWColorWord (jointChargeEquiv n h j).val) (by
      intro he
      change (orderedPBWColorWord (flipCurrentIndex j.val) : Multiset NormalOrdering.Letter) = _ at he
      rw [orderedPBW_flip_multiset] at he
      have hj := orderedPBW_multiset_injective
        (Multiset.map_injective oppositeLetter_involutive.injective he)
      exact hne (Subtype.ext hj.symm))
  rw [hz, Polynomial.coeff_zero, mul_zero]

/-- A diagonal top coefficient is the adjoint sign times the exact product
of positive depths, Killing coefficients and repeated-letter multiplicities. -/
theorem jointTopMatrix_diagonal (n h : ℤ) (i : JointIndex n h) :
    jointTopMatrix n h i i =
      (-1 : ℂ)^(orderedPBWColorWord i.val).length * diagonalContraction (orderedPBWColorWord i.val) := by
  rw [jointTopMatrix_eq_contractions n h i i (jointColumnLength_eq n h i).symm,
    jointWord_adjoint_eq]
  change (-1 : ℂ)^(jointWord n h i).length *
    (centralPolynomial (applyContractions
      ((orderedPBWColorWord i.val).reverse.map (fun a => (a.1,(a.2 : ℤ)+1)))
      (Finsupp.single (0,orderedPBWColorWord (flipCurrentIndex i.val)) 1))).coeff
      (jointColumnLength n h i) = _
  rw [contractions_vacuum_diagonal _ _ (orderedPBW_flip_multiset i.val)]
  simp [jointColumnLength_eq, jointWord_length]

/-- All diagonal top coefficients are nonzero, at every joint weight. -/
theorem jointTopMatrix_diagonal_ne_zero (n h : ℤ) (i : JointIndex n h) :
    jointTopMatrix n h i i ≠ 0 := by
  rw [jointTopMatrix_diagonal]
  exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
    (diagonalContraction_ne_zero _)

end VOA.AffineSl2GeneralRigidity
