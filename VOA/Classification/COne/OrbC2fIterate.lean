import VOA.Classification.COne.OrbC2eSeeds
import VOA.Core.BorcherdsIdentity

/-! # Finite iterate reduction for the dressed tetrahedral seed

The bounds follow from the actual VOA grading and positivity. In particular,
the weight-nine self-products reduce to finitely many J/E-left products.
-/
set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096

noncomputable section
namespace VOA.Classification.COne.OrbC2f
open VOA VertexOperatorAlgebra OrbC2c OrbC2e PlusUnitary

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- An explicit cutoff, with no chosen regularity witness. -/
theorem smul_eq_zero_of_weights (W : VertexOperatorAlgebra V)
    {a x : V} {p q n : ℤ} (ha : a ∈ W.grading p) (hx : x ∈ W.grading q)
    (hn : p + q ≤ n) : W.smul a n x = 0 := by
  have h := W.smul_mem_grading ha hx n
  rw [W.positivity (p + q - n - 1) (by omega)] at h
  exact h

/-- Finite Borcherds iterate, valid at every inner and outer integral mode. -/
theorem mode_iterate_finite (W : VertexOperatorAlgebra V)
    {a b x : V} {p q r : ℤ} (ha : a ∈ W.grading p)
    (hb : b ∈ W.grading q) (hx : x ∈ W.grading r)
    (ell n : ℤ) (B : ℕ) (hB₁ : p + r ≤ B) (hB₂ : q + r - n ≤ B) :
    W.smul (W.smul a ell b) n x =
      ∑ i ∈ Finset.range B, ((-1 : ℂ)^i * gBinom ell i) •
        (W.smul a (ell-i) (W.smul b (n+i) x) -
          ((-1 : ℂ)^ell) • W.smul b (ell+n-i) (W.smul a i x)) := by
  rw [W.mode_iterate]
  apply finsum_eq_finsetSum_of_support_subset
  intro i hi
  by_contra hnot
  have hiB : B ≤ i := by simpa using hnot
  have hax := smul_eq_zero_of_weights W ha hx (n := i) (by omega)
  have hbx := smul_eq_zero_of_weights W hb hx (n := n+i) (by omega)
  apply hi
  dsimp only
  rw [hax, hbx, PreVertexAlgebra.smul_zero_right, PreVertexAlgebra.smul_zero_right,
    smul_zero, sub_self, smul_zero]

/-- The normal-product case explicitly requested by the dressed-left evaluator. -/
theorem mode_neg_one_finite (W : VertexOperatorAlgebra V)
    {a b x : V} {p q r : ℤ} (ha : a ∈ W.grading p)
    (hb : b ∈ W.grading q) (hx : x ∈ W.grading r)
    (n : ℤ) (B : ℕ) (hB₁ : p + r ≤ B) (hB₂ : q + r - n ≤ B) :
    W.smul (W.smul a (-1) b) n x =
      ∑ i ∈ Finset.range B,
        (W.smul a (-1-i) (W.smul b (n+i) x) +
          W.smul b (-1+n-i) (W.smul a i x)) := by
  rw [mode_iterate_finite W ha hb hx (-1) n B hB₁ hB₂]
  apply Finset.sum_congr rfl
  intro i _
  have hc : (-1 : ℂ)^i * gBinom (-1) i = 1 := by
    rw [gBinom_neg_one]
    rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
  rw [hc, one_smul]
  norm_num

/-- Each term has only the two original generators on the left. -/
def seedIterateTerm (n : ℤ) (i : ℕ) (x : PlusC2.VP 4 four_ge_one) :
    PlusC2.VP 4 four_ge_one :=
  let W := V2mPlus 4 four_ge_one
  let j := J 4 four_ge_one
  let e := EP 4 four_ge_one
  ((-1 : ℂ)^i * gBinom (-2) i) •
    ((W.smul j (-2-i) (W.smul e (n+i) x) -
        W.smul e (-2+n-i) (W.smul j i x)) -
      (W.smul e (-2-i) (W.smul j (n+i) x) -
        W.smul j (-2+n-i) (W.smul e i x)))

/-- Dressed-left reduction of D against any homogeneous right state. -/
theorem weightNine_smul_finite {x : PlusC2.VP 4 four_ge_one} {r : ℤ}
    (hx : x ∈ (V2mPlus 4 four_ge_one).grading r) (n : ℤ)
    (B : ℕ) (hB₁ : 4 + r ≤ B) (hB₂ : 4 + r - n ≤ B) :
    (V2mPlus 4 four_ge_one).smul weightNine n x =
      ∑ i ∈ Finset.range B, seedIterateTerm n i x := by
  have hj := J_mem_grading_four 4 four_ge_one
  have he : EP 4 four_ge_one ∈ (V2mPlus 4 four_ge_one).grading (4 : ℤ) :=
    EP_mem_grading 4 four_ge_one
  have hsub (a b : PlusC2.VP 4 four_ge_one) :
      (V2mPlus 4 four_ge_one).smul (a-b) n x =
        (V2mPlus 4 four_ge_one).smul a n x - (V2mPlus 4 four_ge_one).smul b n x := by
    rw [sub_eq_add_neg, PreVertexAlgebra.smul_add_left, ← neg_one_smul ℂ b,
      PreVertexAlgebra.smul_smul_left, neg_one_smul, ← sub_eq_add_neg]
  rw [weightNine, hsub]
  rw [mode_iterate_finite _ hj he hx (-2) n B hB₁ hB₂,
    mode_iterate_finite _ he hj hx (-2) n B hB₁ hB₂, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  norm_num only [seedIterateTerm, zpow_neg, neg_neg, even_two,
    Even.neg_pow, one_pow, inv_one, one_smul]
  module

/-- The weight-20 self-product has this finite expansion with a safe cutoff. -/
theorem weightNine_self_neg_three :
    (V2mPlus 4 four_ge_one).smul weightNine (-3) weightNine =
      ∑ i ∈ Finset.range 16, seedIterateTerm (-3) i weightNine :=
  weightNine_smul_finite weightNine_mem_grading (-3) 16 (by norm_num) (by norm_num)

/-- The weight-22 self-product has this finite expansion with a safe cutoff. -/
theorem weightNine_self_neg_five :
    (V2mPlus 4 four_ge_one).smul weightNine (-5) weightNine =
      ∑ i ∈ Finset.range 18, seedIterateTerm (-5) i weightNine :=
  weightNine_smul_finite weightNine_mem_grading (-5) 18 (by norm_num) (by norm_num)

end VOA.Classification.COne.OrbC2f
