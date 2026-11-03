import VOA.DeligneAudit.D4CharBoxGaussian
import VOA.DeligneAudit.D4LeviKSBoxCountCore
import VOA.DeligneAudit.D4CharLeviCount

/-! Products of finite degree boxes, including the exact D4 q-multinomial count. -/

namespace VOA.DeligneAudit.D4Char

open Polynomial Sl2Weyl A3Sector D4Levi

noncomputable section

def boxDegreePoly {α : Type*} (s : Finset α) (d : α → ℕ) : ℚ[X] :=
  ∑ x ∈ s, X ^ d x

theorem boxDegreePoly_coeff {α : Type*} (s : Finset α) (d : α → ℕ) (N : ℕ) :
    (boxDegreePoly s d).coeff N = ((s.filter fun x => d x = N).card : ℚ) := by
  classical
  simp [boxDegreePoly, finsetSum_coeff, coeff_X_pow, Finset.sum_boole, eq_comm]

theorem boxDegreePoly_product {α β : Type*}
    (s : Finset α) (t : Finset β) (d : α → ℕ) (e : β → ℕ) :
    boxDegreePoly (s ×ˢ t) (fun p => d p.1 + e p.2) =
      boxDegreePoly s d * boxDegreePoly t e := by
  simp [boxDegreePoly, Finset.sum_product, Finset.sum_mul_sum, pow_add]

/-- Splitting by degree gives the convolution, with no truncation of either box. -/
theorem boxDegree_card_product {α β : Type*}
    (s : Finset α) (t : Finset β) (d : α → ℕ) (e : β → ℕ) (N : ℕ) :
    ((s ×ˢ t).filter fun p => d p.1 + e p.2 = N).card =
      A2.conv (fun i => (s.filter fun x => d x = i).card)
        (fun j => (t.filter fun y => e y = j).card) N := by
  have hc := congrArg (fun p : ℚ[X] => p.coeff N) (boxDegreePoly_product s t d e)
  dsimp only at hc
  rw [boxDegreePoly_coeff,
    A2.coeff_mul_eq_convQ (boxDegreePoly_coeff s d) (boxDegreePoly_coeff t e)] at hc
  exact_mod_cast hc

/-- The D4 triple box retains precisely the three Gaussian factors in every degree. -/
theorem ksGradedBoxCount_eq_conv (m a b c d : ℕ) (h : a + b + c ≤ m) :
    ksGradedBoxCount m a b c d =
      A2.conv (A2.conv (A2.qbinomCoeff (m - c - b) a)
        (A2.qbinomCoeff (m - c) b)) (A2.qbinomCoeff m c) d := by
  unfold ksGradedBoxCount ksBoxTriples ksBoxDegree
  rw [boxDegree_card_product
    (a2BoxModeSet (m - c - b) a ×ˢ a2BoxModeSet (m - c) b) (a2BoxModeSet m c)
    (fun p => (Finsupp.weight om p.1).2 + (Finsupp.weight om p.2).2)
    (fun f => (Finsupp.weight om f).2)]
  congr 1
  · funext i
    rw [boxDegree_card_product (a2BoxModeSet (m - c - b) a) (a2BoxModeSet (m - c) b)
      (fun f => (Finsupp.weight om f).2)
      (fun f => (Finsupp.weight om f).2)]
    congr 1
    · funext j
      exact modeBox_card_degree _ _ _ (by omega)
    · funext j
      exact modeBox_card_degree _ _ _ (by omega)
  · funext j
    exact modeBox_card_degree _ _ _ (by omega)

theorem natConv_comm (f g : ℕ → ℕ) : A2.conv f g = A2.conv g f := by
  funext N
  unfold A2.conv
  rw [← Finset.sum_range_reflect (fun i => f i * g (N - i)) (N + 1)]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i ≤ N := by simpa using hi
  simp only [Nat.add_sub_cancel, Nat.sub_sub_self hi', Nat.mul_comm]

/-- Exact identification of the original per-degree box count with `qmultiCoeff`. -/
theorem ksGradedBoxCount_eq_qmulti (t : Fin 4 → ℕ) (d : ℕ) :
    ksGradedBoxCount (∑ i, t i) (t 0) (t 2) (t 3) d = qmultiCoeff t d := by
  have hs : (∑ i, t i) = t 0 + t 1 + t 2 + t 3 := by
    simp [Fin.sum_univ_succ, add_assoc]
  rw [ksGradedBoxCount_eq_conv _ _ _ _ _ (by rw [hs]; omega)]
  have h₁ : (∑ i, t i) - t 3 - t 2 = t 0 + t 1 := by rw [hs]; omega
  have h₂ : (∑ i, t i) - t 3 = t 0 + t 1 + t 2 := by rw [hs]; omega
  rw [h₁, h₂]
  have hc := A2.coeff_mul_eq_convQ
    (fun j => A2.coeff_mul_eq_convQ
      (A2.coeff_qbinom_X (t 0 + t 1) (t 0))
      (A2.coeff_qbinom_X (t 0 + t 1 + t 2) (t 2)) j)
    (A2.coeff_qbinom_X (∑ i, t i) (t 3)) d
  have he : VOA.DeligneGaussian.qbinom (X : ℚ[X]) (t 0 + t 1) (t 0) *
      VOA.DeligneGaussian.qbinom X (t 0 + t 1 + t 2) (t 2) *
      VOA.DeligneGaussian.qbinom X (∑ i, t i) (t 3) = qmultiPoly t := by
    unfold qmultiPoly
    ring
  rw [he, coeff_qmultiPoly] at hc
  exact_mod_cast hc.symm

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.boxDegreePoly_coeff
#print axioms VOA.DeligneAudit.D4Char.boxDegreePoly_product
#print axioms VOA.DeligneAudit.D4Char.boxDegree_card_product
#print axioms VOA.DeligneAudit.D4Char.ksGradedBoxCount_eq_conv
#print axioms VOA.DeligneAudit.D4Char.natConv_comm
#print axioms VOA.DeligneAudit.D4Char.ksGradedBoxCount_eq_qmulti
