import VOA.DeligneAudit.SL4TThomPolynomial

/-! # The four truncation relations in the two-alphabet ring -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open Polynomial

def S_relationIdeal (M a b : ℕ) : Ideal (S M a b)[X] :=
  relationIdeal (leftP M a b) (rightP M a b) M

theorem thomNGPiece_eq_map (M a b : ℕ) :
    ThomNGPiece M a b = (thomI2 M a b).map (Ideal.Quotient.mk (thomI1 M a b)) := by
  simp only [ThomNGPiece, thomI2, Ideal.map_span, Set.image_singleton]

theorem thomBothPiece_eq_map (M a b : ℕ) :
    ThomBothPiece M a b = (thomI3 M a b).map (Ideal.Quotient.mk (thomI2 M a b)) := by
  simp only [ThomBothPiece, thomI3, Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq,
    Ideal.map_span, Set.image_singleton]

/-- The unsigned `(nn)` relation. -/
theorem thom_relation_nn (M a b : ℕ) (hM : 0 < M) :
    Polynomial.C (leftE M a b a * rightE M a b b) * X ^ (M - 1) ∈
      S_relationIdeal M a b := by
  have h := polynomial_nn_mem (leftP M a b) (rightP M a b) (M - 1)
  rw [Nat.sub_add_cancel (show 1 ≤ M by omega), leftP_constant, rightP_constant] at h
  apply ((S_relationIdeal M a b).smul_mem_iff_of_isUnit
    (isUnit_neg_one.pow (a + b))).mp
  change (-1 : (S M a b)[X]) ^ (a + b) *
    (Polynomial.C (leftE M a b a * rightE M a b b) * X ^ (M - 1)) ∈ _
  convert h using 1
  simp only [map_mul, map_pow, map_neg, map_one, pow_add]
  ring

/-- The `(ng)` relation modulo the preceding ideal. -/
theorem thom_relation_ng (M a b : ℕ) :
    Polynomial.C (leftE M a b a) * X * leftP M a b * (rightP M a b).divX ∈
      S_relationIdeal M a b ⊔ (thomI1 M a b).map Polynomial.C := by
  apply polynomial_ng_mem
  rw [rightP_constant]
  have h : leftE M a b a * rightE M a b b ∈ thomI1 M a b :=
    Ideal.subset_span (Set.mem_singleton _)
  simpa only [mul_comm, mul_left_comm, mul_assoc] using
    (thomI1 M a b).mul_mem_left ((-1) ^ b) h

/-- The `(both)` relation; the complement identity is used before passing to the piece. -/
theorem thom_relation_both (M a b : ℕ) (hM : 0 < M) (hb : b ≤ M) :
    Polynomial.C (rightH M a b (M - b)) * X * (leftP M a b).divX *
        (rightP M a b).divX ∈
      S_relationIdeal M a b ⊔ (thomI2 M a b).map Polynomial.C := by
  have hfact : rightP M a b * rightPbar M a b = X ^ ((M - 1) + 1) := by
    rw [Nat.sub_add_cancel (show 1 ≤ M by omega)]
    exact right_characteristic_product M a b hb
  have hp : (leftP M a b).coeff 0 ∈ thomI2 M a b := by
    rw [leftP_constant]
    exact (thomI2 M a b).mul_mem_left _ (Ideal.subset_span (Set.mem_singleton _))
  have h := polynomial_both_mem (leftP M a b) (rightP M a b) (rightPbar M a b)
    (M - 1) (thomI2 M a b) hfact hp
  simpa only [rightPbar_constant, Nat.sub_add_cancel (show 1 ≤ M by omega)] using h

/-- The final `(gn)` relation. -/
theorem thom_relation_gn (M a b : ℕ) :
    X * (leftP M a b).divX * rightP M a b ∈
      S_relationIdeal M a b ⊔ (thomI3 M a b).map Polynomial.C := by
  apply polynomial_gn_mem
  rw [leftP_constant]
  apply (thomI3 M a b).mul_mem_left
  exact thomI2_le_I3 M a b (Ideal.subset_span (Set.mem_singleton _))

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.thomNGPiece_eq_map
#print axioms VOA.DeligneAudit.SL4T.thomBothPiece_eq_map
#print axioms VOA.DeligneAudit.SL4T.thom_relation_nn
#print axioms VOA.DeligneAudit.SL4T.thom_relation_ng
#print axioms VOA.DeligneAudit.SL4T.thom_relation_both
#print axioms VOA.DeligneAudit.SL4T.thom_relation_gn
