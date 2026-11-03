import VOA.DeligneAudit.SL4TThomMap

/-! # The four surjective pieces of the Thom chain -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

def thomI1 (M a b : ℕ) : Ideal (S M a b) :=
  Ideal.span {leftE M a b a * rightE M a b b}

def thomI2 (M a b : ℕ) : Ideal (S M a b) := Ideal.span {leftE M a b a}

def thomI3 (M a b : ℕ) : Ideal (S M a b) :=
  thomI2 M a b ⊔ Ideal.span {rightH M a b (M - b)}

theorem thomI1_le_I2 (M a b : ℕ) : thomI1 M a b ≤ thomI2 M a b := by
  apply Ideal.span_le.mpr
  rintro x rfl
  exact Ideal.mem_span_singleton.mpr ⟨rightE M a b b, rfl⟩

theorem thomI2_le_I3 (M a b : ℕ) : thomI2 M a b ≤ thomI3 M a b := le_sup_left

theorem thomNN_kills (M a b : ℕ) (ha : a < M) (hb : b < M) :
    ∀ x ∈ boundaryIdeal M a b false false,
      (AlgHom.id ℂ (S M a b)) ((leftE M a b a * rightE M a b b) * x) = 0 := by
  rw [boundaryIdeal_eq]
  refine thom_kills_span_sup _ _ _ _ ?_ ?_
  · change (leftE M a b a * rightE M a b b) * leftH M a b (M - a) = 0
    calc
      _ = rightE M a b b * (leftE M a b a * leftH M a b (M - a)) := by ring
      _ = 0 := by rw [left_boundary_product M a b (by omega) ha.le, mul_zero]
  · change (leftE M a b a * rightE M a b b) * rightH M a b (M - b) = 0
    rw [mul_assoc, right_boundary_product M a b (by omega) hb.le, mul_zero]

theorem thomNG_kills (M a b : ℕ) (ha : a < M) :
    ∀ x ∈ boundaryIdeal M a b false true,
      Ideal.Quotient.mkₐ ℂ (thomI1 M a b) (leftE M a b a * x) = 0 := by
  rw [boundaryIdeal_eq]
  refine thom_kills_span_sup _ _ _ _ ?_ ?_
  · simp only [Bool.false_eq_true, if_false]
    rw [left_boundary_product M a b (by omega) ha.le, map_zero]
  · apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.subset_span (Set.mem_singleton _)

theorem thomBoth_kills (M a b : ℕ) (hM : 0 < M) (hb : b ≤ M) :
    ∀ x ∈ boundaryIdeal M a b true true,
      Ideal.Quotient.mkₐ ℂ (thomI2 M a b) (rightH M a b (M - b) * x) = 0 := by
  rw [boundaryIdeal_eq]
  refine thom_kills_span_sup _ _ _ _ ?_ ?_
  · apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.mem_span_singleton.mpr ⟨rightH M a b (M - b), mul_comm _ _⟩
  · simp only [if_true]
    rw [mul_comm, right_boundary_product M a b hM hb, map_zero]

/-- The `nn` map is multiplication by the product of the two top elementary classes. -/
def thomNN (M a b : ℕ) (ha : a < M) (hb : b < M) :
    S (M - 1) a b →ₗ[ℂ] thomI1 M a b :=
  (principalThom (AlgHom.id ℂ (S M a b))
    (leftE M a b a * rightE M a b b) (boundaryIdeal M a b false false)
    (thomNN_kills M a b ha hb)).comp
      (S_boundary_quot M a b false false ha.le hb.le ha hb).symm.toLinearMap

theorem thomNN_surjective (M a b : ℕ) (ha : a < M) (hb : b < M) :
    Function.Surjective (thomNN M a b ha hb) :=
  (principalThom_surjective (AlgHom.id ℂ (S M a b)) Function.surjective_id
    (leftE M a b a * rightE M a b b) (boundaryIdeal M a b false false)
    (thomNN_kills M a b ha hb)).comp
      (S_boundary_quot M a b false false ha.le hb.le ha hb).symm.surjective

/-- The `ng` piece, realized as the image of `I₂` in `S/I₁`. -/
abbrev ThomNGPiece (M a b : ℕ) :=
  Ideal.span {Ideal.Quotient.mk (thomI1 M a b) (leftE M a b a)}

def thomNG (M a b : ℕ) (ha : a < M) (hb : b ≤ M) (hb0 : 0 < b) :
    S (M - 1) a (b - 1) →ₗ[ℂ] ThomNGPiece M a b :=
  (principalThom (Ideal.Quotient.mkₐ ℂ (thomI1 M a b))
    (leftE M a b a) (boundaryIdeal M a b false true) (thomNG_kills M a b ha)).comp
      (S_boundary_quot M a b false true ha.le hb ha hb0).symm.toLinearMap

theorem thomNG_surjective (M a b : ℕ) (ha : a < M) (hb : b ≤ M) (hb0 : 0 < b) :
    Function.Surjective (thomNG M a b ha hb hb0) :=
  (principalThom_surjective (Ideal.Quotient.mkₐ ℂ (thomI1 M a b))
    (Ideal.Quotient.mkₐ_surjective ℂ _) (leftE M a b a)
    (boundaryIdeal M a b false true) (thomNG_kills M a b ha)).comp
      (S_boundary_quot M a b false true ha.le hb ha hb0).symm.surjective

/-- The `both` piece, realized as the image of `I₃` in `S/I₂`. -/
abbrev ThomBothPiece (M a b : ℕ) :=
  Ideal.span {Ideal.Quotient.mk (thomI2 M a b) (rightH M a b (M - b))}

def thomBoth (M a b : ℕ) (ha : a ≤ M) (hb : b ≤ M) (ha0 : 0 < a) (hb0 : 0 < b) :
    S (M - 1) (a - 1) (b - 1) →ₗ[ℂ] ThomBothPiece M a b :=
  (principalThom (Ideal.Quotient.mkₐ ℂ (thomI2 M a b))
    (rightH M a b (M - b)) (boundaryIdeal M a b true true)
    (thomBoth_kills M a b (by omega) hb)).comp
      (S_boundary_quot M a b true true ha hb ha0 hb0).symm.toLinearMap

theorem thomBoth_surjective (M a b : ℕ) (ha : a ≤ M) (hb : b ≤ M)
    (ha0 : 0 < a) (hb0 : 0 < b) :
    Function.Surjective (thomBoth M a b ha hb ha0 hb0) :=
  (principalThom_surjective (Ideal.Quotient.mkₐ ℂ (thomI2 M a b))
    (Ideal.Quotient.mkₐ_surjective ℂ _) (rightH M a b (M - b))
    (boundaryIdeal M a b true true) (thomBoth_kills M a b (by omega) hb)).comp
      (S_boundary_quot M a b true true ha hb ha0 hb0).symm.surjective

theorem thomI3_eq_boundary (M a b : ℕ) :
    thomI3 M a b = boundaryIdeal M a b true false := by
  simp only [boundaryIdeal_eq, if_true, Bool.false_eq_true, if_false, thomI3, thomI2]

/-- The final `gn` piece is a quotient algebra, not just a linear image. -/
def thomGN (M a b : ℕ) (ha : a ≤ M) (ha0 : 0 < a) (hb : b < M) :
    (S M a b ⧸ thomI3 M a b) ≃ₐ[ℂ] S (M - 1) (a - 1) b :=
  (Ideal.quotientEquivAlgOfEq ℂ (thomI3_eq_boundary M a b)).trans
    (S_boundary_quot M a b true false ha hb.le ha0 hb)

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.thomNN_surjective
#print axioms VOA.DeligneAudit.SL4T.thomNG_surjective
#print axioms VOA.DeligneAudit.SL4T.thomBoth_surjective
#print axioms VOA.DeligneAudit.SL4T.thomGN
