import VOA.DeligneAudit.SL4TGrassmannian

/-! # Boundary quotients and the boundary product in the Grassmannian ring -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

/-- Setting the top elementary generator to zero removes one row. -/
def grassQuotE (d T : ℕ) :
    (GrassRing (d + 1) T ⧸ Ideal.span {eClass (d + 1) T (d + 1)}) ≃ₐ[ℂ]
      GrassRing d T := by
  have e := DoubleQuot.quotQuotEquivQuotSupₐ ℂ (grassIdeal (d + 1) T)
    (Ideal.span {elementary (d + 1)})
  rw [Ideal.map_span, Set.image_singleton] at e
  exact e.trans (Ideal.quotientEquivAlgOfEq ℂ (grassIdeal_peel_e d T).symm)

/-- Setting the top complete generator to zero removes one column. -/
def grassQuotH (d T : ℕ) :
    (GrassRing d (T + 1) ⧸ Ideal.span {hClass d (T + 1) (T + 1)}) ≃ₐ[ℂ]
      GrassRing d T := by
  have e := DoubleQuot.quotQuotEquivQuotSupₐ ℂ (grassIdeal d (T + 1))
    (Ideal.span {complete (T + 1)})
  rw [Ideal.map_span, Set.image_singleton] at e
  exact e.trans (Ideal.quotientEquivAlgOfEq ℂ (grassIdeal_peel_h d T).symm)

/-- Transport of the width parameter, preserving the algebra structure. -/
def grassRingCongr (d : ℕ) {T U : ℕ} (h : T = U) : GrassRing d T ≃ₐ[ℂ] GrassRing d U := by
  subst U
  exact AlgEquiv.refl

/-- (G-b), elementary boundary, in the original `(d,M)` coordinates. -/
def H_quot_e (d M : ℕ) (hd : 1 ≤ d) (hdM : d ≤ M) :
    (H d M ⧸ Ideal.span {eClass d (M - d) d}) ≃ₐ[ℂ] H (d - 1) (M - 1) := by
  let T := M - d
  let Q := fun a => (GrassRing a T ⧸ Ideal.span {eClass a T a}) ≃ₐ[ℂ]
    GrassRing (a - 1) T
  have h : d - 1 + 1 = d := by omega
  have e : Q d := Eq.mp (congrArg Q h) (grassQuotE (d - 1) T)
  exact e.trans (grassRingCongr (d - 1) (show T = M - 1 - (d - 1) by dsimp [T]; omega))

/-- (G-b), complete boundary. At `d = M` the quotient by `h_0 = 1` is zero instead. -/
def H_quot_h (d M : ℕ) (hdM : d < M) :
    (H d M ⧸ Ideal.span {hClass d (M - d) (M - d)}) ≃ₐ[ℂ] H d (M - 1) := by
  let T := M - d
  let Q := fun w => (GrassRing d w ⧸ Ideal.span {hClass d w w}) ≃ₐ[ℂ]
    GrassRing d (w - 1)
  have h : T - 1 + 1 = T := by dsimp [T]; omega
  have e : Q T := Eq.mp (congrArg Q h) (grassQuotH d (T - 1))
  exact e.trans (grassRingCongr d (show T - 1 = M - 1 - d by dsimp [T]; omega))

/-- The convolution relation isolates the product at the corner of the rectangle. -/
theorem grass_boundary_product (d T : ℕ) (hpos : 0 < d + T) :
    eClass d T d * hClass d T T = 0 := by
  let π := Ideal.Quotient.mk (grassIdeal d T)
  have hsum := congrArg π (complete_relation (d + T) hpos)
  simp only [map_sum, map_mul, map_pow, map_neg, map_one, map_zero] at hsum
  have he : ∀ i, π (elementary i) = eClass d T i := fun _ => rfl
  have hh : ∀ i, π (complete i) = hClass d T i := fun _ => rfl
  simp only [he, hh] at hsum
  rw [Finset.sum_eq_single d] at hsum
  · rw [show d + T - d = T by omega, mul_assoc] at hsum
    exact (IsUnit.mul_right_eq_zero (isUnit_neg_one.pow d)).mp hsum
  · intro i _ hi
    by_cases hdi : d < i
    · rw [eClass_eq_zero d T i hdi, mul_zero, zero_mul]
    · rw [hClass_eq_zero d T (d + T - i) (by omega), mul_zero]
  · intro hd
    exact False.elim (hd (Finset.mem_range.mpr (by omega)))

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.grassQuotE
#print axioms VOA.DeligneAudit.SL4T.grassQuotH
#print axioms VOA.DeligneAudit.SL4T.H_quot_e
#print axioms VOA.DeligneAudit.SL4T.H_quot_h
#print axioms VOA.DeligneAudit.SL4T.grass_boundary_product
