import VOA.DeligneAudit.SL4TThomEdges

/-! # Representative formulas for the Thom maps and the peeled alphabets -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open Polynomial

theorem S_boundary_quot_symm_mk (M a b : ℕ) (cutL cutR : Bool)
    (ha : a ≤ M) (hb : b ≤ M)
    (hL : BoundaryAllowed M a cutL) (hR : BoundaryAllowed M b cutR) (p : BiSymPoly) :
    (S_boundary_quot M a b cutL cutR ha hb hL hR).symm (Ideal.Quotient.mk _ p) =
      Ideal.Quotient.mk _ (Ideal.Quotient.mk _ p) := by
  apply (S_boundary_quot M a b cutL cutR ha hb hL hR).injective
  rw [AlgEquiv.apply_symm_apply, S_boundary_quot_mk]

theorem boundaryProjection_surjective (M a b : ℕ) (cutL cutR : Bool)
    (ha : a ≤ M) (hb : b ≤ M)
    (hL : BoundaryAllowed M a cutL) (hR : BoundaryAllowed M b cutR) :
    Function.Surjective (boundaryProjection M a b cutL cutR ha hb hL hR) :=
  (S_boundary_quot M a b cutL cutR ha hb hL hR).surjective.comp
    (Ideal.Quotient.mkₐ_surjective ℂ _)

theorem thomNN_mk (M a b : ℕ) (ha : a < M) (hb : b < M) (p : BiSymPoly) :
    (thomNN M a b ha hb (Ideal.Quotient.mk _ p) : S M a b) =
      (leftE M a b a * rightE M a b b) * Ideal.Quotient.mk _ p := by
  change (principalThom (AlgHom.id ℂ (S M a b))
    (leftE M a b a * rightE M a b b) (boundaryIdeal M a b false false)
    (thomNN_kills M a b ha hb)
    ((S_boundary_quot M a b false false ha.le hb.le ha hb).symm
      (Ideal.Quotient.mk _ p)) : S M a b) = _
  rw [S_boundary_quot_symm_mk M a b false false ha.le hb.le ha hb p,
    principalThom_mk]
  rfl

theorem thomNG_mk (M a b : ℕ) (ha : a < M) (hb : b ≤ M) (hb0 : 0 < b)
    (p : BiSymPoly) :
    (thomNG M a b ha hb hb0 (Ideal.Quotient.mk _ p) : S M a b ⧸ thomI1 M a b) =
      Ideal.Quotient.mk (thomI1 M a b) (leftE M a b a * Ideal.Quotient.mk _ p) := by
  change (principalThom (Ideal.Quotient.mkₐ ℂ (thomI1 M a b))
    (leftE M a b a) (boundaryIdeal M a b false true) (thomNG_kills M a b ha)
    ((S_boundary_quot M a b false true ha.le hb ha hb0).symm
      (Ideal.Quotient.mk _ p)) : S M a b ⧸ thomI1 M a b) = _
  rw [S_boundary_quot_symm_mk M a b false true ha.le hb ha hb0 p, principalThom_mk]
  exact (map_mul (Ideal.Quotient.mk (thomI1 M a b)) _ _).symm

theorem thomBoth_mk (M a b : ℕ) (ha : a ≤ M) (hb : b ≤ M)
    (ha0 : 0 < a) (hb0 : 0 < b) (p : BiSymPoly) :
    (thomBoth M a b ha hb ha0 hb0 (Ideal.Quotient.mk _ p) : S M a b ⧸ thomI2 M a b) =
      Ideal.Quotient.mk (thomI2 M a b)
        (rightH M a b (M - b) * Ideal.Quotient.mk _ p) := by
  change (principalThom (Ideal.Quotient.mkₐ ℂ (thomI2 M a b))
    (rightH M a b (M - b)) (boundaryIdeal M a b true true)
    (thomBoth_kills M a b (by omega) hb)
    ((S_boundary_quot M a b true true ha hb ha0 hb0).symm
      (Ideal.Quotient.mk _ p)) : S M a b ⧸ thomI2 M a b) = _
  rw [S_boundary_quot_symm_mk M a b true true ha hb ha0 hb0 p, principalThom_mk]
  exact (map_mul (Ideal.Quotient.mk (thomI2 M a b)) _ _).symm

theorem thomGN_mk (M a b : ℕ) (ha : a ≤ M) (ha0 : 0 < a) (hb : b < M)
    (p : BiSymPoly) :
    thomGN M a b ha ha0 hb (Ideal.Quotient.mk _ (Ideal.Quotient.mk _ p)) =
      Ideal.Quotient.mk _ p := by
  rw [thomGN, AlgEquiv.trans_apply, Ideal.quotientEquivAlgOfEq_mk]
  exact S_boundary_quot_mk M a b true false ha hb.le ha0 hb p

theorem thomGN_surjective (M a b : ℕ) (ha : a ≤ M) (ha0 : 0 < a) (hb : b < M) :
    Function.Surjective (thomGN M a b ha ha0 hb).symm :=
  (thomGN M a b ha ha0 hb).symm.surjective

/-- On a row boundary, the divided polynomial is precisely the smaller alphabet. -/
theorem boundaryProjection_leftP_divX (M a b : ℕ) (cutR : Bool)
    (ha : a ≤ M) (hb : b ≤ M) (ha0 : 0 < a) (hR : BoundaryAllowed M b cutR) :
    ((leftP M a b).divX).map
        (boundaryProjection M a b true cutR ha hb ha0 hR).toRingHom =
      leftP (M - 1) (a - 1) (boundaryIndex b cutR) := by
  have h := boundaryProjection_leftP M a b true cutR ha hb ha0 hR
  ext n
  have hc := congrArg
    (fun P : (S (M - 1) (a - 1) (boundaryIndex b cutR))[X] => P.coeff (n + 1)) h
  change ((leftP M a b).map _).coeff (n + 1) =
    (X * leftP (M - 1) (a - 1) (boundaryIndex b cutR)).coeff (n + 1) at hc
  rw [coeff_map, coeff_X_mul] at hc
  simpa only [coeff_map, coeff_divX] using hc

theorem boundaryProjection_rightP_divX (M a b : ℕ) (cutL : Bool)
    (ha : a ≤ M) (hb : b ≤ M) (hL : BoundaryAllowed M a cutL) (hb0 : 0 < b) :
    ((rightP M a b).divX).map
        (boundaryProjection M a b cutL true ha hb hL hb0).toRingHom =
      rightP (M - 1) (boundaryIndex a cutL) (b - 1) := by
  have h := boundaryProjection_rightP M a b cutL true ha hb hL hb0
  ext n
  have hc := congrArg
    (fun P : (S (M - 1) (boundaryIndex a cutL) (b - 1))[X] => P.coeff (n + 1)) h
  change ((rightP M a b).map _).coeff (n + 1) =
    (X * rightP (M - 1) (boundaryIndex a cutL) (b - 1)).coeff (n + 1) at hc
  rw [coeff_map, coeff_X_mul] at hc
  simpa only [coeff_map, coeff_divX] using hc

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.S_boundary_quot_symm_mk
#print axioms VOA.DeligneAudit.SL4T.boundaryProjection_surjective
#print axioms VOA.DeligneAudit.SL4T.thomNN_mk
#print axioms VOA.DeligneAudit.SL4T.thomNG_mk
#print axioms VOA.DeligneAudit.SL4T.thomBoth_mk
#print axioms VOA.DeligneAudit.SL4T.thomGN_mk
#print axioms VOA.DeligneAudit.SL4T.thomGN_surjective
#print axioms VOA.DeligneAudit.SL4T.boundaryProjection_leftP_divX
#print axioms VOA.DeligneAudit.SL4T.boundaryProjection_rightP_divX
