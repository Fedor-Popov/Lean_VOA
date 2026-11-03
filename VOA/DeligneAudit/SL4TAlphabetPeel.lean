import VOA.DeligneAudit.SL4TTwoBoundary

/-! # Identification of the alphabets after a boundary quotient -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open Polynomial

theorem descendingPoly_map {R T : Type*} [Semiring R] [Semiring T]
    (φ : R →+* T) (f : ℕ → R) (d : ℕ) :
    (descendingPoly f d).map φ = descendingPoly (fun i => φ (f i)) d := by
  simp only [descendingPoly_eq_sum, Polynomial.map_sum, Polynomial.map_mul,
    Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X]

theorem descendingPoly_step {R : Type*} [CommSemiring R] (f : ℕ → R) (d : ℕ) :
    descendingPoly f (d + 1) = X * descendingPoly f d + Polynomial.C (f (d + 1)) := by
  rw [descendingPoly_eq_sum, descendingPoly_eq_sum, Finset.sum_range_succ,
    Finset.mul_sum]
  simp only [Nat.sub_self, pow_zero, mul_one]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [show d + 1 - i = (d - i) + 1 by have := Finset.mem_range.mp hi; omega,
    pow_succ]
  ring

def boundaryProjection (M a b : ℕ) (cutL cutR : Bool)
    (ha : a ≤ M) (hb : b ≤ M)
    (hL : BoundaryAllowed M a cutL) (hR : BoundaryAllowed M b cutR) :
    S M a b →ₐ[ℂ] S (M - 1) (boundaryIndex a cutL) (boundaryIndex b cutR) :=
  (S_boundary_quot M a b cutL cutR ha hb hL hR).toAlgHom.comp
    (Ideal.Quotient.mkₐ ℂ (boundaryIdeal M a b cutL cutR))

theorem boundaryProjection_mk (M a b : ℕ) (cutL cutR : Bool)
    (ha : a ≤ M) (hb : b ≤ M)
    (hL : BoundaryAllowed M a cutL) (hR : BoundaryAllowed M b cutR) (p : BiSymPoly) :
    boundaryProjection M a b cutL cutR ha hb hL hR (Ideal.Quotient.mk _ p) =
      Ideal.Quotient.mk _ p := S_boundary_quot_mk M a b cutL cutR ha hb hL hR p

theorem boundaryProjection_leftE (M a b : ℕ) (cutL cutR : Bool)
    (ha : a ≤ M) (hb : b ≤ M)
    (hL : BoundaryAllowed M a cutL) (hR : BoundaryAllowed M b cutR) (i : ℕ) :
    boundaryProjection M a b cutL cutR ha hb hL hR (leftE M a b i) =
      leftE (M - 1) (boundaryIndex a cutL) (boundaryIndex b cutR) i :=
  boundaryProjection_mk M a b cutL cutR ha hb hL hR (alphabetIn false (elementary i))

theorem boundaryProjection_rightE (M a b : ℕ) (cutL cutR : Bool)
    (ha : a ≤ M) (hb : b ≤ M)
    (hL : BoundaryAllowed M a cutL) (hR : BoundaryAllowed M b cutR) (i : ℕ) :
    boundaryProjection M a b cutL cutR ha hb hL hR (rightE M a b i) =
      rightE (M - 1) (boundaryIndex a cutL) (boundaryIndex b cutR) i :=
  boundaryProjection_mk M a b cutL cutR ha hb hL hR (alphabetIn true (elementary i))

theorem boundaryProjection_leftH (M a b : ℕ) (cutL cutR : Bool)
    (ha : a ≤ M) (hb : b ≤ M)
    (hL : BoundaryAllowed M a cutL) (hR : BoundaryAllowed M b cutR) (i : ℕ) :
    boundaryProjection M a b cutL cutR ha hb hL hR (leftH M a b i) =
      leftH (M - 1) (boundaryIndex a cutL) (boundaryIndex b cutR) i :=
  boundaryProjection_mk M a b cutL cutR ha hb hL hR (alphabetIn false (complete i))

theorem boundaryProjection_rightH (M a b : ℕ) (cutL cutR : Bool)
    (ha : a ≤ M) (hb : b ≤ M)
    (hL : BoundaryAllowed M a cutL) (hR : BoundaryAllowed M b cutR) (i : ℕ) :
    boundaryProjection M a b cutL cutR ha hb hL hR (rightH M a b i) =
      rightH (M - 1) (boundaryIndex a cutL) (boundaryIndex b cutR) i :=
  boundaryProjection_mk M a b cutL cutR ha hb hL hR (alphabetIn true (complete i))

theorem leftE_eq_zero (M a b i : ℕ) (hi : a < i) : leftE M a b i = 0 := by
  unfold leftE
  rw [eClass_eq_zero _ _ _ hi, map_zero]

theorem rightE_eq_zero (M a b i : ℕ) (hi : b < i) : rightE M a b i = 0 := by
  unfold rightE
  rw [eClass_eq_zero _ _ _ hi, map_zero]

theorem leftP_as_descending (M a b : ℕ) :
    leftP M a b = descendingPoly (fun i => (-1) ^ i * leftE M a b i) a := by
  rw [leftP_eq_sum, descendingPoly_eq_sum]

theorem rightP_as_descending (M a b : ℕ) :
    rightP M a b = descendingPoly (fun i => (-1) ^ i * rightE M a b i) b := by
  rw [rightP_eq_sum, descendingPoly_eq_sum]

theorem boundaryProjection_leftP (M a b : ℕ) (cutL cutR : Bool)
    (ha : a ≤ M) (hb : b ≤ M)
    (hL : BoundaryAllowed M a cutL) (hR : BoundaryAllowed M b cutR) :
    (leftP M a b).map (boundaryProjection M a b cutL cutR ha hb hL hR).toRingHom =
      if cutL then X * leftP (M - 1) (boundaryIndex a cutL) (boundaryIndex b cutR)
      else leftP (M - 1) (boundaryIndex a cutL) (boundaryIndex b cutR) := by
  rw [leftP_as_descending, descendingPoly_map]
  simp only [map_mul, map_pow, map_neg, map_one, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, boundaryProjection_leftE]
  cases cutL with
  | false =>
      simp only [Bool.false_eq_true, if_false, boundaryIndex, leftP_as_descending]
      rfl
  | true =>
      simp only [if_true, boundaryIndex, leftP_as_descending]
      have ha0 : 0 < a := hL
      have hs : a - 1 + 1 = a := by omega
      have hstep := descendingPoly_step
        (fun i => (-1) ^ i * leftE (M - 1) (a - 1) (boundaryIndex b cutR) i) (a - 1)
      rw [hs, leftE_eq_zero _ _ _ a (by omega), mul_zero, map_zero, add_zero] at hstep
      exact hstep

theorem boundaryProjection_rightP (M a b : ℕ) (cutL cutR : Bool)
    (ha : a ≤ M) (hb : b ≤ M)
    (hL : BoundaryAllowed M a cutL) (hR : BoundaryAllowed M b cutR) :
    (rightP M a b).map (boundaryProjection M a b cutL cutR ha hb hL hR).toRingHom =
      if cutR then X * rightP (M - 1) (boundaryIndex a cutL) (boundaryIndex b cutR)
      else rightP (M - 1) (boundaryIndex a cutL) (boundaryIndex b cutR) := by
  rw [rightP_as_descending, descendingPoly_map]
  simp only [map_mul, map_pow, map_neg, map_one, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, boundaryProjection_rightE]
  cases cutR with
  | false =>
      simp only [Bool.false_eq_true, if_false, boundaryIndex, rightP_as_descending]
      rfl
  | true =>
      simp only [if_true, boundaryIndex, rightP_as_descending]
      have hb0 : 0 < b := hR
      have hs : b - 1 + 1 = b := by omega
      have hstep := descendingPoly_step
        (fun i => (-1) ^ i * rightE (M - 1) (boundaryIndex a cutL) (b - 1) i) (b - 1)
      rw [hs, rightE_eq_zero _ _ _ b (by omega), mul_zero, map_zero, add_zero] at hstep
      exact hstep

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.boundaryProjection_leftP
#print axioms VOA.DeligneAudit.SL4T.boundaryProjection_rightP
