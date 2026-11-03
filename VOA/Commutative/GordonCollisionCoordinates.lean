/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Commutative.GordonTwoBlock

/-!
# Transport from displacement vanishing to a two-block difference divisor

The coefficient ring is arbitrary. Thus all other block variables and residual
variables may remain formal coefficient parameters during this argument.
-/

namespace VOA.GordonCollisionCoordinates

open Polynomial VOA.SymmetricOccupancy VOA.GordonTwoBlock

noncomputable section

variable {σ K : Type*} [DecidableEq σ] [CommRing K]

/-- Two genuine independent block variables, indexed by `Bool`. -/
def twoValueEval (S : Finset σ) : MvPolynomial σ K →+* MvPolynomial Bool K :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (fun i ↦ if i ∈ S then MvPolynomial.X true else MvPolynomial.X false)

/-- Undo the displacement coordinates by sending the center to the second block
variable and the displacement to the first minus the second. -/
def unshift : Polynomial K[X] →+* MvPolynomial Bool K :=
  Polynomial.eval₂RingHom
    (Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X false))
    (MvPolynomial.X true - MvPolynomial.X false)

theorem unshift_shiftedSpecialize (S : Finset σ) (F : MvPolynomial σ K) :
    unshift (shiftedSpecialize Polynomial.X S (MvPolynomial.map Polynomial.C F)) =
      twoValueEval S F := by
  induction F using MvPolynomial.induction_on with
  | C a => simp [unshift, shiftedSpecialize, twoValueEval]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp]
    congr 1
    by_cases hi : i ∈ S
    · simp [unshift, shiftedSpecialize, twoValueEval, hi]
    · simp [unshift, shiftedSpecialize, twoValueEval, hi]

/-- Divisibility by a displacement power transports to the corresponding power of
the difference of the two independent block variables. -/
theorem difference_pow_dvd_of_shifted (S : Finset σ) (F : MvPolynomial σ K) (m : ℕ)
    (h : Polynomial.X ^ m ∣
      shiftedSpecialize Polynomial.X S (MvPolynomial.map Polynomial.C F)) :
    (MvPolynomial.X true - MvPolynomial.X false) ^ m ∣ twoValueEval S F := by
  have hm := map_dvd (unshift (K := K)) h
  rw [map_pow, unshift_shiftedSpecialize] at hm
  simpa [unshift] using hm

/-- Forward displacement coordinates for the two block variables. -/
def shift : MvPolynomial Bool K →+* Polynomial K[X] :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp Polynomial.C)
    (fun b ↦ if b then Polynomial.C Polynomial.X + Polynomial.X else Polynomial.C Polynomial.X)

theorem shift_twoValueEval (S : Finset σ) (F : MvPolynomial σ K) :
    shift (twoValueEval S F) =
      shiftedSpecialize Polynomial.X S (MvPolynomial.map Polynomial.C F) := by
  induction F using MvPolynomial.induction_on with
  | C a => simp [shift, shiftedSpecialize, twoValueEval]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp]
    congr 1
    by_cases hi : i ∈ S
    · simp [shift, shiftedSpecialize, twoValueEval, hi]
    · simp [shift, shiftedSpecialize, twoValueEval, hi]

variable [Algebra ℚ K] [IsDomain K] [CharZero K]

/-- The explicit two-block Gordon multiplicity in independent block variables. -/
theorem difference_pow_two_mul_dvd {a b : ℕ} (hab : b ≤ a)
    (F : MvPolynomial (Fin (a + b)) K) (hF : F.IsSymmetric)
    (hlow : ∀ i : Fin b, twoValueEval (initialVariables (a + b) i.val) F = 0)
    (hhigh : ∀ i : Fin b,
      twoValueEval (initialVariables (a + b) (a + 1 + i.val)) F = 0) :
    (MvPolynomial.X true - MvPolynomial.X false) ^ (2 * b) ∣
      twoValueEval (initialVariables (a + b) a) F := by
  apply difference_pow_dvd_of_shifted
  apply X_pow_two_mul_dvd_twoBlock hab (MvPolynomial.map Polynomial.C F)
    (hF.map Polynomial.C) Polynomial.X
  · intro i
    rw [← shift_twoValueEval, hlow i, map_zero]
  · intro i
    rw [← shift_twoValueEval, hhigh i, map_zero]

end
end VOA.GordonCollisionCoordinates
