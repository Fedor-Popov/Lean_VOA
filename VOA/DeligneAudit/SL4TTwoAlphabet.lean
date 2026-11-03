import VOA.DeligneAudit.SL4TCharacteristic
import Mathlib.Algebra.MvPolynomial.Rename

/-!
# Two Grassmannian alphabets in a fixed polynomial presentation

The two copies of the elementary generators are independent. Taking the sum of the
two extended Grassmannian ideals presents their tensor product over `ℂ`, without
requiring tensor-product representatives. All site-peeling maps keep this ambient ring.
-/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open Polynomial

abbrev BiSymPoly := MvPolynomial (Bool × ℕ) ℂ

/-- Insert a symmetric polynomial into one of the two alphabets. -/
def alphabetIn (side : Bool) : SymPoly →ₐ[ℂ] BiSymPoly :=
  MvPolynomial.rename (fun i => (side, i))

/-- The relations in the two independent rectangles. -/
def biGrassIdeal (a A b B : ℕ) : Ideal BiSymPoly :=
  (grassIdeal a A).map (alphabetIn false) ⊔ (grassIdeal b B).map (alphabetIn true)

abbrev BiGrass (a A b B : ℕ) := BiSymPoly ⧸ biGrassIdeal a A b B

/-- The two-alphabet ring `S_M(a,b)`. Intended use has `a,b ≤ M`. -/
abbrev S (M a b : ℕ) := BiGrass a (M - a) b (M - b)

def biLeft (a A b B : ℕ) : GrassRing a A →ₐ[ℂ] BiGrass a A b B :=
  Ideal.quotientMapₐ _ (alphabetIn false) (Ideal.map_le_iff_le_comap.mp le_sup_left)

def biRight (a A b B : ℕ) : GrassRing b B →ₐ[ℂ] BiGrass a A b B :=
  Ideal.quotientMapₐ _ (alphabetIn true) (Ideal.map_le_iff_le_comap.mp le_sup_right)

theorem biLeft_mk (a A b B : ℕ) (p : SymPoly) :
    biLeft a A b B (Ideal.Quotient.mk _ p) =
      Ideal.Quotient.mk _ (alphabetIn false p) := rfl

theorem biRight_mk (a A b B : ℕ) (p : SymPoly) :
    biRight a A b B (Ideal.Quotient.mk _ p) =
      Ideal.Quotient.mk _ (alphabetIn true p) := rfl

def leftE (M a b i : ℕ) : S M a b := biLeft a (M - a) b (M - b) (eClass a (M - a) i)

def rightE (M a b i : ℕ) : S M a b :=
  biRight a (M - a) b (M - b) (eClass b (M - b) i)

def leftH (M a b i : ℕ) : S M a b := biLeft a (M - a) b (M - b) (hClass a (M - a) i)

def rightH (M a b i : ℕ) : S M a b :=
  biRight a (M - a) b (M - b) (hClass b (M - b) i)

def leftP (M a b : ℕ) : (S M a b)[X] :=
  (grassP a (M - a)).map (biLeft a (M - a) b (M - b)).toRingHom

def leftPbar (M a b : ℕ) : (S M a b)[X] :=
  (grassPbar a (M - a)).map (biLeft a (M - a) b (M - b)).toRingHom

def rightP (M a b : ℕ) : (S M a b)[X] :=
  (grassP b (M - b)).map (biRight a (M - a) b (M - b)).toRingHom

def rightPbar (M a b : ℕ) : (S M a b)[X] :=
  (grassPbar b (M - b)).map (biRight a (M - a) b (M - b)).toRingHom

theorem leftP_eq_sum (M a b : ℕ) :
    leftP M a b = ∑ i ∈ Finset.range (a + 1),
      Polynomial.C ((-1) ^ i * leftE M a b i) * X ^ (a - i) := by
  simp [leftP, grassP_eq_sum, Polynomial.map_sum, leftE]

theorem rightP_eq_sum (M a b : ℕ) :
    rightP M a b = ∑ i ∈ Finset.range (b + 1),
      Polynomial.C ((-1) ^ i * rightE M a b i) * X ^ (b - i) := by
  simp [rightP, grassP_eq_sum, Polynomial.map_sum, rightE]

theorem leftPbar_eq_sum (M a b : ℕ) :
    leftPbar M a b = ∑ i ∈ Finset.range (M - a + 1),
      Polynomial.C (leftH M a b i) * X ^ (M - a - i) := by
  simp [leftPbar, grassPbar_eq_sum, Polynomial.map_sum, leftH]

theorem rightPbar_eq_sum (M a b : ℕ) :
    rightPbar M a b = ∑ i ∈ Finset.range (M - b + 1),
      Polynomial.C (rightH M a b i) * X ^ (M - b - i) := by
  simp [rightPbar, grassPbar_eq_sum, Polynomial.map_sum, rightH]

theorem leftP_constant (M a b : ℕ) :
    (leftP M a b).coeff 0 = (-1) ^ a * leftE M a b a := by
  simp [leftP, grassP_constant, leftE]

theorem rightP_constant (M a b : ℕ) :
    (rightP M a b).coeff 0 = (-1) ^ b * rightE M a b b := by
  simp [rightP, grassP_constant, rightE]

theorem leftPbar_constant (M a b : ℕ) :
    (leftPbar M a b).coeff 0 = leftH M a b (M - a) := by
  simp [leftPbar, grassPbar_constant, leftH]

theorem rightPbar_constant (M a b : ℕ) :
    (rightPbar M a b).coeff 0 = rightH M a b (M - b) := by
  simp [rightPbar, grassPbar_constant, rightH]

theorem left_characteristic_product (M a b : ℕ) (ha : a ≤ M) :
    leftP M a b * leftPbar M a b = X ^ M := by
  rw [leftP, leftPbar, ← Polynomial.map_mul, H_characteristic_product a M ha]
  simp

theorem right_characteristic_product (M a b : ℕ) (hb : b ≤ M) :
    rightP M a b * rightPbar M a b = X ^ M := by
  rw [rightP, rightPbar, ← Polynomial.map_mul, H_characteristic_product b M hb]
  simp

theorem left_boundary_product (M a b : ℕ) (hM : 0 < M) (ha : a ≤ M) :
    leftE M a b a * leftH M a b (M - a) = 0 := by
  unfold leftE leftH
  rw [← map_mul, grass_boundary_product a (M - a) (by omega), map_zero]

theorem right_boundary_product (M a b : ℕ) (hM : 0 < M) (hb : b ≤ M) :
    rightE M a b b * rightH M a b (M - b) = 0 := by
  unfold rightE rightH
  rw [← map_mul, grass_boundary_product b (M - b) (by omega), map_zero]

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.left_characteristic_product
#print axioms VOA.DeligneAudit.SL4T.right_characteristic_product
#print axioms VOA.DeligneAudit.SL4T.left_boundary_product
#print axioms VOA.DeligneAudit.SL4T.right_boundary_product
