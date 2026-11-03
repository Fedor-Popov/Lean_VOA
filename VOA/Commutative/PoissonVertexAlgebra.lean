import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Nat.Choose.Basic

/-!
# Poisson vertex algebras in nonnegative-mode form

Over the complex numbers the locally finite modes `a_(n)b` encode the polynomial
lambda bracket by the coefficient convention `a_(n)b / n!`. The structure records
locality, both translation laws, skew-symmetry, Jacobi, and the Leibniz rule.
-/

namespace VOA
open scoped BigOperators

/-- A complex Poisson vertex algebra, expressed by its nonnegative products.
The translation derivation and the products are independent data; every structural
identity is an explicit obligation. -/
structure PoissonVertexAlgebra (A : Type*) [CommRing A] [Algebra ℂ A] where
  /-- The translation derivation of the underlying commutative algebra. -/
  translation : Derivation ℂ A A
  /-- The nonnegative products, bilinear in both entries. -/
  mode : ℕ → A →ₗ[ℂ] A →ₗ[ℂ] A
  /-- Only finitely many nonnegative products contribute for any pair of elements. -/
  locality : ∀ x y, ∃ B : ℕ, ∀ n, B ≤ n → mode n x y = 0
  /-- The zeroth product of a translated first entry vanishes. -/
  translation_left_zero : ∀ x y, mode 0 (translation x) y = 0
  /-- The positive products obey left sesquilinearity. -/
  translation_left_succ : ∀ n x y,
    mode (n + 1) (translation x) y = (-((n + 1 : ℕ) : ℂ)) • mode n x y
  /-- Translation is a derivation of each product, equivalently right sesquilinearity
  together with the left translation laws. -/
  translation_mode : ∀ n x y,
    translation (mode n x y) = mode n (translation x) y + mode n x (translation y)
  /-- Each mode is a derivation in its second argument. -/
  leibniz : ∀ n x y z, mode n x (y * z) = mode n x y * z + y * mode n x z
  /-- Skew-symmetry, with the formal substitution of negative translation and lambda. -/
  skew : ∀ n x y, mode n x y = ∑ᶠ j : ℕ,
    (j.factorial : ℂ)⁻¹ • (-1 : ℂ) ^ (n + j + 1) •
      ((translation.toLinearMap ^ j) (mode (n + j) y x))
  /-- Jacobi in finite nonnegative-mode form. -/
  jacobi : ∀ m n x y z,
    mode m x (mode n y z) - mode n y (mode m x z) =
      ∑ j : Fin (m + 1), (m.choose j.val : ℂ) • mode (m + n - j.val) (mode j.val x y) z

end VOA
