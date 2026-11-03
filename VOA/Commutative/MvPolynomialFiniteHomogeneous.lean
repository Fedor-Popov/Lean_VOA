/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import Mathlib.Data.Finsupp.Weight
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
# Finite-dimensional homogeneous multivariable-polynomial pieces

Mathlib identifies a weighted-homogeneous submodule with the finitely supported functions on the
set of monomial exponents of the prescribed weight.  If there are finitely many variables and all
weights are positive, that exponent set is finite.  This file packages the resulting
finite-dimensional instance used by the boundary-affine residual windows.
-/

namespace VOA.MvPolynomialFiniteHomogeneous

universe u v

variable {K : Type u} [Field K]
variable {I : Type v}

/-- The exponents of one fixed positive weighted degree form a finite set. -/
theorem finite_weightFiber [Finite I] (w : I → ℕ) (hw : ∀ i, w i ≠ 0) (n : ℕ) :
    {d : I →₀ ℕ | Finsupp.weight w d = n}.Finite :=
  (Finsupp.finite_of_nat_weight_le w hw n).subset fun _ hd ↦ hd.le

/-- Finsupps supported on a finite set form a finite-dimensional vector space. -/
theorem finiteDimensional_supported {s : Set I} (hs : s.Finite) :
    FiniteDimensional K (Finsupp.supported K K s) := by
  letI : Fintype s := hs.fintype
  exact FiniteDimensional.of_injective
    (Finsupp.supportedEquivFinsupp (R := K) s).toLinearMap
    (Finsupp.supportedEquivFinsupp (R := K) s).injective

/-- A fixed positive weighted-homogeneous piece in finitely many variables is finite-dimensional. -/
theorem finiteDimensional_weightedHomogeneousSubmodule [Finite I]
    (w : I → ℕ) (hw : ∀ i, w i ≠ 0) (n : ℕ) :
    FiniteDimensional K (MvPolynomial.weightedHomogeneousSubmodule K w n) := by
  rw [MvPolynomial.weightedHomogeneousSubmodule_eq_finsupp_supported]
  exact finiteDimensional_supported (finite_weightFiber w hw n)

/-- The ordinary homogeneous degree-`n` submodule in finitely many variables is
finite-dimensional. -/
theorem finiteDimensional_homogeneousSubmodule [Finite I] (n : ℕ) :
    FiniteDimensional K (MvPolynomial.homogeneousSubmodule I K n) := by
  rw [← MvPolynomial.weightedHomogeneousSubmodule_one]
  exact finiteDimensional_weightedHomogeneousSubmodule (fun _ : I ↦ 1) (fun _ ↦ one_ne_zero) n

end VOA.MvPolynomialFiniteHomogeneous
