import VOA.DeligneAudit.SL4TMonicCoefficientDual

/-! # Top coefficient minors of a variable-stable polynomial submodule

The polynomial submodule can be the inverse image of a submodule of the monic quotient.
Only stability under multiplication by the variable is required.
-/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open Polynomial

variable {A : Type*} [CommRing A]

/-- The top coefficient minors of a family in a polynomial submodule, reduced modulo `P`. -/
def polynomialSubmoduleTopIdeal (P : Polynomial A) (r j : ℕ)
    (U : Submodule A (Polynomial A)) : Ideal A :=
  Ideal.span {a | ∃ p : Fin j → U,
    Matrix.det (fun i b : Fin j => ((p b).val %ₘ P).coeff (r - j + i.val)) = a}

/-- All coefficient minors of a family in a polynomial submodule, reduced modulo `P`. -/
def polynomialSubmoduleAllIdeal (P : Polynomial A) (r j : ℕ)
    (U : Submodule A (Polynomial A)) : Ideal A :=
  Ideal.span {a | ∃ (rows : Fin j → Fin r) (p : Fin j → U),
    Matrix.det (fun i b : Fin j => ((p b).val %ₘ P).coeff (rows i).val) = a}

/-- Stability under the variable implies stability under each of its powers. -/
theorem polynomialSubmodule_variable_pow_mem (U : Submodule A (Polynomial A))
    (hU : ∀ p ∈ U, X * p ∈ U) (p : Polynomial A) (hp : p ∈ U) (n : ℕ) :
    X ^ n * p ∈ U := by
  induction n with
  | zero => simpa only [pow_zero, one_mul] using hp
  | succ n ih => simpa only [pow_succ', mul_assoc] using hU _ ih

/-- Consecutive highest-coordinate moments belong to the top coefficient ideal. -/
theorem stableSubmodule_consecutive_moment_minor_mem (P : Polynomial A) (r j : ℕ)
    (hP : P.Monic) (hr : P.natDegree = r) (hj : j ≤ r)
    (U : Submodule A (Polynomial A)) (hU : ∀ p ∈ U, X * p ∈ U)
    (p : Fin j → U) (d : Fin j → ℕ) :
    Matrix.det (fun a b : Fin j =>
      monicRemainderPairing P r (p b).val (X ^ (d b + a.val))) ∈
        polynomialSubmoduleTopIdeal P r j U := by
  classical
  nontriviality A
  let shifted : Fin j → U := fun b =>
    ⟨X ^ d b * (p b).val, polynomialSubmodule_variable_pow_mem U hU _ (p b).property _⟩
  let L : Fin j → Polynomial A →ₗ[A] A :=
    fun b => monicRemainderPairing P r (shifted b).val
  have hshift : (fun a b : Fin j =>
      monicRemainderPairing P r (p b).val (X ^ (d b + a.val))) =
      (fun a b : Fin j => L b (X ^ a.val)) := by
    ext a b
    simp only [L, shifted, monicRemainderPairing_apply, pow_add, mul_assoc, mul_left_comm]
  rw [hshift, ← polynomial_functional_determinant_monic L
    (fun a => monicCoefficientDual P r a.val)
    (fun a => (monicCoefficientDual_monic_degree P r a.val).1)
    (fun a => (monicCoefficientDual_monic_degree P r a.val).2)]
  let M : Matrix (Fin j) (Fin j) A := fun a b =>
    ((shifted b).val %ₘ P).coeff (r - j + a.val)
  have he : (fun a b => L b (monicCoefficientDual P r a.val)) =
      M.submatrix Fin.revPerm id := by
    ext a b
    rw [monicCoefficientDual_pairing P _ r a.val hP hr (by omega)]
    change _ = ((shifted b).val %ₘ P).coeff (r - j + (Fin.rev a).val)
    congr 1
    simp only [Fin.val_rev]
    omega
  rw [he, Matrix.det_permute]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨shifted, rfl⟩)

/-- Every coefficient minor lies in the top coefficient ideal of a variable-stable submodule. -/
theorem stableSubmodule_coefficient_minor_mem (P : Polynomial A) (r j : ℕ)
    (hP : P.Monic) (hr : P.natDegree = r) (hj : j ≤ r)
    (U : Submodule A (Polynomial A)) (hU : ∀ p ∈ U, X * p ∈ U)
    (p : Fin j → U) (rows : Fin j → Fin r) :
    Matrix.det (fun a b => ((p b).val %ₘ P).coeff (rows a).val) ∈
      polynomialSubmoduleTopIdeal P r j U := by
  have h := polynomial_functional_determinant_mem
    (fun b => monicRemainderPairing P r (p b).val)
    (polynomialSubmoduleTopIdeal P r j U)
    (stableSubmodule_consecutive_moment_minor_mem P r j hP hr hj U hU p)
    (fun a => monicCoefficientDual P r (r - 1 - (rows a).val))
  convert h using 1
  congr 1
  ext a b
  rw [monicCoefficientDual_pairing P _ r _ hP hr (by have := (rows a).isLt; omega)]
  congr 1
  have := (rows a).isLt
  omega

/-- Over any commutative ring, the top minors generate all minors of a
variable-stable submodule in a monic polynomial quotient. -/
theorem stableSubmodule_allIdeal_eq_topIdeal (P : Polynomial A) (r j : ℕ)
    (hP : P.Monic) (hr : P.natDegree = r) (hj : j ≤ r)
    (U : Submodule A (Polynomial A)) (hU : ∀ p ∈ U, X * p ∈ U) :
    polynomialSubmoduleAllIdeal P r j U = polynomialSubmoduleTopIdeal P r j U := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro a ⟨rows, p, rfl⟩
    exact stableSubmodule_coefficient_minor_mem P r j hP hr hj U hU p rows
  · apply Ideal.span_le.mpr
    rintro a ⟨p, rfl⟩
    exact Ideal.subset_span
      ⟨fun a => ⟨r - j + a.val, by omega⟩, p, rfl⟩

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.polynomialSubmodule_variable_pow_mem
#print axioms VOA.DeligneAudit.SL4T.stableSubmodule_consecutive_moment_minor_mem
#print axioms VOA.DeligneAudit.SL4T.stableSubmodule_coefficient_minor_mem
#print axioms VOA.DeligneAudit.SL4T.stableSubmodule_allIdeal_eq_topIdeal
