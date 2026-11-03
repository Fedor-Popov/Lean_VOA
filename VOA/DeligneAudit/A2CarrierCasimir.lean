/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.A2Relations
import VOA.Commutative.FiniteJet

/-!
# Input U3 for A₂: the Casimir is annihilated by the currents modulo `I₂ⁿˢ`

The auxiliary (Casimir) filtration of the Deligne chain (step B1) needs, in the ring
`R̃ = Sym sl₃ / I₂ⁿˢ`, the identities `X · Q = 0` for every current `X` and `Q² = 0`, where `Q` is the
quadratic Casimir.  For A₂ this is Cayley–Hamilton for the matrix `Z` of `A2Relations`; here it is
proved by explicit integer certificates
`X a * casimir = Σ_b ℓ_{a b} * relationPoly b` with linear `ℓ_{a b}`
(found by exact rational elimination, then checked by `ring`).

Coordinates are those of `A2Relations` (`e₁, e₂, e₁₂, f₁, f₂, f₁₂, h₁, h₂`).  The Casimir is
`3 Σ_a x_a x^a` for the trace form:
`casimir = 2h₁² + 2h₁h₂ + 2h₂² + 6(e₁f₁ + e₂f₂ + e₁₂f₁₂)`.
-/

namespace VOA.DeligneAudit.A2

open MvPolynomial

noncomputable section

/-- The quadratic Casimir of `sl₃` (three times the trace-form Casimir) in current coordinates. -/
def casimir : MvPolynomial (Fin 8) ℂ :=
  2 * q 6 6 + 2 * q 6 7 + 2 * q 7 7 + 6 * q 0 3 + 6 * q 1 4 + 6 * q 2 5

/-- A polynomial combination of the relations lies in `I₂ⁿˢ`. -/
theorem mem_I2ns_of_eq_sum (f : MvPolynomial (Fin 8) ℂ) (ℓ : Fin 8 → MvPolynomial (Fin 8) ℂ)
    (h : f = ∑ b, ℓ b * relationPoly b) : f ∈ I2ns := by
  rw [h]
  exact Submodule.sum_mem _ fun b _ => Ideal.mul_mem_left _ _ (relationPoly_mem_I2ns b)

/-- The explicit linear multipliers:
`X a * casimir = Σ_b casimirCertificate a b * relationPoly b`. -/
def casimirCertificate : Fin 8 → Fin 8 → MvPolynomial (Fin 8) ℂ :=
  ![![2 * X 6 + 2 * X 7, 0, 2 * X 4, 0, 4 * X 2, 0, 0, 2 * X 0],
    ![0, -2 * X 6 - 2 * X 7, 2 * X 3, 4 * X 2, 0, 0, -2 * X 1, 0],
    ![4 * X 1, 2 * X 0, -2 * X 7, 0, 0, 0, 2 * X 2, 0],
    ![0, 4 * X 5, 0, 2 * X 6 + 2 * X 7, 0, 2 * X 1, 0, 2 * X 3],
    ![4 * X 5, 0, 0, 0, -2 * X 6 - 2 * X 7, 2 * X 0, -2 * X 4, 0],
    ![0, 0, 0, 4 * X 4, 2 * X 3, -2 * X 7, 2 * X 5, 0],
    ![6 * X 3, -6 * X 4, 6 * X 5, -6 * X 0, 0, 0, 2 * X 6 + 2 * X 7, 2 * X 6],
    ![0, 0, -6 * X 5, 6 * X 0, 0, 0, -2 * X 7, -2 * X 6 - 2 * X 7]]

theorem X_mul_casimir_eq (a : Fin 8) :
    X a * casimir = ∑ b, casimirCertificate a b * relationPoly b := by
  fin_cases a <;>
    simp [Fin.sum_univ_eight, casimirCertificate, relationPoly, casimir, q] <;> ring

/-- **U3 for A₂.**  Every current times the Casimir lies in `I₂ⁿˢ`. -/
theorem X_mul_casimir_mem_I2ns (a : Fin 8) : X a * casimir ∈ I2ns :=
  mem_I2ns_of_eq_sum _ _ (X_mul_casimir_eq a)

/-- Hence any polynomial without constant term times the Casimir lies in `I₂ⁿˢ`; in particular
every linear form. -/
theorem mul_casimir_mem_I2ns_of_mem_span_X (f : MvPolynomial (Fin 8) ℂ)
    (hf : f ∈ Ideal.span (Set.range (X : Fin 8 → MvPolynomial (Fin 8) ℂ))) :
    f * casimir ∈ I2ns := by
  refine Submodule.span_induction (p := fun f _ => f * casimir ∈ I2ns) ?_ ?_ ?_ ?_ hf
  · rintro _ ⟨a, rfl⟩
    exact X_mul_casimir_mem_I2ns a
  · simp
  · intro f g _ _ hf hg
    rw [add_mul]
    exact Ideal.add_mem _ hf hg
  · intro r f _ hf
    rw [smul_eq_mul, mul_assoc]
    exact Ideal.mul_mem_left _ r hf

theorem casimir_mem_span_X :
    casimir ∈ Ideal.span (Set.range (X : Fin 8 → MvPolynomial (Fin 8) ℂ)) := by
  have hX : ∀ a, (X a : MvPolynomial (Fin 8) ℂ) ∈
      Ideal.span (Set.range (X : Fin 8 → MvPolynomial (Fin 8) ℂ)) :=
    fun a => Ideal.subset_span ⟨a, rfl⟩
  unfold casimir q
  refine Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _
    (Ideal.add_mem _ ?_ ?_) ?_) ?_) ?_) ?_ <;>
    exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (hX _))

/-- **`Q² = 0` in `R̃`.** -/
theorem casimir_sq_mem_I2ns : casimir * casimir ∈ I2ns :=
  mul_casimir_mem_I2ns_of_mem_span_X _ casimir_mem_span_X

/-- The Casimir is homogeneous of degree two. -/
theorem casimir_isHomogeneous : casimir.IsHomogeneous 2 := by
  rw [← mem_homogeneousSubmodule]
  unfold casimir
  repeat' first
    | exact q_mem _ _
    | apply ofNat_mul_mem
    | apply Submodule.add_mem

/-! ### Jet-level consequences (the mixed and Casimir-square jet relations of step B1) -/

open VOA.FiniteJet in
/-- **Mixed jet relations vanish in `Jet R̃`.**  For every order `n ≤ M`,
`Σ_{i+j=n} x_a^{(i)} Q_{(j)} ∈ jetIdeal M I₂ⁿˢ`. -/
theorem mixed_jetRelation_mem (M n : ℕ) (hn : n ≤ M) (a : Fin 8) :
    (∑ ij ∈ Finset.antidiagonal n,
        relationCoeff (R := ℂ) M ij.1 (X a) * relationCoeff (R := ℂ) M ij.2 casimir) ∈
      jetIdeal (R := ℂ) M I2ns := by
  rw [← relationCoeff_mul]
  exact relationCoeff_mem_jetIdeal M n I2ns _ (X_mul_casimir_mem_I2ns a) hn

open VOA.FiniteJet in
/-- **Casimir-square jet relations vanish in `Jet R̃`.** -/
theorem casimirSq_jetRelation_mem (M n : ℕ) (hn : n ≤ M) :
    (∑ ij ∈ Finset.antidiagonal n,
        relationCoeff (R := ℂ) M ij.1 casimir * relationCoeff (R := ℂ) M ij.2 casimir) ∈
      jetIdeal (R := ℂ) M I2ns := by
  rw [← relationCoeff_mul]
  exact relationCoeff_mem_jetIdeal M n I2ns _ casimir_sq_mem_I2ns hn

end

end VOA.DeligneAudit.A2

section AxiomAudit
open VOA.DeligneAudit.A2
#print axioms X_mul_casimir_eq
#print axioms X_mul_casimir_mem_I2ns
#print axioms casimir_sq_mem_I2ns
#print axioms casimir_isHomogeneous
#print axioms mixed_jetRelation_mem
#print axioms casimirSq_jetRelation_mem
end AxiomAudit
