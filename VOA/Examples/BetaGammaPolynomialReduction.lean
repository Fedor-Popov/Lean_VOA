/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Examples.BetaGamma

/-!
# Polynomial reduction for the beta--gamma Fock space

The beta--gamma Fock space is the polynomial ring on variables indexed by `ℕ ⊕ ℕ`.  This file
isolates two elementary algebra facts used by its `C₂` and Poisson quotients.

* Modulo the linear span of all multiples of positive-level variables, every polynomial is
  represented by a polynomial in the two level-zero variables.
* Over `ℂ`, partial differentiation in any fixed variable is surjective.  In particular, the
  linear span of the two level-zero derivative images is the whole Fock space; the constant is
  included, since it is the derivative of the corresponding variable.

No vertex-algebra statement is made here.  The consuming file must separately prove that the
relevant variable multiples or derivative images lie in its relation submodule.
-/

namespace VOA.BetaGamma

open MvPolynomial

/-! ## The two-variable representative -/

/-- Polynomials in the two level-zero variables. -/
noncomputable abbrev ZeroFock := MvPolynomial (Fin 2) ℂ

/-- Include the two level-zero labels into the full beta--gamma alphabet. -/
def zeroIndex (i : Fin 2) : ℕ ⊕ ℕ :=
  if i = 0 then Sum.inl 0 else Sum.inr 0

@[simp] theorem zeroIndex_zero : zeroIndex (0 : Fin 2) = Sum.inl 0 := by
  simp [zeroIndex]

@[simp] theorem zeroIndex_one : zeroIndex (1 : Fin 2) = Sum.inr 0 := by
  simp [zeroIndex]

/-- Embed a polynomial in the two level-zero variables into the full Fock space. -/
noncomputable def zeroEmbed : ZeroFock →ₐ[ℂ] Fock :=
  MvPolynomial.rename zeroIndex

/-- Send the two level-zero variables to the two-variable polynomial ring and every positive-level
variable to zero. -/
noncomputable def zeroProjectVar : (ℕ ⊕ ℕ) → ZeroFock
  | Sum.inl 0 => X 0
  | Sum.inl (_ + 1) => 0
  | Sum.inr 0 => X 1
  | Sum.inr (_ + 1) => 0

/-- Project the full Fock polynomial ring onto its two level-zero variables. -/
noncomputable def zeroProject : Fock →ₐ[ℂ] ZeroFock :=
  MvPolynomial.aeval zeroProjectVar

@[simp] theorem zeroEmbed_C (c : ℂ) : zeroEmbed (C c) = C c := by
  simp [zeroEmbed]

@[simp] theorem zeroEmbed_X_zero : zeroEmbed (X (0 : Fin 2)) = X (Sum.inl 0) := by
  simp [zeroEmbed]

@[simp] theorem zeroEmbed_X_one : zeroEmbed (X (1 : Fin 2)) = X (Sum.inr 0) := by
  simp [zeroEmbed]

@[simp] theorem zeroProject_C (c : ℂ) : zeroProject (C c) = C c := by
  simp [zeroProject]

@[simp] theorem zeroProject_X_inl_zero : zeroProject (X (Sum.inl 0)) = X 0 := by
  simp [zeroProject, zeroProjectVar]

@[simp] theorem zeroProject_X_inr_zero : zeroProject (X (Sum.inr 0)) = X 1 := by
  simp [zeroProject, zeroProjectVar]

@[simp] theorem zeroProject_X_inl_succ (k : ℕ) :
    zeroProject (X (Sum.inl (k + 1))) = 0 := by
  simp [zeroProject, zeroProjectVar]

@[simp] theorem zeroProject_X_inr_succ (k : ℕ) :
    zeroProject (X (Sum.inr (k + 1))) = 0 := by
  simp [zeroProject, zeroProjectVar]

/-! ## The span of positive-level variable multiples -/

/-- A polynomial is a positive-variable multiple when it is divisible, with a displayed
cofactor, by a positive beta or gamma variable. -/
noncomputable def PositiveVariableMultiple (f : Fock) : Prop :=
  (∃ (k : ℕ) (v : Fock), f = X (Sum.inl (k + 1)) * v) ∨
    ∃ (k : ℕ) (v : Fock), f = X (Sum.inr (k + 1)) * v

/-- The `ℂ`-linear span of all positive-level beta and gamma variable multiples. -/
noncomputable def positiveVariableSpan : Submodule ℂ Fock :=
  Submodule.span ℂ {f | PositiveVariableMultiple f}

theorem X_inl_succ_mul_mem_positiveVariableSpan (k : ℕ) (v : Fock) :
    X (Sum.inl (k + 1)) * v ∈ positiveVariableSpan :=
  Submodule.subset_span (Or.inl ⟨k, v, rfl⟩)

theorem X_inr_succ_mul_mem_positiveVariableSpan (k : ℕ) (v : Fock) :
    X (Sum.inr (k + 1)) * v ∈ positiveVariableSpan :=
  Submodule.subset_span (Or.inr ⟨k, v, rfl⟩)

/-- Although defined only as a linear span, `positiveVariableSpan` is stable under multiplication
by an arbitrary polynomial. -/
theorem positiveVariableSpan_mul {f : Fock} (hf : f ∈ positiveVariableSpan) (g : Fock) :
    f * g ∈ positiveVariableSpan := by
  refine Submodule.span_induction
    (p := fun f _ => f * g ∈ positiveVariableSpan) ?_ ?_ ?_ ?_ hf
  · intro x hx
    rcases hx with ⟨k, v, rfl⟩ | ⟨k, v, rfl⟩
    · simpa only [mul_assoc] using X_inl_succ_mul_mem_positiveVariableSpan k (v * g)
    · simpa only [mul_assoc] using X_inr_succ_mul_mem_positiveVariableSpan k (v * g)
  · simp only [zero_mul, Submodule.zero_mem]
  · intro x y _ _ hx hy
    simpa only [add_mul] using (positiveVariableSpan.add_mem hx hy)
  · intro c x _ hx
    simpa only [smul_mul_assoc] using (positiveVariableSpan.smul_mem c hx)

/-- The full positive-variable span maps into any submodule containing every displayed positive
beta and gamma multiple. -/
theorem positiveVariableSpan_le (S : Submodule ℂ Fock)
    (hbeta : ∀ (k : ℕ) (v : Fock), X (Sum.inl (k + 1)) * v ∈ S)
    (hgamma : ∀ (k : ℕ) (v : Fock), X (Sum.inr (k + 1)) * v ∈ S) :
    positiveVariableSpan ≤ S := by
  rw [positiveVariableSpan, Submodule.span_le]
  intro f hf
  rcases hf with ⟨k, v, rfl⟩ | ⟨k, v, rfl⟩
  · exact hbeta k v
  · exact hgamma k v

/-- Subtracting the canonical two-variable projection leaves an element of the positive-variable
span. -/
theorem sub_zeroEmbed_zeroProject_mem (f : Fock) :
    f - zeroEmbed (zeroProject f) ∈ positiveVariableSpan := by
  induction f using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq =>
      have h := positiveVariableSpan.add_mem hp hq
      simpa only [map_add, add_sub_add_comm] using h
  | mul_X p i hp =>
      cases i with
      | inl k =>
          cases k with
          | zero =>
              have h := positiveVariableSpan_mul hp (X (Sum.inl 0))
              simpa only [map_mul, zeroProject_X_inl_zero, zeroEmbed_X_zero, sub_mul] using h
          | succ k =>
              have h := X_inl_succ_mul_mem_positiveVariableSpan k p
              simpa only [map_mul, zeroProject_X_inl_succ, map_zero, mul_zero, zero_mul, sub_zero,
                mul_comm] using h
      | inr k =>
          cases k with
          | zero =>
              have h := positiveVariableSpan_mul hp (X (Sum.inr 0))
              simpa only [map_mul, zeroProject_X_inr_zero, zeroEmbed_X_one, sub_mul] using h
          | succ k =>
              have h := X_inr_succ_mul_mem_positiveVariableSpan k p
              simpa only [map_mul, zeroProject_X_inr_succ, map_zero, mul_zero, zero_mul, sub_zero,
                mul_comm] using h

/-- Every full Fock polynomial is congruent modulo `positiveVariableSpan` to a polynomial in the
two level-zero variables. -/
theorem exists_zeroPolynomial_mod_positive (f : Fock) :
    ∃ q : ZeroFock, f - zeroEmbed q ∈ positiveVariableSpan :=
  ⟨zeroProject f, sub_zeroEmbed_zeroProject_mem f⟩

/-- Consumer form: the same two-variable representative exists modulo any submodule containing
all positive-level beta and gamma multiples. -/
theorem exists_zeroPolynomial_mod_of_positive_mem (S : Submodule ℂ Fock)
    (hbeta : ∀ (k : ℕ) (v : Fock), X (Sum.inl (k + 1)) * v ∈ S)
    (hgamma : ∀ (k : ℕ) (v : Fock), X (Sum.inr (k + 1)) * v ∈ S)
    (f : Fock) : ∃ q : ZeroFock, f - zeroEmbed q ∈ S := by
  refine ⟨zeroProject f, positiveVariableSpan_le S hbeta hgamma ?_⟩
  exact sub_zeroEmbed_zeroProject_mem f

/-! ## Algebraic integration -/

/-- Over `ℂ`, partial differentiation in any fixed variable of any multivariate polynomial ring
is surjective.  On a monomial, increase that variable's exponent by one and divide the coefficient
by the new positive exponent. -/
theorem pderiv_surjective {σ : Type*} (i : σ) :
    Function.Surjective (pderiv i : MvPolynomial σ ℂ → MvPolynomial σ ℂ) := by
  intro p
  induction p using MvPolynomial.induction_on' with
  | monomial m a =>
      let d : ℂ := ((m i + 1 : ℕ) : ℂ)
      have hd : d ≠ 0 := by
        dsimp [d]
        norm_cast
      refine ⟨monomial (m + (Finsupp.single i 1 : σ →₀ ℕ)) (a / d), ?_⟩
      rw [pderiv_monomial]
      have hsub : m + (Finsupp.single i 1 : σ →₀ ℕ) - Finsupp.single i 1 = m := by
        exact add_tsub_cancel_right m (Finsupp.single i 1)
      have happ : (m + (Finsupp.single i 1 : σ →₀ ℕ)) i = m i + 1 := by
        simp
      rw [hsub, happ]
      change monomial m ((a / d) * d) = monomial m a
      rw [div_mul_cancel₀ a hd]
  | add p q hp hq =>
      obtain ⟨P, hP⟩ := hp
      obtain ⟨Q, hQ⟩ := hq
      refine ⟨P + Q, ?_⟩
      simp only [map_add, hP, hQ]

/-- The concrete beta--gamma derivative endomorphism is surjective in every variable. -/
theorem der_surjective (i : ℕ ⊕ ℕ) : Function.Surjective (der i) := by
  intro f
  obtain ⟨g, hg⟩ := pderiv_surjective i f
  exact ⟨g, hg⟩

/-- A submodule containing every value of one fixed partial derivative is already the whole Fock
space. -/
theorem submodule_eq_top_of_der_mem (S : Submodule ℂ Fock) (i : ℕ ⊕ ℕ)
    (hder : ∀ f : Fock, der i f ∈ S) : S = ⊤ := by
  apply le_antisymm le_top
  intro f _
  obtain ⟨g, rfl⟩ := der_surjective i f
  exact hder g

/-- The linear span of the two level-zero partial-derivative images. -/
noncomputable def zeroDerivativeImageSpan : Submodule ℂ Fock :=
  Submodule.span ℂ
    (Set.range (der (Sum.inl 0)) ∪ Set.range (der (Sum.inr 0)))

/-- The two level-zero derivative images span the whole Fock space.  In fact the proof uses only
the beta derivative image. -/
theorem zeroDerivativeImageSpan_eq_top : zeroDerivativeImageSpan = ⊤ := by
  apply submodule_eq_top_of_der_mem zeroDerivativeImageSpan (Sum.inl 0)
  intro f
  exact Submodule.subset_span (Or.inl ⟨f, rfl⟩)

end VOA.BetaGamma
