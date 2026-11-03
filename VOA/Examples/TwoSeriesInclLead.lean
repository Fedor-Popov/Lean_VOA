/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.TwoSeriesInclDegOne

/-!
# Leading coefficients of a dual-number specialisation of `ℂ[T_j]`

Send `T_m ↦ a_m + ε b_m ∈ R[s][ε]` (`ε² = 0`), where `deg a_m ≤ 1` and `b_m` has degree `m + 1`
with leading coefficient `(-1)^{m+1}`.  For a `T`-polynomial `F` of degree `d` in `T_0, …, T_M`:

* `lead_list`, `lead_span` — the `ε`-part has `s`-degree at most `d + M`, and its
  `s^{d+M}` coefficient is `(-1)^{M+1} (∂_M F)(a'_0, a'_1, …)`, `a'_m` the `s`-coefficient of
  `a_m`.

Two facts about `ℂ[T_j]` used with it:

* `aeval_sq_injective` — `T₀ ↦ T₀², T_m ↦ T_m` (`m ≥ 1`) is injective;
* `not_mem_vars_of_pderiv_eq_zero` — `∂_M F = 0` forces `T_M ∉ vars F` (characteristic zero).

Everything is proved outright.
-/

namespace VOA.TwoSeries.StrictModel

open MvPolynomial

noncomputable section

namespace InclLead

variable {R : Type} [CommRing R] [Algebra ℂ R]

/-- The jet variables of `ℂ[T_j]`. -/
abbrev Xc : ℕ → MvPolynomial ℕ ℂ := X

/-- `T_m ↦ a_m + ε b_m`. -/
def theta (a b : ℕ → Polynomial R) : MvPolynomial ℕ ℂ →ₐ[ℂ] DualNumber (Polynomial R) :=
  aeval fun m => TrivSqZeroExt.inl (a m) + DualNumber.eps * TrivSqZeroExt.inl (b m)

/-- The `s`-coefficients of the `a_m`. -/
abbrev sb (a : ℕ → Polynomial R) : ℕ → R := fun m => (a m).coeff 1

theorem theta_X_mul (a b : ℕ → Polynomial R) (x : ℕ) (P : MvPolynomial ℕ ℂ) :
    (theta a b (X x * P)).fst = a x * (theta a b P).fst ∧
      (theta a b (X x * P)).snd = a x * (theta a b P).snd + b x * (theta a b P).fst := by
  have g1 : (TrivSqZeroExt.inl (a x) + DualNumber.eps * TrivSqZeroExt.inl (b x) :
      DualNumber (Polynomial R)).fst = a x := by simp
  have g2 : (TrivSqZeroExt.inl (a x) + DualNumber.eps * TrivSqZeroExt.inl (b x) :
      DualNumber (Polynomial R)).snd = b x := by simp
  rw [map_mul, TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, theta, aeval_X, g1, g2,
    smul_eq_mul, op_smul_eq_mul]
  exact ⟨rfl, by ring⟩

/-- **The leading coefficients of a `T`-monomial.** -/
theorem lead_list (a b : ℕ → Polynomial R) (ha : ∀ m, (a m).natDegree ≤ 1)
    (hb : ∀ m, (b m).natDegree ≤ m + 1) (hb1 : ∀ m, (b m).coeff (m + 1) = (-1) ^ (m + 1))
    (M : ℕ) : ∀ l : List ℕ, (∀ x ∈ l, x ≤ M) →
      (theta a b (l.map Xc).prod).fst.natDegree ≤ l.length ∧
      (theta a b (l.map Xc).prod).fst.coeff l.length = aeval (sb a) (l.map Xc).prod ∧
      (theta a b (l.map Xc).prod).snd.natDegree ≤ l.length + M ∧
      (theta a b (l.map Xc).prod).snd.coeff (l.length + M) =
        (-1) ^ (M + 1) * aeval (sb a) (pderiv M (l.map Xc).prod)
  | [], _ => by
    simp [theta]
  | x :: l, hl => by
    have hxM : x ≤ M := hl x (by simp)
    obtain ⟨h1, h2, h3, h4⟩ := lead_list a b ha hb hb1 M l fun y hy => hl y (by simp [hy])
    obtain ⟨e1, e2⟩ := theta_X_mul a b x (l.map Xc).prod
    simp only [List.map_cons, List.prod_cons, List.length_cons]
    set F := (theta a b (l.map Xc).prod).fst
    set S := (theta a b (l.map Xc).prod).snd
    rw [e1, e2]
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact Polynomial.natDegree_mul_le.trans (by have := ha x; omega)
    · rw [show l.length + 1 = 1 + l.length by ring,
        Polynomial.coeff_mul_add_eq_of_natDegree_le (ha x) h1, h2, map_mul, aeval_X]
    · refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
      · exact Polynomial.natDegree_mul_le.trans (by have := ha x; omega)
      · exact Polynomial.natDegree_mul_le.trans (by have := hb x; omega)
    · rw [Polynomial.coeff_add, show l.length + 1 + M = 1 + (l.length + M) by ring,
        Polynomial.coeff_mul_add_eq_of_natDegree_le (ha x) h3, h4, Derivation.leibniz, smul_eq_mul,
        smul_eq_mul, pderiv_X, map_add, map_mul, map_mul, aeval_X]
      by_cases hx : x = M
      · subst hx
        rw [show 1 + (l.length + x) = (x + 1) + l.length by ring,
          Polynomial.coeff_mul_add_eq_of_natDegree_le (hb x) h1, hb1, h2]
        simp
        ring
      · have hlt : x < M := lt_of_le_of_ne hxM hx
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt
          (lt_of_le_of_lt Polynomial.natDegree_mul_le (by have := hb x; omega))]
        simp [Ne.symm hx]
        ring

/-- The span of the `T`-monomials of degree `d` in `T_0, …, T_M`. -/
def V (M d : ℕ) : Submodule ℂ (MvPolynomial ℕ ℂ) :=
  Submodule.span ℂ {P | ∃ l : List ℕ, l.length = d ∧ (∀ x ∈ l, x ≤ M) ∧ (l.map Xc).prod = P}

/-- **The leading `ε`-coefficient on the span.** -/
theorem lead_span (a b : ℕ → Polynomial R) (ha : ∀ m, (a m).natDegree ≤ 1)
    (hb : ∀ m, (b m).natDegree ≤ m + 1) (hb1 : ∀ m, (b m).coeff (m + 1) = (-1) ^ (m + 1))
    {M d : ℕ} {F : MvPolynomial ℕ ℂ} (hF : F ∈ V M d) :
    (theta a b F).snd.natDegree ≤ d + M ∧
      (theta a b F).snd.coeff (d + M) = (-1) ^ (M + 1) * aeval (sb a) (pderiv M F) := by
  induction hF using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨l, rfl, hl, rfl⟩ := hP
    obtain ⟨-, -, h3, h4⟩ := lead_list a b ha hb hb1 M l hl
    exact ⟨h3, h4⟩
  | zero => simp
  | add P Q _ _ hP hQ =>
    refine ⟨?_, ?_⟩
    · rw [map_add, TrivSqZeroExt.snd_add]
      exact (Polynomial.natDegree_add_le _ _).trans (max_le hP.1 hQ.1)
    · rw [map_add, TrivSqZeroExt.snd_add, Polynomial.coeff_add, hP.2, hQ.2, map_add, map_add,
        mul_add]
  | smul c P _ hP =>
    refine ⟨?_, ?_⟩
    · rw [map_smul, TrivSqZeroExt.snd_smul]
      exact (Polynomial.natDegree_smul_le _ _).trans hP.1
    · rw [map_smul, TrivSqZeroExt.snd_smul, Polynomial.coeff_smul, hP.2, Derivation.map_smul,
        map_smul, mul_smul_comm]

/-! ### Two facts about `ℂ[T_j]` -/

/-- The exponent map `β ↦ β + β₀ e₀`. -/
def sqExp : (ℕ →₀ ℕ) →+ (ℕ →₀ ℕ) :=
  AddMonoidHom.id _ + (Finsupp.singleAddHom 0).comp (Finsupp.applyAddHom 0)

theorem sqExp_apply (β : ℕ →₀ ℕ) : sqExp β = β + Finsupp.single 0 (β 0) := rfl

theorem sqExp_injective : Function.Injective sqExp := by
  intro β γ h
  ext m
  have hm := DFunLike.congr_fun h m
  rw [sqExp_apply, sqExp_apply, Finsupp.add_apply, Finsupp.add_apply] at hm
  by_cases h0 : m = 0
  · subst h0
    simp only [Finsupp.single_eq_same] at hm
    omega
  · simpa [Finsupp.single_apply, Ne.symm h0] using hm

/-- `T₀ ↦ T₀²`, `T_m ↦ T_m`. -/
def sqMap : MvPolynomial ℕ ℂ →ₐ[ℂ] MvPolynomial ℕ ℂ :=
  aeval fun m => if m = 0 then X 0 ^ 2 else X m

/-- **`T₀ ↦ T₀²` is injective.** -/
theorem aeval_sq_injective : Function.Injective sqMap := by
  have h : sqMap = AddMonoidAlgebra.mapDomainAlgHom ℂ ℂ sqExp := by
    refine MvPolynomial.algHom_ext fun m => ?_
    rw [sqMap, aeval_X, AddMonoidAlgebra.mapDomainAlgHom_apply]
    change _ = AddMonoidAlgebra.mapDomain sqExp (AddMonoidAlgebra.single (Finsupp.single m 1) 1)
    rw [AddMonoidAlgebra.mapDomain_single, sqExp_apply]
    split_ifs with hm
    · subst hm
      rw [Finsupp.single_eq_same, ← Finsupp.single_add, X_pow_eq_monomial]
      rfl
    · rw [show Finsupp.single m 1 + Finsupp.single 0 ((Finsupp.single m 1) 0) =
          Finsupp.single m 1 by simp [Ne.symm hm]]
      rfl
  rw [h, AddMonoidAlgebra.mapDomainAlgHom]
  exact AddMonoidAlgebra.mapDomain_injective sqExp_injective

/-- **In characteristic zero, `∂_M F = 0` forces `T_M ∉ vars F`.** -/
theorem not_mem_vars_of_pderiv_eq_zero {F : MvPolynomial ℕ ℂ} {M : ℕ}
    (h : pderiv M F = 0) : M ∉ F.vars := by
  intro hM
  rw [mem_vars_iff_mem_support] at hM
  obtain ⟨β, hβ, hβM⟩ := hM
  have hβM' : β M ≠ 0 := Finsupp.mem_support_iff.mp hβM
  have hle : Finsupp.single M 1 ≤ β := by
    rw [Finsupp.single_le_iff]; omega
  have hc := congrArg (coeff (β - Finsupp.single M 1)) h
  rw [as_sum F, map_sum, coeff_sum, coeff_zero] at hc
  simp only [pderiv_monomial, coeff_monomial] at hc
  rw [Finset.sum_eq_single β] at hc
  · rw [if_pos rfl] at hc
    have hne : coeff β F ≠ 0 := mem_support_iff.mp hβ
    have : (β M : ℂ) ≠ 0 := by exact_mod_cast hβM'
    exact mul_ne_zero hne this hc
  · intro γ _ hγ
    split_ifs with heq
    · have hγM : γ M = 0 := by
        by_contra hγM
        have hle' : Finsupp.single M 1 ≤ γ := by rw [Finsupp.single_le_iff]; omega
        exact hγ (by rw [← tsub_add_cancel_of_le hle', heq, tsub_add_cancel_of_le hle])
      simp [hγM]
    · rfl
  · intro hβ'; exact absurd hβ hβ'

end InclLead

end

end VOA.TwoSeries.StrictModel
