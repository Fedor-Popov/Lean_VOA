import VOA.Examples.HeisenbergNCentral
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.LinearAlgebra.Basis.Bilinear
import Mathlib.Data.Complex.BigOperators

/-! # OrbSpan: the positive-definite Hermitian form on the rank-`r` Fock space

`FockN r = ℂ[X_{(i,a)}]`, where `X_{(i,a)}` stands for `aᵃ(-i-1)`. The monomial `X^μ` gets
norm `w(μ) = ∏ (i+1)^{μ(i,a)} μ(i,a)!`, monomials are orthogonal. Then (level `k = 1`)

* `fockForm_oscN`: `⟨aᵃ(n)p, q⟩ = ⟨p, aᵃ(-n)q⟩`;
* `fockForm_LvirN`: `⟨L(m)p, q⟩ = ⟨p, L(-m)q⟩` for the Sugawara modes;
* `fockForm_hermitian`, `fockForm_pos`.
-/

set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbSpan
open VOA HeisenbergN MvPolynomial

variable {r : ℕ}

/-- The weight factor of one variable. -/
def fwf (x : ℕ × Fin r) (k : ℕ) : ℕ := (x.1 + 1) ^ k * k.factorial

/-- The norm of a monomial. -/
def fw (μ : (ℕ × Fin r) →₀ ℕ) : ℕ := μ.prod fwf

theorem fwf_zero (x : ℕ × Fin r) : fwf x 0 = 1 := by simp [fwf]

theorem fw_pos (μ : (ℕ × Fin r) →₀ ℕ) : 0 < fw μ :=
  Finset.prod_pos fun x _ => by unfold fwf; positivity

theorem fw_eq_prod (μ : (ℕ × Fin r) →₀ ℕ) {S : Finset (ℕ × Fin r)} (hS : μ.support ⊆ S) :
    fw μ = ∏ x ∈ S, fwf x (μ x) :=
  Finsupp.prod_of_support_subset μ hS fwf (fun x _ => fwf_zero x)

theorem fw_add_single (ρ : (ℕ × Fin r) →₀ ℕ) (e : ℕ × Fin r) :
    fw (ρ + Finsupp.single e 1) = fw ρ * ((e.1 + 1) * (ρ e + 1)) := by
  classical
  set S := insert e ρ.support
  have h1 : (ρ + Finsupp.single e 1).support ⊆ S := fun x hx => by
    rcases Finset.mem_union.mp (Finsupp.support_add hx) with h | h
    · exact Finset.mem_insert_of_mem h
    · rw [Finset.mem_singleton.mp (Finsupp.support_single_subset h)]
      exact Finset.mem_insert_self _ _
  have h2 : ρ.support ⊆ S := Finset.subset_insert _ _
  have he : e ∈ S := Finset.mem_insert_self _ _
  rw [fw_eq_prod _ h1, fw_eq_prod _ h2, ← Finset.mul_prod_erase S _ he,
    ← Finset.mul_prod_erase S _ he]
  have hrest : ∏ x ∈ S.erase e, fwf x ((ρ + Finsupp.single e 1 : (ℕ × Fin r) →₀ ℕ) x) =
      ∏ x ∈ S.erase e, fwf x (ρ x) := by
    apply Finset.prod_congr rfl
    intro x hx
    rw [Finsupp.add_apply, Finsupp.single_eq_of_ne (Finset.ne_of_mem_erase hx), add_zero]
  rw [hrest, Finsupp.add_apply, Finsupp.single_eq_same]
  simp only [fwf, pow_succ, Nat.factorial_succ]
  ring

/-- The raw pairing (linear on the left, conjugate-linear on the right). -/
def fockPair (p q : FockN r) : ℂ :=
  ∑ μ ∈ p.support, (fw μ : ℂ) * p.coeff μ * starRingEnd ℂ (q.coeff μ)

theorem fockPair_eq_sum (p q : FockN r) {S : Finset ((ℕ × Fin r) →₀ ℕ)}
    (hS : p.support ⊆ S) :
    fockPair p q = ∑ μ ∈ S, (fw μ : ℂ) * p.coeff μ * starRingEnd ℂ (q.coeff μ) := by
  apply Finset.sum_subset hS
  intro μ _ hμ
  rw [MvPolynomial.notMem_support_iff.mp hμ]
  simp

/-- The Hermitian Fock form. -/
def fockForm : FockN r →ₗ[ℂ] FockN r →ₗ⋆[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) fockPair
    (fun p p' q => by
      classical
      have hS : (p + p').support ⊆ p.support ∪ p'.support := MvPolynomial.support_add
      rw [fockPair_eq_sum _ _ hS, fockPair_eq_sum p q Finset.subset_union_left,
        fockPair_eq_sum p' q Finset.subset_union_right, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro μ _
      rw [MvPolynomial.coeff_add]
      ring)
    (fun c p q => by
      classical
      rw [fockPair_eq_sum _ _ (MvPolynomial.support_smul (a := c) (f := p)), fockPair,
        RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro μ _
      rw [MvPolynomial.coeff_smul, smul_eq_mul]
      ring)
    (fun p q q' => by
      simp only [fockPair, MvPolynomial.coeff_add, map_add, mul_add, Finset.sum_add_distrib])
    (fun c p q => by
      simp only [fockPair, MvPolynomial.coeff_smul, smul_eq_mul, map_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro μ _
      ring)

theorem fockForm_apply (p q : FockN r) : fockForm p q = fockPair p q := rfl

theorem fockForm_hermitian (p q : FockN r) :
    fockForm q p = starRingEnd ℂ (fockForm p q) := by
  classical
  rw [fockForm_apply, fockForm_apply, fockPair_eq_sum q p (Finset.subset_union_right
      (s₁ := p.support)), fockPair_eq_sum p q (Finset.subset_union_left (s₂ := q.support)),
    map_sum]
  apply Finset.sum_congr rfl
  intro μ _
  simp only [map_mul, Complex.conj_conj, map_natCast]
  ring

theorem fockForm_self_re (p : FockN r) :
    (fockForm p p).re = ∑ μ ∈ p.support, (fw μ : ℝ) * Complex.normSq (p.coeff μ) := by
  rw [fockForm_apply, fockPair]
  simp only [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro μ _
  rw [mul_assoc, Complex.mul_conj]
  simp [← Complex.ofReal_natCast, Complex.re_ofReal_mul]

theorem fockForm_pos {p : FockN r} (hp : p ≠ 0) : 0 < (fockForm p p).re := by
  rw [fockForm_self_re]
  have hne : p.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, Ne, MvPolynomial.support_eq_empty]; exact hp
  apply Finset.sum_pos _ hne
  intro μ hμ
  have hc : p.coeff μ ≠ 0 := MvPolynomial.mem_support_iff.mp hμ
  have := fw_pos μ
  exact mul_pos (by exact_mod_cast this) (Complex.normSq_pos.mpr hc)

theorem fockForm_monomial (μ ν : (ℕ × Fin r) →₀ ℕ) (a b : ℂ) :
    fockForm (monomial μ a) (monomial ν b) =
      if μ = ν then (fw μ : ℂ) * a * starRingEnd ℂ b else 0 := by
  classical
  rw [fockForm_apply, fockPair_eq_sum _ _ (MvPolynomial.support_monomial_subset (s := μ) (a := a)),
    Finset.sum_singleton, MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial, if_pos rfl]
  by_cases h : μ = ν
  · subst h; simp
  · rw [if_neg (Ne.symm h), if_neg h]; simp

/-- Creation and (scaled) annihilation are adjoint. -/
theorem fockForm_X_mul (e : ℕ × Fin r) (p q : FockN r) :
    fockForm (X e * p) q = fockForm p ((((e.1 + 1 : ℕ)) : ℂ) • pderiv e q) := by
  classical
  have key : (fockForm (r := r)).comp (LinearMap.mul ℂ (FockN r) (X e)) =
      (fockForm (r := r)).compl₂ ((((e.1 + 1 : ℕ)) : ℂ) •
        (pderiv e : Derivation ℂ (FockN r) (FockN r)).toLinearMap) := by
    apply LinearMap.ext_basis (MvPolynomial.basisMonomials _ ℂ)
      (MvPolynomial.basisMonomials _ ℂ)
    intro μ ν
    simp only [MvPolynomial.coe_basisMonomials, LinearMap.comp_apply, LinearMap.compl₂_apply,
      LinearMap.mul_apply', LinearMap.smul_apply, Derivation.coeFn_coe]
    rw [X, MvPolynomial.monomial_mul, pderiv_monomial, MvPolynomial.smul_monomial,
      fockForm_monomial, fockForm_monomial]
    by_cases hν : ν e = 0
    · have hne : Finsupp.single e 1 + μ ≠ ν := by
        intro h
        have := congrArg (fun f => f e) h
        simp only [Finsupp.add_apply, Finsupp.single_eq_same] at this
        omega
      rw [if_neg hne, hν]
      split_ifs <;> simp
    · obtain ⟨ρ, rfl⟩ : ∃ ρ, ν = ρ + Finsupp.single e 1 :=
        ⟨ν - Finsupp.single e 1, (tsub_add_cancel_of_le (by
          rw [Finsupp.single_le_iff]; omega)).symm⟩
      rw [add_tsub_cancel_right, Finsupp.add_apply, Finsupp.single_eq_same, add_comm _ μ]
      by_cases hμ : μ = ρ
      · subst hμ
        rw [if_pos rfl, if_pos rfl, fw_add_single]
        simp only [map_mul, map_natCast, map_one, smul_eq_mul]
        push_cast
        ring
      · rw [if_neg (fun h => hμ (add_right_cancel h)), if_neg hμ]
  have := LinearMap.congr_fun (LinearMap.congr_fun key p) q
  simpa using this

/-- The level-one oscillators are adjoint: `⟨a(n)p, q⟩ = ⟨p, a(-n)q⟩`. -/
theorem fockForm_oscN_neg (a : Fin r) {n : ℤ} (hn : n < 0) (p q : FockN r) :
    fockForm (oscN r 1 a n p) q = fockForm p (oscN r 1 a (-n) q) := by
  rw [oscN_apply_neg r 1 a hn, oscN_apply_pos r 1 a (by omega), fockForm_X_mul, one_smul]
  congr 2
  · have h : (((-n - 1).toNat + 1 : ℕ) : ℤ) = -n := by omega
    have h' := congrArg (fun z : ℤ => (z : ℂ)) h
    push_cast at h' ⊢
    exact h'

theorem fockForm_oscN (a : Fin r) (n : ℤ) (p q : FockN r) :
    fockForm (oscN r 1 a n p) q = fockForm p (oscN r 1 a (-n) q) := by
  rcases lt_trichotomy n 0 with hn | hn | hn
  · exact fockForm_oscN_neg a hn p q
  · subst hn; simp
  · have h := fockForm_oscN_neg a (by omega : -n < 0) q p
    rw [neg_neg] at h
    rw [fockForm_hermitian, ← h, ← fockForm_hermitian]

theorem oscN_commute_vec (a : Fin r) {s t : ℤ} (hst : s + t ≠ 0) (x : FockN r) :
    oscN r 1 a s (oscN r 1 a t x) = oscN r 1 a t (oscN r 1 a s x) := by
  have h := LinearMap.congr_fun (oscN_comm r 1 a a s t) x
  rw [if_neg (by rintro ⟨_, h⟩; exact hst h)] at h
  simp only [LinearMap.sub_apply, Module.End.mul_apply, zero_smul, LinearMap.zero_apply] at h
  exact sub_eq_zero.mp h

theorem fockForm_sugTermN (a : Fin r) (m j : ℤ) (x y : FockN r) :
    fockForm (sugTermN r 1 a m j x) y = fockForm x (sugTermN r 1 a (-m) (j - m) y) := by
  rw [sugTermN_apply, sugTermN_apply]
  by_cases hj : j < 0
  · rw [if_pos hj, fockForm_oscN, fockForm_oscN]
    by_cases hjm : j - m < 0
    · rw [if_pos hjm]; congr 2 <;> [congr 1; congr 2] <;> ring
    · rw [if_neg hjm, oscN_commute_vec a (by omega)]
      congr 2 <;> [congr 1; congr 2] <;> ring
  · rw [if_neg hj, fockForm_oscN, fockForm_oscN]
    by_cases hjm : j - m < 0
    · rw [if_pos hjm, oscN_commute_vec a (by omega)]
      congr 2 <;> [congr 1; congr 2] <;> ring
    · rw [if_neg hjm]; congr 2 <;> [congr 1; congr 2] <;> ring

theorem fockForm_LvirNa (a : Fin r) (m : ℤ) (x y : FockN r) :
    fockForm (LvirNa r 1 a m x) y = fockForm x (LvirNa r 1 a (-m) y) := by
  rw [LvirNa_apply', LvirNa_apply', map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ]
  have h1 : fockForm (∑ᶠ j : ℤ, sugTermN r 1 a m j x) y =
      ∑ᶠ j : ℤ, fockForm (sugTermN r 1 a m j x) y :=
    map_finsum ((fockForm (r := r)).flip y) (sugTermN_support_finite r 1 a m x)
  have h2 : fockForm x (∑ᶠ j : ℤ, sugTermN r 1 a (-m) j y) =
      ∑ᶠ j : ℤ, fockForm x (sugTermN r 1 a (-m) j y) :=
    map_finsum (fockForm x) (sugTermN_support_finite r 1 a (-m) y)
  rw [h1, h2]
  simp_rw [fockForm_sugTermN]
  have h3 : ∑ᶠ j : ℤ, fockForm x (sugTermN r 1 a (-m) (j - m) y) =
      ∑ᶠ j : ℤ, fockForm x (sugTermN r 1 a (-m) j y) :=
    finsum_comp_equiv (Equiv.subRight m) (f := fun j => fockForm x (sugTermN r 1 a (-m) j y))
  rw [h3]
  congr 1
  simp only [map_div₀, map_one, map_mul, map_ofNat]

theorem fockForm_LvirN (m : ℤ) (x y : FockN r) :
    fockForm (LvirN r 1 m x) y = fockForm x (LvirN r 1 (-m) y) := by
  rw [LvirN_apply, LvirN_apply, map_sum, LinearMap.sum_apply, map_sum]
  exact Finset.sum_congr rfl fun a _ => fockForm_LvirNa a m x y

end VOA.Classification.COne.OrbSpan
