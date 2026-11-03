/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroVermaPositiveSymbols

/-!
# Invariants of the positive leading derivations

A polynomial killed by every positive leading Virasoro derivation can use
only the translation variable. Indeed, at its largest occurring index a>0,
the a-th derivation is (2a+1) X_0 times partial differentiation in X_a.
Characteristic zero and the polynomial domain rule out such a variable.
-/
namespace VOA.InverseDS.VirasoroVerma
open scoped Classical

/-- Multiplying a partial derivative by its variable counts that variable's
exponent in each coefficient. This finite identity avoids analytic arguments. -/
theorem vermaSymbol_euler_coeff {σ : Type*} (f : MvPolynomial σ ℂ)
    (i : σ) (d : σ →₀ ℕ) :
    MvPolynomial.coeff d (MvPolynomial.X i * MvPolynomial.pderiv i f)=
      (d i:ℂ)*MvPolynomial.coeff d f := by
  induction f using MvPolynomial.induction_on' with
  | add f g hf hg => simp only [map_add,mul_add,MvPolynomial.coeff_add,hf,hg]
  | monomial e a =>
    rw [MvPolynomial.X_mul_pderiv_monomial,MvPolynomial.coeff_smul]
    by_cases he : e=d
    · subst e; simp [MvPolynomial.coeff_monomial,nsmul_eq_mul]
    · simp [MvPolynomial.coeff_monomial,he,Ne.symm he]

/-- Over the complex numbers, zero partial derivative means the variable
does not occur. The proof reads a nonzero monomial coefficient and uses its
positive integer exponent, so it cannot hold unchanged in positive characteristic. -/
theorem vermaSymbol_notMem_vars_of_pderiv_zero {σ : Type*}
    (f : MvPolynomial σ ℂ) (i : σ) (hi : MvPolynomial.pderiv i f=0) : i∉f.vars := by
  intro hm
  obtain ⟨d,hd,hdi⟩ := (MvPolynomial.mem_vars_iff_mem_support i).mp hm
  have he := vermaSymbol_euler_coeff f i d
  rw [hi,mul_zero,MvPolynomial.coeff_zero] at he
  have hz : (d i:ℂ)=0 := (mul_eq_zero.mp he.symm).resolve_right
    (MvPolynomial.mem_support_iff.mp hd)
  exact (Finsupp.mem_support_iff.mp hdi) (by exact_mod_cast hz)

/-- At the largest occurring index, the corresponding positive derivation
is a nonzero multiple of a single partial derivative. No other variable in
the polynomial can contribute to that positive mode. -/
theorem vermaLeadingDerivation_at_max (f : MvPolynomial (ℕ × Fin 1) ℂ) (a : ℕ)
    (hmax : ∀ i∈f.vars, i.1≤a) :
    vermaLeadingDerivation a f=
      (((2*a+1:ℕ):ℂ) • MvPolynomial.X (0,0))*MvPolynomial.pderiv (a,0) f := by
  have he := MvPolynomial.derivation_eq_of_forall_mem_vars
    (D₁ := vermaLeadingDerivation a)
    (D₂ := (((2*a+1:ℕ):ℂ) • (MvPolynomial.X (0,0) : MvPolynomial (ℕ × Fin 1) ℂ)) • MvPolynomial.pderiv (a,0))
    (f := f) (fun i hi => ?_)
  · simpa only [Derivation.smul_apply,smul_eq_mul] using he
  · by_cases he : i=(a,0)
    · subst i
      simp [vermaLeadingDerivation,MvPolynomial.mkDerivation_X,two_mul]
    · have hn : ¬ a ≤ i.1 := by
        intro hh
        apply he
        exact Prod.ext (Nat.le_antisymm (hmax i hi) hh) (Subsingleton.elim _ _)
      simp [vermaLeadingDerivation,MvPolynomial.mkDerivation_X,hn,
        MvPolynomial.pderiv_X_of_ne he]

/-- Every polynomial annihilated by all positive leading Virasoro modes
uses only the translation variable X_0. A largest positive index would
have nonzero partial derivative, contradicting the corresponding equation. -/
theorem vermaLeadingInvariants_vars (f : MvPolynomial (ℕ × Fin 1) ℂ)
    (hf : ∀ m : ℕ, 0 < m → vermaLeadingDerivation m f=0) :
    ∀ i∈f.vars, i.1=0 := by
  intro i hi
  obtain ⟨⟨a,b⟩,ha,hmax⟩ := f.vars.exists_max_image Prod.fst ⟨i,hi⟩
  have hb : b=0 := Subsingleton.elim _ _
  subst b
  have haz : a=0 := by
    by_contra hn
    have hpos : 0<a := Nat.pos_of_ne_zero hn
    have he := vermaLeadingDerivation_at_max f a hmax
    rw [hf a hpos] at he
    have hg : (((2*a+1:ℕ):ℂ) • (MvPolynomial.X (0,0) : MvPolynomial (ℕ × Fin 1) ℂ))≠0 :=
      smul_ne_zero (by exact_mod_cast (show 2*a+1≠0 by omega)) (MvPolynomial.X_ne_zero _)
    have hd := (mul_eq_zero.mp he.symm).resolve_left hg
    exact vermaSymbol_notMem_vars_of_pderiv_zero f (a,0) hd ha
  have h := hmax i hi
  simp only [haz] at h
  omega

end VOA.InverseDS.VirasoroVerma
