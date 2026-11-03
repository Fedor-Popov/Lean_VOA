/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl3Structure
import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# Actual free oscillators for the sl3 Wakimoto construction

Three beta-gamma pairs and two Cartan bosons act on an ordinary polynomial
ring. Beta and boson variables of index j have energy j+1; gamma variables
have energy j, including zero modes. Positive Cartan modes differentiate
using the A2 Cartan matrix times k+3, requiring no square roots.
These are free-field operators, not yet the eight affine sl3 currents.
-/
namespace VOA.AffineSl3.FreeField
noncomputable section
open MvPolynomial

/-- Eight oscillator species, separated so that mixed derivatives vanish. -/
inductive Colour
  | beta : Fin 3 → Colour
  | gamma : Fin 3 → Colour
  | boson : Fin 2 → Colour
  deriving DecidableEq

/-- Finite polynomials in the three beta, three gamma and two boson families. -/
abbrev Fock := MvPolynomial (Colour × ℕ) ℂ

/-- Creation of one oscillator variable. -/
def create (v : Colour × ℕ) : Module.End ℂ Fock := LinearMap.mulLeft ℂ (X v)

/-- Annihilation by ordinary formal partial differentiation. -/
def deriv (v : Colour × ℕ) : Module.End ℂ Fock := (pderiv v).toLinearMap

/-- Creation acts by multiplication by the indicated polynomial variable. -/
theorem create_apply (v : Colour × ℕ) (P : Fock) : create v P = X v * P := rfl

/-- Annihilation acts by the indicated formal partial derivative. -/
theorem deriv_apply (v : Colour × ℕ) (P : Fock) : deriv v P = pderiv v P := rfl

/-- Scalar multiplication in the first slot of an actual endomorphism commutator. -/
theorem comm_smul_left (a : ℂ) (S T : Module.End ℂ Fock) :
    ⁅a • S, T⁆ = a • ⁅S,T⁆ := by
  simp [Ring.lie_def, smul_mul_assoc, mul_smul_comm, smul_sub]

/-- Scalar multiplication in the second slot of the same commutator. -/
theorem comm_smul_right (a : ℂ) (S T : Module.End ℂ Fock) :
    ⁅S, a • T⁆ = a • ⁅S,T⁆ := by
  simp [Ring.lie_def, smul_mul_assoc, mul_smul_comm, smul_sub]

/-- Independent polynomial creation operators commute. -/
theorem create_create (v w : Colour × ℕ) : ⁅create v, create w⁆ = 0 := by
  refine LinearMap.ext fun P => ?_
  simp [Ring.lie_def, Module.End.mul_apply, create_apply]
  ring

/-- Mixed formal partial derivatives commute, by induction on polynomials. -/
theorem partial_comm (v w : Colour × ℕ) (P : Fock) :
    pderiv v (pderiv w P) = pderiv w (pderiv v P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p s h =>
    rw [pderiv_mul, pderiv_mul, map_add, map_add, pderiv_mul, pderiv_mul]
    simp only [pderiv_X, Pi.single_apply, h]
    by_cases hsv : s = v <;> by_cases hsw : s = w <;> simp_all <;> ring

/-- Every pair of annihilation operators commutes. -/
theorem deriv_deriv (v w : Colour × ℕ) : ⁅deriv v, deriv w⁆ = 0 := by
  refine LinearMap.ext fun P => ?_
  simp [Ring.lie_def, Module.End.mul_apply, deriv_apply, partial_comm]

/-- The canonical derivative-creation commutator is the Kronecker delta. -/
theorem deriv_create (v w : Colour × ℕ) :
    ⁅deriv v, create w⁆ = if v=w then (1 : Module.End ℂ Fock) else 0 := by
  refine LinearMap.ext fun P => ?_
  simp only [Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply,
    deriv_apply, create_apply, pderiv_mul, pderiv_X, Pi.single_apply]
  by_cases hv : v=w
  · subst w; simp
  · simp [hv, Ne.symm hv]

/-- The opposite ordering has the negative canonical commutator. -/
theorem create_deriv (v w : Colour × ℕ) :
    ⁅create v, deriv w⁆ = if v=w then -(1 : Module.End ℂ Fock) else 0 := by
  rw [← lie_skew, deriv_create]
  by_cases hv : v=w <;> simp [hv, Ne.symm]

/-- Beta has creation modes at negative indices and gamma derivatives otherwise. -/
def beta (i : Fin 3) (m : ℤ) : Module.End ℂ Fock :=
  if m<0 then create (.beta i, (-m-1).toNat) else deriv (.gamma i, m.toNat)

/-- Gamma has creation modes at nonpositive indices; its positive modes are
minus beta derivatives. The zero creation mode is deliberately included. -/
def gamma (i : Fin 3) (m : ℤ) : Module.End ℂ Fock :=
  if m≤0 then create (.gamma i, (-m).toNat) else -deriv (.beta i, (m-1).toNat)

/-- The matrix of the trace form on the two simple coroots. -/
def cartan (i j : Fin 2) : ℂ := if i=j then 2 else -1

/-- Symmetry of the A2 Cartan matrix. -/
theorem cartan_symm (i j : Fin 2) : cartan i j = cartan j i := by
  simp [cartan, eq_comm]

/-- Cartan annihilation in row i, combining both boson partials. -/
def cartanDeriv (i : Fin 2) (m : ℕ) : Module.End ℂ Fock :=
  ∑ j, cartan i j • deriv (.boson j, m)

/-- Boson modes at shifted level k+3. At zero the scalar m kills the
annihilation operator; no nonzero zero-mode charge is inserted here. -/
def boson (k : ℂ) (i : Fin 2) (m : ℤ) : Module.End ℂ Fock :=
  if m<0 then create (.boson i, (-m-1).toNat)
  else ((k+3)*(m : ℂ)) • cartanDeriv i (m-1).toNat

/-- The polynomial vacuum is nonzero independently of any affine quotient. -/
theorem vacuum_ne_zero : (1 : Fock) ≠ 0 := one_ne_zero

/-- The canonical beta-gamma relation, including zero modes and different pairs. -/
theorem beta_gamma (i j : Fin 3) (m n : ℤ) :
    ⁅beta i m, gamma j n⁆ =
      if i=j ∧ m+n=0 then (1 : Module.End ℂ Fock) else 0 := by
  by_cases hm : m<0 <;> by_cases hn : n≤0
  · simp [beta, gamma, hm, hn, create_create, show m+n≠0 by omega]
  · simp only [beta, gamma, if_pos hm, if_neg hn, lie_neg, create_deriv]
    have he : ((Colour.beta i, (-m-1).toNat) = (Colour.beta j, (n-1).toNat)) ↔
        i=j ∧ m+n=0 := by simp only [Prod.mk.injEq, Colour.beta.injEq]; omega
    by_cases h : i=j ∧ m+n=0
    · simp only [if_pos (he.mpr h), if_pos h, neg_neg]
    · simp only [if_neg (fun hh => h (he.mp hh)), if_neg h, neg_zero]
  · simp only [beta, gamma, if_neg hm, if_pos hn, deriv_create]
    have he : ((Colour.gamma i, m.toNat) = (Colour.gamma j, (-n).toNat)) ↔
        i=j ∧ m+n=0 := by simp only [Prod.mk.injEq, Colour.gamma.injEq]; omega
    simp only [he]
  · simp [beta, gamma, hm, hn, lie_neg, deriv_deriv, show m+n≠0 by omega]

/-- All beta modes commute, within a pair and across different pairs. -/
theorem beta_beta (i j : Fin 3) (m n : ℤ) : ⁅beta i m, beta j n⁆ = 0 := by
  by_cases hm : m<0 <;> by_cases hn : n<0 <;>
    simp [beta, hm, hn, create_create, create_deriv, deriv_create, deriv_deriv]

/-- All gamma modes commute, including their zero modes. -/
theorem gamma_gamma (i j : Fin 3) (m n : ℤ) : ⁅gamma i m, gamma j n⁆ = 0 := by
  by_cases hm : m≤0 <;> by_cases hn : n≤0 <;>
    simp [gamma, hm, hn, lie_neg, neg_lie, create_create, create_deriv,
      deriv_create, deriv_deriv]

/-- A Cartan annihilation row pairs with a boson variable by its Cartan entry. -/
theorem cartanDeriv_create (i j : Fin 2) (m n : ℕ) :
    ⁅cartanDeriv i m, create (.boson j,n)⁆ =
      if m=n then cartan i j • (1 : Module.End ℂ Fock) else 0 := by
  fin_cases j <;> by_cases h : m=n <;>
    simp [h, cartanDeriv, Fin.sum_univ_two, add_lie, comm_smul_left, deriv_create, Prod.mk.injEq,
    Colour.boson.injEq, smul_ite, Finset.sum_ite_irrel]

/-- The Cartan annihilation rows commute because ordinary partials commute. -/
theorem cartanDeriv_cartanDeriv (i j : Fin 2) (m n : ℕ) :
    ⁅cartanDeriv i m, cartanDeriv j n⁆ = 0 := by
  simp [cartanDeriv, Fin.sum_univ_two, add_lie, lie_add, comm_smul_left, comm_smul_right, deriv_deriv]

/-- The full rank-two Heisenberg relation carries the normalized Cartan matrix
and shifted level k+3; it holds at every complex k, including critical level. -/
theorem boson_boson (k : ℂ) (i j : Fin 2) (m n : ℤ) :
    ⁅boson k i m, boson k j n⁆ =
      if m+n=0 then ((k+3)*(m : ℂ)*cartan i j) • (1 : Module.End ℂ Fock) else 0 := by
  by_cases hm : m<0 <;> by_cases hn : n<0
  · simp [boson, hm, hn, create_create, show m+n≠0 by omega]
  · by_cases hn0 : n=0
    · subst n
      simp [boson, hm, show m≠0 by omega]
    simp only [boson, if_pos hm, if_neg hn, comm_smul_right]
    rw [← lie_skew, cartanDeriv_create]
    have he : (n-1).toNat=(-m-1).toNat ↔ m+n=0 := by omega
    by_cases h : m+n=0
    · have he' : (n : ℂ) = -(m : ℂ) := by exact_mod_cast (show n = -m by omega)
      simp only [he, h, if_true, he', cartan_symm j i, mul_neg, neg_mul, neg_smul, smul_neg, neg_neg, smul_smul]
    · simp only [he, h, if_false, neg_zero, smul_zero]
  · by_cases hm0 : m=0
    · subst m
      simp [boson, hn, show n≠0 by omega]
    simp only [boson, if_neg hm, if_pos hn, comm_smul_left, cartanDeriv_create]
    have he : (m-1).toNat=(-n-1).toNat ↔ m+n=0 := by omega
    by_cases h : m+n=0 <;> simp only [he, h, if_true, if_false, smul_smul, smul_zero]
  · simp only [boson, if_neg hm, if_neg hn, comm_smul_left, comm_smul_right,
      cartanDeriv_cartanDeriv, smul_zero]
    by_cases h : m+n=0
    · have hz : m=0 := by omega
      simp [h,hz]
    · simp [h]

/-- A Cartan derivative commutes with every partial derivative, of any species. -/
theorem cartanDeriv_deriv (i : Fin 2) (m : ℕ) (v : Colour × ℕ) :
    ⁅cartanDeriv i m, deriv v⁆ = 0 := by
  simp [cartanDeriv, Fin.sum_univ_two, add_lie, comm_smul_left, deriv_deriv]

/-- Cartan derivatives do not differentiate beta variables. -/
theorem cartanDeriv_beta_create (i : Fin 2) (j : Fin 3) (m n : ℕ) :
    ⁅cartanDeriv i m, create (.beta j,n)⁆ = 0 := by
  simp [cartanDeriv, Fin.sum_univ_two, add_lie, comm_smul_left, deriv_create]

/-- Cartan derivatives do not differentiate gamma variables, including zero modes. -/
theorem cartanDeriv_gamma_create (i : Fin 2) (j : Fin 3) (m n : ℕ) :
    ⁅cartanDeriv i m, create (.gamma j,n)⁆ = 0 := by
  simp [cartanDeriv, Fin.sum_univ_two, add_lie, comm_smul_left, deriv_create]

/-- Every Cartan boson mode commutes with every beta mode. -/
theorem boson_beta (k : ℂ) (i : Fin 2) (j : Fin 3) (m n : ℤ) :
    ⁅boson k i m, beta j n⁆ = 0 := by
  by_cases hm : m<0 <;> by_cases hn : n<0 <;>
    simp [boson, beta, hm, hn, comm_smul_left, create_create, create_deriv,
      cartanDeriv_beta_create, cartanDeriv_deriv]

/-- Every Cartan boson mode commutes with every gamma mode. -/
theorem boson_gamma (k : ℂ) (i : Fin 2) (j : Fin 3) (m n : ℤ) :
    ⁅boson k i m, gamma j n⁆ = 0 := by
  by_cases hm : m<0 <;> by_cases hn : n≤0 <;>
    simp [boson, gamma, hm, hn, lie_neg, comm_smul_left, create_create, create_deriv,
      cartanDeriv_gamma_create, cartanDeriv_deriv]

/-- Nonnegative beta modes annihilate the polynomial vacuum. -/
theorem beta_vacuum (i : Fin 3) (m : ℤ) (hm : 0≤m) : beta i m 1 = 0 := by
  simp [beta, show ¬m<0 by omega, deriv_apply]

/-- Strictly positive gamma modes annihilate the vacuum; gamma zero is creation. -/
theorem gamma_vacuum (i : Fin 3) (m : ℤ) (hm : 0<m) : gamma i m 1 = 0 := by
  simp [gamma, show ¬m≤0 by omega, deriv_apply]

/-- All nonnegative Cartan boson modes annihilate the uncharged vacuum. -/
theorem boson_vacuum (k : ℂ) (i : Fin 2) (m : ℤ) (hm : 0≤m) :
    boson k i m 1 = 0 := by
  simp [boson, show ¬m<0 by omega, cartanDeriv, LinearMap.sum_apply, deriv_apply]

/-- A uniform cutoff computed from the finite set of variables of a polynomial. -/
def cutoff (P : Fock) : ℤ := ((P.vars.sup (fun v => v.2) : ℕ) : ℤ) + 2

/-- The cutoff is at least two, so modes beyond it are genuine annihilation modes. -/
theorem two_le_cutoff (P : Fock) : 2≤cutoff P := by
  have h := Int.natCast_nonneg (P.vars.sup fun v => v.2)
  simp only [cutoff]
  omega

/-- A variable above the cutoff does not occur in the polynomial. -/
theorem derivative_above {P : Fock} (c : Colour) (n : ℕ)
    (hn : cutoff P ≤ (n : ℤ)+1) : deriv (c,n) P = 0 := by
  apply pderiv_eq_zero_of_notMem_vars
  intro hv
  have hl : n ≤ P.vars.sup (fun v => v.2) := Finset.le_sup (f := fun v => v.2) hv
  simp only [cutoff] at hn
  omega

/-- All sufficiently high beta modes vanish on each polynomial. -/
theorem beta_above (i : Fin 3) {P : Fock} {m : ℤ} (hm : cutoff P≤m) :
    beta i m P = 0 := by
  have h2 := two_le_cutoff P
  rw [beta, if_neg (by omega)]
  exact derivative_above _ _ (by omega)

/-- The same cutoff controls the gamma annihilation modes. -/
theorem gamma_above (i : Fin 3) {P : Fock} {m : ℤ} (hm : cutoff P≤m) :
    gamma i m P = 0 := by
  have h2 := two_le_cutoff P
  rw [gamma, if_neg (by omega), LinearMap.neg_apply]
  rw [derivative_above _ _ (by omega), neg_zero]

/-- The same cutoff controls both Cartan bosons at every level k. -/
theorem boson_above (k : ℂ) (i : Fin 2) {P : Fock} {m : ℤ} (hm : cutoff P≤m) :
    boson k i m P = 0 := by
  have h2 := two_le_cutoff P
  rw [boson, if_neg (by omega)]
  simp only [LinearMap.smul_apply, cartanDeriv, LinearMap.sum_apply]
  have hd : ∀ j : Fin 2, deriv (.boson j,(m-1).toNat) P = 0 :=
    fun j => derivative_above _ _ (by omega)
  simp only [LinearMap.smul_apply, hd, smul_zero, Finset.sum_const_zero]

end
end VOA.AffineSl3.FreeField
