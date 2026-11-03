/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroVermaBSANonvanishing
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-!
# Symbols of descendants of arbitrary Verma states

The fixed-weight free-momentum family represents every state by a vector
polynomial. Its highest nonzero symbol detects a nonzero state. Each negative
mode multiplies that symbol by one oscillator variable, including L-minus-one.
This supplies the domain argument for independent full Verma descendants.
-/
namespace VOA.InverseDS.VirasoroVerma
open VirModule LeeYangFockExponential LeeYangFockVirasoro LeeYangWardClosure

/-- The polynomial action of a single creation mode: its constant part is
the zero-momentum mode, and its linear part creates an oscillator. -/
noncomputable def vermaPolynomialCreation (ell p : ℂ) (i : ℕ)
    (q : PolynomialModule ℂ VermaFockFamily) : PolynomialModule ℂ VermaFockFamily :=
  PolynomialModule.map ℂ ((vermaFockFamilyData ell p 0).L (-(i:ℤ)-1)) q +
    (Polynomial.X : Polynomial ℂ) • PolynomialModule.map ℂ (vermaMomentumMode i) q

/-- A negative mode raises the free-momentum degree by at most one. -/
theorem vermaPolynomialCreation_above (ell p : ℂ) (i d : ℕ)
    (q : PolynomialModule ℂ VermaFockFamily) (hq : ∀ k, d<k → q k=0)
    (k : ℕ) (hk : d+1<k) : vermaPolynomialCreation ell p i q k=0 := by
  rw [vermaPolynomialCreation,PolynomialModule.add_apply,polynomialModule_map_coeff,
    polynomialModule_X_coeff,if_pos (by omega),polynomialModule_map_coeff,
    hq k (by omega),hq (k-1) (by omega)]
  simp

/-- At maximal degree the negative mode multiplies the projected symbol by
its oscillator variable; the fixed part contributes only lower degrees. -/
theorem vermaPolynomialCreation_top (ell p : ℂ) (i d : ℕ)
    (q : PolynomialModule ℂ VermaFockFamily) (hq : ∀ k, d<k → q k=0) :
    vermaSymbolProjection (vermaPolynomialCreation ell p i q (d+1))=
      MvPolynomial.X (i,(0:Fin 1))*vermaSymbolProjection (q d) := by
  rw [vermaPolynomialCreation,PolynomialModule.add_apply,polynomialModule_map_coeff,
    hq (d+1) (by omega),map_zero,zero_add,polynomialModule_X_coeff,
    if_pos (by omega),Nat.add_sub_cancel,polynomialModule_map_coeff,
    vermaSymbolProjection_momentum]

/-- Extract one vector coefficient as a complex-linear map, allowing finite
state relations to pass to their momentum coefficients. -/
noncomputable def vermaPolynomialCoefficient (k : ℕ) :
    PolynomialModule ℂ VermaFockFamily →ₗ[ℂ] VermaFockFamily where
  toFun q := q k
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Every nonzero state has a highest free-momentum coefficient whose
projected oscillator symbol is nonzero. Distinct longest PBW words supply
distinct monomials, so their coefficients cannot cancel. -/
theorem vermaPolynomialLift_top_exists (ell p : ℂ)
    (v : Verma (3-24*ell^2) (p^2-2*ell*p)) (hv : v≠0) :
    ∃ d, (∀ k, d<k → vermaPolynomialLift ell p v k=0) ∧
      vermaSymbolProjection (vermaPolynomialLift ell p v d)≠0 := by
  classical
  let b := vermaSortedBasis (3-24*ell^2) (p^2-2*ell*p)
  let a := b.repr v
  have ha : a≠0 := fun he => hv (b.repr.injective (he.trans (map_zero _).symm))
  obtain ⟨w,hw,hm⟩ := a.support.exists_max_image (fun w => w.val.length)
    (Finsupp.support_nonempty_iff.mpr ha)
  have hs : vermaPolynomialLift ell p v =
      ∑ u ∈ a.support, a u • vermaWordPolynomial ell p u.val := by
    have he := congrArg (vermaPolynomialLift ell p) (b.linearCombination_repr v)
    simpa only [Finsupp.linearCombination_apply,Finsupp.sum,map_sum,map_smul,b,vermaSortedBasis_apply,vermaPolynomialLift_sorted] using he.symm
  have hscoeff (k : ℕ) : vermaPolynomialLift ell p v k =
      ∑ u ∈ a.support, a u • vermaWordPolynomial ell p u.val k := by
    have he := congrArg (vermaPolynomialCoefficient k) hs
    simpa only [map_sum,map_smul,vermaPolynomialCoefficient,LinearMap.coe_mk,
      AddHom.coe_mk] using he
  refine ⟨w.val.length,?_,?_⟩
  · intro k hk
    rw [hscoeff]
    apply Finset.sum_eq_zero
    intro u hu
    rw [vermaWordPolynomial_coeff_above ell p u.val k (lt_of_le_of_lt (hm u hu) hk),smul_zero]
  · intro hz
    have he := congrArg (MvPolynomial.coeff (vermaWordExponent w.val)) hz
    rw [hscoeff] at he
    simp only [
      map_sum,map_smul,MvPolynomial.coeff_sum,MvPolynomial.coeff_smul,
      smul_eq_mul,MvPolynomial.coeff_zero] at he
    have hc : (∑ u ∈ a.support, a u *
        MvPolynomial.coeff (vermaWordExponent w.val)
          (vermaSymbolProjection (vermaWordPolynomial ell p u.val w.val.length)))=a w := by
      rw [Finset.sum_eq_single w]
      · rw [vermaWordPolynomial_top_selector ell p _ w.val w.val w.property w.property
          (le_refl _) rfl]; simp
      · intro u hu huw
        rw [vermaWordPolynomial_top_selector ell p _ u.val w.val u.property w.property
          (hm u hu) rfl,if_neg (fun h => huw (Subtype.ext h)),mul_zero]
      · exact fun h => (h hw).elim
    rw [hc] at he
    exact (Finsupp.mem_support_iff.mp hw) he

end VOA.InverseDS.VirasoroVerma
