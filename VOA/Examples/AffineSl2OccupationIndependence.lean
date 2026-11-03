/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.WakimotoShiftedVacuum

/-!
# Independence for arbitrary fixed orders of vacuum occupation words

The established minimum-Li symbol of every literal word is a commutative
product. Its independence therefore does not require the chosen word order
to be sorted. Injectively relabelling creation modes gives independent words,
by the already proved injectivity of the classical Wakimoto substitution.
-/
namespace VOA.Wak.Charged
open MvPolynomial
open AffineSl2WakimotoLiLeading AffineSl2PBWWakimotoReduction
noncomputable section

/-- Relabel each occupied oscillator by an arbitrary chosen vacuum creation
mode and retain the actual finite occupation word order. -/
def relabelledWord (f : Fin 3×ℕ→Fin 3×ℕ) (d : Occupation) : List (Fin 3×ℕ) :=
  d.toMultiset.toList.map f

/-- The corresponding exponent in the existing vacuum polynomial algebra. -/
def relabelledExponent (f : Fin 3×ℕ→Fin 3×ℕ) (d : Occupation) : (Fin 3×ₗℕ)→₀ℕ :=
  Finsupp.mapDomain (fun v => toLex (f v)) d

/-- Products of variables attached to the literal occupation list have the
expected exponent, independently of that list's order. -/
theorem relabelled_variable_product (f : Fin 3×ℕ→Fin 3×ℕ) (d : Occupation) :
    (d.toMultiset.toList.map (fun v => (X (toLex (f v)) : MvPolynomial (Fin 3×ₗℕ) ℂ))).prod=
      monomial (relabelledExponent f d) 1 := by
  have h (e : Occupation) :
      (e.toMultiset.map (fun v => (X (toLex (f v)) : MvPolynomial (Fin 3×ₗℕ) ℂ))).prod=
        monomial (relabelledExponent f e) 1 := by
    induction e using Finsupp.induction_linear with
    | zero => simp [relabelledExponent]
    | add e g he hg =>
        rw [Finsupp.toMultiset_add,Multiset.map_add,Multiset.prod_add,he,hg]
        simp [relabelledExponent,Finsupp.mapDomain_add,monomial_mul]
    | single v n =>
        simp [Finsupp.toMultiset_single,Multiset.map_nsmul,Multiset.prod_nsmul,
          relabelledExponent,Finsupp.mapDomain_single,X_pow_eq_monomial]
  simpa only [← Multiset.prod_coe,← Multiset.map_coe,Multiset.coe_toList] using h d

/-- Every literal classical word is the substitution of its abstract
commutative variable product, without a sorting assumption. -/
theorem classicalWord_substitution (k : ℂ) (w : List (Fin 3×ℕ)) :
    classicalWordState k w=classicalSubstitution k ((w.map (fun v => X (toLex v))).prod) := by
  induction w with
  | nil => simp [classicalWordState]
  | cons v w ih =>
      rw [classicalWordState,List.map_cons,List.prod_cons,map_mul,← ih]
      simp [classicalSubstitution]

/-- The exact leading symbol of a relabelled occupation is the image of
its exponent monomial in the injective classical substitution. -/
theorem classical_relabelled_monomial (k : ℂ) (f : Fin 3×ℕ→Fin 3×ℕ) (d : Occupation) :
    classicalWordState k (relabelledWord f d)=
      classicalSubstitution k (monomial (relabelledExponent f d) 1) := by
  rw [classicalWord_substitution,relabelledWord,List.map_map]
  simp only [Function.comp_def]
  rw [relabelled_variable_product]

/-- Injective current relabelling preserves distinct occupation exponents. -/
theorem relabelledExponent_injective (f : Fin 3×ℕ→Fin 3×ℕ) (hf : Function.Injective f) :
    Function.Injective (relabelledExponent f) := by
  apply Finsupp.mapDomain_injective
  intro a b h
  exact hf (congrArg ofLex h)

/-- Classical products of injectively relabelled occupation words are
linearly independent, by the existing classical Wakimoto injection. -/
theorem classical_relabelled_independent (k : ℂ) (f : Fin 3×ℕ→Fin 3×ℕ)
    (hf : Function.Injective f) :
    LinearIndependent ℂ (fun d : Occupation => classicalWordState k (relabelledWord f d)) := by
  have hmono := (MvPolynomial.basisMonomials (Fin 3×ₗℕ) ℂ).linearIndependent.comp
    (relabelledExponent f) (relabelledExponent_injective f hf)
  have himage := hmono.map' (classicalSubstitution k).toLinearMap
    (LinearMap.ker_eq_bot.mpr (classicalSubstitution_injective k))
  change LinearIndependent ℂ (fun d : Occupation =>
    classicalSubstitution k (monomial (relabelledExponent f d) 1)) at himage
  simpa only [← classical_relabelled_monomial] using himage

/-- ACTUAL Wakimoto words attached to any injective creation-mode
relabelling are independent, regardless of the finite order chosen for each
occupation. The existing minimum-Li estimates discharge all lower terms. -/
theorem wakimoto_relabelled_independent (k : ℂ) (f : Fin 3×ℕ→Fin 3×ℕ)
    (hf : Function.Injective f) :
    LinearIndependent ℂ (fun d : Occupation => wakimotoWordState k (relabelledWord f d)) := by
  apply linearIndependent_of_lowerLeading (fun d => wordFreeLiDegree (relabelledWord f d))
    (fun d => wakimotoWordState k (relabelledWord f d))
    (fun d => classicalWordState k (relabelledWord f d))
    (fun n => weightedHomogeneousComponent freeLiWeight n)
  · intro d
    exact weightedComponent_wakimotoWordState_min k _
  · intro d n hn
    exact weightedComponent_wakimotoWordState_eq_zero k _ n hn
  · exact classical_relabelled_independent k f hf

end
end VOA.Wak.Charged
