/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2HighestGramRoot
import Mathlib.Algebra.Polynomial.Roots

/-!
# Uniform ordinary affine highest-word roots on the screening Kac lines

The finite integer screenings give infinitely many distinct roots along
k=t-2, lambda=qt-r-1. The actual word determinant is polynomial in both
parameters, so its restriction to each such line vanishes identically.
This proves genuine ordinary roots, but neither multiplicities nor a vacuum
simple-root transfer is asserted here.
-/
namespace VOA.Wak.Charged
open scoped BigOperators
noncomputable section

/-- Restrict the actual two-parameter determinant to a screening Kac line.
The restriction is an ordinary polynomial; no inverse parameter occurs. -/
def highestKacPolynomial (r q : ℕ) : Polynomial ℂ :=
  MvPolynomial.eval₂Hom Polynomial.C
    ![Polynomial.X-Polynomial.C 2,
      Polynomial.C (q : ℂ)*Polynomial.X-Polynomial.C (r : ℂ)-Polynomial.C 1]
    (highestDeterminant (r*q) (r : ℤ))

/-- Restriction and scalar evaluation agree with the actual highest-word
determinant at the indicated level and Cartan highest weight. -/
theorem highestKacPolynomial_eval (r q : ℕ) (t : ℂ) :
    (highestKacPolynomial r q).eval t=
      MvPolynomial.eval ![t-2,(q : ℂ)*t-(r : ℂ)-1]
        (highestDeterminant (r*q) (r : ℤ)) := by
  change Polynomial.evalRingHom t (highestKacPolynomial r q)=_
  rw [highestKacPolynomial,MvPolynomial.map_eval₂Hom]
  have hc : (Polynomial.evalRingHom t).comp Polynomial.C=RingHom.id ℂ := by
    ext z; simp
  rw [hc]
  have hv : (fun i : Fin 2 => Polynomial.evalRingHom t
      (![Polynomial.X-Polynomial.C 2,
        Polynomial.C (q : ℂ)*Polynomial.X-Polynomial.C (r : ℂ)-Polynomial.C 1] i))=
      ![t-2,(q : ℂ)*t-(r : ℂ)-1] := by
    funext i
    fin_cases i <;> simp
  rw [hv]
  rfl

/-- Positive inverse integers are pairwise distinct complex parameters. -/
theorem inverse_successor_injective : Function.Injective (fun m : ℕ => ((m+1 : ℕ) : ℂ)⁻¹) := by
  intro m n h
  have he := inv_injective h
  exact Nat.add_right_cancel (Nat.cast_injective he)

/-- Actual nonzero screenings make the restricted ordinary determinant
zero at every positive inverse integer, with all Ward inputs discharged. -/
theorem highestKacPolynomial_inverse_root (r q : ℕ) (hr : 0<r) (hq : 0<q) (m : ℕ) :
    (highestKacPolynomial r q).eval (((m+1 : ℕ) : ℂ)⁻¹)=0 := by
  rw [highestKacPolynomial_eval]
  have hm : ((m+1 : ℕ) : ℂ)≠0 := by exact_mod_cast (Nat.succ_ne_zero m)
  have hk : (((m+1 : ℕ) : ℂ))*((((m+1 : ℕ) : ℂ)⁻¹-2)+2)=1 := by
    rw [sub_add_cancel,mul_inv_cancel₀ hm]
  have hz := highestDeterminant_screening_root r q (m+1) hr hq
    ((((m+1 : ℕ) : ℂ)⁻¹)-2) hk
  simpa only [sub_add_cancel] using hz

/-- The actual determinant vanishes identically on every positive-label
screening Kac line, by infinitely many proved ordinary roots. -/
theorem highestKacPolynomial_eq_zero (r q : ℕ) (hr : 0<r) (hq : 0<q) :
    highestKacPolynomial r q=0 := by
  apply Polynomial.eq_zero_of_infinite_isRoot
  apply (Set.infinite_range_of_injective inverse_successor_injective).mono
  intro t ht
  obtain ⟨m,rfl⟩ := ht
  exact highestKacPolynomial_inverse_root r q hr hq m

/-- Uniform ordinary highest-word Gram determinant roots at ALL complex
parameters on the screening Kac line. This includes nonreal parameters;
no continuity or specialization of a chosen singular vector is needed. -/
theorem highestDeterminant_kac_root (r q : ℕ) (hr : 0<r) (hq : 0<q) (t : ℂ) :
    MvPolynomial.eval ![t-2,(q : ℂ)*t-(r : ℂ)-1]
      (highestDeterminant (r*q) (r : ℤ))=0 := by
  rw [← highestKacPolynomial_eval,highestKacPolynomial_eq_zero r q hr hq,Polynomial.eval_zero]

end
end VOA.Wak.Charged
