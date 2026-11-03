/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2AdmissibleVacuumRoot

/-!
# Nondegeneracy below the first admissible vacuum root

Coprime root arithmetic and the proved actual vacuum determinant identity
exclude every null state below the first possible admissible energy.
-/
namespace VOA.Wak.Charged
open Polynomial AffineVOA.HighestModule AffineSl2AdmissibleArithmetic
noncomputable section
open scoped Classical

/-- Root-label isolation is uniform in the target charge and every energy
at or below the first admissible energy. -/
theorem admissible_zero_labels_le (p q : ℕ) (hp : 2≤p) (hq : 0<q)
    (hcop : p.Coprime q) (n : ℕ) (c : ℤ) (hn : n ≤ q*(p-1))
    (i : (Fin 3×ℕ)×ℕ)
    (hi : i∈affineKacLabels n c)
    (hz : realRootWeight ((p : ℂ)/q) i=0) :
    i=((1,0),0) ∨ i=((0,q-1),p-2) := by
  obtain ⟨hc,he⟩ := affineKacLabels_bounds _ _ i hi
  rcases i with ⟨⟨a,m⟩,r⟩
  fin_cases a
  · have hz' : ((m+1 : ℕ) : ℂ)*((p : ℂ)/q)-((r+1 : ℕ) : ℂ)-1=0 := by
      norm_num [realRootWeight,realRootSlope,realRootOffset,Fin.ext_iff] at hz
      push_cast
      linear_combination hz
    have eqn := positive_weight_zero_equation p q (m+1) (r+1) hq hz'
    have hb : (m+1)*(r+1)≤q*(p-1) := by
      exact le_trans (by simpa [oscillatorEnergy,Nat.mul_comm] using he) hn
    obtain ⟨hm,hr⟩ := first_minus_resonance_unique hp hq (by omega) hcop eqn hb
    right
    have hm' : m=q-1 := by omega
    have hr' : r=p-2 := by omega
    simp [hm',hr']
  · by_cases hm : m=0
    · subst m
      have hr : r=0 := by
        have hz' : (r : ℂ)=0 := by simpa [realRootWeight,realRootSlope,realRootOffset] using hz
        exact_mod_cast hz'
      left; simp [hr]
    · have hz' : ((r+1 : ℕ) : ℂ)-1-(m : ℂ)*((p : ℂ)/q)=0 := by
        simpa [realRootWeight,realRootSlope,realRootOffset,Nat.cast_add,sub_eq_add_neg,
          neg_mul,add_comm,add_left_comm,add_assoc] using hz
      have eqn := negative_weight_zero_equation p q m (r+1) hq hz'
      have hs := plus_resonance_energy_gt hp hq (by omega) hcop eqn
      have hb : m*(r+1)≤q*(p-1) := by
        exact le_trans (by simpa [oscillatorEnergy,Nat.mul_comm] using he) hn
      omega
  · exact False.elim (hc rfl)

/-- Strictly below the first admissible energy only the removed horizontal
root can vanish. -/
theorem affineVacuumProduct_admissible_below (p q : ℕ) (hp : 2 ≤ p)
    (hq : 0 < q) (hcop : p.Coprime q) (n : ℕ) (c : ℤ)
    (hn : n < q * (p - 1)) :
    (affineVacuumProduct n c).eval ((p : ℂ) / q - 2) ≠ 0 := by
  simp only [affineVacuumProduct, eval_prod, eval_pow, eval_neg, eval_add,
    eval_mul, eval_C, eval_X, sub_add_cancel]
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  apply pow_ne_zero
  apply neg_ne_zero.mpr
  change realRootWeight ((p : ℂ) / q) i ≠ 0
  intro hz
  obtain hi' | hi' := admissible_zero_labels_le p q hp hq hcop n c
    (Nat.le_of_lt hn) i (Finset.mem_erase.mp hi).2 hz
  · exact (Finset.mem_erase.mp hi).1 hi'
  · obtain ⟨_, he⟩ := affineKacLabels_bounds n c i (Finset.mem_erase.mp hi).2
    rw [hi'] at he
    have hp' : p - 2 + 1 = p - 1 := by omega
    have hq' : q - 1 + 1 = q := by omega
    simp only [oscillatorEnergy, Fin.isValue, Fin.reduceEq, if_false, hp', hq'] at he
    rw [Nat.mul_comm] at he
    omega

/-- The actual Chevalley vacuum matrix is nonsingular below the first
admissible energy. Its determinant is obtained from the proved Kac identity,
without assuming any graded character. -/
theorem vacuumChevalleyDeterminant_admissible_below (p q : ℕ) (hp : 2 ≤ p)
    (hq : 0 < q) (hcop : p.Coprime q) (n : ℕ) (c : ℤ)
    (hn : n < q * (p - 1)) (hc : 0 < 2 * (n : ℤ) - c) :
    (vacuumChevalleyPolynomial n c).det.eval ((p : ℂ) / q - 2) ≠ 0 := by
  have hid := congrArg (Polynomial.eval ((p : ℂ) / q - 2))
    (affine_vacuum_polynomial_identity n c hc)
  simp only [eval_mul, eval_C] at hid
  have hk : (p : ℂ) / q - 2 + 2 ≠ 0 := by
    rw [sub_add_cancel]
    exact div_ne_zero (by exact_mod_cast (show p ≠ 0 by omega))
      (by exact_mod_cast (Nat.ne_of_gt hq))
  have hr := mul_ne_zero
    (mul_ne_zero (vacuumDeterminantScale_ne_zero n c)
      (affineLeadingPolynomial_eval_ne_zero _ hk n c))
    (affineVacuumProduct_admissible_below p q hp hq hcop n c hn)
  intro hz
  rw [hz, zero_mul] at hid
  exact hr hid.symm

/-- At the first energy, a charge above the primitive charge removes even
the single resonant factor: its zero-energy descendant space is empty. -/
theorem affineVacuumProduct_admissible_above_charge (p q : ℕ) (hp : 2 ≤ p)
    (hq : 0 < q) (hcop : p.Coprime q) (c : ℤ) (hc : (p : ℤ) - 1 < c) :
    (affineVacuumProduct (q * (p - 1)) c).eval ((p : ℂ) / q - 2) ≠ 0 := by
  simp only [affineVacuumProduct, eval_prod, eval_pow, eval_neg, eval_add,
    eval_mul, eval_C, eval_X, sub_add_cancel]
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  by_cases hz : realRootWeight ((p : ℂ) / q) i = 0
  · obtain hi' | hi' := admissible_zero_labels_le p q hp hq hcop
      (q * (p - 1)) c le_rfl i (Finset.mem_erase.mp hi).2 hz
    · exact False.elim ((Finset.mem_erase.mp hi).1 hi')
    · have hm : affineKacMultiplicity (q * (p - 1)) c i = 0 := by
        rw [hi']
        have hp' : p - 2 + 1 = p - 1 := by omega
        have hq' : q - 1 + 1 = q := by omega
        simp only [affineKacMultiplicity, oscillatorEnergy, oscillatorCharge,
          Fin.isValue, Fin.reduceEq, if_false, if_true, hp', hq']
        rw [Nat.mul_comm (p - 1) q, Nat.sub_self]
        letI := jointIndex_zero_positive_empty (c - (p - 1 : ℕ)) (by omega)
        simp
      rw [hm, pow_zero]
      exact one_ne_zero
  · apply pow_ne_zero
    exact neg_ne_zero.mpr hz

/-- Above the primitive charge, the actual first-energy vacuum determinant
is nonzero. This excludes a horizontal raising image of a first null state. -/
theorem vacuumChevalleyDeterminant_admissible_above_charge (p q : ℕ)
    (hp : 2 ≤ p) (hq : 0 < q) (hcop : p.Coprime q) (c : ℤ)
    (hc : (p : ℤ) - 1 < c) (hprincipal : 0 < 2 * (q * (p - 1) : ℕ) - c) :
    (vacuumChevalleyPolynomial (q * (p - 1)) c).det.eval ((p : ℂ) / q - 2) ≠ 0 := by
  have hid := congrArg (Polynomial.eval ((p : ℂ) / q - 2))
    (affine_vacuum_polynomial_identity (q * (p - 1)) c hprincipal)
  simp only [eval_mul, eval_C] at hid
  have hk : (p : ℂ) / q - 2 + 2 ≠ 0 := by
    rw [sub_add_cancel]
    exact div_ne_zero (by exact_mod_cast (show p ≠ 0 by omega))
      (by exact_mod_cast (Nat.ne_of_gt hq))
  have hr := mul_ne_zero
    (mul_ne_zero (vacuumDeterminantScale_ne_zero (q * (p - 1)) c)
      (affineLeadingPolynomial_eval_ne_zero _ hk (q * (p - 1)) c))
    (affineVacuumProduct_admissible_above_charge p q hp hq hcop c hc)
  intro hz
  rw [hz, zero_mul] at hid
  exact hr hid.symm

end
end VOA.Wak.Charged
