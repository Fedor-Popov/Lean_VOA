/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2KacVacuumCoefficient

/-! # Horizontal factor removal at every nonnegative integral highest weight

The coefficient is taken after translation of the highest-weight variable by d.
Exactly the horizontal relation F₀^(d+1) is removed; all other real-root
factors and their genuine descendant multiplicities remain.
-/
namespace VOA.Wak.Charged
open Polynomial AffineVOA.HighestModule
noncomputable section
open scoped Classical
local instance parabolicKacFintype (n : ℕ) (c : ℤ) : Fintype (JointIndex n c) :=
  jointIndexFintype n c

/-- The horizontal relation label fits precisely the finite principal bound. -/
theorem affineKacLabels_horizontal_power_mem (d n : ℕ) (c : ℤ)
    (hc : (d : ℤ) < 2*(n : ℤ)-c) :
    ((1,0),d) ∈ affineKacLabels n c := by
  simp [affineKacLabels,realRootModes,jointModeBox,oscillatorEnergy,
    show d < (2*(n : ℤ)-c).toNat by omega]

/-- The Kac product with only the horizontal d+1 relation omitted. -/
def affineKacWithoutHorizontalPower (t : ℂ) (d n : ℕ) (c : ℤ) : ℂ[X] :=
  ∏ i ∈ (affineKacLabels n c).erase ((1,0),d),
    (X-Polynomial.C (realRootWeight t i))^affineKacMultiplicity n c i

/-- Exact extraction of the horizontal highest-weight factor, with actual
shifted Verma descendant dimension as its exponent. -/
theorem affineKacProduct_horizontal_power_factor (t : ℂ) (d n : ℕ) (c : ℤ)
    (hc : (d : ℤ) < 2*(n : ℤ)-c) :
    affineKacProduct t n c =
      (X-Polynomial.C (d : ℂ))^Fintype.card (JointIndex n (c+(d+1 : ℕ))) *
        affineKacWithoutHorizontalPower t d n c := by
  have he := Finset.mul_prod_erase (affineKacLabels n c)
    (fun i => (X-Polynomial.C (realRootWeight t i))^affineKacMultiplicity n c i)
    (affineKacLabels_horizontal_power_mem d n c hc)
  have hr : realRootWeight t ((1,0),d) = (d : ℂ) := by
    simp [realRootWeight,realRootSlope,realRootOffset]
  have hm : affineKacMultiplicity n c ((1,0),d) =
      Fintype.card (JointIndex n (c+(d+1 : ℕ))) := by
    unfold affineKacMultiplicity
    congr 2 <;> simp [oscillatorEnergy,oscillatorCharge] <;> omega
  dsimp only at he
  rw [hr,hm] at he
  exact he.symm

/-- Outside the finite label box the reflected descendant block is empty,
so the factorization holds with exponent zero as well. -/
theorem affineKacProduct_horizontal_power_factor_all (t : ℂ) (d n : ℕ) (c : ℤ) :
    affineKacProduct t n c =
      (X-Polynomial.C (d : ℂ))^Fintype.card (JointIndex n (c+(d+1 : ℕ))) *
        affineKacWithoutHorizontalPower t d n c := by
  by_cases hc : (d : ℤ) < 2*(n : ℤ)-c
  · exact affineKacProduct_horizontal_power_factor t d n c hc
  · have hn : ((1,0),d) ∉ affineKacLabels n c := by
      intro hi
      have hh := (Finset.mem_product.mp (Finset.mem_filter.mp hi).1).2
      have hh' : d < (2*(n : ℤ)-c).toNat := Finset.mem_range.mp hh
      omega
    letI : IsEmpty (JointIndex n (c+(d+1 : ℕ))) := ⟨fun e => by
      have he := occupationPrincipal_eq e.val
      rw [e.property.1,e.property.2] at he
      push_cast at he
      omega⟩
    have he : Fintype.card (JointIndex n (c+(d+1 : ℕ))) = 0 := Fintype.card_eq_zero
    rw [he,pow_zero,one_mul]
    simp only [affineKacWithoutHorizontalPower,Finset.erase_eq_of_notMem hn,affineKacProduct]

/-- The reduced determinant product at weight d, as an explicit polynomial
in the central level; the shifted level is X+2. -/
def affineParabolicProduct (d n : ℕ) (c : ℤ) : ℂ[X] :=
  ∏ i ∈ (affineKacLabels n c).erase ((1,0),d),
    (Polynomial.C (d : ℂ) - (Polynomial.C (realRootSlope i.1 : ℂ)*(X+Polynomial.C 2)+
      Polynomial.C (realRootOffset i.1 i.2 : ℂ)))^affineKacMultiplicity n c i

/-- Translation to weight d converts the extracted horizontal factor to
an exact power of X. -/
theorem affineKacProduct_horizontal_shift (t : ℂ) (d n : ℕ) (c : ℤ)
    (hc : (d : ℤ) < 2*(n : ℤ)-c) :
    (affineKacProduct t n c).comp (X+Polynomial.C (d : ℂ)) =
      X^Fintype.card (JointIndex n (c+(d+1 : ℕ))) *
        (affineKacWithoutHorizontalPower t d n c).comp (X+Polynomial.C (d : ℂ)) := by
  rw [affineKacProduct_horizontal_power_factor t d n c hc]
  simp

/-- The first possible Taylor coefficient at weight d is exactly the
remaining root product, including roots that happen to collide at special levels. -/
theorem affineKacProduct_parabolic_coefficient (k : ℂ) (d n : ℕ) (c : ℤ)
    (hc : (d : ℤ) < 2*(n : ℤ)-c) :
    ((affineKacProduct (k+2) n c).comp (X+Polynomial.C (d : ℂ))).coeff
        (Fintype.card (JointIndex n (c+(d+1 : ℕ)))) =
      (affineParabolicProduct d n c).eval k := by
  rw [affineKacProduct_horizontal_shift _ _ _ _ hc]
  have he := coeff_X_pow_mul
    ((affineKacWithoutHorizontalPower (k+2) d n c).comp (X+Polynomial.C (d : ℂ)))
    (Fintype.card (JointIndex n (c+(d+1 : ℕ)))) 0
  simp only [zero_add] at he
  rw [he]
  simp [coeff_zero_eq_eval_zero,affineKacWithoutHorizontalPower,
    affineParabolicProduct,eval_prod,realRootWeight]

/-- The same coefficient of the actual, normalized Verma determinant.
This statement has no generic-level or noncritical hypothesis. -/
theorem weightDeterminant_parabolic_coefficient (k : ℂ) (d n : ℕ) (c : ℤ)
    (hc : (d : ℤ) < 2*(n : ℤ)-c) :
    ((weightDeterminant k n c).comp (X+Polynomial.C (d : ℂ))).coeff
        (Fintype.card (JointIndex n (c+(d+1 : ℕ)))) =
      (affineLeadingPolynomial n c).eval k * (affineParabolicProduct d n c).eval k := by
  have hf := weightDeterminant_eq_affineKacProduct_all (k+2) n c
  simp only [add_sub_cancel_right] at hf
  rw [hf,mul_comp,C_comp,coeff_C_mul,affineKacProduct_parabolic_coefficient k d n c hc]
  simp [affineLeadingPolynomial,eval_prod,derivativePolynomial_eval]

/-- Unconditional centered coefficient extraction, including empty reflected blocks. -/
theorem weightDeterminant_parabolic_coefficient_all (k : ℂ) (d n : ℕ) (c : ℤ) :
    ((weightDeterminant k n c).comp (X+Polynomial.C (d : ℂ))).coeff
        (Fintype.card (JointIndex n (c+(d+1 : ℕ)))) =
      (affineLeadingPolynomial n c).eval k * (affineParabolicProduct d n c).eval k := by
  have hf := weightDeterminant_eq_affineKacProduct_all (k+2) n c
  simp only [add_sub_cancel_right] at hf
  rw [hf,mul_comp,C_comp,coeff_C_mul,affineKacProduct_horizontal_power_factor_all,
    mul_comp,pow_comp,sub_comp,X_comp,C_comp,add_sub_cancel_right]
  have he := coeff_X_pow_mul
    ((affineKacWithoutHorizontalPower (k+2) d n c).comp (X+Polynomial.C (d : ℂ)))
    (Fintype.card (JointIndex n (c+(d+1 : ℕ)))) 0
  simp only [zero_add] at he
  rw [he]
  simp [coeff_zero_eq_eval_zero,affineKacWithoutHorizontalPower,
    affineParabolicProduct,realRootWeight,affineLeadingPolynomial,
    eval_prod,derivativePolynomial_eval]

/-- Central specialization of the genuine reflected Verma determinant. -/
def affineReflectedPolynomial (d n : ℕ) (c : ℤ) : ℂ[X] :=
  MvPolynomial.eval₂Hom Polynomial.C ![X,Polynomial.C (-(d : ℂ)-2)] (highestDeterminant n c)

/-- The denominator block is the actual Verma form at reflected highest
weight -d-2, with its fixed normalization. -/
theorem affineReflectedPolynomial_eval (k : ℂ) (d n : ℕ) (c : ℤ) :
    (affineReflectedPolynomial d n c).eval k =
      (weightDeterminant k n c).eval (-(d : ℂ)-2) := by
  rw [weightDeterminant_eval_highest]
  change Polynomial.evalRingHom k (MvPolynomial.eval₂Hom Polynomial.C
    ![X,Polynomial.C (-(d : ℂ)-2)] _) = _
  rw [MvPolynomial.map_eval₂Hom]
  have hc : (Polynomial.evalRingHom k).comp Polynomial.C = RingHom.id ℂ := by ext z; simp
  rw [hc]
  have hx : (fun a : Fin 2 => Polynomial.evalRingHom k (![X,Polynomial.C (-(d : ℂ)-2)] a)) =
      ![k,-(d : ℂ)-2] := by funext a; fin_cases a <;> simp
  rw [hx]
  rfl

end
end VOA.Wak.Charged
