/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.Int.Interval
import Mathlib.Tactic

/-!
# Integer-indexed creation convolutions and formal jet coefficients

Extending a sequence by zero at negative indices converts its integer
convolution into the finite coefficient convolution of formal series.
The support proof justifies the change of index even for unrestricted
sequences; no convergence or finite support of the individual sequence
is required.
-/
namespace VOA.IntegerJet
noncomputable section
open Classical
open scoped BigOperators
variable {R : Type*} [CommRing R]

/-- A natural-index sequence, extended by zero at negative integer indices. -/
def extend (f : ℕ → R) (p : ℤ) : R := if 0≤p then f p.toNat else 0

/-- At natural indices the extension returns the original coefficient. -/
theorem extend_nat (f : ℕ → R) (n : ℕ) : extend f (n : ℤ)=f n := by simp [extend]

/-- Negative indices contribute no coefficient. -/
theorem extend_negative (f : ℕ → R) (p : ℤ) (hp : p<0) : extend f p=0 := by
  simp [extend, show ¬0≤p by omega]

/-- A coefficient convolution has support in the finite interval from
zero to the target coefficient, even for infinite input sequences. -/
theorem convolution_finite (f g : ℕ → R) (n : ℤ) :
    (Function.support fun p => extend f p * extend g (n-p)).Finite := by
  apply (Set.finite_Icc 0 n).subset
  intro p hp
  change extend f p * extend g (n-p) ≠ 0 at hp
  by_cases h1 : 0≤p <;> by_cases h2 : 0≤n-p
  · exact ⟨h1,by omega⟩
  all_goals simp only [extend,h1,h2,ite_true,ite_false,mul_zero,zero_mul,ne_eq,not_true_eq_false] at hp

/-- The integer convolution equals the actual formal-series coefficient. -/
theorem convolution_coefficient (f g : ℕ → R) (n : ℕ) :
    (∑ᶠ p : ℤ, extend f p * extend g ((n : ℤ)-p)) =
      PowerSeries.coeff n (PowerSeries.mk f * PowerSeries.mk g) := by
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.Icc 0 (n : ℤ)) (by
    intro p hp
    change extend f p * extend g ((n : ℤ)-p) ≠ 0 at hp
    by_cases h1 : 0≤p <;> by_cases h2 : 0≤(n : ℤ)-p
    · simp only [Finset.mem_coe, Finset.mem_Icc]; omega
    all_goals simp only [extend,h1,h2,ite_true,ite_false,mul_zero,zero_mul,ne_eq,not_true_eq_false] at hp)]
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [PowerSeries.coeff_mk]
  apply Finset.sum_nbij' Int.toNat (fun a : ℕ => (a : ℤ))
  · intro p hp
    simp only [Finset.mem_Icc] at hp
    simp only [Finset.mem_range]
    omega
  · intro a ha
    simp only [Finset.mem_range] at ha
    simp only [Finset.mem_Icc]
    omega
  · intro p hp
    simp only [Finset.mem_Icc] at hp
    exact Int.toNat_of_nonneg hp.1
  · intro a _
    exact Int.toNat_natCast a
  · intro p hp
    simp only [Finset.mem_Icc] at hp
    simp only [extend, if_pos hp.1, if_pos (by omega : 0≤(n : ℤ)-p)]
    congr 2
    omega

/-- A convolution at a negative target is zero: two nonnegative indices
cannot sum to that target. -/
theorem convolution_negative (f g : ℕ → R) (n : ℤ) (hn : n<0) :
    (∑ᶠ p : ℤ, extend f p * extend g (n-p))=0 := by
  apply finsum_eq_zero_of_forall_eq_zero
  intro p
  by_cases hp : p<0
  · simp [extend_negative f p hp]
  · simp [extend_negative g (n-p) (by omega)]

/-- A uniform signed-index coefficient formula, including the negative
zero range. -/
theorem convolution_extend (f g : ℕ → R) (n : ℤ) :
    (∑ᶠ p : ℤ, extend f p * extend g (n-p)) =
      extend (fun r => PowerSeries.coeff r (PowerSeries.mk f * PowerSeries.mk g)) n := by
  by_cases hn : 0≤n
  · simpa only [Int.toNat_of_nonneg hn, extend, if_pos hn] using convolution_coefficient f g n.toNat
  · rw [convolution_negative f g n (by omega), extend_negative _ n (by omega)]

/-- Mode-indexed creation convolutions, after reversing the integer
summation index and accounting for the creation-field shift. -/
theorem creation_convolution (f g : ℕ → R) (a n : ℤ) :
    (∑ᶠ p : ℤ, extend f (-p-a) * extend g (p-n)) =
      extend (fun r => PowerSeries.coeff r (PowerSeries.mk f * PowerSeries.mk g)) (-n-a) := by
  calc
    _ = ∑ᶠ p : ℤ, extend f (-(-a-p)-a) * extend g ((-a-p)-n) :=
      (finsum_comp_equiv (Equiv.subLeft (-a))
        (f := fun p : ℤ => extend f (-p-a) * extend g (p-n))).symm
    _ = ∑ᶠ p : ℤ, extend f p * extend g ((-n-a)-p) := by
      apply finsum_congr
      intro p
      congr 2 <;> ring
    _ = _ := convolution_extend f g (-n-a)

end
end VOA.IntegerJet
