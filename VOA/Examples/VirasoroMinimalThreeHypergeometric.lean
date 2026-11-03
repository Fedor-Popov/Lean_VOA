/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroMinimalThreeNormScalar
import VOA.Examples.VirasoroBSANormRecurrence

/-!
# The finite hypergeometric resonance for the q=3 norm problem

This is an ordinary scalar calculation. The third-order operator has no
normalized formal solution through its resonant index at coprime (p,3).
The proof only uses finite coefficient equations; no infinite hypergeometric
series with a zero denominator is introduced. Connecting this operator to
the actual norm recurrence is a separate pullback calculation.
-/
namespace VOA.InverseDS.VirasoroVerma
open VirModule PowerSeries

/-- The cubic numerator in the adjacent-coefficient equation. Its three
factors are the upper hypergeometric parameters shifted by the index. -/
noncomputable def minimalThreeHyperNumerator (a : ℂ) (n : ℕ) : ℂ :=
  ((n:ℂ)-2*a)*((n:ℂ)-3*a/2)*((n:ℂ)+(1-a)/2)

/-- The third-order hypergeometric operator, applied to an arbitrary
formal series. It is an operator, not an asserted infinite solution. -/
noncomputable def minimalThreeHyperOperator (a : ℂ) (F : PowerSeries ℂ) : PowerSeries ℂ :=
  bsaEuler (bsaEuler (bsaEuler F)) - PowerSeries.C (4*a+1)*bsaEuler (bsaEuler F) +
    PowerSeries.C (a*(3*a+1))*bsaEuler F -
  X*(bsaEuler (bsaEuler (bsaEuler F)) + PowerSeries.C ((1-8*a)/2)*bsaEuler (bsaEuler F) +
    PowerSeries.C ((19*a^2-7*a)/4)*bsaEuler F + PowerSeries.C (3*a^2*(1-a)/2)*F)

/-- The operator's coefficient equation uses just two adjacent values.
The new coefficient's factor vanishes at n+1=3a+1; its right-hand side
must therefore be retained as a terminal obstruction. -/
theorem minimalThreeHyperOperator_coeff (a : ℂ) (F : PowerSeries ℂ) (n : ℕ) :
    coeff (n+1) (minimalThreeHyperOperator a F)=
      ((n:ℂ)+1)*((n:ℂ)+1-a)*((n:ℂ)-3*a)*coeff (n+1) F-
        minimalThreeHyperNumerator a n*coeff n F := by
  unfold minimalThreeHyperOperator minimalThreeHyperNumerator
  simp only [map_add,map_sub,add_mul,sub_mul,coeff_C_mul,coeff_succ_X_mul,bsaEuler_coeff]
  push_cast
  ring

/-- Coprimality with three and parity exclude all three numerator zeros,
at every natural index. No positivity or analytic convergence is needed. -/
theorem minimalThreeHyperNumerator_ne_zero (p n : ℕ) (hcop : Nat.Coprime p 3) :
    minimalThreeHyperNumerator (2*(p:ℂ)/3-1) n≠0 := by
  unfold minimalThreeHyperNumerator
  apply mul_ne_zero
  · apply mul_ne_zero
    · intro h
      have he : 3*n+6=4*p := by
        exact_mod_cast (show (3:ℂ)*(n:ℂ)+6=4*(p:ℂ) by linear_combination 3*h)
      have hd : 3∣4*p := he ▸ (by omega : 3∣3*n+6)
      exact minimal_three_not_dvd p hcop ((by decide : Nat.Coprime 3 4).dvd_of_dvd_mul_left hd)
    · intro h
      have he : 2*n+3=2*p := by
        exact_mod_cast (show (2:ℂ)*(n:ℂ)+3=2*(p:ℂ) by linear_combination 2*h)
      omega
  · intro h
    have he : 3*n+3=p := by
      exact_mod_cast (show (3:ℂ)*(n:ℂ)+3=(p:ℂ) by linear_combination 3*h)
    exact minimal_three_not_dvd p hcop (he ▸ (by omega : 3∣3*n+3))

/-- No formal series starting at one can satisfy all coefficient equations
through the terminal index. The equations propagate nonzero coefficients,
then the last equation contradicts a nonzero numerator. -/
theorem minimalThreeHyper_resonance (p : ℕ) (hp : 2≤p) (hcop : Nat.Coprime p 3)
    (F : PowerSeries ℂ) (h0 : coeff 0 F=1)
    (hF : ∀ n, n≤(p-1)*2 → coeff n (minimalThreeHyperOperator (2*(p:ℂ)/3-1) F)=0) : False := by
  have hnz : ∀ n, n<(p-1)*2 → coeff n F≠0 := by
    intro n
    induction n with
    | zero => intro _; rw [h0]; exact one_ne_zero
    | succ n ih =>
      intro hn hz
      have he := hF (n+1) (by omega)
      rw [minimalThreeHyperOperator_coeff,hz,mul_zero,zero_sub,neg_eq_zero] at he
      exact (mul_ne_zero (minimalThreeHyperNumerator_ne_zero p n hcop) (ih (by omega))) he
  have hr : (p-1)*2=((p-1)*2-1)+1 := by omega
  have he := hF (((p-1)*2-1)+1) (by omega)
  rw [minimalThreeHyperOperator_coeff] at he
  have hs : (((p-1)*2-1:ℕ):ℂ)=2*(p:ℂ)-3 := by
    have hn : (p-1)*2-1+3=2*p := by omega
    have hc : ((((p-1)*2-1:ℕ):ℂ)+3)=2*(p:ℂ) := by exact_mod_cast hn
    linear_combination hc
  have hz : (((p-1)*2-1:ℕ):ℂ)-3*(2*(p:ℂ)/3-1)=0 := by rw [hs]; ring
  rw [hz,mul_zero,zero_mul,zero_sub,neg_eq_zero] at he
  exact (mul_ne_zero (minimalThreeHyperNumerator_ne_zero p _ hcop) (hnz _ (by omega))) he

end VOA.InverseDS.VirasoroVerma
