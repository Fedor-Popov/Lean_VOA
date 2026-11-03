/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroBSAIntermediateNorm
import Mathlib.RingTheory.PowerSeries.Derivative

/-!
# A nonzero terminal residual for the BSA norm recurrence

The intermediate canonical norms obey a sum over all earlier levels. Taking
its second finite difference gives a three-term recurrence. Its terminal
source is retained without dividing by the zero terminal denominator.
A formal binomial gauge converts the equation to hypergeometric form. Its
positive even resonance proves this scalar residual is nonzero. Later modules
VirasoroBSADiagonalResponse and VirasoroBSATaylor identify the actual norm
derivative with a nonzero multiple of this residual, completing boundary
minimal-model rigidity; that identification is not part of this module.
-/
namespace VOA.VirModule

/-- The undivided Ward sum for an arbitrary numerical sequence. At the
terminal index this remains meaningful even though the BSA recursion's
coefficient has zero denominator. -/
noncomputable def bsaWardSum (N : ℕ) (a : ℕ → ℂ) (r : ℕ) : ℂ :=
  ∑ j : Fin r, bsaWardCoefficient N r j * a j

/-- An empty source contains no summands. -/
@[simp] theorem bsaWardSum_zero (N : ℕ) (a : ℕ → ℂ) :
    bsaWardSum N a 0 = 0 := by simp [bsaWardSum]

/-- The level-one Ward coefficient is zero, as required by translation of
the vacuum. This boundary is valid for any scalar sequence. -/
@[simp] theorem bsaWardSum_one (N : ℕ) (a : ℕ → ℂ) :
    bsaWardSum N a 1 = 0 := by simp [bsaWardSum, bsaWardCoefficient]

/-- Away from the newest two summands the Ward coefficient is affine in
its level. Its second finite difference therefore vanishes, including the
special L₁ boundary coefficient. -/
theorem bsaWardCoefficient_second_difference (N r j : ℕ) (hj : j<r) :
    bsaWardCoefficient N (r+2) j - 2*bsaWardCoefficient N (r+1) j +
      bsaWardCoefficient N r j = 0 := by
  unfold bsaWardCoefficient
  have h1 : j+1 ≠ r+1 := by omega
  have h2 : j+1 ≠ r+2 := by omega
  rw [if_neg h2, if_neg h1]
  split_ifs with he
  · subst r
    push_cast
    ring
  · push_cast
    ring

/-- The full Ward sum has a local second difference. All earlier entries
cancel, leaving only the two newest sequence values. -/
theorem bsaWardSum_second_difference (N r : ℕ) (a : ℕ → ℂ) :
    bsaWardSum N a (r+2) - 2*bsaWardSum N a (r+1) + bsaWardSum N a r =
      ((r:ℂ)+1)*a (r+1) + (bsaL2Offset N+2-(r:ℂ))*a r := by
  classical
  unfold bsaWardSum
  rw [show r+2=(r+1)+1 by omega, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last]
  have hs : (∑ j : Fin r, bsaWardCoefficient N (r+1+1) j * a j) -
      2*(∑ j : Fin r, bsaWardCoefficient N (r+1) j * a j) +
      (∑ j : Fin r, bsaWardCoefficient N r j * a j) = 0 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro j hj
    have h := bsaWardCoefficient_second_difference N r j j.isLt
    linear_combination h * a j
  have hA : bsaWardCoefficient N (r+1+1) (r+1) = (r:ℂ)+1 := by
    simp [bsaWardCoefficient]
  have hB : bsaWardCoefficient N (r+1+1) r = (r:ℂ)+2+bsaL2Offset N := by
    simp [bsaWardCoefficient]
    ring
  have hC : bsaWardCoefficient N (r+1) r = (r:ℂ) := by simp [bsaWardCoefficient]
  rw [hA, hB, hC]
  linear_combination hs

/-- Multiplying by the recursion denominator gives an equation valid at
all levels strictly before the singular level, including level zero. -/
theorem bsaNormCoefficient_ward (N r : ℕ) (hr : r<N) :
    (r:ℂ)*((r:ℂ)-(N:ℂ))*bsaNormCoefficient N r =
      bsaParameter N * bsaWardSum N (bsaNormCoefficient N) r := by
  cases r with
  | zero => simp
  | succ r =>
    have h1 : (r:ℂ)+1 ≠ 0 := Nat.cast_add_one_ne_zero r
    have h2 : (N:ℂ)-((r:ℂ)+1) ≠ 0 := by
      exact_mod_cast (show (N:ℤ)-((r:ℤ)+1) ≠ 0 by omega)
    rw [bsaNormCoefficient]
    unfold bsaWardSum
    push_cast
    field_simp
    ring

/-- The actual intermediate norm sequence satisfies a three-term equation.
This is a consequence of the Ward recurrence, not a guessed special-function
formula. No assertion is made at the singular denominator. -/
theorem bsaNormCoefficient_three_term (N r : ℕ) (hr : r+2<N) :
    ((r:ℂ)+2)*((r:ℂ)+2-(N:ℂ))*bsaNormCoefficient N (r+2) -
      (2*((r:ℂ)+1)*((r:ℂ)+1-(N:ℂ))+bsaParameter N*((r:ℂ)+1))*
        bsaNormCoefficient N (r+1) +
      ((r:ℂ)*((r:ℂ)-(N:ℂ))-bsaParameter N*(bsaL2Offset N+2-(r:ℂ)))*
        bsaNormCoefficient N r = 0 := by
  have h0 := bsaNormCoefficient_ward N r (by omega)
  have h1 := bsaNormCoefficient_ward N (r+1) (by omega)
  have h2 := bsaNormCoefficient_ward N (r+2) hr
  have hs := bsaWardSum_second_difference N r (bsaNormCoefficient N)
  push_cast at h1 h2
  linear_combination h2 - 2*h1 + h0 + bsaParameter N*hs

/-- The terminal residual is the undivided scalar Ward source. It is not
the terminal value of the norm recursion, which has a zero denominator. -/
noncomputable def bsaNormTerminalResidual (N : ℕ) : ℂ :=
  bsaWardSum N (bsaNormCoefficient N) N

/-- At the terminal level the residual is computed by the preceding two
norm coefficients. This retains the obstruction rather than cancelling a
zero denominator. -/
theorem bsaNormTerminalResidual_eq (r : ℕ) :
    bsaParameter (r+2)*bsaNormTerminalResidual (r+2) =
      (2*((r:ℂ)+1)*((r:ℂ)+1-((r:ℂ)+2))+bsaParameter (r+2)*((r:ℂ)+1))*
        bsaNormCoefficient (r+2) (r+1) -
      ((r:ℂ)*((r:ℂ)-((r:ℂ)+2))-bsaParameter (r+2)*(bsaL2Offset (r+2)+2-(r:ℂ)))*
        bsaNormCoefficient (r+2) r := by
  have h0 := bsaNormCoefficient_ward (r+2) r (by omega)
  have h1 := bsaNormCoefficient_ward (r+2) (r+1) (by omega)
  have hs := bsaWardSum_second_difference (r+2) r (bsaNormCoefficient (r+2))
  unfold bsaNormTerminalResidual
  push_cast at h0 h1
  linear_combination bsaParameter (r+2)*hs - 2*h1 + h0


open PowerSeries

/-- Euler's formal differential operator multiplies the coefficient at
level n by n. It is used only algebraically; no convergence is required. -/
noncomputable def bsaEuler (F : PowerSeries ℂ) : PowerSeries ℂ :=
  X * derivative ℂ F

/-- The diagonal action of the Euler operator on coefficients. -/
theorem bsaEuler_coeff (F : PowerSeries ℂ) (n : ℕ) :
    coeff n (bsaEuler F) = (n:ℂ)*coeff n F := by
  cases n with
  | zero => simp [bsaEuler]
  | succ n =>
    rw [bsaEuler, coeff_succ_X_mul, coeff_derivative]
    push_cast
    ring

/-- The Euler operator obeys the product rule, just like ordinary formal
 differentiation. -/
theorem bsaEuler_mul (F G : PowerSeries ℂ) :
    bsaEuler (F*G) = bsaEuler F*G + F*bsaEuler G := by
  simp only [bsaEuler, Derivation.leibniz, smul_eq_mul]
  ring

/-- The differential operator encoding the scalar norm recurrence after
multiplication by (1-X)^2. The apparent singularity at X=1 has thus been
cleared without any analytic assumptions. -/
noncomputable def bsaNormOperator (N : ℕ) (F : PowerSeries ℂ) : PowerSeries ℂ :=
  (1-X)^2*bsaEuler (bsaEuler F) -
    (PowerSeries.C (N:ℂ)*(1-X)^2+PowerSeries.C (bsaParameter N)*X*(1-X))*bsaEuler F -
    PowerSeries.C (bsaParameter N*(bsaL2Offset N+2))*X^2*F

/-- The generating series uses the established scalar norms. Only its
coefficients below N matter; no terminal division is used in the proofs. -/
noncomputable def bsaNormSeries (N : ℕ) : PowerSeries ℂ :=
  PowerSeries.mk (bsaNormCoefficient N)

/-- The coefficient of the norm differential operator is precisely the
local three-term expression. This connects finite differences with formal
power-series manipulation. -/
theorem bsaNormOperator_coeff (N r : ℕ) (F : PowerSeries ℂ) :
    coeff (r+2) (bsaNormOperator N F) =
      ((r:ℂ)+2)*((r:ℂ)+2-(N:ℂ))*coeff (r+2) F -
      (2*((r:ℂ)+1)*((r:ℂ)+1-(N:ℂ))+bsaParameter N*((r:ℂ)+1))*coeff (r+1) F +
      ((r:ℂ)*((r:ℂ)-(N:ℂ))-bsaParameter N*(bsaL2Offset N+2-(r:ℂ)))*coeff r F := by
  have he : bsaNormOperator N F =
      bsaEuler (bsaEuler F) - PowerSeries.C (N:ℂ)*bsaEuler F -
      X*(2*bsaEuler (bsaEuler F)+(PowerSeries.C (bsaParameter N)-2*PowerSeries.C (N:ℂ))*bsaEuler F) +
      X*(X*(bsaEuler (bsaEuler F)+(PowerSeries.C (bsaParameter N)-PowerSeries.C (N:ℂ))*bsaEuler F -
        PowerSeries.C (bsaParameter N*(bsaL2Offset N+2))*F)) := by
    unfold bsaNormOperator
    ring
  rw [he]
  simp only [map_add, map_sub, sub_mul, add_mul, coeff_C_mul, mul_assoc,
    show r+2=(r+1)+1 by omega, coeff_succ_X_mul,
    two_mul, coeff_C_mul, bsaEuler_coeff]
  push_cast
  ring

/-- The first two coefficients of the norm equation vanish because a₁=0.
These are the boundary conditions needed before using the three-term rule. -/
theorem bsaNormOperator_initial (N : ℕ) :
    coeff 0 (bsaNormOperator N (bsaNormSeries N)) = 0 ∧
    coeff 1 (bsaNormOperator N (bsaNormSeries N)) = 0 := by
  have he : ∀ F : PowerSeries ℂ, bsaNormOperator N F =
      bsaEuler (bsaEuler F) - PowerSeries.C (N:ℂ)*bsaEuler F -
      X*(2*bsaEuler (bsaEuler F)+(PowerSeries.C (bsaParameter N)-2*PowerSeries.C (N:ℂ))*bsaEuler F) +
      X*(X*(bsaEuler (bsaEuler F)+(PowerSeries.C (bsaParameter N)-PowerSeries.C (N:ℂ))*bsaEuler F -
        PowerSeries.C (bsaParameter N*(bsaL2Offset N+2))*F)) := by
    intro F
    unfold bsaNormOperator
    ring
  rw [he]
  constructor <;>
    simp only [map_add, map_sub, sub_mul, add_mul, coeff_C_mul, coeff_succ_X_mul,
      coeff_zero_X_mul,
      bsaEuler_coeff, bsaNormSeries, bsaNormCoefficient_one, coeff_mk, Nat.cast_zero, Nat.cast_one, zero_mul,
      sub_zero, add_zero, mul_zero,
      two_mul]

/-- Assuming the undivided terminal residual vanishes would extend the
formal norm equation through the singular index. This implication retains
exactly the obstruction that the subsequent resonance argument tests. -/
theorem bsaNormOperator_vanish_through (N : ℕ)
    (hres : bsaNormTerminalResidual N=0) (n : ℕ) (hn : n≤N) :
    coeff n (bsaNormOperator N (bsaNormSeries N)) = 0 := by
  obtain rfl | hn0 := Nat.eq_zero_or_pos n
  · exact (bsaNormOperator_initial N).1
  obtain hz | hn1 := Nat.eq_zero_or_pos (n-1)
  · have : n=1 := by omega
    subst n
    exact (bsaNormOperator_initial N).2
  have he : n=(n-2)+2 := by omega
  rw [he, bsaNormOperator_coeff]
  simp only [bsaNormSeries, coeff_mk]
  by_cases hlt : n<N
  · exact bsaNormCoefficient_three_term N (n-2) (by omega)
  · have hN : N=(n-2)+2 := by omega
    subst N
    have hh := bsaNormTerminalResidual_eq (n-2)
    rw [hres, mul_zero] at hh
    push_cast
    linear_combination hh


/-- Coefficients of the inverse gauge factor (1-X)^(-α). Its only
denominators are positive integers, so the series exists at every α. -/
noncomputable def bsaGaugeCoefficient (α : ℂ) : ℕ → ℂ
  | 0 => 1
  | n+1 => ((n:ℂ)+α)/((n:ℂ)+1)*bsaGaugeCoefficient α n

/-- A formal gauge factor with constant term one. Unlike the proposed
hypergeometric series, this series has no resonant denominator. -/
noncomputable def bsaGaugeSeries (α : ℂ) : PowerSeries ℂ :=
  PowerSeries.mk (bsaGaugeCoefficient α)

/-- The formal binomial gauge solves its first-order differential equation.
This is proved coefficient by coefficient from its nonsingular recursion. -/
theorem bsaGaugeSeries_derivative (α : ℂ) :
    (1-X)*derivative ℂ (bsaGaugeSeries α) = PowerSeries.C α*bsaGaugeSeries α := by
  ext n
  cases n with
  | zero =>
    simp only [sub_mul, one_mul, map_sub, coeff_zero_X_mul, coeff_C_mul,
      coeff_derivative, bsaGaugeSeries, coeff_mk, bsaGaugeCoefficient]
    norm_num
  | succ n =>
    simp only [sub_mul, one_mul, map_sub, coeff_succ_X_mul, coeff_derivative,
      coeff_C_mul, bsaGaugeSeries, coeff_mk]
    simp only [bsaGaugeCoefficient]
    have h1 : (n:ℂ)+1 ≠ 0 := Nat.cast_add_one_ne_zero n
    have h2 : (n:ℂ)+1+1 ≠ 0 := by exact_mod_cast (show n+1+1≠0 by omega)
    push_cast
    field_simp
    ring

/-- Multiplying the gauge differential equation by X gives the Euler form
needed to conjugate the norm operator. -/
theorem bsaGaugeSeries_euler (α : ℂ) :
    (1-X)*bsaEuler (bsaGaugeSeries α) = PowerSeries.C α*X*bsaGaugeSeries α := by
  have h := bsaGaugeSeries_derivative α
  unfold bsaEuler
  linear_combination X*h

/-- The second Euler derivative of the gauge has a polynomial numerator.
Both factors of 1-X are retained, avoiding formal inversion in the proof. -/
theorem bsaGaugeSeries_euler_two (α : ℂ) :
    (1-X)^2*bsaEuler (bsaEuler (bsaGaugeSeries α)) =
      (PowerSeries.C α*X+(PowerSeries.C α)^2*X^2)*bsaGaugeSeries α := by
  have h1 := bsaGaugeSeries_euler α
  have h2 := congrArg (bsaEuler) h1
  simp only [bsaEuler_mul] at h2
  have he : bsaEuler (1-X : PowerSeries ℂ) = -X := by
    simp [bsaEuler, map_sub]
  have hc : bsaEuler (PowerSeries.C α*X) = PowerSeries.C α*X := by
    simp [bsaEuler, Derivation.leibniz, smul_eq_mul]
    ring
  rw [he] at h2
  have hc0 : bsaEuler (PowerSeries.C α) = 0 := by simp [bsaEuler]
  have hx : bsaEuler (X : PowerSeries ℂ) = X := by simp [bsaEuler]
  rw [hc0, hx, zero_mul, zero_add] at h2
  linear_combination (1-X)*h2+(X+PowerSeries.C α*X)*h1

/-- The hypergeometric differential operator in Euler form. It is used as
an operator on arbitrary formal series, not as an infinite solution with
the forbidden denominator 1-N. -/
noncomputable def bsaHypergeometricOperator (N : ℕ) (H : PowerSeries ℂ) : PowerSeries ℂ :=
  (1-X)*bsaEuler (bsaEuler H) - (PowerSeries.C (N:ℂ)+X)*bsaEuler H -
    PowerSeries.C (bsaParameter N*(1-bsaParameter N))*X*H

/-- Conjugation by the binomial gauge converts the genuine norm equation
to a hypergeometric equation. This is a formal ring identity and remains
valid at the resonant terminal index. -/
theorem bsaNormOperator_gauge (N : ℕ) (F : PowerSeries ℂ) :
    (1-X)*bsaHypergeometricOperator N (bsaGaugeSeries (bsaParameter N/2)*F) =
      bsaGaugeSeries (bsaParameter N/2)*bsaNormOperator N F := by
  have h1 := bsaGaugeSeries_euler (bsaParameter N/2)
  have h2 := bsaGaugeSeries_euler_two (bsaParameter N/2)
  unfold bsaHypergeometricOperator bsaNormOperator
  rw [bsaEuler_mul]
  have hadd : ∀ A B : PowerSeries ℂ, bsaEuler (A+B)=bsaEuler A+bsaEuler B := by
    intro A B
    simp [bsaEuler, map_add, mul_add]
  rw [hadd, bsaEuler_mul, bsaEuler_mul]
  have hs1 : 2*(bsaParameter N/2)-1-(N:ℂ)+bsaParameter N = 0 := by
    unfold bsaParameter
    ring
  have hs2 : bsaParameter N/2-(bsaParameter N/2)*(N:ℂ)-
      bsaParameter N*(1-bsaParameter N) = 0 := by
    unfold bsaParameter
    ring
  have hs3 : (bsaParameter N/2)^2-bsaParameter N/2+
      bsaParameter N*(1-bsaParameter N)+bsaParameter N*(bsaL2Offset N+2) = 0 := by
    unfold bsaParameter bsaL2Offset
    ring
  have g1 := congrArg (PowerSeries.C (R := ℂ)) hs1
  have g2 := congrArg (PowerSeries.C (R := ℂ)) hs2
  have g3 := congrArg (PowerSeries.C (R := ℂ)) hs3
  simp only [map_add, map_sub, map_mul, map_pow, map_one, map_ofNat, map_zero] at g1 g2 g3 ⊢
  linear_combination h2*F + h1*(2*(1-X)*bsaEuler F-(PowerSeries.C (N:ℂ)+X)*F) +
    g1*X*(1-X)*bsaGaugeSeries (bsaParameter N/2)*bsaEuler F +
    g2*X*bsaGaugeSeries (bsaParameter N/2)*F +
    g3*X^2*bsaGaugeSeries (bsaParameter N/2)*F


/-- The transformed equation has a first-order coefficient recursion.
At index N its left coefficient vanishes; the right factor is retained. -/
theorem bsaHypergeometricOperator_coeff (N n : ℕ) (H : PowerSeries ℂ) :
    coeff (n+1) (bsaHypergeometricOperator N H) =
      ((n:ℂ)+1)*((n:ℂ)+1-(N:ℂ))*coeff (n+1) H -
        ((n:ℂ)+bsaParameter N)*((n:ℂ)+1-bsaParameter N)*coeff n H := by
  have he : bsaHypergeometricOperator N H =
      bsaEuler (bsaEuler H) - PowerSeries.C (N:ℂ)*bsaEuler H -
      X*(bsaEuler (bsaEuler H)+bsaEuler H+
        PowerSeries.C (bsaParameter N*(1-bsaParameter N))*H) := by
    unfold bsaHypergeometricOperator
    ring
  rw [he]
  simp only [map_sub, map_add, coeff_C_mul, coeff_succ_X_mul, bsaEuler_coeff]
  push_cast
  ring

/-- Multiplication by any formal series preserves a specified initial
segment of zero coefficients. This uses finite convolution only. -/
theorem bsaSeries_mul_vanish (F G : PowerSeries ℂ) (N : ℕ)
    (hG : ∀ n, n≤N → coeff n G=0) (n : ℕ) (hn : n≤N) :
    coeff n (F*G)=0 := by
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  intro ab hab
  have hsum := Finset.mem_antidiagonal.mp hab
  rw [hG ab.2 (by omega), mul_zero]

/-- Removing a factor 1-X preserves an initial segment of zero coefficients:
its constant term is one, so induction recovers the vanished coefficients. -/
theorem bsaSeries_remove_one_sub (G : PowerSeries ℂ) (N : ℕ)
    (hG : ∀ n, n≤N → coeff n ((1-X)*G)=0) (n : ℕ) (hn : n≤N) :
    coeff n G=0 := by
  induction n with
  | zero => simpa only [sub_mul, one_mul, map_sub, coeff_zero_X_mul, sub_zero] using hG 0 hn
  | succ n ih =>
    have hh := hG (n+1) hn
    rw [sub_mul, one_mul, map_sub, coeff_succ_X_mul, ih (by omega), sub_zero] at hh
    exact hh

/-- If the scalar residual were zero, the gauged norm series would solve
the hypergeometric equation through the resonant index, not just below it. -/
theorem bsaNormGauge_vanish_through (N : ℕ) (hres : bsaNormTerminalResidual N=0)
    (n : ℕ) (hn : n≤N) :
    coeff n (bsaHypergeometricOperator N
      (bsaGaugeSeries (bsaParameter N/2)*bsaNormSeries N)) = 0 := by
  apply bsaSeries_remove_one_sub _ N _ n hn
  intro m hm
  rw [bsaNormOperator_gauge]
  exact bsaSeries_mul_vanish _ _ N (bsaNormOperator_vanish_through N hres) m hm

/-- The first hypergeometric numerator factor is positive as a rational
number, hence nonzero as a complex scalar. -/
theorem bsaHypergeometric_first_factor_ne_zero (N n : ℕ) :
    (n:ℂ)+bsaParameter N ≠ 0 := by
  intro h
  have hh : ((2*n+N+1:ℕ):ℂ)=0 := by
    push_cast
    unfold bsaParameter at h
    linear_combination 2*h
  have hz : 2*n+N+1=0 := by exact_mod_cast hh
  omega

/-- For even N, the other numerator factor is a nonzero half-integer.
Its hypothetical vanishing would equate an odd integer with an even one. -/
theorem bsaHypergeometric_second_factor_ne_zero (k n : ℕ) :
    (n:ℂ)+1-bsaParameter (2*k) ≠ 0 := by
  intro h
  have hh : ((2*n+1:ℕ):ℂ)=((2*k:ℕ):ℂ) := by
    push_cast
    unfold bsaParameter at h
    push_cast at h
    linear_combination 2*h
  have hz : 2*n+1=2*k := by exact_mod_cast hh
  omega

/-- No normalized formal series can solve this hypergeometric equation
through a positive even resonance. Below resonance its coefficients cannot
vanish; the terminal equation would force the last one to vanish. This
argument never constructs an infinite hypergeometric solution. -/
theorem bsaHypergeometric_even_resonance (k : ℕ) (H : PowerSeries ℂ)
    (h0 : coeff 0 H=1)
    (hH : ∀ n, n≤2*(k+1) → coeff n (bsaHypergeometricOperator (2*(k+1)) H)=0) : False := by
  have hnz : ∀ n, n<2*(k+1) → coeff n H≠0 := by
    intro n
    induction n with
    | zero => intro _; rw [h0]; exact one_ne_zero
    | succ n ih =>
      intro hn hz
      have hh := hH (n+1) (by omega)
      rw [bsaHypergeometricOperator_coeff, hz, mul_zero, zero_sub, neg_eq_zero] at hh
      exact (mul_ne_zero (mul_ne_zero (bsaHypergeometric_first_factor_ne_zero _ n)
        (bsaHypergeometric_second_factor_ne_zero (k+1) n)) (ih (by omega))) hh
  have hh := hH (2*k+1+1) (by omega)
  rw [bsaHypergeometricOperator_coeff] at hh
  have he : ((2*k+1:ℕ):ℂ)+1-((2*(k+1):ℕ):ℂ)=0 := by push_cast; ring
  rw [he, mul_zero, zero_mul, zero_sub, neg_eq_zero] at hh
  exact (mul_ne_zero (mul_ne_zero (bsaHypergeometric_first_factor_ne_zero _ _)
    (bsaHypergeometric_second_factor_ne_zero (k+1) _)) (hnz (2*k+1) (by omega))) hh

/-- The undivided scalar recurrence residual is NONZERO at every positive
even level. The proof uses formal gauge conjugation and terminal resonance,
not the experimentally observed product formula. This is not yet the norm
response within this module. The later diagonal-response and reflection
theorems establish the required link and complete the boundary rigidity proof. -/
theorem bsaNormTerminalResidual_even_ne_zero (k : ℕ) :
    bsaNormTerminalResidual (2*(k+1)) ≠ 0 := by
  intro hres
  apply bsaHypergeometric_even_resonance k
    (bsaGaugeSeries (bsaParameter (2*(k+1))/2)*bsaNormSeries (2*(k+1)))
  · simp [bsaGaugeSeries, bsaNormSeries, bsaGaugeCoefficient, bsaNormCoefficient]
  · exact bsaNormGauge_vanish_through _ hres

end VOA.VirModule
