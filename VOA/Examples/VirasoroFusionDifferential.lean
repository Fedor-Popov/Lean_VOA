/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroFusionScalar

/-!
# Formal differential reduction of the fusion scalar

A binomial gauge removes the quadratic singular coefficient. The resulting
coefficient equation has the resonant denominator n(n-N). It is only used
at intermediate indices; the terminal equation remains an obstruction.
-/
namespace VOA.InverseDS.VirasoroVerma
open VirModule PowerSeries

/-- The polynomial differential operator encoding the normalized finite
convolution, with both factors of 1-X kept and no analytic interpretation. -/
noncomputable def fusionOperator (b t y : ℂ) (N : ℕ) (F : PowerSeries ℂ) : PowerSeries ℂ :=
  (1-X)^2*bsaEuler (bsaEuler F)-
    (PowerSeries.C (N:ℂ)*(1-X)^2+PowerSeries.C t*X*(1-X))*bsaEuler F+
    PowerSeries.C t*(PowerSeries.C y*X*(1-X)-PowerSeries.C b*X)*F

/-- The scalar term after choosing a gauge exponent satisfying
ell²+(t-1)ell=tb. Its dependence on the exponent y is affine. -/
noncomputable def fusionConstant (b t y ell : ℂ) (N : ℕ) : ℂ :=
  ell*((N:ℂ)-1)+t*(y-b)

/-- The gauged operator has only a linear polynomial coefficient in X.
Its coefficient equation is hypergeometric, without using an infinite
hypergeometric solution at its singular terminal parameter. -/
noncomputable def fusionHyperOperator (b t y ell : ℂ) (N : ℕ)
    (F : PowerSeries ℂ) : PowerSeries ℂ :=
  (1-X)*bsaEuler (bsaEuler F)-
    (PowerSeries.C (N:ℂ)+PowerSeries.C (t+2*ell-(N:ℂ))*X)*bsaEuler F+
    PowerSeries.C (fusionConstant b t y ell N)*X*F

/-- The formal gauge identity follows from the binomial differential
identities and the displayed quadratic equation, at every parameter. -/
theorem fusionOperator_gauge (b t y ell : ℂ) (N : ℕ)
    (hell : ell^2+(t-1)*ell-t*b=0) (F : PowerSeries ℂ) :
    (1-X)*fusionHyperOperator b t y ell N (bsaGaugeSeries ell*F)=
      bsaGaugeSeries ell*fusionOperator b t y N F := by
  have h1 := bsaGaugeSeries_euler ell
  have h2 := bsaGaugeSeries_euler_two ell
  have g := congrArg (PowerSeries.C (R := ℂ)) hell
  simp only [map_add,map_sub,map_mul,map_pow,map_one,map_zero] at g
  unfold fusionHyperOperator fusionOperator fusionConstant
  rw [bsaEuler_mul]
  have hadd : ∀ A B : PowerSeries ℂ, bsaEuler (A+B)=bsaEuler A+bsaEuler B := by
    intro A B
    simp [bsaEuler,map_add,mul_add]
  rw [hadd,bsaEuler_mul,bsaEuler_mul]
  simp only [map_add,map_sub,map_mul,map_ofNat,map_one]
  linear_combination h2*F+h1*(2*(1-X)*bsaEuler F-
    (PowerSeries.C (N:ℂ)+(PowerSeries.C t+2*PowerSeries.C ell-PowerSeries.C (N:ℂ))*X)*F)-g*X^2*bsaGaugeSeries ell*F

/-- Coefficients of the gauged equation depend only on adjacent terms.
The coefficient multiplying the new term is zero at the terminal index N. -/
theorem fusionHyperOperator_coeff (b t y ell : ℂ) (N n : ℕ) (F : PowerSeries ℂ) :
    coeff (n+1) (fusionHyperOperator b t y ell N F)=
      ((n:ℂ)+1)*((n:ℂ)+1-(N:ℂ))*coeff (n+1) F-
      ((n:ℂ)*((n:ℂ)-(N:ℂ)+t+2*ell)-fusionConstant b t y ell N)*coeff n F := by
  unfold fusionHyperOperator
  simp only [sub_mul,add_mul,one_mul,map_add,map_sub,coeff_succ_X_mul,coeff_C_mul,
    mul_assoc,bsaEuler_coeff]
  push_cast
  ring

/-- Expanding the two polynomial coefficients exposes only shifts by zero,
one and two, making the initial coefficient equations finite calculations. -/
theorem fusionOperator_expand (b t y : ℂ) (N : ℕ) : ∀ F : PowerSeries ℂ, fusionOperator b t y N F=
      bsaEuler (bsaEuler F)-PowerSeries.C (N:ℂ)*bsaEuler F-
      X*(2*bsaEuler (bsaEuler F)+(PowerSeries.C t-2*PowerSeries.C (N:ℂ))*bsaEuler F-PowerSeries.C (t*(y-b))*F)+
      X*(X*(bsaEuler (bsaEuler F)+(PowerSeries.C t-PowerSeries.C (N:ℂ))*bsaEuler F-PowerSeries.C (t*y)*F)) := by
    intro F
    unfold fusionOperator
    simp only [map_mul,map_sub]
    ring

/-- The ungauged equation is the second finite difference of the original
undivided Ward residual. This identity applies to any numerical sequence. -/
theorem fusionOperator_coeff (b t y : ℂ) (N n : ℕ) (q : ℕ → ℂ) :
    coeff (n+2) (fusionOperator b t y N (PowerSeries.mk q))=
      (((n:ℂ)+2)*((n:ℂ)+2-(N:ℂ))*q (n+2)-t*fusionSum b y q (n+2))-
      2*(((n:ℂ)+1)*((n:ℂ)+1-(N:ℂ))*q (n+1)-t*fusionSum b y q (n+1))+
      ((n:ℂ)*((n:ℂ)-(N:ℂ))*q n-t*fusionSum b y q n) := by
  rw [fusionOperator_expand]
  simp only [map_add,map_sub,sub_mul,add_mul,coeff_C_mul,mul_assoc,
    show n+2=(n+1)+1 by omega,coeff_succ_X_mul,two_mul,bsaEuler_coeff,coeff_mk]
  have hs := fusionSum_second_difference b y q n
  push_cast
  linear_combination t*hs

/-- If the terminal source vanishes, the actual scalar series solves the
polynomial differential equation through the terminal index. -/
theorem fusionOperator_vanish_through (b t y : ℂ) (N : ℕ)
    (hs : fusionSum b y (fusionCoeff b t y N) N=0) (n : ℕ) (hn : n≤N) :
    coeff n (fusionOperator b t y N (PowerSeries.mk (fusionCoeff b t y N)))=0 := by
  have hw (j : ℕ) (hj : j≤N) : (j:ℂ)*((j:ℂ)-(N:ℂ))*fusionCoeff b t y N j=
      t*fusionSum b y (fusionCoeff b t y N) j := by
    rcases lt_or_eq_of_le hj with hj | rfl
    · exact fusionCoeff_ward b t y N j hj
    · simp [hs]
  cases n with
  | zero =>
    simp only [fusionOperator,map_add,map_sub,sub_mul,add_mul,mul_assoc,
      coeff_C_mul,coeff_zero_X_mul,one_mul,sub_zero,bsaEuler_coeff,Nat.cast_zero,zero_mul,add_zero,pow_two]
    simp [bsaEuler]
  | succ n =>
    cases n with
    | zero =>
      have hw1 := hw 1 (by omega)
      simp only [fusionSum,Fin.sum_univ_one,Fin.val_zero,Nat.cast_zero,Nat.cast_one,
        sub_zero,zero_add,show fusionCoeff b t y N 0=1 by rw [fusionCoeff],mul_one] at hw1
      rw [fusionOperator_expand]
      simp only [map_add,map_sub,sub_mul,add_mul,one_mul,coeff_C_mul,mul_assoc,
        coeff_succ_X_mul,coeff_zero_X_mul,two_mul,bsaEuler_coeff,coeff_mk,
        Nat.cast_zero,Nat.cast_one,zero_mul,sub_zero,zero_add,show fusionCoeff b t y N 0=1 by rw [fusionCoeff]]
      linear_combination hw1
    | succ n =>
      rw [show n+1+1=n+2 by omega,fusionOperator_coeff]
      have h0 := hw n (by omega)
      have h1 := hw (n+1) (by omega)
      have h2 := hw (n+2) (by omega)
      push_cast at h1 h2
      linear_combination h2-2*h1+h0

/-- A vanishing terminal source forces the gauged equation through N.
The binomial factor has no singular coefficient denominators. -/
theorem fusionHyper_vanish_through (b t y ell : ℂ) (N : ℕ)
    (hell : ell^2+(t-1)*ell-t*b=0) (hs : fusionSum b y (fusionCoeff b t y N) N=0) :
    ∀ n≤N, coeff n (fusionHyperOperator b t y ell N
      (bsaGaugeSeries ell*PowerSeries.mk (fusionCoeff b t y N)))=0 := by
  apply bsaSeries_remove_one_sub
  rw [fusionOperator_gauge b t y ell N hell]
  exact bsaSeries_mul_vanish _ _ N (fusionOperator_vanish_through b t y N hs)
end VOA.InverseDS.VirasoroVerma
