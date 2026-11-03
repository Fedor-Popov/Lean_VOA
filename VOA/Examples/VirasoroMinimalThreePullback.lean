/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroMinimalThreeHypergeometric

/-!
# Formal gauge and quadratic pullback for the q=3 scalar equation

All calculations are in formal power series. Multiplication by (1-X)^3
clears the scalar Ward equation's denominators; no convergence, division
at resonance, or infinite hypergeometric solution is involved.
-/
namespace VOA.InverseDS.VirasoroVerma
open VirModule PowerSeries

/-- The polynomial differential operator obtained by clearing the three
powers of 1-X from the normalized scalar Ward equation. -/
noncomputable def minimalThreeNormOperator (a : ℂ) (F : PowerSeries ℂ) : PowerSeries ℂ :=
  (1-X)^3*(bsaEuler (bsaEuler (bsaEuler F))-PowerSeries.C (4*a+1)*bsaEuler (bsaEuler F)+
    PowerSeries.C (a*(3*a+1))*bsaEuler F)+
  PowerSeries.C (a+1)*(PowerSeries.C (2*a^2)*X^2*(2-X)*F+
    PowerSeries.C a*X*(3-4*X)*(1-X)*bsaEuler F-2*X*(1-X)^2*bsaEuler (bsaEuler F))

/-- The scalar norm operator written in ordinary derivatives, making the
formal chain and product rules applicable directly. -/
theorem minimalThreeNormOperator_derivatives (a : ℂ) (F : PowerSeries ℂ) :
    minimalThreeNormOperator a F=
      (1-X)^3*X^3*derivative ℂ (derivative ℂ (derivative ℂ F))+
      ((2-4*PowerSeries.C a)*(1-X)^3*X^2-2*(PowerSeries.C a+1)*X^3*(1-X)^2)*
        derivative ℂ (derivative ℂ F)+
      ((3*(PowerSeries.C a)^2-3*PowerSeries.C a)*(1-X)^3*X+
        (PowerSeries.C a+1)*PowerSeries.C a*X^2*(3-4*X)*(1-X)-
        2*(PowerSeries.C a+1)*X^2*(1-X)^2)*derivative ℂ F+
      2*(PowerSeries.C a+1)*(PowerSeries.C a)^2*X^2*(2-X)*F := by
  simp only [minimalThreeNormOperator,bsaEuler,Derivation.leibniz,smul_eq_mul,
    derivative_X,Derivation.map_one_eq_zero,zero_mul,mul_zero,add_zero,zero_add,one_mul,map_add,map_sub,map_mul,map_pow,map_ofNat,map_one]
  ring

/-- Second ordinary derivative of the binomial gauge, with its polynomial
denominator kept on the left. -/
theorem minimalThreeGauge_derivative_two (α : ℂ) :
    (1-X)^2*derivative ℂ (derivative ℂ (bsaGaugeSeries α))=
      PowerSeries.C (α*(α+1))*bsaGaugeSeries α := by
  have h1 := bsaGaugeSeries_derivative α
  have h2 := congrArg (derivative ℂ) h1
  simp only [Derivation.leibniz,smul_eq_mul,map_sub,Derivation.map_one_eq_zero,derivative_X,
    zero_sub,neg_one_mul,derivative_C,zero_mul,zero_add] at h2
  simp only [map_mul,map_add,map_one]
  linear_combination (1-X)*h2+(1+PowerSeries.C α)*h1

/-- Third ordinary derivative of the same gauge. This is a formal
consequence of its first-order equation, valid at every complex exponent. -/
theorem minimalThreeGauge_derivative_three (α : ℂ) :
    (1-X)^3*derivative ℂ (derivative ℂ (derivative ℂ (bsaGaugeSeries α)))=
      PowerSeries.C (α*(α+1)*(α+2))*bsaGaugeSeries α := by
  have h1 := bsaGaugeSeries_derivative α
  have h2 := minimalThreeGauge_derivative_two α
  have h3 := congrArg (derivative ℂ) h2
  simp only [pow_two,Derivation.leibniz,smul_eq_mul,map_sub,Derivation.map_one_eq_zero,derivative_X,
    zero_sub,neg_one_mul,derivative_C,zero_mul,zero_add] at h3
  simp only [map_mul,map_add,map_one,map_ofNat] at h2 ⊢
  simp only [map_mul,map_add,map_one] at h3
  linear_combination (1-X)*h3+2*h2+PowerSeries.C α*(PowerSeries.C α+1)*h1

/-- The norm operator after removing the binomial gauge. Its coefficients
are polynomials; the next change of variable is quadratic. -/
noncomputable def minimalThreeGaugedOperator (a : ℂ) (F : PowerSeries ℂ) : PowerSeries ℂ :=
  (1-X)^3*X^3*derivative ℂ (derivative ℂ (derivative ℂ F))+
  2*X^2*(2*PowerSeries.C a-1)*(1-X)^2*(2*X-1)*derivative ℂ (derivative ℂ F)+
  X*(1-X)*(19*(PowerSeries.C a)^2*X^2-19*(PowerSeries.C a)^2*X+
    3*(PowerSeries.C a)^2-15*PowerSeries.C a*X^2+15*PowerSeries.C a*X-
    3*PowerSeries.C a+2*X^2-2*X)*derivative ℂ F-
  6*(PowerSeries.C a)^2*X*(PowerSeries.C a-1)*(1-X)*(2*X-1)*F

/-- Multiplication by the nonsingular binomial gauge conjugates the
cleared Ward operator exactly. This holds on every formal input series. -/
theorem minimalThreeNormOperator_gauge (a : ℂ) (F : PowerSeries ℂ) :
    minimalThreeNormOperator a (bsaGaugeSeries (2*a)*F)=
      bsaGaugeSeries (2*a)*minimalThreeGaugedOperator a F := by
  have h1 := bsaGaugeSeries_derivative (2*a)
  have h2 := minimalThreeGauge_derivative_two (2*a)
  have h3 := minimalThreeGauge_derivative_three (2*a)
  simp only [map_mul,map_add,map_ofNat,map_one] at h1 h2 h3
  apply mul_left_cancel₀ (show (1-X:PowerSeries ℂ)^3≠0 by
    apply pow_ne_zero
    intro h
    have := congrArg (coeff 0) h
    simpa using this)
  rw [minimalThreeNormOperator_derivatives]
  simp only [minimalThreeGaugedOperator,Derivation.leibniz,smul_eq_mul,map_add]
  linear_combination
    X^3*(1-X)^3*F*h3+
    (1-X)*(3*X^3*(1-X)^3*derivative ℂ F+
      ((2-4*PowerSeries.C a)*(1-X)^3*X^2-2*(PowerSeries.C a+1)*X^3*(1-X)^2)*F)*h2+
    (1-X)^2*(3*X^3*(1-X)^3*derivative ℂ (derivative ℂ F)+
      2*((2-4*PowerSeries.C a)*(1-X)^3*X^2-2*(PowerSeries.C a+1)*X^3*(1-X)^2)*derivative ℂ F+
      ((3*(PowerSeries.C a)^2-3*PowerSeries.C a)*(1-X)^3*X+
        (PowerSeries.C a+1)*PowerSeries.C a*X^2*(3-4*X)*(1-X)-
        2*(PowerSeries.C a+1)*X^2*(1-X)^2)*F)*h1


/-- Four times the transformed operator has integral polynomial coefficients
in a. This ordinary-derivative version avoids any formal-series division. -/
theorem minimalThreeHyperOperator_four (a : ℂ) (F : PowerSeries ℂ) :
    4*minimalThreeHyperOperator a F=
      4*X^3*(1-X)*derivative ℂ (derivative ℂ (derivative ℂ F))+
      X^2*(8-16*PowerSeries.C a-(14-16*PowerSeries.C a)*X)*derivative ℂ (derivative ℂ F)+
      X*(12*(PowerSeries.C a)^2-12*PowerSeries.C a-
        (19*(PowerSeries.C a)^2-23*PowerSeries.C a+6)*X)*derivative ℂ F-
      6*(PowerSeries.C a)^2*(1-PowerSeries.C a)*X*F := by
  have h2 := congrArg (PowerSeries.C (R:=ℂ))
    (show 4*((1-8*a)/2)=2-16*a by ring)
  have h3 := congrArg (PowerSeries.C (R:=ℂ))
    (show 4*((19*a^2-7*a)/4)=19*a^2-7*a by ring)
  have h4 := congrArg (PowerSeries.C (R:=ℂ))
    (show 4*(3*a^2*(1-a)/2)=6*a^2*(1-a) by ring)
  simp only [map_mul,map_sub,map_pow,map_ofNat,map_one] at h2 h3 h4
  simp only [minimalThreeHyperOperator,bsaEuler,Derivation.leibniz,smul_eq_mul,
    derivative_X,Derivation.map_one_eq_zero,one_mul,zero_mul,mul_zero,add_zero,
    zero_add,map_add,map_sub,map_mul,map_pow,map_ofNat,map_one]
  linear_combination -X*(X*derivative ℂ F+X^2*derivative ℂ (derivative ℂ F))*h2-
    X^2*derivative ℂ F*h3-X*F*h4

/-- The quadratic variable change has zero constant term, so its
substitution into every formal series is well-defined. -/
noncomputable def minimalThreeQuadratic : PowerSeries ℂ := 4*X*(1-X)

/-- The quadratic substitution is legitimate in the formal topology. -/
theorem minimalThreeQuadratic_hasSubst : HasSubst minimalThreeQuadratic := by
  apply HasSubst.of_constantCoeff_zero'
  simp [minimalThreeQuadratic]

/-- The quadratic pullback changes the gauged norm operator into the
hypergeometric operator. The extra factor has constant coefficient one. -/
theorem minimalThreeGaugedOperator_pullback (a : ℂ) (G : PowerSeries ℂ) :
    minimalThreeGaugedOperator a (G.subst minimalThreeQuadratic)=
      (1-2*X)*(minimalThreeHyperOperator a G).subst minimalThreeQuadratic := by
  have hs := minimalThreeQuadratic_hasSubst
  have hh := congrArg (fun F : PowerSeries ℂ => F.subst minimalThreeQuadratic)
    (minimalThreeHyperOperator_four a G)
  simp only [← coe_substAlgHom hs,map_mul,map_add,map_sub,map_pow,map_ofNat,map_one] at hh
  simp only [coe_substAlgHom,subst_C,subst_X hs] at hh
  have hn4 : derivative ℂ (4:PowerSeries ℂ)=0 := Derivation.map_natCast _ 4
  have hn2 : derivative ℂ (2:PowerSeries ℂ)=0 := Derivation.map_natCast _ 2
  have hn8 : derivative ℂ (-8:PowerSeries ℂ)=0 := by
    rw [map_neg]; exact neg_eq_zero.mpr (Derivation.map_natCast _ 8)
  have hd : derivative ℂ minimalThreeQuadratic=4*(1-2*X) := by
    simp [minimalThreeQuadratic,Derivation.leibniz,smul_eq_mul,hn4,hn2]
    ring
  have hdd : derivative ℂ (4*(1-2*X):PowerSeries ℂ)= -8 := by
    simp [Derivation.leibniz,smul_eq_mul,hn4,hn2]
    ring
  apply mul_left_cancel₀ (show (4:PowerSeries ℂ)≠0 by
    intro h; have := congrArg PowerSeries.constantCoeff h; norm_num only [map_ofNat,map_zero] at this)
  simp only [minimalThreeGaugedOperator,derivative_subst ℂ hs,
    Derivation.leibniz,smul_eq_mul,map_add,hd,hdd,hn4,hn2,hn8,
    map_sub,Derivation.map_one_eq_zero,derivative_X,zero_mul,mul_zero,zero_add,add_zero]
  simp only [minimalThreeQuadratic] at hh ⊢
  simp only [show (MvPowerSeries.C a:PowerSeries ℂ)=PowerSeries.C a from rfl] at hh
  linear_combination -(1-2*X)*hh

/-- The complete formal change of variables, including its binomial
gauge. This identity is valid even at the resonant parameter. -/
theorem minimalThreeNormOperator_pullback (a : ℂ) (G : PowerSeries ℂ) :
    minimalThreeNormOperator a (bsaGaugeSeries (2*a)*G.subst minimalThreeQuadratic)=
      bsaGaugeSeries (2*a)*(1-2*X)*(minimalThreeHyperOperator a G).subst minimalThreeQuadratic := by
  rw [minimalThreeNormOperator_gauge,minimalThreeGaugedOperator_pullback]
  ring

end VOA.InverseDS.VirasoroVerma
