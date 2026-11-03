/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroFusionTopConvolution

/-!
# A binomial gauge for the complete fusion equation

The previous-coefficient term becomes a single quadratic monomial after
the same formal gauge used for the diagonal. Thus the complete scalar
problem reduces to a two-dimensional nearest-neighbor recurrence. No
infinite hypergeometric solution or experimental normalization product is
used, and the terminal equation is left undivided.
-/
namespace VOA.InverseDS.VirasoroVerma
open VirModule PowerSeries

/-- The preceding coefficient sequence, taken as zero at coefficient zero.
This convention removes exceptional negative coefficient indices. -/
noncomputable def fusionTopPrevious (q : ℕ → ℕ → ℂ) (r j : ℕ) : ℂ :=
  if 0<r then q j (r-1) else 0

/-- The full source splits into the known diagonal source and one prefix
sum of the preceding coefficient, with no omitted boundary term. -/
theorem fusionTopSum_prefix (b y : ℂ) (q : ℕ → ℕ → ℂ) (n r : ℕ) :
    fusionTopSum b y q (n+1) r=
      fusionSum b (y+(r:ℂ)) (fun j => q j r) (n+1)+
        ∑ j : Fin n, fusionTopPrevious q r j := by
  rw [fusionTopSum_decompose]
  unfold fusionTopPrevious
  split_ifs <;> simp

/-- Second differences of a prefix sum leave only two adjacent terms. -/
theorem fusionPrefix_second_difference (p : ℕ → ℂ) (n : ℕ) :
    (∑ j : Fin (n+2),p j)-2*(∑ j : Fin (n+1),p j)+(∑ j : Fin n,p j)=p (n+1)-p n := by
  rw [show n+2=(n+1)+1 by omega,Fin.sum_univ_castSucc,Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc,Fin.val_last]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc,Fin.val_last]
  ring

/-- The polynomial differential operator for the full two-coefficient
source. F is the current coefficient series, P the preceding one. -/
noncomputable def fusionTopOperator (b t y : ℂ) (N : ℕ)
    (F P : PowerSeries ℂ) : PowerSeries ℂ :=
  fusionOperator b t y N F-PowerSeries.C t*X*(X*((1-X)*P))

/-- The gauged equation has a single quadratic coupling to the preceding
coefficient. This is a finite formal identity, not an analytic series assertion. -/
noncomputable def fusionTopHyperOperator (b t y ell : ℂ) (N : ℕ)
    (F P : PowerSeries ℂ) : PowerSeries ℂ :=
  fusionHyperOperator b t y ell N F-PowerSeries.C t*X*(X*P)

/-- The diagonal gauge simultaneously transforms the complete source,
including its off-diagonal term. The same factor multiplies both series. -/
theorem fusionTopOperator_gauge (b t y ell : ℂ) (N : ℕ)
    (hell : ell^2+(t-1)*ell-t*b=0) (F P : PowerSeries ℂ) :
    (1-X)*fusionTopHyperOperator b t y ell N (bsaGaugeSeries ell*F) (bsaGaugeSeries ell*P)=
      bsaGaugeSeries ell*fusionTopOperator b t y N F P := by
  unfold fusionTopHyperOperator fusionTopOperator
  linear_combination fusionOperator_gauge b t y ell N hell F

/-- Coefficients of the gauged full equation involve the current and
previous stages, together with one term from the previous coefficient. -/
theorem fusionTopHyperOperator_coeff (b t y ell : ℂ) (N n : ℕ)
    (F P : PowerSeries ℂ) :
    coeff (n+2) (fusionTopHyperOperator b t y ell N F P)=
      ((n:ℂ)+2)*((n:ℂ)+2-(N:ℂ))*coeff (n+2) F-
      (((n:ℂ)+1)*((n:ℂ)+1-(N:ℂ)+t+2*ell)-fusionConstant b t y ell N)*coeff (n+1) F-
      t*coeff n P := by
  unfold fusionTopHyperOperator
  rw [map_sub,show n+2=(n+1)+1 by omega,fusionHyperOperator_coeff]
  simp only [mul_assoc,coeff_C_mul,coeff_succ_X_mul,Nat.cast_add,Nat.cast_one]
  ring

/-- The undivided residual at any stage; it is zero before resonance for
the actual normalized recursion, and becomes minus t times its source at N. -/
noncomputable def fusionTopResidual (b t y : ℂ) (N : ℕ) (q : ℕ → ℕ → ℂ)
    (n r : ℕ) : ℂ :=
  (n:ℂ)*((n:ℂ)-(N:ℂ))*q n r-t*fusionTopSum b y q n r

/-- The polynomial differential equation is exactly the second finite
difference of the full undivided recurrence, including the coupling. -/
theorem fusionTopOperator_coeff_three (b t y : ℂ) (N n r : ℕ)
    (q : ℕ → ℕ → ℂ) :
    coeff (n+3) (fusionTopOperator b t (y+(r:ℂ)) N
      (PowerSeries.mk (fun j => q j r)) (PowerSeries.mk (fusionTopPrevious q r)))=
      fusionTopResidual b t y N q (n+3) r-
        2*fusionTopResidual b t y N q (n+2) r+fusionTopResidual b t y N q (n+1) r := by
  unfold fusionTopOperator fusionTopResidual
  rw [map_sub,show n+3=(n+1)+2 by omega,fusionOperator_coeff]
  simp only [mul_assoc,coeff_C_mul,show n+1+2=(n+1+1)+1 by omega,
    coeff_succ_X_mul,sub_mul,one_mul,map_sub,coeff_mk]
  rw [show n+1+1+1=(n+2)+1 by omega,fusionTopSum_prefix,
    show n+2=(n+1)+1 by omega,fusionTopSum_prefix,fusionTopSum_prefix]
  have hh := fusionPrefix_second_difference (fusionTopPrevious q r) n
  push_cast
  linear_combination t*hh

/-- At stage zero the full polynomial differential operator vanishes. -/
theorem fusionTopOperator_coeff_zero (b t y : ℂ) (N : ℕ) (F P : PowerSeries ℂ) :
    coeff 0 (fusionTopOperator b t y N F P)=0 := by
  rw [fusionTopOperator,fusionOperator_expand]
  simp only [map_add,map_sub,mul_assoc,coeff_C_mul,coeff_zero_X_mul,
    bsaEuler_coeff,Nat.cast_zero,mul_zero,zero_mul,sub_zero,zero_add]

/-- At stage one there is no coupling to the previous coefficient. -/
theorem fusionTopOperator_coeff_one (b t y : ℂ) (N r : ℕ) (q : ℕ → ℕ → ℂ) :
    coeff 1 (fusionTopOperator b t (y+(r:ℂ)) N
      (PowerSeries.mk (fun j => q j r)) (PowerSeries.mk (fusionTopPrevious q r)))=
      fusionTopResidual b t y N q 1 r := by
  rw [fusionTopOperator,fusionOperator_expand]
  simp only [sub_mul,add_mul,mul_assoc,map_add,map_sub,coeff_C_mul,
    coeff_succ_X_mul,coeff_zero_X_mul,two_mul,bsaEuler_coeff,coeff_mk]
  norm_num [fusionTopResidual,fusionTopSum,fusionTopStep,Fin.sum_univ_one]
  ring

/-- Stage two contains the first preceding-coefficient term. Its exact
boundary residual is needed before using the uniform second differences. -/
theorem fusionTopOperator_coeff_two (b t y : ℂ) (N r : ℕ) (q : ℕ → ℕ → ℂ) :
    coeff 2 (fusionTopOperator b t (y+(r:ℂ)) N
      (PowerSeries.mk (fun j => q j r)) (PowerSeries.mk (fusionTopPrevious q r)))=
      fusionTopResidual b t y N q 2 r-2*fusionTopResidual b t y N q 1 r := by
  rw [fusionTopOperator,fusionOperator_expand]
  simp only [sub_mul,add_mul,mul_assoc,map_add,map_sub,coeff_C_mul,
    coeff_succ_X_mul,coeff_zero_X_mul,two_mul,bsaEuler_coeff,coeff_mk]
  norm_num [fusionTopResidual,fusionTopSum,fusionTopStep,fusionTopPrevious,
    Fin.sum_univ_two,Fin.sum_univ_one]
  split_ifs <;> ring


/-- If all earlier recurrence residuals vanish, the differential operator's
next coefficient is exactly the next residual, including the boundary stages. -/
theorem fusionTopOperator_first_residual (b t y : ℂ) (N n r : ℕ)
    (q : ℕ → ℕ → ℂ) (hq : ∀ j<n, fusionTopResidual b t y N q j r=0) :
    coeff n (fusionTopOperator b t (y+(r:ℂ)) N
      (PowerSeries.mk (fun j => q j r)) (PowerSeries.mk (fusionTopPrevious q r)))=
      fusionTopResidual b t y N q n r := by
  cases n with
  | zero => simp [fusionTopOperator_coeff_zero,fusionTopResidual]
  | succ n =>
    cases n with
    | zero => exact fusionTopOperator_coeff_one b t y N r q
    | succ n =>
      cases n with
      | zero =>
        rw [fusionTopOperator_coeff_two,hq 1 (by omega),mul_zero,sub_zero]
      | succ n =>
        rw [show n+1+1+1=n+3 by omega,fusionTopOperator_coeff_three,
          hq (n+2) (by omega),hq (n+1) (by omega),mul_zero,sub_zero,add_zero]

/-- The actual normalized recursion has zero residual at every
intermediate stage, for every coefficient of every input. -/
theorem fusionTopResidual_before (b t y : ℂ) (N : ℕ) (u : ℕ → ℂ) (n r : ℕ)
    (hn : n<N) :
    fusionTopResidual b t y N (fusionTopCoeff b t y N u) n r=0 := by
  unfold fusionTopResidual
  rw [fusionTopCoeff_ward b t y N n u r hn,sub_self]

/-- The full differential operator vanishes before resonance. This uses
the actual two-index recursion, so the previous-coefficient terms are included. -/
theorem fusionTopOperator_before (b t y : ℂ) (N : ℕ) (u : ℕ → ℂ) (n r : ℕ)
    (hn : n<N) :
    coeff n (fusionTopOperator b t (y+(r:ℂ)) N
      (PowerSeries.mk (fun j => fusionTopCoeff b t y N u j r))
      (PowerSeries.mk (fusionTopPrevious (fusionTopCoeff b t y N u) r)))=0 := by
  rw [fusionTopOperator_first_residual b t y N n r _
    (fun j hj => fusionTopResidual_before b t y N u j r (by omega))]
  exact fusionTopResidual_before b t y N u n r hn

/-- At resonance the undivided differential obstruction is exactly minus
t times the complete normalized source; the terminal denominator stays zero. -/
theorem fusionTopOperator_terminal (b t y : ℂ) (N : ℕ) (u : ℕ → ℂ) (r : ℕ) :
    coeff N (fusionTopOperator b t (y+(r:ℂ)) N
      (PowerSeries.mk (fun j => fusionTopCoeff b t y N u j r))
      (PowerSeries.mk (fusionTopPrevious (fusionTopCoeff b t y N u) r)))=
      -t*fusionTopSum b y (fusionTopCoeff b t y N u) N r := by
  rw [fusionTopOperator_first_residual b t y N N r _
    (fun j hj => fusionTopResidual_before b t y N u j r hj)]
  simp [fusionTopResidual]

/-- The full gauged equation also vanishes at every intermediate stage.
The binomial gauge has constant coefficient one and no resonance pole. -/
theorem fusionTopHyper_before (b t y ell : ℂ) (N : ℕ) (u : ℕ → ℂ)
    (hell : ell^2+(t-1)*ell-t*b=0) (n r : ℕ) (hn : n<N) :
    coeff n (fusionTopHyperOperator b t (y+(r:ℂ)) ell N
      (bsaGaugeSeries ell*PowerSeries.mk (fun j => fusionTopCoeff b t y N u j r))
      (bsaGaugeSeries ell*PowerSeries.mk (fusionTopPrevious (fusionTopCoeff b t y N u) r)))=0 := by
  apply bsaSeries_remove_one_sub _ n
  · rw [fusionTopOperator_gauge b t (y+(r:ℂ)) ell N hell]
    apply bsaSeries_mul_vanish
    intro j hj
    exact fusionTopOperator_before b t y N u j r (by omega)
  · rfl

/-- At resonance the gauge preserves the actual full source obstruction,
not just its diagonal contribution. This is the scalar attached to the
actual terminal PBW coordinate by the preceding module. -/
theorem fusionTopHyper_terminal (b t y ell : ℂ) (N : ℕ) (hN : 0<N) (u : ℕ → ℂ)
    (hell : ell^2+(t-1)*ell-t*b=0) (r : ℕ) :
    coeff N (fusionTopHyperOperator b t (y+(r:ℂ)) ell N
      (bsaGaugeSeries ell*PowerSeries.mk (fun j => fusionTopCoeff b t y N u j r))
      (bsaGaugeSeries ell*PowerSeries.mk (fusionTopPrevious (fusionTopCoeff b t y N u) r)))=
      -t*fusionTopSum b y (fusionTopCoeff b t y N u) N r := by
  have hh := congrArg (coeff N) (fusionTopOperator_gauge b t (y+(r:ℂ)) ell N hell
    (PowerSeries.mk (fun j => fusionTopCoeff b t y N u j r))
    (PowerSeries.mk (fusionTopPrevious (fusionTopCoeff b t y N u) r)))
  rw [fusion_mul_first_coefficient _ _ N (fun j hj => fusionTopOperator_before b t y N u j r hj),
    fusionTopOperator_terminal b t y N u r] at hh
  have hg : coeff 0 (bsaGaugeSeries ell)=1 := by simp [bsaGaugeSeries,bsaGaugeCoefficient]
  rw [hg,one_mul] at hh
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N≠0)
  rw [sub_mul,one_mul,map_sub,coeff_succ_X_mul,
    fusionTopHyper_before b t y ell (n+1) u hell n r (by omega),sub_zero] at hh
  exact hh

end VOA.InverseDS.VirasoroVerma
