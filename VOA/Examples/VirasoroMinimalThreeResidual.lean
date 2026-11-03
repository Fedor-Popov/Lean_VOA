/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroMinimalThreeNormEquation

/-!
# Nonvanishing of the actual q=3 scalar Ward residual

Formal substitution and multiplication by units preserve a finite initial
zero segment. The quadratic pullback is invertible at zero. Consequently a
vanishing actual terminal residual would contradict the finite hypergeometric
resonance. This scalar residual is not yet identified with the singular
norm derivative; that separate comparison is not assumed here.
-/
namespace VOA.InverseDS.VirasoroVerma
open VirModule PowerSeries

/-- Substitution by a series with zero constant term leaves the input's
constant coefficient unchanged. Only its constant and X-divisible parts
are needed for this identity. -/
theorem minimalThree_subst_constant (F P : PowerSeries ℂ)
    (hP : PowerSeries.constantCoeff P=0) :
    PowerSeries.constantCoeff (F.subst P)=PowerSeries.constantCoeff F := by
  have hs := HasSubst.of_constantCoeff_zero' hP
  conv_lhs => rw [eq_X_mul_shift_add_const F]
  simp only [PowerSeries.subst_add hs,PowerSeries.subst_mul hs,subst_X hs,subst_C,
    map_add,map_mul,hP,zero_mul,zero_add]
  rfl

/-- Formal substitution preserves divisibility by X to every finite power
when the substituted series has zero constant term. -/
theorem minimalThree_subst_dvd (F P : PowerSeries ℂ)
    (hP : PowerSeries.constantCoeff P=0) (n : ℕ) (hF : (X:PowerSeries ℂ)^n∣F) :
    (X:PowerSeries ℂ)^n∣F.subst P := by
  have hs := HasSubst.of_constantCoeff_zero' hP
  obtain ⟨G,hG⟩ := hF
  rw [hG,PowerSeries.subst_mul hs,PowerSeries.subst_pow hs,subst_X hs]
  exact dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd (X_dvd_iff.mpr hP) n) _

/-- A unit can be removed from a divisibility assertion. This is used for
the binomial gauge and for the factor 1-2X in the pullback. -/
theorem minimalThree_remove_unit (A B : PowerSeries ℂ) (n : ℕ)
    (hA : IsUnit A) (h : (X:PowerSeries ℂ)^n∣A*B) : (X:PowerSeries ℂ)^n∣B := by
  obtain ⟨u,rfl⟩ := hA
  obtain ⟨G,hG⟩ := h
  refine ⟨(↑(u⁻¹):PowerSeries ℂ)*G,?_⟩
  calc
    B=(↑(u⁻¹):PowerSeries ℂ)*((↑u:PowerSeries ℂ)*B) := by simp
    _=(X:PowerSeries ℂ)^n*((↑(u⁻¹):PowerSeries ℂ)*G) := by rw [hG]; ring

/-- The quadratic map has invertible linear coefficient four. Its formal
inverse therefore exists independently of any hypergeometric solution. -/
theorem minimalThreeQuadratic_linear_unit : IsUnit (coeff 1 minimalThreeQuadratic) := by
  have he : coeff 1 minimalThreeQuadratic=(4:ℂ) := by
    rw [minimalThreeQuadratic,show (4:PowerSeries ℂ)=PowerSeries.C (4:ℂ) by rfl]
    simp [mul_assoc,coeff_C_mul]
  rw [he]
  exact isUnit_iff_ne_zero.mpr (by norm_num)

/-- Every formal series can be written in the pullback coordinates.
The gauge has constant one and the quadratic map has nonzero linear part,
so this assertion requires no differential equation. -/
theorem minimalThree_exists_pullback (a : ℂ) (F : PowerSeries ℂ) :
    ∃ G : PowerSeries ℂ, F=bsaGaugeSeries (2*a)*G.subst minimalThreeQuadratic := by
  have hb : IsUnit (bsaGaugeSeries (2*a)) := by
    apply isUnit_iff_constantCoeff.mpr
    have he : PowerSeries.constantCoeff (bsaGaugeSeries (2*a))=1 := by
      rw [← coeff_zero_eq_constantCoeff_apply]
      simp [bsaGaugeSeries,bsaGaugeCoefficient]
    rw [he]
    exact isUnit_one
  obtain ⟨u,hu⟩ := hb
  let P := minimalThreeQuadratic
  let Q := P.substInvOfIsUnit minimalThreeQuadratic_linear_unit
  have hP : PowerSeries.constantCoeff P=0 := by simp [P,minimalThreeQuadratic]
  have hQ : HasSubst Q := HasSubst.substInvOfIsUnit _ _
  refine ⟨((↑(u⁻¹):PowerSeries ℂ)*F).subst Q,?_⟩
  rw [subst_comp_subst_apply hQ minimalThreeQuadratic_hasSubst,
    subst_substInvOfIsUnit_left P hP minimalThreeQuadratic_linear_unit,X_subst,← hu]
  simp

/-- The cleared norm equation has no normalized formal solution through
the minimal-model resonance. This transfers the finite obstruction through
the proved formal gauge and quadratic substitution. -/
theorem minimalThreeNormOperator_resonance (p : ℕ) (hp : 2≤p) (hcop : Nat.Coprime p 3)
    (F : PowerSeries ℂ) (h0 : coeff 0 F=1)
    (hF : ∀ n, n≤(p-1)*2 → coeff n (minimalThreeNormOperator (2*(p:ℂ)/3-1) F)=0) : False := by
  let a : ℂ := 2*(p:ℂ)/3-1
  obtain ⟨G,hG⟩ := minimalThree_exists_pullback a F
  have hP : PowerSeries.constantCoeff minimalThreeQuadratic=0 := by
    simp [minimalThreeQuadratic]
  have hB : PowerSeries.constantCoeff (bsaGaugeSeries (2*a))=1 := by
    rw [← coeff_zero_eq_constantCoeff_apply]
    simp [bsaGaugeSeries,bsaGaugeCoefficient]
  have hG0 : coeff 0 G=1 := by
    rw [coeff_zero_eq_constantCoeff_apply] at h0 ⊢
    rw [hG,map_mul,hB,one_mul,minimalThree_subst_constant _ _ hP] at h0
    exact h0
  apply minimalThreeHyper_resonance p hp hcop G hG0
  have hd : (X:PowerSeries ℂ)^((p-1)*2+1)∣minimalThreeNormOperator a F :=
    X_pow_dvd_iff.mpr (fun n hn => hF n (by omega))
  rw [hG,minimalThreeNormOperator_pullback] at hd
  have hunit : IsUnit (bsaGaugeSeries (2*a)*(1-2*X)) := by
    apply isUnit_iff_constantCoeff.mpr
    simpa [hB] using (isUnit_one : IsUnit (1:ℂ))
  have hd' := minimalThree_remove_unit _ _ _ hunit hd
  let Q := minimalThreeQuadratic.substInvOfIsUnit minimalThreeQuadratic_linear_unit
  have hQ0 : PowerSeries.constantCoeff Q=0 := constantCoeff_substInvOfIsUnit _ _
  have hQ : HasSubst Q := HasSubst.substInvOfIsUnit _ _
  have hfinal := minimalThree_subst_dvd _ Q hQ0 _ hd'
  rw [subst_comp_subst_apply minimalThreeQuadratic_hasSubst hQ,
    subst_substInvOfIsUnit_right minimalThreeQuadratic hP minimalThreeQuadratic_linear_unit,
    X_subst] at hfinal
  intro n hn
  exact X_pow_dvd_iff.mp hfinal n (by omega)

/-- The actual intermediate canonical norms have a NONZERO undivided
terminal Ward residual for every coprime M(p,3), p at least two. This is
not yet a norm-derivative theorem: the separate comparison is still needed. -/
theorem minimalThreeNormResidual_ne_zero (p : ℕ) (hp : 2≤p) (hcop : Nat.Coprime p 3) :
    minimalThreeNormResidual p≠0 := by
  intro hz
  apply minimalThreeNormOperator_resonance p hp hcop
    (PowerSeries.mk (minimalThreeNormCoefficient p))
  · simp [minimalThreeNormCoefficient]
  · intro n hn
    rw [← minimalThree_field_weight p hp]
    exact minimalThreeNormOperator_vanish_through p hp hcop hz n hn

end VOA.InverseDS.VirasoroVerma
