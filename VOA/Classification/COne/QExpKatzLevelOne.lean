/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.QExpKatzAlgebra
import VOA.Huang.AndersonMooreForms

/-!
# Bounded coefficients at level one, unconditionally

Every complex level-one modular form has coefficients in a finite integer module.
The proof uses Mathlib's explicit Eisenstein coefficients and division of a cusp
form by the discriminant, decreasing the weight by 12. Unlike coefficientwise
Galois invariance, this really proves bounded denominators.

This discharges the level-one coefficient step in the Cramer-frame route. It
does not construct a frame at general level, nor prove its leading coefficient
is a unit. No arithmetic q-expansion principle is assumed.
-/

open UpperHalfPlane ModularForm ModularFormClass EisensteinSeries
open VOA.Huang.AndersonMoore
open scoped MatrixGroups Pointwise

noncomputable section

namespace VOA.Classification.COne.SSHecke

/-- A power series whose coefficients lie in one finite integer module. -/
def HasFiniteCoeffLattice (f : PowerSeries ℂ) : Prop :=
  ∃ L : Submodule ℤ ℂ, L.FG ∧ ∀ n, PowerSeries.coeff n f ∈ L

theorem HasFiniteCoeffLattice.zero : HasFiniteCoeffLattice 0 :=
  ⟨⊥, Submodule.fg_bot, by simp⟩

theorem HasFiniteCoeffLattice.C (c : ℂ) : HasFiniteCoeffLattice (PowerSeries.C c) := by
  refine ⟨Submodule.span ℤ {c}, Submodule.fg_span_singleton c, fun n => ?_⟩
  rw [PowerSeries.coeff_C]
  split_ifs
  · exact Submodule.subset_span rfl
  · exact Submodule.zero_mem _

theorem HasFiniteCoeffLattice.add {f g : PowerSeries ℂ}
    (hf : HasFiniteCoeffLattice f) (hg : HasFiniteCoeffLattice g) :
    HasFiniteCoeffLattice (f + g) := by
  obtain ⟨L, hL, hf⟩ := hf
  obtain ⟨K, hK, hg⟩ := hg
  refine ⟨L ⊔ K, hL.sup hK, fun n => ?_⟩
  rw [map_add]
  exact Submodule.add_mem _ (Submodule.mem_sup_left (hf n))
    (Submodule.mem_sup_right (hg n))

theorem HasFiniteCoeffLattice.smul (c : ℂ) {f : PowerSeries ℂ}
    (hf : HasFiniteCoeffLattice f) : HasFiniteCoeffLattice (c • f) := by
  obtain ⟨L, hL, hf⟩ := hf
  refine ⟨L.map (LinearMap.mulLeft ℤ c), hL.map _, fun n => ?_⟩
  rw [PowerSeries.coeff_smul]
  exact Submodule.mem_map_of_mem (hf n)

theorem HasFiniteCoeffLattice.sub {f g : PowerSeries ℂ}
    (hf : HasFiniteCoeffLattice f) (hg : HasFiniteCoeffLattice g) :
    HasFiniteCoeffLattice (f - g) := by
  simpa only [neg_one_smul, sub_eq_add_neg] using hf.add (hg.smul (-1))

theorem HasFiniteCoeffLattice.mul {f g : PowerSeries ℂ}
    (hf : HasFiniteCoeffLattice f) (hg : HasFiniteCoeffLattice g) :
    HasFiniteCoeffLattice (f * g) := by
  obtain ⟨L, hL, hf⟩ := hf
  obtain ⟨K, hK, hg⟩ := hg
  refine ⟨L * K, hL.mul hK, fun n => ?_⟩
  rw [PowerSeries.coeff_mul]
  exact Submodule.sum_mem _ fun x _ => Submodule.mul_mem_mul (hf x.1) (hg x.2)

theorem HasFiniteCoeffLattice.pow {f : PowerSeries ℂ}
    (hf : HasFiniteCoeffLattice f) (n : ℕ) : HasFiniteCoeffLattice (f ^ n) := by
  induction n with
  | zero => simpa using HasFiniteCoeffLattice.C 1
  | succ n ih => simpa only [pow_succ] using ih.mul hf

/-- The explicit divisor-sum formula bounds all coefficients of a fixed Eisenstein series. -/
theorem eisenstein_hasFiniteCoeffLattice {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k) :
    HasFiniteCoeffLattice (qExpansion 1 (ModularForm.E hk)) := by
  let β : ℂ := -(2 * k / bernoulli k : ℂ)
  let L := Submodule.span ℤ ({1, β} : Set ℂ)
  refine ⟨L, Submodule.fg_span (Set.toFinite _), fun n => ?_⟩
  rw [E_qExpansion_coeff hk hk2]
  split_ifs
  · exact Submodule.subset_span (by simp)
  · change β * _ ∈ L
    rw [mul_comm]
    have h := L.smul_mem ((ArithmeticFunction.sigma (k - 1) n : ℕ) : ℤ)
      (Submodule.subset_span (show β ∈ ({1, β} : Set ℂ) by simp))
    simpa only [zsmul_eq_mul, Int.cast_natCast] using h

theorem discriminant_hasFiniteCoeffLattice :
    HasFiniteCoeffLattice (qExpansion 1 ModularForm.discriminant) := by
  rw [qExpansion_discriminant_eq]
  exact (((eisenstein_hasFiniteCoeffLattice (k := 4) (by omega) ⟨2, rfl⟩).pow 3).sub
    ((eisenstein_hasFiniteCoeffLattice (k := 6) (by omega) ⟨3, rfl⟩).pow 2)).smul _

/-- Unconditional bounded coefficients for all weights at level one. -/
theorem levelOne_hasFiniteCoeffLattice (k : ℤ) (F : ModularForm 𝒮ℒ k) :
    HasFiniteCoeffLattice (qExpansion 1 F) := by
  induction hn : k.toNat using Nat.strong_induction_on generalizing k with
  | _ n ih =>
    rcases lt_or_ge k 0 with hneg | hpos
    · simp only [ModularFormClass.levelOne_neg_weight_eq_zero hneg F, qExpansion_zero]
      exact HasFiniteCoeffLattice.zero
    rcases Int.even_or_odd k with hev | hodd
    swap
    · simp only [ModularForm.levelOne_odd_weight_eq_zero hodd F,
        ModularForm.coe_zero, qExpansion_zero]
      exact HasFiniteCoeffLattice.zero
    rcases lt_or_ge k 4 with hsmall | hbig
    · interval_cases k
      · obtain ⟨c, hc⟩ := ModularFormClass.levelOne_weight_zero_const F
        have hF : (⇑F : ℍ → ℂ) = ⇑(c • (1 : ModularForm 𝒮ℒ 0)) := by
          rw [hc]; funext z; simp
        rw [hF, qExpansion_smul_one]
        exact HasFiniteCoeffLattice.C c
      · exact absurd hev (by decide)
      · have : Subsingleton (ModularForm 𝒮ℒ 2) := by
          rw [← rank_zero_iff (R := ℂ)]
          exact ModularForm.levelOne_weight_two_rank_zero
        rw [Subsingleton.elim F 0, ModularForm.coe_zero, qExpansion_zero]
        exact HasFiniteCoeffLattice.zero
      · exact absurd hev (by decide)
    have hk : 3 ≤ k.toNat := by omega
    have hke : Even k.toNat := by
      rcases hev with ⟨m, hm⟩
      exact ⟨m.toNat, by omega⟩
    let M : ModularForm 𝒮ℒ k := ModularForm.mcast (by omega) (ModularForm.E hk)
    have hM0 : (qExpansion 1 M).coeff 0 = 1 := E_qExpansion_coeff_zero hk hke
    have hMb : HasFiniteCoeffLattice (qExpansion 1 M) :=
      eisenstein_hasFiniteCoeffLattice hk hke
    let c := (qExpansion 1 F).coeff 0
    have hcoeff : (qExpansion 1 (F - c • M)).coeff 0 = 0 := by
      rw [qExpansion_sub (analyticAt_cuspFunction_one F)
          (analyticAt_cuspFunction_one_smul M c),
        qExpansion_smul (analyticAt_cuspFunction_one M), map_sub,
        PowerSeries.coeff_smul, hM0, smul_eq_mul, mul_one]
      exact sub_self c
    let F' : ModularForm 𝒮ℒ (k - 12) :=
      CuspForm.discriminantEquiv (ModularForm.toCuspForm (F - c • M) hcoeff)
    have hF' := ih (k - 12).toNat (by omega) (k - 12) F' rfl
    have hsplit : qExpansion 1 F = c • qExpansion 1 M +
        qExpansion 1 ModularForm.discriminant * qExpansion 1 F' := by
      rw [← ModularForm.qExpansion_eq_qExpansion_discriminant_mul (F - c • M) hcoeff,
        show (⇑(F - c • M) : ℍ → ℂ) = ⇑F - c • ⇑M from rfl,
        qExpansion_sub (analyticAt_cuspFunction_one F)
          (analyticAt_cuspFunction_one_smul M c),
        qExpansion_smul (analyticAt_cuspFunction_one M)]
      abel
    rw [hsplit]
    exact (hMb.smul c).add (discriminant_hasFiniteCoeffLattice.mul hF')

end VOA.Classification.COne.SSHecke
