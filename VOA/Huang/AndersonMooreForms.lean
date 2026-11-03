/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion

/-!
# Galois action on level-one modular forms through `q`-expansions

For every ring endomorphism `σ : ℂ →+* ℂ` (no continuity assumed) and every level-one modular
form `F` of weight `k`, the power series obtained by applying `σ` to the coefficients of the
`q`-expansion of `F` is again the `q`-expansion of a level-one modular form of weight `k`.

## Route (Serre's induction)

* `E₄`, `E₆` have rational `q`-coefficients (`EisensteinSeries.E_qExpansion_coeff`: Bernoulli
  numbers and divisor sums), so their `q`-expansions are fixed by `σ`; hence so is that of
  `Δ = (E₄³ − E₆²)/1728`.
* Strong induction on the weight: negative, odd and weight-two forms vanish; weight-zero forms are
  constant; for even `k ≥ 4` subtract `c · M` with `M = E₄ᵃE₆ᵇ` of constant term `1`, divide the
  resulting cusp form by `Δ` (`CuspForm.discriminantEquiv`), and recurse at weight `k − 12`.

## Main results

* `qExpansion_E4_map`, `qExpansion_E6_map`, `qExpansion_discriminant_map` — the `q`-expansions
  of `E₄`, `E₆`, `Δ` are fixed by every ring endomorphism of `ℂ`;
* `exists_modularForm_qExpansion_map` — the Galois action on level-one modular forms.
-/

namespace VOA.Huang.AndersonMoore

open UpperHalfPlane ModularForm ModularFormClass EisensteinSeries
open scoped MatrixGroups

/-- The `q`-expansion of a normalised Eisenstein series of even weight `k ≥ 4` is fixed by
every ring endomorphism of `ℂ` (its coefficients are rational). -/
theorem qExpansion_E_map (σ : ℂ →+* ℂ) {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k) :
    PowerSeries.map σ (qExpansion 1 (ModularForm.E hk)) = qExpansion 1 (ModularForm.E hk) := by
  ext m
  rw [PowerSeries.coeff_map, E_qExpansion_coeff hk hk2 m]
  split_ifs
  · exact map_one σ
  · simp [map_ratCast, map_ofNat]

theorem qExpansion_E4_map (σ : ℂ →+* ℂ) :
    PowerSeries.map σ (qExpansion 1 ModularForm.E₄) = qExpansion 1 ModularForm.E₄ :=
  qExpansion_E_map σ _ ⟨2, rfl⟩

theorem qExpansion_E6_map (σ : ℂ →+* ℂ) :
    PowerSeries.map σ (qExpansion 1 ModularForm.E₆) = qExpansion 1 ModularForm.E₆ :=
  qExpansion_E_map σ _ ⟨3, rfl⟩

/-- `E₄³ − E₆²` as a level-one modular form of weight `12`. -/
noncomputable def E4CubeSubE6Sq : ModularForm 𝒮ℒ 12 :=
  ModularForm.mcast (by decide) (E₄.pow 3) - ModularForm.mcast (by decide) (E₆.pow 2)

/-- `q`-expansion of `Δ` in terms of those of `E₄`, `E₆`. -/
theorem qExpansion_discriminant_eq :
    qExpansion 1 ModularForm.discriminant
      = (1728 : ℂ)⁻¹ • (qExpansion 1 ModularForm.E₄ ^ 3 - qExpansion 1 ModularForm.E₆ ^ 2) := by
  have hfun : (ModularForm.discriminant : ℍ → ℂ)
      = (1728 : ℂ)⁻¹ • ⇑E4CubeSubE6Sq := by
    funext z
    rw [ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq z]
    simp only [E4CubeSubE6Sq, Pi.smul_apply, coe_sub, coe_mcast, coe_pow, Pi.sub_apply,
      Pi.pow_apply,
      smul_eq_mul]
    ring
  rw [hfun,
    ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL, E4CubeSubE6Sq, coe_sub,
    ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL,
    ModularForm.qExpansion_mcast, ModularForm.qExpansion_mcast,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]

theorem qExpansion_discriminant_map (σ : ℂ →+* ℂ) :
    PowerSeries.map σ (qExpansion 1 ModularForm.discriminant)
      = qExpansion 1 ModularForm.discriminant := by
  rw [qExpansion_discriminant_eq, PowerSeries.smul_eq_C_mul, map_mul, map_sub, map_pow, map_pow,
    qExpansion_E4_map, qExpansion_E6_map, PowerSeries.map_C]
  congr 2
  rw [map_inv₀, map_ofNat]

/-! ## Monomials of constant term `1` with `σ`-fixed `q`-expansion -/

theorem coeff_zero_qExpansion_mul {a b : ℤ} (f : ModularForm 𝒮ℒ a) (g : ModularForm 𝒮ℒ b) :
    (qExpansion 1 (f.mul g)).coeff 0 = (qExpansion 1 f).coeff 0 * (qExpansion 1 g).coeff 0 := by
  rw [ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL, PowerSeries.coeff_mul,
    Finset.Nat.antidiagonal_zero, Finset.sum_singleton]

/-- For every even `k ≥ 4` there is a level-one form of weight `k` (a monomial `E₄ᵃE₆ᵇ`) whose
`q`-expansion has constant term `1` and is fixed by every ring endomorphism of `ℂ`. -/
theorem exists_unit_form_qExpansion_fixed : ∀ k : ℕ, Even k → 4 ≤ k →
    ∃ M : ModularForm 𝒮ℒ (k : ℤ), (qExpansion 1 M).coeff 0 = 1 ∧
      ∀ σ : ℂ →+* ℂ, PowerSeries.map σ (qExpansion 1 M) = qExpansion 1 M := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk h4
    rcases eq_or_lt_of_le h4 with h | h4'
    · refine ⟨ModularForm.mcast (show (4 : ℤ) = (k : ℤ) from by omega) ModularForm.E₄, ?_, ?_⟩
      · rw [ModularForm.qExpansion_mcast]; exact E_qExpansion_coeff_zero _ ⟨2, rfl⟩
      · intro σ; rw [ModularForm.qExpansion_mcast]; exact qExpansion_E4_map σ
    rcases eq_or_lt_of_le (show 6 ≤ k by rcases hk with ⟨m, rfl⟩; omega) with h6 | h6'
    · refine ⟨ModularForm.mcast (show (6 : ℤ) = (k : ℤ) from by omega) ModularForm.E₆, ?_, ?_⟩
      · rw [ModularForm.qExpansion_mcast]; exact E_qExpansion_coeff_zero _ ⟨3, rfl⟩
      · intro σ; rw [ModularForm.qExpansion_mcast]; exact qExpansion_E6_map σ
    · have hk8 : 8 ≤ k := by rcases hk with ⟨m, rfl⟩; omega
      obtain ⟨G, hG0, hGσ⟩ := ih (k - 4) (by omega) (by
        rcases hk with ⟨m, rfl⟩; exact ⟨m - 2, by omega⟩) (by omega)
      refine ⟨ModularForm.mcast (show (4 : ℤ) + ((k - 4 : ℕ) : ℤ) = (k : ℤ) from by
        push_cast [Nat.cast_sub (by omega : 4 ≤ k)]; ring) (ModularForm.E₄.mul G), ?_, ?_⟩
      · rw [ModularForm.qExpansion_mcast, coeff_zero_qExpansion_mul, hG0,
          E_qExpansion_coeff_zero _ ⟨2, rfl⟩, one_mul]
      · intro σ
        rw [ModularForm.qExpansion_mcast,
          ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL, map_mul,
          qExpansion_E4_map, hGσ]

/-! ## The Galois action -/

theorem analyticAt_cuspFunction_one {w : ℤ} (f : ModularForm 𝒮ℒ w) :
    AnalyticAt ℂ (cuspFunction 1 (⇑f : ℍ → ℂ)) 0 :=
  ModularFormClass.analyticAt_cuspFunction_zero f one_pos one_mem_strictPeriods_SL

theorem analyticAt_cuspFunction_one_smul {w : ℤ} (f : ModularForm 𝒮ℒ w) (a : ℂ) :
    AnalyticAt ℂ (cuspFunction 1 (a • (⇑f : ℍ → ℂ))) 0 := by
  rw [cuspFunction_smul (analyticAt_cuspFunction_one f).continuousAt]
  exact (analyticAt_cuspFunction_one f).const_smul

theorem qExpansion_smul_one (a : ℂ) :
    qExpansion 1 ⇑(a • (1 : ModularForm 𝒮ℒ 0)) = PowerSeries.C a := by
  rw [show (⇑(a • (1 : ModularForm 𝒮ℒ 0)) : ℍ → ℂ) = a • ⇑(1 : ModularForm 𝒮ℒ 0) from rfl,
    ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL, ModularForm.qExpansion_one,
    PowerSeries.smul_eq_C_mul, mul_one]

/-- **Galois action on level-one modular forms.**  For every ring endomorphism `σ` of `ℂ`
(not necessarily continuous) and every level-one modular form `F` of weight `k`, applying `σ`
to the `q`-expansion coefficients of `F` yields the `q`-expansion of a level-one modular form of
the same weight. -/
theorem exists_modularForm_qExpansion_map (σ : ℂ →+* ℂ) (k : ℤ) (F : ModularForm 𝒮ℒ k) :
    ∃ G : ModularForm 𝒮ℒ k, qExpansion 1 G = PowerSeries.map σ (qExpansion 1 F) := by
  induction hn : k.toNat using Nat.strong_induction_on generalizing k with
  | _ n ih =>
    rcases lt_or_ge k 0 with hneg | hpos
    · refine ⟨0, ?_⟩
      rw [ModularFormClass.levelOne_neg_weight_eq_zero hneg F, ModularForm.coe_zero,
        qExpansion_zero, map_zero]
    rcases Int.even_or_odd k with hev | hodd
    swap
    · refine ⟨0, ?_⟩
      rw [ModularForm.levelOne_odd_weight_eq_zero hodd F, ModularForm.coe_zero,
        qExpansion_zero, map_zero]
    rcases lt_or_ge k 4 with hsmall | hbig
    · interval_cases k
      · obtain ⟨c, hc⟩ := ModularFormClass.levelOne_weight_zero_const F
        have hF : (⇑F : ℍ → ℂ) = ⇑(c • (1 : ModularForm 𝒮ℒ 0)) := by
          rw [hc]; funext z; simp
        refine ⟨σ c • (1 : ModularForm 𝒮ℒ 0), ?_⟩
        rw [hF, qExpansion_smul_one, qExpansion_smul_one, PowerSeries.map_C]
      · exact absurd hev (by decide)
      · have : Subsingleton (ModularForm 𝒮ℒ 2) := by
          rw [← rank_zero_iff (R := ℂ)]
          exact ModularForm.levelOne_weight_two_rank_zero
        refine ⟨0, ?_⟩
        rw [Subsingleton.elim F 0, ModularForm.coe_zero, qExpansion_zero, map_zero]
      · exact absurd hev (by decide)
    -- the main case: `k` even, `k ≥ 4`
    obtain ⟨M0, hM00, hM0σ⟩ := exists_unit_form_qExpansion_fixed k.toNat
      (by rcases hev with ⟨m, hm⟩; exact ⟨m.toNat, by omega⟩) (by omega)
    have hcast : ((k.toNat : ℕ) : ℤ) = k := by omega
    set M : ModularForm 𝒮ℒ k := ModularForm.mcast hcast M0 with hMdef
    have hM0 : (qExpansion 1 M).coeff 0 = 1 := hM00
    have hMσ : PowerSeries.map σ (qExpansion 1 M) = qExpansion 1 M := hM0σ σ
    set c : ℂ := (qExpansion 1 F).coeff 0 with hc
    have hcoeff : (qExpansion 1 (F - c • M)).coeff 0 = 0 := by
      rw [qExpansion_sub (analyticAt_cuspFunction_one F) (analyticAt_cuspFunction_one_smul M c),
        qExpansion_smul (analyticAt_cuspFunction_one M), map_sub, PowerSeries.coeff_smul, hM0,
        smul_eq_mul, mul_one, ← hc, sub_self]
    set F' : ModularForm 𝒮ℒ (k - 12) :=
      CuspForm.discriminantEquiv (ModularForm.toCuspForm (F - c • M) hcoeff) with hF'
    obtain ⟨G', hG'⟩ := ih (k - 12).toNat (by omega) (k - 12) F' rfl
    have hsplitF : qExpansion 1 F
        = c • qExpansion 1 M + qExpansion 1 ModularForm.discriminant * qExpansion 1 F' := by
      rw [← ModularForm.qExpansion_eq_qExpansion_discriminant_mul (F - c • M) hcoeff,
        show (⇑(F - c • M) : ℍ → ℂ) = ⇑F - c • ⇑M from rfl,
        qExpansion_sub (analyticAt_cuspFunction_one F) (analyticAt_cuspFunction_one_smul M c),
        qExpansion_smul (analyticAt_cuspFunction_one M)]
      abel
    refine ⟨σ c • M + ((CuspForm.ofMulDiscriminant G' : CuspForm 𝒮ℒ k) : ModularForm 𝒮ℒ k), ?_⟩
    have hcusp : (⇑(σ c • M + ((CuspForm.ofMulDiscriminant G' : CuspForm 𝒮ℒ k) :
        ModularForm 𝒮ℒ k)) : ℍ → ℂ) = σ c • ⇑M + ⇑CuspForm.discriminant * ⇑G' := rfl
    have hAΔ : AnalyticAt ℂ (cuspFunction 1 (⇑CuspForm.discriminant * ⇑G' : ℍ → ℂ)) 0 :=
      analyticAt_cuspFunction_one
        ((CuspForm.ofMulDiscriminant G' : CuspForm 𝒮ℒ k) : ModularForm 𝒮ℒ k)
    rw [hcusp, qExpansion_add (analyticAt_cuspFunction_one_smul M (σ c)) hAΔ,
      qExpansion_smul (analyticAt_cuspFunction_one M),
      ModularForm.qExpansion_mul_coe one_pos one_mem_strictPeriods_SL, hG', hsplitF, map_add,
      PowerSeries.smul_eq_C_mul, PowerSeries.smul_eq_C_mul, map_mul, map_mul, PowerSeries.map_C,
      hMσ, CuspForm.coe_discriminant, qExpansion_discriminant_map]

end VOA.Huang.AndersonMoore
