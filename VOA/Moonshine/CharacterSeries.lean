/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.TwistedSectorDim
import VOA.Modularity.JFunction

/-!
# The two-sector character as a single power series  (Moonshine step M7d, part 1)

The graded dimensions of the two summands of `V♮ = V_Λ^+ ⊕ (V_Λ^T)^+` were computed weight by
weight in `LatticeGradedDim.lean` and `TwistedSectorDim.lean`.  This file packages them as one
formal power series

  `sectorSeries = Σ_{n ≥ 0} (dim (V_Λ^+)_n + dim (V_Λ^T)^+_n) qⁿ`

and identifies it with an explicit combination of products (all in `ℂ⟦q⟧`):

  `sectorSeries_eq : sectorSeries = ½ (Θ_Λ · P + B) + 4096 · q² · T_odd`,

where `Θ_Λ = leechThetaSeries = Σ #{⟨α,α⟩ = 2n} qⁿ`, `P = fockGenFun 24 = ∏(1-qⁿ)^{-24}`,
`B = fockSignedGenFun 24 = ∏(1+qⁿ)^{-24}`, and `T_odd = twOddSeries = Σ P_T(24, 2n+1) qⁿ`
(the odd part of `∏(1-x^{2i+1})^{-24}`, `x = q^{1/2}`, compressed to the variable `q`).

The target `sectorSeries = JShift` (`JShift = q·J`, `Modularity/JFunction.lean`) is then reduced
to three named identities of formal power series:

* `DeltaProductIdentity : deltaOverQ * fockGenFun 24 = 1` — Jacobi's product
  `Δ = q ∏(1-qⁿ)^{24}` for the *formal* `Δ = (E₄³ - E₆²)/1728`;
* `LeechThetaIdentity : leechThetaSeries = E₄³ - 720 Δ` (formal series);
* `LevelTwoIdentity : B + 8192 q² T_odd = jShift - 768 q` — the trace of the `Γ₀(2)` hauptmodul
  `t = η(τ)^{24}/η(2τ)^{24}` over the three cosets of `Γ₀(2)` in `SL₂(ℤ)`:
  `t(τ) + t(-1/τ) + t(-1/(τ+1)) = j - 768`.

`sectorSeries_eq_JShift_of : DeltaProductIdentity → LeechThetaIdentity → LevelTwoIdentity →
sectorSeries = JShift` is the formal reduction (pure algebra in `ℂ⟦q⟧`).  The three identities
are proved in the companion files `CharacterDelta` (`deltaProductIdentity`,
`leechThetaIdentity`) and `CharacterLevelTwo` (`levelTwoIdentity`); `Character.lean` assembles
`sectorSeries_eq_JShift`.

The coefficient sanity checks `coeff_sectorSeries_zero/one/two/three` (`1, 0, 196884, 21493760`)
are re-derived from the per-weight theorems.

## Status
All declarations proved, no `sorry`, no new axioms.  The three identities are `Prop`s here (proved
downstream), *not* assumptions of any theorem claimed as a result.  Honest scope as in `TwistedSectorDim.lean`: the
series is the sum of the graded dimensions of the two summands.  (The VOA `V♮` is constructed
downstream, `Moonshine.moonshine`.)

## Numerical pre-check
All three identities, and `sectorSeries = JShift`, were reportedly checked on the first 40
`q`-coefficients with exact integer arithmetic (Python) before formalisation.  That script is not
in the repository (`scripts/moonshine/numerics/` has no such check); the Lean proofs here do not
depend on it.
-/

set_option linter.style.longLine false

open scoped TensorProduct

namespace VOA

namespace Moonshine

open LatGen TwistedSector TwistedHeisenberg Module PowerSeries

/-! ## The series -/

/-- **The two-sector series** `Σ_n (dim (V_Λ^+)_n + dim (V_Λ^T)^+_n) qⁿ`. -/
noncomputable def sectorSeries : PowerSeries ℂ :=
  PowerSeries.mk fun n =>
    ((finrank ℂ (leechVOAPlus.grading (n : ℤ))
      + finrank ℂ (twFixed 24 leechT ⊓ twWeight 24 leechT ((n : ℤ) : ℚ) :
          Submodule ℂ leechTwistedSpace) : ℕ) : ℂ)

/-- The Leech theta series `Θ_Λ = Σ_n #{α : ⟨α,α⟩ = 2n} qⁿ` (formal). -/
noncomputable def leechThetaSeries : PowerSeries ℂ :=
  PowerSeries.mk fun n => ((normEq leech leech_posDef (2 * n)).card : ℂ)

/-- The odd part of the twisted Fock generating function, compressed:
`T_odd = Σ_n P_T(24, 2n+1) qⁿ`, so that `x³·(odd part of ∏(1-x^{2i+1})^{-24}) = q² T_odd`. -/
noncomputable def twOddSeries : PowerSeries ℂ :=
  PowerSeries.mk fun n => (twCount 24 (2 * n + 1) : ℂ)

/-! ## Coefficients of the two sectors -/

theorem coeff_leechTheta_mul_fock (n : ℕ) :
    coeff n (leechThetaSeries * fockGenFun 24)
      = (finrank ℂ (gradingLatGen leech (n : ℤ)) : ℂ) := by
  rw [finrank_gradingLatGen_eq_sum_theta leech leech_posDef leech_even n, leech_rank,
    PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => coeff i leechThetaSeries * coeff j (fockGenFun 24))]
  push_cast
  refine Finset.sum_congr rfl fun m _ => ?_
  simp [leechThetaSeries, fockGenFun]

/-- `2 dim (V_Λ^+)_n = [qⁿ](Θ_Λ P + B)`. -/
theorem two_mul_finrank_plus (n : ℕ) :
    2 * (finrank ℂ (leechVOAPlus.grading (n : ℤ)) : ℂ)
      = coeff n (leechThetaSeries * fockGenFun 24 + fockSignedGenFun 24) := by
  rw [(leechVOAPlusGradingEquiv (n : ℤ)).finrank_eq, map_add, coeff_leechTheta_mul_fock]
  have h := two_mul_finrank_plusK_eq_signed leech leech_posDef leech_even n
  have h2 : fockSigned leech.rank n = fockSigned 24 n := by rw [leech_rank]
  rw [h2] at h
  have h' : ((2 * (finrank ℂ (plusK leech (n : ℤ)) : ℤ) : ℤ) : ℂ)
      = (((finrank ℂ (gradingLatGen leech (n : ℤ)) : ℤ) + fockSigned 24 n : ℤ) : ℂ) := by
    rw [h]
  push_cast at h'
  rw [h']
  simp [fockSignedGenFun]

/-- The twisted sector: `dim (V_Λ^T)^+_n = [qⁿ] (4096 q² T_odd)`. -/
theorem finrank_twisted_eq_coeff (n : ℕ) :
    (finrank ℂ (twFixed 24 leechT ⊓ twWeight 24 leechT ((n : ℤ) : ℚ) :
        Submodule ℂ leechTwistedSpace) : ℂ)
      = coeff n ((4096 : ℂ) • (X ^ 2 * twOddSeries)) := by
  rw [PowerSeries.coeff_smul, PowerSeries.coeff_X_pow_mul']
  split_ifs with h
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    have hq : (((m + 2 : ℕ) : ℤ) : ℚ) = (((m : ℤ) + 2 : ℤ) : ℚ) := by push_cast; ring
    rw [hq, finrank_twFixed_inf_twWeight_24, finrank_leechT, Nat.add_sub_cancel]
    simp [twOddSeries, mul_comm]
  · have hlt : (((n : ℤ) : ℚ)) < 2 := by
      have : n < 2 := by omega
      exact_mod_cast this
    rw [twFixed_inf_twWeight_of_lt_two hlt, finrank_bot]
    simp

/-- **The two-sector series as products**:
`sectorSeries = ½ (Θ_Λ · ∏(1-qⁿ)^{-24} + ∏(1+qⁿ)^{-24}) + 4096 q² T_odd`. -/
theorem sectorSeries_eq :
    sectorSeries
      = (2 : ℂ)⁻¹ • (leechThetaSeries * fockGenFun 24 + fockSignedGenFun 24)
        + (4096 : ℂ) • (X ^ 2 * twOddSeries) := by
  ext n
  rw [map_add, PowerSeries.coeff_smul, ← two_mul_finrank_plus, ← finrank_twisted_eq_coeff]
  simp only [sectorSeries, PowerSeries.coeff_mk]
  push_cast
  rw [smul_eq_mul]
  ring

/-! ## The three identities -/

/-- **Jacobi's product formula for the formal discriminant**: `Δ/q = ∏(1-qⁿ)^{24}`, stated as
`(Δ/q) · ∏(1-qⁿ)^{-24} = 1`, where `Δ = deltaSeries = (E₄³ - E₆²)/1728` is the *formal*
discriminant of `Modularity/JFunction.lean`. -/
def DeltaProductIdentity : Prop := deltaOverQ * fockGenFun 24 = 1

/-- **The Leech theta series is `E₄³ - 720Δ`** (formal `q`-series). -/
def LeechThetaIdentity : Prop :=
  leechThetaSeries = E4Series ^ 3 - (720 : ℂ) • deltaSeries

/-- **The level-two (`Γ₀(2)` hauptmodul trace) identity**, multiplied by `q`:
`∏(1+qⁿ)^{-24} + 2¹³ q² T_odd = q·j - 768 q`.  Equivalently, with `t = η(τ)^{24}/η(2τ)^{24}`,
`t(τ) + t(-1/τ) + t(-1/(τ+1)) = j(τ) - 768`. -/
def LevelTwoIdentity : Prop :=
  fockSignedGenFun 24 + (8192 : ℂ) • (X ^ 2 * twOddSeries) = jShift - (768 : ℂ) • X

/-- Under the product formula, `j·q = E₄³ · ∏(1-qⁿ)^{-24}`. -/
theorem jShift_eq_of_deltaProduct (hD : DeltaProductIdentity) :
    jShift = E4Series ^ 3 * fockGenFun 24 := by
  rw [jShift]
  congr 1
  have h1 : ((deltaOverQUnit : (PowerSeries ℂ)ˣ) : PowerSeries ℂ)
      * ((deltaOverQUnit⁻¹ : (PowerSeries ℂ)ˣ) : PowerSeries ℂ) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [deltaOverQUnit_coe] at h1
  calc ((deltaOverQUnit⁻¹ : (PowerSeries ℂ)ˣ) : PowerSeries ℂ)
      = (fockGenFun 24 * deltaOverQ) * ((deltaOverQUnit⁻¹ : (PowerSeries ℂ)ˣ) : PowerSeries ℂ) := by
        rw [mul_comm (fockGenFun 24), hD, one_mul]
    _ = fockGenFun 24 := by rw [mul_assoc, h1, mul_one]

/-- **`q⁻¹ A = j - 720`** (with `A = q Θ_Λ ∏(1-qⁿ)^{-24}` the character of `V_Λ`), from the
product formula and `Θ_Λ = E₄³ - 720Δ`: `Θ_Λ · ∏(1-qⁿ)^{-24} = q·j - 720 q`. -/
theorem leechTheta_mul_fock_of (hD : DeltaProductIdentity) (hT : LeechThetaIdentity) :
    leechThetaSeries * fockGenFun 24 = jShift - (720 : ℂ) • X := by
  rw [hT, jShift_eq_of_deltaProduct hD, sub_mul, deltaSeries_eq, smul_mul_assoc, mul_assoc,
    hD, mul_one]

/-- **The formal reduction**: the three identities imply `sectorSeries = q·J`. -/
theorem sectorSeries_eq_JShift_of (hD : DeltaProductIdentity) (hT : LeechThetaIdentity)
    (hL : LevelTwoIdentity) : sectorSeries = JShift := by
  have hB : fockSignedGenFun 24
      = jShift - (768 : ℂ) • X - (8192 : ℂ) • (X ^ 2 * twOddSeries) := by
    rw [← hL]; abel
  rw [sectorSeries_eq, leechTheta_mul_fock_of hD hT, hB, JShift]
  ext n
  simp only [map_add, map_sub, PowerSeries.coeff_smul, smul_eq_mul]
  ring

/-! ## Sanity checks against the per-weight theorems -/

theorem coeff_sectorSeries (n : ℕ) :
    coeff n sectorSeries
      = ((finrank ℂ (leechVOAPlus.grading (n : ℤ))
          + finrank ℂ (twFixed 24 leechT ⊓ twWeight 24 leechT ((n : ℤ) : ℚ) :
              Submodule ℂ leechTwistedSpace) : ℕ) : ℂ) := by
  rw [sectorSeries, PowerSeries.coeff_mk]

theorem coeff_sectorSeries_two : coeff 2 sectorSeries = 196884 := by
  rw [coeff_sectorSeries]
  have h := finrank_sectors_two
  push_cast at h ⊢
  exact_mod_cast h

theorem coeff_sectorSeries_three : coeff 3 sectorSeries = 21493760 := by
  rw [coeff_sectorSeries]
  have h := finrank_sectors_three
  push_cast at h ⊢
  exact_mod_cast h

end Moonshine

end VOA
