/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.CharacterLevelTwo

/-!
# The two sectors of `V♮` have graded dimension `J`  (Moonshine step M7d)

`sectorSeries_eq_JShift`:

  `Σ_{n≥0} (dim (V_Λ^+)_n + dim (V_Λ^T)^+_n) qⁿ = q·J(q)`,   `J = j - 744 = q⁻¹ + 196884 q + ⋯`,

as an identity in `ℂ⟦q⟧`, for **all** weights, where `JShift = q·J` is the formal series of
`Modularity/JFunction.lean` (`jShift = E₄³/(Δ/q)` with the formal Eisenstein series and the formal
`Δ = (E₄³ - E₆²)/1728`).  Coefficientwise: `finrank_sectors_eq_coeff_JShift`.

## Route (decided before formalising; all identities first checked numerically on 40 coefficients)
The analytic route, since every formal-only route needs Jacobi's abstruse identity or the theta
formula for `E₄`, neither of which is in Mathlib:
1. `CharacterSeries.sectorSeries_eq` — the per-weight dimension theorems of M7b/M7c assembled
   into `sectorSeries = ½(Θ_Λ P + B) + 4096 q² T_odd` (formal; `P = ∏(1-qⁿ)^{-24}`,
   `B = ∏(1+qⁿ)^{-24}`).
2. `CharacterDelta.deltaProductIdentity` — Jacobi's product `Δ = q∏(1-qⁿ)^{24}` for the formal
   `Δ`: Mathlib's analytic product for `Δ` plus the dominated-convergence bridge
   `CharacterBridge.bridge` (formal infinite products evaluate to the analytic ones) and
   uniqueness of `q`-expansions.  `CharacterDelta.leechThetaIdentity` — `Θ_Λ = E₄³ - 720Δ` from
   `dim M₁₂ = 2` and `r_Λ(2) = 0`.  Hence `Θ_Λ P = q(j - 720)`.
3. `CharacterLevelTwo.levelTwoIdentity` — `B + 2¹³ q² T_odd = q(j - 768)`, i.e.
   `t(τ) + t(-1/τ) + t(-1/(τ+1)) = j - 768` for the `Γ₀(2)` hauptmodul `t = Δ(τ)/Δ(2τ)`.
   Proof: `Φ = Δ(τ)²(Δ(2τ)⁻¹ + 2¹²Δ(τ/2)⁻¹ + 2¹²Δ((τ+1)/2)⁻¹)` is a level-one modular form of
   weight 12 (`phiForm`: `S`/`T` permute the three cosets; holomorphic; bounded at `i∞`), its
   `q`-expansion is `1 - 48q + ⋯` (computed through the bridge), so `Φ = E₄³ - 768Δ`; formal product
   identities (`∏(1+qⁿ)∏(1-qⁿ) = ∏(1-q^{2n})`, odd/even splitting) turn `Φ/Δ` into `B + 2¹³q²T_odd`.
4. Algebra: `CharacterSeries.sectorSeries_eq_JShift_of`.

## Status
Proved, no `sorry`, no new axioms; `#print axioms sectorSeries_eq_JShift` is
`[propext, Classical.choice, Quot.sound]` (no `pbw`).  **Unconditional** as a statement about
the two summands: no hypotheses.  Honest scope (as in `TwistedSectorDim.lean`): this is the sum of
the graded dimensions of `V_Λ^+` (a genuine VOA) and of `(S[θ] ⊗ T)^+` with the `L₀`-grading
*defined* by oscillator weight `+ 3/2` and `θ_tw = θ ⊗ (-1)` as in FLM; `V♮` itself (step M8) and
the twisted vertex operators (step M6) are not used and not constructed.
-/

set_option linter.style.longLine false

open scoped TensorProduct

namespace VOA

namespace Moonshine

open TwistedSector Module PowerSeries

/-- **The graded dimension of the two sectors of `V♮` is `J`**:
`Σ_n (dim (V_Λ^+)_n + dim (V_Λ^T)^+_n) qⁿ = q·J(q)` in `ℂ⟦q⟧`. -/
theorem sectorSeries_eq_JShift : sectorSeries = JShift :=
  sectorSeries_eq_JShift_of_levelTwo levelTwoIdentity

/-- **Coefficientwise**: for every `n`, `dim (V_Λ^+)_n + dim (V_Λ^T)^+_n = [q^{n-1}] J`. -/
theorem finrank_sectors_eq_coeff_JShift (n : ℕ) :
    ((finrank ℂ (leechVOAPlus.grading (n : ℤ))
      + finrank ℂ (twFixed 24 leechT ⊓ twWeight 24 leechT ((n : ℤ) : ℚ) :
          Submodule ℂ leechTwistedSpace) : ℕ) : ℂ)
      = coeff n JShift := by
  rw [← coeff_sectorSeries, sectorSeries_eq_JShift]

/-- Consistency with M7a/M7c: the weight-2 coefficient computed per-weight (`finrank_sectors_two`)
and the one of `J` (`coeff_two_JShift`) agree. -/
theorem coeff_two_consistency : coeff 2 sectorSeries = coeff 2 JShift := by
  rw [coeff_sectorSeries_two, coeff_two_JShift]

/-- **A new coefficient of `J`, read off from the sector dimensions**: `[q²] J = 21493760`
(from `finrank_sectors_three`, M7c). -/
theorem coeff_three_JShift : coeff 3 JShift = 21493760 := by
  rw [← sectorSeries_eq_JShift, coeff_sectorSeries_three]

/-- `V♮` has no weight-one states in either sector, and `[q⁰] J = 0`: the two agree. -/
theorem coeff_one_JShift : coeff 1 JShift = 0 := by
  rw [← sectorSeries_eq_JShift, coeff_sectorSeries]
  have h1 : leechVOAPlus.grading ((1 : ℕ) : ℤ) = ⊥ := leechVOAPlus_grading_one
  have h2 : twFixed 24 leechT ⊓ twWeight 24 leechT (((1 : ℕ) : ℤ) : ℚ) = ⊥ := by
    have := twFixed_inf_twWeight_one (T := leechT)
    simpa using this
  rw [h1, h2, finrank_bot, finrank_bot]
  simp

end Moonshine

end VOA
