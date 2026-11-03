/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Huang.AndersonMooreCore
import VOA.Huang.AndersonMooreReduction

/-!
# The Anderson–Moore theorem, proved

`AndersonMooreInput` (`VOA/Huang/AndersonMoore.lean`, statement unchanged): if finitely many
`f_i(τ) = Σ_m a_{i,m} e^{2πi(λ_i+m)τ}` (`a_{i,m} ∈ ℕ`, `a_{i,0} ≠ 0`) span an `S`-closed family,
every `λ_i` is rational.

* `amCore_holds : AMCore` — the core theorem `rat_of_sClosed` (Galois–MLDE argument of
  Anderson–Moore 1988 / Gannon, arXiv:1310.4458, Prop. 3.5(b)), in the form required by the
  reduction;
* `andersonMooreInput_holds : AndersonMooreInput` — via `andersonMooreInput_of_core`
  (classes mod `ℤ`, ℚ-echelon bases with distinct exponents).
* `dlmRationalityInput_of_pbw_am` — hence `DLMRationalityInput` from the PBW datum alone.

## Status
No `sorry`, no new axioms.
-/

namespace VOA.Huang.AndersonMoore

open VOA VOA.Classification.COne VOA.Huang.ZhuModData VOA.Huang.IModDataReduced

universe u

/-- The core statement of the reduction holds. -/
theorem amCore_holds : AMCore := by
  intro n ν U hU hUr hν hU0 S hS j
  exact rat_of_sClosed hU hUr hν hU0 S hS j

/-- **The Anderson–Moore theorem.** -/
theorem andersonMooreInput_holds : AndersonMooreInput :=
  andersonMooreInput_of_core amCore_holds

/-- `DLMRationalityInput` with the Anderson–Moore input discharged. -/
theorem dlmRationalityInput_of_pbw_am (hPBW : ZhuPBWBottomInput.{u}) :
    DLMRationalityInput.{u} :=
  dlmRationalityInput_of_andersonMoore hPBW andersonMooreInput_holds

end VOA.Huang.AndersonMoore
