/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.ZhuGenFiltration
import VOA.Moonshine.SigmaExistZhu

/-!
# `ZhuGenerated ((V₀⁺)₂)` reduced to a spanning statement about `V₀⁺`  (Moonshine step M8g, R-gen)

`SigmaExistZhu.lean` reduced the zero-mode clause of the top-level residual of `σ` to
`ZhuGenerated G` for a set `G` of letters.  Here the filtered criterion
`ZhuGen.eq_top_of_lowerSpan` (VOA-generic, `ZhuGenFiltration.lean`) is applied to `V₀⁺ = V0P` with
`G = (V₀⁺)₂`:

`zhuGenerated_weightTwo_of_lowerSpanned : V0LowerSpanned → ZhuGenerated weightTwo`.

The named residual `V0LowerSpanned` says: for every `n ≥ 3`, `(V₀⁺)_n` is spanned by products
`a₍ₘ₎b` with `m ≤ 0` and `a, b` homogeneous of weight `< n`.  It mentions neither `∗` nor `O(V)`:
it is a statement about the vertex algebra `V₀⁺` alone, checkable weight by weight, and it is
**strictly stronger** than (not equivalent to) `ZhuGenerated weightTwo`.  The route by which it is
expected to be proved: Fock sector by bilinear `0`-modes plus a degree-4 cancellation, charged
sectors by lattice products.

Weights `≤ 2` are free: `(V₀⁺)₀ = ℂ𝟙`, `(V₀⁺)₁ = 0` (`V0P_grading_one`), `(V₀⁺)₂ = G`.

## Main results
* `weightTwo`, `V0P_grading_one`.
* `V0LowerSpanned` — the named residual (a `Prop`).
* `zhuGenerated_weightTwo_of_lowerSpanned`.
* `topSigmaV3_of_lowerSpanned`, `topSigmaTT_of_lowerSpanned` — the σ top-level residuals with
  `ZhuGenerated` replaced by `V0LowerSpanned`.

## Status
`sorry`-free; no project axiom.  Conditional on `V0LowerSpanned` (open) and, for the `σ`
corollaries, on the weight-2 zero-mode identities (R-top).  Imported by the
umbrella `VOA/Moonshine.lean`.
-/

set_option linter.style.longLine false

namespace VOA.Moonshine.SigmaExist

open VOA VOA.Moonshine VOA.Moonshine.TrialityTw VOA.Moonshine.ZhuGen
open Submodule

/-- The weight-2 letters `G = (V₀⁺)₂`. -/
def weightTwo : Set V0Sub.carrier := {g | g ∈ V0P.grading 2}

theorem mem_V0P_grading_iff {k : ℤ} {x : V0Sub.carrier} :
    x ∈ V0P.grading k ↔ (x : VPlus) ∈ leechVOAPlus.grading k := Iff.rfl

/-- `(V₀⁺)₁ = 0` (since `(V_Λ⁺)₁ = 0`). -/
theorem V0P_grading_one : V0P.grading 1 = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [mem_V0P_grading_iff, leechVOAPlus_grading_one] at hx
  rw [mem_bot]
  exact Subtype.ext ((mem_bot ℂ).mp hx)

/-- **The named residual (R-gen′).**  For every `n ≥ 3`, `(V₀⁺)_n` is spanned by the products
`a₍ₘ₎b`, `m ≤ 0`, of homogeneous `a ∈ (V₀⁺)_p`, `b ∈ (V₀⁺)_q` with `p, q < n` and
`p + q − m − 1 = n` (`ZhuGen.lowerProd`).  A statement about `V₀⁺` alone (no `∗`, no `O(V)`);
sufficient for, and strictly stronger than, `ZhuGenerated weightTwo`. -/
def V0LowerSpanned : Prop :=
  ∀ n : ℤ, 3 ≤ n → V0P.grading n ≤ span ℂ (lowerProd V0P n)

/-- **`ZhuGenerated ((V₀⁺)₂)` from the spanning residual.** -/
theorem zhuGenerated_weightTwo_of_lowerSpanned (h : V0LowerSpanned) : ZhuGenerated weightTwo := by
  intro S h1 hO hmul hG
  refine eq_top_of_lowerSpan weightTwo (fun n hn => ?_) S h1 hO hmul hG
  rcases lt_or_ge n 3 with h3 | h3
  · interval_cases n
    · rw [V0P_grading_one]; exact bot_le
    · intro x hx
      exact subset_span (Or.inl hx)
  · exact (h n h3).trans (span_mono Set.subset_union_right)

/-- `TopSigmaV3` with `ZhuGenerated` replaced by the spanning residual. -/
theorem topSigmaV3_of_lowerSpanned {s : ZMod 2} {φ : VPlus →ₗ[ℂ] TP}
    (hf : ∀ x ∈ OmegaV3, φ x ∈ TPframe s) (hw : ∀ x ∈ OmegaV3, φ x ∈ plusModule.weight (2 : ℂ))
    (hL : V0LowerSpanned)
    (hGφ : ∀ g ∈ weightTwo, ∀ x ∈ OmegaV3, φ (actV g 1 x) = actT (sig g) 1 (φ x))
    (hc : ∃ t₀ : TLeechT, t₀ ∈ leechFrameT s ∧ t₀ ≠ 0 ∧ ∃ x ∈ OmegaV3, φ x = x0T t₀) :
    TopSigmaV3 s φ :=
  topSigmaV3_of_zhuGenerated hf hw (zhuGenerated_weightTwo_of_lowerSpanned hL)
    (fun g hg => ⟨2, hg, by simpa using hGφ g hg⟩) hc

/-- `TopSigmaTT` with `ZhuGenerated` replaced by the spanning residual. -/
theorem topSigmaTT_of_lowerSpanned {s' s : ZMod 2} {φ : TP →ₗ[ℂ] TP}
    (hf : ∀ x ∈ OmegaT s', φ x ∈ TPframe s) (hw : ∀ x ∈ OmegaT s', φ x ∈ plusModule.weight (2 : ℂ))
    (hL : V0LowerSpanned)
    (hGφ : ∀ g ∈ weightTwo, ∀ x ∈ OmegaT s', φ (actT g 1 x) = actT (sig g) 1 (φ x))
    (hc : ∃ t₀ : TLeechT, t₀ ∈ leechFrameT s ∧ t₀ ≠ 0 ∧ ∃ x ∈ OmegaT s', φ x = x0T t₀) :
    TopSigmaTT s' s φ :=
  topSigmaTT_of_zhuGenerated hf hw (zhuGenerated_weightTwo_of_lowerSpanned hL)
    (fun g hg => ⟨2, hg, by simpa using hGφ g hg⟩) hc

end VOA.Moonshine.SigmaExist
