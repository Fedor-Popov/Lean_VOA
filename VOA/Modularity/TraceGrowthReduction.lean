/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.GrowthClosure
import VOA.Modularity.BuhlSpanningC2

/-!
# The trace bound is the single remaining input to `OnePointSubexp`

`Modularity.GrowthClosure` says in prose that the one-point growth datum `OnePointSubexp` follows
from Zhu's trace bound `|tr_{M_{h+n}} o(v)| ≤ C·nᵖ·dim M_{h+n}`, "leaving the trace bound itself as
the single remaining mathematical input".  This file turns that sentence into a theorem: the bound
is named (`TraceGrowthBound`), and the reduction is proved, with **no other open input**.

The index conventions already line up, so no re-indexing is needed: `gradedDim N (h+n)` and
`torusOnePoint N v (h+n)` sit at the *same* shift, and for the adjoint module the relevant shift is
`0 - c/24` in both `subexponentialCoeffs_adjoint_of_C2Cofinite` and
`onePointSubexp_adjoint_of_C2Cofinite`.

## What is proved, and what is not

**Proved here (unconditional).**  Given the bound on the finitely many `C₂`-generators, the whole
growth datum follows — the `𝟙`-sequence is already unconditional from Buhl's ordered spanning set,
and `Modularity.OnePointDescent` propagates the generators to all of `𝒱`.

**Not proved here.**  `TraceGrowthBound` itself.  Zhu §4.4 and Dong–Li–Mason obtain it *not* from a
coefficient estimate on the ordered spanning set — the naive bubble-sort bound is factorial in the
word length — but from the modular-invariant ODE satisfied by `Z_M(v,q)`.  The repo's
finite-dimensionality layer (`Modularity.BlockFiniteDim`) currently takes `OnePointSubexp` as a
hypothesis, so it cannot be used here without circularity; breaking that would need a *formal*
(pre-convergence) finiteness and indicial-equation layer.  That is the honest residual.

## Main results

* `TraceGrowthBound` — the named datum;
* `subexponential_of_traceGrowthBound` — the consumption step, at one `v`;
* `onePointSubexp_of_traceGrowthBound` — the general-module reduction;
* `onePointSubexp_adjoint_of_generatorTraceBound` — for `𝒱` itself, the datum is needed on
  **finitely many homogeneous generators only**.

## Status
Proved, axiom-clean, `pbw`-free, no `sorry`.  `TraceGrowthBound` is a named hypothesis, never an
axiom, and is *not* claimed to be discharged.
-/

namespace VOA

open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
  {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- **Zhu's trace bound at one vector.**  `|tr_{M_{h+n}} o(v)| ≤ C·nᵖ·dim M_{h+n}` — the graded
trace of the zero mode grows at most polynomially faster than the graded dimension. -/
def TraceGrowthBound (N : OrdVModule W M) (h : ℂ) (v : 𝒱) : Prop :=
  ∃ (C : ℝ) (p : ℕ), 0 ≤ C ∧ ∀ n : ℕ,
    ‖torusOnePoint N v (h + (n : ℂ))‖ ≤ C * ((n : ℝ) ^ p * ‖gradedDim N (h + (n : ℂ))‖)

/-- **The consumption step at one `v`.**  A polynomial multiple of a subexponential sequence is
subexponential (`subexponential_of_le_pow_mul`), so the trace bound plus the *dimension* growth
gives the *trace* growth. -/
theorem subexponential_of_traceGrowthBound (N : OrdVModule W M) (h : ℂ)
    (hdim : SubexponentialCoeffs N h) {v : 𝒱} (hv : TraceGrowthBound N h v) :
    Subexponential (fun n : ℕ => ‖torusOnePoint N v (h + (n : ℂ))‖) := by
  obtain ⟨C, p, hC, hb⟩ := hv
  exact subexponential_of_le_pow_mul hdim (fun _ => norm_nonneg _) hC p hb

/-- **The general-module reduction.**  With the dimension growth in hand, the trace bound for
*every* `v` is exactly `OnePointSubexp`. -/
theorem onePointSubexp_of_traceGrowthBound (N : OrdVModule W M) (h : ℂ)
    (hdim : SubexponentialCoeffs N h) (htr : ∀ v : 𝒱, TraceGrowthBound N h v) :
    OnePointSubexp N h :=
  fun v => subexponential_of_traceGrowthBound N h hdim (htr v)

/-- **For `𝒱` itself, only finitely many trace bounds are needed.**  Buhl's ordered spanning set
gives the dimension growth and the `𝟙`-sequence unconditionally, and `OnePointDescent` propagates
the `C₂`-generators to all of `𝒱`; so the entire growth datum reduces to `TraceGrowthBound` on the
`g` homogeneous generators.  This is the machine-checked form of "the trace bound is the single
remaining input". -/
theorem onePointSubexp_adjoint_of_generatorTraceBound (W : VertexOperatorAlgebra 𝒱)
    (hne : W.vacuum ≠ 0) (hC2 : C2Cofinite W)
    (hsupp : OnePointSupported (adjointModule W) (0 - W.centralCharge / 24)) :
    ∃ (g : ℕ) (gen : Fin g → 𝒱) (wt : Fin g → ℕ),
      (∀ i, 1 ≤ wt i) ∧ (∀ i, gen i ∈ W.grading (wt i : ℤ)) ∧
      ((∀ i, TraceGrowthBound (adjointModule W) (0 - W.centralCharge / 24) (gen i)) →
        OnePointSubexp (adjointModule W) (0 - W.centralCharge / 24)) := by
  obtain ⟨g, gen, wt, hwt, hgenmem, hall⟩ :=
    onePointSubexp_adjoint_of_C2Cofinite W hne hC2 hsupp
  refine ⟨g, gen, wt, hwt, hgenmem, fun htr => hall (fun i => ?_)⟩
  exact subexponential_of_traceGrowthBound (adjointModule W) (0 - W.centralCharge / 24)
    (subexponentialCoeffs_adjoint_of_C2Cofinite W hne hC2) (htr i)

/-- The unconditional-in-everything-else form for `𝒱`: the trace bound for all `v` gives the growth
datum outright. -/
theorem onePointSubexp_adjoint_of_traceGrowthBound (W : VertexOperatorAlgebra 𝒱)
    (hne : W.vacuum ≠ 0) (hC2 : C2Cofinite W)
    (htr : ∀ v : 𝒱, TraceGrowthBound (adjointModule W) (0 - W.centralCharge / 24) v) :
    OnePointSubexp (adjointModule W) (0 - W.centralCharge / 24) :=
  onePointSubexp_of_traceGrowthBound (adjointModule W) (0 - W.centralCharge / 24)
    (subexponentialCoeffs_adjoint_of_C2Cofinite W hne hC2) htr

end VOA
