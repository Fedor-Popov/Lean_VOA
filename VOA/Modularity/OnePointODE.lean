/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.IndicialGrowth
import VOA.Modularity.AnalyticBlock

/-!
# `OnePointSubexp` from a formal ODE — steps (2)–(5) of residual (c)

Zhu §4.4 and DLM §§6–7 obtain the convergence of `Z_M(v,q)` from a monic linear equation
`(q d/dq)^s F + ∑_{i<s} g_i(q)·(q d/dq)^i F = 0`, **not** from a coefficient growth bound — there is
no such bound anywhere in Zhu, DLM or Miyamoto.  This file completes the passage
*ODE ⟹ subexponential coefficients ⟹ `OnePointSubexp`*, so that the whole of residual **(c)**
reduces to producing the ODE.

Note what is **not** needed: no Frobenius–Fuchs, no regular-singular theory, no analytic
continuation.  Mathlib has none of those, and the argument does not use them.

## What remains, named exactly

The hypothesis `hode` below.  ⚠ **It cannot be obtained from `Modularity.BlockDeterminacy`**:
`IsAnalyticBlock.serreDeriv_mem` and `IsAnalyticBlock.mem_span_eisenstein` both take
`hF : IsAnalyticBlock W F`, and the only route to that for a trace function is
`torusOnePoint_isAnalyticBlock`, which takes **`OnePointSubexp` as a hypothesis** — the very thing
being proved.  Producing `hode` therefore requires the *formal*, pre-convergence analogues of those
two theorems, over the banked `IsFormalBlock` (`Modularity.ZhuBlockConditions`, unconditional) with
`qDeriv`/`qConv` in place of `deriv`/multiplication.  That is Zhu Lemmas 4.4.1/4.4.2/4.4.4 =
DLM Lemmas 5.2/5.3/6.1–6.3, ported to `FormalQSeries`.

## Main results

* `subexponential_of_indicialODE` — the sequence-level statement, `hp`-free;
* `onePointSubexp_of_indicialODE` — `OnePointSubexp` from the formal ODE.

## Status
Proved, axiom-clean, `pbw`-free, no `sorry`.  `hode` is an explicit hypothesis here, never an
axiom.  It is not discharged in this file, but the conclusion `OnePointSubexp` it serves is proved
from `C₂`-cofiniteness by another route (`onePointSubexp_of_c2`, `Modularity/BlockGrowth.lean`), and
under `EtingofFinite` via `Modules.QuasiLisseFinite`.
-/

namespace VOA

open scoped BigOperators
open Filter

/-- **The indicial recursion gives subexponential coefficients** — with the growth of the
divisor discharged (`tendsto_indicialDivisor_atTop`), so monicity is the only input. -/
theorem subexponential_of_indicialODE {χ : ℕ → ℂ} (lam : ℂ) {s : ℕ} (hs : 1 ≤ s)
    (g : ℕ → ℕ → ℂ) (hg : ∀ i, Subexponential (fun k => ‖g i k‖))
    (hrec : ∀ n : ℕ, indicialP lam s g n * χ n
      = - ∑ m ∈ Finset.range n, ∑ i ∈ Finset.range s,
          g i (n - m) * (lam + (m : ℂ)) ^ i * χ m) :
    Subexponential (fun n => ‖χ n‖) :=
  subexponential_of_indicial_recursion lam hs g hg (tendsto_indicialDivisor_atTop lam hs g) hrec

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
  {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- **`OnePointSubexp` from the formal ODE.**  `hode` says: for every `v`, the one-point
function `𝒵_M(v; q)` satisfies a **monic** linear equation of some order `s ≥ 1` whose coefficient
`q`-series have subexponential coefficients — read off at the `q^{h+n}`-coefficient. -/
theorem onePointSubexp_of_indicialODE (N : OrdVModule W M) (hbase : ℂ)
    (hode : ∀ v : 𝒱, ∃ (s : ℕ) (g : ℕ → ℕ → ℂ), 1 ≤ s ∧
      (∀ i, Subexponential (fun k => ‖g i k‖)) ∧
      ∀ n : ℕ, indicialP hbase s g n * torusOnePoint N v (hbase + (n : ℂ))
        = - ∑ m ∈ Finset.range n, ∑ i ∈ Finset.range s,
            g i (n - m) * (hbase + (m : ℂ)) ^ i * torusOnePoint N v (hbase + (m : ℂ))) :
    OnePointSubexp N hbase := by
  intro v
  obtain ⟨s, g, hs, hg, hrec⟩ := hode v
  exact subexponential_of_indicialODE hbase hs g hg hrec

end VOA
