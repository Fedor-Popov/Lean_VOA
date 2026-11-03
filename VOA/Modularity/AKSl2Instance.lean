/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Modularity.AKSl2Payoff
import VOA.Modularity.AKZhuModularity
import VOA.Examples.AffineSl2Presentation

/-!
# Arakawa–Kawasetsu at a **non-trivial** vertex operator algebra: `L₋₄⁄₃(𝔰𝔩₂)`

`Modularity.AKSl2Payoff` states the Arakawa–Kawasetsu consequences of an `𝔰𝔩₂` symbol
presentation, and says in capitals that the presentation is never constructed, so that every
statement there is *"an implication, not an example"*.  `Examples.AffineSl2Presentation`
**constructs** it — `Sl2Pres.sl2PresentationSimpleSl2QL : Sl2Presentation simpleSl2QL` — so this
file discharges the hypothesis and records what falls out.

## The main result, stated exactly

> **`EtingofFinite (L₋₄⁄₃(𝔰𝔩₂))` holds unconditionally, and the character of `L₋₄⁄₃(𝔰𝔩₂)`
> satisfies a monic linear ODE in `q d/dq` with subexponential coefficients — with no
> hypotheses, and without the PBW theorem `VOA.pbw`.**

The trivial VOA has `EtingofFinite` unconditionally (`QuasiLisseFinite.trivial_etingofFinite`,
itself via `EtingofFinite_of_C2Cofinite`).  `L₋₄⁄₃(𝔰𝔩₂)` is a non-trivial instance, and the
route is not `EtingofFinite_of_C2Cofinite`: it is `Sl2Presentation.etingofFinite`, which spans
`A₂(W)` by Poisson brackets together with the three classes `[1]`, `[h²]`, `[ef]`.

## ⚠⚠ What this is NOT — the three things it would be easy to overclaim

1. **Non-lisseness is proved elsewhere, not in this file.**  `¬ C2Cofinite (L₋₄⁄₃(𝔰𝔩₂))` is
   proved unconditionally as `Sl2NonLisse.not_C2Cofinite_simpleSl2QL`
   (`Examples/AffineSl2NonLisse.lean`, via linear independence of the classes `[e^r]` in `A₂`).
   This file also states the conditional form
   `character_formalODE_of_non_lisse_simpleSl2QL`, on the hypothesis `Sl2Pres.Sl2ExactSymbol`
   (exactness of the symbol ideal `Cas·𝔪`).  That hypothesis is not proved; note that Arakawa's
   theorem gives the associated variety `X_L = 𝒩`, i.e. only the *radical* of the symbol ideal,
   not its exact form.
2. **NOT "quasi-lisse".**  Quasi-lisseness — associated varieties, symplectic leaves, the
   Etingof–Schedler D-module theorem — is not formalized anywhere in this repository.
   `EtingofFinite` is a deliberate axiomatization of the *conclusion* of Etingof–Schedler.
3. **NOT AK Theorem 5.1, and NOT a modular linear differential equation** — and the formal ODE
   is near-vacuous (see `Modularity.AKModularODE`).  The three gaps of
   `Modularity.AKModularODE` are carried forward unchanged: the basis is the Euler operator
   `(q d/dq)^i` rather than AK's iterated Serre derivative; the coefficients are subexponential
   power series rather than `ℂ[G̃₄,G̃₆]`; and nothing is proved about modularity of the
   coefficients or about the span of characters being an `SL₂(ℤ)`-representation.

Nor does anything here give **Zhu modularity** for `L₋₄⁄₃(𝔰𝔩₂)`: the main theorem of
`Modularity.AKZhuModularity` additionally needs `hfib` and the rank bound `hrank`, and
`EtingofFinite` provably cannot supply `hrank` (see `Modularity.AKZhuModularity`, module
docstring).

## Main results (all unconditional at `L₋₄⁄₃(𝔰𝔩₂)`, all `pbw`-free)

* `character_formalODE_simpleSl2QL_uncond` — the character ODE for `L₋₄⁄₃(𝔰𝔩₂)` itself.
* `uniform_order_character_formalODE_simpleSl2QL` — one ODE order `s` for *every* ordinary
  module of `L₋₄⁄₃(𝔰𝔩₂)`.
* `character_formalODE_module_simpleSl2QL` — the character ODE for every ordinary module
  with a conformal weight.
* `qSummable_character_simpleSl2QL` — the character `q`-series of `L₋₄⁄₃(𝔰𝔩₂)` converges on
  the upper half plane.
* `finiteDimensional_analyticBlocks_simpleSl2QL` — **Zhu 5.3.2** for `L₋₄⁄₃(𝔰𝔩₂)`: the space
  of analytic conformal blocks is finite-dimensional, obtained *without* `C₂`-cofiniteness.

## Status
`sorry`-free and axiom-clean: every declaration reports exactly
`[propext, Classical.choice, Quot.sound]`.  The PBW theorem `VOA.pbw` is **not**
used — the nonzero vacuum comes from `Sl2Pres.vacuum_simpleSl2QL_ne_zero'`
(`AffineSl2Rigidity43.L43_vacuum_ne_zero`, Wakimoto), not from
`QuasiLisseSl2.vacuum_simpleSl2QL_ne_zero` (which does use `pbw`).

## References
* T. Arakawa, K. Kawasetsu, *Quasi-lisse vertex algebras and modular linear differential
  equations*, arXiv:1610.05865, Theorem 5.1 and Lemma 5.5.
* P. Etingof, T. Schedler, *Poisson traces and D-modules on Poisson varieties*, GAFA **20**
  (2010) 958–987.
* Y. Zhu, *Modular invariance of characters of vertex operator algebras*, JAMS **9** (1996),
  Theorem 5.3.2.
-/

namespace VOA.Sl2Pres

open VOA
open VOA.QuasiLisseSl2

universe u

noncomputable section

/-- `VacuumGradeZero` for `L₋₄⁄₃(𝔰𝔩₂)` — free for every VOA, it is the VOA4 field
`vacuum_grade` weakened from `=` to `≤`. -/
theorem vacuumGradeZero_simpleSl2QL : VacuumGradeZero simpleSl2QL :=
  vacuumGradeZero_of_vacuum_grade simpleSl2QL

/-- **THE HEADLINE.**  The character of `L₋₄⁄₃(𝔰𝔩₂)` — the trace
`tr_V q^{L₀ − c/24}` of the simple affine vertex operator algebra of `𝔰𝔩₂` at the admissible
level `k = -4/3`, central charge `c = -6` — satisfies a **monic linear ODE in `q d/dq` with
subexponential coefficients** (a formal `q`-series identity), unconditionally.

This is the first vertex operator algebra other than `trivialVOA` at which the repository proves
the formal character ODE produced by the Arakawa–Kawasetsu *argument*; it is **not** the
Arakawa–Kawasetsu character equation itself (see ⚠ below).  The finiteness input is *not*
`C₂`-cofiniteness: it is `Sl2Pres.etingofFinite_simpleSl2QL'`, obtained from the constructed
`𝔰𝔩₂` symbol presentation of `A₂(L₋₄⁄₃(𝔰𝔩₂))`.

Non-lisseness is proved separately: `Sl2NonLisse.not_C2Cofinite_simpleSl2QL`
(`Examples/AffineSl2NonLisse.lean`).

⚠ Formal `q`-series identity in the `(q d/dq)^i` basis with `SubexpPS` coefficients — **not** AK
Theorem 5.1, **not** a modular linear differential equation, and near-vacuous (such an equation
holds for essentially any convergent `q`-series with bounded zero multiplicity; paper argument; see
`Modularity.AKModularODE`). -/
theorem character_formalODE_simpleSl2QL_uncond :
    ∃ (s : ℕ) (g : ℕ → ℕ → ℂ), 1 ≤ s ∧ (∀ i, Subexponential (fun k => ‖g i k‖)) ∧
      ∀ e : ℂ, (qDeriv^[s] (torusPartition (adjointModule simpleSl2QL))) e
        + ∑ i ∈ Finset.range s,
            qConv (g i) (qDeriv^[i] (torusPartition (adjointModule simpleSl2QL))) e = 0 :=
  character_formalODE_adjoint_of_etingofFinite simpleSl2QL vacuum_simpleSl2QL_ne_zero'
    vacuumGradeZero_simpleSl2QL etingofFinite_simpleSl2QL'

/-- The character ODE for **every** ordinary `L₋₄⁄₃(𝔰𝔩₂)`-module carrying a conformal
weight, unconditionally. -/
theorem character_formalODE_module_simpleSl2QL {M : Type} [AddCommGroup M] [Module ℂ M]
    (N : OrdVModule simpleSl2QL M) {hw : ℂ} (hcw : HasConformalWeight N hw) :
    ∃ (s : ℕ) (g : ℕ → ℕ → ℂ), 1 ≤ s ∧ (∀ i, Subexponential (fun k => ‖g i k‖)) ∧
      ∀ e : ℂ, (qDeriv^[s] (torusPartition N)) e
        + ∑ i ∈ Finset.range s, qConv (g i) (qDeriv^[i] (torusPartition N)) e = 0 :=
  character_formalODE_of_etingofFinite simpleSl2QL N hcw vacuumGradeZero_simpleSl2QL
    etingofFinite_simpleSl2QL'

/-- **A module-independent ODE order for `L₋₄⁄₃(𝔰𝔩₂)`.**  There is a single `s ≥ 1` such
that the character of *every* ordinary module satisfies a monic order-`s` linear ODE in `q d/dq`.

⚠ Only the **order** is uniform; the coefficients are still chosen after the module. -/
theorem uniform_order_character_formalODE_simpleSl2QL :
    ∃ s : ℕ, 1 ≤ s ∧
      ∀ {M : Type} [AddCommGroup M] [Module ℂ M] (N : OrdVModule simpleSl2QL M) (hw : ℂ),
        HasConformalWeight N hw →
          ∃ g : ℕ → ℕ → ℂ, (∀ i, Subexponential (fun k => ‖g i k‖)) ∧
            ∀ e : ℂ, (qDeriv^[s] (torusPartition N)) e
              + ∑ i ∈ Finset.range s,
                  qConv (g i) (qDeriv^[i] (torusPartition N)) e = 0 :=
  uniform_order_character_formalODE_of_etingofFinite simpleSl2QL vacuumGradeZero_simpleSl2QL
    etingofFinite_simpleSl2QL'

/-- **The character `q`-series of `L₋₄⁄₃(𝔰𝔩₂)` converges on the upper half plane**, from
Etingof–Schedler finiteness alone — no `C₂`-cofiniteness. -/
theorem qSummable_character_simpleSl2QL (τ : UpperHalfPlane) :
    QSummableAt (gradedDim (adjointModule simpleSl2QL))
      ((0 : ℂ) - simpleSl2QL.centralCharge / 24) τ :=
  qSummable_gradedDim_of_etingofFinite (adjointModule simpleSl2QL)
    (adjoint_hasConformalWeight simpleSl2QL vacuum_simpleSl2QL_ne_zero')
    vacuumGradeZero_simpleSl2QL etingofFinite_simpleSl2QL' τ

/-- **Zhu's Theorem 5.3.2 for `L₋₄⁄₃(𝔰𝔩₂)`**: the space of analytic conformal blocks is
finite-dimensional.  Obtained through `Modularity.AKZhuModularity`'s Etingof route, which
bypasses the two `C₂`-cofiniteness entry points `ZhuAlgebraFinite.finiteDimensional_A_of_C2Cofinite`
and `BlockRelSpanE.moduleFinite_quot_blockRelSpanE`. -/
theorem finiteDimensional_analyticBlocks_simpleSl2QL :
    FiniteDimensional ℂ (Submodule.map restrictImGT (analyticBlocks simpleSl2QL)) :=
  finiteDimensional_analyticBlocks_of_etingofFinite simpleSl2QL vacuumGradeZero_simpleSl2QL
    etingofFinite_simpleSl2QL'

/-! ## Non-lisseness

The statement that makes Arakawa–Kawasetsu do work *beyond* Zhu — that `L₋₄⁄₃(𝔰𝔩₂)` is not
`C₂`-cofinite — is proved unconditionally as `Sl2NonLisse.not_C2Cofinite_simpleSl2QL`
(`Examples/AffineSl2NonLisse.lean`, imported through `Modularity.AKSl2Payoff`). -/

/-- **The Arakawa–Kawasetsu configuration at `L₋₄⁄₃(𝔰𝔩₂)`**, unconditionally: the algebra is
**not** `C₂`-cofinite (`Sl2NonLisse.not_C2Cofinite_simpleSl2QL`), and its character satisfies a
monic linear ODE in `q d/dq` (`character_formalODE_simpleSl2QL_uncond`).  The named hypothesis
`hex : Sl2ExactSymbol` (exactness of the symbol ideal; not proved) is not needed.  The ODE is a
formal `(q d/dq)`-equation with
subexponential coefficients, not a modular linear differential equation, and is near-vacuous
(see `Modularity.AKModularODE`). -/
theorem character_formalODE_of_non_lisse_simpleSl2QL :
    ¬ C2Cofinite simpleSl2QL ∧
      ∃ (s : ℕ) (g : ℕ → ℕ → ℂ), 1 ≤ s ∧ (∀ i, Subexponential (fun k => ‖g i k‖)) ∧
        ∀ e : ℂ, (qDeriv^[s] (torusPartition (adjointModule simpleSl2QL))) e
          + ∑ i ∈ Finset.range s,
              qConv (g i) (qDeriv^[i] (torusPartition (adjointModule simpleSl2QL))) e = 0 :=
  ⟨Sl2NonLisse.not_C2Cofinite_simpleSl2QL, character_formalODE_simpleSl2QL_uncond⟩

end

end VOA.Sl2Pres

section AxiomAudit
#print axioms VOA.Sl2Pres.vacuumGradeZero_simpleSl2QL
#print axioms VOA.Sl2Pres.character_formalODE_simpleSl2QL_uncond
#print axioms VOA.Sl2Pres.character_formalODE_module_simpleSl2QL
#print axioms VOA.Sl2Pres.uniform_order_character_formalODE_simpleSl2QL
#print axioms VOA.Sl2Pres.qSummable_character_simpleSl2QL
#print axioms VOA.Sl2Pres.finiteDimensional_analyticBlocks_simpleSl2QL
#print axioms VOA.Sl2Pres.character_formalODE_of_non_lisse_simpleSl2QL
end AxiomAudit
