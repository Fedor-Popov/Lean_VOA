/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.AKUniformODE
import VOA.Examples.AffineSl2QuasiLisse
import VOA.Examples.AffineSl2NonLisse

/-!
# Arakawa–Kawasetsu: a (formal) character ODE for a non-lisse VOA

The whole point of Arakawa–Kawasetsu (*Quasi-lisse vertex algebras and modular linear differential
equations*, arXiv:1610.05865) is that quasi-lisse **strictly generalises** lisse: their Theorem 5.1
constrains the character of vertex operator algebras that Zhu's theorem cannot touch, because they
are not `C₂`-cofinite.  The library proves the two halves separately:

* `Modularity.AKModularODE.character_formalODE_of_etingofFinite` — the character ODE, from
  `EtingofFinite W`;
* `Examples.AffineSl2QuasiLisse.Sl2Presentation.etingofFinite` — `EtingofFinite W` from an
  `𝔰𝔩₂` symbol presentation, obtained **not** via `EtingofFinite_of_C2Cofinite` but by spanning
  `A₂(W)` with Poisson brackets plus the three classes `[1]`, `[h²]`, `[ef]`;
* `Examples.AffineSl2QuasiLisse.Sl2Presentation.not_C2Cofinite` — from the *same* bundle plus
  `IsExact`, the VOA is **not** `C₂`-cofinite.

This file states the composition.

## The constructed presentation, and what is still an implication

**`Sl2Presentation simpleSl2QL` is constructed**, in `Examples.AffineSl2Presentation`
(`Sl2Pres.sl2PresentationSimpleSl2QL`), `pbw`-free.  The unconditional consequences — the
Arakawa–Kawasetsu character ODE for `L_{-4/3}(𝔰𝔩₂)` and `EtingofFinite (L_{-4/3}(𝔰𝔩₂))` — are
collected in `Modularity.AKSl2Instance`.  The theorems in *this* file remain stated over an
arbitrary `Sl2Presentation W`, which is what makes them reusable; they are not vacuous.

**What is still an implication: the `IsExact` half.**  `IsExact` is *not* discharged.  It is the
named hypothesis `Sl2Pres.Sl2ExactSymbol`.  ⚠ It is **not** Arakawa's theorem: Arakawa's
associated-variety theorem `X_{L_k(𝔰𝔩₂)} = 𝒩` determines only the *radical* of the symbol ideal,
whereas `IsExact` asserts the ideal is exactly `Cas·𝔪`.  Therefore every theorem below whose
statement contains `hex : P.IsExact` is still conditional.

Non-lisseness itself does not need `IsExact`: `¬ C2Cofinite (L_{-4/3}(𝔰𝔩₂))` is
proved unconditionally as `Sl2NonLisse.not_C2Cofinite_simpleSl2QL`
(`Examples/AffineSl2NonLisse.lean`).  So `L_{-4/3}(𝔰𝔩₂)` *is* a non-lisse instance of the
(formal, near-vacuous; see `Modularity.AKModularODE`) character ODE.

⚠ The obstruction to `IsExact` is *only* the lower bound.  The *surjectivity* of the symbol map
needs no new PBW input: `Sl2Pres.symbolAlg_surjective` proves it `pbw`-free.

The obstruction to constructing `IsExact` is recorded at
`Examples.AffineSl2QuasiLisse` §"Status" and in `Examples.AffineSl2Symbol`: it is the statement
`A₂(L_{-4/3}(𝔰𝔩₂)) ≅ Sym(𝔰𝔩₂)/Cas·𝔪` (stronger than Arakawa's theorem, which gives the radical), a
*lower* bound on `A₂` of the **simple** quotient, and
neither field of the theorem `VOA.pbw` (`affineVacuum`, `inducedBottom`) yields
the linear independence of creation monomials it needs.

## ⚠ The three gaps of `Modularity.AKModularODE` are carried forward unchanged

The conclusion below is AK's equation (2) in **formal `q`-series** form.  It is **not** AK Theorem
5.1 and **not** a modular linear differential equation:

1. the basis is the Euler operator `(q d/dq)^i`, not AK's iterated Serre derivative `∂^i`;
2. the coefficients are **subexponential** power series (`SubexpPS`), not AK's `A = ℂ[G̃₄,G̃₆]`;
   `θ`-stability of the Eisenstein ring is Ramanujan's identities, which are not formalized here;
3. nothing is proved about modularity of the coefficients, about an analytic limit `p_i(τ)`, about
   the operators `ϑ_Δ` on `ℍ`, or about the span of characters being an `SL₂(ℤ)`-representation.

`EtingofFinite` also remains an axiomatized hypothesis standing in for AK Theorem 2.2
(Etingof–Schedler); it is not derived from quasi-lisseness here.

## Main results

* `vacuumGradeZero_of_vacuum_grade` — `VacuumGradeZero W` holds for **every** vertex operator
  algebra, since it is the VOA4 field `vacuum_grade` weakened to `≤`;
* `character_formalODE_of_sl2Presentation` — the character ODE from an `𝔰𝔩₂` presentation
  alone (`pbw`-free);
* `character_formalODE_of_non_lisse` — **the main result**: `¬ C2Cofinite W` **and** the character
  ODE, from the same hypothesis bundle (`pbw`-free);
* `uniform_order_character_formalODE_of_non_lisse` — the same with the order of the ODE fixed
  before the module, via `Modularity.AKUniformODE` (`pbw`-free);
* `character_formalODE_adjoint_of_non_lisse_simpleSl2QL` — the flagship, at
  `L_{-4/3}(𝔰𝔩₂)`.  ⚠ This one **uses the theorem `VOA.pbw`**,
  through `QuasiLisseSl2.vacuum_simpleSl2QL_ne_zero`.

## Status
Proved, no `sorry`.  The `Sl2Presentation` hypothesis is **discharged** at `L_{-4/3}(𝔰𝔩₂)` in
`Examples.AffineSl2Presentation`; the `IsExact` hypothesis is **not** discharged anywhere.  So the
results with `hex : P.IsExact` are conditional and the others are not.  Everything except
`character_formalODE_adjoint_of_non_lisse_simpleSl2QL` (and `character_formalODE_simpleSl2QL`) is
`pbw`-free; the `pbw`-free replacements for those two live in `Modularity.AKSl2Instance`.
-/

namespace VOA.QuasiLisseSl2

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- `VacuumGradeZero W` is not an extra hypothesis: it is the VOA4 field
`VertexOperatorAlgebra.vacuum_grade : grading 0 = ℂ ∙ vacuum` weakened from `=` to `≤`.

This lets the theorems below drop the `hzero` argument that
`Modularity.AKModularODE.character_formalODE_of_etingofFinite` carries.  (Upstream statements keep
their `hzero` argument.) -/
theorem vacuumGradeZero_of_vacuum_grade (W : VertexOperatorAlgebra 𝒱) : VacuumGradeZero W :=
  le_of_eq W.vacuum_grade

section Payoff

variable {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- **The character ODE from an `𝔰𝔩₂` symbol presentation.**  `Sl2Presentation.etingofFinite`
supplies `EtingofFinite W` without any appeal to `C₂`-cofiniteness, so this is a genuine
Arakawa–Kawasetsu statement rather than a rerun of Zhu.

`Sl2Presentation` is inhabited at `L_{-4/3}(𝔰𝔩₂)` (`Sl2Pres.sl2PresentationSimpleSl2QL`), so
this is not an implication over an uninhabited structure; the unconditional instance is
`Sl2Pres.character_formalODE_module_simpleSl2QL`.  See the file header.

⚠ Formal `q`-series identity in the `(q d/dq)^i` basis with subexponential coefficients; **not** a
modular linear differential equation.  See the file header. -/
theorem character_formalODE_of_sl2Presentation (W : VertexOperatorAlgebra 𝒱)
    (P : Sl2Presentation W) (N : OrdVModule W M) {hw : ℂ} (hcw : HasConformalWeight N hw) :
    ∃ (s : ℕ) (g : ℕ → ℕ → ℂ), 1 ≤ s ∧ (∀ i, Subexponential (fun k => ‖g i k‖)) ∧
      ∀ e : ℂ, (qDeriv^[s] (torusPartition N)) e
        + ∑ i ∈ Finset.range s, qConv (g i) (qDeriv^[i] (torusPartition N)) e = 0 :=
  character_formalODE_of_etingofFinite W N hcw (vacuumGradeZero_of_vacuum_grade W) P.etingofFinite

/-- **THE ARAKAWA–KAWASETSU PAYOFF.**  From one hypothesis bundle — an `𝔰𝔩₂` symbol
presentation of `A₂(W)` that is exact — both halves follow at once:

* `W` is **not** `C₂`-cofinite, so Zhu's modularity theorem does not apply to it; and
* the normalised character of **every** ordinary `W`-module with a conformal weight nevertheless
  satisfies a monic linear ODE in `q d/dq` with subexponential coefficients.

The second half is a formal `q d/dq`-equation, not a modular linear differential equation, and is
near-vacuous (see `Modularity.AKModularODE`).

⚠⚠ `Sl2Presentation` **is** inhabited at `L_{-4/3}(𝔰𝔩₂)` (`Sl2Pres.sl2PresentationSimpleSl2QL`),
but `IsExact` is **not** discharged anywhere (`Sl2Pres.Sl2ExactSymbol`; stronger than Arakawa's
associated-variety theorem, which gives only the radical).  At `L_{-4/3}(𝔰𝔩₂)` both conjuncts hold
without it: `Sl2NonLisse.not_C2Cofinite_simpleSl2QL` and
`Sl2Pres.character_formalODE_simpleSl2QL_uncond`.

⚠ Formal `q`-series identity, **not** AK Theorem 5.1 and **not** a modular linear differential
equation: `(q d/dq)^i` basis, `SubexpPS` coefficients, nothing proved about modularity.  See the
file header for the three precise gaps. -/
theorem character_formalODE_of_non_lisse (W : VertexOperatorAlgebra 𝒱)
    (P : Sl2Presentation W) (hex : P.IsExact)
    (N : OrdVModule W M) {hw : ℂ} (hcw : HasConformalWeight N hw) :
    ¬ C2Cofinite W ∧
      ∃ (s : ℕ) (g : ℕ → ℕ → ℂ), 1 ≤ s ∧ (∀ i, Subexponential (fun k => ‖g i k‖)) ∧
        ∀ e : ℂ, (qDeriv^[s] (torusPartition N)) e
          + ∑ i ∈ Finset.range s, qConv (g i) (qDeriv^[i] (torusPartition N)) e = 0 :=
  ⟨P.not_C2Cofinite hex, character_formalODE_of_sl2Presentation W P N hcw⟩

end Payoff

/-- **The character ODE with a module-independent order.**  `Modularity.AKUniformODE` fixes the
order `s` before any module is mentioned, so the statement below reads: *`W` is not `C₂`-cofinite,
and there is a single order `s ≥ 1` at which the character of every ordinary `W`-module satisfies a
monic linear ODE in `q d/dq`.*

⚠ Only the **order** is uniform; the coefficients `g` are still chosen after the module.  See the
header of `Modularity.AKUniformODE` for exactly why, and for what a block-independent AK Lemma 5.5
would take.

⚠⚠ Conditional on `IsExact`, which is undischarged (`Sl2Pres.Sl2ExactSymbol`).  At
`L_{-4/3}(𝔰𝔩₂)` both halves hold without it (`Sl2NonLisse.not_C2Cofinite_simpleSl2QL`,
`Sl2Pres.uniform_order_character_formalODE_simpleSl2QL`).  The ODE is formal and near-vacuous
(see `Modularity.AKModularODE`). -/
theorem uniform_order_character_formalODE_of_non_lisse (W : VertexOperatorAlgebra 𝒱)
    (P : Sl2Presentation W) (hex : P.IsExact) :
    ¬ C2Cofinite W ∧
      ∃ s : ℕ, 1 ≤ s ∧
        ∀ {M : Type u} [AddCommGroup M] [Module ℂ M] (N : OrdVModule W M) (hw : ℂ),
          HasConformalWeight N hw →
            ∃ g : ℕ → ℕ → ℂ, (∀ i, Subexponential (fun k => ‖g i k‖)) ∧
              ∀ e : ℂ, (qDeriv^[s] (torusPartition N)) e
                + ∑ i ∈ Finset.range s,
                    qConv (g i) (qDeriv^[i] (torusPartition N)) e = 0 :=
  ⟨P.not_C2Cofinite hex,
    uniform_order_character_formalODE_of_etingofFinite W
      (vacuumGradeZero_of_vacuum_grade W) P.etingofFinite⟩

/-! ## The flagship: `L_{-4/3}(𝔰𝔩₂)` -/

/-- **`EtingofFinite (L_{-4/3}(𝔰𝔩₂))`**, unconditionally and `pbw`-free, through the
constructed presentation `Sl2Pres.sl2PresentationSimpleSl2QL` (`Sl2Pres.etingofFinite_simpleSl2QL'`).
No presentation argument is needed. -/
theorem etingofFinite_simpleSl2QL : EtingofFinite simpleSl2QL :=
  Sl2Pres.etingofFinite_simpleSl2QL'

/-- **`L_{-4/3}(𝔰𝔩₂)` is not `C₂`-cofinite**, unconditionally: this is
`Sl2NonLisse.not_C2Cofinite_simpleSl2QL`.  Neither a presentation `S` nor
the undischarged exactness hypothesis `S.IsExact` is needed. -/
theorem not_C2Cofinite_simpleSl2QL : ¬ C2Cofinite simpleSl2QL :=
  Sl2NonLisse.not_C2Cofinite_simpleSl2QL

/-- The finite-dimensional Poisson trace space of `L_{-4/3}(𝔰𝔩₂)`, unconditionally, with no
presentation argument. -/
theorem finiteDimensional_poissonTraces_simpleSl2QL :
    FiniteDimensional ℂ (poissonTraces simpleSl2QL) :=
  Sl2Pres.finiteDimensional_poissonTraces_simpleSl2QL'

/-- **The Arakawa–Kawasetsu witness at `k = -4/3`**, unconditionally: `L_{-4/3}(𝔰𝔩₂)` is NOT
`C₂`-cofinite and DOES satisfy the Etingof–Schedler finiteness hypothesis
(`Sl2NonLisse.strictEtingofFinite_simpleSl2QL`).  Neither a presentation `S` nor
`S.IsExact` is needed. -/
theorem quasiLisseWitness_simpleSl2QL : ¬ C2Cofinite simpleSl2QL ∧ EtingofFinite simpleSl2QL :=
  ⟨not_C2Cofinite_simpleSl2QL, etingofFinite_simpleSl2QL⟩

/-- **The character ODE for the adjoint module of `L_{-4/3}(𝔰𝔩₂)`**, unconditionally and
`pbw`-free: the nonzero vacuum comes from `Sl2Pres.vacuum_simpleSl2QL_ne_zero'` (Wakimoto) and
`EtingofFinite` from the constructed presentation.  No presentation argument is needed, and
the vacuum does not go through `vacuum_simpleSl2QL_ne_zero` (which uses `VOA.pbw`).  Same
statement as `Sl2Pres.character_formalODE_simpleSl2QL_uncond`.

⚠ Formal `q`-series identity in the `(q d/dq)^i` basis with subexponential coefficients; **not** a
modular linear differential equation, and near-vacuous (see `Modularity.AKModularODE`). -/
theorem character_formalODE_simpleSl2QL :
    ∃ (s : ℕ) (g : ℕ → ℕ → ℂ), 1 ≤ s ∧ (∀ i, Subexponential (fun k => ‖g i k‖)) ∧
      ∀ e : ℂ, (qDeriv^[s] (torusPartition (adjointModule simpleSl2QL))) e
        + ∑ i ∈ Finset.range s,
            qConv (g i) (qDeriv^[i] (torusPartition (adjointModule simpleSl2QL))) e = 0 :=
  character_formalODE_adjoint_of_etingofFinite simpleSl2QL Sl2Pres.vacuum_simpleSl2QL_ne_zero'
    (vacuumGradeZero_of_vacuum_grade simpleSl2QL) etingofFinite_simpleSl2QL

/-- **The non-lisse character ODE at `L_{-4/3}(𝔰𝔩₂)`, unconditionally.**  The vertex operator
algebra `L_{-4/3}(𝔰𝔩₂)`
is **not** `C₂`-cofinite (`Sl2NonLisse.not_C2Cofinite_simpleSl2QL`), and its own character
`tr_V q^{L₀−c/24}` satisfies a monic linear ODE in `q d/dq` with subexponential coefficients
(`character_formalODE_simpleSl2QL`).  `pbw`-free.  No `𝔰𝔩₂` presentation
`P`, no exactness `P.IsExact` (the undischarged `Sl2Pres.Sl2ExactSymbol`) and no `VOA.pbw` is
needed.

⚠ Formal `q`-series identity, not AK Theorem 5.1 and not a modular linear differential equation;
near-vacuous (see `Modularity.AKModularODE`). -/
theorem character_formalODE_adjoint_of_non_lisse_simpleSl2QL :
    ¬ C2Cofinite simpleSl2QL ∧
      ∃ (s : ℕ) (g : ℕ → ℕ → ℂ), 1 ≤ s ∧ (∀ i, Subexponential (fun k => ‖g i k‖)) ∧
        ∀ e : ℂ, (qDeriv^[s] (torusPartition (adjointModule simpleSl2QL))) e
          + ∑ i ∈ Finset.range s,
              qConv (g i) (qDeriv^[i] (torusPartition (adjointModule simpleSl2QL))) e = 0 :=
  ⟨not_C2Cofinite_simpleSl2QL, character_formalODE_simpleSl2QL⟩

end VOA.QuasiLisseSl2
