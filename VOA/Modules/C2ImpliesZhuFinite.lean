/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.GNProp8Closure
import VOA.Modularity.StrictSpanning
import VOA.Modularity.Anm0FiniteDim

/-!
# `C₂`-cofiniteness discharges the whole Zhu-algebra finiteness tower

This file is the **single hub** for everything that the hypothesis `C2Cofinite W` alone buys
about finite-dimensionality of Zhu-type quotients of `𝒱`.  Every statement here has `C2Cofinite W`
as its *only* non-structural hypothesis; nothing is conditional on an unproved input.

## What was already in the repository

The headline implication `C2Cofinite W → FiniteDimensional ℂ (A W)` was **already proved**, in
`Modularity.ZhuAlgebraFinite.finiteDimensional_A_of_C2Cofinite`.  It does *not* go through finite
generation at all: it runs the degree induction of `Modularity.BlockRelSpanning` with the
relation module `O(𝒱)` in place of the deformed one, using `circ_n_mem_O` at `n = 0`,

  `a ∘ b = ∑_{i=0}^{wt a} C(wt a, i) · a₍ᵢ₋₂₎b ∈ O(𝒱)`,

whose `i = 0` term is `a₍₋₂₎b` and whose `i ≥ 1` terms have strictly lower conformal weight.  So
`C₂(𝒱) = O₂(𝒱)` is absorbed into lower degrees modulo `O(𝒱)`, and the `C₂`-generators span `𝒱`
modulo `O(𝒱)`.  It is restated below as `zhuAlgebra_finiteDimensional_of_C2Cofinite` so that this
file states its nominal goal explicitly; the proof is the existing one, and the alias adds no
hypotheses.

⚠ The `Modules.C2Cofinite` docstring's finite-generation target `5.3.11a` is also proved, in
`Modules.FiniteGenerationProof.iterProdSpan_eq_top`, but it is **not needed** for the headline.

## What is new here

The consumers `Examples.TripletW2Log` and `Examples.ZhuTripletW2Alt` carry **two** finiteness
hypotheses side by side, `hA : FiniteDimensional ℂ (A 𝒱)` and
`hAnm : ∀ n, FiniteDimensional ℂ (AnmFull 𝒱 n 0)`.  Only the first was discharged.  The second
needs `C_{n+2}`-cofiniteness (`Modularity.Anm0FiniteDim`), which is a *stronger* condition than
`C₂`-cofiniteness on its face, since `C_{m+1}(𝒱) ⊆ C_m(𝒱)`.

The missing bridge is Gaberdiel–Neitzke `hep-th/0009235` Prop. 8 + Thm 11, and **both halves are
in the repository**:

* `Modularity.GNProp8Closure.strictSpanning_of_C2Cofinite` — Prop. 8: `C₂`-cofiniteness produces
  a `StrictSpanning W` datum (spanning mode words with `N₁ > N₂ > ⋯ > N_k > 0`);
* `Modularity.StrictSpanning.cofinite_of_strictSpanning` — Thm 11: strict decrease bounds the
  word length by `N₁`, so the words surviving modulo `C_m(𝒱)` form a finite set.

They had never been composed.  Composing them gives `C₂`-cofinite ⟹ `C_m`-cofinite for every
`m ≥ 1`, and hence the entire finiteness tower.

⚠ **Correction to a stale docstring.**  `Modularity.BuhlSpanningC2` states "GN Prop. 8 is not in
this repository" and warns against using its own (weakly decreasing) ordered spanning to obtain
`C_m`-cofiniteness.  The *warning* is correct — `BuhlSpanningC2`'s datum really is too weak — but
the *claim* is out of date: `GNProp8Closure` supplies the strict-decrease datum.  This file
uses `GNProp8Closure`, never `BuhlSpanningC2`.

## Main results

* `zhuAlgebra_finiteDimensional_of_C2Cofinite` — the nominal goal,
  `C2Cofinite W → FiniteDimensional ℂ (A W)` (alias of the existing proof, no extra hypotheses);
* `exists_finset_span_sup_CGen_of_C2Cofinite` — `C₂`-cofinite ⟹ for every `m ≥ 1` a *finite
  homogeneous* family spanning `𝒱` modulo `C_m(𝒱)`;
* `finiteDimensional_quot_CGen_of_C2Cofinite` — hence `C₂`-cofinite ⟹ `C_m`-cofinite;
* `finiteDimensional_An_of_C2Cofinite` — Frenkel–Zhu `dim A_n(𝒱) < ∞`;
* `finiteDimensional_AnmFull_of_C2Cofinite` — Dong–Jiang `dim A_{n,0}(𝒱) < ∞`, the
  hypothesis `hAnm`;
* `zhuFinitenessPackage_of_C2Cofinite` — the pair `(hAnm, hA)` in exactly the order the
  consumers take it;
* `finiteDimensional_DJPiece_of_C2Cofinite` — the Dong–Jiang level pieces of `M(U)`.

## Status
Proved, axiom-clean, `pbw`-free, no `sorry`, no new axioms.  `#print axioms` on every declaration
below (and on `finiteDimensional_A_of_C2Cofinite` and `strictSpanning_of_C2Cofinite`, the two
imported inputs that carry the real content) returns exactly
`[propext, Classical.choice, Quot.sound]`.

⚠ This file lives in `Modules/` (as its task specified) but imports `Modularity/`; two `Modules/`
files (`ModuleRestrict`, `PoissonTrace`) already do the same, so the dependency is not new.
-/

namespace VOA

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The nominal goal -/

/-- **`C₂`-cofinite ⟹ Zhu's algebra `A(𝒱) = 𝒱/O(𝒱)` is finite-dimensional.**

This is the goal of this file, stated with `C2Cofinite W` as its only hypothesis and with `A W`
unweakened.  The proof is `Modularity.ZhuAlgebraFinite.finiteDimensional_A_of_C2Cofinite`, which
was already in the repository; this alias exists so that the statement has a home in `Modules/`
and so that the `C₂`-discharge hub below is complete. -/
theorem zhuAlgebra_finiteDimensional_of_C2Cofinite (W : VertexOperatorAlgebra 𝒱)
    (hC2 : C2Cofinite W) : FiniteDimensional ℂ (A W) :=
  finiteDimensional_A_of_C2Cofinite W hC2

/-! ## `C₂`-cofinite ⟹ `C_m`-cofinite (Gaberdiel–Neitzke Prop. 8 + Thm 11, composed) -/

/-- **`C₂`-cofiniteness gives a finite homogeneous spanning family modulo `C_m(𝒱)`, for every
`m ≥ 1`.**

The composite of the two halves of Gaberdiel–Neitzke that the repository already proves
separately: `strictSpanning_of_C2Cofinite` (Prop. 8) produces spanning mode words with strictly
decreasing positive mode indices, and `cofinite_of_strictSpanning` (Thm 11) observes that a word
whose outermost index is `≥ m` lies in `C_m(𝒱)`, while strict decrease confines the survivors to
pairwise distinct indices in `[1, m−1]` — hence to length `< m`, hence to a finite set. -/
theorem exists_finset_span_sup_CGen_of_C2Cofinite (W : VertexOperatorAlgebra 𝒱)
    (hC2 : C2Cofinite W) (m : ℕ) (hm : 1 ≤ m) :
    ∃ S : Finset 𝒱, (∀ s ∈ (S : Set 𝒱), IsHomog W s) ∧
      (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ (S : Set 𝒱) ⊔ CGen W (-(m : ℤ)) :=
  cofinite_of_strictSpanning (strictSpanning_of_C2Cofinite W hC2) m hm

/-- **`C₂`-cofinite ⟹ `C_m`-cofinite** for every `m ≥ 1`: `dim 𝒱/C_m(𝒱) < ∞`.

Note `m = 2` recovers `C2Cofinite` itself (`CGen W (-2) = O₂ W` by `CGen_neg_two`), and the
containments `C_{m+1}(𝒱) ⊆ C_m(𝒱)` (`CGen_succ_le`) make the statement progressively stronger as
`m` grows. -/
theorem finiteDimensional_quot_CGen_of_C2Cofinite (W : VertexOperatorAlgebra 𝒱)
    (hC2 : C2Cofinite W) (m : ℕ) (hm : 1 ≤ m) :
    FiniteDimensional ℂ (𝒱 ⧸ CGen W (-(m : ℤ))) := by
  obtain ⟨S, _, htop⟩ := exists_finset_span_sup_CGen_of_C2Cofinite W hC2 m hm
  exact (finiteDimensional_and_finrank_quot_le_of_span_sup S htop).1

/-! ## The Zhu-algebra tower -/

/-- **`C₂`-cofinite ⟹ `dim A_n(𝒱) < ∞`** for the Frenkel–Zhu algebras `A_n(𝒱) = 𝒱/O_n(𝒱)`.

`Modularity.AnFiniteDim.finiteDimensional_An_of_cofinite` needs `C_{2n+2}`-cofiniteness (the pole
of `circ W n` is `2n+2`); `exists_finset_span_sup_CGen_of_C2Cofinite` supplies it at `m = 2n+2`. -/
theorem finiteDimensional_An_of_C2Cofinite (W : VertexOperatorAlgebra 𝒱)
    (hC2 : C2Cofinite W) (n : ℕ) : FiniteDimensional ℂ (An W n) := by
  obtain ⟨S, hShom, htop⟩ :=
    exists_finset_span_sup_CGen_of_C2Cofinite W hC2 (2 * n + 2) (by omega)
  refine (finiteDimensional_An_of_cofinite W n S hShom ?_).1
  rwa [show -((2 * n + 2 : ℕ) : ℤ) = -2 * (n : ℤ) - 2 by push_cast; ring] at htop

/-- **`C₂`-cofinite ⟹ `dim A_{n,0}(𝒱) < ∞`** for the Dong–Jiang bimodules
`A_{n,0}(𝒱) = 𝒱/O_{n,0}^{full}(𝒱)`.

This is the hypothesis carried as `hAnm : ∀ n, FiniteDimensional ℂ (AnmFull 𝒱 n 0)` throughout
`Examples.TripletW2Log` and `Examples.ZhuTripletW2Alt`.
`Modularity.Anm0FiniteDim.finiteDimensional_AnmFull_of_cofinite` needs `C_{n+2}`-cofiniteness (the
pole of `anmCirc W n 0` is `n+2`); `exists_finset_span_sup_CGen_of_C2Cofinite` supplies it at
`m = n+2`. -/
theorem finiteDimensional_AnmFull_of_C2Cofinite (W : VertexOperatorAlgebra 𝒱)
    (hC2 : C2Cofinite W) (n : ℕ) : FiniteDimensional ℂ (AnmFull W n 0) := by
  obtain ⟨S, hShom, htop⟩ :=
    exists_finset_span_sup_CGen_of_C2Cofinite W hC2 (n + 2) (by omega)
  refine (finiteDimensional_AnmFull_of_cofinite W n S hShom ?_).1
  rwa [show -((n + 2 : ℕ) : ℤ) = -((n : ℤ) + 2) by push_cast; ring] at htop

/-! ## The package the `W(2)` consumers take -/

/-- **Both finiteness hypotheses of the logarithmic-module construction, from `C₂` alone.**

`Examples.TripletW2Log.omegaJordanLogVModule` and its `W(2)` specialisations
(`TripletW2Log.lean:620,628,636`), together with
`Examples.ZhuTripletW2Alt.tripletW2Log_L0nil_ne_zero_of_jordanVector` and
`..._of_zhuMul` (`ZhuTripletW2Alt.lean:334,343`), each carry the pair

  `hAnm : ∀ n : ℕ, FiniteDimensional ℂ (AnmFull 𝒱 n 0)`  and  `hA : FiniteDimensional ℂ (A 𝒱)`.

This theorem produces that pair, in that order, from `C2Cofinite W`.  It is stated for a general
`W` on purpose: those files are not edited or imported here, and once `C2Cofinite tripletW2` is
available it instantiates at `W := tripletW2` with no further work.

⚠ The remaining hypothesis `hgate : DJAnnEqAn 𝒱 0` of those consumers is **not** discharged by
`C₂`-cofiniteness and is untouched here. -/
theorem zhuFinitenessPackage_of_C2Cofinite (W : VertexOperatorAlgebra 𝒱) (hC2 : C2Cofinite W) :
    (∀ n : ℕ, FiniteDimensional ℂ (AnmFull W n 0)) ∧ FiniteDimensional ℂ (A W) :=
  ⟨finiteDimensional_AnmFull_of_C2Cofinite W hC2, zhuAlgebra_finiteDimensional_of_C2Cofinite W hC2⟩

/-- **The Dong–Jiang level pieces of the induced module are finite-dimensional.**
`DJPiece W U n = A_{n,0}(𝒱) ⊗_{A(𝒱)} U`, so `C₂`-cofiniteness plus finite-dimensionality of the
bottom `U` is enough. -/
theorem finiteDimensional_DJPiece_of_C2Cofinite {W : VertexOperatorAlgebra 𝒱}
    (hC2 : C2Cofinite W) (U : AmMod W 0) (n : ℕ) (hU : FiniteDimensional ℂ U.carrier) :
    FiniteDimensional ℂ (DJPiece W U n) :=
  finiteDimensional_DJPiece U n (finiteDimensional_AnmFull_of_C2Cofinite W hC2 n) hU

end VOA
