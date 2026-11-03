/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.BlockRelSpanTransport
import VOA.Modularity.CuspPoint
import VOA.Modularity.BlockFiniteDim
import VOA.Modularity.ZhuAlgebraFinite
import VOA.Modularity.SymmetricFunctionals

/-!
# Arike–Nagatomo Theorem 3.3.6 — `dim 𝒞₁(𝒱) ≤ dim SLF(A(𝒱))` for any `C₂`-cofinite `𝒱`

`Modularity.ZhuBlockCount` proves `dim 𝔅 ≤ #Φ(𝒱)`, Zhu's Theorem 5.3.3.  That statement is
**rational**: its proof passes through Artin–Wedderburn for `A(𝒱)` and therefore carries the
hypotheses `IsSemisimpleRing (A 𝒱)`, `SimpleAModsRealized 𝒱`, `Finite (Φ 𝒱)` and a
`BottomProjection`.

This file removes **all four**.  The bound proved here is

  `dim 𝔅 ≤ dim (A(𝒱) ⧸ [A(𝒱), A(𝒱)]) = dim SLF(A(𝒱))`,

under the hypotheses `VacuumGradeZero 𝒱` and `C2Cofinite 𝒱` and *nothing else*.  This is

> Y. Arike and K. Nagatomo, *Some remarks on pseudo-trace functions for orbifold models associated
> with symplectic fermions*, Internat. J. Math. **24** (2013), no. 2, 1350008, **Theorem 3.3.6**,

with `SLF(A(𝒱))` the space of **symmetric linear functionals** `φ(ab) = φ(ba)` on Zhu's algebra.
It is the first *sharp* bound on the genus-one block space in this library that does not assume
rationality.

⚠ Novelty, calibrated.  Mere **finiteness** of the block space without rationality was already
four lines away: composing `BlockRelSpanning.exists_finset_span_sup_blockRelSpan` (hypotheses
`hzero + hC2` only) with `BlockFiniteDim.finrank_analyticBlocks_le_card_of_blockRel` gives a
rationality-free, `pbw`-free finiteness-plus-bound directly.  So
`finiteDimensional_analyticBlocks_of_C2Cofinite` below is a convenience projection, not new
content.  What is genuinely new is the **right-hand side**: that prior-art route bounds the block
space by "number of `C₂`-generators plus one", a crude quantity with no intrinsic meaning, whereas
`dim SLF(A(𝒱))` is the literature's own answer.  Getting from the former to the latter is the
content of this file.

⚠ Also note what this is *not*: an upper bound on a dimension, not a modular-invariance statement,
and — as of this writing — instantiated only at `trivialVOA`, for which `trivial_semisimpleA`
proves `IsSemisimpleRing (A trivialVOA)`.  The sole witness is therefore a *rational* one; no
non-rational witness exists in the library until `C2Cofinite` is proved for a logarithmic example
such as `tripletW2`.

## Why the semisimplicity disappears

Only one step of the Zhu chain used it, and only to *evaluate* a dimension.  Zhu's count at the
cusp (`Modularity.ZhuCount`, `Modularity.ZhuCountC2`) does not stop at
`dim (𝒱 ⧸ blockRelSpanAtCusp 𝒱) = dim (A(𝒱) ⧸ [A(𝒱), A(𝒱)])` — which is
`finrank_quot_blockRelSpanAtCusp_eq` and needs only `VacuumGradeZero` — but goes on to identify
the right-hand side with `#Φ(𝒱)` through Artin–Wedderburn.  Stopping one step earlier, at
`CuspPoint.exists_finset_span_sup_blockRelSpanAtCusp`, keeps the whole remaining chain (Nakayama
transport into `ℍ`, then the dual descent) intact and hypothesis-free.  On the algebra side,
`Modularity.SymmetricFunctionals` supplies `symmetricFunctionals ≃ (A ⧸ [A,A])*` for a completely
arbitrary algebra, so the commutator quotient may be renamed `SLF(A(𝒱))` at no cost.

## Main results

* `exists_interior_span_sup_blockRelSpan_of_C2` — a spanning family at an interior point of
  size `≤ dim (A(𝒱) ⧸ [A(𝒱), A(𝒱)])`, from `hzero + hC2` alone.
* `finrank_analyticBlocks_le_finrank_quot_commSpan` — the bound in commutator-quotient form,
  together with finite-dimensionality of the block space.
* `finrank_analyticBlocks_le_finrank_symmetricFunctionals` — **Arike–Nagatomo Theorem
  3.3.6**, `dim 𝒞₁(𝒱) ≤ dim SLF(A(𝒱))`.
* `finiteDimensional_analyticBlocks_of_C2Cofinite` — the finiteness half on its own.

## ⚠ What this does and does not achieve

It is **the upper-bound half only** of the non-rational modular-invariance picture.  Miyamoto's
theorem (Duke Math. J. **122** (2004) 51–91) asserts in addition that pseudo-trace functions
*span* `𝒞₁(𝒱)`, i.e. the matching **lower** bound `dim 𝒞₁(𝒱) ≥ dim SLF(A(𝒱))` and hence equality.
That spanning statement is **not** proved here and is not a corollary of anything here: it needs
the construction of pseudo-trace functions from generalized Verma modules over `A(𝒱)`, their
convergence, and their linear independence — a separate development of months, not days.  Nor is
the modular-invariance (`SL(2,ℤ)`-action) statement touched.

A second caution: Miyamoto's *published*
proof is incomplete — his Propositions 4.4, 4.5 and 4.6 are not proved there, and 4.6 has no proof
in the literature at all.  The theorem in this file is Arike–Nagatomo's and is **not** affected by
that gap: it depends on none of those propositions.

Finally, this bound says nothing about `C2Cofinite tripletW2`, which remains unproved in this
repository (it is Abe, Math. Z. **255** (2007), Theorem 3.10); logarithmic `tripletW2` statements
elsewhere in the library continue to carry `FiniteDimensional ℂ (A tripletW2)` as an explicit
hypothesis.

## Status
No `sorry`, no new axioms, and — the point of the exercise — **`VOA.pbw`-free**: the
theorem `VOA.pbw` entered the rational count only through
`voaPBWBottomProjection`, supplying the `BottomProjection` argument `Pr`, which no result in this
file takes.
-/

namespace VOA

open VHat VHat.DLM3 Module

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] (W : VertexOperatorAlgebra 𝒱)

/-- **A spanning family at an interior point, without semisimplicity.**

`𝒱` is spanned, modulo the block relations at some interior point `z₀ ∈ ℍ`, by at most
`dim (A(𝒱) ⧸ [A(𝒱), A(𝒱)])` vectors.

This is the `hss`-free replacement for
`Modularity.ZhuBlockCount.exists_interior_span_sup_blockRelSpan_card_le_Φ`: the cusp count is
stopped at the commutator quotient instead of being pushed through Artin–Wedderburn to `#Φ(𝒱)`,
after which the Nakayama transport `exists_interior_span_sup_blockRelSpan_of_cusp` applies
verbatim. -/
theorem exists_interior_span_sup_blockRelSpan_of_C2
    (hzero : VacuumGradeZero W) (hC2 : C2Cofinite W) :
    ∃ (T : Finset 𝒱) (z₀ : UpperHalfPlane),
      T.card ≤ (letI := instRingA W; letI := instAlgebraA W;
          finrank ℂ (A W ⧸ commSpan ℂ (A W))) ∧
        (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ (T : Set 𝒱) ⊔ blockRelSpan W (z₀ : ℂ) := by
  classical
  obtain ⟨T, hTcard, hTspan⟩ :=
    exists_finset_span_sup_blockRelSpanAtCusp (finiteDimensional_A_of_C2Cofinite W hC2)
  obtain ⟨z₀, hz₀⟩ :=
    exists_interior_span_sup_blockRelSpan_of_cusp W hzero hC2 (T : Set 𝒱) hTspan
  exact ⟨T, z₀, hTcard, hz₀⟩

/-- **The `C₂` block bound, in commutator-quotient form.**

For any `C₂`-cofinite `𝒱` with `VacuumGradeZero`, the genus-one block space is
finite-dimensional and

  `dim 𝔅 ≤ dim (A(𝒱) ⧸ [A(𝒱), A(𝒱)])`.

No semisimplicity of `A(𝒱)`, no realization hypothesis, no finiteness of `Φ(𝒱)` and no
`BottomProjection`.  See `finrank_analyticBlocks_le_finrank_symmetricFunctionals` for the same
statement written with the right-hand side in the literature's notation. -/
theorem finrank_analyticBlocks_le_finrank_quot_commSpan
    (hzero : VacuumGradeZero W) (hC2 : C2Cofinite W) :
    FiniteDimensional ℂ (Submodule.map restrictImGT (analyticBlocks W)) ∧
      finrank ℂ (Submodule.map restrictImGT (analyticBlocks W))
        ≤ (letI := instRingA W; letI := instAlgebraA W;
            finrank ℂ (A W ⧸ commSpan ℂ (A W))) := by
  obtain ⟨T, z₀, hTcard, hz₀⟩ := exists_interior_span_sup_blockRelSpan_of_C2 W hzero hC2
  obtain ⟨hfd, hle⟩ := finrank_analyticBlocks_le_card_of_blockRel (coe_mem_imGT_zero z₀) T hz₀
  exact ⟨hfd, le_trans hle hTcard⟩

/-- The finiteness half on its own: `C₂`-cofiniteness alone makes the block space
finite-dimensional.  (`Modularity.BlockFiniteDim` proves finite-dimensionality from a spanning
family; this records that `hzero + hC2` produce one.) -/
theorem finiteDimensional_analyticBlocks_of_C2Cofinite
    (hzero : VacuumGradeZero W) (hC2 : C2Cofinite W) :
    FiniteDimensional ℂ (Submodule.map restrictImGT (analyticBlocks W)) :=
  (finrank_analyticBlocks_le_finrank_quot_commSpan W hzero hC2).1

/-- **ARIKE–NAGATOMO, THEOREM 3.3.6.**

  `dim 𝒞₁(𝒱) ≤ dim SLF(A(𝒱))`

for **any** `C₂`-cofinite vertex operator algebra `𝒱` — rationality is *not* assumed.  Here
`𝒞₁(𝒱) = Submodule.map restrictImGT (analyticBlocks 𝒱)` is the space of genus-one conformal
blocks and `SLF(A(𝒱)) = symmetricFunctionals ℂ (A 𝒱)` is the space of symmetric linear
functionals `φ : A(𝒱) → ℂ` with `φ(ab) = φ(ba)`.

Reference: Y. Arike and K. Nagatomo, *Some remarks on pseudo-trace functions for orbifold models
associated with symplectic fermions*, Internat. J. Math. **24** (2013), no. 2, 1350008,
Theorem 3.3.6.

The proof is `finrank_analyticBlocks_le_finrank_quot_commSpan` together with the unconditional
`finrank_symmetricFunctionals_eq_finrank_quot_commSpan`, which identifies `dim SLF(A)` with
`dim (A ⧸ [A,A])` for an arbitrary algebra `A`.

⚠ This is the **upper** bound only.  The matching spanning statement — that pseudo-trace functions
exhaust `𝒞₁(𝒱)`, giving equality — is not proved in this library; see the module docstring. -/
theorem finrank_analyticBlocks_le_finrank_symmetricFunctionals
    (hzero : VacuumGradeZero W) (hC2 : C2Cofinite W) :
    finrank ℂ (Submodule.map restrictImGT (analyticBlocks W))
      ≤ (letI := instRingA W; letI := instAlgebraA W;
          finrank ℂ (symmetricFunctionals ℂ (A W))) := by
  letI := instRingA W
  letI := instAlgebraA W
  rw [finrank_symmetricFunctionals_eq_finrank_quot_commSpan]
  exact (finrank_analyticBlocks_le_finrank_quot_commSpan W hzero hC2).2

end VOA
