/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.OmegaCentral
import VOA.Modules.ZhuVermaAnArchZhu534
import VOA.Modularity.ZhuAlgebraFinite

/-!
# Residual **(b)** reduced to the `OrdVModule.finrank` obligation alone

`Modules.ZhuVermaAnArchZhu534.djIrrRealization` already builds Dong–Jiang's `L(U)` as an
`IrrRealization W U`. It carries five inputs: the explicit `regularAMod` `BottomProjection`
hypothesis `Pr` (already a hypothesis of the modularity theorem),
`hU : Nontrivial U.carrier`, the grading scalar `hval`/`hL0`, the
`OrdVModule.finrank` obligation `hfin`, and `hsimple`.

Of these, three are theorems:

* `hU` is `hsimple.1`;
* `hval` comes from `Modularity.OmegaCentral.exists_omegaScalar_of_isSimpleAMod` — `[ω]` is
  central in `A(𝒱)` and `U` is simple and finite-dimensional (the latter free from `C₂` via
  `finiteDimensional_A_of_C2Cofinite`), so Schur gives the scalar;
* `hL0` comes from `Modularity.HL0Scoped.genHL0`, which needs only that scalar.

**Thus, after the standing explicit `BottomProjection` assumption `Pr`, residual (b) is exactly
the weight-space finiteness of `L(U)`.**

## Main result

* `simpleAModsRealized_of_finiteWeights` — `SimpleAModsRealized W` from `hfin`.

## Status
Proof-term `#print axioms`-clean and `pbw`-free, no `sorry`. `hfin` and the explicit
`BottomProjection` assumption `Pr` are named hypotheses, carried explicitly. The project-level
`regularAMod` witness is supplied by `voaPBWBottomProjection`, from the generic relative-induction
field of the theorem `VOA.pbw : PBWPrinciple`. This is a
reduction of (b), *not* an unconditional discharge.
-/

namespace VOA

open VHat VHat.DLM3

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- **Residual (b), reduced to `hfin`.**  Every simple `A(𝒱)`-module is the bottom of an
irreducible lowest-weight `𝒱`-module, provided the induced module `L(U)` has finite-dimensional
weight spaces. -/
theorem simpleAModsRealized_of_finiteWeights {W : VertexOperatorAlgebra 𝒱}
    (hfd : letI := instRingA W; FiniteDimensional ℂ (A W))
    (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W)))
    (hfin : ∀ (U : AMod W) (hs : IsSimpleAMod U) (hval : ℂ)
      (hL0 : ∀ (n : ℕ) (x : DJCarrier W U.toAmModZero), x ∈ DJCarrier.deg W U.toAmModZero n →
        djModeZero W U.toAmModZero 1 W.conformalVector x = (hval + (n : ℂ)) • x),
      (djLU Pr U.toAmModZero hs.1 hval hL0).FiniteWeights) :
    SimpleAModsRealized W := by
  intro U hs
  obtain ⟨hval, homega⟩ := exists_omegaScalar_of_isSimpleAMod hfd U hs
  exact ⟨djIrrRealization Pr U hs.1 hval (genHL0 U hval homega)
    (hfin U hs hval (genHL0 U hval homega)) hs⟩

/-- The `C₂`-cofinite form: `dim A(𝒱) < ∞` is free. -/
theorem simpleAModsRealized_of_finiteWeights_of_C2 {W : VertexOperatorAlgebra 𝒱}
    (hC2 : C2Cofinite W)
    (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W)))
    (hfin : ∀ (U : AMod W) (hs : IsSimpleAMod U) (hval : ℂ)
      (hL0 : ∀ (n : ℕ) (x : DJCarrier W U.toAmModZero), x ∈ DJCarrier.deg W U.toAmModZero n →
        djModeZero W U.toAmModZero 1 W.conformalVector x = (hval + (n : ℂ)) • x),
      (djLU Pr U.toAmModZero hs.1 hval hL0).FiniteWeights) :
    SimpleAModsRealized W :=
  simpleAModsRealized_of_finiteWeights (finiteDimensional_A_of_C2Cofinite W hC2) Pr hfin

end VOA
