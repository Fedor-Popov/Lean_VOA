/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Examples.SympFermSuperC2
import VOA.Examples.SympFermSuperZhu

/-!
# The strict finite, non-semisimple super-Zhu benchmark

This file packages the unconditional algebraic endpoint for the genuine symplectic-fermion
super VOA.  It deliberately does not call the package `SuperStronglyFinite`: the repository has
no super analogues of the simplicity and self-contragredience predicates which are fields of the
bosonic `StronglyFinite`, and it has no admissible-super rationality theorem implying
semisimplicity of the super Zhu algebra.

What is proved is exactly the part needed as the integral-super strongly-finite-row benchmark:

* integral conformal weights;
* super `C₂`-cofiniteness;
* an honest associative super Zhu ring, finite-dimensional over `ℂ`;
* a nonzero square-zero two-sided ideal in that ring, hence non-semisimplicity.

The ideal clause is intentionally bundled, rather than replaced by the weaker assertion that the
ring contains a nonzero nilpotent element.
-/

namespace VOA

universe u

open GammaThetaStmt

variable {VType : Type u} [AddCommGroup VType] [Module ℂ VType]

/-- The exact finite super-Zhu package currently supported by the repository.

This is not a definition of `SuperStronglyFinite`: it contains neither simplicity nor
self-contragredience.  Its purpose is to keep the algebraic benchmark honest while those super
notions and the admissible-super rationality bridge are absent. -/
structure IntegralSuperC2FiniteZhuBenchmark (W : SuperVertexOperatorAlgebra VType)
    (hW : W.toSuperNearVOA.IntegralWeights) : Prop where
  /-- The super `C₂` quotient is finite-dimensional. -/
  c2Cofinite : SuperC2Cofinite W
  /-- The Dong–Zhao quotient carries its proved associative ring structure. -/
  zhuRingData : SuperZhuRingData W.toSuperNearVOA hW
  /-- Non-semisimplicity is witnessed by an actual nonzero square-zero two-sided ideal. -/
  squareZeroIdeal :
    letI := zhuRingData.AsRing
    ∃ I : TwoSidedIdeal (W.toSuperNearVOA.superA hW), I ≠ ⊥ ∧
      ∀ {x y : W.toSuperNearVOA.superA hW}, x ∈ I → y ∈ I → x * y = 0

namespace IntegralSuperC2FiniteZhuBenchmark

variable {W : SuperVertexOperatorAlgebra VType}
  {hW : W.toSuperNearVOA.IntegralWeights}

/-- Super `C₂`-cofiniteness makes the honest super Zhu quotient finite-dimensional. -/
theorem finiteDimensionalSuperA (h : IntegralSuperC2FiniteZhuBenchmark W hW) :
    FiniteDimensional ℂ (W.toSuperNearVOA.superA hW) :=
  SuperNearVOA.finiteDimensional_superA_of_superC2Cofinite W hW h.c2Cofinite

/-- The bundled square-zero two-sided ideal obstructs semisimplicity. -/
theorem not_isSemisimpleRing (h : IntegralSuperC2FiniteZhuBenchmark W hW) :
    letI := h.zhuRingData.AsRing
    ¬ IsSemisimpleRing (W.toSuperNearVOA.superA hW) := by
  letI := h.zhuRingData.AsRing
  obtain ⟨I, hI, hsq⟩ := h.squareZeroIdeal
  exact SympFerm.not_isSemisimpleRing_of_nonzero_sq_zero_twoSidedIdeal I hI hsq

end IntegralSuperC2FiniteZhuBenchmark

namespace SympFerm

/-- The genuine symplectic-fermion super VOA realizes the strict unconditional finite
super-Zhu benchmark. -/
theorem sympFerm_integralSuperC2FiniteZhuBenchmark :
    IntegralSuperC2FiniteZhuBenchmark sympFermSVOA sympFerm_integralWeights where
  c2Cofinite := sympFerm_superC2Cofinite
  zhuRingData := sympFermSuperZhuRingData
  squareZeroIdeal :=
    exists_chiClass_twoSidedIdeal_sq_zero_of_words sympFermSuperZhuRingData
      sfWordCircleEvalVanishes

/-- The benchmark's super Zhu quotient is finite-dimensional over `ℂ`. -/
theorem sympFerm_benchmark_superA_finiteDimensional :
    FiniteDimensional ℂ ASF :=
  sympFerm_integralSuperC2FiniteZhuBenchmark.finiteDimensionalSuperA

/-- The benchmark's honest super Zhu ring is not semisimple. -/
theorem sympFerm_benchmark_superA_not_isSemisimpleRing :
    letI := instRingASF
    ¬ IsSemisimpleRing ASF :=
  sympFerm_integralSuperC2FiniteZhuBenchmark.not_isSemisimpleRing

end SympFerm

end VOA
