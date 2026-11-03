/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modularity.SuperCuspFunctionalCount
import VOA.Modularity.SuperBlockRelSpanTransport

/-!
# The sharp super Arike--Nagatomo genus-one bound

For an integral-weight, `C₂`-cofinite super VOA, the untwisted supertrace block space has dimension
at most the dimension of the supersymmetric linear functionals on its super Zhu algebra.  No
rationality or semisimplicity hypothesis is used.

This is the upper-bound half only.  It neither constructs pseudo-supertraces nor proves their
modular transformation law.
-/

namespace VOA

open Module (finrank)
open GammaThetaStmt

set_option autoImplicit false

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace SuperNearVOA

/-- A sharp cusp family transports to an interior point without changing cardinality. -/
theorem exists_interior_span_sup_superBlockRelSpan_of_superC2
    (W : SuperVertexOperatorAlgebra 𝒱) (hV : W.toSuperNearVOA.IntegralWeights)
    (hC2 : SuperC2Cofinite W) :
    ∃ (T : Finset 𝒱) (z0 : UpperHalfPlane),
      T.card ≤ (let hZ := W.superZhuRingData hV
        letI := hZ.AsRing
        letI := hZ.AsAlgebra
        finrank ℂ (W.toSuperNearVOA.superA hV ⧸ hZ.superZhuCommSpan)) ∧
      (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ (T : Set 𝒱) ⊔
        W.toSuperNearVOA.superBlockRelSpan (z0 : ℂ) := by
  obtain ⟨T, hTcard, hTcusp⟩ :=
    exists_finset_span_sup_superBlockRelSpanAtCusp W hV hC2
  obtain ⟨z0, hz0⟩ :=
    exists_interior_span_sup_superBlockRelSpan_of_cusp W hV hC2 (T : Set 𝒱) hTcusp
  exact ⟨T, z0, hTcard, hz0⟩

/-- The sharp bound in supercommutator-quotient form. -/
theorem finrank_superAnalyticBlocks_le_finrank_quot_superZhuCommSpan
    (W : SuperVertexOperatorAlgebra 𝒱) (hV : W.toSuperNearVOA.IntegralWeights)
    (hC2 : SuperC2Cofinite W) :
    FiniteDimensional ℂ
        (Submodule.map restrictImGT W.toSuperNearVOA.superAnalyticBlocks) ∧
      finrank ℂ (Submodule.map restrictImGT W.toSuperNearVOA.superAnalyticBlocks)
        ≤ (let hZ := W.superZhuRingData hV
          letI := hZ.AsRing
          letI := hZ.AsAlgebra
          finrank ℂ (W.toSuperNearVOA.superA hV ⧸ hZ.superZhuCommSpan)) := by
  obtain ⟨T, z0, hTcard, hz0⟩ :=
    exists_interior_span_sup_superBlockRelSpan_of_superC2 W hV hC2
  obtain ⟨hfd, hle⟩ :=
    finrank_superAnalyticBlocks_le_card_of_superBlockRel (coe_mem_imGT_zero z0) T hz0
  exact ⟨hfd, hle.trans hTcard⟩

/-- `C₂`-cofiniteness already implies finite-dimensionality of the untwisted integral-weight
supertrace block space. -/
theorem finiteDimensional_superAnalyticBlocks_of_superC2
    (W : SuperVertexOperatorAlgebra 𝒱) (hV : W.toSuperNearVOA.IntegralWeights)
    (hC2 : SuperC2Cofinite W) :
    FiniteDimensional ℂ
      (Submodule.map restrictImGT W.toSuperNearVOA.superAnalyticBlocks) :=
  (finrank_superAnalyticBlocks_le_finrank_quot_superZhuCommSpan W hV hC2).1

/-- **Super Arike--Nagatomo upper bound.**  For an integral-weight `C₂`-cofinite super VOA,
the untwisted supertrace block space is bounded by the supersymmetric linear functionals on the
super Zhu algebra. -/
theorem finrank_superAnalyticBlocks_le_finrank_superZhuSymmetricFunctionals
    (W : SuperVertexOperatorAlgebra 𝒱) (hV : W.toSuperNearVOA.IntegralWeights)
    (hC2 : SuperC2Cofinite W) :
    finrank ℂ (Submodule.map restrictImGT W.toSuperNearVOA.superAnalyticBlocks)
      ≤ (let hZ := W.superZhuRingData hV
        letI := hZ.AsRing
        letI := hZ.AsAlgebra
        finrank ℂ hZ.superZhuSymmetricFunctionals) := by
  let hZ := W.superZhuRingData hV
  letI := hZ.AsRing
  letI := hZ.AsAlgebra
  rw [hZ.finrank_superZhuSymmetricFunctionals_eq]
  exact (finrank_superAnalyticBlocks_le_finrank_quot_superZhuCommSpan W hV hC2).2

end SuperNearVOA

end VOA
