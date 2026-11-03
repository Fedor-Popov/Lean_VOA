/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.OrbA4Rational
import VOA.Classification.COne.OrbRatZhu

/-!
# The Zhu algebra of the tetrahedral model is `ℂ²¹`, and what that does (not) decide

With `OrbSgl.cubicZhuDimensionBound_holds` (`dim A(W) ≤ 21`) and
`OrbRat6.cubicZhuCharacterTable_holds` (21 distinct characters), the evaluation map
`A(W) → ℂ²¹` is an algebra isomorphism.  Hence `A(W)` is commutative and semisimple
(`cubicModel_zhuAlgEquiv`, `cubicModel_zhuSemisimple`, `cubicModel_zhu_finrank`).

`W` is also strongly finite (`cubicModel_stronglyFinite`: simple and self-dual as a finite
orbifold of `V₈⁺ ≅ V₂^{V₄}`, `C₂` by `OrbA4.cubicModel_c2Cofinite_holds`).  Consequently:

* `cubicModel_admissiblyRational_iff_resonant`: rationality of `W` is EQUIVALENT to resonant whole
  splitting for `W` (no hypothesis);
* `cubicModel_admissiblyRational_of_zhuCriterion`: McRae's criterion
  (`OrbRat.ZhuSemisimpleRationalityFact`, arXiv:2108.01898 Main Theorem 3; stated, NOT proved)
  gives rationality of `W` directly, bypassing the two `TopCyclic` residuals.

What semisimplicity does NOT give: the residuals `OrbRat8.TopCyclicFourOneResidual` and
`OrbRat8.TopCyclicVanishing cubicModel (1/4) (9/4)`.  The Zhu dimension bound is already one of
the inputs of the reduction to those residuals (`OrbRat8.cubicModelRationalOfC2_of_residuals`), so
semisimplicity of `A(W)` has been fully consumed: the residuals concern the degree `2` and `3`
parts of a cyclic module, which `A(W)` (the top level) does not see.
-/

set_option maxSynthPendingDepth 3

noncomputable section

namespace VOA.Classification.COne.OrbTop

open VOA VertexOperatorAlgebra OrbRat2

attribute [local instance] instRingA instAlgebraA

/-- `A(W) ≅ ℂ²¹` as `ℂ`-algebras (the 21 characters of the table). -/
theorem cubicModel_zhuAlgEquiv : Nonempty (VOA.A cubicModel ≃ₐ[ℂ] (Fin 21 → ℂ)) := by
  letI := finiteDimensional_A_of_C2Cofinite cubicModel OrbA4.cubicModel_c2Cofinite_holds
  obtain ⟨χ, hχ, -⟩ := OrbRat6.cubicZhuCharacterTable_holds
  exact ⟨PlusSplitting.characterAlgEquiv χ hχ
    (by simpa using OrbSgl.cubicZhuDimensionBound_holds)⟩

/-- `dim A(W) = 21`. -/
theorem cubicModel_zhu_finrank : Module.finrank ℂ (VOA.A cubicModel) = 21 := by
  obtain ⟨e⟩ := cubicModel_zhuAlgEquiv
  rw [e.toLinearEquiv.finrank_eq]
  simp

/-- `A(W)` is commutative. -/
theorem cubicModel_zhu_comm (a b : VOA.A cubicModel) : a * b = b * a := by
  obtain ⟨e⟩ := cubicModel_zhuAlgEquiv
  apply e.injective
  rw [map_mul, map_mul, mul_comm]

/-- `A(W)` is semisimple. -/
theorem cubicModel_zhuSemisimple : IsSemisimpleRing (VOA.A cubicModel) :=
  OrbRat2.isSemisimpleRing_of_charTable OrbA4.cubicModel_c2Cofinite_holds
    OrbSgl.cubicZhuDimensionBound_holds OrbRat6.cubicZhuCharacterTable_holds

/-- The tetrahedral model is strongly finite (simple, self-dual, `C₂`-cofinite). -/
theorem cubicModel_stronglyFinite : StronglyFinite cubicModel :=
  OrbRat.orbifold_stronglyFinite OrbC2b.klein_stronglyRational.toStronglyFinite
    (Subgroup.zpowers OrbC2b.kleinCubic) OrbA4.cubicModel_c2Cofinite_holds

/-- Rationality of the tetrahedral model is exactly resonant whole splitting (no hypotheses:
`C₂` and Zhu semisimplicity are proved). -/
theorem cubicModel_admissiblyRational_iff_resonant :
    AdmissiblyRational cubicModel ↔ OrbRat.ResonantWholeSplitting cubicModel :=
  OrbRat.admissiblyRational_iff_resonantWholeSplitting OrbA4.cubicModel_c2Cofinite_holds
    cubicModel_zhuSemisimple

/-- McRae's Zhu criterion (stated, not proved) gives rationality of the tetrahedral model,
without the two `TopCyclic` residuals. -/
theorem cubicModel_admissiblyRational_of_zhuCriterion
    (hZ : OrbRat.ZhuSemisimpleRationalityFact.{0}) : AdmissiblyRational cubicModel :=
  hZ _ cubicModel cubicModel_stronglyFinite cubicModel_zhuSemisimple

end VOA.Classification.COne.OrbTop
