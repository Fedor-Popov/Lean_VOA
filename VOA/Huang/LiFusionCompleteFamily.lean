import VOA.Huang.LiFusionZhuLaws
import VOA.Modularity.GNProp8Closure

/-! # From a complete family of VOA simples to top separation

C₂-cofiniteness is used explicitly to realize every simple Zhu module by an
ordinary module. The general module Zhu identities remain a named input.
-/
namespace VOA.Huang.LiFusion
open VOA VHat VHat.DLM3
universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}
  {A : OrdVModule W M} {ι : Type u}

/-- Realization turns completeness for VOA simples into completeness for Zhu simples. -/
theorem completeTopFamily_of_realization (hreal : SimpleAModsRealized W)
    (P : ι → LWModule W)
    (hcomplete : ∀ Q : LWModule W, Q.IsIrreducibleLW → ∃ i, LWModule.Iso W Q (P i)) :
    CompleteTopFamily P := by
  intro U hU
  obtain ⟨Q, hQ, ⟨e⟩⟩ := isBottomOfIrr_of_simple hreal hU
  obtain ⟨i, ⟨d⟩⟩ := hcomplete Q hQ
  exact ⟨i, ⟨AModEquiv.trans W (AModEquiv.symm W e) (LWModule.isoToAModEquiv W d)⟩⟩

/-- The intended complete-family separation statement, conditional only on
raw module Zhu identities beyond the displayed rationality and PBW hypotheses.
C₂-cofiniteness supplies the library's simple-module realization theorem. -/
theorem topDataSeparate_of_complete_rawLaws [Finite ι]
    (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W)))
    (hC2 : C2Cofinite W) (hrat : AdmissiblyRational W)
    (hraw : RawZhuBimoduleLaws A) (P : ι → LWModule W)
    (hcomplete : ∀ Q : LWModule W, Q.IsIrreducibleLW → ∃ i, LWModule.Iso W Q (P i))
    (hP : ∀ i, (P i).IsIrreducibleLW)
    (hne : ∀ i j, i ≠ j → IsEmpty (AModEquiv W (P i).toAMod (P j).toAMod)) :
    TopDataSeparate A P :=
  topDataSeparate_of_admissiblyRational_rawLaws Pr hrat hraw P
    (completeTopFamily_of_realization (simpleAModsRealized_of_C2Cofinite hC2 Pr) P hcomplete)
    hP hne

end VOA.Huang.LiFusion
