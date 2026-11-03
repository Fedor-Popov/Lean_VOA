import VOA.Classification.COne.AdmissibleOrdinaryFinite
import VOA.Classification.COne.ABDWeakAdmissibleComplete
import VOA.Huang.ZhuSemisimple
import VOA.Modules.ZhuVermaAnArchDLM3PBWAxiom
import VOA.Modules.StronglyRational

/-!
# The named literature predicates that are theorems

`Modules/RationalityLattice.lean` §5 transcribes the Dong–Li–Mason, Abe–Buhl–Dong and Li
theorems as named `Prop`s, consumed as hypotheses.  This file records, under single names, which
of them the library proves, and under which hypotheses.

* `ABDWeakIsAdmissible` (ABD Prop. 5.7) — proved for every `W`:
  `VOA.Classification.COne.ABDWeakAdmissible.abdWeakIsAdmissible` (the `C₂` hypothesis is inside
  the predicate).
* `ABDIrreducibleWeakIsOrdinary` (ABD Cor. 5.8) — proved for every `W`:
  `abdIrreducibleWeakIsOrdinary_holds`.
* `ABDRegularOfC2AndRational` (ABD Thm. 4.5, hard direction) — proved for every `W`:
  `abdRegularOfC2AndRational_holds`.
* `DLMSimpleAdmissibleOrdinary` (DLM Thm. 8.1(c)) — proved for `C₂`-cofinite `W`
  (`dlmSimpleAdmissibleOrdinary_of_c2Cofinite`, existing).
* `DLMFinitelyManyIrredAdmissible` (DLM Thm. 8.1(b)) — proved for `C₂`-cofinite `W`:
  `dlmFinitelyManyIrredAdmissible_of_c2Cofinite`.  The predicate's own `AdmissiblyRational`
  antecedent supplies the semisimplicity of Zhu's algebra; the bottom projection is
  `voaPBWBottomProjection` (built from the theorem `VOA.pbw`; `#print axioms` is the standard
  three).
* `ZhuAdmissibleSemisimple` — proved for every `W` (`zhuAdmissibleSemisimple_of_Pr` with the same
  bottom projection); restated here as `zhuAdmissibleSemisimple_holds`.

For every `StronglyRational W` the corollaries `StronglyRational.regular`,
`StronglyRational.dlmFinitelyManyIrredAdmissible` and `StronglyRational.gannonRational'` carry no
literature hypothesis.

**Still unproved:** `LiC2CofiniteOfRegular` (H. Li, J. Algebra 212, Thm. 3.8), and the non-`C₂`
cases of the two DLM predicates.  Consequently `regular_iff_c2Cofinite_and_admissiblyRational`
remains conditional on `LiC2CofiniteOfRegular`.
-/

namespace VOA.Classification.COne.LiteratureInputs

open VOA.VHat VOA.VHat.DLM3
open VOA.Classification.COne.AdmissibleOrdinary
open VOA.Classification.COne.ABDWeakAdmissible

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

/-- **ABD Cor. 5.8, unconditionally**: for every VOA, `C₂`-cofiniteness makes every irreducible
weak module an ordinary module with the same action.  No rationality is used. -/
theorem abdIrreducibleWeakIsOrdinary_holds : ABDIrreducibleWeakIsOrdinary W :=
  abdIrreducibleWeakIsOrdinary_of_weakIsAdmissible abdWeakIsAdmissible

/-- **ABD Thm. 4.5, hard direction, unconditionally**: for every VOA,
`C₂Cofinite W → AdmissiblyRational W → Regular W`. -/
theorem abdRegularOfC2AndRational_holds : ABDRegularOfC2AndRational W :=
  abdRegularOfC2AndRational_of_components abdWeakIsAdmissible
    abdIrreducibleWeakIsOrdinary_holds

/-- **Zhu / DLM: rationality implies `A(W)` semisimple**, for every VOA, with the bottom projection
supplied by `voaPBWBottomProjection`. -/
theorem zhuAdmissibleSemisimple_holds : ZhuAdmissibleSemisimple W :=
  VOA.Huang.ZhuSemisimple.zhuAdmissibleSemisimple_of_Pr
    (voaPBWBottomProjection (parabolicRepOfAMod W (regularAMod W)))

/-- **DLM Thm. 8.1(b) on the `C₂`-cofinite locus**: a `C₂`-cofinite VOA that is admissibly rational
has finitely many irreducible admissible modules up to isomorphism.  Only `C₂Cofinite W` is a
hypothesis: the predicate's own `AdmissiblyRational W` antecedent gives `IsSemisimpleRing (A W)`
(`isSemisimpleRing_A_of_admissiblyRational`). -/
theorem dlmFinitelyManyIrredAdmissible_of_c2Cofinite (hC2 : C2Cofinite W) :
    DLMFinitelyManyIrredAdmissible W := fun hAR =>
  c2SemisimpleAdmissibleFiniteness_of_bottomProjection
    (voaPBWBottomProjection (parabolicRepOfAMod W (regularAMod W))) hC2
    (VOA.Huang.ZhuSemisimple.isSemisimpleRing_A_of_admissiblyRational
      (voaPBWBottomProjection (parabolicRepOfAMod W (regularAMod W))) hAR)

/-- A strongly rational VOA is regular, with no literature hypothesis (ABD Thm. 4.5). -/
theorem _root_.VOA.StronglyRational.regular (h : StronglyRational W) : Regular W :=
  h.regular_of_abd abdRegularOfC2AndRational_holds

/-- DLM Thm. 8.1(b) for every strongly rational VOA. -/
theorem _root_.VOA.StronglyRational.dlmFinitelyManyIrredAdmissible (h : StronglyRational W) :
    DLMFinitelyManyIrredAdmissible W :=
  dlmFinitelyManyIrredAdmissible_of_c2Cofinite h.c2Cofinite

/-- DLM Thm. 8.1(b) for every strongly rational VOA, discharged: finitely many irreducible
admissible classes. -/
theorem _root_.VOA.StronglyRational.finite_Φadm (h : StronglyRational W) : Finite (Φadm W) :=
  h.dlmFinitelyManyIrredAdmissible h.rational

/-- **`StronglyRational ⟹ GannonRational`** with both DLM inputs discharged
(compare `StronglyRational.gannonRational`, which carries them as hypotheses). -/
theorem _root_.VOA.StronglyRational.gannonRational' (h : StronglyRational W) :
    GannonRational W :=
  h.gannonRational h.dlmFinitelyManyIrredAdmissible
    (dlmSimpleAdmissibleOrdinary_of_stronglyRational h)

end VOA.Classification.COne.LiteratureInputs
