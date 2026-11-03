import VOA.Huang.LiConverseZhuLaws
import VOA.Huang.LiFusionCompleteFamily
import VOA.Huang.GenusOneLiBimodule
import VOA.Modules.ZhuVermaAnArchDLM3PBWAxiom
import VOA.Huang.GenusOneCuspSupport
import VOA.Huang.GenusOneCuspWeight

/-! # The genus-one insertion bimodule, discharged

`LiConverse.rawZhuBimoduleLaws` proves the Frenkel–Zhu bimodule identities for every
ordinary module. Feeding it into the reductions (`LiFusionZhuLaws`,
`LiFusionCompleteFamily`, `GenusOneLiBimodule`) gives:

* `topDataSeparate_of_semisimple` / `insertionTopBimoduleExists_of_semisimple`:
  for a finite, irredundant, complete family of irreducible tops over a semisimple Zhu
  algebra (Lean's three axioms only);
* `insertionTopBimoduleExists_of_rational` : the same from `C₂`-cofiniteness, admissible
  rationality and an explicit regular-module PBW datum `Pr`, for a family complete among
  irreducible lowest-weight modules (Lean's three axioms only);
* `insertionTopBimoduleExists_of_stronglyRational_pbw` : the strongly rational case with
  `Pr` supplied by the theorem `VOA.pbw`.

No `sorry`, no new axioms.
-/

namespace VOA.Huang.LiConverse

open VOA VOA.FZ VHat VHat.DLM3 VOA.Huang.LiFusion VOA.Huang.GenusOne

universe u

variable {V M : Type u} [AddCommGroup V] [Module ℂ V] [AddCommGroup M] [Module ℂ M]
  {W : VertexOperatorAlgebra V} (A : OrdVModule W M) {ι : Type u}

/-- Separation of `M / O(M)` by top data, for a complete irredundant family over a
semisimple Zhu algebra. -/
theorem topDataSeparate_of_semisimple [Finite ι] (P : ι → LWModule W)
    (hss : letI := instRingA W; IsSemisimpleRing (VOA.A W))
    (hcomplete : CompleteTopFamily P) (hP : ∀ i, (P i).IsIrreducibleLW)
    (hne : ∀ i j, i ≠ j → IsEmpty (AModEquiv W (P i).toAMod (P j).toAMod)) :
    TopDataSeparate A P :=
  (topDataSeparate_iff_rawLaws P hss hcomplete hP hne).mpr (rawZhuBimoduleLaws A)

/-- **The insertion bimodule exists** over a semisimple Zhu algebra with a complete
irredundant finite family of irreducible tops. -/
theorem insertionTopBimoduleExists_of_semisimple [Finite ι] (P : ι → LWModule W)
    (hss : letI := instRingA W; IsSemisimpleRing (VOA.A W))
    (hcomplete : CompleteTopFamily P) (hP : ∀ i, (P i).IsIrreducibleLW)
    (hne : ∀ i j, i ≠ j → IsEmpty (AModEquiv W (P i).toAMod (P j).toAMod)) :
    InsertionTopBimoduleExists A P :=
  insertionTopBimoduleExists_of_rawLaws (rawZhuBimoduleLaws A) P hss hcomplete hP hne

/-- **The insertion bimodule exists** for a `C₂`-cofinite admissibly rational VOA and a
finite irredundant family complete among irreducible lowest-weight modules, with the
regular-module PBW datum `Pr` explicit. -/
theorem insertionTopBimoduleExists_of_rational [Finite ι]
    (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W)))
    (hC2 : C2Cofinite W) (hrat : AdmissiblyRational W) (P : ι → LWModule W)
    (hcomplete : ∀ Q : LWModule W, Q.IsIrreducibleLW → ∃ i, LWModule.Iso W Q (P i))
    (hP : ∀ i, (P i).IsIrreducibleLW)
    (hne : ∀ i j, i ≠ j → IsEmpty (AModEquiv W (P i).toAMod (P j).toAMod)) :
    InsertionTopBimoduleExists A P :=
  insertionTopBimoduleExists_of_separate P hP hne
    (topDataSeparate_of_complete_rawLaws Pr hC2 hrat (rawZhuBimoduleLaws A) P hcomplete hP hne)

/-- **The insertion bimodule exists for every strongly rational VOA**, for every
ordinary insertion module and every finite irredundant complete family of irreducible
lowest-weight modules. The PBW datum comes from the theorem `VOA.pbw`. -/
theorem insertionTopBimoduleExists_of_stronglyRational_pbw [Finite ι]
    (hV : StronglyRational W) (P : ι → LWModule W)
    (hcomplete : ∀ Q : LWModule W, Q.IsIrreducibleLW → ∃ i, LWModule.Iso W Q (P i))
    (hP : ∀ i, (P i).IsIrreducibleLW)
    (hne : ∀ i j, i ≠ j → IsEmpty (AModEquiv W (P i).toAMod (P j).toAMod)) :
    InsertionTopBimoduleExists A P :=
  insertionTopBimoduleExists_of_rational A (voaPBWBottomProjection _)
    hV.toStronglyFinite.c2Cofinite hV.rational P hcomplete hP hne

/-- Genus-one consumer: a nonzero leading coefficient of a supported formal insertion block
forces a matching lowest weight in the complete family. Strongly rational `V`; the PBW datum
comes from the theorem `VOA.pbw`; no Li-converse hypothesis. -/
theorem leading_weight_mem_of_stronglyRational [Finite ι] (hV : StronglyRational W)
    (P : ι → LWModule W)
    (hcomplete : ∀ Q : LWModule W, Q.IsIrreducibleLW → ∃ i, LWModule.Iso W Q (P i))
    (hP : ∀ i, (P i).IsIrreducibleLW)
    (hne : ∀ i j, i ≠ j → IsEmpty (AModEquiv W (P i).toAMod (P j).toAMod))
    {S : M →ₗ[ℂ] FormalQSeries} {b : ℂ} (hsupp : ∀ w, S w ∈ QSeriesAt b)
    (hS : IsInsertionFormalBlock A S) {w : M} (hw : S w b ≠ 0) :
    ∃ i, (P i).h = b + W.centralCharge / 24 :=
  leading_weight_mem P (insertionTopBimoduleExists_of_stronglyRational_pbw A hV P hcomplete hP hne)
    hsupp hS hw

/-- Genus-one consumer: leading-term realization by intertwiner traces, with the bimodule
input discharged; the Li converse `InsertionTopSurjectivity` is the only remaining input. -/
theorem leading_realized_at_weight_of_stronglyRational [Fintype ι] (hV : StronglyRational W)
    (P : ι → LWModule W)
    (hcomplete : ∀ Q : LWModule W, Q.IsIrreducibleLW → ∃ i, LWModule.Iso W Q (P i))
    (hP : ∀ i, (P i).IsIrreducibleLW)
    (hne : ∀ i j, i ≠ j → IsEmpty (AModEquiv W (P i).toAMod (P j).toAMod))
    (hlift : InsertionTopSurjectivity A P)
    {S : M →ₗ[ℂ] FormalQSeries} {b : ℂ} (hsupp : ∀ w, S w ∈ QSeriesAt b)
    (hS : IsInsertionFormalBlock A S) :
    ∃ Y : ∀ i, IntertwiningOperator A (P i).isMod (P i).isMod,
      (∀ i, (P i).h ≠ b + W.centralCharge / 24 → Y i = 0) ∧
      ∀ w, S w b = ∑ i, trace (Y i) w b :=
  leading_realized_at_weight P
    (insertionTopBimoduleExists_of_stronglyRational_pbw A hV P hcomplete hP hne) hlift hsupp hS

end VOA.Huang.LiConverse
