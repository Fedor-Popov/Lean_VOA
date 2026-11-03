/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Classification.COne.McRaeO6Main
import VOA.Classification.COne.OrbRatSplitting
import VOA.Classification.COne.OrbRat2Reduction
import VOA.Classification.COne.MainConverseB4

/-! # O7: rationality of `V₂^G` and the Gannon–Rayhaun converse, conditional on the bridge

* `SurjectionsSplit W`: every surjective morphism of `LogModuleCat W` has a section.
* `whole_split`: for `C₂`-cofinite `W` with `SurjectionsSplit W`, every weak `W`-module of
  length two (`P` an atom and `P ⋖ ⊤`) splits. The module is of finite length, hence an object
  `N` of `LogModuleCat W` (`logOfFiniteLength`); the quotient map `N ⟶ N ⧸ P` (`quotMap`) has a
  section `σ`, and `range σ` is a complement of `P`.
* `admissiblyRational_of_surjectionsSplit`: `C₂` + `SurjectionsSplit` ⇒ admissibly rational
  (every two-step interval splits by `relativeComplement_of_whole_factorBottoms`; then
  `semisimple_of_generalized_cyclic_splitting`).
* `TwistedJacobiBridgeAll`: the O5 bridge for every finite `G ≤ Aut V₂` with `C₂`-cofinite
  `V₂^G` (open).
* `finiteV2OrbifoldRationalOfC2_of_bridge`: the bridge implies B3
  (`FiniteV2OrbifoldRationalOfC2Fact`, McRae Cor. 4.23 for `V₂`).
* `exceptionalV2OrbifoldRationalOfC2_of_bridge`, `gannonRayhaunConverse_of_bridge`.
-/

set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.McRaeO7
open CategoryTheory VOA.LogTensor VOA.LogTensor.LogModuleCat
open PlusRational PlusSplitting ABDWeakAdmissible VOA.Huang.LogRemovalAdmissible

universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}

/-- Every surjective morphism of `C = LogModuleCat W` has a section in `C`. -/
def SurjectionsSplit (W : VertexOperatorAlgebra V) : Prop :=
  ∀ {Y₁ Y₂ : LogModuleCat W} (f : Y₁ ⟶ Y₂), Function.Surjective f.1 →
    ∃ σ : Y₂ ⟶ Y₁, σ ≫ f = 𝟙 Y₂

/-- A module with a simple submodule `P` and simple quotient `M ⧸ P` has finite length. -/
theorem finiteLength_of_atom_covBy_top {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (P : Submodule R M) (hP : IsAtom P) (hPt : P ⋖ ⊤) : IsFiniteLength R M := by
  haveI : IsSimpleModule R P := (isSimpleModule_iff_isAtom).mpr hP
  haveI : IsSimpleModule R (M ⧸ P) := (isSimpleModule_iff_isCoatom).mpr (covBy_top_iff.mp hPt)
  have hfP : IsFiniteLength R P := by
    haveI : IsSimpleModule R (P ⧸ (⊥ : Submodule R P)) :=
      IsSimpleModule.congr (Submodule.quotEquivOfEqBot ⊥ rfl)
    exact IsFiniteLength.of_simple_quotient (N := ⊥) IsFiniteLength.of_subsingleton
  exact IsFiniteLength.of_simple_quotient (N := P) hfP

/-- **Length-two weak modules split**, given `SurjectionsSplit W`. -/
theorem whole_split (hC2 : C2Cofinite W) (hs : SurjectionsSplit W)
    {X : Type u} [AddCommGroup X] [Module ℂ X] (B : WeakModule W X)
    (P : Submodule (modeAlg B) X) (hP : IsAtom P) (hPt : P ⋖ ⊤) :
    ∃ Q : Submodule (modeAlg B) X, IsCompl P Q := by
  have hX : IsFiniteLength (modeAlg B) X := finiteLength_of_atom_covBy_top P hP hPt
  haveI := (isFiniteLength_iff_isNoetherian_isArtinian.mp hX).1
  let N : LogModuleCat W :=
    LogModuleCat.of (VOA.LogTensor.LogFin.logOfFiniteLength hC2 B hX)
      (VOA.LogTensor.LogFin.finGen_of_isNoetherian B)
  let P' : WeakModule.Submodule' N.act.toWeakModule := ofR B P
  let q := McRaeO6.quotMap hC2 N P'
  obtain ⟨σ, hσ⟩ := hs q (McRaeO6.quotMap_surjective hC2 N P')
  let qX : X →ₗ[ℂ] McRaeO6.quotObj hC2 N P' := q.1
  let sX : McRaeO6.quotObj hC2 N P' →ₗ[ℂ] X := σ.1
  have hqσ : ∀ y, qX (sX y) = y := fun y =>
    congrArg (fun k : McRaeO6.quotObj hC2 N P' ⟶ McRaeO6.quotObj hC2 N P' => k.1 y) hσ
  have hker : ∀ x : X, qX x = 0 ↔ x ∈ P := fun x => McRaeO6.quotMap_eq_zero_iff hC2 N P' x
  let Q : Submodule (modeAlg B) X := toR B (McRaeO6.rangeSub σ)
  have hQ : ∀ x : X, x ∈ Q ↔ ∃ y, sX y = x := fun x => Iff.rfl
  refine ⟨Q, ?_, ?_⟩
  · rw [Submodule.disjoint_def]
    intro x hxP hxQ
    obtain ⟨y, rfl⟩ := (hQ x).mp hxQ
    have hy : y = 0 := by rw [← hqσ y]; exact (hker _).mpr hxP
    subst hy
    exact map_zero sX
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    refine Submodule.mem_sup.mpr ⟨x - sX (qX x), ?_, sX (qX x), (hQ _).mpr ⟨_, rfl⟩,
      sub_add_cancel _ _⟩
    apply (hker _).mp
    rw [map_sub, hqσ, sub_self]

/-- Every two-step interval of every weak module splits, given `SurjectionsSplit W`. -/
theorem twoStepSplitting_of_surjectionsSplit (hC2 : C2Cofinite W) (hs : SurjectionsSplit W)
    {M : Type u} [AddCommGroup M] [Module ℂ M] (A : WeakModule W M) :
    TwoStepSplitting (Submodule (modeAlg A) M) := by
  intro a b c hab hbc
  obtain ⟨h, hh⟩ := exists_factorBottom hC2 A hab.lt
  obtain ⟨k, hk⟩ := exists_factorBottom hC2 A hbc.lt
  exact relativeComplement_of_whole_factorBottoms hC2 A hab hbc h k hh hk
    (fun B P hP hPt _ _ => whole_split hC2 hs B P hP hPt)

/-- **Split surjections give rationality**: a `C₂`-cofinite VOA all of whose surjections in
`LogModuleCat` split is admissibly rational. -/
theorem admissiblyRational_of_surjectionsSplit (hC2 : C2Cofinite W) (hs : SurjectionsSplit W) :
    AdmissiblyRational W := by
  intro M _ _ N
  apply (isSemisimpleModule_modeAlg_iff N).mp
  have h2 := twoStepSplitting_of_surjectionsSplit hC2 hs N.toWeakModule
  exact semisimple_of_generalized_cyclic_splitting hC2 N.toWeakModule
    (fun _ x _ => twoStepSplitting_submodule h2 (cyclic N.toWeakModule x))

/-! ## `V₂` -/

/-- **The O5 bridge for every finite `G ≤ Aut V₂` with `C₂`-cofinite `V₂^G` (open).** -/
def TwistedJacobiBridgeAll : Prop :=
  ∀ (G : Subgroup (Aut (V2m 1 le_rfl))) [Finite G] (hC2 : C2Cofinite (orbifoldVOA G)),
    McRaeO5.TwistedJacobiBridge G (VOA.Huang.SchurWeyl.V2m_orbifold_finGen G) hC2

/-- **O7: McRae Cor. 4.23 for `V₂`, conditional on the bridge.** For every finite
`G ≤ Aut V₂` with `C₂`-cofinite `V₂^G`, the orbifold `V₂^G` is admissibly rational. -/
theorem finiteV2OrbifoldRationalOfC2_of_bridge (hB : TwistedJacobiBridgeAll) :
    FiniteV2OrbifoldRationalOfC2Fact := by
  intro G _ hC2
  classical
  haveI := Fintype.ofFinite G
  apply admissiblyRational_of_surjectionsSplit hC2
  exact @McRaeO6.V2m_lemma_4_21 G _ _ hC2 (hB G hC2)

/-- The consumed part of B3, conditional on the bridge. -/
theorem exceptionalV2OrbifoldRationalOfC2_of_bridge (hB : TwistedJacobiBridgeAll) :
    OrbRat2.ExceptionalV2OrbifoldRationalOfC2 :=
  OrbRat2.exceptionalV2OrbifoldRationalOfC2_of_finite (finiteV2OrbifoldRationalOfC2_of_bridge hB)

/-- **The converse of Gannon–Rayhaun, conditional only on the O5 bridge.** -/
theorem gannonRayhaunConverse_of_bridge (hB : TwistedJacobiBridgeAll) :
    GannonRayhaunConverse.{0} :=
  gannonRayhaunConverse_of_B3 (finiteV2OrbifoldRationalOfC2_of_bridge hB)

end VOA.Classification.COne.McRaeO7
