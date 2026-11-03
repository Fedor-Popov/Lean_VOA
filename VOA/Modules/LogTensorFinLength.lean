/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modules.LogTensorFinMain
import VOA.Classification.COne.McRaeM2FinLen

/-!
# Finiteness of logarithmic fusion rules among finite-length weak modules (stage T1d, corollary)

`finiteDimensional_logIntertwining_of_finiteLength`: for a `C₂`-cofinite VOA and three weak
modules of **finite length** over their mode algebras, the space of logarithmic intertwining
operators of type `(A₃ / A₁ A₂)` is finite-dimensional.

No grading is assumed: a finite-length weak module is graded by its generalized
`L₀`-eigenspaces (`C2Rigid.gwOfFiniteLength`, `isGenGraded_gwOfFiniteLength`), hence a
`LogVModule` (`GWModule.toLogV`), and it is finitely generated (finite length ⟹ Noetherian).
So `logFusionFiniteFact_of_c2Cofinite` applies.

No `sorry`, no new axioms.
-/

namespace VOA.LogTensor.LogFin

open Module (End)
open VOA.Classification.COne

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

/-- A Noetherian weak module (over its mode algebra) is finitely generated. -/
theorem finGen_of_isNoetherian {X : Type u} [AddCommGroup X] [Module ℂ X] (A : WeakModule W X)
    [IsNoetherian (modeAlg A) X] : FinGen A := by
  classical
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian (⊤ : Submodule (modeAlg A) X))
  refine ⟨(s : Set X), s.finite_toSet, fun P hsP hP => ?_⟩
  let P' : Submodule (modeAlg A) X :=
    { carrier := P
      add_mem' := P.add_mem
      zero_mem' := P.zero_mem
      smul_mem' := by
        intro a y hy
        have key : ∀ f ∈ modeAlg A, ∀ y ∈ P, f y ∈ P := by
          intro f hf
          induction hf using Algebra.adjoin_induction with
          | mem f hf =>
            obtain ⟨u, n, rfl⟩ := hf
            intro y hy
            exact hP u n y hy
          | algebraMap c =>
            intro y hy
            rw [Module.algebraMap_end_apply]
            exact P.smul_mem c hy
          | add f g _ _ hf hg => intro y hy; exact P.add_mem (hf y hy) (hg y hy)
          | mul f g _ _ hf hg => intro y hy; exact hf _ (hg y hy)
        exact key a.1 a.2 y hy }
  have hle : Submodule.span (modeAlg A) (s : Set X) ≤ P' := Submodule.span_le.mpr hsP
  rw [hs] at hle
  rw [eq_top_iff]
  intro y _
  exact hle (Submodule.mem_top : y ∈ (⊤ : Submodule (modeAlg A) X))

/-- The `LogVModule` attached to a finite-length weak module of a `C₂`-cofinite VOA. -/
noncomputable def logOfFiniteLength (hC2 : C2Cofinite W) {X : Type u} [AddCommGroup X]
    [Module ℂ X] (A : WeakModule W X) (hA : IsFiniteLength (modeAlg A) X) : LogVModule W X :=
  (C2Rigid.gwOfFiniteLength hC2 A hA).toLogV (C2Rigid.isGenGraded_gwOfFiniteLength hC2 A hA)

/-- **Finiteness of logarithmic fusion rules among finite-length weak modules** of a
`C₂`-cofinite VOA. -/
theorem finiteDimensional_logIntertwining_of_finiteLength (hC2 : C2Cofinite W)
    {X₁ X₂ X₃ : Type u} [AddCommGroup X₁] [Module ℂ X₁] [AddCommGroup X₂] [Module ℂ X₂]
    [AddCommGroup X₃] [Module ℂ X₃] (A₁ : WeakModule W X₁) (A₂ : WeakModule W X₂)
    (A₃ : WeakModule W X₃) (h₁ : IsFiniteLength (modeAlg A₁) X₁)
    (h₂ : IsFiniteLength (modeAlg A₂) X₂) (h₃ : IsFiniteLength (modeAlg A₃) X₃) :
    FiniteDimensional ℂ (LogIntertwiningOperator A₁ A₂ A₃) := by
  haveI := (isFiniteLength_iff_isNoetherian_isArtinian.mp h₁).1
  haveI := (isFiniteLength_iff_isNoetherian_isArtinian.mp h₂).1
  haveI := (isFiniteLength_iff_isNoetherian_isArtinian.mp h₃).1
  exact logFusionFiniteFact_of_c2Cofinite hC2 X₁ X₂ X₃ (logOfFiniteLength hC2 A₁ h₁)
    (logOfFiniteLength hC2 A₂ h₂) (logOfFiniteLength hC2 A₃ h₃)
    (finGen_of_isNoetherian A₁) (finGen_of_isNoetherian A₂) (finGen_of_isNoetherian A₃)

/-- The same for the `GWModule`-level spaces `GWLogIntertwiningOperator` of the modules
`gwOfFiniteLength`. -/
theorem finiteDimensional_gwLogIntertwining_of_finiteLength (hC2 : C2Cofinite W)
    {X₁ X₂ X₃ : Type u} [AddCommGroup X₁] [Module ℂ X₁] [AddCommGroup X₂] [Module ℂ X₂]
    [AddCommGroup X₃] [Module ℂ X₃] (A₁ : WeakModule W X₁) (A₂ : WeakModule W X₂)
    (A₃ : WeakModule W X₃) (h₁ : IsFiniteLength (modeAlg A₁) X₁)
    (h₂ : IsFiniteLength (modeAlg A₂) X₂) (h₃ : IsFiniteLength (modeAlg A₃) X₃) :
    FiniteDimensional ℂ (GWLogIntertwiningOperator (C2Rigid.gwOfFiniteLength hC2 A₁ h₁)
      (C2Rigid.gwOfFiniteLength hC2 A₂ h₂) (C2Rigid.gwOfFiniteLength hC2 A₃ h₃)) :=
  finiteDimensional_logIntertwining_of_finiteLength hC2 A₁ A₂ A₃ h₁ h₂ h₃

end VOA.LogTensor.LogFin
