/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Huang.ZhuFiniteIrr
import VOA.Huang.LWBottomRecovery

/-!
# O1: finitely many irreducible modules for every `C₂`-cofinite VOA (no semisimple Zhu)

`VOA.Huang.ZhuFiniteIrr.finite_Φ_of_C2Cofinite` carries `IsSemisimpleRing (A W)`.  It used it
twice: to decompose `A(V)` into simple left ideals, and to see that the bottom of an irreducible
module is simple.  Neither is needed:

* bottom simplicity holds for every VOA
  (`VOA.Huang.LWBottomRecovery.isSimpleAMod_toAMod_of_irreducible`);
* for a finite-dimensional (hence Artinian) `A = A(V)`, the `A`-module `A ⧸ J(A)` is semisimple
  (`IsArtinian.isSemisimpleModule_iff_jacobson`, `Module.jacobson_quotient_jacobson`), hence a
  finite sum of simple submodules; `J(A)` annihilates every simple module, so every simple `U`
  receives a nonzero map `A ⧸ J(A) → U`, `ā ↦ a·u`, and is isomorphic to one of those finitely
  many summands (Schur).

## Main results

* `finite_Φ_of_finiteDimensional` : `Pr`, `dim A(V) < ∞` ⟹ `Finite (Φ W)`;
* `finite_Φ_of_C2Cofinite'` / `finite_Φ_of_C2Cofinite_pbw` : the `C₂`-cofinite forms.

The McRae-M2 consumer `VOA.C2Rigid.LocalInjective.finiteLength_maximal_of_c2` (in
`McRaeM2TensorFiniteLength`) uses `finite_Φ_of_C2Cofinite_pbw`, so the whole logarithmic tensor
chain built on `maximalLogModule` carries no semisimple-Zhu hypothesis.
-/

set_option maxSynthPendingDepth 3

namespace VOA.Huang.ZhuFiniteIrr

open VOA VOA.VHat VOA.VHat.DLM3

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

section LocalRing

attribute [local instance] instRingA

/-- Schur, for an arbitrary module covered by simple submodules: a simple `AMod` receiving a
nonzero map from `M` is isomorphic to one of the covering simple submodules. -/
theorem exists_mem_linearEquiv_of_map
    {M : Type*} [AddCommGroup M] [Module (A W) M]
    (s : Set (Submodule (A W) M)) (htop : sSup s = ⊤)
    (hsimp : ∀ m ∈ s, IsSimpleModule (A W) m)
    (U : AMod W) (hU : IsSimpleAMod U)
    (f : letI := U.moduleA; M →ₗ[A W] U.carrier) (hf : f ≠ 0) :
    letI := U.moduleA
    ∃ I ∈ s, Nonempty (I ≃ₗ[A W] U.carrier) := by
  letI := U.moduleA
  haveI hUm : IsSimpleModule (A W) U.carrier := (isSimpleAMod_iff_isSimpleModule U).1 hU
  have hex : ∃ I ∈ s, f.comp I.subtype ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hle : sSup s ≤ LinearMap.ker f := by
      refine sSup_le fun I hI => ?_
      intro a ha
      have := congrArg (fun g => g ⟨a, ha⟩) (hcon I hI)
      simpa using this
    rw [htop, top_le_iff, LinearMap.ker_eq_top] at hle
    exact hf hle
  obtain ⟨I, hI, hne⟩ := hex
  haveI := hsimp I hI
  exact ⟨I, hI, ⟨LinearEquiv.ofBijective _ (LinearMap.bijective_of_ne_zero hne)⟩⟩

end LocalRing

/-- **Finitely many irreducible modules when `A(V)` is finite-dimensional**, given the PBW
datum `Pr`.  No semisimplicity of `A(V)`. -/
theorem finite_Φ_of_finiteDimensional
    (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W)))
    (hfd : letI := instRingA W; FiniteDimensional ℂ (A W)) : Finite (Φ W) := by
  classical
  letI := instRingA W
  letI := instAlgebraA W
  haveI : IsNoetherian ℂ (A W) := IsNoetherian.iff_fg.mpr hfd
  haveI : IsNoetherian (A W) (A W) := isNoetherian_of_tower ℂ inferInstance
  haveI : IsArtinian ℂ (A W) := inferInstance
  haveI : IsArtinian (A W) (A W) := isArtinian_of_tower ℂ inferInstance
  -- the semisimple top `A ⧸ J(A)`
  let J : Submodule (A W) (A W) := Module.jacobson (A W) (A W)
  haveI hss : IsSemisimpleModule (A W) (A W ⧸ J) :=
    (IsArtinian.isSemisimpleModule_iff_jacobson (A W) (A W ⧸ J)).2
      (Module.jacobson_quotient_jacobson (A W) (A W))
  obtain ⟨s, hind, htop, hsimp⟩ :=
    IsSemisimpleModule.exists_sSupIndep_sSup_simples_eq_top (A W) (A W ⧸ J)
  have hsfin : s.Finite := WellFoundedGT.finite_of_sSupIndep hind
  haveI := hsfin.to_subtype
  have hUs : ∀ c : Φ W, IsSimpleAMod
      (lowestAMod (canonicalIrrFamily_hasConformalWeight (W := W) c).2) := fun c =>
    VOA.Huang.LWBottomRecovery.isSimpleAMod_toAMod_of_irreducible (canonicalIrrLWModule c)
      (canonicalIrrLWModule_irreducible c)
  have hex : ∀ c : Φ W, ∃ I ∈ s, Nonempty (letI :=
      (lowestAMod (canonicalIrrFamily_hasConformalWeight (W := W) c).2).moduleA;
      I ≃ₗ[A W] (lowestAMod (canonicalIrrFamily_hasConformalWeight (W := W) c).2).carrier) := by
    intro c
    set U := lowestAMod (canonicalIrrFamily_hasConformalWeight (W := W) c).2
    letI := U.moduleA
    haveI : IsSimpleModule (A W) U.carrier := (isSimpleAMod_iff_isSimpleModule U).1 (hUs c)
    haveI : Nontrivial U.carrier := (hUs c).1
    obtain ⟨u, hu⟩ := exists_ne (0 : U.carrier)
    let f : A W →ₗ[A W] U.carrier := LinearMap.toSpanSingleton (A W) U.carrier u
    have hJ : J ≤ LinearMap.ker f :=
      IsSemisimpleModule.jacobson_le_ker (A W) (A W) (A W) U.carrier f
    let g : (A W ⧸ J) →ₗ[A W] U.carrier := J.liftQ f hJ
    have hg : g ≠ 0 := by
      intro h0
      apply hu
      have h1 : g (J.mkQ 1) = 0 := by rw [h0]; rfl
      rw [Submodule.mkQ_apply, Submodule.liftQ_apply] at h1
      simpa [f] using h1
    exact exists_mem_linearEquiv_of_map s htop hsimp U (hUs c) g hg
  choose I hIs hIe using hex
  refine Finite.of_injective (fun c => (⟨I c, hIs c⟩ : s)) ?_
  intro j k hjk
  have hI : I j = I k := congrArg Subtype.val hjk
  by_contra hne
  obtain ⟨ej⟩ := hIe j
  obtain ⟨ek⟩ := hIe k
  exact (canonicalIrrFamily_bottomSeparated_of_Pr Pr hne).false
    (amodEquivOfLinearEquiv (ej.symm.trans ((LinearEquiv.ofEq _ _ hI).trans ek)))

/-- The `C₂`-cofinite form, with no semisimple-Zhu hypothesis (PBW datum explicit). -/
theorem finite_Φ_of_C2Cofinite'
    (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W)))
    (hC2 : C2Cofinite W) : Finite (Φ W) :=
  finite_Φ_of_finiteDimensional Pr (finiteDimensional_A_of_C2Cofinite W hC2)

/-- **Every `C₂`-cofinite VOA has finitely many irreducible modules** (PBW datum supplied by
`voaPBWBottomProjection`, from the theorem `VOA.pbw`;
`#print axioms` is Lean's standard three). -/
theorem finite_Φ_of_C2Cofinite_pbw (hC2 : C2Cofinite W) : Finite (Φ W) :=
  finite_Φ_of_C2Cofinite' (voaPBWBottomProjection (parabolicRepOfAMod W (regularAMod W))) hC2

end VOA.Huang.ZhuFiniteIrr
