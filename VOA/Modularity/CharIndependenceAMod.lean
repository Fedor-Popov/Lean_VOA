/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.CharIndependence
import VOA.Modularity.AModBridge

/-!
# The separating character, in the repo's `AMod` language

`Modularity.CharIndependence.exists_trace_separating` is stated for an abstract ring `R`.  This file
discharges its two instance side conditions and restates it for a family of bundled `AMod 𝒱`s, which
is the form residual **(d)**'s peeling argument consumes: a **vector `v ∈ 𝒱`** whose bottom
character is nonzero on one member of the family and zero on the others.

## The two side conditions

* `IsSemisimpleModule R (∀ l, U l)` — the ranges of `LinearMap.single` are simple (transport along
  `LinearEquiv.ofInjective`) and span, so `IsSemisimpleModule.of_sSup_simples_eq_top` applies;
* `Module.Finite (End R M) M` — from `Module.Finite ℂ M` along the tower `ℂ → End R M → M`
  (`Module.Finite.of_restrictScalars_finite`), which needs `SMulCommClass R ℂ M`; for an `AMod` that
  is the banked `AMod.smul_comm_C`.

## Main results

* `isSemisimpleModule_pi_of_simple`;
* `exists_vector_trace_separating` — the separating **vector**.

## Status
Proved, axiom-clean, `pbw`-free, no `sorry`.
-/

namespace VOA

open Module (End)

section Semisimple

universe uR uU

variable {R : Type uR} [Ring R] {r : ℕ} (U : Fin r → Type uU)
  [∀ k, AddCommGroup (U k)] [∀ k, Module R (U k)]

/-- The range of the `k`-th inclusion is simple. -/
theorem isSimpleModule_range_single (hsimp : ∀ k, IsSimpleModule R (U k)) (k : Fin r) :
    IsSimpleModule R (LinearMap.range (LinearMap.single R U k)) := by
  haveI := hsimp k
  have hinj : Function.Injective (LinearMap.single R U k) := by
    intro x y hxy
    have := congrFun hxy k
    simpa using this
  exact IsSimpleModule.congr (LinearEquiv.ofInjective _ hinj).symm

/-- A finite product of simple modules is semisimple. -/
theorem isSemisimpleModule_pi_of_simple (hsimp : ∀ k, IsSimpleModule R (U k)) :
    IsSemisimpleModule R (∀ l, U l) := by
  classical
  refine IsSemisimpleModule.of_sSup_simples_eq_top ?_
  refine le_antisymm le_top ?_
  intro x _
  have hx : x = ∑ l : Fin r, Pi.single l (x l) := by rw [Finset.univ_sum_single]
  rw [hx]
  refine Submodule.sum_mem _ fun l _ => ?_
  refine le_sSup (show LinearMap.range (LinearMap.single R U l)
      ∈ {m : Submodule R (∀ k, U k) | IsSimpleModule R m} from
    isSimpleModule_range_single U hsimp l) ?_
  exact ⟨x l, rfl⟩

end Semisimple

section AModFamily

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

/-- **`ℂ` acts through `A(𝒱)`**: `algebraMap ℂ (A 𝒱) c` acts as the scalar `c`. -/
theorem AMod.algebraMap_smul_eq (U : AMod W) (c : ℂ) (x : U.carrier) :
    letI := instRingA W; letI := instAlgebraA W; letI := U.moduleA
    (algebraMap ℂ (A W) c) • x = c • x := by
  letI := instRingA W
  letI := instAlgebraA W
  letI := U.moduleA
  rw [AMod.smul_def, Algebra.algebraMap_eq_smul_one, map_smul]
  change c • (U.ρ (1 : A W)) x = c • x
  rw [show (1 : A W) = one W from rfl, U.ρ_one]
  rfl

/-- An `AMod`-isomorphism is an `A(𝒱)`-linear equivalence. -/
noncomputable def AModEquiv.toLinearEquivA {P Q : AMod W} (e : AModEquiv W P Q) :
    letI := instRingA W; letI := P.moduleA; letI := Q.moduleA
    P.carrier ≃ₗ[A W] Q.carrier :=
  letI := instRingA W; letI := P.moduleA; letI := Q.moduleA
  { e.toLinearEquiv with
    map_smul' := fun a x => by
      show e.toLinearEquiv (P.ρ a x) = Q.ρ a (e.toLinearEquiv x)
      exact e.map_ρ a x }

/-- **The separating vector.**  For a finite family of pairwise non-isomorphic simple bundled
`A(𝒱)`-modules, finite-dimensional over `ℂ`, there is a **vector of `𝒱`** whose bottom character is
nonzero on the `k`-th member and zero on all the others. -/
theorem exists_vector_trace_separating {r : ℕ} (U : Fin r → AMod W)
    (hfd : ∀ k, FiniteDimensional ℂ (U k).carrier)
    (hsimp : ∀ k, IsSimpleAMod (U k))
    (hne : ∀ k l : Fin r, k ≠ l → IsEmpty (AModEquiv W (U k) (U l))) (k : Fin r) :
    ∃ v : 𝒱,
      LinearMap.trace ℂ (U k).carrier ((U k).ρ (mk W v)) ≠ 0 ∧
        ∀ l : Fin r, l ≠ k → LinearMap.trace ℂ (U l).carrier ((U l).ρ (mk W v)) = 0 := by
  classical
  letI := instRingA W
  letI : ∀ l, Module (A W) (U l).carrier := fun l => (U l).moduleA
  haveI : ∀ l, IsSimpleModule (A W) (U l).carrier := fun l =>
    (isSimpleAMod_iff_isSimpleModule (U l)).mp (hsimp l)
  haveI : ∀ l, SMulCommClass (A W) ℂ (U l).carrier := fun l =>
    ⟨fun a c x => by
      rw [AMod.smul_def, AMod.smul_def]
      exact ((U l).ρ a).map_smul c x⟩
  haveI : ∀ l, FiniteDimensional ℂ (U l).carrier := hfd
  haveI hss : IsSemisimpleModule (A W) (∀ l, (U l).carrier) :=
    isSemisimpleModule_pi_of_simple (fun l => (U l).carrier) (fun l => inferInstance)
  haveI : SMulCommClass (A W) ℂ (∀ l, (U l).carrier) :=
    ⟨fun a c x => funext fun l => (SMulCommClass.smul_comm a c (x l))⟩
  haveI : Module.Finite ℂ (∀ l, (U l).carrier) := Module.Finite.pi
  haveI hfin : Module.Finite (Module.End (A W) (∀ l, (U l).carrier)) (∀ l, (U l).carrier) :=
    Module.Finite.of_restrictScalars_finite ℂ
      (Module.End (A W) (∀ l, (U l).carrier)) (∀ l, (U l).carrier)
  have hneA : ∀ k l : Fin r, k ≠ l →
      IsEmpty ((U k).carrier ≃ₗ[A W] (U l).carrier) := by
    intro k l hkl
    refine ⟨fun e => ?_⟩
    refine (hne k l hkl).false ?_
    letI := instAlgebraA W
    refine { toLinearEquiv := { e.toAddEquiv with
              map_smul' := fun c x => ?_ }
             map_ρ := fun a x => ?_ }
    · change e (c • x) = c • e x
      rw [← AMod.algebraMap_smul_eq (U k) c x, e.map_smul,
        AMod.algebraMap_smul_eq (U l) c (e x)]
    · change e ((U k).ρ a x) = (U l).ρ a (e x)
      rw [← AMod.smul_def, e.map_smul, AMod.smul_def]
  obtain ⟨a, hk, hl⟩ := exists_trace_separating (R := A W) (fun l => (U l).carrier)
    (fun l => inferInstance) hneA k
  obtain ⟨v, rfl⟩ := _root_.VOA.mk_surjective W a
  refine ⟨v, ?_, ?_⟩
  · convert hk using 2
  · intro l hlk
    convert hl l hlk using 2

end AModFamily

end VOA
