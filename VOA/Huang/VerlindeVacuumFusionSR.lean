/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli
-/
import VOA.Huang.VerlindeVacuumFusion
import VOA.Huang.GenusOneG1fSkew
import VOA.Huang.VerlindeRhoPairing
import VOA.Modules.SelfDualContragredient

/-!
# The vacuum-fusion chain without pseudo-unitarity

The theorems below are copies of their `Nice`-hypothesis originals, with `StronglyRational W` in place of
`Nice W`. The originals are untouched. Each original used pseudo-unitarity only through
`VerlindeVacuum.contra_vacuum_equiv` (`M_{v0}′ ≅ V`); here that step is
`contra_vacuum_equiv_of_stronglyRational` (`Modules/SelfDualContragredient.lean`), which uses the
self-duality built into `StronglyRational`.

* `VerlindeVacuum.famFusion_vacuum_le_of_stronglyRational`
* `VerlindeVacuum.famFusion_vacuum_contra_of_stronglyRational`
* `VerlindeVacuum.famFusion_vacuum_ne_zero_of_stronglyRational`
* `GenusOneG1f.vacuum_pairing_le_one_of_stronglyRational`
* `VerlindeRho.one_le_famFusion_contragredient_of_stronglyRational`

`CardyPositivity.vacColumn_mem_K` keeps `Nice`: pseudo-unitarity is essential there (the
statement fails for the non-unitary Lee–Yang model `M(2,5)`).
-/

namespace VOA.Huang.VerlindeVacuum

open VOA VOA.Classification.COne VOA.Huang.VerlindeFusion VOA.Huang.VerlindeEigen
  VOA.Huang.ATransform VOA.Huang.BraidingSkew VOA.Huang.FusionUnit VOA.Huang.HuangODEContra

universe u w

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

section Channel

variable {ι : Type w} [Fintype ι] [DecidableEq ι] (D : VOA.ModularData W ι)

open Classical in
/-- **Upper bound** in famFusion form: `N_{ab}^{v0} ≤ [M_b ≅ M_a']`. -/
theorem famFusion_vacuum_le_of_stronglyRational (hSR : StronglyRational W) (v0 : ι)
    (hv0 : Nonempty (ModuleEquiv W (D.Mfam v0).isMod (adjointModule W))) (a b : ι) :
    famFusion D a b v0
      ≤ if Nonempty (ModuleEquiv W (D.Mfam b).isMod (contragredientModule (D.Mfam a).isMod))
        then 1 else 0 := by
  obtain ⟨e0⟩ := hv0
  obtain ⟨e'⟩ := contra_vacuum_equiv_of_stronglyRational hSR (D.Mfam v0).isMod (D.Mfam v0).irreducible e0
  rw [famFusion, ← fusionRule_swap (D.Mfam a).isMod (D.Mfam b).isMod (D.Mfam v0).isMod]
  exact (vacuum_upper D v0 e' a b).2

/-- **The contragredient vacuum channel**: if `M_a' ≅ M_b` then `N_{ab}^{v0} = 1`
(no irredundancy or completeness needed). -/
theorem famFusion_vacuum_contra_of_stronglyRational (hSR : StronglyRational W) (v0 : ι)
    (hv0 : Nonempty (ModuleEquiv W (D.Mfam v0).isMod (adjointModule W))) (a b : ι)
    (hab : Nonempty (ModuleEquiv W (contragredientModule (D.Mfam a).isMod) (D.Mfam b).isMod)) :
    famFusion D a b v0 = 1 := by
  classical
  obtain ⟨g⟩ := hab
  have hle := famFusion_vacuum_le_of_stronglyRational D hSR v0 hv0 a b
  rw [if_pos ⟨g.symm⟩] at hle
  refine le_antisymm hle ?_
  obtain ⟨e0⟩ := hv0
  obtain ⟨e'⟩ := contra_vacuum_equiv_of_stronglyRational hSR (D.Mfam v0).isMod (D.Mfam v0).irreducible e0
  -- the identifications `I(M_{v0}' / M_a M_a') ≅ I(M_{v0} / M_a M_b)`
  let Emid := equivMid (D.Mfam a).isMod _ (D.Mfam v0).isMod g
  let Eright := equivRight (D.Mfam a).isMod (contragredientModule (D.Mfam a).isMod) _
    (e'.trans e0.symm)
  haveI : FiniteDimensional ℂ (intertwiningSpace (D.Mfam a).isMod (D.Mfam b).isMod
      (D.Mfam v0).isMod) := (vacuum_upper D v0 e' b a).1
  haveI : FiniteDimensional ℂ (intertwiningSpace (D.Mfam a).isMod
      (contragredientModule (D.Mfam a).isMod) (contragredientModule (D.Mfam v0).isMod)) :=
    LinearEquiv.finiteDimensional (Eright.trans Emid).symm
  have h1 : fusionRule (D.Mfam a).isMod (D.Mfam v0).isMod (D.Mfam a).isMod = 1 := by
    rw [← fusionRule_swap (D.Mfam a).isMod (D.Mfam v0).isMod (D.Mfam a).isMod,
      fusionRule_congr_left e0]
    exact fusionRule_adjoint_self (lwOf D a) (lwOf_irreducible D a)
  calc 1 = fusionRule (D.Mfam a).isMod (D.Mfam v0).isMod (D.Mfam a).isMod := h1.symm
    _ ≤ fusionRule (D.Mfam a).isMod (contragredientModule (D.Mfam a).isMod)
        (contragredientModule (D.Mfam v0).isMod) := fusionRule_le_atrans _ _ _
    _ = famFusion D a b v0 := (Eright.trans Emid).finrank_eq

/-- Nonvanishing form of `famFusion_vacuum_contra` (the shape consumed by the `ρ(−1)` reduction). -/
theorem famFusion_vacuum_ne_zero_of_stronglyRational (hSR : StronglyRational W) (v0 : ι)
    (hv0 : Nonempty (ModuleEquiv W (D.Mfam v0).isMod (adjointModule W))) (a b : ι)
    (hab : Nonempty (ModuleEquiv W (contragredientModule (D.Mfam a).isMod) (D.Mfam b).isMod)) :
    famFusion D a b v0 ≠ 0 := by
  rw [famFusion_vacuum_contra_of_stronglyRational D hSR v0 hv0 a b hab]; exact one_ne_zero

end Channel

end VOA.Huang.VerlindeVacuum

namespace VOA.Huang.GenusOneG1f

open VOA.Classification.COne VOA.Huang.VerlindeFusion VOA.Huang.VerlindeEigen
  VOA.Huang.ATransform VOA.Huang.FusionUnit VOA.Huang.HuangODEContra
  VOA.Huang.VerlindeVacuum VOA.Huang.TensorCat VOA.Huang.VerlindeTransport
open VOA.Huang.GenusTwoPoint (vacuumLW)
open VOA.Huang.FusionProduct (postcompose)
open VOA.Huang.GenusOneG1c (piInt epsInt)
open scoped BigOperators

universe u w

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

section Bound

variable {ι : Type w} [Fintype ι] [DecidableEq ι] (D : VOA.ModularData W ι)

/-- **`I(V / M_b M_a)` is finite-dimensional of dimension `≤ 1`** (nice `V`). -/
theorem vacuum_pairing_le_one_of_stronglyRational (hSR : StronglyRational W) (a b : ι) :
    FiniteDimensional ℂ (intertwiningSpace (D.Mfam b).isMod (D.Mfam a).isMod (adjointModule W))
      ∧ fusionRule (D.Mfam b).isMod (D.Mfam a).isMod (adjointModule W) ≤ 1 := by
  classical
  have hirrV : (adjointModule W).IsIrreducible :=
    (isSimple_iff_adjointModule_isIrreducible W).mp hSR.simple
  obtain ⟨e'⟩ := contra_vacuum_equiv_of_stronglyRational hSR (adjointModule W) hirrV (ModuleEquiv.refl _)
  let E : intertwiningSpace (D.Mfam b).isMod (contragredientModule (adjointModule W))
        (contragredientModule (D.Mfam a).isMod)
      ≃ₗ[ℂ] intertwiningSpace (adjointModule W) (D.Mfam b).isMod
        (contragredientModule (D.Mfam a).isMod) :=
    (BraidingSkew.skewEquiv _ _ _ BraidingSkew.omegaPhase_succ
      BraidingSkew.omegaPhase_ne_zero).trans (intertwiningEquivLeft e'.symm)
  have hP₂ := lwOf_irreducible D b
  have hP₃ : (contraLW (lwOf D a)).IsIrreducibleLW :=
    contraLW_isIrreducibleLW (lwOf_irreducible D a)
  haveI hfin : FiniteDimensional ℂ (intertwiningSpace (adjointModule W) (D.Mfam b).isMod
      (contragredientModule (D.Mfam a).isMod)) :=
    finiteDimensional_intertwiningSpace_adjoint (P₂ := lwOf D b) (P₃ := contraLW (lwOf D a))
      hP₂ hP₃
  haveI : FiniteDimensional ℂ (intertwiningSpace (D.Mfam b).isMod
      (contragredientModule (adjointModule W)) (contragredientModule (D.Mfam a).isMod)) :=
    LinearEquiv.finiteDimensional E.symm
  refine ⟨finiteDimensional_of_atrans _ _ _, ?_⟩
  calc fusionRule (D.Mfam b).isMod (D.Mfam a).isMod (adjointModule W)
      ≤ fusionRule (D.Mfam b).isMod (contragredientModule (adjointModule W))
          (contragredientModule (D.Mfam a).isMod) := fusionRule_le_atrans _ _ _
    _ = fusionRule (adjointModule W) (D.Mfam b).isMod (contragredientModule (D.Mfam a).isMod) :=
        E.finrank_eq
    _ ≤ 1 := fusionRule_adjoint_le_one (P₂ := lwOf D b) (P₃ := contraLW (lwOf D a)) hP₂ hP₃

end Bound

end VOA.Huang.GenusOneG1f

namespace VOA.Huang.VerlindeRho

open VOA VOA.Classification.COne VOA.Huang.VerlindeFusion
  VOA.Huang.VerlindeVacuum VOA.Huang.ATransform VOA.Huang.FusionUnit
  VOA.Huang.BraidingSkew

universe u w
variable {V : Type u} [AddCommGroup V] [Module ℂ V]
variable {W : VertexOperatorAlgebra V}
variable {ι : Type w} [Fintype ι] [DecidableEq ι]

/-- The contragredient-labelled vacuum fusion rule is positive, without a
completeness, irredundancy, or modularity hypothesis. -/
theorem one_le_famFusion_contragredient_of_stronglyRational (hSR : StronglyRational W) (D : VOA.ModularData W ι)
    (v0 : ι) (e0 : ModuleEquiv W (D.Mfam v0).isMod (adjointModule W))
    (a b : ι) (g : ModuleEquiv W (contragredientModule (D.Mfam a).isMod)
      (D.Mfam b).isMod) : 1 ≤ famFusion D a b v0 := by
  obtain ⟨e'⟩ := contra_vacuum_equiv_of_stronglyRational hSR (D.Mfam v0).isMod (D.Mfam v0).irreducible e0
  let Emid := intertwiningEquivMid (A₁ := (D.Mfam a).isMod)
    (A₃ := (D.Mfam v0).isMod) g
  let Eright := intertwiningEquivRight (A₁ := (D.Mfam a).isMod)
    (A₂ := contragredientModule (D.Mfam a).isMod) (e'.trans e0.symm)
  haveI : FiniteDimensional ℂ
      (intertwiningSpace (D.Mfam a).isMod (D.Mfam b).isMod (D.Mfam v0).isMod) :=
    (vacuum_upper D v0 e' b a).1
  haveI : FiniteDimensional ℂ (intertwiningSpace (D.Mfam a).isMod
      (contragredientModule (D.Mfam a).isMod)
      (contragredientModule (D.Mfam v0).isMod)) :=
    LinearEquiv.finiteDimensional (Eright.trans Emid).symm
  have hunit : fusionRule (D.Mfam a).isMod (D.Mfam v0).isMod (D.Mfam a).isMod = 1 := by
    rw [← fusionRule_swap (D.Mfam a).isMod (D.Mfam v0).isMod (D.Mfam a).isMod,
      fusionRule_congr_left e0]
    exact fusionRule_adjoint_self (lwOf D a) (lwOf_irreducible D a)
  calc
    1 = fusionRule (D.Mfam a).isMod (D.Mfam v0).isMod (D.Mfam a).isMod := hunit.symm
    _ ≤ fusionRule (D.Mfam a).isMod (contragredientModule (D.Mfam a).isMod)
        (contragredientModule (D.Mfam v0).isMod) := fusionRule_le_atrans _ _ _
    _ = famFusion D a b v0 := (Eright.trans Emid).finrank_eq

end VOA.Huang.VerlindeRho

section AxiomAudit
#print axioms VOA.Huang.VerlindeVacuum.famFusion_vacuum_ne_zero_of_stronglyRational
#print axioms VOA.Huang.GenusOneG1f.vacuum_pairing_le_one_of_stronglyRational
#print axioms VOA.Huang.VerlindeRho.one_le_famFusion_contragredient_of_stronglyRational
end AxiomAudit
