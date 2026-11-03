/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.ATransformDual
import VOA.Huang.VerlindeEigen

/-!
# Fusion into the vacuum: `N_{ab}^{V} = δ_{b, a'}`

For a nice VOA and a complete irredundant family with vacuum label `v0`, this file proves
`vacuumFusionInput : VacuumFusionInput` (`VOA/Huang/VerlindeEigen.lean`): there is a
relabelling `σ` (the index of the contragredient, `M_{σa} ≅ M_a'`) with `N_{ab}^{v0} = δ_{b,σa}`.

Route (FHL Props. 5.5.2 and 5.4.7):

* `contra_vacuum_equiv` — `M_{v0}' ≅ V`: the contragredient of the vacuum module is irreducible
  (`contragredient_isIrreducible`) with a nonzero weight-`0` space, so pseudo-unitarity forces
  `M_{v0}' ≅ V`;
* `vacuum_upper`, `famFusion_vacuum_le` — `I(M_{v0} / M_b M_a) ↪ I(M_a' / M_b M_{v0}')`
  (`atransMap`, injective), and `I(M_a' / M_b M_{v0}') ≅ I(M_a' / M_{v0}' M_b) ≅ I(M_a' / V M_b)`
  (skew-symmetry, `M_{v0}' ≅ V`), of dimension `[M_b ≅ M_a']` (`fusionRule_adjoint_eq`);
* `famFusion_vacuum_contra` — if `M_a' ≅ M_b` then `N_{ab}^{v0} = 1` (no irredundancy):
  `N_{ab}^{v0} = N^{M_{v0}'}_{a, a'} ≥ N^{M_a}_{a, v0} = N^{M_a}_{v0, a} = 1`
  (`fusionRule_le_atrans`, skew-symmetry, `fusionRule_adjoint_self`);
  `famFusion_vacuum_ne_zero` is its nonvanishing form.

Consequences: `chargeConjugationInput_of_rhoNegOne : RhoNegOneInput → ChargeConjugationInput` and
`huangVerlindeFusionInput_of_eigen_rho : FusionEigenInput → RhoNegOneInput →
HuangVerlindeFusionInput`.

The genus-one input of Huang's §5 is not used. `VOA.pbw` is not used.

## Status
No `sorry`, no new axioms.
-/

namespace VOA.Huang.VerlindeVacuum

open VOA VOA.Classification.COne VOA.Huang.VerlindeFusion VOA.Huang.VerlindeEigen
  VOA.Huang.ATransform VOA.Huang.BraidingSkew VOA.Huang.FusionUnit VOA.Huang.HuangODEContra

universe u w

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

/-! ## Module isomorphisms in the second and third slots -/

section Congr

variable {M₁ M₂ M₃ M₄ : Type u} [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂]
  [Module ℂ M₂] [AddCommGroup M₃] [Module ℂ M₃] [AddCommGroup M₄] [Module ℂ M₄]
  {A₁ : OrdVModule W M₁} {A₂ : OrdVModule W M₂} {A₃ : OrdVModule W M₃}
  {A₄ : OrdVModule W M₄}

/-- A module isomorphism in the third slot identifies the intertwiner spaces
(`ATransform.equivRight` with implicit modules). -/
noncomputable def intertwiningEquivRight (e : ModuleEquiv W A₃ A₄) :
    intertwiningSpace A₁ A₂ A₃ ≃ₗ[ℂ] intertwiningSpace A₁ A₂ A₄ :=
  equivRight A₁ A₂ A₃ e

/-- A module isomorphism in the second slot identifies the intertwiner spaces
(`ATransform.equivMid` with implicit modules). -/
noncomputable def intertwiningEquivMid (e : ModuleEquiv W A₂ A₄) :
    intertwiningSpace A₁ A₂ A₃ ≃ₗ[ℂ] intertwiningSpace A₁ A₄ A₃ :=
  equivMid A₁ A₂ A₃ e

end Congr

/-! ## The contragredient of the vacuum module -/

section Vacuum

variable {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- The weight-`h` space of the contragredient is nonzero when that of the module is. -/
theorem contragredient_weight_ne_bot (A : OrdVModule W M) {h : ℂ} (hh : A.weight h ≠ ⊥) :
    (contragredientModule A).weight h ≠ ⊥ := by
  classical
  haveI : ∀ α, FiniteDimensional ℂ (A.weight α) := A.finrank
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hh
  obtain ⟨g, hg⟩ : ∃ g : Module.Dual ℂ (A.weight h), g ⟨x, hx⟩ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have := (Module.forall_dual_apply_eq_zero_iff ℂ (⟨x, hx⟩ : A.weight h)).mp hcon
    exact hx0 (congrArg Subtype.val this)
  intro hbot
  have hmem : DirectSum.lof ℂ ℂ (fun β => Module.Dual ℂ (A.weight β)) h g
      ∈ (contragredientModule A).weight h := ⟨g, rfl⟩
  rw [hbot] at hmem
  erw [Submodule.mem_bot] at hmem
  have := congrArg (cmp A h) hmem
  erw [DirectSum.component.lof_self, map_zero] at this
  exact hg (by rw [this]; rfl)

/-- A module isomorphic to `V` has a nonzero weight-`0` space (given a nontrivial carrier). -/
theorem weight_zero_ne_bot (A : OrdVModule W M) [Nontrivial M]
    (e : ModuleEquiv W A (adjointModule W)) : A.weight 0 ≠ ⊥ := by
  have hvac : W.vacuum ≠ 0 := by
    intro h0
    obtain ⟨x, hx⟩ := exists_ne (0 : M)
    have h1 := WeakModule.act_vacuum A.toWeakModule (-1) x
    rw [if_pos rfl, h0] at h1
    apply hx
    rw [← h1, WeakModule.act_def, map_zero, mode_zero, LinearMap.zero_apply]
  set x0 : M := e.symm.toLinearEquiv W.vacuum with hx0
  have hx0ne : x0 ≠ 0 := by
    rw [hx0]; exact (LinearEquiv.map_ne_zero_iff _).mpr hvac
  have hmem : x0 ∈ A.weight 0 := by
    apply eigenvector_mem_weight A
    have h := e.symm.map_act W.conformalVector 1 W.vacuum
    rw [WeakModule.act_def, WeakModule.act_def] at h
    have hL : mode ((adjointModule W).YM W.conformalVector) 1 W.vacuum = (0 : ℂ) • W.vacuum := by
      have := W.L0_grading W.vacuum W.vacuum_mem_grading_zero
      simpa using this
    rw [hL, map_smul] at h
    rw [hx0, ← h]
  intro hbot
  rw [hbot] at hmem
  exact hx0ne ((Submodule.mem_bot ℂ).mp hmem)

/-- **`M_{v0}' ≅ V`** for a nice `V` and an irreducible module `M_{v0} ≅ V`: the contragredient
is irreducible with a nonzero weight-`0` space, so pseudo-unitarity forces it to be `≅ V`. -/
theorem contra_vacuum_equiv (hV : Nice W) (A : OrdVModule W M) (hirr : A.IsIrreducible)
    (e : ModuleEquiv W A (adjointModule W)) :
    Nonempty (ModuleEquiv W (contragredientModule A) (adjointModule W)) := by
  haveI : Nontrivial M := hirr.1
  have h0 := weight_zero_ne_bot A e
  have hirr' := contragredient_isIrreducible A h0 hirr
  by_contra hne
  have hpos := hV.2 (RestrictedDual A) (contragredientModule A) hirr' (not_nonempty_iff.mp hne) 0
    (contragredient_weight_ne_bot A h0)
  simp at hpos

end Vacuum

/-! ## The fusion rules into the vacuum -/

section Fusion

variable {ι : Type w} [Fintype ι] [DecidableEq ι] (D : VOA.ModularData W ι)

/-- The contragredient of a family member, as a bundled irreducible module. -/
noncomputable def contraIrr (a : ι) : IrrModule W where
  carrier := RestrictedDual (D.Mfam a).isMod
  isMod := contragredientModule (D.Mfam a).isMod
  irreducible := contragredient_isIrreducible _ (D.hasWeight a).1 (D.Mfam a).irreducible

open Classical in
/-- **Upper bound**: `I(M_{v0} / M_y M_x)` is finite-dimensional, of dimension
`≤ [M_y ≅ M_x']`. -/
theorem vacuum_upper (v0 : ι) (e' : ModuleEquiv W (contragredientModule (D.Mfam v0).isMod)
      (adjointModule W)) (x y : ι) :
    FiniteDimensional ℂ (intertwiningSpace (D.Mfam y).isMod (D.Mfam x).isMod (D.Mfam v0).isMod)
      ∧ fusionRule (D.Mfam y).isMod (D.Mfam x).isMod (D.Mfam v0).isMod
        ≤ if Nonempty (ModuleEquiv W (D.Mfam y).isMod (contragredientModule (D.Mfam x).isMod))
          then 1 else 0 := by
  classical
  -- the target space of the `A`-transform, identified with `I(M_x' / V M_y)`
  let E : intertwiningSpace (D.Mfam y).isMod (contragredientModule (D.Mfam v0).isMod)
        (contragredientModule (D.Mfam x).isMod)
      ≃ₗ[ℂ] intertwiningSpace (adjointModule W) (D.Mfam y).isMod
        (contragredientModule (D.Mfam x).isMod) :=
    (skewEquiv _ _ _ omegaPhase_succ omegaPhase_ne_zero).trans
      (intertwiningEquivLeft e'.symm)
  have hP₂ := lwOf_irreducible D y
  have hP₃ : (contraLW (lwOf D x)).IsIrreducibleLW :=
    contraLW_isIrreducibleLW (lwOf_irreducible D x)
  haveI hfin : FiniteDimensional ℂ (intertwiningSpace (adjointModule W) (D.Mfam y).isMod
      (contragredientModule (D.Mfam x).isMod)) :=
    finiteDimensional_intertwiningSpace_adjoint (P₂ := lwOf D y) (P₃ := contraLW (lwOf D x))
      hP₂ hP₃
  haveI : FiniteDimensional ℂ (intertwiningSpace (D.Mfam y).isMod
      (contragredientModule (D.Mfam v0).isMod) (contragredientModule (D.Mfam x).isMod)) :=
    LinearEquiv.finiteDimensional E.symm
  refine ⟨finiteDimensional_of_atrans _ _ _, ?_⟩
  calc fusionRule (D.Mfam y).isMod (D.Mfam x).isMod (D.Mfam v0).isMod
      ≤ fusionRule (D.Mfam y).isMod (contragredientModule (D.Mfam v0).isMod)
          (contragredientModule (D.Mfam x).isMod) := fusionRule_le_atrans _ _ _
    _ = fusionRule (adjointModule W) (D.Mfam y).isMod (contragredientModule (D.Mfam x).isMod) :=
        E.finrank_eq
    _ = _ := fusionRule_adjoint_eq (P₂ := lwOf D y) (P₃ := contraLW (lwOf D x)) hP₂ hP₃

end Fusion

/-! ## The vacuum channel -/

section Channel

variable {ι : Type w} [Fintype ι] [DecidableEq ι] (D : VOA.ModularData W ι)

open Classical in
/-- **Upper bound** in famFusion form: `N_{ab}^{v0} ≤ [M_b ≅ M_a']`. -/
theorem famFusion_vacuum_le (hV : Nice W) (v0 : ι)
    (hv0 : Nonempty (ModuleEquiv W (D.Mfam v0).isMod (adjointModule W))) (a b : ι) :
    famFusion D a b v0
      ≤ if Nonempty (ModuleEquiv W (D.Mfam b).isMod (contragredientModule (D.Mfam a).isMod))
        then 1 else 0 := by
  obtain ⟨e0⟩ := hv0
  obtain ⟨e'⟩ := contra_vacuum_equiv hV (D.Mfam v0).isMod (D.Mfam v0).irreducible e0
  rw [famFusion, ← fusionRule_swap (D.Mfam a).isMod (D.Mfam b).isMod (D.Mfam v0).isMod]
  exact (vacuum_upper D v0 e' a b).2

/-- **The contragredient vacuum channel**: if `M_a' ≅ M_b` then `N_{ab}^{v0} = 1`
(no irredundancy or completeness needed). -/
theorem famFusion_vacuum_contra (hV : Nice W) (v0 : ι)
    (hv0 : Nonempty (ModuleEquiv W (D.Mfam v0).isMod (adjointModule W))) (a b : ι)
    (hab : Nonempty (ModuleEquiv W (contragredientModule (D.Mfam a).isMod) (D.Mfam b).isMod)) :
    famFusion D a b v0 = 1 := by
  classical
  obtain ⟨g⟩ := hab
  have hle := famFusion_vacuum_le D hV v0 hv0 a b
  rw [if_pos ⟨g.symm⟩] at hle
  refine le_antisymm hle ?_
  obtain ⟨e0⟩ := hv0
  obtain ⟨e'⟩ := contra_vacuum_equiv hV (D.Mfam v0).isMod (D.Mfam v0).irreducible e0
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
theorem famFusion_vacuum_ne_zero (hV : Nice W) (v0 : ι)
    (hv0 : Nonempty (ModuleEquiv W (D.Mfam v0).isMod (adjointModule W))) (a b : ι)
    (hab : Nonempty (ModuleEquiv W (contragredientModule (D.Mfam a).isMod) (D.Mfam b).isMod)) :
    famFusion D a b v0 ≠ 0 := by
  rw [famFusion_vacuum_contra D hV v0 hv0 a b hab]; exact one_ne_zero

end Channel

/-! ## The theorem -/

/-- **Fusion into the vacuum** (FHL Props. 5.5.2, 5.4.7): for a nice VOA and a complete
irredundant family with vacuum label `v0`, `N_{ab}^{v0} = δ_{b,σa}`, `σa` the label of `M_a'`. -/
theorem vacuumFusionInput : VacuumFusionInput.{u, w} := by
  intro 𝒱 _ _ W hNice ι _ _ D _ hirr hcomp v0 hv0
  classical
  choose σ hσ using fun a => hcomp (contraIrr D a)
  refine ⟨σ, fun a b => ?_⟩
  have hiff : Nonempty (ModuleEquiv W (D.Mfam b).isMod (contragredientModule (D.Mfam a).isMod))
      ↔ b = σ a := by
    constructor
    · rintro ⟨f⟩
      obtain ⟨g⟩ := hσ a
      exact hirr b (σ a) ⟨f.trans g⟩
    · rintro rfl
      obtain ⟨g⟩ := hσ a
      exact ⟨g.symm⟩
  split_ifs with hb
  · subst hb
    exact famFusion_vacuum_contra D hNice v0 hv0 a (σ a) (hσ a)
  · have hle := famFusion_vacuum_le D hNice v0 hv0 a b
    rw [if_neg (mt hiff.mp hb)] at hle
    omega

/-- **Charge conjugation reduced to `ρ(−1) = C`**: with the fusion rule into the vacuum
proved, `RhoNegOneInput → ChargeConjugationInput`. -/
theorem chargeConjugationInput_of_rhoNegOne (hR : RhoNegOneInput.{u, w}) :
    ChargeConjugationInput.{u, w} :=
  chargeConjugationInput_of vacuumFusionInput hR

/-- **The Verlinde package from Huang's Theorem 5.2 and `ρ(−1) = C`.** -/
theorem huangVerlindeFusionInput_of_eigen_rho (hE : FusionEigenInput.{u, w})
    (hR : RhoNegOneInput.{u, w}) : HuangVerlindeFusionInput.{u, w} :=
  huangVerlindeFusionInput_of_three hE vacuumFusionInput hR

end VOA.Huang.VerlindeVacuum
