/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli
-/
import VOA.Modules.ContragredientClose
import VOA.Modules.ContragredientTransport
import VOA.Modules.StronglyRational

/-!
# A nondegenerate invariant form identifies a module with its contragredient

* `ModuleForm N`: a bilinear form on an ordinary module `N` with three properties: it is fully invariant
  (the module form of `InvariantForm.IsFullyInvariant`), it makes distinct weight spaces orthogonal, and it
  is left-nondegenerate.
* `ModuleForm.contraEquiv : ModuleEquiv W N (contragredientModule N)`, given by `a ↦ (a | ·)`.
  - It intertwines the actions because the contragredient mode is the transpose of the twisted mode
    (`dualPairing_mode_adj`), and full invariance identifies the two.
  - It is injective by nondegeneracy.
  - It is surjective weight by weight: each weight space is finite-dimensional, and the form is
    nondegenerate on it.
* `contragredient_equiv_of_selfDual`: if `W.SelfDual` and `A ≅ V`, then `A′ ≅ V`. The form on `A` is
  `(e·|e·)`.
* `contra_vacuum_equiv_of_stronglyRational`: the conclusion of `VerlindeVacuumFusion.contra_vacuum_equiv`,
  with `StronglyRational W` in place of `Nice W`. **No pseudo-unitarity.**
-/

namespace VOA

open Module (Dual)
open Classical
open VertexOperatorAlgebra (InvariantForm)

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
  {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- A fully invariant, weight-orthogonal, left-nondegenerate bilinear form on an ordinary module. -/
structure ModuleForm (N : OrdVModule W M) where
  β : M →ₗ[ℂ] M →ₗ[ℂ] ℂ
  ortho : ∀ (α γ : ℂ) (x y : M), x ∈ N.weight α → y ∈ N.weight γ → α ≠ γ → β x y = 0
  full : ∀ (wt : ℤ) (u : 𝒱), u ∈ W.grading wt → ∀ (n : ℤ) (x y : M),
    β (mode (N.YM u) n x) y = (-1 : ℂ) ^ wt • ∑ j ∈ Finset.range (wt.toNat + 1),
      ((j.factorial : ℂ)⁻¹) • β x (mode (N.YM ((W.L 1 ^ j) u)) (2 * wt - n - 2 - (j : ℤ)) y)
  nondeg : ∀ x : M, (∀ y, β x y = 0) → x = 0

namespace ModuleForm

variable {N : OrdVModule W M} (F : ModuleForm N)

/-- `(x|·)` restricted to a weight space. -/
noncomputable def ψ (α : ℂ) : N.weight α →ₗ[ℂ] Dual ℂ (N.weight α) :=
  (F.β.compl₂ (N.weight α).subtype).comp (N.weight α).subtype

/-- One weight space's contribution, typed into the restricted dual. -/
noncomputable def piece (α : ℂ) : N.weight α →ₗ[ℂ] RestrictedDual N :=
  (DirectSum.lof ℂ ℂ (fun β => Dual ℂ (N.weight β)) α).comp (F.ψ α)

/-- The map `a ↦ (a|·)` into the restricted dual. -/
noncomputable def Φ : M →ₗ[ℂ] RestrictedDual N :=
  letI := N.isInternal.chooseDecomposition
  (DirectSum.toModule ℂ ℂ (RestrictedDual N) F.piece).comp
    (DirectSum.decomposeLinearEquiv N.weight).toLinearMap

theorem Φ_of_mem {α : ℂ} {x : M} (hx : x ∈ N.weight α) :
    F.Φ x = DirectSum.lof ℂ ℂ (fun β => Dual ℂ (N.weight β)) α (F.ψ α ⟨x, hx⟩) := by
  letI := N.isInternal.chooseDecomposition
  simp only [Φ, LinearMap.comp_apply, LinearEquiv.coe_coe, DirectSum.decomposeLinearEquiv_apply]
  rw [DirectSum.decompose_of_mem N.weight hx]
  erw [DirectSum.toModule_lof]
  rfl

omit F in
theorem mem_iSup (x : M) : x ∈ ⨆ α, N.weight α := by
  rw [N.isInternal.submodule_iSup_eq_top]; trivial

/-- **The pairing reads off the form**: `⟨x, Φ a⟩ = (a|x)`. -/
theorem dualPairing_Φ (a x : M) : dualPairing N x (F.Φ a) = F.β a x := by
  classical
  induction mem_iSup (N := N) a using Submodule.iSup_induction' generalizing x with
  | mem α a ha =>
      induction mem_iSup (N := N) x using Submodule.iSup_induction' with
      | mem γ x hx =>
          rw [dualPairing_component N _ hx, F.Φ_of_mem ha]
          by_cases hαγ : α = γ
          · subst hαγ
            rw [DirectSum.component.lof_self]
            rfl
          · rw [DirectSum.component.of, dif_neg hαγ, F.ortho α γ a x ha hx hαγ]
            rfl
      | zero =>
          have h := dualPairing_smul_left N (0 : ℂ) (0 : M) (F.Φ a)
          rwa [zero_smul, zero_smul, ← (F.β a).map_zero] at h
      | add x x' _ _ h h' => rw [dualPairing_add_left, h, h', map_add]
  | zero => simp
  | add a a' _ _ h h' => rw [map_add, map_add, h x, h' x, map_add, LinearMap.add_apply]

/-- The contragredient mode is computed by the form (homogeneous `u`). -/
theorem Φ_act_homog {wt : ℤ} {u : 𝒱} (hu : u ∈ W.grading wt) (n : ℤ) (a : M) :
    F.Φ (mode (N.YM u) n a) = mode (YMdual N u) n (F.Φ a) := by
  refine restrictedDual_ext_of_pairing N fun γ x hx => ?_
  rw [dualPairing_Φ, dualPairing_mode_adj N hu n (F.Φ a) hx, dualPairing_Φ, F.full wt u hu n a x]
  simp only [adjVec, Submodule.coe_smul, Submodule.coe_sum, map_smul, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  rw [internalProjTo_coe_mem N (by
    have h := twistMode_mem_weight N hu hx n j
    convert h using 2)]

/-- **`a ↦ (a|·)` intertwines the action with the contragredient action.** -/
theorem Φ_act (u : 𝒱) (n : ℤ) (a : M) :
    F.Φ (mode (N.YM u) n a) = mode (YMdual N u) n (F.Φ a) := by
  have hu : u ∈ ⨆ w, W.grading w := by rw [W.isInternal.submodule_iSup_eq_top]; trivial
  induction hu using Submodule.iSup_induction' with
  | mem w u hu => exact F.Φ_act_homog hu n a
  | zero => simp [mode]
  | add u u' _ _ h h' =>
      rw [map_add, mode_add, LinearMap.add_apply, map_add, h, h', map_add (YMdual N), mode_add,
        LinearMap.add_apply]

theorem Φ_injective : Function.Injective F.Φ := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  refine F.nondeg a fun y => ?_
  rw [← dualPairing_Φ, ha]
  have h := dualPairing_smul_left N (0 : ℂ) y (0 : RestrictedDual N)
  simp

theorem ψ_injective (α : ℂ) : Function.Injective (F.ψ α) := by
  rw [injective_iff_map_eq_zero]
  intro y hy
  apply Subtype.ext
  refine F.nondeg y fun z => ?_
  induction mem_iSup (N := N) z using Submodule.iSup_induction' with
  | mem γ z hz =>
      by_cases hαγ : α = γ
      · subst hαγ
        have := LinearMap.congr_fun hy ⟨z, hz⟩
        simpa [ψ] using this
      · exact F.ortho α γ y z y.2 hz hαγ
  | zero => exact map_zero _
  | add z z' _ _ h h' => rw [map_add, h, h', add_zero]

theorem ψ_surjective (α : ℂ) : Function.Surjective (F.ψ α) := by
  haveI := N.finrank α
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (Subspace.dual_finrank_eq).symm).mp (F.ψ_injective α)

theorem Φ_surjective : Function.Surjective F.Φ := by
  intro f
  refine DirectSum.induction_on (β := fun β => Dual ℂ (N.weight β)) f ?_ ?_ ?_
  · exact ⟨0, map_zero _⟩
  · intro α g
    obtain ⟨y, rfl⟩ := F.ψ_surjective α g
    exact ⟨y, F.Φ_of_mem y.2⟩
  · rintro f₁ f₂ ⟨a₁, rfl⟩ ⟨a₂, rfl⟩
    exact ⟨a₁ + a₂, map_add _ _ _⟩

/-- **A module with a nondegenerate fully invariant form is isomorphic to its contragredient.** -/
noncomputable def contraEquiv : ModuleEquiv W N (contragredientModule N) where
  toLinearEquiv := LinearEquiv.ofBijective F.Φ ⟨F.Φ_injective, F.Φ_surjective⟩
  map_act u n x := F.Φ_act u n x

end ModuleForm

/-! ## Transport of the VOA's invariant form along `A ≅ V` -/

/-- The invariant form of `W`, pulled back along a module isomorphism `A ≅ V`. -/
noncomputable def ModuleForm.ofEquiv {A : OrdVModule W M} (e : ModuleEquiv W A (adjointModule W))
    (B : InvariantForm W) (hfull : B.IsFullyInvariant) (hrad : InvariantForm.leftRadical B = ⊥) :
    ModuleForm A where
  β := (B.form.compl₂ e.toLinearEquiv.toLinearMap).comp e.toLinearEquiv.toLinearMap
  ortho α γ x y hx hy hαγ := by
    show B.form (e.toLinearEquiv x) (e.toLinearEquiv y) = 0
    have hL0x : W.L 0 (e.toLinearEquiv x) = α • e.toLinearEquiv x := by
      have h := e.map_act W.conformalVector 1 x
      rw [show A.toWeakModule.act W.conformalVector 1 x = α • x from A.L0_weight α x hx,
        map_smul] at h
      exact h.symm
    have hL0y : W.L 0 (e.toLinearEquiv y) = γ • e.toLinearEquiv y := by
      have h := e.map_act W.conformalVector 1 y
      rw [show A.toWeakModule.act W.conformalVector 1 y = γ • y from A.L0_weight γ y hy,
        map_smul] at h
      exact h.symm
    have hadj := B.L0_adj (e.toLinearEquiv x) (e.toLinearEquiv y)
    rw [hL0x, hL0y, map_smul, LinearMap.smul_apply, map_smul, smul_eq_mul, smul_eq_mul] at hadj
    have : (α - γ) * B.form (e.toLinearEquiv x) (e.toLinearEquiv y) = 0 := by
      rw [sub_mul, hadj, sub_self]
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hαγ)
  full wt u hu n x y := by
    show B.form (e.toLinearEquiv (A.toWeakModule.act u n x)) (e.toLinearEquiv y) = _
    rw [e.map_act]
    show B.form (W.smul u n (e.toLinearEquiv x)) (e.toLinearEquiv y) = _
    rw [hfull wt u hu n]
    refine congrArg _ (Finset.sum_congr rfl fun j _ => congrArg _ ?_)
    show _ = B.form (e.toLinearEquiv x)
        (e.toLinearEquiv (A.toWeakModule.act ((W.L 1 ^ j) u) (2 * wt - n - 2 - (j : ℤ)) y))
    rw [e.map_act]
    rfl
  nondeg x hx := by
    have hrad' : e.toLinearEquiv x ∈ InvariantForm.leftRadical B := by
      rw [InvariantForm.mem_leftRadical]
      refine LinearMap.ext fun z => ?_
      obtain ⟨y, rfl⟩ := e.toLinearEquiv.surjective z
      exact hx y
    rw [hrad, Submodule.mem_bot] at hrad'
    exact e.toLinearEquiv.injective (by rw [hrad', map_zero])

/-- **Self-duality makes the contragredient of `A ≅ V` isomorphic to `V`.** -/
theorem contragredient_equiv_of_selfDual (hSD : W.SelfDual) (A : OrdVModule W M)
    (e : ModuleEquiv W A (adjointModule W)) :
    Nonempty (ModuleEquiv W (contragredientModule A) (adjointModule W)) := by
  obtain ⟨B, hfull, hrad⟩ := hSD
  exact ⟨((ModuleForm.ofEquiv e B hfull hrad).contraEquiv).symm.trans e⟩

/-- **`contra_vacuum_equiv` without pseudo-unitarity**: for a strongly rational `W` and an
irreducible module `A ≅ V`, the contragredient `A′` is again `≅ V`. -/
theorem contra_vacuum_equiv_of_stronglyRational (hSR : StronglyRational W) (A : OrdVModule W M)
    (_hirr : A.IsIrreducible) (e : ModuleEquiv W A (adjointModule W)) :
    Nonempty (ModuleEquiv W (contragredientModule A) (adjointModule W)) :=
  contragredient_equiv_of_selfDual hSR.toStronglyFinite.selfDual A e

end VOA

section AxiomAudit
#print axioms VOA.ModuleForm.contraEquiv
#print axioms VOA.contragredient_equiv_of_selfDual
#print axioms VOA.contra_vacuum_equiv_of_stronglyRational
end AxiomAudit
