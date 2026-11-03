/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Core.Automorphism
import VOA.Core.LieAlgebraV1
import VOA.Core.DeformationLiftedModes
import VOA.Core.RigidityBridge

/-!
# Automorphisms act on the Griess algebra  (Gannon §5.2.1; FLM)

For a VOA `W` with `𝟙 ≠ 0`, the weight-2 space carries the Griess product `u × v = u₍₁₎v`
(`VertexOperatorAlgebra.griessMul`) and the **intrinsic Griess form**

  `u₍₃₎v = ⟨u, v⟩₃ · 𝟙`        (`griessForm`; `u₍₃₎v ∈ W₀ = ℂ𝟙`).

The form is read off from the vertex operators alone, so every VOA automorphism preserves it
with no appeal to the uniqueness of invariant forms.

## Main results
* `aut_map_mem_grading`, `aut_map_grading` — automorphisms preserve every weight space
  (they commute with `L₀`, `VertexOperatorAlgebra.aut_comm_L`, and weight spaces are `L₀`
  eigenspaces, `Deform.grading_eq_L_zero_eigenspace`).
* `autRestrict α n : W.grading n ≃ₗ[ℂ] W.grading n`.
* `griessForm`, `griessForm_aut` — the intrinsic Griess form and its invariance.
* `griessAut hvac` — the group of linear automorphisms of `W₂` preserving `×` and `⟨·,·⟩₃`.
* `griessRestrict hvac : Aut W →* griessAut hvac` — restriction to the Griess algebra.
-/

namespace VOA

open Module (End)

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

namespace GriessAut

/-! ## Automorphisms preserve the grading -/

theorem aut_map_mem_grading (α : Aut W) {n : ℤ} {v : 𝒱} (hv : v ∈ W.grading n) :
    α v ∈ W.grading n := by
  rw [Deform.grading_eq_L_zero_eigenspace (W := W), Module.End.mem_eigenspace_iff] at hv ⊢
  rw [← VertexOperatorAlgebra.aut_comm_L α 0 v, hv]
  exact α.toLinearEquiv.map_smul _ _

theorem aut_map_grading (α : Aut W) (n : ℤ) :
    (W.grading n).map α.toLinearEquiv.toLinearMap = W.grading n := by
  apply le_antisymm
  · rintro _ ⟨v, hv, rfl⟩
    exact aut_map_mem_grading α hv
  · intro v hv
    exact ⟨α.toLinearEquiv.symm v, aut_map_mem_grading α⁻¹ hv,
      α.toLinearEquiv.apply_symm_apply v⟩

/-- The restriction of an automorphism to the weight-`n` space. -/
noncomputable def autRestrict (α : Aut W) (n : ℤ) : W.grading n ≃ₗ[ℂ] W.grading n :=
  α.toLinearEquiv.ofSubmodules _ _ (aut_map_grading α n)

@[simp] theorem autRestrict_coe (α : Aut W) (n : ℤ) (v : W.grading n) :
    ((autRestrict α n v : W.grading n) : 𝒱) = α v := rfl

/-! ## The intrinsic Griess form -/

/-- `u₍₃₎v` for `u, v ∈ W₂`, as an element of `W₀`. -/
def griessThree (u v : W.grading 2) : W.grading 0 :=
  ⟨W.smul (u : 𝒱) 3 (v : 𝒱), by
    have h := W.smul_mem_grading u.2 v.2 3
    rwa [show (2 : ℤ) + 2 - 3 - 1 = 0 by ring] at h⟩

@[simp] theorem griessThree_coe (u v : W.grading 2) :
    ((griessThree u v : W.grading 0) : 𝒱) = W.smul (u : 𝒱) 3 (v : 𝒱) := rfl

/-- The **intrinsic Griess form** `⟨u, v⟩₃`, defined by `u₍₃₎v = ⟨u, v⟩₃ · 𝟙`. -/
noncomputable def griessForm (hvac : W.vacuum ≠ 0) (u v : W.grading 2) : ℂ :=
  RigidBridge.vacCoeff W hvac (griessThree u v)

theorem griessForm_spec (hvac : W.vacuum ≠ 0) (u v : W.grading 2) :
    W.smul (u : 𝒱) 3 (v : 𝒱) = griessForm hvac u v • W.vacuum :=
  ((RigidBridge.vacCoeff_eq_iff hvac (griessThree u v) _).1 rfl)

/-- Automorphisms preserve the intrinsic Griess form. -/
theorem griessForm_aut (hvac : W.vacuum ≠ 0) (α : Aut W) (u v : W.grading 2) :
    griessForm hvac (autRestrict α 2 u) (autRestrict α 2 v) = griessForm hvac u v := by
  rw [griessForm, RigidBridge.vacCoeff_eq_iff, griessThree_coe, autRestrict_coe, autRestrict_coe,
    ← Aut.map_smul, griessForm_spec hvac u v, α.toLinearEquiv.map_smul,
    Aut.coe_toLinearEquiv, α.map_vacuum]

/-- Automorphisms preserve the Griess product. -/
theorem griessMul_aut (α : Aut W) (u v : W.grading 2) :
    autRestrict α 2 (W.griessMul u v) = W.griessMul (autRestrict α 2 u) (autRestrict α 2 v) := by
  apply Subtype.ext
  rw [autRestrict_coe, VertexOperatorAlgebra.griessMul_coe, VertexOperatorAlgebra.griessMul_coe,
    autRestrict_coe, autRestrict_coe, Aut.map_smul]

/-! ## The automorphism group of the Griess algebra -/

/-- Linear automorphisms of `W₂` preserving the Griess product and the intrinsic form. -/
noncomputable def griessAut (hvac : W.vacuum ≠ 0) : Subgroup (W.grading 2 ≃ₗ[ℂ] W.grading 2) where
  carrier := {g | (∀ u v, g (W.griessMul u v) = W.griessMul (g u) (g v)) ∧
    ∀ u v, griessForm hvac (g u) (g v) = griessForm hvac u v}
  mul_mem' {f g} hf hg := ⟨fun u v => by
      change f (g _) = W.griessMul (f (g u)) (f (g v))
      rw [hg.1, hf.1],
    fun u v => by
      change griessForm hvac (f (g u)) (f (g v)) = _
      rw [hf.2, hg.2]⟩
  one_mem' := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  inv_mem' {f} hf := ⟨fun u v => by
      have h1 := hf.1 (f.symm u) (f.symm v)
      rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h1
      show f.symm (W.griessMul u v) = W.griessMul (f.symm u) (f.symm v)
      rw [← h1, LinearEquiv.symm_apply_apply],
    fun u v => by
      show griessForm hvac (f.symm u) (f.symm v) = _
      rw [← hf.2, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]⟩

/-- **Restriction to the Griess algebra**: every VOA automorphism acts on `(W₂, ×, ⟨·,·⟩₃)`. -/
noncomputable def griessRestrict (hvac : W.vacuum ≠ 0) : Aut W →* griessAut hvac where
  toFun α := ⟨autRestrict α 2, fun u v => griessMul_aut α u v, fun u v => griessForm_aut hvac α u v⟩
  map_one' := by
    apply Subtype.ext
    exact LinearEquiv.ext fun _ => rfl
  map_mul' α β := by
    apply Subtype.ext
    exact LinearEquiv.ext fun _ => rfl

@[simp] theorem griessRestrict_apply_coe (hvac : W.vacuum ≠ 0) (α : Aut W) (v : W.grading 2) :
    (((griessRestrict hvac α : griessAut hvac) : W.grading 2 ≃ₗ[ℂ] W.grading 2) v : 𝒱) = α v :=
  rfl

/-! ## Faithfulness from generation by the weight-2 space -/

/-- `W` is **generated by `W₂`**: every subspace containing `W₂` and closed under all
`n`-th products is the whole space. -/
def GeneratedByWeightTwo (W : VertexOperatorAlgebra 𝒱) : Prop :=
  ∀ S : Submodule ℂ 𝒱, W.grading 2 ≤ S → (∀ u ∈ S, ∀ v ∈ S, ∀ n : ℤ, W.smul u n v ∈ S) → S = ⊤

/-- The fixed space `{v | α v = v}` of an automorphism. -/
def fixedSpace (α : Aut W) : Submodule ℂ 𝒱 :=
  LinearMap.ker (α.toLinearEquiv.toLinearMap - LinearMap.id)

theorem mem_fixedSpace {α : Aut W} {v : 𝒱} : v ∈ fixedSpace α ↔ α v = v := by
  rw [fixedSpace, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
  rfl

/-- The fixed space of an automorphism is closed under every product. -/
theorem smul_mem_fixedSpace (α : Aut W) {u v : 𝒱} (hu : u ∈ fixedSpace α)
    (hv : v ∈ fixedSpace α) (n : ℤ) : W.smul u n v ∈ fixedSpace α := by
  rw [mem_fixedSpace] at hu hv ⊢
  rw [Aut.map_smul, hu, hv]

/-- An automorphism fixing `W₂` pointwise is the identity, when `W` is generated by `W₂`. -/
theorem eq_one_of_fix_weightTwo (hgen : GeneratedByWeightTwo W) (α : Aut W)
    (hα : ∀ v ∈ W.grading 2, α v = v) : α = 1 := by
  have htop := hgen (fixedSpace α) (fun v hv => mem_fixedSpace.2 (hα v hv))
    (fun u hu v hv n => smul_mem_fixedSpace α hu hv n)
  refine Aut.ext (LinearEquiv.ext fun v => ?_)
  have hv : v ∈ fixedSpace α := htop ▸ Submodule.mem_top
  exact mem_fixedSpace.1 hv

/-- **Faithfulness**: if `W` is generated by `W₂`, restriction to the Griess algebra is
injective, so `Aut W` embeds in the automorphism group of the Griess algebra. -/
theorem griessRestrict_injective (hvac : W.vacuum ≠ 0) (hgen : GeneratedByWeightTwo W) :
    Function.Injective (griessRestrict hvac) := by
  rw [injective_iff_map_eq_one]
  intro α hα
  refine eq_one_of_fix_weightTwo hgen α fun v hv => ?_
  have h := congrArg (fun g : griessAut hvac =>
    (((g : W.grading 2 ≃ₗ[ℂ] W.grading 2) ⟨v, hv⟩ : W.grading 2) : 𝒱)) hα
  simpa using h

end GriessAut

end VOA
