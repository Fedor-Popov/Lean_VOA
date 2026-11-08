/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.MoonshineCNStringCritical
import VOA.Moonshine.MoonshineCNStringLongitudinal
import VOA.Moonshine.MoonshineCNStringOrthogonals

/-! # Critical physical-state splitting and the exact radicals

The physical weight-one splitting uses precisely the light-cone splitting and central charge 26.
The identification of the radical with the physical spurious intersection
already follows from weightwise orthogonals, at every central charge.
-/

namespace VOA.Moonshine.ConwayNorton.StringModule

universe u
variable {H : Type u} [AddCommGroup H] [Module ℂ H] (M : StringModule H)

/-- The radical of the restricted form, represented as a subspace of `wt N`. -/
def formRadicalIn (U : Submodule ℂ H) (N : ℤ) : Submodule ℂ (M.wt N) :=
  M.weightSlice U N ⊓ (M.stringWeightForm N).orthogonal (M.weightSlice U N)

theorem mem_formRadicalIn_iff (U : Submodule ℂ H) (N : ℤ) (x : M.wt N) :
    x ∈ M.formRadicalIn U N ↔ (x : H) ∈ U ∧
      ∀ y : M.wt N, (y : H) ∈ U → M.B x y = 0 := by
  change ((x : H) ∈ U ∧ ∀ y : M.wt N, (y : H) ∈ U → M.B y x = 0) ↔ _
  simp only [M.B_symm.eq]

/-- The physical radical is exactly the physical spurious intersection,
without a critical-charge or light-cone assumption. -/
theorem physicalOne_radical_eq :
    M.formRadicalIn M.physical 1 = M.weightSlice (M.physical ⊓ M.spurious) 1 := by
  rw [formRadicalIn, M.orthogonal_physical_eq]
  rfl

/-- At every weight, the longitudinal radical is the intersection with `S_K`. -/
theorem kVacuum_radical_eq (N : ℤ) :
    M.formRadicalIn M.kVacuum N = M.weightSlice (M.kVacuum ⊓ M.kSpurious) N := by
  rw [formRadicalIn, M.orthogonal_kVacuum_eq]
  rfl

theorem spurious_one_tilde_decomposition (x : H) (hx : x ∈ M.spurious)
    (hw : x ∈ M.wt 1) :
    ∃ a ∈ M.wt 0, ∃ b ∈ M.wt (-1), M.L (-1) a + M.tildeNegativeTwo b = x := by
  obtain ⟨a, ha, b, hb, he⟩ := M.spurious_weight_two 1 x hx hw
  norm_num at ha hb
  have hwb : M.L (-1) b ∈ M.wt 0 := by simpa using M.L_wt (-1) (-1) b hb
  refine ⟨a - (3 / 2 : ℂ) • M.L (-1) b,
    (M.wt 0).sub_mem ha ((M.wt 0).smul_mem _ hwb), b, hb, ?_⟩
  rw [← he]
  simp only [tildeNegativeTwo, LinearMap.add_apply, LinearMap.smul_apply,
    Module.End.mul_apply, map_sub, map_smul]
  module

/-- `L 1` preserves spurious vectors of weight one, at every central charge. -/
theorem criticalSpurious_L_one (x : H) (hx : x ∈ M.spurious) (hw : x ∈ M.wt 1) :
    M.L 1 x ∈ M.spurious := by
  obtain ⟨a, ha, b, hb, he⟩ := M.spurious_one_tilde_decomposition x hx hw
  rw [← he, map_add, M.L_one_negative_one_weight_zero a ha,
    M.L_one_tildeNegativeTwo_weight_neg_one b hb]
  exact M.spurious.add_mem (M.negative_L_mem_spurious 0 _) (M.tildeNegativeTwo_mem_spurious _)

/-- At central charge 26, the modified positive mode preserves spurious
vectors of weight one. -/
theorem criticalSpurious_L_two_tilde (hc : M.c = 26) (x : H)
    (hx : x ∈ M.spurious) (hw : x ∈ M.wt 1) : M.tildePositiveTwo x ∈ M.spurious := by
  obtain ⟨a, ha, b, hb, he⟩ := M.spurious_one_tilde_decomposition x hx hw
  rw [← he, map_add, M.tildePositiveTwo_negative_one_weight_zero a ha,
    M.tildeTwo_critical_commute hc b hb]
  exact M.spurious.add_mem (M.negative_L_mem_spurious 0 _) (M.tildeNegativeTwo_mem_spurious _)

/-- The spanning part of the weight-one physical splitting `P¹ = T¹ ⊕ N¹`: every physical
weight-one state is transverse plus physical spurious. -/
theorem physicalOne_eq_transverse_sup_null (hc : M.c = 26) (hF : M.LightConeSplit) :
    M.weightSlice M.physical 1 = M.weightSlice M.transverse 1 ⊔
      M.weightSlice (M.physical ⊓ M.spurious) 1 := by
  apply le_antisymm
  · intro x hx
    obtain ⟨s, hs, k, hk, hsw, hkw, he⟩ := M.lightConeSplit_decompose_weight hF 1 x x.property
    have vanish (A : Module.End ℂ H) (hAs : A s ∈ M.spurious)
        (hAk : A k ∈ M.kVacuum) (hAx : A x = 0) : A k = 0 := by
      have h := congrArg A he
      rw [map_add, hAx] at h
      have heq : A k = -(A s) := by linear_combination (norm := module) h
      exact Submodule.disjoint_def.mp hF.disjoint (A k)
        (heq ▸ M.spurious.neg_mem hAs) hAk
    have hp := (M.mem_physical_iff x).mp hx
    have hp₁ : M.L 1 x = 0 := hp 0
    have hp₂ : M.L 2 x = 0 := hp 1
    have h₁ : M.L 1 k = 0 := vanish (M.L 1)
      (M.criticalSpurious_L_one s hs hsw) (M.kVacuum_L_stable 0 k hk) (hp 0)
    have ht : M.tildePositiveTwo k = 0 := vanish M.tildePositiveTwo
      (M.criticalSpurious_L_two_tilde hc s hs hsw) (M.tildePositiveTwo_kVacuum k hk)
      (by simp [tildePositiveTwo, Module.End.mul_apply, hp₁, hp₂])
    have h₂ : M.L 2 k = 0 := by
      simpa [tildePositiveTwo, Module.End.mul_apply, h₁] using ht
    have hkp := M.physical_of_L_one_two k h₁ h₂
    have hsp : s ∈ M.physical := by
      have h := M.physical.sub_mem hx hkp
      change (x : H) - k ∈ M.physical at h
      rw [← he, add_sub_cancel_right] at h
      exact h
    exact Submodule.mem_sup.mpr
      ⟨⟨k, hkw⟩, ⟨hkp, hk⟩, ⟨s, hsw⟩, ⟨hsp, hs⟩,
        Subtype.ext (by change k + s = (x : H); rw [add_comm]; exact he)⟩
  · exact sup_le (fun _ h => h.1) (fun _ h => h.1)

/-- The sum `T¹ + N¹` is direct, already from the light-cone splitting. -/
theorem physicalOne_transverse_null_disjoint (hF : M.LightConeSplit) :
    Disjoint (M.weightSlice M.transverse 1) (M.weightSlice (M.physical ⊓ M.spurious) 1) := by
  rw [Submodule.disjoint_def]
  intro x hx hn
  apply Subtype.ext
  exact Submodule.disjoint_def.mp hF.disjoint x hn.2 hx.2

end VOA.Moonshine.ConwayNorton.StringModule
