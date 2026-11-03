/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modules.LogTensorPzAction

/-!
# The maximal compatible weak module in the actual tensor dual

We take the sum of all stable lower-truncated `P(1)`-compatible subspaces of
`(W₁ ⊗ W₂)*`. Since each vector in this sum lies in a finite sum of such spaces,
compatibility and lower truncation survive. The resulting object has a genuine weak
VOA module structure. Grading restriction and finite length are subsequent tasks;
they are not silently included in this construction.
-/

namespace VOA.LogTensor.Pz
open scoped BigOperators
open VOA.Huang.PzTensorRho
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable {M₁ M₂ : Type u} [AddCommGroup M₁] [Module ℂ M₁]
  [AddCommGroup M₂] [Module ℂ M₂]
variable (A₁ : WeakModule W M₁) (A₂ : WeakModule W M₂)

private theorem trunc_zero (a : V) : TruncAt A₁ A₂ a (0 : BilinearDual) :=
  ⟨0, fun _ _ => map_zero _⟩

private theorem trunc_add {a : V} {b c : BilinearDual (M₁ := M₁) (M₂ := M₂)}
    (hb : TruncAt A₁ A₂ a b) (hc : TruncAt A₁ A₂ a c) : TruncAt A₁ A₂ a (b+c) := by
  obtain ⟨B,hB⟩ := hb
  obtain ⟨C,hC⟩ := hc
  exact ⟨min B C, fun p hp => by
    rw [map_add, hB p (le_trans hp (min_le_left _ _)),
      hC p (le_trans hp (min_le_right _ _)), add_zero]⟩

private theorem trunc_smul {a : V} {b : BilinearDual (M₁ := M₁) (M₂ := M₂)}
    (hb : TruncAt A₁ A₂ a b) (s : ℂ) : TruncAt A₁ A₂ a (s • b) := by
  obtain ⟨B,hB⟩ := hb
  exact ⟨B, fun p hp => by rw [map_smul, hB p hp, smul_zero]⟩

private theorem defect_zero (a : V) (m L : ℤ) (x : M₁) (y : M₂) :
    Dsl A₁ A₂ a m L (0 : BilinearDual) x y = 0 := by
  simp [Dsl, Out, InL, InR]

private theorem defect_add {a : V} {b c : BilinearDual (M₁ := M₁) (M₂ := M₂)}
    (hb : TruncAt A₁ A₂ a b) (hc : TruncAt A₁ A₂ a c)
    (m L : ℤ) (x : M₁) (y : M₂) :
    Dsl A₁ A₂ a m L (b+c) x y = Dsl A₁ A₂ a m L b x y + Dsl A₁ A₂ a m L c x y := by
  simp only [Dsl, Out, InL, InR, map_add, LinearMap.add_apply, mul_add]
  rw [finsum_add_distrib (Out_fin A₁ A₂ hb m L x y) (Out_fin A₁ A₂ hc m L x y),
    finsum_add_distrib (InL_fin A₁ a m L b x y) (InL_fin A₁ a m L c x y),
    finsum_add_distrib (InR_fin A₂ a m L b x y) (InR_fin A₂ a m L c x y)]
  ring

private theorem defect_smul {a : V} {b : BilinearDual (M₁ := M₁) (M₂ := M₂)}
    (s : ℂ) (m L : ℤ) (x : M₁) (y : M₂) :
    Dsl A₁ A₂ a m L (s • b) x y = s * Dsl A₁ A₂ a m L b x y := by
  simp only [Dsl, Out, InL, InR, map_smul, LinearMap.smul_apply, smul_eq_mul]
  simp_rw [mul_left_comm _ s, mul_assoc]
  rw [← mul_finsum, ← mul_finsum, ← mul_finsum]
  ring

/-- The pointwise compatibility and truncation conditions form an actual linear subspace. -/
noncomputable def regularForms : Submodule ℂ (BilinearDual (M₁ := M₁) (M₂ := M₂)) where
  carrier := {b | ∀ (d : ℤ) (a : V), a ∈ W.grading d →
    TruncAt A₁ A₂ a b ∧ CompatAt A₁ A₂ a b}
  zero_mem' d a ha := ⟨trunc_zero A₁ A₂ a, fun L x y => defect_zero A₁ A₂ a 0 L x y⟩
  add_mem' hb hc d a ha := ⟨trunc_add A₁ A₂ (hb d a ha).1 (hc d a ha).1, fun L x y => by
    rw [defect_add A₁ A₂ (hb d a ha).1 (hc d a ha).1,
      (hb d a ha).2 L x y, (hc d a ha).2 L x y, add_zero]⟩
  smul_mem' s b hb d a ha := ⟨trunc_smul A₁ A₂ (hb d a ha).1 s, fun L x y => by
    rw [defect_smul, (hb d a ha).2 L x y, mul_zero]⟩

/-- The sum of every compatible stable subspace of the actual tensor dual. -/
noncomputable def maximalCarrier : Submodule ℂ (BilinearDual (M₁ := M₁) (M₂ := M₂)) :=
  ⨆ S : CompatibleSpace A₁ A₂, S.carrier

theorem compatibleSpace_le_maximal (S : CompatibleSpace A₁ A₂) :
    S.carrier ≤ maximalCarrier A₁ A₂ := le_iSup_of_le S le_rfl

theorem maximalCarrier_le_regular : maximalCarrier A₁ A₂ ≤ regularForms A₁ A₂ := by
  refine iSup_le fun S => ?_
  intro b hb d a ha
  exact ⟨S.truncated b hb d a ha, S.compatible b hb d a ha⟩

/-- The maximal compatible space is stable under the actual twisted coproduct. -/
theorem maximalCarrier_stable (d : ℤ) (a : V) (ha : a ∈ W.grading d) (n : ℤ)
    (b : BilinearDual (M₁ := M₁) (M₂ := M₂)) (hb : b ∈ maximalCarrier A₁ A₂) :
    tauHat A₁ A₂ d a n b ∈ maximalCarrier A₁ A₂ := by
  change b ∈ ⨆ S : CompatibleSpace A₁ A₂, S.carrier at hb
  refine Submodule.iSup_induction (fun S : CompatibleSpace A₁ A₂ => S.carrier)
    (motive := fun b => tauHat A₁ A₂ d a n b ∈ maximalCarrier A₁ A₂) hb ?_ ?_ ?_
  · intro S b hb
    exact compatibleSpace_le_maximal A₁ A₂ S (S.stable d a ha n b hb)
  · dsimp only
    rw [← tauEnd_apply, map_zero]
    exact Submodule.zero_mem _
  · intro b c hb hc
    rw [← tauEnd_apply, map_add, tauEnd_apply, tauEnd_apply]
    exact Submodule.add_mem _ hb hc

/-- The canonical maximal compatible space. Its conditions are proved from its
construction; no existence, compatibility, or rationality input is assumed. -/
noncomputable def maximalCompatibleSpace : CompatibleSpace A₁ A₂ where
  carrier := maximalCarrier A₁ A₂
  stable := maximalCarrier_stable A₁ A₂
  truncated b hb d a ha := (maximalCarrier_le_regular A₁ A₂ hb d a ha).1
  compatible b hb d a ha := (maximalCarrier_le_regular A₁ A₂ hb d a ha).2

/-- The resulting genuine weak VOA module in the algebraic tensor dual. -/
noncomputable def maximalWeakModule : WeakModule W (maximalCarrier A₁ A₂) :=
  (maximalCompatibleSpace A₁ A₂).weakModule

end VOA.LogTensor.Pz
