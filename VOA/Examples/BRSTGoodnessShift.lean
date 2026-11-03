/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.ConcreteGoodZeroModes

/-!
# Generic shift bookkeeping for graded operators

Everything here is generic and proved outright.

* `shiftTarget d P k = ⨆_{δ, P δ} d (k + δ)` and `ShiftsInto d T P` (`T` maps `d k` into
  `shiftTarget d P k`); closure under composition (`ShiftsInto.apply_target`), and under tensor
  products of operators (`tensorDeg_map_shiftTarget`).
* For an internal family: membership in a sub-supremum is detected by projections
  (`mem_iSup_pred_iff`), and sub-suprema intersect as their index sets do
  (`mem_iSup_pred_inf`).
* Coarsening a tensor grading along an additive map (`tensorDeg_le_coarsen`).
-/

namespace VOA.ConcreteHodge

open scoped TensorProduct

noncomputable section

universe u v w

section Shift

variable {κ : Type w} [AddCommGroup κ] {E : Type u} [AddCommGroup E] [Module ℂ E]

/-- The pieces reachable from `k` along shifts satisfying `P`. -/
def shiftTarget (d : κ → Submodule ℂ E) (P : κ → Prop) (k : κ) : Submodule ℂ E :=
  ⨆ (δ : κ) (_ : P δ), d (k + δ)

theorem mem_shiftTarget {d : κ → Submodule ℂ E} {P : κ → Prop} {k δ : κ} {x : E} (hP : P δ)
    (hx : x ∈ d (k + δ)) : x ∈ shiftTarget d P k :=
  Submodule.mem_iSup_of_mem δ (Submodule.mem_iSup_of_mem hP hx)

theorem shiftTarget_mono {d : κ → Submodule ℂ E} {P P' : κ → Prop} (h : ∀ δ, P δ → P' δ)
    (k : κ) : shiftTarget d P k ≤ shiftTarget d P' k :=
  iSup_le fun δ => iSup_le fun hδ => (le_iSup_of_le δ (le_iSup_of_le (h δ hδ) le_rfl))

/-- The sum of two shift predicates. -/
def addPred (P Q : κ → Prop) (δ : κ) : Prop := ∃ a b, P a ∧ Q b ∧ δ = a + b

theorem shiftTarget_shift_le {d : κ → Submodule ℂ E} {P Q : κ → Prop} {k a : κ} (ha : P a) :
    shiftTarget d Q (k + a) ≤ shiftTarget d (addPred P Q) k := by
  refine iSup_le fun b => iSup_le fun hb => ?_
  intro x hx
  exact mem_shiftTarget ⟨a, b, ha, hb, rfl⟩ (by rwa [← add_assoc])

/-- `T` maps every piece `d k` into `shiftTarget d P k`. -/
def ShiftsInto (d : κ → Submodule ℂ E) (T : E →ₗ[ℂ] E) (P : κ → Prop) : Prop :=
  ∀ k, ∀ x ∈ d k, T x ∈ shiftTarget d P k

theorem ShiftsInto.of_exact {d : κ → Submodule ℂ E} {T : E →ₗ[ℂ] E} {δ₀ : κ}
    (h : ∀ k, ∀ x ∈ d k, T x ∈ d (k + δ₀)) : ShiftsInto d T (· = δ₀) :=
  fun k x hx => mem_shiftTarget rfl (h k x hx)

theorem ShiftsInto.mono {d : κ → Submodule ℂ E} {T : E →ₗ[ℂ] E} {P P' : κ → Prop}
    (hT : ShiftsInto d T P) (h : ∀ δ, P δ → P' δ) : ShiftsInto d T P' :=
  fun k x hx => shiftTarget_mono h k (hT k x hx)

/-- Applying a shifting operator to an element of a target. -/
theorem ShiftsInto.apply_target {d : κ → Submodule ℂ E} {T : E →ₗ[ℂ] E} {P Q : κ → Prop}
    (hT : ShiftsInto d T Q) {k : κ} {x : E} (hx : x ∈ shiftTarget d P k) :
    T x ∈ shiftTarget d (addPred P Q) k := by
  refine Submodule.iSup_induction _ (motive := fun x => T x ∈ shiftTarget d (addPred P Q) k)
    hx ?_ (by simp) (fun x y hx hy => by
      beta_reduce at hx hy ⊢; rw [map_add]; exact Submodule.add_mem _ hx hy)
  intro a x hx
  refine Submodule.iSup_induction _ (motive := fun x => T x ∈ shiftTarget d (addPred P Q) k)
    hx ?_ (by simp) (fun x y hx hy => by
      beta_reduce at hx hy ⊢; rw [map_add]; exact Submodule.add_mem _ hx hy)
  intro ha x hx
  exact shiftTarget_shift_le ha (hT _ x hx)

theorem ShiftsInto.comp {d : κ → Submodule ℂ E} {T S : E →ₗ[ℂ] E} {P Q : κ → Prop}
    (hT : ShiftsInto d T P) (hS : ShiftsInto d S Q) : ShiftsInto d (S ∘ₗ T) (addPred P Q) :=
  fun k x hx => hS.apply_target (hT k x hx)

theorem ShiftsInto.add {d : κ → Submodule ℂ E} {T S : E →ₗ[ℂ] E} {P : κ → Prop}
    (hT : ShiftsInto d T P) (hS : ShiftsInto d S P) : ShiftsInto d (T + S) P :=
  fun k x hx => by rw [LinearMap.add_apply]; exact Submodule.add_mem _ (hT k x hx) (hS k x hx)

theorem ShiftsInto.smul {d : κ → Submodule ℂ E} {T : E →ₗ[ℂ] E} {P : κ → Prop}
    (hT : ShiftsInto d T P) (c : ℂ) : ShiftsInto d (c • T) P :=
  fun k x hx => by rw [LinearMap.smul_apply]; exact Submodule.smul_mem _ c (hT k x hx)

theorem ShiftsInto.zero (d : κ → Submodule ℂ E) (P : κ → Prop) : ShiftsInto d 0 P :=
  fun k x _ => by rw [LinearMap.zero_apply]; exact Submodule.zero_mem _

theorem ShiftsInto.sum {d : κ → Submodule ℂ E} {α : Type*} (s : Finset α)
    {T : α → E →ₗ[ℂ] E} {P : κ → Prop} (hT : ∀ a ∈ s, ShiftsInto d (T a) P) :
    ShiftsInto d (∑ a ∈ s, T a) P := by
  classical
  intro k x hx
  rw [LinearMap.sum_apply]
  exact Submodule.sum_mem _ fun a ha => hT a ha k x hx

end Shift

/-! ### Tensor products of shifting operators -/

section TensorShift

variable {ι : Type w} [AddCommGroup ι]
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : Type v} [AddCommGroup W] [Module ℂ W]

theorem tmul_mem_tensor_shiftTarget (dV : ι → Submodule ℂ V) (dW : ι → Submodule ℂ W)
    {P Q : ι → Prop} {b c : ι} {x : V} {y : W} (hx : x ∈ shiftTarget dV P b)
    (hy : y ∈ shiftTarget dW Q c) :
    x ⊗ₜ[ℂ] y ∈ shiftTarget (tensorDeg dV dW) (addPred P Q) (b + c) := by
  refine Submodule.iSup_induction _
    (motive := fun x => x ⊗ₜ[ℂ] y ∈ shiftTarget (tensorDeg dV dW) (addPred P Q) (b + c))
    hx ?_ (by simp) (fun x x' hx hx' => by
      beta_reduce at hx hx' ⊢; rw [TensorProduct.add_tmul]; exact Submodule.add_mem _ hx hx')
  intro δ₁ x hx
  refine Submodule.iSup_induction _
    (motive := fun x => x ⊗ₜ[ℂ] y ∈ shiftTarget (tensorDeg dV dW) (addPred P Q) (b + c))
    hx ?_ (by simp) (fun x x' hx hx' => by
      beta_reduce at hx hx' ⊢; rw [TensorProduct.add_tmul]; exact Submodule.add_mem _ hx hx')
  intro h₁ x hx
  refine Submodule.iSup_induction _
    (motive := fun y => x ⊗ₜ[ℂ] y ∈ shiftTarget (tensorDeg dV dW) (addPred P Q) (b + c))
    hy ?_ (by simp) (fun y y' hy hy' => by
      beta_reduce at hy hy' ⊢; rw [TensorProduct.tmul_add]; exact Submodule.add_mem _ hy hy')
  intro δ₂ y hy
  refine Submodule.iSup_induction _
    (motive := fun y => x ⊗ₜ[ℂ] y ∈ shiftTarget (tensorDeg dV dW) (addPred P Q) (b + c))
    hy ?_ (by simp) (fun y y' hy hy' => by
      beta_reduce at hy hy' ⊢; rw [TensorProduct.tmul_add]; exact Submodule.add_mem _ hy hy')
  intro h₂ y hy
  refine mem_shiftTarget ⟨δ₁, δ₂, h₁, h₂, rfl⟩ ?_
  have e : b + c + (δ₁ + δ₂) = (b + δ₁) + (c + δ₂) := by abel
  rw [e]
  exact tmul_mem_tensorDeg dV dW hx hy

/-- **Tensor products of shifting operators shift the tensor grading by the sum.** -/
theorem tensorDeg_map_shiftTarget (dV : ι → Submodule ℂ V) (dW : ι → Submodule ℂ W)
    {T : V →ₗ[ℂ] V} {S : W →ₗ[ℂ] W} {P Q : ι → Prop} (hT : ShiftsInto dV T P)
    (hS : ShiftsInto dW S Q) :
    ShiftsInto (tensorDeg dV dW) (TensorProduct.map T S) (addPred P Q) := by
  intro a z hz
  refine tensorDeg_induction dV dW a
    (fun z => TensorProduct.map T S z ∈ shiftTarget (tensorDeg dV dW) (addPred P Q) a)
    (by simp) (fun x y hx hy => by simpa only [map_add] using Submodule.add_mem _ hx hy)
    (fun c x hx => by simpa only [map_smul] using Submodule.smul_mem _ c hx) ?_ z hz
  intro b x hx y hy
  rw [TensorProduct.map_tmul]
  have h := tmul_mem_tensor_shiftTarget dV dW (hT b x hx) (hS _ y hy)
  rwa [add_sub_cancel] at h

theorem shiftsInto_id (d : ι → Submodule ℂ V) : ShiftsInto d LinearMap.id (· = 0) :=
  ShiftsInto.of_exact fun k x hx => by rw [add_zero]; exact hx

/-- Coarsening a tensor grading: if the factor pieces sit in suprema of fine pieces along an
additive map, so do the tensor pieces. -/
theorem tensorDeg_le_coarsen {κ : Type*} [AddCommGroup κ] (π : κ →+ ι)
    (dV : ι → Submodule ℂ V) (dW : ι → Submodule ℂ W) (fV : κ → Submodule ℂ V)
    (fW : κ → Submodule ℂ W) (hV : ∀ i, dV i ≤ ⨆ (k : κ) (_ : π k = i), fV k)
    (hW : ∀ i, dW i ≤ ⨆ (k : κ) (_ : π k = i), fW k) (i : ι) :
    tensorDeg dV dW i ≤ ⨆ (k : κ) (_ : π k = i), tensorDeg fV fW k := by
  intro z hz
  refine tensorDeg_induction dV dW i (fun z => z ∈ ⨆ (k : κ) (_ : π k = i), tensorDeg fV fW k)
    (Submodule.zero_mem _) (fun x y hx hy => Submodule.add_mem _ hx hy)
    (fun c x hx => Submodule.smul_mem _ c hx) ?_ z hz
  intro b x hx y hy
  have hx' := hV b hx
  have hy' := hW (i - b) hy
  refine Submodule.iSup_induction _
    (motive := fun x => x ⊗ₜ[ℂ] y ∈ ⨆ (k : κ) (_ : π k = i), tensorDeg fV fW k)
    hx' ?_ (by simp) (fun x x' hx hx' => by
      beta_reduce at hx hx' ⊢; rw [TensorProduct.add_tmul]; exact Submodule.add_mem _ hx hx')
  intro k₁ x hx
  refine Submodule.iSup_induction _
    (motive := fun x => x ⊗ₜ[ℂ] y ∈ ⨆ (k : κ) (_ : π k = i), tensorDeg fV fW k)
    hx ?_ (by simp) (fun x x' hx hx' => by
      beta_reduce at hx hx' ⊢; rw [TensorProduct.add_tmul]; exact Submodule.add_mem _ hx hx')
  intro e₁ x hx
  refine Submodule.iSup_induction _
    (motive := fun y => x ⊗ₜ[ℂ] y ∈ ⨆ (k : κ) (_ : π k = i), tensorDeg fV fW k)
    hy' ?_ (by simp) (fun y y' hy hy' => by
      beta_reduce at hy hy' ⊢; rw [TensorProduct.tmul_add]; exact Submodule.add_mem _ hy hy')
  intro k₂ y hy
  refine Submodule.iSup_induction _
    (motive := fun y => x ⊗ₜ[ℂ] y ∈ ⨆ (k : κ) (_ : π k = i), tensorDeg fV fW k)
    hy ?_ (by simp) (fun y y' hy hy' => by
      beta_reduce at hy hy' ⊢; rw [TensorProduct.tmul_add]; exact Submodule.add_mem _ hy hy')
  intro e₂ y hy
  refine Submodule.mem_iSup_of_mem (k₁ + k₂) (Submodule.mem_iSup_of_mem ?_
    (tmul_mem_tensorDeg fV fW hx hy))
  rw [map_add, e₁, e₂, add_sub_cancel]

end TensorShift

/-! ### Sub-suprema of an internal family -/

section Internal

variable {κ : Type w} [DecidableEq κ] {E : Type u} [AddCommGroup E] [Module ℂ E]
  {F : κ → Submodule ℂ E}

/-- Membership in a sub-supremum of an internal family is detected by projections. -/
theorem mem_iSup_pred_iff (hI : DirectSum.IsInternal F) (S : κ → Prop) (x : E) :
    x ∈ (⨆ (k : κ) (_ : S k), F k) ↔ ∀ k, ¬ S k → iproj hI k x = 0 := by
  constructor
  · intro hx k hk
    refine Submodule.iSup_induction _ (motive := fun x => iproj hI k x = 0) hx ?_
      (by simp) (fun x y hx hy => by beta_reduce at hx hy ⊢; rw [map_add, hx, hy, add_zero])
    intro j x hx
    refine Submodule.iSup_induction _ (motive := fun x => iproj hI k x = 0) hx ?_
      (by simp) (fun x y hx hy => by beta_reduce at hx hy ⊢; rw [map_add, hx, hy, add_zero])
    intro hj x hx
    exact iproj_of_mem_ne hI (fun h => hk (by subst h; exact hj)) hx
  · intro h
    obtain ⟨s, hs⟩ := sum_iproj hI x
    rw [← hs]
    refine Submodule.sum_mem _ fun k _ => ?_
    by_cases hk : S k
    · exact Submodule.mem_iSup_of_mem k (Submodule.mem_iSup_of_mem hk (iproj_mem hI k x))
    · rw [h k hk]; exact Submodule.zero_mem _

theorem mem_iSup_pred_inf (hI : DirectSum.IsInternal F) {S T : κ → Prop} {x : E}
    (hS : x ∈ ⨆ (k : κ) (_ : S k), F k) (hT : x ∈ ⨆ (k : κ) (_ : T k), F k) :
    x ∈ ⨆ (k : κ) (_ : S k ∧ T k), F k := by
  rw [mem_iSup_pred_iff hI] at hS hT ⊢
  intro k hk
  by_cases h : S k
  · exact hT k fun h' => hk ⟨h, h'⟩
  · exact hS k h

theorem iSup_pred_mono {S T : κ → Prop} (h : ∀ k, S k → T k) :
    (⨆ (k : κ) (_ : S k), F k) ≤ ⨆ (k : κ) (_ : T k), F k :=
  iSup_le fun k => iSup_le fun hk => le_iSup_of_le k (le_iSup_of_le (h k hk) le_rfl)

end Internal

end

end VOA.ConcreteHodge
