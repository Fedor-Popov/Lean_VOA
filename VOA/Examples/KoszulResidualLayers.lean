/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.ConcreteGoodGrading

/-!
# Components of operators along an internal grading, and the layer grading of a GU VOA

Generic tools for the native Koszul argument.

* `compOp hI T σ` — **the `σ`-component of an operator** `T` along an internal grading
  `L : ι → Submodule`: on `L i` it is `iproj (σ i) ∘ T`. (`compOp_of_mem`, `compOp_mem`.)
* `layerDeg_isInternal` — the interpreted layer grading of a graded-unitary VOA is an internal
  direct sum (orthogonality + positivity of the carrier form).
* `piece_le_iSup_layerDeg` — the `t`-th flag piece at weight `m` lies in the sum of the layers
  `s ≤ t` at weight `m`; `sub_iproj_layer_mem` — a vector of the `t`-th piece differs from its
  `t`-th layer component by a vector of the layers `s < t`.

Everything is proved outright.
-/

namespace VOA.KoszulResidual

open VOA.ConcreteHodge VOA.GradedUnitaryCohomology VOA.VertexOperatorAlgebra
open VOA.LeeYangCosetTransfer
open scoped DirectSum

noncomputable section

universe u v

/-! ### Components of an operator -/

section Comp

variable {ι : Type v} [DecidableEq ι] {E : Type u} [AddCommGroup E] [Module ℂ E]
  {L : ι → Submodule ℂ E}

/-- **The `σ`-component of `T`**: on the summand `L i` it is `iproj (σ i) ∘ T`. -/
def compOp (hI : DirectSum.IsInternal L) (T : E →ₗ[ℂ] E) (σ : ι → ι) : E →ₗ[ℂ] E :=
  DirectSum.toModule ℂ ι E (fun i => iproj hI (σ i) ∘ₗ T ∘ₗ (L i).subtype) ∘ₗ
    (internalEquiv hI).symm.toLinearMap

theorem compOp_of_mem (hI : DirectSum.IsInternal L) (T : E →ₗ[ℂ] E) (σ : ι → ι) {i : ι}
    {x : E} (hx : x ∈ L i) : compOp hI T σ x = iproj hI (σ i) (T x) := by
  simp only [compOp, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
  rw [internalEquiv_symm_of_mem hI hx, ← DirectSum.lof_eq_of ℂ, DirectSum.toModule_lof]
  rfl

theorem compOp_mem (hI : DirectSum.IsInternal L) (T : E →ₗ[ℂ] E) (σ : ι → ι) {i : ι}
    {x : E} (hx : x ∈ L i) : compOp hI T σ x ∈ L (σ i) := by
  rw [compOp_of_mem hI T σ hx]; exact iproj_mem hI _ _

/-- Membership in a sup of summands is detected by the projections. -/
theorem mem_iSup_of_iproj (hI : DirectSum.IsInternal L) (P : ι → Prop) {x : E}
    (h : ∀ i, ¬ P i → iproj hI i x = 0) : x ∈ ⨆ (i : ι) (_ : P i), L i := by
  obtain ⟨s, hs⟩ := sum_iproj hI x
  rw [← hs]
  refine Submodule.sum_mem _ fun i _ => ?_
  by_cases hi : P i
  · exact Submodule.mem_iSup_of_mem i (Submodule.mem_iSup_of_mem hi (iproj_mem hI i x))
  · rw [h i hi]; exact Submodule.zero_mem _

/-- Projections of a vector of a sup of summands vanish outside the sup. -/
theorem iproj_eq_zero_of_mem_iSup (hI : DirectSum.IsInternal L) (P : ι → Prop) {x : E}
    (hx : x ∈ ⨆ (i : ι) (_ : P i), L i) {j : ι} (hj : ¬ P j) : iproj hI j x = 0 := by
  refine Submodule.iSup_induction _ (motive := fun x => iproj hI j x = 0) hx ?_ (map_zero _)
    (fun x y hx hy => by beta_reduce at hx hy ⊢; rw [map_add, hx, hy, add_zero])
  intro i y hy
  refine Submodule.iSup_induction _ (motive := fun x => iproj hI j x = 0) hy ?_ (map_zero _)
    (fun x y hx hy => by beta_reduce at hx hy ⊢; rw [map_add, hx, hy, add_zero])
  intro hi z hz
  exact iproj_of_mem_ne hI (fun e => hj (by rw [← e]; exact hi)) hz

end Comp

/-! ### The layer grading of a graded-unitary VOA -/

section Layers

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
variable (B : InvariantForm W) (R : RealStructure W) (F : GradedFlag W)
  (hGU : GradedUnitary B R F) (hrefl : GramRefl B)

include hGU hrefl in
/-- **The layer grading of a graded-unitary VOA is internal.** -/
theorem layerDeg_isInternal : DirectSum.IsInternal (layerDeg B F) := by
  classical
  have hpos := isPosOn_carrierForm B R F hGU hrefl
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top _
    (layerDeg_span B R F hGU hrefl)
  rw [iSupIndep_def]
  intro a
  rw [Submodule.disjoint_def]
  intro x hx hx'
  apply eq_zero_of_sesq_self_eq_zero _ hpos
  refine sesq_iSup_right' _ (fun b => ⨆ (_ : b ≠ a), layerDeg B F b) (fun b y hy => ?_) x hx'
  by_cases hba : b = a
  · subst hba
    simp only [ne_eq, not_true_eq_false, iSup_false, Submodule.mem_bot] at hy
    rw [hy, SesqForm.zero_right]
  · beta_reduce at hy
    rw [iSup_pos (show b ≠ a from hba)] at hy
    exact layerDeg_orth B R F hGU hrefl a b (Ne.symm hba) x hx y hy

theorem layerDeg_layerIndex (t : ℕ) (m : ℤ) :
    layerDeg B F (layerIndex t m) =
      (F.layer m (LiRadical.gradedForm B m) t).map (W.grading m).subtype := by
  apply le_antisymm
  · refine iSup_le fun m' => iSup_le fun t' => iSup_le fun h => ?_
    obtain ⟨rfl, rfl⟩ := layerIndex_injective h
    exact le_rfl
  · exact le_iSup₂_of_le m t (le_iSup_of_le rfl le_rfl)

theorem layerDeg_le_piece (t : ℕ) (m : ℤ) : layerDeg B F (layerIndex t m) ≤ F.piece t m := by
  rw [layerDeg_layerIndex]
  rintro _ ⟨x, hx, rfl⟩
  exact (GradedFlag.layer_le_pieceIn F m _ t hx)

theorem layerDeg_le_grading (t : ℕ) (m : ℤ) :
    layerDeg B F (layerIndex t m) ≤ W.grading m := by
  rw [layerDeg_layerIndex]
  rintro _ ⟨x, -, rfl⟩
  exact x.2

theorem layerDeg_eq_bot_of {i : (ℤ × ℤ) × ℂ} (h : ∀ t m, layerIndex t m ≠ i) :
    layerDeg B F i = ⊥ := by
  rw [eq_bot_iff]
  refine iSup_le fun m => iSup_le fun t => iSup_le fun e => ?_
  exact absurd e (h t m)

include hGU hrefl in
/-- **The `t`-th piece at weight `m` lies in the sum of the layers `s ≤ t` at weight `m`.** -/
theorem piece_le_iSup_layerDeg (t : ℕ) (m : ℤ) :
    F.piece t m ≤ ⨆ (s : ℕ) (_ : s ≤ t), layerDeg B F (layerIndex s m) := by
  haveI := W.finrank m
  intro w hw
  have hwm : w ∈ W.grading m := F.le_grading t m hw
  have hin : (⟨w, hwm⟩ : W.grading m) ∈ F.pieceIn t m := hw
  -- induction on `t` in the `pieceIn` formulation
  suffices H : ∀ t : ℕ, ∀ y ∈ F.pieceIn t m, ((y : W.grading m) : 𝒱) ∈
      ⨆ (s : ℕ) (_ : s ≤ t), layerDeg B F (layerIndex s m) from H t _ hin
  intro t
  induction t with
  | zero =>
      intro y hy
      have h := (layerDecomposition F (hrefl m) (hGU m).1 0).1
      rw [GradedFlag.pieceLT_zero, bot_sup_eq] at h
      rw [← h] at hy
      refine Submodule.mem_iSup_of_mem 0 (Submodule.mem_iSup_of_mem le_rfl ?_)
      rw [layerDeg_layerIndex]
      exact ⟨y, hy, rfl⟩
  | succ q ih =>
      intro y hy
      have h := (layerDecomposition F (hrefl m) (hGU m).1 (q + 1)).1
      rw [GradedFlag.pieceLT_succ] at h
      rw [← h] at hy
      obtain ⟨f, hf, l, hl, rfl⟩ := Submodule.mem_sup.mp hy
      rw [Submodule.coe_add]
      refine Submodule.add_mem _ ?_ ?_
      · have hle : (⨆ (s : ℕ) (_ : s ≤ q), layerDeg B F (layerIndex s m)) ≤
            ⨆ (s : ℕ) (_ : s ≤ q + 1), layerDeg B F (layerIndex s m) :=
          iSup_mono fun s => iSup_mono' fun hs => ⟨Nat.le_succ_of_le hs, le_rfl⟩
        exact hle (ih f hf)
      · refine Submodule.mem_iSup_of_mem (q + 1) (Submodule.mem_iSup_of_mem le_rfl ?_)
        rw [layerDeg_layerIndex]
        exact ⟨l, hl, rfl⟩

include hGU hrefl in
/-- **A vector of the `t`-th piece and its `t`-th layer component differ by lower layers.** -/
theorem sub_iproj_layer_mem (t : ℕ) (m : ℤ) {w : 𝒱} (hw : w ∈ F.piece t m) :
    w - iproj (layerDeg_isInternal B R F hGU hrefl) (layerIndex t m) w ∈
      ⨆ (s : ℕ) (_ : s < t), layerDeg B F (layerIndex s m) := by
  set hI := layerDeg_isInternal B R F hGU hrefl
  have h := piece_le_iSup_layerDeg B R F hGU hrefl t m hw
  have h' : w - iproj hI (layerIndex t m) w ∈
      ⨆ (i : (ℤ × ℤ) × ℂ) (_ : ∃ s < t, layerIndex s m = i), layerDeg B F i := by
    refine mem_iSup_of_iproj hI (fun i => ∃ s < t, layerIndex s m = i) ?_
    intro i hi
    rw [map_sub]
    by_cases hit : i = layerIndex t m
    · subst hit
      rw [iproj_of_mem_same hI (iproj_mem hI _ _), sub_self]
    · rw [iproj_of_mem_ne hI (Ne.symm hit) (iproj_mem hI _ _), sub_zero]
      refine iproj_eq_zero_of_mem_iSup hI (fun i => ∃ s ≤ t, layerIndex s m = i) ?_ ?_
      · have hle : (⨆ (s : ℕ) (_ : s ≤ t), layerDeg B F (layerIndex s m)) ≤
            ⨆ (i : (ℤ × ℤ) × ℂ) (_ : ∃ s ≤ t, layerIndex s m = i), layerDeg B F i :=
          iSup_le fun s => iSup_le fun hs =>
            le_iSup_of_le (layerIndex s m) (le_iSup_of_le ⟨s, hs, rfl⟩ le_rfl)
        exact hle h
      · rintro ⟨s, hs, rfl⟩
        rcases lt_or_eq_of_le hs with hs | rfl
        · exact hi ⟨s, hs, rfl⟩
        · exact hit rfl
  have hle : (⨆ (i : (ℤ × ℤ) × ℂ) (_ : ∃ s < t, layerIndex s m = i), layerDeg B F i) ≤
      ⨆ (s : ℕ) (_ : s < t), layerDeg B F (layerIndex s m) := by
    refine iSup_le fun i => iSup_le fun hi => ?_
    obtain ⟨s, hs, rfl⟩ := hi
    exact le_iSup_of_le s (le_iSup_of_le hs le_rfl)
  exact hle h'

theorem iSup_layer_lt_le_piece (t : ℕ) (m : ℤ) :
    (⨆ (s : ℕ) (_ : s < t), layerDeg B F (layerIndex s m)) ≤ F.piece (t - 1) m :=
  iSup_le fun s => iSup_le fun hs =>
    (layerDeg_le_piece B F s m).trans (F.mono m (by omega))

end Layers

end

end VOA.KoszulResidual
