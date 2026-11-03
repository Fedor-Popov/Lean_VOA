/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.KoszulConcreteGrading
import VOA.Examples.TwoSeriesKoszulGr

/-!
# Level-generic port of `KoszulConcreteGrading`
-/

namespace VOA.TwoSeries

open VOA.ConcreteHodge VOA.KoszulConcrete VOA.SymbolModel VOA.CyclicEval Sl2CosetConcrete
open Sl2SemiInfinite AffineSl2GeneralRigidity AffineSl2BelowCritical VOA.GradedUnitaryCohomology
open VOA.LeeYangCosetTransfer VOA.VertexOperatorAlgebra VOA.LeeYangTransferAssembly VOA.SympFerm
open VOA.Ghost
open scoped TensorProduct

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

universe u v w

variable (L : CosetLevels)

/-! ## Port of `KoszulConcreteGrading` -/


/-! ### Ghost counts of a fine index -/

/-! ### The joint grading -/

/-- Matter part: the fine matter grading at antighost number `0`. -/
def matterBK (j : KF × ℤ) : Submodule ℂ (MatterSpace L) := if j.2 = 0 then (matterF L) j.1 else ⊥

/-- **The joint (fine index, antighost number) grading of the BRST space.** -/
def blockB : KF × ℤ → Submodule ℂ (BRSTSpace L) := tensorDeg (matterBK L) VOA.KoszulConcrete.ghostB

theorem matterB_span (hA : GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag L)) :
    iSup (matterBK L) = ⊤ := by
  rw [eq_top_iff, ← (matterF_span L) hA]
  refine iSup_le fun k => le_iSup_of_le (k, 0) ?_
  simp [matterBK]

section Internal

variable {BB : InvariantForm BVOA} {RB : RealStructure BVOA}

theorem matterB_orth (hA : GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag L)) :
    ∀ a b, a ≠ b → ∀ x ∈ (matterBK L) a, ∀ y ∈ (matterBK L) b,
      (((carrierForm (affineForm L) (affineRealStructure L) (affineFlag L) hA (affineGramRefl L)).tensor
        (unitaryCarrierForm BB RB)).tensor
        (carrierForm (auxiliaryForm L) (auxiliaryRealStructure L) (auxiliaryFlag L) (auxiliaryGradedUnitary L)
          (auxiliaryGramRefl L))) x y = 0 := by
  intro a b hab x hx y hy
  unfold matterBK at hx hy
  split_ifs at hx hy with ha hb
  · have : a.1 ≠ b.1 := fun h => hab (Prod.ext h (ha.trans hb.symm))
    exact (matterF_orth L) hA a.1 b.1 this x hx y hy
  · rw [Submodule.mem_bot] at hy; rw [hy, SesqForm.zero_right]
  · rw [Submodule.mem_bot] at hx; rw [hx, SesqForm.zero_left]
  · rw [Submodule.mem_bot] at hx; rw [hx, SesqForm.zero_left]

theorem blockB_orth (hA : GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag L))
    (w : Finset ModeIdx → ℝ) :
    ∀ a b, a ≠ b → ∀ x ∈ (blockB L) a, ∀ y ∈ (blockB L) b,
      (matterGhostForm L) hA BB RB (ghostForm w) x y = 0 :=
  tensorDeg_orth _ _ _ _ ((matterB_orth L) hA) (ghostB_orth w)

/-- **The joint grading is internal.** -/
theorem blockB_isInternal (hA : GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag L))
    (hB : VOA.ConcreteHodge.Unitary BB RB) (w : Finset ModeIdx → ℝ) (hw : ∀ s, 0 < w s) :
    DirectSum.IsInternal (blockB L) := by
  classical
  have hpos := (weakGU_matterGhostForm L) hA hB (ghostForm_pos w hw)
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top _
    (tensorDeg_span _ _ ((matterB_span L) hA) ghostB_span)
  rw [iSupIndep_def]
  intro a
  rw [Submodule.disjoint_def]
  intro x hx hx'
  apply eq_zero_of_sesq_self_eq_zero _ hpos
  refine sesq_iSup_right' _ (fun b => ⨆ (_ : b ≠ a), (blockB L) b) (fun b y hy => ?_) x hx'
  by_cases hba : b = a
  · subst hba
    simp only [ne_eq, not_true_eq_false, iSup_false, Submodule.mem_bot] at hy
    rw [hy, SesqForm.zero_right]
  · beta_reduce at hy
    rw [iSup_pos (show b ≠ a from hba)] at hy
    exact blockB_orth L (BB := BB) (RB := RB) hA w a b (Ne.symm hba) x hx y hy

end Internal

/-! ### Comparison with the fine grading -/

theorem blockB_le_brstDegF (j : KF × ℤ) : (blockB L) j ≤ (brstDegF L) j.1 :=
  tensorDeg_le (AddMonoidHom.fst KF ℤ) _ _ (matterF L) ghostDegF (brstDegF L)
    (fun _ _ _ _ hx hy => tmul_mem_tensorDeg _ _ hx hy)
    (fun i => by unfold matterBK; split_ifs <;> simp)
    (fun i => by unfold VOA.KoszulConcrete.ghostB; split_ifs <;> simp) j

theorem matterF_eq_bot {k : KF} (hk : k.2 ≠ 0 ∨ k.1.1.2 ≠ 0) : (matterF L) k = ⊥ := by
  unfold matterF
  split_ifs with h
  · rcases hk with hk | hk
    · exact absurd h hk
    · refine le_bot_iff.mp fun x hx => ?_
      rw [Submodule.mem_bot]
      exact eq_zero_of_mem_zeroGhost hk ((matterDeg_le_zeroGhost L) k.1 hx)
  · rfl

/-- **No negative antighost or ghost counts**: `(blockB L) (k, q) = 0` unless `q ≥ 0` and
`gh + q ≥ 0` (`#c = gh + #b`). -/
theorem blockB_eq_bot {j : KF × ℤ} (hj : j.2 < 0 ∨ j.1.1.1.2 + j.2 < 0) : (blockB L) j = ⊥ := by
  refine le_bot_iff.mp (iSup_le fun b => ?_)
  by_cases hb : b.2 = 0 ∧ b.1.2 = 0 ∧ b.1.1.1.2 = 0
  · obtain ⟨hb2, hbc, hbg⟩ := hb
    have hg : VOA.KoszulConcrete.ghostB (j - b) = ⊥ := by
      unfold VOA.KoszulConcrete.ghostB
      split_ifs with h
      · refine VOA.KoszulConcrete.ghostDegF_eq_bot ?_
        rintro ⟨nb, nc, hnb, hnc⟩
        simp only [Prod.fst_sub, Prod.snd_sub, hb2, sub_zero] at h hnb hnc
        simp only [b2_apply, c2_apply, Prod.fst_sub, Prod.snd_sub] at h hnb hnc
        rcases hj with hj | hj <;> omega
      · rfl
    rw [hg, Submodule.map₂_bot_right]
  · have hm : (matterBK L) b = ⊥ := by
      unfold matterBK
      split_ifs with h
      · refine (matterF_eq_bot L) ?_
        by_contra hc
        push Not at hc
        exact hb ⟨h, hc.1, hc.2⟩
      · rfl
    rw [hm, Submodule.map₂_bot_left]

/-! ### Lifting shifts to the joint grading -/

theorem matterB_lift {T : (MatterSpace L) →ₗ[ℂ] (MatterSpace L)} {P : KF → Prop}
    (hT : ShiftsInto (matterF L) T P) : ShiftsInto (matterBK L) T (fun δ => P δ.1 ∧ δ.2 = 0) := by
  intro j x hx
  unfold matterBK at hx
  split_ifs at hx with hj
  · have h := hT j.1 x hx
    refine (iSup_le fun δ => iSup_le fun hδ => ?_ : shiftTarget (matterF L) P j.1 ≤ _) h
    intro y hy
    refine mem_shiftTarget (δ := (δ, 0)) ⟨hδ, rfl⟩ ?_
    simp only [matterBK, Prod.snd_add, hj, add_zero, if_true, Prod.fst_add]
    exact hy
  · rw [Submodule.mem_bot] at hx
    rw [hx, map_zero]; exact Submodule.zero_mem _

/-! ### `Q` changes the antighost number by `0` or `-1` -/

/-- **`Q` shifts the joint grading by `GoodB`** on the whole BRST space: the antighost number
changes by `0` (`c`-creating terms) or `-1` (`b`-annihilating terms). -/
theorem semiInfiniteQ_shiftsB (hA : GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag L)) :
    ShiftsInto (blockB L) (semiInfiniteQ (matterAction L).toAffineSl2Action) GoodB := by
  intro k z hz
  refine tensorDeg_induction (matterBK L) VOA.KoszulConcrete.ghostB k
    (fun z => semiInfiniteQ (matterAction L).toAffineSl2Action z ∈
      shiftTarget (blockB L) GoodB k)
    (by simp) (fun x y hx hy => by simpa only [map_add] using Submodule.add_mem _ hx hy)
    (fun c x hx => by simpa only [map_smul] using Submodule.smul_mem _ c hx) ?_ z hz
  intro b x hx y hy
  rw [semiInfiniteQ_tmul, matter_even_invol]
  have hk : b + (k - b) = k := by abel
  refine Submodule.add_mem _ (Submodule.sum_mem _ fun a _ => ?_) ?_
  · refine finsum_induction (fun u => u ∈ shiftTarget (blockB L) GoodB k)
      (Submodule.zero_mem _) (fun _ _ h1 h2 => Submodule.add_mem _ h1 h2) (fun n => ?_)
    have hJ := (matterB_lift L) ((matterMode_shiftsF L) hA a n) b x hx
    have hc : mode (sl2GhostSVA.Y (cGhost a)) (-n - 1) y ∈
        shiftTarget VOA.KoszulConcrete.ghostB (fun δ : KF × ℤ => δ.1 = ghShiftF 1 n ∧ b2 δ.1 = 2 * δ.2)
          (k - b) := by
      have h := ghostB_lift (ghostYCoeff_shifts a 1 n) (k - b) y hy
      simpa only [ghostGenerator_one, mode_apply, show -(-n - 1) - 1 = n by ring] using h
    have h := tmul_mem_tensor_shiftTarget (matterBK L) VOA.KoszulConcrete.ghostB hJ hc
    rw [hk] at h
    exact shiftTarget_mono (current_term_goodB n) k h
  · have hx' : x ∈ shiftTarget (matterBK L) (· = 0) b := mem_shiftTarget rfl (by rwa [add_zero])
    have h := tmul_mem_tensor_shiftTarget (matterBK L) VOA.KoszulConcrete.ghostB hx'
      (ghostB_lift cubicCharge_shifts (k - b) y hy)
    rw [hk] at h
    refine shiftTarget_mono ?_ k h
    rintro δ ⟨a₁, a₂, rfl, ⟨h1, h2⟩, rfl⟩
    rw [zero_add]
    exact goodB_of h1 h2

/-! ### Stability of the relative weight spaces -/

theorem matterZero_mem_matterB (a : Fin 3) {j : KF × ℤ} {x : (MatterSpace L)} (hx : x ∈ (matterBK L) j) :
    mode ((matterSVA L).Y ((matterAction L).toAffineSl2Action.current a)) 0 x ∈ (matterBK L) j := by
  unfold matterBK matterF at hx ⊢
  split_ifs at hx ⊢ <;> first
    | exact (matterDeg_zero_preserve L) (aZeroModesPreserveLayers L) (uZeroModesPreserveLayers L) a _ x hx
    | (rw [Submodule.mem_bot] at hx ⊢; rw [hx, map_zero])

theorem totalZero_mem_blockB (a : Fin 3) (j : KF × ℤ) :
    ∀ x ∈ (blockB L) j, totalCurrentZero (matterAction L).toAffineSl2Action a x ∈ (blockB L) j :=
  tensorDeg_preserve_sum (matterBK L) VOA.KoszulConcrete.ghostB _ _ (ghZero a)
    (fun m g => totalCurrentZero_tmul _ a m g) (fun _ _ hx => (matterZero_mem_matterB L) a hx)
    (fun _ _ hy => ghZero_mem_ghostB a hy) j

theorem antiZero_mem_blockB (a : Fin 3) (j : KF × ℤ) :
    ∀ x ∈ (blockB L) j, antighostZero (matterSVA L) a x ∈ (blockB L) (j + antiShiftB) := by
  refine tensorDeg_shift_right (matterBK L) VOA.KoszulConcrete.ghostB _ (VOA.ConcreteHodge.gMode a 0 0) antiShiftB
    (fun m g => ?_)
    (fun i y hy => ?_) j
  · rw [antighostZero_eq, TensorProduct.map_tmul, LinearMap.id_apply]
  · unfold VOA.KoszulConcrete.ghostB at hy ⊢
    split_ifs at hy with h1
    · have hb : b2 (i + antiShiftB).1 = 2 * (i + antiShiftB).2 := by
        simp only [antiShiftB, Prod.fst_add, Prod.snd_add, map_add, b2_antiShift, h1, add_zero]
      rw [if_pos hb]
      simpa [antiShiftB] using ghostModeF_mem a 0 0 hy
    · rw [Submodule.mem_bot] at hy; rw [hy, map_zero]; exact Submodule.zero_mem _

theorem blockB_le_weight (w : Finset ModeIdx → ℝ) (j : KF × ℤ) :
    (blockB L) j ≤ (brstSVA L).grading j.1.1.2 :=
  ((blockB_le_brstDegF L) j).trans (((brstDegF_le_brstDeg L) w j.1).trans
    ((brstDeg_le_weight L) (ghostRGrading w) _))

/-- **The actual relative weight spaces are stable under the joint projections.** -/
theorem relativeWeight_stableB (hA : GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag L))
    {BB : InvariantForm BVOA} {RB : RealStructure BVOA} (hB : VOA.ConcreteHodge.Unitary BB RB)
    (w : Finset ModeIdx → ℝ) (hw : ∀ s, 0 < w s) (n : ℤ) :
    ProjStable ((blockB_isInternal L) hA hB w hw) ((relativeWeight L) n) := by
  have hI := (blockB_isInternal L) hA hB w hw
  refine projStable_inf hI (projStable_inf hI ?_ ?_) ?_
  · exact projStable_iInf hI fun a => projStable_ker hI _ ((totalZero_mem_blockB L) a)
  · exact projStable_iInf hI fun a =>
      projStable_ker_shift hI _ (· + antiShiftB) (add_left_injective _) ((antiZero_mem_blockB L) a)
  · exact projStable_weight hI (brstSVA L).isInternal (fun j => j.1.1.2) ((blockB_le_weight L) w) (n : ℂ)


end

end VOA.TwoSeries
