/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.TwoSeriesHodgeGood
import VOA.Examples.BRSTGoodnessCreation

/-!
# Level-generic port of the level-specific parts of `BRSTGoodness*`

Goodness of the actual level-`L` BRST differential for the interpreted grading, and the
creation-mode generator test.  Level-independent declarations are reused from
`BRSTGoodnessMatter`, `BRSTGoodnessDifferential`, `BRSTGoodnessEndpoint`,
`BRSTGoodnessCreation`.
-/

namespace VOA.TwoSeries

open VOA.ConcreteHodge Sl2CosetConcrete Sl2SemiInfinite AffineSl2GeneralRigidity
open AffineSl2BelowCritical VOA.GradedUnitaryCohomology VOA.LeeYangCosetTransfer
open VOA.VertexOperatorAlgebra VOA.LeeYangTransferAssembly AffineVOA AffineVOA.Inst
open AffineVOA.CorrectedR VOA.SympFerm VOA.Ghost LeeYangTransferAssembly LeeYangShortcut
open VirGradedUnitarity LeeYang VirModule
open scoped TensorProduct

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

variable (L : CosetLevels)

/-! ## Port of `BRSTGoodnessMatter` -/


/-! ### Generic: adjoint pairs of filtered operators shift layers by a bounded amount -/

section Generic

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

end Generic

/-! ### Li-goodness of the corrected affine flag -/

section Li

variable (k : ℂ) (hk : k + 2 ≠ 0)

end Li

/-! ### The three factors -/

/-- The `A` current mode. -/
def aMode (a : Fin 3) (n : ℤ) : Module.End ℂ (ASpace L) := mode ((ASVA L).Y ((aAction L).current
    a)) n

/-- The `U` current mode. -/
def uMode (a : Fin 3) (n : ℤ) : Module.End ℂ (USpace L) := mode ((USVA L).Y ((uAction L).current
    a)) n

theorem aMode_mkQ (a : Fin 3) (n : ℤ) (x : WakModule L.kA) :
    (aMode L) a n ((QuotVOA.maxGradedIdeal (universal L.kA L.aNoncritical)).mkQ x) =
      (QuotVOA.maxGradedIdeal (universal L.kA L.aNoncritical)).mkQ (J L.kA a n x) := by
  have h : (aMode L) a n ((QuotVOA.maxGradedIdeal (universal L.kA L.aNoncritical)).mkQ x) =
      (QuotVOA.maxGradedIdeal (universal L.kA L.aNoncritical)).mkQ
        ((universal L.kA L.aNoncritical).smul (currentState L.kA a) n x) :=
    SimpleQuot.maxQuotientVOA_mkQ_smul _ _ _ _
  rw [h]
  congr 1
  exact smul_currentState_eq_J L.kA L.aNoncritical a n x

theorem uMode_apply (a : Fin 3) (n : ℤ) (x : (USpace L)) : (uMode L) a n x = J L.kU a n x :=
  smul_currentState_eq_J L.kU L.uNoncritical a n x

theorem aMode_flag (a : Fin 3) (n : ℤ) (p : ℕ) (m : ℤ) :
    ∀ x ∈ (affineFlag L).piece p m, (aMode L) a n x ∈ (affineFlag L).piece (p + eN n) (m - n) := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
  rw [aMode_mkQ]
  exact Submodule.mem_map_of_mem ⟨correctedPiece_J L.kA L.aNoncritical a n hy.1,
    J_mem_grading L.aNoncritical a n hy.2⟩

theorem aMode_adj (a : Fin 3) (n : ℤ) (x y : (ASpace L)) :
    (affineForm L).form ((aMode L) a n x) y = -(affineForm L).form x ((aMode L) a (-n) y) := by
  obtain ⟨x, rfl⟩ := (QuotVOA.maxGradedIdeal (universal L.kA L.aNoncritical)).mkQ_surjective x
  obtain ⟨y, rfl⟩ := (QuotVOA.maxGradedIdeal (universal L.kA L.aNoncritical)).mkQ_surjective y
  rw [aMode_mkQ, aMode_mkQ]
  change (simpleForm L.kA L.aNoncritical).form _ _ = -(simpleForm L.kA L.aNoncritical).form _ _
  rw [simpleForm_mkQ, simpleForm_mkQ]
  exact universalForm_current_adj L.aNoncritical a n x y

/-- **The `A` current modes are good for the corrected layers** (from `hA`). -/
theorem aMode_shifts (hA : GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag L))
    (a : Fin 3) (n : ℤ) : ShiftsInto (aDeg L) ((aMode L) a n) (modePred n) :=
  layerDeg_shifts (affineForm L) (affineFlag L) (simpleForm_isSymmetric L.kA L.aNoncritical)
    (fun m => (hA m).1) ((aMode L) a n) ((aMode L) a (-n)) n (eN n) (eN (-n))
    ((aMode_flag L) a n) (fun q m x hx => by
      have h := (aMode_flag L) a (-n) q m x hx
      rwa [sub_neg_eq_add] at h)
    ((aMode_adj L) a n)

theorem uMode_flag (a : Fin 3) (n : ℤ) (p : ℕ) (m : ℤ) :
    ∀ x ∈ (auxiliaryFlag L).piece p m, (uMode L) a n x ∈ (auxiliaryFlag L).piece (p + eN n) (m -
        n) := by
  intro x hx
  rw [uMode_apply]
  unfold eN
  split_ifs with hn
  · exact J_mem_ordinaryFlag_of_nonneg L.uNoncritical a hn hx
  · have h := J_mem_ordinaryFlag_of_neg L.uNoncritical a (m := -n) (by omega) hx
    rwa [neg_neg, ← sub_eq_add_neg] at h

/-- **The `U` current modes are good for the PBW layers** (unconditional). -/
theorem uMode_shifts (a : Fin 3) (n : ℤ) : ShiftsInto (uDeg L) ((uMode L) a n) (modePred n) :=
  layerDeg_shifts (auxiliaryForm L) (auxiliaryFlag L) (universalForm_isSymmetric L.kU
      L.uNoncritical)
    (fun m => ((auxiliaryGradedUnitary L) m).1) ((uMode L) a n) ((uMode L) a (-n)) n (eN n) (eN
        (-n))
    ((uMode_flag L) a n) (fun q m x hx => by
      have h := (uMode_flag L) a (-n) q m x hx
      rwa [sub_neg_eq_add] at h)
    (fun x y => by
      rw [uMode_apply, uMode_apply]
      exact universalForm_current_adj L.uNoncritical a n x y)

/-! ### The matter current modes -/

theorem matterMode_tmul (a : Fin 3) (n : ℤ) (x : (ASpace L)) (y : BSpace) (z : (USpace L)) :
    mode ((matterSVA L).Y ((matterAction L).toAffineSl2Action.current a)) n
        ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] z) =
      (((aMode L) a n x ⊗ₜ[ℂ] y + x ⊗ₜ[ℂ] bMode a n y) ⊗ₜ[ℂ] z) +
        (x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (uMode L) a n z := by
  have h1 := tensorCurrentMode_tmul
    (tensorAffineAction (aAction L).toAffineSl2Action bAction.toAffineSl2Action
      (aParityCompatible L) bParityCompatible (abTensorGrading L)) (uAction L).toAffineSl2Action a n
    (x ⊗ₜ[ℂ] y) z
  have h2 : mode ((TensorVA.tensorSVA (ASVA L) BSVA (aParityCompatible L) bParityCompatible
      (abTensorGrading L)).Y ((tensorAffineAction (aAction L).toAffineSl2Action
          bAction.toAffineSl2Action
        (aParityCompatible L) bParityCompatible (abTensorGrading L)).current a)) n (x ⊗ₜ[ℂ] y) =
      (aMode L) a n x ⊗ₜ[ℂ] y + x ⊗ₜ[ℂ] bMode a n y :=
    tensorCurrentMode_tmul (aAction L).toAffineSl2Action bAction.toAffineSl2Action a n x y
  refine h1.trans ?_
  change mode ((TensorVA.tensorSVA (ASVA L) BSVA (aParityCompatible L) bParityCompatible
      (abTensorGrading L)).Y ((tensorAffineAction (aAction L).toAffineSl2Action
          bAction.toAffineSl2Action
        (aParityCompatible L) bParityCompatible (abTensorGrading L)).current a)) n (x ⊗ₜ[ℂ] y)
            ⊗ₜ[ℂ] z +
      (x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (uMode L) a n z = _
  rw [h2]

/-- The matter current mode as a sum of factor modes. -/
theorem matterMode_eq (a : Fin 3) (n : ℤ) :
    mode ((matterSVA L).Y ((matterAction L).toAffineSl2Action.current a)) n =
      TensorProduct.map (TensorProduct.map ((aMode L) a n) LinearMap.id) LinearMap.id +
      TensorProduct.map (TensorProduct.map LinearMap.id (bMode a n)) LinearMap.id +
      TensorProduct.map LinearMap.id ((uMode L) a n) := by
  apply TensorProduct.ext'
  intro w z
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add w w' hw hw' => rw [TensorProduct.add_tmul, map_add, map_add, hw, hw']
  | tmul x y =>
      rw [matterMode_tmul]
      simp only [LinearMap.add_apply, TensorProduct.map_tmul, LinearMap.id_apply,
        TensorProduct.add_tmul]

/-- **The matter current mode `J_n` is good for the interpreted matter grading.** -/
theorem matterMode_shifts (hA : GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag L))
    (a : Fin 3) (n : ℤ) :
    ShiftsInto (matterDeg L)
      (mode ((matterSVA L).Y ((matterAction L).toAffineSl2Action.current a)) n) (modePred n) := by
  rw [matterMode_eq]
  refine ((ShiftsInto.add ?_ ?_).add ?_)
  · exact (tensorDeg_map_shiftTarget _ (uDeg L)
      ((tensorDeg_map_shiftTarget (aDeg L) bDeg ((aMode_shifts L) hA a n) (shiftsInto_id bDeg)).mono
        fun _ h => addPred_zero_right h)
      (shiftsInto_id (uDeg L))).mono fun _ h => addPred_zero_right h
  · exact (tensorDeg_map_shiftTarget _ (uDeg L)
      ((tensorDeg_map_shiftTarget (aDeg L) bDeg (shiftsInto_id (aDeg L)) (bMode_shifts a n)).mono
        fun _ h => addPred_zero_left h)
      (shiftsInto_id (uDeg L))).mono fun _ h => addPred_zero_right h
  · exact (tensorDeg_map_shiftTarget (tensorDeg (aDeg L) bDeg) (uDeg L)
      (shiftsInto_id _) ((uMode_shifts L) a n)).mono fun _ h => addPred_zero_left h


/-! ## Port of `BRSTGoodnessDifferential` -/


/-! ### The fine BRST grading -/

/-- The matter grading, placed at `c₀`-number `0`. -/
def matterF (k : KF) : Submodule ℂ (MatterSpace L) := if k.2 = 0 then (matterDeg L) k.1 else ⊥

theorem matterF_le (k : KF) : (matterF L) k ≤ (matterDeg L) (fstF k) := by
  unfold matterF; split_ifs <;> simp

theorem matterDeg_le_matterF (i : (ℤ × ℤ) × ℂ) : (matterDeg L) i ≤ (matterF L) (i, 0) := by
  simp [matterF]

theorem matterDeg_le_coarsen (i : (ℤ × ℤ) × ℂ) :
    (matterDeg L) i ≤ ⨆ (k : KF) (_ : fstF k = i), (matterF L) k :=
  le_trans ((matterDeg_le_matterF L) i) (le_iSup_of_le (i, 0) (le_iSup_of_le rfl le_rfl))

/-- **The fine BRST grading.** -/
def brstDegF : KF → Submodule ℂ (BRSTSpace L) := tensorDeg (matterF L) ghostDegF

theorem brstDegF_le_brstDeg (w : Finset ModeIdx → ℝ) (k : KF) :
    (brstDegF L) k ≤ (brstDeg L) (ghostRGrading w) (fstF k) :=
  tensorDeg_le fstF _ _ _ _ _ (fun _ _ _ _ hx hy => tmul_mem_tensorDeg _ _ hx hy)
    (matterF_le L) ghostDegF_le_ghostDeg k

theorem brstDeg_le_coarsenF (w : Finset ModeIdx → ℝ) (i : (ℤ × ℤ) × ℂ) :
    (brstDeg L) (ghostRGrading w) i ≤ ⨆ (k : KF) (_ : fstF k = i), (brstDegF L) k :=
  tensorDeg_le_coarsen fstF _ _ _ _ (matterDeg_le_coarsen L) ghostDeg_le_coarsen i

section Internal

variable {BB : InvariantForm BVOA} {RB : RealStructure BVOA}

theorem matterDeg_orth' (hA : GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag L)) :
    ∀ a b, a ≠ b → ∀ x ∈ (matterDeg L) a, ∀ y ∈ (matterDeg L) b,
      (((carrierForm (affineForm L) (affineRealStructure L) (affineFlag L) hA (affineGramRefl
          L)).tensor
        (unitaryCarrierForm BB RB)).tensor
        (carrierForm (auxiliaryForm L) (auxiliaryRealStructure L) (auxiliaryFlag L)
            (auxiliaryGradedUnitary L)
          (auxiliaryGramRefl L))) x y = 0 :=
  tensorDeg_orth _ _ _ _
    (tensorDeg_orth _ _ _ _
      (layerDeg_orth (affineForm L) (affineRealStructure L) (affineFlag L) hA (affineGramRefl L))
      (trivialDeg_orth _ (unitaryCarrierForm_weight_orth BB RB)))
    (layerDeg_orth _ _ _ (auxiliaryGradedUnitary L) (auxiliaryGramRefl L))

theorem matterF_orth (hA : GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag L)) :
    ∀ a b, a ≠ b → ∀ x ∈ (matterF L) a, ∀ y ∈ (matterF L) b,
      (((carrierForm (affineForm L) (affineRealStructure L) (affineFlag L) hA (affineGramRefl
          L)).tensor
        (unitaryCarrierForm BB RB)).tensor
        (carrierForm (auxiliaryForm L) (auxiliaryRealStructure L) (auxiliaryFlag L)
            (auxiliaryGradedUnitary L)
          (auxiliaryGramRefl L))) x y = 0 := by
  intro a b hab x hx y hy
  unfold matterF at hx hy
  split_ifs at hx hy with ha hb
  · have : a.1 ≠ b.1 := fun h => hab (Prod.ext h (ha.trans hb.symm))
    exact (matterDeg_orth' L) hA a.1 b.1 this x hx y hy
  · rw [Submodule.mem_bot] at hy; rw [hy, SesqForm.zero_right]
  · rw [Submodule.mem_bot] at hx; rw [hx, SesqForm.zero_left]
  · rw [Submodule.mem_bot] at hx; rw [hx, SesqForm.zero_left]

theorem matterF_span (hA : GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag L)) :
    iSup (matterF L) = ⊤ := by
  rw [eq_top_iff, ← (matterDeg_span L) hA]
  exact iSup_le fun i => ((matterDeg_le_matterF L) i).trans (le_iSup _ _)

theorem brstDegF_orth (hA : GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag L))
    (w : Finset ModeIdx → ℝ) :
    ∀ a b, a ≠ b → ∀ x ∈ (brstDegF L) a, ∀ y ∈ (brstDegF L) b,
      (matterGhostForm L) hA BB RB (ghostForm w) x y = 0 :=
  tensorDeg_orth _ _ _ _ ((matterF_orth L) hA) (ghostDegF_orth w)

theorem brstDegF_isInternal (hA : GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag
    L))
    (hB : ConcreteHodge.Unitary BB RB) (w : Finset ModeIdx → ℝ) (hw : ∀ s, 0 < w s) :
    DirectSum.IsInternal (brstDegF L) := by
  classical
  have hpos := (weakGU_matterGhostForm L) hA hB (ghostForm_pos w hw)
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top _
    (tensorDeg_span _ _ ((matterF_span L) hA) ghostDegF_span)
  rw [iSupIndep_def]
  intro a
  rw [Submodule.disjoint_def]
  intro x hx hx'
  apply eq_zero_of_sesq_self_eq_zero _ hpos
  refine sesq_iSup_right' _ (fun b => ⨆ (_ : b ≠ a), (brstDegF L) b) (fun b y hy => ?_) x hx'
  by_cases hba : b = a
  · subst hba
    simp only [ne_eq, not_true_eq_false, iSup_false, Submodule.mem_bot] at hy
    rw [hy, SesqForm.zero_right]
  · beta_reduce at hy
    rw [iSup_pos (show b ≠ a from hba)] at hy
    exact (brstDegF_orth L) hA w a b (Ne.symm hba) x hx y hy

end Internal

/-! ### Goodness of `Q` for `R'` on the whole space -/

theorem matterMode_shiftsF (hA : GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag
    L))
    (a : Fin 3) (n : ℤ) :
    ShiftsInto (matterF L)
      (mode ((matterSVA L).Y ((matterAction L).toAffineSl2Action.current a)) n)
      (matterPredF n) := by
  intro k x hx
  unfold matterF at hx
  split_ifs at hx with hk
  · have h := (matterMode_shifts L) hA a n k.1 x hx
    refine (iSup_le fun δ => iSup_le fun hδ => ?_ : shiftTarget (matterDeg L) (modePred n) k.1 ≤ _)
        h
    intro y hy
    refine mem_shiftTarget (δ := (δ, 0)) ⟨rfl, hδ⟩ ?_
    simp only [matterF, Prod.snd_add, hk, add_zero, if_true, Prod.fst_add]
    exact hy
  · rw [Submodule.mem_bot] at hx
    rw [hx, map_zero]; exact Submodule.zero_mem _

theorem matter_even_invol (x : (MatterSpace L)) : (TensorVA.parGr (matterSVA L)).parityInvol x =
    x :=
  (TensorVA.parGr (matterSVA L)).parityInvol_even ((matter_mem_parity_zero L) x)

/-- **`Q` shifts `2R'` by exactly `±1` on the whole BRST space.** -/
theorem semiInfiniteQ_shifts (hA : GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag
    L)) :
    ShiftsInto (brstDegF L) (semiInfiniteQ (matterAction L).toAffineSl2Action) GoodRp := by
  intro k z hz
  refine tensorDeg_induction (matterF L) ghostDegF k
    (fun z => semiInfiniteQ (matterAction L).toAffineSl2Action z ∈
      shiftTarget (brstDegF L) GoodRp k)
    (by simp) (fun x y hx hy => by simpa only [map_add] using Submodule.add_mem _ hx hy)
    (fun c x hx => by simpa only [map_smul] using Submodule.smul_mem _ c hx) ?_ z hz
  intro b x hx y hy
  rw [semiInfiniteQ_tmul, matter_even_invol]
  have hk : b + (k - b) = k := by abel
  refine Submodule.add_mem _ (Submodule.sum_mem _ fun a _ => ?_) ?_
  · refine finsum_induction (fun u => u ∈ shiftTarget (brstDegF L) GoodRp k)
      (Submodule.zero_mem _) (fun _ _ h1 h2 => Submodule.add_mem _ h1 h2) (fun n => ?_)
    have hJ := (matterMode_shiftsF L) hA a n b x hx
    have hc : mode (sl2GhostSVA.Y (cGhost a)) (-n - 1) y ∈
        shiftTarget ghostDegF (· = ghShiftF 1 n) (k - b) := by
      have h := ghostYCoeff_shifts a 1 n (k - b) y hy
      simpa only [ghostGenerator_one, mode_apply, show -(-n - 1) - 1 = n by ring] using h
    have h := tmul_mem_tensor_shiftTarget (matterF L) ghostDegF hJ hc
    rw [hk] at h
    exact shiftTarget_mono (current_term_good n) k h
  · have hx' : x ∈ shiftTarget (matterF L) (· = 0) b := mem_shiftTarget rfl (by rwa [add_zero])
    have h := tmul_mem_tensor_shiftTarget (matterF L) ghostDegF hx'
      (cubicCharge_shifts (k - b) y hy)
    rw [hk] at h
    exact shiftTarget_mono (fun δ hδ => addPred_zero_left hδ) k h

/-! ### Relative states have no `c₀` -/

/-- The `c₀`-number operator on the BRST space. -/
def Phi0 : Module.End ℂ (BRSTSpace L) := TensorProduct.map LinearMap.id Nc0

theorem Phi0_eigen {k : KF} {z : (BRSTSpace L)} (hz : z ∈ (brstDegF L) k) :
    (Phi0 L) z = ((k.2 : ℤ) : ℂ) • z := by
  refine tensorDeg_induction (matterF L) ghostDegF k (fun z => (Phi0 L) z = ((k.2 : ℤ) : ℂ) • z)
    (by simp) (fun x y hx hy => by beta_reduce at hx hy ⊢; rw [map_add, hx, hy, smul_add])
    (fun c x hx => by beta_reduce at hx ⊢; rw [map_smul, hx, smul_comm]) ?_ z hz
  intro b x hx y hy
  unfold matterF at hx
  split_ifs at hx with hb
  · rw [Phi0, TensorProduct.map_tmul, LinearMap.id_apply, Nc0_eigen hy,
      TensorProduct.tmul_smul]
    have : (k - b).2 = k.2 := by simp [Prod.snd_sub, hb]
    rw [this]
  · rw [Submodule.mem_bot] at hx
    rw [hx, TensorProduct.zero_tmul, map_zero, smul_zero]

theorem antighostZero_eq (a : Fin 3) :
    antighostZero (matterSVA L) a = TensorProduct.map LinearMap.id (ConcreteHodge.gMode a 0 0) := by
  apply TensorProduct.ext'
  intro m g
  rw [antighostZero_tmul a ((matter_mem_parity_zero L) m) g, TensorProduct.map_tmul,
    LinearMap.id_apply]
  simp [koszul, ConcreteHodge.gMode]

theorem Phi0_of_antighost {z : (BRSTSpace L)} (hz : ∀ a, antighostZero (matterSVA L) a z = 0) :
    (Phi0 L) z = 0 := by
  have h : ∀ z, (Phi0 L) z = ∑ a : Fin 3, TensorProduct.map LinearMap.id (ConcreteHodge.gMode a 1
      (-1))
      (antighostZero (matterSVA L) a z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul m g =>
        simp only [Phi0, antighostZero_eq, TensorProduct.map_tmul, LinearMap.id_apply, Nc0,
          LinearMap.sum_apply, LinearMap.comp_apply, TensorProduct.tmul_sum]
    | add u v hu hv =>
        rw [map_add, hu, hv, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [map_add, map_add]
  rw [h]
  exact Finset.sum_eq_zero fun a _ => by rw [hz a, map_zero]

/-- **Relative states have `c₀`-number zero.** -/
theorem relative_c0free (hA : GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag L))
    {BB : InvariantForm BVOA} {RB : RealStructure BVOA} (hB : ConcreteHodge.Unitary BB RB)
    (w : Finset ModeIdx → ℝ) (hw : ∀ s, 0 < w s) {z : (BRSTSpace L)}
    (hz : ∀ a, antighostZero (matterSVA L) a z = 0) :
    z ∈ ⨆ (k : KF) (_ : k.2 = 0), (brstDegF L) k := by
  classical
  have hI := (brstDegF_isInternal L) hA hB w hw
  rw [mem_iSup_pred_iff hI]
  intro k hk
  have hpres : ∀ i, ∀ x ∈ (brstDegF L) i, (Phi0 L) x ∈ (brstDegF L) i := fun i x hx => by
    rw [(Phi0_eigen L) hx]; exact Submodule.smul_mem _ _ hx
  have hcomm := LinearMap.congr_fun (iproj_comm_of_preserves hI (Phi0 L) hpres k) z
  simp only [LinearMap.coe_comp, Function.comp_apply, (Phi0_of_antighost L) hz, map_zero] at hcomm
  rw [(Phi0_eigen L) (iproj_mem hI k z)] at hcomm
  have hk' : ((k.2 : ℤ) : ℂ) ≠ 0 := by exact_mod_cast hk
  calc iproj hI k z = (((k.2 : ℤ) : ℂ))⁻¹ • ((((k.2 : ℤ) : ℂ)) • iproj hI k z) := by
        rw [smul_smul, inv_mul_cancel₀ hk', one_smul]
    _ = 0 := by rw [← hcomm, smul_zero]

/-! ### The relative goodness -/

/-- **`RelativeDifferentialGood L` for the concrete ghost grading**, from `hA` and `hB`. -/
theorem relativeDifferentialGood_of_affine
    (hA : GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag L))
    {BB : InvariantForm BVOA} {RB : RealStructure BVOA} (hB : ConcreteHodge.Unitary BB RB)
    (w : Finset ModeIdx → ℝ) (hw : ∀ s, 0 < w s) :
    (RelativeDifferentialGood L) (ghostRGrading w) := by
  classical
  intro n j g x hxrel hx
  have hI := (brstDegF_isInternal L) hA hB w hw
  set i : (ℤ × ℤ) × ℂ := ((j, g), (n : ℂ)) with hi
  -- `x` in fine form
  have hrel : ∀ a, antighostZero (matterSVA L) a x = 0 := fun a =>
    ((mem_relativeCarrier _ x).mp hxrel.1).2 a
  have hx1 := (brstDeg_le_coarsenF L) w i hx
  have hx2 := (relative_c0free L) hA hB w hw hrel
  have hxF := mem_iSup_pred_inf hI hx1 hx2
  -- `Q x` in the image pieces
  set S : KF → Prop := fun k' => ∃ k δ, (fstF k = i ∧ k.2 = 0) ∧ GoodRp δ ∧ k' = k + δ
  have hQ1 : (brstComplex L).Q x ∈ ⨆ (k' : KF) (_ : S k'), (brstDegF L) k' := by
    refine Submodule.iSup_induction _
      (motive := fun x => (brstComplex L).Q x ∈ ⨆ (k' : KF) (_ : S k'), (brstDegF L) k')
      hxF ?_ (by simp) (fun x y hx hy => by
        beta_reduce at hx hy ⊢; rw [map_add]; exact Submodule.add_mem _ hx hy)
    intro k y hy
    refine Submodule.iSup_induction _
      (motive := fun y => (brstComplex L).Q y ∈ ⨆ (k' : KF) (_ : S k'), (brstDegF L) k')
      hy ?_ (by simp) (fun x y hx hy => by
        beta_reduce at hx hy ⊢; rw [map_add]; exact Submodule.add_mem _ hx hy)
    intro hk y hy
    have h := (semiInfiniteQ_shifts L) hA k y hy
    rw [← brstComplex_Q] at h
    refine (iSup_le fun δ => iSup_le fun hδ => ?_ :
      shiftTarget (brstDegF L) GoodRp k ≤ _) h
    exact le_iSup_of_le (k + δ) (le_iSup_of_le ⟨k, δ, hk, hδ, rfl⟩ le_rfl)
  have hQrel : (brstComplex L).Q x ∈ (relativeWeight L) n :=
    ((relativeDifferential L) n ⟨x, hxrel⟩).2
  have hQ2 := (relative_c0free L) hA hB w hw
    ((mem_relativeCarrier _ _).mp hQrel.1).2
  have hQF := mem_iSup_pred_inf hI hQ1 hQ2
  refine (iSup_le fun k' => iSup_le fun hk' => ?_ :
    (⨆ (k' : KF) (_ : S k' ∧ k'.2 = 0), (brstDegF L) k') ≤ _) hQF
  obtain ⟨⟨k, δ, ⟨hk1, hk2⟩, hδ, rfl⟩, hk'2⟩ := hk'
  have hδ2 : δ.2 = 0 := by
    simp only [Prod.snd_add, hk2, zero_add] at hk'2; exact hk'2
  have hfst : fstF (k + δ) = i + piRp δ := by
    rw [map_add, hk1, piRp_eq_fst hδ2]
  refine ((brstDegF_le_brstDeg L) w (k + δ)).trans ?_
  rw [hfst]
  rcases hδ with h | h
  · rw [h]
    refine le_sup_of_le_left (le_of_eq ?_)
    congr 1
    rw [hi]
    simp only [Prod.mk_add_mk, add_zero]
  · rw [h]
    refine le_sup_of_le_right (le_of_eq ?_)
    congr 1
    rw [hi]
    simp only [Prod.mk_add_mk, add_zero, sub_eq_add_neg]


/-! ## Port of `BRSTGoodnessEndpoint` -/


/-- The proved zero-mode homogeneity for the concrete ghost grading. -/
abbrev hZproved (w : Finset ModeIdx → ℝ) : (ZeroModesPreserve L) (ghostRGrading w) :=
  (zeroModesPreserve_concrete L) w ghostCurrentZeroPreserve antighostZeroShift


/-! ## Port of `BRSTGoodnessCreation` -/


/-- Coefficients of corrected-degree-one states of `A` raise the layer index by `≤ 1`. -/
theorem aY_shifts (hA : GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag L))
    {s : (ASpace L)} {w : ℤ} (hs : s ∈ (affineFlag L).piece 1 w) (j : ℤ) :
    ShiftsInto (aDeg L) ((ASVA L).Y s j) UpTwo := by
  intro i x₀ hx₀
  refine Submodule.iSup_induction _ (motive := fun x => (ASVA L).Y s j x ∈ shiftTarget _ _ i) hx₀
    ?_ (by simp) (fun x y hx hy => by
      beta_reduce at hx hy ⊢; rw [map_add]; exact Submodule.add_mem _ hx hy)
  intro m x₁ hx₁
  refine Submodule.iSup_induction _ (motive := fun x => (ASVA L).Y s j x ∈ shiftTarget _ _ i) hx₁
    ?_ (by simp) (fun x y hx hy => by
      beta_reduce at hx hy ⊢; rw [map_add]; exact Submodule.add_mem _ hx hy)
  intro q x₂ hx₂
  by_cases h : layerIndex q m = i
  swap
  · rw [iSup_neg h, Submodule.mem_bot] at hx₂
    rw [hx₂, map_zero]; exact Submodule.zero_mem _
  rw [iSup_pos h] at hx₂
  subst h
  obtain ⟨xW, hxW, rfl⟩ := Submodule.mem_map.mp hx₂
  have hxp : (xW : (ASpace L)) ∈ (affineFlag L).piece q m := hxW.1
  have hmode := affineFlag_modeCompatible L (k := -j - 1) hs hxp
  have hY : (ASVA L).Y s j xW = (AVOA L).smul s (-j - 1) xW := by
    rw [PreVertexAlgebra.smul_def, mode_apply, show -(-j - 1) - 1 = j by ring]; rfl
  change (ASVA L).Y s j (xW : (ASpace L)) ∈ _
  rw [hY]
  have hl := piece_le_layers (affineForm L) (affineFlag L) (simpleForm_isSymmetric L.kA
      L.aNoncritical)
    (fun m => (hA m).1) (1 + q) _ hmode
  refine (iSup_le fun q' => iSup_le fun hq' => ?_ :
    (⨆ (q' : ℕ) (_ : q' ≤ 1 + q), (aDeg L) (layerIndex q' (w + m - (-j - 1) - 1))) ≤ _) hl
  intro z hz
  refine mem_shiftTarget (δ := ((2 * ((q' : ℤ) - q), 0),
    (((w + m - (-j - 1) - 1 : ℤ) : ℂ) - (m : ℂ)))) ⟨rfl, show 2 * ((q' : ℤ) - q) ≤ 2 by omega⟩ ?_
  have e : layerIndex q m + ((2 * ((q' : ℤ) - q), 0),
      (((w + m - (-j - 1) - 1 : ℤ) : ℂ) - (m : ℂ))) = layerIndex q' (w + m - (-j - 1) - 1) := by
    simp only [layerIndex, Prod.mk_add_mk, add_zero]
    congr 2 <;> ring
  rw [e]; exact hz

/-- The span of `s_A ⊗ s_B` with `s_A` of corrected degree at most one. -/
def G1 : Submodule ℂ ((ASpace L) ⊗[ℂ] BSpace) :=
  Submodule.span ℂ {z | ∃ (sA : (ASpace L)) (sB : BSpace) (w : ℤ),
    sA ∈ (affineFlag L).piece 1 w ∧ z = sA ⊗ₜ[ℂ] sB}

/-- The `j`-th coefficient of the `A ⊗ B` state-field map, as a linear map. -/
def abYCoeff (j : ℤ) : ((ASpace L) ⊗[ℂ] BSpace) →ₗ[ℂ] Module.End ℂ ((ASpace L) ⊗[ℂ] BSpace) :=
  (LinearMap.proj j : (ℤ → Module.End ℂ ((ASpace L) ⊗[ℂ] BSpace)) →ₗ[ℂ] _) ∘ₗ (abSVA L).Y

theorem abYCoeff_apply (j : ℤ) (z : (ASpace L) ⊗[ℂ] BSpace) : (abYCoeff L) j z = (abSVA L).Y z j :=
    rfl

/-- **Coefficients of `G1 L` states raise the interpreted `A ⊗ B` degree by at most two.** -/
theorem G1_shifts (hA : GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag L))
    {s : (ASpace L) ⊗[ℂ] BSpace} (hs : s ∈ (G1 L)) (j : ℤ) :
    ShiftsInto (tensorDeg (aDeg L) bDeg) ((abSVA L).Y s j) UpTwo := by
  rw [G1] at hs
  rw [← abYCoeff_apply]
  induction hs using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨sA, sB, w, hsA, rfl⟩ := hz
      intro i x hx
      refine tensorDeg_induction (aDeg L) bDeg i
        (fun x => (abYCoeff L) j (sA ⊗ₜ[ℂ] sB) x ∈ shiftTarget (tensorDeg (aDeg L) bDeg) UpTwo i)
        (by simp) (fun x y hx hy => by simpa only [map_add] using Submodule.add_mem _ hx hy)
        (fun c x hx => by simpa only [map_smul] using Submodule.smul_mem _ c hx) ?_ x hx
      intro b a ha y hy
      rw [abYCoeff_apply]
      change TensorVA.tenY (ASVA L) BSVA (sA ⊗ₜ[ℂ] sB) j (a ⊗ₜ[ℂ] y) ∈ _
      rw [TensorVA.tenY_tmul_parity (ASVA L) BSVA sA (bSpace_even sB), TensorVA.kappaTen_zero,
        LinearMap.id_apply, TensorVA.rawCoeff_tmul]
      refine finsum_induction (fun u => u ∈ shiftTarget (tensorDeg (aDeg L) bDeg) UpTwo i)
        (Submodule.zero_mem _) (fun _ _ h1 h2 => Submodule.add_mem _ h1 h2) (fun m => ?_)
      have h := tmul_mem_tensor_shiftTarget (aDeg L) bDeg ((aY_shifts L) hA hsA m b a ha)
        (bY_shifts sB (j - m) (i - b) y hy)
      rw [add_sub_cancel] at h
      exact shiftTarget_mono (fun δ hδ => upTwo_add hδ) i h
  | zero => rw [map_zero]; exact ShiftsInto.zero _ _
  | add x y _ _ hx hy => rw [map_add]; exact hx.add hy
  | smul c x _ hx => rw [map_smul]; exact hx.smul c

theorem aVacuum_mem_piece_one : (ASVA L).vacuum ∈ (affineFlag L).piece 1 0 := by
  have h : (ASVA L).vacuum ∈ (affineFlag L).piece 0 0 := by
    rw [(affineFlag L).vacuum_zero]; exact Submodule.mem_span_singleton_self _
  exact (affineFlag L).mono 0 (Nat.zero_le 1) h

theorem aCurrent_mem_piece_one (c : Fin 3) : (aAction L).current c ∈ (affineFlag L).piece 1 1 :=
  (affineCurrent_mem_flag_one L) c

theorem tmul_mem_G1 {sA : (ASpace L)} {w : ℤ} (h : sA ∈ (affineFlag L).piece 1 w) (sB : BSpace) :
    sA ⊗ₜ[ℂ] sB ∈ (G1 L) :=
  Submodule.subset_span ⟨sA, sB, w, h, rfl⟩

/-- The non-Casimir part of one diagonal bilinear lies in `G1 L`. -/
theorem diag_bilinear_sub_mem_G1 (b c : Fin 3) :
    mode ((abSVA L).Y ((diagonalAction L).current b)) (-1) ((diagonalAction L).current c) -
      mode ((ASVA L).Y ((aAction L).current b)) (-1) ((aAction L).current c) ⊗ₜ[ℂ] BSVA.vacuum ∈
          (G1 L) := by
  change mode (TensorVA.tenY (ASVA L) BSVA (tensorCurrentState (aAction L).toAffineSl2Action
      bAction.toAffineSl2Action b)) (-1) (tensorCurrentState (aAction L).toAffineSl2Action
      bAction.toAffineSl2Action c) - _ ∈ (G1 L)
  rw [show tensorCurrentState (aAction L).toAffineSl2Action bAction.toAffineSl2Action c =
    (aAction L).current c ⊗ₜ[ℂ] BSVA.vacuum + (ASVA L).vacuum ⊗ₜ[ℂ] bAction.current c from rfl,
    map_add, tensorCurrentMode_tmul, tensorCurrentMode_tmul]
  have hvA : mode ((ASVA L).Y ((aAction L).current b)) (-1) (ASVA L).vacuum = (aAction L).current
      b :=
    ((ASVA L).creation _).1
  have hvB : mode (BSVA.Y (bAction.current b)) (-1) BSVA.vacuum = bAction.current b :=
    (BSVA.creation _).1
  rw [hvA, hvB, add_sub_right_comm, add_sub_cancel_left]
  refine Submodule.add_mem _ ((tmul_mem_G1 L) ((aCurrent_mem_piece_one L) c) _)
    (Submodule.add_mem _ ((tmul_mem_G1 L) ((aCurrent_mem_piece_one L) b) _)
      ((tmul_mem_G1 L) (aVacuum_mem_piece_one L) _))

theorem aQuadratic_eq :
    quadraticState (aAction L).toAffineSl2Action = ((2 : ℂ) * (L.kAct + 2)) • (AVOA
        L).conformalVector := by
  rw [← aAction_sugawara, sugawaraState, smul_smul, mul_inv_cancel₀ (mul_ne_zero two_ne_zero
      (kAct_noncritical L)), one_smul]

/-- **The coset conformal vector has corrected degree at most one.** -/
theorem cosetOmega_mem_G1 : (cosetOmega L) ∈ (G1 L) := by
  have hamb : (ambientConformal L) ∈ (G1 L) :=
    Submodule.add_mem _ ((tmul_mem_G1 L) (affineConformal_mem_flag_one L) _)
      ((tmul_mem_G1 L) (aVacuum_mem_piece_one L) _)
  have hquad : quadraticState (diagonalAction L).toAffineSl2Action -
      quadraticState (aAction L).toAffineSl2Action ⊗ₜ[ℂ] BSVA.vacuum ∈ (G1 L) := by
    have e : quadraticState (diagonalAction L).toAffineSl2Action -
        quadraticState (aAction L).toAffineSl2Action ⊗ₜ[ℂ] BSVA.vacuum =
        ∑ b : Fin 3, ∑ c : Fin 3, AffineVOA.kappaInv b c •
          (mode ((abSVA L).Y ((diagonalAction L).current b)) (-1) ((diagonalAction L).current c) -
            mode ((ASVA L).Y ((aAction L).current b)) (-1) ((aAction L).current c) ⊗ₜ[ℂ]
                BSVA.vacuum) := by
      simp only [quadraticState, TensorProduct.sum_tmul, ← TensorProduct.smul_tmul',
        smul_sub, Finset.sum_sub_distrib]
    rw [e]
    exact Submodule.sum_mem _ fun b _ => Submodule.sum_mem _ fun c _ =>
      Submodule.smul_mem _ _ ((diag_bilinear_sub_mem_G1 L) b c)
  have hA2 : quadraticState (aAction L).toAffineSl2Action ⊗ₜ[ℂ] BSVA.vacuum ∈ (G1 L) := by
    rw [aQuadratic_eq, ← TensorProduct.smul_tmul']
    exact Submodule.smul_mem _ _ ((tmul_mem_G1 L) (affineConformal_mem_flag_one L) _)
  have hdiag : (diagonalSugawara L) ∈ (G1 L) := by
    unfold diagonalSugawara sugawaraState
    refine Submodule.smul_mem _ _ ?_
    have := Submodule.add_mem _ hquad hA2
    rwa [sub_add_cancel] at this
  exact Submodule.sub_mem _ hamb hdiag

/-- The BRST image of the coset conformal vector. -/
abbrev omegaB : (BRSTSpace L) := (cosetToComplex L) (cosetOmegaState L)

/-- Coefficients of `ω_C` act on the matter factor `A ⊗ B` only. -/
theorem omegaB_Y_eq (j : ℤ) :
    (brstSVA L).Y (omegaB L) j = TensorProduct.map
      (TensorProduct.map ((abSVA L).Y (cosetOmega L) j) LinearMap.id) LinearMap.id := by
  apply TensorProduct.ext'
  intro m g
  change TensorVA.tenY (matterSVA L) sl2GhostSVA
    (((cosetOmega L) ⊗ₜ[ℂ] (USVA L).vacuum) ⊗ₜ[ℂ] sl2GhostSVA.vacuum) j (m ⊗ₜ[ℂ] g) = _
  rw [tenY_left_unit (matterSVA L) sl2GhostSVA, TensorProduct.map_tmul, LinearMap.id_apply]
  congr 1
  induction m using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul x u =>
      change TensorVA.tenY (abSVA L) (USVA L) ((cosetOmega L) ⊗ₜ[ℂ] (USVA L).vacuum) j (x ⊗ₜ[ℂ] u)
          = _
      rw [tenY_left_unit (abSVA L) (USVA L), TensorProduct.map_tmul, LinearMap.id_apply]

/-- **Every coefficient of `ω_C` raises the interpreted `2R` by at most two.** -/
theorem omegaB_shifts (hA : GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag L))
    (w : Finset ModeIdx → ℝ) (j : ℤ) :
    ShiftsInto ((brstDeg L) (ghostRGrading w)) ((brstSVA L).Y (omegaB L) j) UpTwo := by
  rw [omegaB_Y_eq]
  have h1 := (G1_shifts L) hA (cosetOmega_mem_G1 L) j
  have h2 := tensorDeg_map_shiftTarget (tensorDeg (aDeg L) bDeg) (uDeg L) h1 (shiftsInto_id (uDeg
      L))
  have h3 := tensorDeg_map_shiftTarget (matterDeg L) (ghostRGrading w).deg
    (h2.mono fun _ h => addPred_zero_right h) (shiftsInto_id _)
  exact h3.mono fun _ h => addPred_zero_right h

/-! ### Interpreted pieces with negative `2R` vanish -/

theorem brstDeg_nonnegR (w : Finset ModeIdx → ℝ) : NonnegR ((brstDeg L) (ghostRGrading w)) :=
  tensorDeg_nonnegR (tensorDeg_nonnegR (tensorDeg_nonnegR (layerDeg_nonnegR _ _)
    (trivialDeg_nonnegR _)) (layerDeg_nonnegR _ _))
    (tensorDeg_nonnegR (tensorDeg_nonnegR fockDeg_nonnegR fockDeg_nonnegR) fockDeg_nonnegR)

theorem omegaB_relative : (omegaB L) ∈ relativeCarrier (matterAction L).toAffineSl2Action :=
  (cosetToComplex_relative L) _

theorem omegaB_weight : (omegaB L) ∈ (brstSVA L).grading ((2 : ℤ) : ℂ) :=
  (cosetToComplex_mem_weight L) 2 _ (cosetOmegaState_weight L)

theorem omegaB_even : (omegaB L) ∈ (brstSVA L).parity 0 := by
  change ((cosetOmega L) ⊗ₜ[ℂ] (USVA L).vacuum) ⊗ₜ[ℂ] sl2GhostSVA.vacuum ∈
    TensorVA.tenParity (matterSVA L) sl2GhostSVA 0
  refine TensorVA.tmul_mem_tenParity (matterSVA L) sl2GhostSVA (p₁ := 0) ?_ ?_
  · exact TensorVA.tmul_mem_tenParity (abSVA L) (USVA L) (p₁ := 0) (cosetOmega_even L)
      (by simpa using (USVA L).vacuum_parity)
  · simpa using sl2GhostSVA.vacuum_parity

/-- `Q` commutes with every mode of `ω_C`. -/
theorem Q_omegaB_mode (m : ℤ) (v : (BRSTSpace L)) :
    semiInfiniteQ (matterAction L).toAffineSl2Action (mode ((brstSVA L).Y (omegaB L)) m v) =
      mode ((brstSVA L).Y (omegaB L)) m (semiInfiniteQ (matterAction L).toAffineSl2Action v) := by
  have h := semiInfiniteQ_deriv_of_translation (matterAction L) (matterParityCompatible L)
    (matterGhostTensorGrading L) (omegaB L) v m
  change semiInfiniteQ (matterAction L).toAffineSl2Action (mode ((brstSVA L).Y (omegaB L)) m v) =
    mode ((brstSVA L).Y (semiInfiniteQ (matterAction L).toAffineSl2Action (omegaB L))) m v +
      mode ((brstSVA L).Y (BRST.sgn (brstSVA L) (omegaB L))) m
        (semiInfiniteQ (matterAction L).toAffineSl2Action v) at h
  have hQ : semiInfiniteQ (matterAction L).toAffineSl2Action (omegaB L) = 0 :=
    (cosetToComplex_closed L) (cosetOmegaState L)
  have hs : BRST.sgn (brstSVA L) (omegaB L) = (omegaB L) := by
    rw [BRST.sgn_homog (omegaB_even L), parSign_zero, one_smul]
  have h0 : mode ((brstSVA L).Y (0 : (BRSTSpace L))) m v = 0 := by
    rw [map_zero]; rfl
  rw [hQ, hs, h0] at h
  exact h.trans (zero_add _)

theorem omegaB_mode_relative (m : ℤ) {v : (BRSTSpace L)}
    (hv : v ∈ relativeCarrier (matterAction L).toAffineSl2Action) :
    mode ((brstSVA L).Y (omegaB L)) m v ∈ relativeCarrier (matterAction L).toAffineSl2Action :=
  relativeCarrier_mode (matterAction L).toAffineSl2Action (matterAction L).translation
    (matterParityCompatible L) (matterGhostTensorGrading L) (omegaB_relative L) hv m

/-- The creation operator `L_{-i-2}` of the coset, on relative weight spaces. -/
def creationOp (n : ℤ) (i : ℕ) : (relativeWeight L) n →ₗ[ℂ] (relativeWeight L) (n + i + 2) :=
  (mode ((brstSVA L).Y (omegaB L)) (-(i : ℤ) - 1)).restrict (fun v hv => by
    refine ⟨(omegaB_mode_relative L) _ hv.1, ?_⟩
    have h := (brstSVA L).grading_mode (omegaB L) (omegaB_weight L) v hv.2 (-(i : ℤ) - 1)
    show _ ∈ (brstSVA L).grading (((n + i + 2 : ℤ)) : ℂ)
    rw [show (((n + i + 2 : ℤ)) : ℂ) = ((2 : ℤ) : ℂ) + (n : ℂ) - ((-(i : ℤ) - 1 : ℤ) : ℂ) - 1 by
      push_cast; ring]
    exact h)

theorem creationOp_coe (n : ℤ) (i : ℕ) (v : (relativeWeight L) n) :
    ((creationOp L) n i v : (BRSTSpace L)) = mode ((brstSVA L).Y (omegaB L)) (-(i : ℤ) - 1) v := rfl

theorem creationOp_D (n : ℤ) (i : ℕ) (v : (relativeWeight L) n) :
    (relativeDifferential L) (n + i + 2) ((creationOp L) n i v) =
      (creationOp L) n i ((relativeDifferential L) n v) := by
  apply Subtype.ext
  simp only [relativeDifferential_coe, creationOp_coe]
  have h := (Q_omegaB_mode L) (-(i : ℤ) - 1) (v : (BRSTSpace L))
  rw [← brstComplex_Q] at h
  exact h

/-- The representative of a Virasoro creation is the coset creation of the representative. -/
theorem representative_creation (n : ℤ) (i : ℕ) (x : (UniversalWeight L) n) :
    (universalWeightRepresentative L) (n + i + 2) ((universalCreation L) n i x) =
      (creationOp L) n i ((universalWeightRepresentative L) n x) := by
  apply Subtype.ext
  rw [creationOp_coe]
  change (cosetToComplex L) ((virasoroToCoset L) (Lop L.c (-(i : ℤ) - 2) x)) =
    mode ((brstSVA L).Y (omegaB L)) (-(i : ℤ) - 1) ((cosetToComplex L) ((virasoroToCoset L) x))
  rw [show (virasoroToCoset L) (Lop L.c (-(i : ℤ) - 2) x) =
    (cosetVOA L).L (-(i : ℤ) - 2) ((virasoroToCoset L) x) from conformalEval_L (cosetVOA L) rfl _ _]
  rw [VertexOperatorAlgebra.L_def, show -(i : ℤ) - 2 + 1 = -(i : ℤ) - 1 by ring,
    ← PreVertexAlgebra.smul_def, cosetVOA_mode, cosetToComplex_mode]
  rfl

section Creation

variable (w : Finset ModeIdx → ℝ) (hw : ∀ s, 0 < w s)
  (hA : GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag L))
  {BB : InvariantForm BVOA} {RB : RealStructure BVOA} (hB : ConcreteHodge.Unitary BB RB)

theorem creation_shift (hA : GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag L))
    (p : ℕ) (j : ℤ) {v : (BRSTSpace L)}
    (hv : v ∈ ⨆ (k : (ℤ × ℤ) × ℂ) (_ : RowPred p k), (brstDeg L) (ghostRGrading w) k) :
    (brstSVA L).Y (omegaB L) j v ∈
      ⨆ (k : (ℤ × ℤ) × ℂ) (_ : RowPred (p + 1) k), (brstDeg L) (ghostRGrading w) k := by
  refine Submodule.iSup_induction _ (motive := fun v => (brstSVA L).Y (omegaB L) j v ∈
      ⨆ (k : (ℤ × ℤ) × ℂ) (_ : RowPred (p + 1) k), (brstDeg L) (ghostRGrading w) k)
    hv ?_ (by simp) (fun x y hx hy => by
      beta_reduce at hx hy ⊢; rw [map_add]; exact Submodule.add_mem _ hx hy)
  intro k y hy
  refine Submodule.iSup_induction _ (motive := fun v => (brstSVA L).Y (omegaB L) j v ∈
      ⨆ (k : (ℤ × ℤ) × ℂ) (_ : RowPred (p + 1) k), (brstDeg L) (ghostRGrading w) k)
    hy ?_ (by simp) (fun x y hx hy => by
      beta_reduce at hx hy ⊢; rw [map_add]; exact Submodule.add_mem _ hx hy)
  intro hk y hy
  have h := (omegaB_shifts L) hA w j k y hy
  refine (iSup_le fun δ => iSup_le fun hδ => ?_ :
    shiftTarget ((brstDeg L) (ghostRGrading w)) UpTwo k ≤ _) h
  refine le_iSup_of_le (k + δ) (le_iSup_of_le ⟨?_, ?_⟩ le_rfl)
  · simp only [Prod.fst_add]; push_cast; have := hk.1; have := hδ.2; omega
  · simp only [Prod.fst_add, Prod.snd_add, hk.2, hδ.1, add_zero]

end Creation


end

end VOA.TwoSeries
