/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.BRSTGoodnessFine
import VOA.Examples.BRSTGoodnessMatter

/-!
# Goodness of the actual BRST differential on relative states

`relativeDifferentialGood_of_affine`: **`RelativeDifferentialGood (ghostRGrading w)` holds**,
given `hA` and the unitarity of `B` (both already inputs of the endpoint), for every positive
ghost weight function `w`.

The argument:

1. **Fine grading of the BRST space** `brstDegF = matterF ⊗ ghostDegF`, indexed by
   `((2R, gh), weight)` and the number of `c₀`'s. It refines `brstDeg` (`brstDeg_le_coarsenF`,
   `brstDegF_le_brstDeg`) and is internal (`brstDegF_isInternal`, by positivity).
2. **`R'`-goodness of `Q` on the whole space** (`semiInfiniteQ_shifts`): with `R' = R + n_{c₀}/2`
   every term of `Q = Σ_a Σ_n J^a_n ⊗ c^a_{-n} + Q_gh` shifts `2R'` by exactly `±1`. The matter
   modes are good by `matterMode_shifts` (Li-goodness plus adjointness of the actual flags), the
   `c`-modes shift `2R'` by the sign of their index (`c₀` included), and the cubic charge is
   `cubicCharge_shifts`.
3. **Relative states have no `c₀`** (`relative_c0free`): `Σ_a c₀ᵃ b₀ᵃ` acts on the fine piece
   `k` as `k.2` and kills every state annihilated by the antighost zero modes.
4. On `c₀`-free states `R' = R`; `Q` preserves relative states; so on relative states `Q` shifts
   `2R` by exactly `±1`.

Everything is proved outright from `hA` and `hB`.
-/

namespace VOA.ConcreteHodge

open Sl2CosetConcrete Sl2SemiInfinite AffineSl2GeneralRigidity AffineSl2BelowCritical
open VOA.GradedUnitaryCohomology VOA.LeeYangCosetTransfer VOA.VertexOperatorAlgebra
open VOA.LeeYangTransferAssembly VOA.SympFerm VOA.Ghost
open scoped TensorProduct

noncomputable section

/-! ### The fine BRST grading -/

/-- The matter grading, placed at `c₀`-number `0`. -/
def matterF (k : KF) : Submodule ℂ MatterSpace := if k.2 = 0 then matterDeg k.1 else ⊥

theorem matterF_le (k : KF) : matterF k ≤ matterDeg (fstF k) := by
  unfold matterF; split_ifs <;> simp

theorem matterDeg_le_matterF (i : (ℤ × ℤ) × ℂ) : matterDeg i ≤ matterF (i, 0) := by
  simp [matterF]

theorem matterDeg_le_coarsen (i : (ℤ × ℤ) × ℂ) :
    matterDeg i ≤ ⨆ (k : KF) (_ : fstF k = i), matterF k :=
  le_trans (matterDeg_le_matterF i) (le_iSup_of_le (i, 0) (le_iSup_of_le rfl le_rfl))

/-- **The fine BRST grading.** -/
def brstDegF : KF → Submodule ℂ BRSTSpace := tensorDeg matterF ghostDegF

theorem brstDegF_le_brstDeg (w : Finset ModeIdx → ℝ) (k : KF) :
    brstDegF k ≤ brstDeg (ghostRGrading w) (fstF k) :=
  tensorDeg_le fstF _ _ _ _ _ (fun _ _ _ _ hx hy => tmul_mem_tensorDeg _ _ hx hy)
    matterF_le ghostDegF_le_ghostDeg k

theorem brstDeg_le_coarsenF (w : Finset ModeIdx → ℝ) (i : (ℤ × ℤ) × ℂ) :
    brstDeg (ghostRGrading w) i ≤ ⨆ (k : KF) (_ : fstF k = i), brstDegF k :=
  tensorDeg_le_coarsen fstF _ _ _ _ matterDeg_le_coarsen ghostDeg_le_coarsen i

section Internal

variable {BB : InvariantForm BVOA} {RB : RealStructure BVOA}

theorem matterDeg_orth' (hA : GradedUnitary affineForm affineRealStructure affineFlag) :
    ∀ a b, a ≠ b → ∀ x ∈ matterDeg a, ∀ y ∈ matterDeg b,
      (((carrierForm affineForm affineRealStructure affineFlag hA affineGramRefl).tensor
        (unitaryCarrierForm BB RB)).tensor
        (carrierForm auxiliaryForm auxiliaryRealStructure auxiliaryFlag auxiliaryGradedUnitary
          auxiliaryGramRefl)) x y = 0 :=
  tensorDeg_orth _ _ _ _
    (tensorDeg_orth _ _ _ _
      (layerDeg_orth affineForm affineRealStructure affineFlag hA affineGramRefl)
      (trivialDeg_orth _ (unitaryCarrierForm_weight_orth BB RB)))
    (layerDeg_orth _ _ _ auxiliaryGradedUnitary auxiliaryGramRefl)

theorem matterF_orth (hA : GradedUnitary affineForm affineRealStructure affineFlag) :
    ∀ a b, a ≠ b → ∀ x ∈ matterF a, ∀ y ∈ matterF b,
      (((carrierForm affineForm affineRealStructure affineFlag hA affineGramRefl).tensor
        (unitaryCarrierForm BB RB)).tensor
        (carrierForm auxiliaryForm auxiliaryRealStructure auxiliaryFlag auxiliaryGradedUnitary
          auxiliaryGramRefl)) x y = 0 := by
  intro a b hab x hx y hy
  unfold matterF at hx hy
  split_ifs at hx hy with ha hb
  · have : a.1 ≠ b.1 := fun h => hab (Prod.ext h (ha.trans hb.symm))
    exact matterDeg_orth' hA a.1 b.1 this x hx y hy
  · rw [Submodule.mem_bot] at hy; rw [hy, SesqForm.zero_right]
  · rw [Submodule.mem_bot] at hx; rw [hx, SesqForm.zero_left]
  · rw [Submodule.mem_bot] at hx; rw [hx, SesqForm.zero_left]

theorem matterF_span (hA : GradedUnitary affineForm affineRealStructure affineFlag) :
    iSup matterF = ⊤ := by
  rw [eq_top_iff, ← matterDeg_span hA]
  exact iSup_le fun i => (matterDeg_le_matterF i).trans (le_iSup _ _)

theorem brstDegF_orth (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    (w : Finset ModeIdx → ℝ) :
    ∀ a b, a ≠ b → ∀ x ∈ brstDegF a, ∀ y ∈ brstDegF b,
      matterGhostForm hA BB RB (ghostForm w) x y = 0 :=
  tensorDeg_orth _ _ _ _ (matterF_orth hA) (ghostDegF_orth w)

theorem brstDegF_isInternal (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    (hB : Unitary BB RB) (w : Finset ModeIdx → ℝ) (hw : ∀ s, 0 < w s) :
    DirectSum.IsInternal brstDegF := by
  classical
  have hpos := weakGU_matterGhostForm hA hB (ghostForm_pos w hw)
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top _
    (tensorDeg_span _ _ (matterF_span hA) ghostDegF_span)
  rw [iSupIndep_def]
  intro a
  rw [Submodule.disjoint_def]
  intro x hx hx'
  apply eq_zero_of_sesq_self_eq_zero _ hpos
  refine sesq_iSup_right' _ (fun b => ⨆ (_ : b ≠ a), brstDegF b) (fun b y hy => ?_) x hx'
  by_cases hba : b = a
  · subst hba
    simp only [ne_eq, not_true_eq_false, iSup_false, Submodule.mem_bot] at hy
    rw [hy, SesqForm.zero_right]
  · beta_reduce at hy
    rw [iSup_pos (show b ≠ a from hba)] at hy
    exact brstDegF_orth hA w a b (Ne.symm hba) x hx y hy

end Internal

/-! ### Goodness of `Q` for `R'` on the whole space -/

/-- The matter shifts, placed at `c₀`-number `0`. -/
def matterPredF (n : ℤ) (δ : KF) : Prop := δ.2 = 0 ∧ modePred n δ.1

theorem matterMode_shiftsF (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    (a : Fin 3) (n : ℤ) :
    ShiftsInto matterF
      (mode (matterSVA.Y (leeYangMatterAction.toAffineSl2Action.current a)) n)
      (matterPredF n) := by
  intro k x hx
  unfold matterF at hx
  split_ifs at hx with hk
  · have h := matterMode_shifts hA a n k.1 x hx
    refine (iSup_le fun δ => iSup_le fun hδ => ?_ : shiftTarget matterDeg (modePred n) k.1 ≤ _) h
    intro y hy
    refine mem_shiftTarget (δ := (δ, 0)) ⟨rfl, hδ⟩ ?_
    simp only [matterF, Prod.snd_add, hk, add_zero, if_true, Prod.fst_add]
    exact hy
  · rw [Submodule.mem_bot] at hx
    rw [hx, map_zero]; exact Submodule.zero_mem _

theorem eN_cases (n : ℤ) :
    (0 < n ∧ eN n = 0 ∧ eN (-n) = 1) ∨ (n = 0 ∧ eN n = 0 ∧ eN (-n) = 0) ∨
      (n < 0 ∧ eN n = 1 ∧ eN (-n) = 0) := by
  unfold eN
  rcases lt_trichotomy n 0 with h | h | h
  · right; right; exact ⟨h, by rw [if_neg (by omega)], by rw [if_pos (by omega)]⟩
  · right; left; subst h; simp
  · left; exact ⟨h, by rw [if_pos (by omega)], by rw [if_neg (by omega)]⟩

theorem piRp_eq_fst {δ : KF} (h : δ.2 = 0) : piRp δ = fstF δ := by
  obtain ⟨⟨⟨r, g⟩, wt⟩, c⟩ := δ
  simp only at h
  subst h
  simp

theorem wt_cancel (n : ℤ) : ((-n : ℤ) : ℂ) + ((n : ℂ) + ((ghWt 1 : ℕ) : ℂ)) = 0 := by
  simp [ghWt]

theorem current_term_good (n : ℤ) :
    ∀ δ, addPred (matterPredF n) (· = ghShiftF 1 n) δ → GoodRp δ := by
  rintro δ ⟨a₁, a₂, ⟨h0, d, hd, hlo, hhi⟩, rfl, rfl⟩
  have hpa : piRp a₁ = a₁.1 := by rw [piRp_eq_fst h0]; rfl
  unfold GoodRp
  rw [map_add, piRp_ghShiftF, hpa, hd]
  simp only [Prod.mk_add_mk, Prod.mk.injEq]
  have hgh : (0 : ℤ) + ghCharge 1 = 1 := by simp [ghCharge]
  rcases eN_cases n with ⟨hn, h1, h2⟩ | ⟨hn, h1, h2⟩ | ⟨hn, h1, h2⟩
  · rw [h1] at hhi; rw [h2] at hlo
    push_cast at hlo hhi
    rw [if_pos hn.le]
    rcases (by omega : d = 0 ∨ d = -1) with rfl | rfl
    · left; exact ⟨⟨by norm_num, hgh⟩, wt_cancel n⟩
    · right; exact ⟨⟨by norm_num, hgh⟩, wt_cancel n⟩
  · rw [h1] at hhi; rw [h2] at hlo
    push_cast at hlo hhi
    rw [if_pos (by omega)]
    rcases (by omega : d = 0) with rfl
    left; exact ⟨⟨by norm_num, hgh⟩, wt_cancel n⟩
  · rw [h1] at hhi; rw [h2] at hlo
    push_cast at hlo hhi
    rw [if_neg (by omega)]
    rcases (by omega : d = 0 ∨ d = 1) with rfl | rfl
    · right; exact ⟨⟨by norm_num, hgh⟩, wt_cancel n⟩
    · left; exact ⟨⟨by norm_num, hgh⟩, wt_cancel n⟩

theorem matter_even_invol (x : MatterSpace) : (TensorVA.parGr matterSVA).parityInvol x = x :=
  (TensorVA.parGr matterSVA).parityInvol_even (matter_mem_parity_zero x)

/-- **`Q` shifts `2R'` by exactly `±1` on the whole BRST space.** -/
theorem semiInfiniteQ_shifts (hA : GradedUnitary affineForm affineRealStructure affineFlag) :
    ShiftsInto brstDegF (semiInfiniteQ leeYangMatterAction.toAffineSl2Action) GoodRp := by
  intro k z hz
  refine tensorDeg_induction matterF ghostDegF k
    (fun z => semiInfiniteQ leeYangMatterAction.toAffineSl2Action z ∈
      shiftTarget brstDegF GoodRp k)
    (by simp) (fun x y hx hy => by simpa only [map_add] using Submodule.add_mem _ hx hy)
    (fun c x hx => by simpa only [map_smul] using Submodule.smul_mem _ c hx) ?_ z hz
  intro b x hx y hy
  rw [semiInfiniteQ_tmul, matter_even_invol]
  have hk : b + (k - b) = k := by abel
  refine Submodule.add_mem _ (Submodule.sum_mem _ fun a _ => ?_) ?_
  · refine finsum_induction (fun u => u ∈ shiftTarget brstDegF GoodRp k)
      (Submodule.zero_mem _) (fun _ _ h1 h2 => Submodule.add_mem _ h1 h2) (fun n => ?_)
    have hJ := matterMode_shiftsF hA a n b x hx
    have hc : mode (sl2GhostSVA.Y (cGhost a)) (-n - 1) y ∈
        shiftTarget ghostDegF (· = ghShiftF 1 n) (k - b) := by
      have h := ghostYCoeff_shifts a 1 n (k - b) y hy
      simpa only [ghostGenerator_one, mode_apply, show -(-n - 1) - 1 = n by ring] using h
    have h := tmul_mem_tensor_shiftTarget matterF ghostDegF hJ hc
    rw [hk] at h
    exact shiftTarget_mono (current_term_good n) k h
  · have hx' : x ∈ shiftTarget matterF (· = 0) b := mem_shiftTarget rfl (by rwa [add_zero])
    have h := tmul_mem_tensor_shiftTarget matterF ghostDegF hx'
      (cubicCharge_shifts (k - b) y hy)
    rw [hk] at h
    exact shiftTarget_mono (fun δ hδ => addPred_zero_left hδ) k h

/-! ### Relative states have no `c₀` -/

/-- The `c₀`-number operator on the BRST space. -/
def Phi0 : Module.End ℂ BRSTSpace := TensorProduct.map LinearMap.id Nc0

theorem Phi0_eigen {k : KF} {z : BRSTSpace} (hz : z ∈ brstDegF k) :
    Phi0 z = ((k.2 : ℤ) : ℂ) • z := by
  refine tensorDeg_induction matterF ghostDegF k (fun z => Phi0 z = ((k.2 : ℤ) : ℂ) • z)
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
    antighostZero matterSVA a = TensorProduct.map LinearMap.id (gMode a 0 0) := by
  apply TensorProduct.ext'
  intro m g
  rw [antighostZero_tmul a (matter_mem_parity_zero m) g, TensorProduct.map_tmul,
    LinearMap.id_apply]
  simp [koszul, gMode]

theorem Phi0_of_antighost {z : BRSTSpace} (hz : ∀ a, antighostZero matterSVA a z = 0) :
    Phi0 z = 0 := by
  have h : ∀ z, Phi0 z = ∑ a : Fin 3, TensorProduct.map LinearMap.id (gMode a 1 (-1))
      (antighostZero matterSVA a z) := by
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
theorem relative_c0free (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    {BB : InvariantForm BVOA} {RB : RealStructure BVOA} (hB : Unitary BB RB)
    (w : Finset ModeIdx → ℝ) (hw : ∀ s, 0 < w s) {z : BRSTSpace}
    (hz : ∀ a, antighostZero matterSVA a z = 0) :
    z ∈ ⨆ (k : KF) (_ : k.2 = 0), brstDegF k := by
  classical
  have hI := brstDegF_isInternal hA hB w hw
  rw [mem_iSup_pred_iff hI]
  intro k hk
  have hpres : ∀ i, ∀ x ∈ brstDegF i, Phi0 x ∈ brstDegF i := fun i x hx => by
    rw [Phi0_eigen hx]; exact Submodule.smul_mem _ _ hx
  have hcomm := LinearMap.congr_fun (iproj_comm_of_preserves hI Phi0 hpres k) z
  simp only [LinearMap.coe_comp, Function.comp_apply, Phi0_of_antighost hz, map_zero] at hcomm
  rw [Phi0_eigen (iproj_mem hI k z)] at hcomm
  have hk' : ((k.2 : ℤ) : ℂ) ≠ 0 := by exact_mod_cast hk
  calc iproj hI k z = (((k.2 : ℤ) : ℂ))⁻¹ • ((((k.2 : ℤ) : ℂ)) • iproj hI k z) := by
        rw [smul_smul, inv_mul_cancel₀ hk', one_smul]
    _ = 0 := by rw [← hcomm, smul_zero]

/-! ### The relative goodness -/

/-- **`RelativeDifferentialGood` for the concrete ghost grading**, from `hA` and `hB`. -/
theorem relativeDifferentialGood_of_affine
    (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    {BB : InvariantForm BVOA} {RB : RealStructure BVOA} (hB : Unitary BB RB)
    (w : Finset ModeIdx → ℝ) (hw : ∀ s, 0 < w s) :
    RelativeDifferentialGood (ghostRGrading w) := by
  classical
  intro n j g x hxrel hx
  have hI := brstDegF_isInternal hA hB w hw
  set i : (ℤ × ℤ) × ℂ := ((j, g), (n : ℂ)) with hi
  -- `x` in fine form
  have hrel : ∀ a, antighostZero matterSVA a x = 0 := fun a =>
    ((mem_relativeCarrier _ x).mp hxrel.1).2 a
  have hx1 := brstDeg_le_coarsenF w i hx
  have hx2 := relative_c0free hA hB w hw hrel
  have hxF := mem_iSup_pred_inf hI hx1 hx2
  -- `Q x` in the image pieces
  set S : KF → Prop := fun k' => ∃ k δ, (fstF k = i ∧ k.2 = 0) ∧ GoodRp δ ∧ k' = k + δ
  have hQ1 : leeYangBRSTComplex.Q x ∈ ⨆ (k' : KF) (_ : S k'), brstDegF k' := by
    refine Submodule.iSup_induction _
      (motive := fun x => leeYangBRSTComplex.Q x ∈ ⨆ (k' : KF) (_ : S k'), brstDegF k')
      hxF ?_ (by simp) (fun x y hx hy => by
        beta_reduce at hx hy ⊢; rw [map_add]; exact Submodule.add_mem _ hx hy)
    intro k y hy
    refine Submodule.iSup_induction _
      (motive := fun y => leeYangBRSTComplex.Q y ∈ ⨆ (k' : KF) (_ : S k'), brstDegF k')
      hy ?_ (by simp) (fun x y hx hy => by
        beta_reduce at hx hy ⊢; rw [map_add]; exact Submodule.add_mem _ hx hy)
    intro hk y hy
    have h := semiInfiniteQ_shifts hA k y hy
    rw [← leeYangBRSTComplex_Q] at h
    refine (iSup_le fun δ => iSup_le fun hδ => ?_ :
      shiftTarget brstDegF GoodRp k ≤ _) h
    exact le_iSup_of_le (k + δ) (le_iSup_of_le ⟨k, δ, hk, hδ, rfl⟩ le_rfl)
  have hQrel : leeYangBRSTComplex.Q x ∈ relativeWeight n :=
    (relativeDifferential n ⟨x, hxrel⟩).2
  have hQ2 := relative_c0free hA hB w hw
    ((mem_relativeCarrier _ _).mp hQrel.1).2
  have hQF := mem_iSup_pred_inf hI hQ1 hQ2
  refine (iSup_le fun k' => iSup_le fun hk' => ?_ :
    (⨆ (k' : KF) (_ : S k' ∧ k'.2 = 0), brstDegF k') ≤ _) hQF
  obtain ⟨⟨k, δ, ⟨hk1, hk2⟩, hδ, rfl⟩, hk'2⟩ := hk'
  have hδ2 : δ.2 = 0 := by
    simp only [Prod.snd_add, hk2, zero_add] at hk'2; exact hk'2
  have hfst : fstF (k + δ) = i + piRp δ := by
    rw [map_add, hk1, piRp_eq_fst hδ2]
  refine (brstDegF_le_brstDeg w (k + δ)).trans ?_
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

end

end VOA.ConcreteHodge
