/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.KoszulResidualGhost

/-!
# The antighost-lowering block component of the actual `Q` is the native Koszul differential

For a vector `z` of a joint piece `blockB j` with no `c₀` and conformal weight `n₀ ≤ N`,

  `Q z = dN (sN N) z + (components in joint pieces whose (bidegree, antighost) index differs
  from that of `j + δT`, or with a negative number of `c₀`)`,

where `δT` is the shift `(2R, gh, q) ↦ (2R + 1, gh + 1, q - 1)` (`Q_sub_dN_mem`). Together with
`dN_mem_blockB` (`dN` maps `blockB j` into `blockB (j + δT)`) this identifies the actual block
component `d_K` with `dN`.

Everything is proved outright from `hA`.
-/

namespace VOA.KoszulResidual

open VOA.ConcreteHodge VOA.GradedUnitaryCohomology VOA.VertexOperatorAlgebra
open Sl2CosetConcrete Sl2SemiInfinite AffineSl2GeneralRigidity AffineSl2BelowCritical
open VOA.LeeYangTransferAssembly VOA.KoszulConcrete VOA.SympFerm VOA.Ghost
open scoped TensorProduct

noncomputable section

/-! ### Generic: projections determine vectors -/

section Generic

variable {ι : Type*} [DecidableEq ι] {E : Type*} [AddCommGroup E] [Module ℂ E]
  {L : ι → Submodule ℂ E}

theorem eq_of_iproj_eq (hI : DirectSum.IsInternal L) {a b : E}
    (h : ∀ j, iproj hI j a = iproj hI j b) : a = b := by
  rw [← sub_eq_zero]
  obtain ⟨s, hs⟩ := sum_iproj hI (a - b)
  rw [← hs]
  exact Finset.sum_eq_zero fun j _ => by rw [map_sub, h j, sub_self]

/-- A vector of a two-term sup minus its component along one term lies in the other term. -/
theorem sub_iproj_mem_of_two [AddCommGroup ι] (hI : DirectSum.IsInternal L) {P : ι → Prop}
    {i e e0 : ι} (hP : ∀ δ, P δ → δ = e ∨ δ = e0) (hne : e ≠ e0) {y : E}
    (hy : y ∈ ⨆ (δ : ι) (_ : P δ), L (i + δ)) :
    y - iproj hI (i + e) y ∈ L (i + e0) := by
  have hy' : y ∈ ⨆ (j : ι) (_ : j = i + e ∨ j = i + e0), L j := by
    have hle : (⨆ (δ : ι) (_ : P δ), L (i + δ)) ≤ ⨆ (j : ι) (_ : j = i + e ∨ j = i + e0), L j :=
      iSup_le fun δ => iSup_le fun hδ => le_iSup_of_le (i + δ) (le_iSup_of_le (by
        rcases hP δ hδ with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl) le_rfl)
    exact hle hy
  have key : y - iproj hI (i + e) y = iproj hI (i + e0) y := by
    refine eq_of_iproj_eq hI fun j => ?_
    rw [map_sub]
    by_cases hj : j = i + e
    · subst hj
      rw [iproj_of_mem_same hI (iproj_mem hI _ _), sub_self]
      exact (iproj_of_mem_ne hI (fun h => hne (add_left_cancel h).symm) (iproj_mem hI _ _)).symm
    · rw [iproj_of_mem_ne hI (fun h => hj h.symm) (iproj_mem hI _ _), sub_zero]
      by_cases hj0 : j = i + e0
      · subst hj0; rw [iproj_of_mem_same hI (iproj_mem hI _ _)]
      · rw [iproj_of_mem_ne hI (fun h => hj0 h.symm) (iproj_mem hI _ _)]
        exact iproj_eq_zero_of_mem_iSup hI _ hy' (by tauto)
  rw [key]; exact iproj_mem hI _ _

end Generic

/-! ### The matter-level components of a creation mode -/

section MatterComp

variable (hA : GradedUnitary affineForm affineRealStructure affineFlag)

/-- The `R`-preserving shift of a creation mode. -/
abbrev e0q (q : LexLetter) : (ℤ × ℤ) × ℂ := ((0, 0), ((letterWt q : ℕ) : ℂ))

theorem eq_ne_e0q (q : LexLetter) : eq q ≠ e0q q := by
  intro h; have := congrArg (fun x : (ℤ × ℤ) × ℂ => x.1.1) h; simp at this

theorem modePred_nq_cases (q : LexLetter) :
    ∀ δ, modePred (nq q) δ → δ = eq q ∨ δ = e0q q := by
  intro δ h
  obtain ⟨d, rfl, h0, h1⟩ := modePred_nq h
  rcases (show d = 1 ∨ d = 0 by omega) with rfl | rfl
  · left; simp
  · right; simp

theorem aMode_sub_aLead_mem (q : LexLetter) {i : (ℤ × ℤ) × ℂ} {x : ASpace} (hx : x ∈ aDeg i) :
    aMode (ofLex q).1 (nq q) x - aLead hA q x ∈ aDeg (i + e0q q) := by
  rw [aLead_of_mem hA q hx]
  exact sub_iproj_mem_of_two (aDeg_isInternal hA) (modePred_nq_cases q) (eq_ne_e0q q)
    (aMode_shifts hA _ _ i x hx)

theorem uMode_sub_uLead_mem (q : LexLetter) {i : (ℤ × ℤ) × ℂ} {x : USpace} (hx : x ∈ uDeg i) :
    uMode (ofLex q).1 (nq q) x - uLead q x ∈ uDeg (i + e0q q) := by
  rw [uLead, compOp_of_mem _ _ _ hx]
  exact sub_iproj_mem_of_two uDeg_isInternal (modePred_nq_cases q) (eq_ne_e0q q)
    (uMode_shifts _ _ i x hx)

theorem uLead_mem (q : LexLetter) {i : (ℤ × ℤ) × ℂ} {x : USpace} (hx : x ∈ uDeg i) :
    uLead q x ∈ uDeg (i + eq q) :=
  compOp_mem _ _ (· + eq q) hx

theorem bMode_mem (a : Fin 3) (n : ℤ) {i : (ℤ × ℤ) × ℂ} {x : BSpace} (hx : x ∈ bDeg i) :
    bMode a n x ∈ bDeg (i + ((0, 0), ((-n : ℤ) : ℂ))) := by
  unfold bDeg trivialDeg at hx ⊢
  split_ifs at hx with h
  · rw [if_pos (by simp [h])]
    have hw := BSVA.grading_mode (bAction.current a) (bAction.current_weight a) x hx n
    have e : (1 : ℂ) + i.2 - (n : ℂ) - 1 = (i + ((0, 0), ((-n : ℤ) : ℂ))).2 := by
      simp only [Prod.snd_add]; push_cast; ring
    rw [e] at hw
    exact hw
  · simp only [Submodule.mem_bot] at hx
    rw [hx, map_zero]; exact Submodule.zero_mem _

/-- The mode of the matter current. -/
abbrev mMode (a : Fin 3) (n : ℤ) : Module.End ℂ MatterSpace :=
  mode (matterSVA.Y (leeYangMatterAction.toAffineSl2Action.current a)) n

theorem aLead_tensor_mem (q : LexLetter) (i : (ℤ × ℤ) × ℂ) :
    ∀ z ∈ tensorDeg aDeg bDeg i,
      TensorProduct.map (aLead hA q) LinearMap.id z ∈ tensorDeg aDeg bDeg (i + eq q) := by
  intro z hz
  have h := tensorDeg_map_shift aDeg bDeg (aLead hA q) LinearMap.id (eq q) 0
    (fun i x hx => aLead_mem hA q hx) (fun i y hy => by rwa [add_zero]) i z hz
  rwa [add_zero] at h

theorem mLead_mem (q : LexLetter) (i : (ℤ × ℤ) × ℂ) :
    ∀ m ∈ matterDeg i, mLead hA q m ∈ matterDeg (i + eq q) := by
  intro m hm
  rw [mLead, LinearMap.add_apply]
  refine Submodule.add_mem _ ?_ ?_
  · have h := tensorDeg_map_shift (tensorDeg aDeg bDeg) uDeg
      (TensorProduct.map (aLead hA q) LinearMap.id) LinearMap.id (eq q) 0
      (fun i z hz => aLead_tensor_mem hA q i z hz) (fun i y hy => by rwa [add_zero]) i m hm
    rwa [add_zero] at h
  · have h := tensorDeg_map_shift (tensorDeg aDeg bDeg) uDeg LinearMap.id (uLead q) 0 (eq q)
      (fun i z hz => by rwa [add_zero]) (fun i y hy => uLead_mem q hy) i m hm
    rwa [zero_add] at h

theorem neg_nq_cast' (q : LexLetter) : ((-nq q : ℤ) : ℂ) = ((letterWt q : ℕ) : ℂ) :=
  neg_nq_cast q

/-- **A creation mode minus its leading part preserves `R`.** -/
theorem mMode_sub_mLead_mem (q : LexLetter) (i : (ℤ × ℤ) × ℂ) :
    ∀ m ∈ matterDeg i, mMode (ofLex q).1 (nq q) m - mLead hA q m ∈ matterDeg (i + e0q q) := by
  intro m hm
  have hsplit : mMode (ofLex q).1 (nq q) - mLead hA q =
      TensorProduct.map (TensorProduct.map (aMode (ofLex q).1 (nq q) - aLead hA q)
        LinearMap.id) LinearMap.id +
      TensorProduct.map (TensorProduct.map LinearMap.id (bMode (ofLex q).1 (nq q)))
        LinearMap.id +
      TensorProduct.map LinearMap.id (uMode (ofLex q).1 (nq q) - uLead q) := by
    have e1 : TensorProduct.map (TensorProduct.map (aMode (ofLex q).1 (nq q) - aLead hA q)
        (LinearMap.id : Module.End ℂ BSpace)) (LinearMap.id : Module.End ℂ USpace) =
        TensorProduct.map (TensorProduct.map (aMode (ofLex q).1 (nq q))
          (LinearMap.id : Module.End ℂ BSpace)) (LinearMap.id : Module.End ℂ USpace) -
          TensorProduct.map (TensorProduct.map (aLead hA q) (LinearMap.id : Module.End ℂ BSpace))
          (LinearMap.id : Module.End ℂ USpace) := by
      change LinearMap.rTensor USpace (LinearMap.rTensor BSpace
          (aMode (ofLex q).1 (nq q) - aLead hA q)) =
        LinearMap.rTensor USpace (LinearMap.rTensor BSpace (aMode (ofLex q).1 (nq q))) -
          LinearMap.rTensor USpace (LinearMap.rTensor BSpace (aLead hA q))
      rw [LinearMap.rTensor_sub, LinearMap.rTensor_sub]
    have e2 : TensorProduct.map (LinearMap.id : Module.End ℂ (ASpace ⊗[ℂ] BSpace))
        (uMode (ofLex q).1 (nq q) - uLead q) =
        TensorProduct.map LinearMap.id (uMode (ofLex q).1 (nq q)) -
          TensorProduct.map LinearMap.id (uLead q) := by
      change LinearMap.lTensor (ASpace ⊗[ℂ] BSpace) (uMode (ofLex q).1 (nq q) - uLead q) =
        LinearMap.lTensor (ASpace ⊗[ℂ] BSpace) (uMode (ofLex q).1 (nq q)) -
          LinearMap.lTensor (ASpace ⊗[ℂ] BSpace) (uLead q)
      rw [LinearMap.lTensor_sub]
    rw [mMode, matterMode_eq, mLead, e1, e2]
    abel
  rw [← LinearMap.sub_apply, hsplit, LinearMap.add_apply, LinearMap.add_apply]
  refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
  · have hin : ∀ i, ∀ z ∈ tensorDeg aDeg bDeg i,
        TensorProduct.map (aMode (ofLex q).1 (nq q) - aLead hA q) LinearMap.id z ∈
          tensorDeg aDeg bDeg (i + e0q q) := by
      intro i z hz
      have h := tensorDeg_map_shift aDeg bDeg (aMode (ofLex q).1 (nq q) - aLead hA q)
        LinearMap.id (e0q q) 0 (fun i x hx => aMode_sub_aLead_mem hA q hx)
        (fun i y hy => by rwa [add_zero]) i z hz
      rwa [add_zero] at h
    have h := tensorDeg_map_shift (tensorDeg aDeg bDeg) uDeg _ LinearMap.id (e0q q) 0 hin
      (fun i y hy => by rwa [add_zero]) i m hm
    rwa [add_zero] at h
  · have hin : ∀ i, ∀ z ∈ tensorDeg aDeg bDeg i,
        TensorProduct.map LinearMap.id (bMode (ofLex q).1 (nq q)) z ∈
          tensorDeg aDeg bDeg (i + e0q q) := by
      intro i z hz
      have h := tensorDeg_map_shift aDeg bDeg LinearMap.id (bMode (ofLex q).1 (nq q))
        0 (e0q q) (fun i x hx => by rwa [add_zero])
        (fun i y hy => by have := bMode_mem (ofLex q).1 (nq q) hy; rwa [neg_nq_cast'] at this)
        i z hz
      rwa [zero_add] at h
    have h := tensorDeg_map_shift (tensorDeg aDeg bDeg) uDeg _ LinearMap.id (e0q q) 0 hin
      (fun i y hy => by rwa [add_zero]) i m hm
    rwa [add_zero] at h
  · have h := tensorDeg_map_shift (tensorDeg aDeg bDeg) uDeg LinearMap.id
      (uMode (ofLex q).1 (nq q) - uLead q) 0 (e0q q) (fun i z hz => by rwa [add_zero])
      (fun i y hy => uMode_sub_uLead_mem q hy) i m hm
    rwa [zero_add] at h

/-! ### Joint-level shifts -/

/-- The joint shift of the Koszul differential: `(2R, gh) + (1, 1)`, antighost number `-1`. -/
abbrev δT : KF × ℤ := ((((1, 1), 0), 0), -1)

theorem ghShiftF_one_neg (jj : ℕ) : ghShiftF 1 (-(jj : ℤ) - 1) = -modeIdxF (jj, 0) := by
  unfold ghShiftF
  rw [if_neg (by omega)]
  congr 2
  refine Prod.ext ?_ rfl
  simp only
  omega

theorem b2_modeIdxF_b (jj : ℕ) : b2 (modeIdxF (jj, 0)) = 2 := by
  rw [b2_modeIdxF]; rfl

theorem gAn_eq_gMode (q : LexLetter) :
    gAn q = ConcreteHodge.gMode (ofLex q).1 1 ((ofLex q).2 : ℤ) := rfl

theorem gAn_mem_ghostB (q : LexLetter) (i : KF × ℤ) :
    ∀ y ∈ KoszulConcrete.ghostB i, gAn q y ∈
      KoszulConcrete.ghostB (i + (-modeIdxF ((ofLex q).2, 0), -1)) := by
  intro y hy
  unfold KoszulConcrete.ghostB at hy ⊢
  split_ifs at hy with h
  · have hb : b2 (i + (-modeIdxF ((ofLex q).2, 0), -1)).1 =
        2 * (i + (-modeIdxF ((ofLex q).2, 0), -1)).2 := by
      simp only [Prod.fst_add, Prod.snd_add, map_add, map_neg, h, b2_modeIdxF_b]; ring
    rw [if_pos hb]
    have h2 := ghostModeF_mem (ofLex q).1 1 ((ofLex q).2 : ℤ) hy
    rw [show -((ofLex q).2 : ℤ) - 1 = -(((ofLex q).2 : ℕ) : ℤ) - 1 from rfl,
      ghShiftF_one_neg] at h2
    exact h2
  · rw [Submodule.mem_bot] at hy; rw [hy, map_zero]; exact Submodule.zero_mem _

theorem mLead_mem_matterB (q : LexLetter) (i : KF × ℤ) :
    ∀ x ∈ KoszulConcrete.matterB i, mLead hA q x ∈
      KoszulConcrete.matterB (i + (((eq q), 0), 0)) := by
  intro x hx
  unfold KoszulConcrete.matterB matterF at hx ⊢
  split_ifs at hx ⊢ with h1 h2 h3 h4 h3 h4
  · exact mLead_mem hA q _ x hx
  all_goals first
    | (rw [Submodule.mem_bot] at hx; rw [hx, map_zero]; exact Submodule.zero_mem _)
    | (simp only [Prod.snd_add, Prod.fst_add, add_zero] at *; contradiction)

theorem eq_add_modeIdxF (q : LexLetter) :
    (((eq q), (0 : ℤ)) : KF) + -modeIdxF ((ofLex q).2, 0) = (((1, 1), 0), 0) := by
  simp only [eq, modeIdxF, modeIdx, modeR, ghCharge, ghModeWt, ghWt, letterWt]
  simp

/-- **`dN` shifts the joint grading by `δT`.** -/
theorem dN_mem_blockB (s : Finset LexLetter) (j : KF × ℤ) :
    ∀ z ∈ KoszulConcrete.blockB j, dN hA s z ∈ KoszulConcrete.blockB (j + δT) := by
  intro z hz
  rw [dN, LinearMap.coe_sum, Finset.sum_apply]
  refine Submodule.sum_mem _ fun q _ => ?_
  have h := tensorDeg_map_shift KoszulConcrete.matterB KoszulConcrete.ghostB (mLead hA q) (gAn q)
    (((eq q), 0), 0) (-modeIdxF ((ofLex q).2, 0), -1) (mLead_mem_matterB hA q)
    (gAn_mem_ghostB q) j z hz
  have e : ((((eq q), 0), 0) : KF × ℤ) + (-modeIdxF ((ofLex q).2, 0), -1) = δT := by
    rw [Prod.mk_add_mk, eq_add_modeIdxF]; rfl
  rwa [e] at h

/-! ### Natural weights -/

theorem fockDegF_eq_bot_of_weight {k : KF} (hk : ¬ ∃ w : ℕ, (w : ℂ) = k.1.2) :
    fockDegF k = ⊥ := by
  rw [fockDegF, Submodule.span_eq_bot]
  rintro _ ⟨l, hl, rfl⟩
  exfalso
  apply hk
  have hl' : wordIdxF l = k := hl
  exact ⟨ghWeight l, by rw [← hl']; rfl⟩

theorem natW_add {a b : KF} (ha : ∃ w : ℕ, (w : ℂ) = a.1.2) (hb : ∃ w : ℕ, (w : ℂ) = b.1.2) :
    ∃ w : ℕ, (w : ℂ) = (a + b).1.2 := by
  obtain ⟨w1, h1⟩ := ha
  obtain ⟨w2, h2⟩ := hb
  exact ⟨w1 + w2, by simp [h1, h2]⟩

theorem ghostDegF_eq_bot_of_weight {k : KF} (hk : ¬ ∃ w : ℕ, (w : ℂ) = k.1.2) :
    ghostDegF k = ⊥ :=
  tensorDeg_eq_bot_of (fun k : KF => ∃ w : ℕ, (w : ℂ) = k.1.2) (fun _ _ => natW_add) _ _
    (fun _ h => tensorDeg_eq_bot_of (fun k : KF => ∃ w : ℕ, (w : ℂ) = k.1.2)
      (fun _ _ => natW_add) _ _
      (fun _ h => fockDegF_eq_bot_of_weight h) (fun _ h => fockDegF_eq_bot_of_weight h) h)
    (fun _ h => fockDegF_eq_bot_of_weight h) hk

theorem ghostB_nat {j2 : KF × ℤ} {g : Sl2GhostSpace} (hg : g ∈ KoszulConcrete.ghostB j2)
    (h0 : g ≠ 0) : ∃ w : ℕ, (w : ℂ) = j2.1.1.2 := by
  by_contra h
  unfold KoszulConcrete.ghostB at hg
  split_ifs at hg
  · rw [ghostDegF_eq_bot_of_weight h, Submodule.mem_bot] at hg; exact h0 hg
  · rw [Submodule.mem_bot] at hg; exact h0 hg

theorem matterB_nat {j1 : KF × ℤ} {m : MatterSpace} (hm : m ∈ KoszulConcrete.matterB j1)
    (h0 : m ≠ 0) : ∃ w : ℕ, (w : ℂ) = j1.1.1.2 := by
  by_contra h
  unfold KoszulConcrete.matterB matterF at hm
  split_ifs at hm
  · have h1 := matterDeg_le_weight _ hm
    rw [matterNatSupported _ (by
      rintro ⟨w, hw⟩; exact h ⟨w, by rw [hw]; rfl⟩), Submodule.mem_bot] at h1
    exact h0 h1
  all_goals (rw [Submodule.mem_bot] at hm; exact h0 hm)

/-! ### The decomposition of `Q` -/

/-- The joint pieces outside the target of `d_K` from `j` (or with negative `c₀`). -/
def NTsup (j : KF × ℤ) : Submodule ℂ BRSTSpace :=
  ⨆ (j' : KF × ℤ) (_ : bIdx j' ≠ bIdx (j + δT) ∨ j'.1.2 < 0), KoszulConcrete.blockB j'

theorem shiftTarget_le_NTsup {P : KF × ℤ → Prop} {j : KF × ℤ}
    (h : ∀ δ, P δ → bIdx (j + δ) ≠ bIdx (j + δT) ∨ (j + δ).1.2 < 0) :
    shiftTarget KoszulConcrete.blockB P j ≤ NTsup j :=
  iSup_le fun δ => iSup_le fun hδ => le_iSup_of_le (j + δ) (le_iSup_of_le (h δ hδ) le_rfl)

theorem bIdx_ne_of_snd {j j' : KF × ℤ} (h : j'.2 ≠ (j + δT).2) : bIdx j' ≠ bIdx (j + δT) := by
  intro e; exact h (congrArg (fun x : (ℤ × ℤ) × ℤ => x.2) e)

theorem bIdx_ne_of_R {j j' : KF × ℤ} (h : j'.1.1.1.1 ≠ (j + δT).1.1.1.1) :
    bIdx j' ≠ bIdx (j + δT) := by
  intro e; exact h (congrArg (fun x : (ℤ × ℤ) × ℤ => x.1.1) e)

theorem sum_sN {M : Type*} [AddCommGroup M] [Module ℂ M] (N : ℕ) (F : LexLetter → M) :
    ∑ q ∈ sN N, F q = ∑ a : Fin 3, ∑ jj ∈ Finset.range N, F (toLex (a, jj)) := by
  rw [sN, Finset.sum_map, Finset.sum_product]
  rfl

theorem cGhost_mode_eq (a : Fin 3) (jj : ℕ) :
    mode (sl2GhostSVA.Y (cGhost a)) (jj : ℤ) = gAn (toLex (a, jj)) := rfl

theorem cm_mem (a : Fin 3) (n : ℤ) (j2 : KF × ℤ) {g : Sl2GhostSpace}
    (hg : g ∈ KoszulConcrete.ghostB j2) :
    mode (sl2GhostSVA.Y (cGhost a)) (-n - 1) g ∈
      shiftTarget KoszulConcrete.ghostB (fun δ : KF × ℤ => δ.1 = ghShiftF 1 n ∧ b2 δ.1 = 2 * δ.2)
        j2 := by
  have h := ghostB_lift (ghostYCoeff_shifts a 1 n) j2 g hg
  simpa only [ghostGenerator_one, mode_apply, show -(-n - 1) - 1 = n by ring] using h

theorem b2_ghShiftF_one_nonneg {n : ℤ} (hn : 0 ≤ n) : b2 (ghShiftF 1 n) = 0 := by
  unfold ghShiftF
  rw [if_pos hn, b2_modeIdxF]
  rfl

include hA in
/-- The current terms with `n ≥ 0` do not lower the antighost number. -/
theorem term_nonneg_mem (a : Fin 3) {n : ℤ} (hn : 0 ≤ n) {j1 j2 : KF × ℤ} {m : MatterSpace}
    {g : Sl2GhostSpace} (hm : m ∈ KoszulConcrete.matterB j1)
    (hg : g ∈ KoszulConcrete.ghostB j2) :
    mMode a n m ⊗ₜ[ℂ] mode (sl2GhostSVA.Y (cGhost a)) (-n - 1) g ∈ NTsup (j1 + j2) := by
  have hJ := matterB_lift (matterMode_shiftsF hA a n) j1 m hm
  have h := tmul_mem_tensor_shiftTarget KoszulConcrete.matterB KoszulConcrete.ghostB hJ
    (cm_mem a n j2 hg)
  refine shiftTarget_le_NTsup ?_ h
  rintro δ ⟨δ1, δ2, ⟨-, h1⟩, ⟨h2, h3⟩, rfl⟩
  left
  apply bIdx_ne_of_snd
  rw [h2, b2_ghShiftF_one_nonneg hn] at h3
  simp only [Prod.snd_add, h1]
  omega

theorem sub_mem_matterB (q : LexLetter) (j1 : KF × ℤ) {m : MatterSpace}
    (hm : m ∈ KoszulConcrete.matterB j1) :
    mMode (ofLex q).1 (nq q) m - mLead hA q m ∈
      KoszulConcrete.matterB (j1 + (((e0q q), 0), 0)) := by
  unfold KoszulConcrete.matterB matterF at hm ⊢
  split_ifs at hm ⊢ with h1 h2 h3 h4 h3 h4
  · exact mMode_sub_mLead_mem hA q _ m hm
  all_goals first
    | (rw [Submodule.mem_bot] at hm; rw [hm, map_zero, map_zero, sub_zero];
        exact Submodule.zero_mem _)
    | (simp only [Prod.snd_add, Prod.fst_add, add_zero] at *; contradiction)

/-- The current terms with `n < 0`, minus their Koszul part, preserve `R` on the matter side. -/
theorem term_neg_mem (q : LexLetter) {j1 j2 : KF × ℤ} {m : MatterSpace}
    {g : Sl2GhostSpace} (hm : m ∈ KoszulConcrete.matterB j1)
    (hg : g ∈ KoszulConcrete.ghostB j2) :
    (mMode (ofLex q).1 (nq q) m - mLead hA q m) ⊗ₜ[ℂ]
      mode (sl2GhostSVA.Y (cGhost (ofLex q).1)) (-nq q - 1) g ∈ NTsup (j1 + j2) := by
  have hJ : mMode (ofLex q).1 (nq q) m - mLead hA q m ∈
      shiftTarget KoszulConcrete.matterB (· = (((e0q q), 0), 0)) j1 :=
    mem_shiftTarget rfl (sub_mem_matterB hA q j1 hm)
  have h := tmul_mem_tensor_shiftTarget KoszulConcrete.matterB KoszulConcrete.ghostB hJ
    (cm_mem (ofLex q).1 (nq q) j2 hg)
  refine shiftTarget_le_NTsup ?_ h
  rintro δ ⟨δ1, δ2, rfl, ⟨h2, -⟩, rfl⟩
  left
  apply bIdx_ne_of_R
  rw [show nq q = -(((ofLex q).2 : ℕ) : ℤ) - 1 from rfl, ghShiftF_one_neg] at h2
  simp only [Prod.fst_add, h2]
  simp [modeIdxF, modeIdx, modeR]

/-- The cubic ghost term never reaches the Koszul target of a `c₀`-free source. -/
theorem term_gh_mem {j1 j2 : KF × ℤ} {m : MatterSpace} {g : Sl2GhostSpace}
    (hm : m ∈ KoszulConcrete.matterB j1) (hg : g ∈ KoszulConcrete.ghostB j2)
    (hc0 : (j1 + j2).1.2 = 0) :
    m ⊗ₜ[ℂ] mode (sl2GhostSVA.Y ghostBRSTState) 0 g ∈ NTsup (j1 + j2) := by
  have hx : m ∈ shiftTarget KoszulConcrete.matterB (· = 0) j1 :=
    mem_shiftTarget rfl (by rwa [add_zero])
  have h := tmul_mem_tensor_shiftTarget KoszulConcrete.matterB KoszulConcrete.ghostB hx
    (ghostB_lift cubicCharge_shifts j2 g hg)
  refine shiftTarget_le_NTsup ?_ h
  rintro δ ⟨δ1, δ2, rfl, ⟨h1, h2⟩, rfl⟩
  rw [zero_add]
  by_cases hb : bIdx (j1 + j2 + δ2) = bIdx (j1 + j2 + δT)
  · right
    have hq : δ2.2 = -1 := by
      have := congrArg (fun x : (ℤ × ℤ) × ℤ => x.2) hb
      simp only [bIdx, Prod.snd_add] at this
      omega
    have hR : δ2.1.1.1.1 = 1 := by
      have := congrArg (fun x : (ℤ × ℤ) × ℤ => x.1.1) hb
      simp only [bIdx, Prod.fst_add] at this
      simp at this
      omega
    rw [hq, b2_eq_piRp] at h2
    rcases h1 with h1 | h1 <;> rw [h1] at h2
    · simp at h2
    · have hc := congrArg (fun x : (ℤ × ℤ) × ℂ => x.1.1) h1
      simp only [piRp_apply] at hc
      simp only [Prod.fst_add, Prod.snd_add] at hc0 ⊢
      omega
  · left; exact hb

/-- The Koszul part of the `a`-th current sum. -/
def Dterm (N : ℕ) (a : Fin 3) (m : MatterSpace) (g : Sl2GhostSpace) (n : ℤ) : BRSTSpace :=
  if n < 0 ∧ (-n - 1).toNat < N then
    mLead hA (toLex (a, (-n - 1).toNat)) m ⊗ₜ[ℂ] mode (sl2GhostSVA.Y (cGhost a)) (-n - 1) g
  else 0

theorem Dterm_support (N : ℕ) (a : Fin 3) (m : MatterSpace) (g : Sl2GhostSpace) :
    Function.support (Dterm hA N a m g) ⊆
      ↑((Finset.range N).image fun jj : ℕ => -(jj : ℤ) - 1) := by
  intro n hn
  rw [Function.mem_support, Dterm] at hn
  split_ifs at hn with h
  · simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio]
    exact ⟨(-n - 1).toNat, h.2, by omega⟩
  · exact absurd rfl hn

theorem finsum_Dterm (N : ℕ) (a : Fin 3) (m : MatterSpace) (g : Sl2GhostSpace) :
    ∑ᶠ n, Dterm hA N a m g n =
      ∑ jj ∈ Finset.range N, mLead hA (toLex (a, jj)) m ⊗ₜ[ℂ] gAn (toLex (a, jj)) g := by
  rw [finsum_eq_sum_of_support_subset _ (Dterm_support hA N a m g),
    Finset.sum_image (fun x _ y _ h => by simpa using h)]
  refine Finset.sum_congr rfl fun jj hjj => ?_
  rw [Finset.mem_range] at hjj
  have e : (-(-(jj : ℤ) - 1) - 1) = (jj : ℤ) := by ring
  rw [Dterm, if_pos ⟨by omega, by rw [e]; simpa using hjj⟩, e, Int.toNat_natCast]
  rfl

/-- **The decomposition of `Q` on a pure tensor**: `Q (m ⊗ g) - dN (m ⊗ g)` has no component
in the Koszul target of the source piece. -/
theorem Q_sub_dN_tmul (N : ℕ) {j1 j2 : KF × ℤ} {m : MatterSpace} {g : Sl2GhostSpace}
    (hm : m ∈ KoszulConcrete.matterB j1) (hg : g ∈ KoszulConcrete.ghostB j2)
    (hc0 : (j1 + j2).1.2 = 0) {n0 : ℤ} (hn0 : (j1 + j2).1.1.2 = (n0 : ℂ)) (hN : n0 ≤ N) :
    semiInfiniteQ leeYangMatterAction.toAffineSl2Action (m ⊗ₜ[ℂ] g) -
      dN hA (sN N) (m ⊗ₜ[ℂ] g) ∈ NTsup (j1 + j2) := by
  by_cases hm0 : m = 0
  · subst hm0; simp
  by_cases hg0 : g = 0
  · subst hg0; simp
  obtain ⟨wm, hwm⟩ := matterB_nat hm hm0
  obtain ⟨wg, hwg⟩ := ghostB_nat hg hg0
  have hwsum : (wm : ℤ) + wg = n0 := by
    have h := hn0
    simp only [Prod.fst_add, Prod.snd_add, ← hwm, ← hwg] at h
    exact_mod_cast h
  rw [semiInfiniteQ_tmul, matter_even_invol]
  have hdN : dN hA (sN N) (m ⊗ₜ[ℂ] g) = ∑ a : Fin 3, ∑ jj ∈ Finset.range N,
      mLead hA (toLex (a, jj)) m ⊗ₜ[ℂ] gAn (toLex (a, jj)) g := by
    rw [dN, LinearMap.coe_sum, Finset.sum_apply, ← sum_sN N (fun q =>
      mLead hA q m ⊗ₜ[ℂ] gAn q g)]
    rfl
  rw [hdN, add_sub_right_comm, ← Finset.sum_sub_distrib]
  refine Submodule.add_mem _ (Submodule.sum_mem _ fun a _ => ?_) (term_gh_mem hm hg hc0)
  rw [← finsum_Dterm hA N a m g, ← finsum_sub_distrib
    (currentMode_support leeYangMatterAction.toAffineSl2Action a m g)
    ((Finset.finite_toSet _).subset (Dterm_support hA N a m g))]
  refine finsum_induction (fun u => u ∈ NTsup (j1 + j2)) (Submodule.zero_mem _)
    (fun _ _ h1 h2 => Submodule.add_mem _ h1 h2) (fun n => ?_)
  by_cases hn : 0 ≤ n
  · rw [Dterm, if_neg (by omega), sub_zero]
    exact term_nonneg_mem hA a hn hm hg
  · by_cases hjj : (-n - 1).toNat < N
    · rw [Dterm, if_pos ⟨by omega, hjj⟩, ← TensorProduct.sub_tmul]
      set q := toLex (a, (-n - 1).toNat) with hq
      have hn' : n = nq q := by simp only [nq, hq, ofLex_toLex]; omega
      have ha : a = (ofLex q).1 := by simp [hq]
      have h := term_neg_mem hA q hm hg
      rw [← hn', ← ha] at h
      exact h
    · rw [Dterm, if_neg (fun h => hjj h.2), sub_zero]
      -- the ghost factor vanishes by weight
      have hcm : mode (sl2GhostSVA.Y (cGhost a)) (-n - 1) g = 0 := by
        have h := ghostModeF_mem a 1 (-n - 1) (show g ∈ ghostDegF j2.1 by
          unfold KoszulConcrete.ghostB at hg
          split_ifs at hg
          · exact hg
          · exact absurd ((Submodule.mem_bot ℂ).mp hg) hg0)
        rw [show -(-n - 1) - 1 = n by ring] at h
        rw [ghostDegF_eq_bot_of_weight, Submodule.mem_bot] at h
        · exact h
        · rintro ⟨w, hw⟩
          have hsh : (ghShiftF 1 n).1.2 = (n : ℂ) := by
            have := congrArg Prod.snd (piRp_ghShiftF 1 n)
            simpa [piRp_apply] using this
          simp only [Prod.fst_add, Prod.snd_add] at hw
          rw [hsh, ← hwg] at hw
          have hw' : (w : ℤ) = wg + n := by exact_mod_cast hw
          omega
      rw [hcm, TensorProduct.tmul_zero]
      exact Submodule.zero_mem _

/-- **The decomposition of `Q` on a `c₀`-free joint piece of weight `n₀ ≤ N`.** -/
theorem Q_sub_dN_mem (N : ℕ) {j : KF × ℤ} (hc0 : j.1.2 = 0) {n0 : ℤ}
    (hn0 : j.1.1.2 = (n0 : ℂ)) (hN : n0 ≤ N) :
    ∀ z ∈ KoszulConcrete.blockB j,
      semiInfiniteQ leeYangMatterAction.toAffineSl2Action z - dN hA (sN N) z ∈ NTsup j := by
  refine tensorDeg_induction KoszulConcrete.matterB KoszulConcrete.ghostB j _ (by simp)
    (fun x y hx hy => by
      beta_reduce at hx hy ⊢
      rw [map_add, map_add, add_sub_add_comm]; exact Submodule.add_mem _ hx hy)
    (fun c x hx => by
      beta_reduce at hx ⊢
      have h := Submodule.smul_mem _ c hx
      rw [smul_sub] at h
      rwa [map_smul, map_smul]) ?_
  intro b x hx y hy
  have hj : b + (j - b) = j := by abel
  have h := Q_sub_dN_tmul hA N hx hy (by rw [hj]; exact hc0) (by rw [hj]; exact hn0) hN
  rwa [hj] at h

end MatterComp

end

end VOA.KoszulResidual
