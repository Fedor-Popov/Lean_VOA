/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.KoszulResidualIdent
import VOA.Examples.TwoSeriesKoszulNative

/-!
# Level-generic port of `KoszulResidualIdent`
-/

namespace VOA.TwoSeries

open VOA.ConcreteHodge VOA.KoszulResidual VOA.KoszulConcrete VOA.SymbolModel VOA.CyclicEval
open VOA.GradedUnitaryCohomology VOA.VertexOperatorAlgebra Sl2CosetConcrete Sl2SemiInfinite
open AffineSl2GeneralRigidity AffineSl2BelowCritical VOA.LeeYangTransferAssembly VOA.SympFerm
open VOA.Ghost
open scoped TensorProduct

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

universe u v w

variable (L : CosetLevels)

/-! ## Port of `KoszulResidualIdent` -/


/-! ### Generic: projections determine vectors -/

/-! ### The matter-level components of a creation mode -/

section MatterComp

variable (hA : GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag L))

theorem aMode_sub_aLead_mem (q : LexLetter) {i : (ℤ × ℤ) × ℂ} {x : (ASpace L)} (hx : x ∈ (aDeg L) i) :
    (aMode L) (ofLex q).1 (nq q) x - (aLead L) hA q x ∈ (aDeg L) (i + e0q q) := by
  rw [(aLead_of_mem L) hA q hx]
  exact sub_iproj_mem_of_two ((aDeg_isInternal L) hA) (modePred_nq_cases q) (eq_ne_e0q q)
    ((aMode_shifts L) hA _ _ i x hx)

theorem uMode_sub_uLead_mem (q : LexLetter) {i : (ℤ × ℤ) × ℂ} {x : (USpace L)} (hx : x ∈ (uDeg L) i) :
    (uMode L) (ofLex q).1 (nq q) x - (uLead L) q x ∈ (uDeg L) (i + e0q q) := by
  rw [uLead, compOp_of_mem _ _ _ hx]
  exact sub_iproj_mem_of_two (uDeg_isInternal L) (modePred_nq_cases q) (eq_ne_e0q q)
    ((uMode_shifts L) _ _ i x hx)

theorem uLead_mem (q : LexLetter) {i : (ℤ × ℤ) × ℂ} {x : (USpace L)} (hx : x ∈ (uDeg L) i) :
    (uLead L) q x ∈ (uDeg L) (i + eq q) :=
  compOp_mem _ _ (· + eq q) hx

/-- The mode of the matter current. -/
abbrev mMode (a : Fin 3) (n : ℤ) : Module.End ℂ (MatterSpace L) :=
  mode ((matterSVA L).Y ((matterAction L).toAffineSl2Action.current a)) n

theorem aLead_tensor_mem (q : LexLetter) (i : (ℤ × ℤ) × ℂ) :
    ∀ z ∈ tensorDeg (aDeg L) bDeg i,
      TensorProduct.map ((aLead L) hA q) LinearMap.id z ∈ tensorDeg (aDeg L) bDeg (i + eq q) := by
  intro z hz
  have h := tensorDeg_map_shift (aDeg L) bDeg ((aLead L) hA q) LinearMap.id (eq q) 0
    (fun i x hx => (aLead_mem L) hA q hx) (fun i y hy => by rwa [add_zero]) i z hz
  rwa [add_zero] at h

theorem mLead_mem (q : LexLetter) (i : (ℤ × ℤ) × ℂ) :
    ∀ m ∈ (matterDeg L) i, (mLead L) hA q m ∈ (matterDeg L) (i + eq q) := by
  intro m hm
  rw [mLead, LinearMap.add_apply]
  refine Submodule.add_mem _ ?_ ?_
  · have h := tensorDeg_map_shift (tensorDeg (aDeg L) bDeg) (uDeg L)
      (TensorProduct.map ((aLead L) hA q) LinearMap.id) LinearMap.id (eq q) 0
      (fun i z hz => (aLead_tensor_mem L) hA q i z hz) (fun i y hy => by rwa [add_zero]) i m hm
    rwa [add_zero] at h
  · have h := tensorDeg_map_shift (tensorDeg (aDeg L) bDeg) (uDeg L) LinearMap.id ((uLead L) q) 0 (eq q)
      (fun i z hz => by rwa [add_zero]) (fun i y hy => (uLead_mem L) q hy) i m hm
    rwa [zero_add] at h

/-- **A creation mode minus its leading part preserves `R`.** -/
theorem mMode_sub_mLead_mem (q : LexLetter) (i : (ℤ × ℤ) × ℂ) :
    ∀ m ∈ (matterDeg L) i, (mMode L) (ofLex q).1 (nq q) m - (mLead L) hA q m ∈ (matterDeg L) (i + e0q q) := by
  intro m hm
  have hsplit : (mMode L) (ofLex q).1 (nq q) - (mLead L) hA q =
      TensorProduct.map (TensorProduct.map ((aMode L) (ofLex q).1 (nq q) - (aLead L) hA q)
        LinearMap.id) LinearMap.id +
      TensorProduct.map (TensorProduct.map LinearMap.id (bMode (ofLex q).1 (nq q)))
        LinearMap.id +
      TensorProduct.map LinearMap.id ((uMode L) (ofLex q).1 (nq q) - (uLead L) q) := by
    have e1 : TensorProduct.map (TensorProduct.map ((aMode L) (ofLex q).1 (nq q) - (aLead L) hA q)
        (LinearMap.id : Module.End ℂ BSpace)) (LinearMap.id : Module.End ℂ (USpace L)) =
        TensorProduct.map (TensorProduct.map ((aMode L) (ofLex q).1 (nq q))
          (LinearMap.id : Module.End ℂ BSpace)) (LinearMap.id : Module.End ℂ (USpace L)) -
          TensorProduct.map (TensorProduct.map ((aLead L) hA q) (LinearMap.id : Module.End ℂ BSpace))
          (LinearMap.id : Module.End ℂ (USpace L)) := by
      change LinearMap.rTensor (USpace L) (LinearMap.rTensor BSpace
          ((aMode L) (ofLex q).1 (nq q) - (aLead L) hA q)) =
        LinearMap.rTensor (USpace L) (LinearMap.rTensor BSpace ((aMode L) (ofLex q).1 (nq q))) -
          LinearMap.rTensor (USpace L) (LinearMap.rTensor BSpace ((aLead L) hA q))
      rw [LinearMap.rTensor_sub, LinearMap.rTensor_sub]
    have e2 : TensorProduct.map (LinearMap.id : Module.End ℂ ((ASpace L) ⊗[ℂ] BSpace))
        ((uMode L) (ofLex q).1 (nq q) - (uLead L) q) =
        TensorProduct.map LinearMap.id ((uMode L) (ofLex q).1 (nq q)) -
          TensorProduct.map LinearMap.id ((uLead L) q) := by
      change LinearMap.lTensor ((ASpace L) ⊗[ℂ] BSpace) ((uMode L) (ofLex q).1 (nq q) - (uLead L) q) =
        LinearMap.lTensor ((ASpace L) ⊗[ℂ] BSpace) ((uMode L) (ofLex q).1 (nq q)) -
          LinearMap.lTensor ((ASpace L) ⊗[ℂ] BSpace) ((uLead L) q)
      rw [LinearMap.lTensor_sub]
    rw [mMode, matterMode_eq, mLead, e1, e2]
    abel
  rw [← LinearMap.sub_apply, hsplit, LinearMap.add_apply, LinearMap.add_apply]
  refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
  · have hin : ∀ i, ∀ z ∈ tensorDeg (aDeg L) bDeg i,
        TensorProduct.map ((aMode L) (ofLex q).1 (nq q) - (aLead L) hA q) LinearMap.id z ∈
          tensorDeg (aDeg L) bDeg (i + e0q q) := by
      intro i z hz
      have h := tensorDeg_map_shift (aDeg L) bDeg ((aMode L) (ofLex q).1 (nq q) - (aLead L) hA q)
        LinearMap.id (e0q q) 0 (fun i x hx => (aMode_sub_aLead_mem L) hA q hx)
        (fun i y hy => by rwa [add_zero]) i z hz
      rwa [add_zero] at h
    have h := tensorDeg_map_shift (tensorDeg (aDeg L) bDeg) (uDeg L) _ LinearMap.id (e0q q) 0 hin
      (fun i y hy => by rwa [add_zero]) i m hm
    rwa [add_zero] at h
  · have hin : ∀ i, ∀ z ∈ tensorDeg (aDeg L) bDeg i,
        TensorProduct.map LinearMap.id (bMode (ofLex q).1 (nq q)) z ∈
          tensorDeg (aDeg L) bDeg (i + e0q q) := by
      intro i z hz
      have h := tensorDeg_map_shift (aDeg L) bDeg LinearMap.id (bMode (ofLex q).1 (nq q))
        0 (e0q q) (fun i x hx => by rwa [add_zero])
        (fun i y hy => by have := bMode_mem (ofLex q).1 (nq q) hy; rwa [neg_nq_cast'] at this)
        i z hz
      rwa [zero_add] at h
    have h := tensorDeg_map_shift (tensorDeg (aDeg L) bDeg) (uDeg L) _ LinearMap.id (e0q q) 0 hin
      (fun i y hy => by rwa [add_zero]) i m hm
    rwa [add_zero] at h
  · have h := tensorDeg_map_shift (tensorDeg (aDeg L) bDeg) (uDeg L) LinearMap.id
      ((uMode L) (ofLex q).1 (nq q) - (uLead L) q) 0 (e0q q) (fun i z hz => by rwa [add_zero])
      (fun i y hy => (uMode_sub_uLead_mem L) q hy) i m hm
    rwa [zero_add] at h

/-! ### Joint-level shifts -/

theorem mLead_mem_matterB (q : LexLetter) (i : KF × ℤ) :
    ∀ x ∈ (matterBK L) i, (mLead L) hA q x ∈
      (matterBK L) (i + (((eq q), 0), 0)) := by
  intro x hx
  unfold matterBK matterF at hx ⊢
  split_ifs at hx ⊢ with h1 h2 h3 h4 h3 h4
  · exact (mLead_mem L) hA q _ x hx
  all_goals first
    | (rw [Submodule.mem_bot] at hx; rw [hx, map_zero]; exact Submodule.zero_mem _)
    | (simp only [Prod.snd_add, Prod.fst_add, add_zero] at *; contradiction)

/-- **`(dN L)` shifts the joint grading by `δT`.** -/
theorem dN_mem_blockB (s : Finset LexLetter) (j : KF × ℤ) :
    ∀ z ∈ (blockB L) j, (dN L) hA s z ∈ (blockB L) (j + δT) := by
  intro z hz
  rw [dN, LinearMap.coe_sum, Finset.sum_apply]
  refine Submodule.sum_mem _ fun q _ => ?_
  have h := tensorDeg_map_shift (matterBK L) KoszulConcrete.ghostB ((mLead L) hA q) (gAn q)
    (((eq q), 0), 0) (-modeIdxF ((ofLex q).2, 0), -1) ((mLead_mem_matterB L) hA q)
    (gAn_mem_ghostB q) j z hz
  have e : ((((eq q), 0), 0) : KF × ℤ) + (-modeIdxF ((ofLex q).2, 0), -1) = δT := by
    rw [Prod.mk_add_mk, eq_add_modeIdxF]; rfl
  rwa [e] at h

/-! ### Natural weights -/

theorem matterB_nat {j1 : KF × ℤ} {m : (MatterSpace L)} (hm : m ∈ (matterBK L) j1)
    (h0 : m ≠ 0) : ∃ w : ℕ, (w : ℂ) = j1.1.1.2 := by
  by_contra h
  unfold matterBK matterF at hm
  split_ifs at hm
  · have h1 := (matterDeg_le_weight L) _ hm
    rw [(matterNatSupported L) _ (by
      rintro ⟨w, hw⟩; exact h ⟨w, by rw [hw]; rfl⟩), Submodule.mem_bot] at h1
    exact h0 h1
  all_goals (rw [Submodule.mem_bot] at hm; exact h0 hm)

/-! ### The decomposition of `Q` -/

/-- The joint pieces outside the target of `d_K` from `j` (or with negative `c₀`). -/
def NTsup (j : KF × ℤ) : Submodule ℂ (BRSTSpace L) :=
  ⨆ (j' : KF × ℤ) (_ : bIdx j' ≠ bIdx (j + δT) ∨ j'.1.2 < 0), (blockB L) j'

theorem shiftTarget_le_NTsup {P : KF × ℤ → Prop} {j : KF × ℤ}
    (h : ∀ δ, P δ → bIdx (j + δ) ≠ bIdx (j + δT) ∨ (j + δ).1.2 < 0) :
    shiftTarget (blockB L) P j ≤ (NTsup L) j :=
  iSup_le fun δ => iSup_le fun hδ => le_iSup_of_le (j + δ) (le_iSup_of_le (h δ hδ) le_rfl)

include hA in
/-- The current terms with `n ≥ 0` do not lower the antighost number. -/
theorem term_nonneg_mem (a : Fin 3) {n : ℤ} (hn : 0 ≤ n) {j1 j2 : KF × ℤ} {m : (MatterSpace L)}
    {g : Sl2GhostSpace} (hm : m ∈ (matterBK L) j1)
    (hg : g ∈ KoszulConcrete.ghostB j2) :
    (mMode L) a n m ⊗ₜ[ℂ] mode (sl2GhostSVA.Y (cGhost a)) (-n - 1) g ∈ (NTsup L) (j1 + j2) := by
  have hJ := (matterB_lift L) ((matterMode_shiftsF L) hA a n) j1 m hm
  have h := tmul_mem_tensor_shiftTarget (matterBK L) KoszulConcrete.ghostB hJ
    (cm_mem a n j2 hg)
  refine (shiftTarget_le_NTsup L) ?_ h
  rintro δ ⟨δ1, δ2, ⟨-, h1⟩, ⟨h2, h3⟩, rfl⟩
  left
  apply bIdx_ne_of_snd
  rw [h2, b2_ghShiftF_one_nonneg hn] at h3
  simp only [Prod.snd_add, h1]
  omega

theorem sub_mem_matterB (q : LexLetter) (j1 : KF × ℤ) {m : (MatterSpace L)}
    (hm : m ∈ (matterBK L) j1) :
    (mMode L) (ofLex q).1 (nq q) m - (mLead L) hA q m ∈
      (matterBK L) (j1 + (((e0q q), 0), 0)) := by
  unfold matterBK matterF at hm ⊢
  split_ifs at hm ⊢ with h1 h2 h3 h4 h3 h4
  · exact (mMode_sub_mLead_mem L) hA q _ m hm
  all_goals first
    | (rw [Submodule.mem_bot] at hm; rw [hm, map_zero, map_zero, sub_zero];
        exact Submodule.zero_mem _)
    | (simp only [Prod.snd_add, Prod.fst_add, add_zero] at *; contradiction)

/-- The current terms with `n < 0`, minus their Koszul part, preserve `R` on the matter side. -/
theorem term_neg_mem (q : LexLetter) {j1 j2 : KF × ℤ} {m : (MatterSpace L)}
    {g : Sl2GhostSpace} (hm : m ∈ (matterBK L) j1)
    (hg : g ∈ KoszulConcrete.ghostB j2) :
    ((mMode L) (ofLex q).1 (nq q) m - (mLead L) hA q m) ⊗ₜ[ℂ]
      mode (sl2GhostSVA.Y (cGhost (ofLex q).1)) (-nq q - 1) g ∈ (NTsup L) (j1 + j2) := by
  have hJ : (mMode L) (ofLex q).1 (nq q) m - (mLead L) hA q m ∈
      shiftTarget (matterBK L) (· = (((e0q q), 0), 0)) j1 :=
    mem_shiftTarget rfl ((sub_mem_matterB L) hA q j1 hm)
  have h := tmul_mem_tensor_shiftTarget (matterBK L) KoszulConcrete.ghostB hJ
    (cm_mem (ofLex q).1 (nq q) j2 hg)
  refine (shiftTarget_le_NTsup L) ?_ h
  rintro δ ⟨δ1, δ2, rfl, ⟨h2, -⟩, rfl⟩
  left
  apply bIdx_ne_of_R
  rw [show nq q = -(((ofLex q).2 : ℕ) : ℤ) - 1 from rfl, ghShiftF_one_neg] at h2
  simp only [Prod.fst_add, h2]
  simp [modeIdxF, modeIdx, modeR]

/-- The cubic ghost term never reaches the Koszul target of a `c₀`-free source. -/
theorem term_gh_mem {j1 j2 : KF × ℤ} {m : (MatterSpace L)} {g : Sl2GhostSpace}
    (hm : m ∈ (matterBK L) j1) (hg : g ∈ KoszulConcrete.ghostB j2)
    (hc0 : (j1 + j2).1.2 = 0) :
    m ⊗ₜ[ℂ] mode (sl2GhostSVA.Y ghostBRSTState) 0 g ∈ (NTsup L) (j1 + j2) := by
  have hx : m ∈ shiftTarget (matterBK L) (· = 0) j1 :=
    mem_shiftTarget rfl (by rwa [add_zero])
  have h := tmul_mem_tensor_shiftTarget (matterBK L) KoszulConcrete.ghostB hx
    (ghostB_lift cubicCharge_shifts j2 g hg)
  refine (shiftTarget_le_NTsup L) ?_ h
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
def Dterm (N : ℕ) (a : Fin 3) (m : (MatterSpace L)) (g : Sl2GhostSpace) (n : ℤ) : (BRSTSpace L) :=
  if n < 0 ∧ (-n - 1).toNat < N then
    (mLead L) hA (toLex (a, (-n - 1).toNat)) m ⊗ₜ[ℂ] mode (sl2GhostSVA.Y (cGhost a)) (-n - 1) g
  else 0

theorem Dterm_support (N : ℕ) (a : Fin 3) (m : (MatterSpace L)) (g : Sl2GhostSpace) :
    Function.support ((Dterm L) hA N a m g) ⊆
      ↑((Finset.range N).image fun jj : ℕ => -(jj : ℤ) - 1) := by
  intro n hn
  rw [Function.mem_support, Dterm] at hn
  split_ifs at hn with h
  · simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio]
    exact ⟨(-n - 1).toNat, h.2, by omega⟩
  · exact absurd rfl hn

theorem finsum_Dterm (N : ℕ) (a : Fin 3) (m : (MatterSpace L)) (g : Sl2GhostSpace) :
    ∑ᶠ n, (Dterm L) hA N a m g n =
      ∑ jj ∈ Finset.range N, (mLead L) hA (toLex (a, jj)) m ⊗ₜ[ℂ] gAn (toLex (a, jj)) g := by
  rw [finsum_eq_sum_of_support_subset _ ((Dterm_support L) hA N a m g),
    Finset.sum_image (fun x _ y _ h => by simpa using h)]
  refine Finset.sum_congr rfl fun jj hjj => ?_
  rw [Finset.mem_range] at hjj
  have e : (-(-(jj : ℤ) - 1) - 1) = (jj : ℤ) := by ring
  rw [Dterm, if_pos ⟨by omega, by rw [e]; simpa using hjj⟩, e, Int.toNat_natCast]
  rfl

/-- **The decomposition of `Q` on a pure tensor**: `Q (m ⊗ g) - (dN L) (m ⊗ g)` has no component
in the Koszul target of the source piece. -/
theorem Q_sub_dN_tmul (N : ℕ) {j1 j2 : KF × ℤ} {m : (MatterSpace L)} {g : Sl2GhostSpace}
    (hm : m ∈ (matterBK L) j1) (hg : g ∈ KoszulConcrete.ghostB j2)
    (hc0 : (j1 + j2).1.2 = 0) {n0 : ℤ} (hn0 : (j1 + j2).1.1.2 = (n0 : ℂ)) (hN : n0 ≤ N) :
    semiInfiniteQ (matterAction L).toAffineSl2Action (m ⊗ₜ[ℂ] g) -
      (dN L) hA (sN N) (m ⊗ₜ[ℂ] g) ∈ (NTsup L) (j1 + j2) := by
  by_cases hm0 : m = 0
  · subst hm0; simp
  by_cases hg0 : g = 0
  · subst hg0; simp
  obtain ⟨wm, hwm⟩ := (matterB_nat L) hm hm0
  obtain ⟨wg, hwg⟩ := ghostB_nat hg hg0
  have hwsum : (wm : ℤ) + wg = n0 := by
    have h := hn0
    simp only [Prod.fst_add, Prod.snd_add, ← hwm, ← hwg] at h
    exact_mod_cast h
  rw [semiInfiniteQ_tmul, matter_even_invol]
  have hdN : (dN L) hA (sN N) (m ⊗ₜ[ℂ] g) = ∑ a : Fin 3, ∑ jj ∈ Finset.range N,
      (mLead L) hA (toLex (a, jj)) m ⊗ₜ[ℂ] gAn (toLex (a, jj)) g := by
    rw [dN, LinearMap.coe_sum, Finset.sum_apply, ← sum_sN N (fun q =>
      (mLead L) hA q m ⊗ₜ[ℂ] gAn q g)]
    rfl
  rw [hdN, add_sub_right_comm, ← Finset.sum_sub_distrib]
  refine Submodule.add_mem _ (Submodule.sum_mem _ fun a _ => ?_) ((term_gh_mem L) hm hg hc0)
  rw [← (finsum_Dterm L) hA N a m g, ← finsum_sub_distrib
    (currentMode_support (matterAction L).toAffineSl2Action a m g)
    ((Finset.finite_toSet _).subset ((Dterm_support L) hA N a m g))]
  refine finsum_induction (fun u => u ∈ (NTsup L) (j1 + j2)) (Submodule.zero_mem _)
    (fun _ _ h1 h2 => Submodule.add_mem _ h1 h2) (fun n => ?_)
  by_cases hn : 0 ≤ n
  · rw [Dterm, if_neg (by omega), sub_zero]
    exact (term_nonneg_mem L) hA a hn hm hg
  · by_cases hjj : (-n - 1).toNat < N
    · rw [Dterm, if_pos ⟨by omega, hjj⟩, ← TensorProduct.sub_tmul]
      set q := toLex (a, (-n - 1).toNat) with hq
      have hn' : n = nq q := by simp only [nq, hq, ofLex_toLex]; omega
      have ha : a = (ofLex q).1 := by simp [hq]
      have h := (term_neg_mem L) hA q hm hg
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
    ∀ z ∈ (blockB L) j,
      semiInfiniteQ (matterAction L).toAffineSl2Action z - (dN L) hA (sN N) z ∈ (NTsup L) j := by
  refine tensorDeg_induction (matterBK L) KoszulConcrete.ghostB j _ (by simp)
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
  have h := (Q_sub_dN_tmul L) hA N hx hy (by rw [hj]; exact hc0) (by rw [hj]; exact hn0) hN
  rwa [hj] at h

end MatterComp


end

end VOA.TwoSeries
