/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.BRSTGoodnessDifferential
import VOA.Examples.BRSTGoodnessEndpoint

/-!
# The antighost-count grading of the actual BRST space

The fine grading `brstDegF = matterF ⊗ ghostDegF` (`BRSTGoodnessDifferential`), indexed by
`KF = ((2R, gh), weight) × (number of c₀)`, forgets how an index splits between matter and ghosts.
The antighost number `#b` (number of `b` creation modes) is a function of the *ghost* part of the
index alone: with `piRp k = ((2R', gh), weight)`, `2R' = #b + #c` and `gh = #c - #b`, so
`2 #b = 2R' - gh` (`b2`) and `2 #c = 2R' + gh` (`c2`).

This file builds the joint grading `blockB` of `BRSTSpace`, indexed by `KF × ℤ` (fine index,
antighost number), as the tensor grading of

* `matterB (k, q) = matterF k` if `q = 0`, else `0`;
* `ghostB (k, q) = ghostDegF k` if `b2 k = 2 q`, else `0`.

## Results (all proved outright, from `hA` and `hB` where positivity is used)

* `ghostDegF_eq_bot` — **parity and positivity of the ghost counts**: a nonzero fine ghost piece
  has `b2 = 2 #b`, `c2 = 2 #c` with `#b, #c ∈ ℕ` (word-level computation);
* `blockB_isInternal` — `blockB` is an internal direct sum (orthogonality + positivity);
* `blockB_le_brstDegF`, `brstDegF_le_blockB` — it refines `brstDegF`, and `brstDegF k` is the
  sum of the `blockB (k, q)`;
* `blockB_eq_bot` — `blockB (k, q) = 0` unless `q ≥ 0` and `gh + q ≥ 0`;
* `semiInfiniteQ_shiftsB` — **`Q` changes the antighost number by `0` or `-1`** (and shifts
  `2R'` by `±1`) on the whole BRST space: the current terms `J ⊗ c` add a `c` or remove a `b`,
  and the cubic ghost charge has `Δ(2R') = ±1`, `Δgh = 1`;
* `relativeWeight_stableB` — the actual relative weight spaces are stable under the `blockB`
  projections (the total current zero modes preserve every piece, the antighost zero modes shift
  it injectively).
-/

namespace VOA.KoszulConcrete

open VOA.ConcreteHodge
open Sl2CosetConcrete Sl2SemiInfinite AffineSl2GeneralRigidity AffineSl2BelowCritical
open VOA.GradedUnitaryCohomology VOA.LeeYangCosetTransfer VOA.VertexOperatorAlgebra
open VOA.LeeYangTransferAssembly VOA.SympFerm VOA.Ghost
open scoped TensorProduct

noncomputable section

/-! ### Ghost counts of a fine index -/

/-- `2 × (number of b)` of a fine index: `2R' - gh`. -/
def b2 : KF →+ ℤ :=
  ((AddMonoidHom.fst ℤ ℤ) - (AddMonoidHom.snd ℤ ℤ)).comp
    ((AddMonoidHom.fst (ℤ × ℤ) ℂ).comp piRp)

/-- `2 × (number of c)` of a fine index: `2R' + gh`. -/
def c2 : KF →+ ℤ :=
  ((AddMonoidHom.fst ℤ ℤ) + (AddMonoidHom.snd ℤ ℤ)).comp
    ((AddMonoidHom.fst (ℤ × ℤ) ℂ).comp piRp)

@[simp] theorem b2_apply (k : KF) : b2 k = k.1.1.1 + k.2 - k.1.1.2 := rfl
@[simp] theorem c2_apply (k : KF) : c2 k = k.1.1.1 + k.2 + k.1.1.2 := rfl

theorem b2_eq_piRp (k : KF) : b2 k = (piRp k).1.1 - (piRp k).1.2 := rfl

/-- A fine index realized by a ghost monomial: even, nonnegative ghost counts. -/
def GoodIdx (k : KF) : Prop := ∃ b c : ℕ, b2 k = 2 * b ∧ c2 k = 2 * c

theorem goodIdx_zero : GoodIdx 0 := ⟨0, 0, by simp, by simp⟩

theorem goodIdx_add {k k' : KF} (h : GoodIdx k) (h' : GoodIdx k') : GoodIdx (k + k') := by
  obtain ⟨b, c, hb, hc⟩ := h
  obtain ⟨b', c', hb', hc'⟩ := h'
  exact ⟨b + b', c + c', by rw [map_add, hb, hb']; push_cast; ring,
    by rw [map_add, hc, hc']; push_cast; ring⟩

theorem goodIdx_modeIdxF (p : ℕ × Fin 2) : GoodIdx (modeIdxF p) := by
  obtain ⟨j, e⟩ := p
  fin_cases e
  · refine ⟨1, 0, ?_, ?_⟩ <;>
      simp [modeIdxF, modeIdx, modeR, ghCharge]
  · by_cases hj : j = 0
    · subst hj
      refine ⟨0, 1, ?_, ?_⟩ <;> simp [modeIdxF, modeIdx, modeR, ghCharge]
    · refine ⟨0, 1, ?_, ?_⟩ <;> simp [modeIdxF, modeIdx, modeR, ghCharge, hj]

theorem goodIdx_wordIdxF (l : SFWord) : GoodIdx (wordIdxF l) := by
  induction l with
  | nil =>
    have : wordIdxF [] = 0 := by
      simp [wordIdxF, wordIdx_nil]
    rw [this]; exact goodIdx_zero
  | cons p l ih => rw [wordIdxF_cons]; exact goodIdx_add (goodIdx_modeIdxF p) ih

theorem fockDegF_eq_bot {k : KF} (hk : ¬ GoodIdx k) : fockDegF k = ⊥ := by
  rw [fockDegF, Submodule.span_eq_bot]
  rintro _ ⟨l, hl, rfl⟩
  exact absurd (hl ▸ goodIdx_wordIdxF l) hk

/-- A tensor grading of two gradings supported on an additively closed set is supported there. -/
theorem tensorDeg_eq_bot_of {ι : Type*} [AddCommGroup ι] {V W : Type*} [AddCommGroup V]
    [Module ℂ V] [AddCommGroup W] [Module ℂ W] (P : ι → Prop)
    (hadd : ∀ a b, P a → P b → P (a + b)) (dV : ι → Submodule ℂ V) (dW : ι → Submodule ℂ W)
    (hV : ∀ i, ¬ P i → dV i = ⊥) (hW : ∀ i, ¬ P i → dW i = ⊥) {k : ι} (hk : ¬ P k) :
    tensorDeg dV dW k = ⊥ := by
  refine le_bot_iff.mp (iSup_le fun b => ?_)
  by_cases hb : P b
  · have hkb : ¬ P (k - b) := fun h => hk (by simpa using hadd _ _ hb h)
    rw [hW _ hkb, Submodule.map₂_bot_right]
  · rw [hV _ hb, Submodule.map₂_bot_left]

theorem ghostDegF_eq_bot {k : KF} (hk : ¬ GoodIdx k) : ghostDegF k = ⊥ :=
  tensorDeg_eq_bot_of GoodIdx (fun _ _ => goodIdx_add) _ _
    (fun _ h => tensorDeg_eq_bot_of GoodIdx (fun _ _ => goodIdx_add) _ _
      (fun _ h => fockDegF_eq_bot h) (fun _ h => fockDegF_eq_bot h) h)
    (fun _ h => fockDegF_eq_bot h) hk

/-! ### The joint grading -/

/-- Matter part: the fine matter grading at antighost number `0`. -/
def matterB (j : KF × ℤ) : Submodule ℂ MatterSpace := if j.2 = 0 then matterF j.1 else ⊥

/-- Ghost part: the fine ghost grading at its antighost number. -/
def ghostB (j : KF × ℤ) : Submodule ℂ Sl2GhostSpace :=
  if b2 j.1 = 2 * j.2 then ghostDegF j.1 else ⊥

/-- **The joint (fine index, antighost number) grading of the BRST space.** -/
def blockB : KF × ℤ → Submodule ℂ BRSTSpace := tensorDeg matterB ghostB

theorem matterB_span (hA : GradedUnitary affineForm affineRealStructure affineFlag) :
    iSup matterB = ⊤ := by
  rw [eq_top_iff, ← matterF_span hA]
  refine iSup_le fun k => le_iSup_of_le (k, 0) ?_
  simp [matterB]

theorem ghostB_span : iSup ghostB = ⊤ := by
  rw [eq_top_iff, ← ghostDegF_span]
  refine iSup_le fun k => ?_
  by_cases hk : GoodIdx k
  · obtain ⟨b, c, hb, -⟩ := hk
    refine le_iSup_of_le (k, (b : ℤ)) ?_
    simp [ghostB, hb]
  · rw [ghostDegF_eq_bot hk]; exact bot_le

section Internal

variable {BB : InvariantForm BVOA} {RB : RealStructure BVOA}

theorem matterB_orth (hA : GradedUnitary affineForm affineRealStructure affineFlag) :
    ∀ a b, a ≠ b → ∀ x ∈ matterB a, ∀ y ∈ matterB b,
      (((carrierForm affineForm affineRealStructure affineFlag hA affineGramRefl).tensor
        (unitaryCarrierForm BB RB)).tensor
        (carrierForm auxiliaryForm auxiliaryRealStructure auxiliaryFlag auxiliaryGradedUnitary
          auxiliaryGramRefl)) x y = 0 := by
  intro a b hab x hx y hy
  unfold matterB at hx hy
  split_ifs at hx hy with ha hb
  · have : a.1 ≠ b.1 := fun h => hab (Prod.ext h (ha.trans hb.symm))
    exact matterF_orth hA a.1 b.1 this x hx y hy
  · rw [Submodule.mem_bot] at hy; rw [hy, SesqForm.zero_right]
  · rw [Submodule.mem_bot] at hx; rw [hx, SesqForm.zero_left]
  · rw [Submodule.mem_bot] at hx; rw [hx, SesqForm.zero_left]

theorem ghostB_orth (w : Finset ModeIdx → ℝ) :
    ∀ a b, a ≠ b → ∀ x ∈ ghostB a, ∀ y ∈ ghostB b, ghostForm w x y = 0 := by
  intro a b hab x hx y hy
  unfold ghostB at hx hy
  split_ifs at hx hy with ha hb
  · have : a.1 ≠ b.1 := by
      intro h
      apply hab
      refine Prod.ext h ?_
      have : 2 * a.2 = 2 * b.2 := by rw [← ha, ← hb, h]
      omega
    exact ghostDegF_orth w a.1 b.1 this x hx y hy
  · rw [Submodule.mem_bot] at hy; rw [hy, SesqForm.zero_right]
  · rw [Submodule.mem_bot] at hx; rw [hx, SesqForm.zero_left]
  · rw [Submodule.mem_bot] at hx; rw [hx, SesqForm.zero_left]

theorem blockB_orth (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    (w : Finset ModeIdx → ℝ) :
    ∀ a b, a ≠ b → ∀ x ∈ blockB a, ∀ y ∈ blockB b,
      matterGhostForm hA BB RB (ghostForm w) x y = 0 :=
  tensorDeg_orth _ _ _ _ (matterB_orth hA) (ghostB_orth w)

/-- **The joint grading is internal.** -/
theorem blockB_isInternal (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    (hB : VOA.ConcreteHodge.Unitary BB RB) (w : Finset ModeIdx → ℝ) (hw : ∀ s, 0 < w s) :
    DirectSum.IsInternal blockB := by
  classical
  have hpos := weakGU_matterGhostForm hA hB (ghostForm_pos w hw)
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top _
    (tensorDeg_span _ _ (matterB_span hA) ghostB_span)
  rw [iSupIndep_def]
  intro a
  rw [Submodule.disjoint_def]
  intro x hx hx'
  apply eq_zero_of_sesq_self_eq_zero _ hpos
  refine sesq_iSup_right' _ (fun b => ⨆ (_ : b ≠ a), blockB b) (fun b y hy => ?_) x hx'
  by_cases hba : b = a
  · subst hba
    simp only [ne_eq, not_true_eq_false, iSup_false, Submodule.mem_bot] at hy
    rw [hy, SesqForm.zero_right]
  · beta_reduce at hy
    rw [iSup_pos (show b ≠ a from hba)] at hy
    exact blockB_orth (BB := BB) (RB := RB) hA w a b (Ne.symm hba) x hx y hy

end Internal

/-! ### Comparison with the fine grading -/

theorem blockB_le_brstDegF (j : KF × ℤ) : blockB j ≤ brstDegF j.1 :=
  tensorDeg_le (AddMonoidHom.fst KF ℤ) _ _ matterF ghostDegF brstDegF
    (fun _ _ _ _ hx hy => tmul_mem_tensorDeg _ _ hx hy)
    (fun i => by unfold matterB; split_ifs <;> simp)
    (fun i => by unfold ghostB; split_ifs <;> simp) j

theorem brstDegF_le_blockB (k : KF) :
    brstDegF k ≤ ⨆ (j : KF × ℤ) (_ : (AddMonoidHom.fst KF ℤ) j = k), blockB j :=
  tensorDeg_le_coarsen (AddMonoidHom.fst KF ℤ) _ _ _ _
    (fun i => le_iSup_of_le (i, 0) (le_iSup_of_le rfl (by simp [matterB])))
    (fun i => by
      by_cases hk : GoodIdx i
      · obtain ⟨b, c, hb, -⟩ := hk
        exact le_iSup_of_le (i, (b : ℤ)) (le_iSup_of_le rfl (by simp [ghostB, hb]))
      · rw [ghostDegF_eq_bot hk]; exact bot_le) k

theorem matterF_eq_bot {k : KF} (hk : k.2 ≠ 0 ∨ k.1.1.2 ≠ 0) : matterF k = ⊥ := by
  unfold matterF
  split_ifs with h
  · rcases hk with hk | hk
    · exact absurd h hk
    · refine le_bot_iff.mp fun x hx => ?_
      rw [Submodule.mem_bot]
      exact eq_zero_of_mem_zeroGhost hk (matterDeg_le_zeroGhost k.1 hx)
  · rfl

/-- **No negative antighost or ghost counts**: `blockB (k, q) = 0` unless `q ≥ 0` and
`gh + q ≥ 0` (`#c = gh + #b`). -/
theorem blockB_eq_bot {j : KF × ℤ} (hj : j.2 < 0 ∨ j.1.1.1.2 + j.2 < 0) : blockB j = ⊥ := by
  refine le_bot_iff.mp (iSup_le fun b => ?_)
  by_cases hb : b.2 = 0 ∧ b.1.2 = 0 ∧ b.1.1.1.2 = 0
  · obtain ⟨hb2, hbc, hbg⟩ := hb
    have hg : ghostB (j - b) = ⊥ := by
      unfold ghostB
      split_ifs with h
      · refine ghostDegF_eq_bot ?_
        rintro ⟨nb, nc, hnb, hnc⟩
        simp only [Prod.fst_sub, Prod.snd_sub, hb2, sub_zero] at h hnb hnc
        simp only [b2_apply, c2_apply, Prod.fst_sub, Prod.snd_sub] at h hnb hnc
        rcases hj with hj | hj <;> omega
      · rfl
    rw [hg, Submodule.map₂_bot_right]
  · have hm : matterB b = ⊥ := by
      unfold matterB
      split_ifs with h
      · refine matterF_eq_bot ?_
        by_contra hc
        push Not at hc
        exact hb ⟨h, hc.1, hc.2⟩
      · rfl
    rw [hm, Submodule.map₂_bot_left]

/-! ### Lifting shifts to the joint grading -/

theorem matterB_lift {T : MatterSpace →ₗ[ℂ] MatterSpace} {P : KF → Prop}
    (hT : ShiftsInto matterF T P) : ShiftsInto matterB T (fun δ => P δ.1 ∧ δ.2 = 0) := by
  intro j x hx
  unfold matterB at hx
  split_ifs at hx with hj
  · have h := hT j.1 x hx
    refine (iSup_le fun δ => iSup_le fun hδ => ?_ : shiftTarget matterF P j.1 ≤ _) h
    intro y hy
    refine mem_shiftTarget (δ := (δ, 0)) ⟨hδ, rfl⟩ ?_
    simp only [matterB, Prod.snd_add, hj, add_zero, if_true, Prod.fst_add]
    exact hy
  · rw [Submodule.mem_bot] at hx
    rw [hx, map_zero]; exact Submodule.zero_mem _

theorem ghostB_lift {T : Sl2GhostSpace →ₗ[ℂ] Sl2GhostSpace} {P : KF → Prop}
    (hT : ShiftsInto ghostDegF T P) :
    ShiftsInto ghostB T (fun δ => P δ.1 ∧ b2 δ.1 = 2 * δ.2) := by
  intro j x hx
  unfold ghostB at hx
  split_ifs at hx with hj
  · have h := hT j.1 x hx
    refine (iSup_le fun δ => iSup_le fun hδ => ?_ : shiftTarget ghostDegF P j.1 ≤ _) h
    intro y hy
    by_cases hg : GoodIdx (j.1 + δ)
    · obtain ⟨nb, nc, hnb, -⟩ := hg
      have hδ2 : b2 δ = 2 * ((nb : ℤ) - j.2) := by
        rw [map_add, hj] at hnb; linarith
      refine mem_shiftTarget (δ := (δ, (nb : ℤ) - j.2)) ⟨hδ, hδ2⟩ ?_
      have hb : b2 (j + (δ, (nb : ℤ) - j.2)).1 = 2 * (j + (δ, (nb : ℤ) - j.2)).2 := by
        simp only [Prod.fst_add, Prod.snd_add, map_add, hj, hδ2]; ring
      have he : ghostB (j + (δ, (nb : ℤ) - j.2)) = ghostDegF (j.1 + δ) := by
        unfold ghostB; rw [if_pos hb]; rfl
      rw [he]
      exact hy
    · rw [ghostDegF_eq_bot hg, Submodule.mem_bot] at hy
      rw [hy]; exact Submodule.zero_mem _
  · rw [Submodule.mem_bot] at hx
    rw [hx, map_zero]; exact Submodule.zero_mem _

/-! ### `Q` changes the antighost number by `0` or `-1` -/

/-- The good joint shifts: `2R'` by `±1`, ghost number `+1`, weight `0`; antighost number `0` or
`-1`. -/
def GoodB (δ : KF × ℤ) : Prop := GoodRp δ.1 ∧ (δ.2 = 0 ∨ δ.2 = -1)

theorem b2_of_goodRp {δ : KF} (h : GoodRp δ) : b2 δ = 0 ∨ b2 δ = -2 := by
  rw [b2_eq_piRp]
  rcases h with h | h <;> rw [h] <;> simp

theorem goodB_of {δ : KF × ℤ} (h : GoodRp δ.1) (h2 : b2 δ.1 = 2 * δ.2) : GoodB δ := by
  refine ⟨h, ?_⟩
  rcases b2_of_goodRp h with e | e <;> rw [e] at h2 <;> omega

theorem b2_ghShiftF_one (n : ℤ) : b2 (ghShiftF 1 n) = 0 ∨ b2 (ghShiftF 1 n) = -2 := by
  rw [b2_eq_piRp, piRp_ghShiftF]
  split_ifs <;> simp [ghCharge]

theorem current_term_goodB (n : ℤ) :
    ∀ δ, addPred (fun δ : KF × ℤ => matterPredF n δ.1 ∧ δ.2 = 0)
      (fun δ : KF × ℤ => δ.1 = ghShiftF 1 n ∧ b2 δ.1 = 2 * δ.2) δ → GoodB δ := by
  rintro δ ⟨a₁, a₂, ⟨h1, h1'⟩, ⟨h2, h2'⟩, rfl⟩
  refine ⟨current_term_good n _ ⟨a₁.1, a₂.1, h1, h2, rfl⟩, ?_⟩
  simp only [Prod.snd_add, h1', zero_add]
  rw [h2] at h2'
  rcases b2_ghShiftF_one n with e | e <;> rw [e] at h2' <;> omega

/-- **`Q` shifts the joint grading by `GoodB`** on the whole BRST space: the antighost number
changes by `0` (`c`-creating terms) or `-1` (`b`-annihilating terms). -/
theorem semiInfiniteQ_shiftsB (hA : GradedUnitary affineForm affineRealStructure affineFlag) :
    ShiftsInto blockB (semiInfiniteQ leeYangMatterAction.toAffineSl2Action) GoodB := by
  intro k z hz
  refine tensorDeg_induction matterB ghostB k
    (fun z => semiInfiniteQ leeYangMatterAction.toAffineSl2Action z ∈
      shiftTarget blockB GoodB k)
    (by simp) (fun x y hx hy => by simpa only [map_add] using Submodule.add_mem _ hx hy)
    (fun c x hx => by simpa only [map_smul] using Submodule.smul_mem _ c hx) ?_ z hz
  intro b x hx y hy
  rw [semiInfiniteQ_tmul, matter_even_invol]
  have hk : b + (k - b) = k := by abel
  refine Submodule.add_mem _ (Submodule.sum_mem _ fun a _ => ?_) ?_
  · refine finsum_induction (fun u => u ∈ shiftTarget blockB GoodB k)
      (Submodule.zero_mem _) (fun _ _ h1 h2 => Submodule.add_mem _ h1 h2) (fun n => ?_)
    have hJ := matterB_lift (matterMode_shiftsF hA a n) b x hx
    have hc : mode (sl2GhostSVA.Y (cGhost a)) (-n - 1) y ∈
        shiftTarget ghostB (fun δ : KF × ℤ => δ.1 = ghShiftF 1 n ∧ b2 δ.1 = 2 * δ.2)
          (k - b) := by
      have h := ghostB_lift (ghostYCoeff_shifts a 1 n) (k - b) y hy
      simpa only [ghostGenerator_one, mode_apply, show -(-n - 1) - 1 = n by ring] using h
    have h := tmul_mem_tensor_shiftTarget matterB ghostB hJ hc
    rw [hk] at h
    exact shiftTarget_mono (current_term_goodB n) k h
  · have hx' : x ∈ shiftTarget matterB (· = 0) b := mem_shiftTarget rfl (by rwa [add_zero])
    have h := tmul_mem_tensor_shiftTarget matterB ghostB hx'
      (ghostB_lift cubicCharge_shifts (k - b) y hy)
    rw [hk] at h
    refine shiftTarget_mono ?_ k h
    rintro δ ⟨a₁, a₂, rfl, ⟨h1, h2⟩, rfl⟩
    rw [zero_add]
    exact goodB_of h1 h2

/-! ### Stability of the relative weight spaces -/

theorem ghShiftF_bc_cancel (m : ℤ) : ghShiftF 0 m + ghShiftF 1 (-1 - m) = 0 := by
  unfold ghShiftF
  by_cases hm : 0 ≤ m
  · rw [if_pos hm, if_neg (by omega),
      show (-(-1 - m) - 1).toNat = m.toNat by congr 1; ring,
      show (1 : Fin 2) + 1 = 0 from rfl, add_neg_cancel]
  · rw [if_neg hm, if_pos (by omega),
      show (-1 - m).toNat = (-m - 1).toNat by congr 1; ring,
      show (0 : Fin 2) + 1 = 1 from rfl, neg_add_cancel]

/-- The ghost current zero modes preserve every fine ghost piece. -/
theorem ghZero_mem_ghostDegF (a : Fin 3) {k : KF} {y : Sl2GhostSpace} (hy : y ∈ ghostDegF k) :
    ghZero a y ∈ ghostDegF k := by
  change sl2GhostSVA.Y (ghostCurrent a) (-0 - 1) y ∈ ghostDegF k
  have h := ghostCurrentCoeff_shifts a (-0 - 1) k y hy
  refine (iSup_le fun δ => iSup_le fun hδ => ?_ : shiftTarget ghostDegF _ k ≤ _) h
  obtain ⟨m, rfl⟩ := hδ
  rw [show (-0 - 1 : ℤ) - m = -1 - m by ring, ghShiftF_bc_cancel, add_zero]

theorem ghZero_mem_ghostB (a : Fin 3) {j : KF × ℤ} {y : Sl2GhostSpace} (hy : y ∈ ghostB j) :
    ghZero a y ∈ ghostB j := by
  unfold ghostB at hy ⊢
  split_ifs at hy ⊢
  · exact ghZero_mem_ghostDegF a hy
  · rw [Submodule.mem_bot] at hy ⊢; rw [hy, map_zero]

theorem matterZero_mem_matterB (a : Fin 3) {j : KF × ℤ} {x : MatterSpace} (hx : x ∈ matterB j) :
    mode (matterSVA.Y (leeYangMatterAction.toAffineSl2Action.current a)) 0 x ∈ matterB j := by
  unfold matterB matterF at hx ⊢
  split_ifs at hx ⊢ <;> first
    | exact matterDeg_zero_preserve aZeroModesPreserveLayers uZeroModesPreserveLayers a _ x hx
    | (rw [Submodule.mem_bot] at hx ⊢; rw [hx, map_zero])

theorem totalZero_mem_blockB (a : Fin 3) (j : KF × ℤ) :
    ∀ x ∈ blockB j, totalCurrentZero leeYangMatterAction.toAffineSl2Action a x ∈ blockB j :=
  tensorDeg_preserve_sum matterB ghostB _ _ (ghZero a)
    (fun m g => totalCurrentZero_tmul _ a m g) (fun _ _ hx => matterZero_mem_matterB a hx)
    (fun _ _ hy => ghZero_mem_ghostB a hy) j

/-- The joint shift of an antighost zero mode (removing `c₀`). -/
def antiShiftB : KF × ℤ := (ghShiftF 0 (-1), 0)

theorem b2_antiShift : b2 (ghShiftF 0 (-1)) = 0 := by
  rw [b2_eq_piRp, piRp_ghShiftF]
  simp [ghCharge]

theorem antiZero_mem_blockB (a : Fin 3) (j : KF × ℤ) :
    ∀ x ∈ blockB j, antighostZero matterSVA a x ∈ blockB (j + antiShiftB) := by
  refine tensorDeg_shift_right matterB ghostB _ (VOA.ConcreteHodge.gMode a 0 0) antiShiftB
    (fun m g => ?_)
    (fun i y hy => ?_) j
  · rw [antighostZero_eq, TensorProduct.map_tmul, LinearMap.id_apply]
  · unfold ghostB at hy ⊢
    split_ifs at hy with h1
    · have hb : b2 (i + antiShiftB).1 = 2 * (i + antiShiftB).2 := by
        simp only [antiShiftB, Prod.fst_add, Prod.snd_add, map_add, b2_antiShift, h1, add_zero]
      rw [if_pos hb]
      simpa [antiShiftB] using ghostModeF_mem a 0 0 hy
    · rw [Submodule.mem_bot] at hy; rw [hy, map_zero]; exact Submodule.zero_mem _

theorem blockB_le_weight (w : Finset ModeIdx → ℝ) (j : KF × ℤ) :
    blockB j ≤ brstSVA.grading j.1.1.2 :=
  (blockB_le_brstDegF j).trans ((brstDegF_le_brstDeg w j.1).trans
    (brstDeg_le_weight (ghostRGrading w) _))

/-- **The actual relative weight spaces are stable under the joint projections.** -/
theorem relativeWeight_stableB (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    {BB : InvariantForm BVOA} {RB : RealStructure BVOA} (hB : VOA.ConcreteHodge.Unitary BB RB)
    (w : Finset ModeIdx → ℝ) (hw : ∀ s, 0 < w s) (n : ℤ) :
    ProjStable (blockB_isInternal hA hB w hw) (relativeWeight n) := by
  have hI := blockB_isInternal hA hB w hw
  refine projStable_inf hI (projStable_inf hI ?_ ?_) ?_
  · exact projStable_iInf hI fun a => projStable_ker hI _ (totalZero_mem_blockB a)
  · exact projStable_iInf hI fun a =>
      projStable_ker_shift hI _ (· + antiShiftB) (add_left_injective _) (antiZero_mem_blockB a)
  · exact projStable_weight hI brstSVA.isInternal (fun j => j.1.1.2) (blockB_le_weight w) (n : ℂ)

end

end VOA.KoszulConcrete
