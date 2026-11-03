/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.BRSTGoodnessShift
import VOA.Examples.ConcreteGoodLayers

/-!
# Goodness of the matter current modes for the interpreted layers

Beem–Garner's shortening `J_n = J_n^{[1]} + J_n^{[0]} + J_n^{[-1]}` with `J_n^{[1]} = 0` for
`n ≥ 0` and `J_n^{[-1]} = 0` for `n ≤ 0`, for the actual flags of the matter factors.

* `layer_map_shift` (generic): if `T` maps `F_p` into `F_{p+e}` (shifting the weight by `-n`),
  `T'` maps `F_q` into `F_{q+e'}`, and `(T x, y) = -(x, T' y)` for a symmetric invariant form that
  is nondegenerate on every flag step, then `T` maps the layer `L_p` into `⨁_{p-e' ≤ q ≤ p+e} L_q`.
  (Components below `p - e'` pair to zero against `L_q` by adjointness.)
* `layerDeg_shifts` — the same, for the interpreted layer grading `layerDeg`.
* `correctedWord_J_nonneg` — **Li-goodness of the corrected affine flag**: a nonnegative
  current mode preserves corrected degree (`J_n F_p ⊆ F_p`, `n ≥ 0`); the Sugawara letter is
  handled by `[L_m, J_n] = -n J_{m+n}`.
* `aMode_shifts`, `uMode_shifts`, `bMode_shifts` — the factor statements;
* `matterMode_shifts` — the matter current mode `J_n` maps `matterDeg` index `((2R,0),h)`
  into `((2R + 2d, 0), h - n)` with `-[n > 0] ≤ d ≤ [n < 0]`.

Everything is proved outright from `hA`.
-/

namespace VOA.ConcreteHodge

open Sl2CosetConcrete Sl2SemiInfinite AffineSl2GeneralRigidity AffineSl2BelowCritical
open VOA.GradedUnitaryCohomology VOA.LeeYangCosetTransfer VOA.VertexOperatorAlgebra
open VOA.LeeYangTransferAssembly
open AffineVOA AffineVOA.Inst AffineVOA.CorrectedR
open scoped TensorProduct

noncomputable section

/-! ### Generic: adjoint pairs of filtered operators shift layers by a bounded amount -/

section Generic

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

theorem pieceLT_mono (F : GradedFlag W) (M : ℤ) {s t : ℕ} (h : s ≤ t) :
    F.pieceLT s M ≤ F.pieceLT t M := by
  rcases s with _ | s
  · rw [GradedFlag.pieceLT_zero]; exact bot_le
  · rcases t with _ | t
    · omega
    · exact F.pieceIn_mono M (by omega)

theorem mem_iSup_layer_of_orth (B : InvariantForm W) (F : GradedFlag W) (M : ℤ)
    (hsymm : B.IsSymmetric) (hnd : LayerNondegenerate F M (LiRadical.gradedForm B M)) :
    ∀ (P s : ℕ) (y : W.grading M), y ∈ F.pieceIn P M →
      (∀ z ∈ F.pieceLT s M, LiRadical.gradedForm B M z y = 0) →
      y ∈ ⨆ (q : ℕ) (_ : s ≤ q ∧ q ≤ P), F.layer M (LiRadical.gradedForm B M) q := by
  haveI := W.finrank M
  have href : (LiRadical.gradedForm B M).IsRefl := fun a b h => by
    rw [LiRadical.gradedForm_apply] at h ⊢; rw [hsymm]; exact h
  intro P
  induction P with
  | zero =>
      intro s y hy horth
      by_cases hs : s = 0
      · subst hs
        refine Submodule.mem_iSup_of_mem 0 (Submodule.mem_iSup_of_mem ⟨le_rfl, le_rfl⟩ ?_)
        rw [GradedFlag.layer_zero]; exact hy
      · -- `F_0 ⊆ F_{s-1}`, so `y` is orthogonal to its own step: `y = 0`.
        have hy0 : y = 0 := by
          have hnd0 := hnd 0
          have : (⟨y, hy⟩ : F.pieceIn 0 M) = 0 := by
            refine hnd0.2 _ fun z => ?_
            have hz : (z : W.grading M) ∈ F.pieceLT s M := by
              obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
              exact F.pieceIn_mono M (Nat.zero_le s') z.2
            exact horth z hz
          exact congrArg Subtype.val this
        rw [hy0]; exact Submodule.zero_mem _
  | succ P ih =>
      intro s y hy horth
      by_cases hsP : P + 1 < s
      · have hy0 : y = 0 := by
          have : (⟨y, hy⟩ : F.pieceIn (P + 1) M) = 0 := by
            refine (hnd (P + 1)).2 _ fun z => ?_
            have hz : (z : W.grading M) ∈ F.pieceLT s M := by
              obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
              exact F.pieceIn_mono M (by omega) z.2
            exact horth z hz
          exact congrArg Subtype.val this
        rw [hy0]; exact Submodule.zero_mem _
      · have hdec := (layerDecomposition F href hnd (P + 1)).1
        have hy' : y ∈ F.pieceLT (P + 1) M ⊔ F.layer M (LiRadical.gradedForm B M) (P + 1) := by
          rw [hdec]; exact hy
        obtain ⟨y₁, hy₁, l, hl, rfl⟩ := Submodule.mem_sup.mp hy'
        refine Submodule.add_mem _ ?_ ?_
        · by_cases hsP' : s ≤ P
          · have h1 := ih s y₁ hy₁ (fun z hz => by
              have h := horth z hz
              have hzl : LiRadical.gradedForm B M z l = 0 :=
                hl.2 z (pieceLT_mono F M (by omega) hz)
              rw [map_add, hzl, add_zero] at h
              exact h)
            exact iSup_pred_mono (F := fun q => F.layer M (LiRadical.gradedForm B M) q)
              (fun q hq => ⟨hq.1, by omega⟩) h1
          · -- `s = P + 1`: the remainder is orthogonal to its own step
            have hs : s = P + 1 := by omega
            subst hs
            have : (⟨y₁, hy₁⟩ : F.pieceIn P M) = 0 := by
              refine (hnd P).2 _ fun z => ?_
              have hz : (z : W.grading M) ∈ F.pieceLT (P + 1) M := z.2
              have h := horth z hz
              have hzl : LiRadical.gradedForm B M z l = 0 := hl.2 z hz
              rw [map_add, hzl, add_zero] at h
              exact h
            rw [show y₁ = 0 from congrArg Subtype.val this]
            exact Submodule.zero_mem _
        · exact Submodule.mem_iSup_of_mem (P + 1)
            (Submodule.mem_iSup_of_mem ⟨by omega, le_rfl⟩ hl)

/-- **Adjoint pairs of filtered operators shift layers by a bounded amount.** -/
theorem layer_map_shift (B : InvariantForm W) (F : GradedFlag W) (hsymm : B.IsSymmetric)
    (hnd : ∀ m, LayerNondegenerate F m (LiRadical.gradedForm B m))
    (T T' : 𝒱 →ₗ[ℂ] 𝒱) (n : ℤ) (e e' : ℕ)
    (hTF : ∀ p m, ∀ x ∈ F.piece p m, T x ∈ F.piece (p + e) (m - n))
    (hT'F : ∀ q m, ∀ x ∈ F.piece q m, T' x ∈ F.piece (q + e') (m + n))
    (hadj : ∀ x y, B.form (T x) y = -B.form x (T' y))
    (p : ℕ) (m : ℤ) (x : W.grading m) (hx : x ∈ F.layer m (LiRadical.gradedForm B m) p) :
    T x ∈ ⨆ (q : ℕ) (_ : p ≤ q + e' ∧ q ≤ p + e),
      (F.layer (m - n) (LiRadical.gradedForm B (m - n)) q).map (W.grading (m - n)).subtype := by
  have hTx : T x ∈ F.piece (p + e) (m - n) := hTF p m x hx.1
  let y : W.grading (m - n) := ⟨T x, F.le_grading _ _ hTx⟩
  have hy : y ∈ F.pieceIn (p + e) (m - n) := hTx
  have horth : ∀ z ∈ F.pieceLT (p - e') (m - n), LiRadical.gradedForm B (m - n) z y = 0 := by
    intro z hz
    rw [LiRadical.gradedForm_apply]
    rcases hs : p - e' with _ | s'
    · rw [hs, GradedFlag.pieceLT_zero, Submodule.mem_bot] at hz
      rw [hz]; simp
    · rw [hs, GradedFlag.pieceLT_succ] at hz
      have hT'z : T' z ∈ F.piece (s' + e') (m - n + n) := hT'F s' (m - n) z hz
      rw [sub_add_cancel] at hT'z
      let w : W.grading m := ⟨T' z, F.le_grading _ _ hT'z⟩
      have hw : w ∈ F.pieceLT p m := by
        obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
        exact F.pieceIn_mono m (by omega) hT'z
      have h0 : LiRadical.gradedForm B m w x = 0 := hx.2 w hw
      rw [LiRadical.gradedForm_apply] at h0
      change B.form (z : 𝒱) (T x) = 0
      rw [hsymm, hadj, hsymm]
      change -B.form (T' z) (x : 𝒱) = 0
      rw [show B.form (T' z) (x : 𝒱) = 0 from h0, neg_zero]
  have hmem := mem_iSup_layer_of_orth B F (m - n) hsymm (hnd (m - n)) (p + e) (p - e') y hy horth
  have hmap := Submodule.mem_map_of_mem (f := (W.grading (m - n)).subtype) hmem
  rw [Submodule.map_iSup] at hmap
  simp only [Submodule.map_iSup] at hmap
  exact iSup_pred_mono (F := fun q =>
    (F.layer (m - n) (LiRadical.gradedForm B (m - n)) q).map (W.grading (m - n)).subtype)
    (fun q hq => ⟨by omega, hq.2⟩) hmap

/-- The layer shifts allowed for an operator with flag shifts `e`, `e'`. -/
def layerPred (n : ℤ) (e e' : ℕ) (δ : (ℤ × ℤ) × ℂ) : Prop :=
  ∃ d : ℤ, δ = ((2 * d, 0), ((-n : ℤ) : ℂ)) ∧ -(e' : ℤ) ≤ d ∧ d ≤ e

theorem layerDeg_shifts (B : InvariantForm W) (F : GradedFlag W) (hsymm : B.IsSymmetric)
    (hnd : ∀ m, LayerNondegenerate F m (LiRadical.gradedForm B m))
    (T T' : 𝒱 →ₗ[ℂ] 𝒱) (n : ℤ) (e e' : ℕ)
    (hTF : ∀ p m, ∀ x ∈ F.piece p m, T x ∈ F.piece (p + e) (m - n))
    (hT'F : ∀ q m, ∀ x ∈ F.piece q m, T' x ∈ F.piece (q + e') (m + n))
    (hadj : ∀ x y, B.form (T x) y = -B.form x (T' y)) :
    ShiftsInto (layerDeg B F) T (layerPred n e e') := by
  intro i x₀ hx₀
  refine Submodule.iSup_induction _ (motive := fun x => T x ∈ shiftTarget _ _ i) hx₀ ?_
    (by simp) (fun x y hx hy => by
      beta_reduce at hx hy ⊢; rw [map_add]; exact Submodule.add_mem _ hx hy)
  intro m x₁ hx₁
  refine Submodule.iSup_induction _ (motive := fun x => T x ∈ shiftTarget _ _ i) hx₁ ?_
    (by simp) (fun x y hx hy => by
      beta_reduce at hx hy ⊢; rw [map_add]; exact Submodule.add_mem _ hx hy)
  intro p x₂ hx₂
  by_cases h : layerIndex p m = i
  swap
  · rw [iSup_neg h, Submodule.mem_bot] at hx₂
    rw [hx₂, map_zero]; exact Submodule.zero_mem _
  rw [iSup_pos h] at hx₂
  subst h
  obtain ⟨xW, hxW, rfl⟩ := Submodule.mem_map.mp hx₂
  have hT := layer_map_shift B F hsymm hnd T T' n e e' hTF hT'F hadj p m xW hxW
  have hle : (⨆ (q : ℕ) (_ : p ≤ q + e' ∧ q ≤ p + e),
      (F.layer (m - n) (LiRadical.gradedForm B (m - n)) q).map (W.grading (m - n)).subtype) ≤
      shiftTarget (layerDeg B F) (layerPred n e e') (layerIndex p m) := by
    refine iSup_le fun q => iSup_le fun hq => ?_
    intro y hy
    refine mem_shiftTarget (δ := ((2 * ((q : ℤ) - p), 0), ((-n : ℤ) : ℂ)))
      ⟨(q : ℤ) - p, rfl, by omega, by omega⟩ ?_
    have e1 : layerIndex p m + ((2 * ((q : ℤ) - p), 0), ((-n : ℤ) : ℂ)) =
        layerIndex q (m - n) := by
      simp only [layerIndex, Prod.mk_add_mk, add_zero]
      push_cast
      congr 2 <;> ring
    rw [e1]
    unfold layerDeg
    exact Submodule.mem_iSup_of_mem (m - n) (Submodule.mem_iSup_of_mem q
      (Submodule.mem_iSup_of_mem rfl hy))
  exact hle hT

end Generic

/-! ### Li-goodness of the corrected affine flag -/

section Li

variable (k : ℂ) (hk : k + 2 ≠ 0)

/-- **A nonnegative current mode does not raise the corrected degree of a word.** -/
theorem correctedWord_J_nonneg (a : Fin 3) {n : ℤ} (hn : 0 ≤ n) :
    ∀ w : List (Generator × ℕ),
      J k a n (correctedWordState k hk w) ∈ correctedAffineRPiece k hk w.length
  | [] => by
      rw [correctedWordState_nil, closed_vacuum, J_vacuum_nonneg k a hn]
      exact Submodule.zero_mem _
  | (.current b, r) :: rest => by
      have ih := correctedWord_J_nonneg a hn rest
      have hrest := correctedWordState_mem_piece k hk rest (p := rest.length) le_rfl
      have hw : correctedWordState k hk ((.current b, r) :: rest) =
          J k b (-(r : ℤ) - 1) (correctedWordState k hk rest) := by
        rw [correctedWordState_cons]
        exact smul_currentState_eq_J k hk b _ _
      rw [hw]
      have hcomm := LinearMap.congr_fun (current_comm k a b n (-(r : ℤ) - 1))
        (correctedWordState k hk rest)
      simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply,
        LinearMap.sum_apply, LinearMap.smul_apply] at hcomm
      rw [sub_eq_iff_eq_add] at hcomm
      rw [hcomm]
      simp only [List.length_cons]
      have hJ : ∀ (c : Fin 3) (m : ℤ) {v : WakModule k} {q : ℕ},
          v ∈ correctedAffineRPiece k hk q → J k c m v ∈ correctedAffineRPiece k hk (q + 1) := by
        intro c m v q hv
        rw [← smul_currentState_eq_J k hk c m v, add_comm]
        exact mode_piece_mem_piece_add k hk (currentState_mem_piece_one k hk c) hv m
      refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
      · exact Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (hJ c _ hrest)
      · split_ifs
        · rw [LinearMap.smul_apply, LinearMap.id_apply]
          exact Submodule.smul_mem _ _ (correctedAffineRPiece_mono k hk (Nat.le_succ _) hrest)
        · rw [LinearMap.zero_apply]; exact Submodule.zero_mem _
      · exact hJ b _ ih
  | (.sugawara, r) :: rest => by
      have ih := correctedWord_J_nonneg a hn rest
      have hrest := correctedWordState_mem_piece k hk rest (p := rest.length) le_rfl
      have hw : correctedWordState k hk ((.sugawara, r) :: rest) =
          mode (YA k hk (omegaA k)) ((-(r : ℤ) - 2) + 1) (correctedWordState k hk rest) := by
        rw [correctedWordState_cons, show (-(r : ℤ) - 2) + 1 = -(r : ℤ) - 1 by ring]
        rfl
      rw [hw]
      have hcomm := Vir.Lcomm_J_apply k hk (-(r : ℤ) - 2) a n (correctedWordState k hk rest)
      have hJ : J k a n (mode (YA k hk (omegaA k)) ((-(r : ℤ) - 2) + 1)
          (correctedWordState k hk rest)) =
          mode (YA k hk (omegaA k)) ((-(r : ℤ) - 2) + 1) (J k a n (correctedWordState k hk rest))
            - ((-n : ℤ) : ℂ) • J k a ((-(r : ℤ) - 2) + n) (correctedWordState k hk rest) := by
        rw [hcomm]; abel
      rw [hJ]
      simp only [List.length_cons]
      refine Submodule.sub_mem _ ?_ (Submodule.smul_mem _ _ ?_)
      · have h := mode_piece_mem_piece_add k hk (conformalVector_mem_piece_one k hk) ih
          ((-(r : ℤ) - 2) + 1)
        rw [add_comm 1] at h
        simpa only [closed_smul, closed_conformalVector] using h
      · rw [← smul_currentState_eq_J k hk a _ _, add_comm]
        exact mode_piece_mem_piece_add k hk (currentState_mem_piece_one k hk a) hrest _

theorem correctedPiece_J_nonneg (a : Fin 3) {n : ℤ} (hn : 0 ≤ n) {p : ℕ} {x : WakModule k}
    (hx : x ∈ correctedAffineRPiece k hk p) : J k a n x ∈ correctedAffineRPiece k hk p := by
  rw [correctedAffineRPiece] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨w, rfl⟩ := hx
      exact correctedAffineRPiece_mono k hk w.2 (correctedWord_J_nonneg k hk a hn w.1)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

/-- The flag shift of a current mode: `0` for `n ≥ 0`, `1` for `n < 0`. -/
def eN (n : ℤ) : ℕ := if 0 ≤ n then 0 else 1

theorem correctedPiece_J (a : Fin 3) (n : ℤ) {p : ℕ} {x : WakModule k}
    (hx : x ∈ correctedAffineRPiece k hk p) :
    J k a n x ∈ correctedAffineRPiece k hk (p + eN n) := by
  unfold eN
  split_ifs with hn
  · exact correctedPiece_J_nonneg k hk a hn hx
  · rw [← smul_currentState_eq_J k hk a n x, add_comm]
    exact mode_piece_mem_piece_add k hk (currentState_mem_piece_one k hk a) hx n

end Li

/-! ### The three factors -/

/-- The `A` current mode. -/
def aMode (a : Fin 3) (n : ℤ) : Module.End ℂ ASpace := mode (ASVA.Y (aAction.current a)) n

/-- The `B` current mode. -/
def bMode (a : Fin 3) (n : ℤ) : Module.End ℂ BSpace := mode (BSVA.Y (bAction.current a)) n

/-- The `U` current mode. -/
def uMode (a : Fin 3) (n : ℤ) : Module.End ℂ USpace := mode (USVA.Y (uAction.current a)) n

theorem aMode_mkQ (a : Fin 3) (n : ℤ) (x : WakModule ALevel) :
    aMode a n ((QuotVOA.maxGradedIdeal (universal ALevel aNoncritical)).mkQ x) =
      (QuotVOA.maxGradedIdeal (universal ALevel aNoncritical)).mkQ (J ALevel a n x) := by
  have h : aMode a n ((QuotVOA.maxGradedIdeal (universal ALevel aNoncritical)).mkQ x) =
      (QuotVOA.maxGradedIdeal (universal ALevel aNoncritical)).mkQ
        ((universal ALevel aNoncritical).smul (currentState ALevel a) n x) :=
    SimpleQuot.maxQuotientVOA_mkQ_smul _ _ _ _
  rw [h]
  congr 1
  exact smul_currentState_eq_J ALevel aNoncritical a n x

theorem uMode_apply (a : Fin 3) (n : ℤ) (x : USpace) : uMode a n x = J (-11 / 3) a n x :=
  smul_currentState_eq_J (-11 / 3) uNoncritical a n x

theorem aMode_flag (a : Fin 3) (n : ℤ) (p : ℕ) (m : ℤ) :
    ∀ x ∈ affineFlag.piece p m, aMode a n x ∈ affineFlag.piece (p + eN n) (m - n) := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
  rw [aMode_mkQ]
  exact Submodule.mem_map_of_mem ⟨correctedPiece_J ALevel aNoncritical a n hy.1,
    J_mem_grading aNoncritical a n hy.2⟩

theorem aMode_adj (a : Fin 3) (n : ℤ) (x y : ASpace) :
    affineForm.form (aMode a n x) y = -affineForm.form x (aMode a (-n) y) := by
  obtain ⟨x, rfl⟩ := (QuotVOA.maxGradedIdeal (universal ALevel aNoncritical)).mkQ_surjective x
  obtain ⟨y, rfl⟩ := (QuotVOA.maxGradedIdeal (universal ALevel aNoncritical)).mkQ_surjective y
  rw [aMode_mkQ, aMode_mkQ]
  change (simpleForm ALevel aNoncritical).form _ _ = -(simpleForm ALevel aNoncritical).form _ _
  rw [simpleForm_mkQ, simpleForm_mkQ]
  exact universalForm_current_adj aNoncritical a n x y

/-- The common shift predicate of the current mode `J_n`. -/
abbrev modePred (n : ℤ) : (ℤ × ℤ) × ℂ → Prop := layerPred n (eN n) (eN (-n))

/-- **The `A` current modes are good for the corrected layers** (from `hA`). -/
theorem aMode_shifts (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    (a : Fin 3) (n : ℤ) : ShiftsInto aDeg (aMode a n) (modePred n) :=
  layerDeg_shifts affineForm affineFlag (simpleForm_isSymmetric ALevel aNoncritical)
    (fun m => (hA m).1) (aMode a n) (aMode a (-n)) n (eN n) (eN (-n))
    (aMode_flag a n) (fun q m x hx => by
      have h := aMode_flag a (-n) q m x hx
      rwa [sub_neg_eq_add] at h)
    (aMode_adj a n)

theorem uMode_flag (a : Fin 3) (n : ℤ) (p : ℕ) (m : ℤ) :
    ∀ x ∈ auxiliaryFlag.piece p m, uMode a n x ∈ auxiliaryFlag.piece (p + eN n) (m - n) := by
  intro x hx
  rw [uMode_apply]
  unfold eN
  split_ifs with hn
  · exact J_mem_ordinaryFlag_of_nonneg uNoncritical a hn hx
  · have h := J_mem_ordinaryFlag_of_neg uNoncritical a (m := -n) (by omega) hx
    rwa [neg_neg, ← sub_eq_add_neg] at h

/-- **The `U` current modes are good for the PBW layers** (unconditional). -/
theorem uMode_shifts (a : Fin 3) (n : ℤ) : ShiftsInto uDeg (uMode a n) (modePred n) :=
  layerDeg_shifts auxiliaryForm auxiliaryFlag (universalForm_isSymmetric (-11 / 3) uNoncritical)
    (fun m => (auxiliaryGradedUnitary m).1) (uMode a n) (uMode a (-n)) n (eN n) (eN (-n))
    (uMode_flag a n) (fun q m x hx => by
      have h := uMode_flag a (-n) q m x hx
      rwa [sub_neg_eq_add] at h)
    (fun x y => by
      rw [uMode_apply, uMode_apply]
      exact universalForm_current_adj uNoncritical a n x y)

/-- **The `B` current modes shift the trivial grading by the weight only.** -/
theorem bMode_shifts (a : Fin 3) (n : ℤ) : ShiftsInto bDeg (bMode a n) (modePred n) := by
  refine (ShiftsInto.of_exact (δ₀ := ((0, 0), ((-n : ℤ) : ℂ))) fun i x hx => ?_).mono ?_
  · unfold bDeg trivialDeg at hx ⊢
    split_ifs at hx with h
    · rw [if_pos (by simp [h])]
      have hw := BSVA.grading_mode (bAction.current a) (bAction.current_weight a) x hx n
      have e : (1 : ℂ) + i.2 - (n : ℂ) - 1 = (i + ((0, 0), ((-n : ℤ) : ℂ))).2 := by
        simp only [Prod.snd_add]; push_cast; ring
      rw [e] at hw
      exact hw
    · simp only [Submodule.mem_bot] at hx
      rw [hx, map_zero]; exact Submodule.zero_mem _
  · rintro δ rfl
    exact ⟨0, by simp, by omega, by omega⟩

/-! ### The matter current modes -/

theorem matterMode_tmul (a : Fin 3) (n : ℤ) (x : ASpace) (y : BSpace) (z : USpace) :
    mode (matterSVA.Y (leeYangMatterAction.toAffineSl2Action.current a)) n
        ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] z) =
      ((aMode a n x ⊗ₜ[ℂ] y + x ⊗ₜ[ℂ] bMode a n y) ⊗ₜ[ℂ] z) +
        (x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] uMode a n z := by
  have h1 := tensorCurrentMode_tmul
    (tensorAffineAction aAction.toAffineSl2Action bAction.toAffineSl2Action
      aParityCompatible bParityCompatible abTensorGrading) uAction.toAffineSl2Action a n
    (x ⊗ₜ[ℂ] y) z
  have h2 : mode ((TensorVA.tensorSVA ASVA BSVA aParityCompatible bParityCompatible
      abTensorGrading).Y ((tensorAffineAction aAction.toAffineSl2Action bAction.toAffineSl2Action
        aParityCompatible bParityCompatible abTensorGrading).current a)) n (x ⊗ₜ[ℂ] y) =
      aMode a n x ⊗ₜ[ℂ] y + x ⊗ₜ[ℂ] bMode a n y :=
    tensorCurrentMode_tmul aAction.toAffineSl2Action bAction.toAffineSl2Action a n x y
  refine h1.trans ?_
  change mode ((TensorVA.tensorSVA ASVA BSVA aParityCompatible bParityCompatible
      abTensorGrading).Y ((tensorAffineAction aAction.toAffineSl2Action bAction.toAffineSl2Action
        aParityCompatible bParityCompatible abTensorGrading).current a)) n (x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] z +
      (x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] uMode a n z = _
  rw [h2]

/-- The matter current mode as a sum of factor modes. -/
theorem matterMode_eq (a : Fin 3) (n : ℤ) :
    mode (matterSVA.Y (leeYangMatterAction.toAffineSl2Action.current a)) n =
      TensorProduct.map (TensorProduct.map (aMode a n) LinearMap.id) LinearMap.id +
      TensorProduct.map (TensorProduct.map LinearMap.id (bMode a n)) LinearMap.id +
      TensorProduct.map LinearMap.id (uMode a n) := by
  apply TensorProduct.ext'
  intro w z
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add w w' hw hw' => rw [TensorProduct.add_tmul, map_add, map_add, hw, hw']
  | tmul x y =>
      rw [matterMode_tmul]
      simp only [LinearMap.add_apply, TensorProduct.map_tmul, LinearMap.id_apply,
        TensorProduct.add_tmul]

theorem addPred_zero_right {ι : Type*} [AddCommGroup ι] {P : ι → Prop} {δ : ι}
    (h : addPred P (· = 0) δ) : P δ := by
  obtain ⟨a, b, ha, rfl, rfl⟩ := h
  rwa [add_zero]

theorem addPred_zero_left {ι : Type*} [AddCommGroup ι] {P : ι → Prop} {δ : ι}
    (h : addPred (· = 0) P δ) : P δ := by
  obtain ⟨a, b, rfl, hb, rfl⟩ := h
  rwa [zero_add]

/-- **The matter current mode `J_n` is good for the interpreted matter grading.** -/
theorem matterMode_shifts (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    (a : Fin 3) (n : ℤ) :
    ShiftsInto matterDeg
      (mode (matterSVA.Y (leeYangMatterAction.toAffineSl2Action.current a)) n) (modePred n) := by
  rw [matterMode_eq]
  refine ((ShiftsInto.add ?_ ?_).add ?_)
  · exact (tensorDeg_map_shiftTarget _ uDeg
      ((tensorDeg_map_shiftTarget aDeg bDeg (aMode_shifts hA a n) (shiftsInto_id bDeg)).mono
        fun _ h => addPred_zero_right h)
      (shiftsInto_id uDeg)).mono fun _ h => addPred_zero_right h
  · exact (tensorDeg_map_shiftTarget _ uDeg
      ((tensorDeg_map_shiftTarget aDeg bDeg (shiftsInto_id aDeg) (bMode_shifts a n)).mono
        fun _ h => addPred_zero_left h)
      (shiftsInto_id uDeg)).mono fun _ h => addPred_zero_right h
  · exact (tensorDeg_map_shiftTarget (tensorDeg aDeg bDeg) uDeg
      (shiftsInto_id _) (uMode_shifts a n)).mono fun _ h => addPred_zero_left h

end

end VOA.ConcreteHodge
