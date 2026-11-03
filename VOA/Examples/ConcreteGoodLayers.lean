/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.ConcreteGoodZeroModes
import VOA.Examples.AffineSl2BelowCriticalRigidity
import VOA.Core.ScreeningKernel

/-!
# Current zero modes preserve the factor layers

Discharges the two matter factor statements of `zeroModesPreserve_of_factors`:

* `layerDeg_preserve` (generic): an operator that preserves every flag step `F_q 𝒱_m` and is
  skew for the invariant form (`(T x, y) = -(x, T y)`) preserves every orthogonal layer
  `F_p ∩ F_{p-1}^⊥` (if `y ⊥ F_{p-1}` and `z ∈ F_{p-1}`, then `(z, T y) = -(T z, y) = 0`).
* `uZeroModesPreserveLayers` — **proved**: the `U = V^{-11/3}(sl₂)` current zero modes preserve
  the ordinary PBW layers. `J^a_0` preserves PBW length (`[J^a_0, J^b_m] = f_{ab}{}^c J^c_m`,
  no central term), and is skew for `universalForm` (`universalForm_current_adj`).
* `aZeroModesPreserveLayers` — **proved**: the `A = L_{-4/3}(sl₂)` current zero modes preserve
  the corrected layers. `J^a_0 = (J^a)_{(0)}` is a derivation of every product that kills `ω`
  (`screening_leibniz`, `screening_conformalVector`) and maps currents to weight one, which is
  corrected degree one; so it preserves corrected word length. Skewness descends from the
  universal form through `simpleForm_mkQ`.

Everything is proved outright.
-/

namespace VOA.ConcreteHodge

open Sl2CosetConcrete Sl2SemiInfinite AffineSl2GeneralRigidity AffineSl2BelowCritical
open VOA.GradedUnitaryCohomology VOA.LeeYangCosetTransfer VOA.VertexOperatorAlgebra
open VOA.LeeYangTransferAssembly
open AffineVOA AffineVOA.Inst AffineVOA.CorrectedR
open scoped TensorProduct

noncomputable section

/-! ### Generic: skew flag-preserving operators preserve layers -/

section Generic

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

theorem layerDeg_preserve (B : InvariantForm W) (F : GradedFlag W) (T : 𝒱 →ₗ[ℂ] 𝒱)
    (hTF : ∀ q m, ∀ x ∈ F.piece q m, T x ∈ F.piece q m)
    (hskew : ∀ x y, B.form (T x) y = -B.form x (T y)) :
    ∀ i, ∀ x ∈ layerDeg B F i, T x ∈ layerDeg B F i := by
  intro i x hx
  refine Submodule.iSup_induction _ (motive := fun x => T x ∈ layerDeg B F i) hx ?_
    (by simp) (fun x y hx hy => by
      beta_reduce at hx hy ⊢; rw [map_add]; exact Submodule.add_mem _ hx hy)
  intro m x hx
  refine Submodule.iSup_induction _ (motive := fun x => T x ∈ layerDeg B F i) hx ?_
    (by simp) (fun x y hx hy => by
      beta_reduce at hx hy ⊢; rw [map_add]; exact Submodule.add_mem _ hx hy)
  intro p x hx
  refine Submodule.iSup_induction _ (motive := fun x => T x ∈ layerDeg B F i) hx ?_
    (by simp) (fun x y hx hy => by
      beta_reduce at hx hy ⊢; rw [map_add]; exact Submodule.add_mem _ hx hy)
  intro h x hx
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
  have hTy : T y ∈ F.piece p m := hTF p m _ hy.1
  let y' : W.grading m := ⟨T y, F.le_grading p m hTy⟩
  have hy' : y' ∈ F.layer m (LiRadical.gradedForm B m) p := by
    refine ⟨hTy, fun z hz => ?_⟩
    change LiRadical.gradedForm B m z y' = 0
    rw [LiRadical.gradedForm_apply]
    change B.form (z : 𝒱) (T y) = 0
    have hz' : (z : 𝒱) ∈ (match p with | 0 => (⊥ : Submodule ℂ 𝒱) | q + 1 => F.piece q m) := by
      cases p with
      | zero =>
          rw [GradedFlag.pieceLT_zero, Submodule.mem_bot] at hz
          rw [hz]; exact Submodule.zero_mem _
      | succ q => exact hz
    cases p with
    | zero =>
        simp only [Submodule.mem_bot] at hz'
        rw [hz', map_zero, LinearMap.zero_apply]
    | succ q =>
        have hTz : T z ∈ F.piece q m := hTF q m _ hz'
        let z' : W.grading m := ⟨T z, F.le_grading q m hTz⟩
        have hz'' : z' ∈ F.pieceLT (q + 1) m := hTz
        have h0 := hy.2 z' hz''
        change LiRadical.gradedForm B m z' y = 0 at h0
        rw [LiRadical.gradedForm_apply] at h0
        have hs := hskew z y
        change B.form (T z) y = -B.form z (T y) at hs
        rw [h0] at hs
        linear_combination hs
  exact Submodule.mem_iSup_of_mem m (Submodule.mem_iSup_of_mem p
    (Submodule.mem_iSup_of_mem h (Submodule.mem_map_of_mem hy')))

end Generic

/-! ### The auxiliary factor `U` -/

section Auxiliary

variable (k : ℂ)

theorem J_neg_mem_ordinaryPiece (b : Fin 3) (n : ℕ) {p : ℕ} {x : WakModule k}
    (hx : x ∈ ordinaryPiece k p) : J k b (-(n : ℤ) - 1) x ∈ ordinaryPiece k (p + 1) := by
  rw [ordinaryPiece] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨w, rfl⟩ := hx
      have : J k b (-(n : ℤ) - 1) (wordStateA k w.1) = wordStateA k ((b, n) :: w.1) := rfl
      rw [this]
      exact wordStateA_mem_ordinaryPiece (by simpa using w.2)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

theorem J_zero_wordStateA (a : Fin 3) :
    ∀ w : List (Fin 3 × ℕ), J k a 0 (wordStateA k w) ∈ ordinaryPiece k w.length
  | [] => by
      rw [wordStateA_nil, J_vacuum_nonneg k a le_rfl]
      exact Submodule.zero_mem _
  | (bn :: rest) => by
      have hcomm := LinearMap.congr_fun (current_comm k a bn.1 0 (-(bn.2 : ℤ) - 1))
        (wordStateA k rest)
      have hne : (0 : ℤ) + (-(bn.2 : ℤ) - 1) ≠ 0 := by omega
      rw [if_neg hne, add_zero] at hcomm
      simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.sum_apply,
        LinearMap.smul_apply] at hcomm
      have hw : wordStateA k (bn :: rest) = J k bn.1 (-(bn.2 : ℤ) - 1) (wordStateA k rest) := rfl
      rw [hw, sub_eq_iff_eq_add.mp hcomm]
      simp only [List.length_cons]
      refine Submodule.add_mem _ (Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ ?_) ?_
      · rw [zero_add]
        have : J k c (-(bn.2 : ℤ) - 1) (wordStateA k rest) = wordStateA k ((c, bn.2) :: rest) :=
          rfl
        rw [this]
        exact wordStateA_mem_ordinaryPiece (by simp)
      · exact J_neg_mem_ordinaryPiece k bn.1 bn.2 (J_zero_wordStateA a rest)

theorem J_zero_mem_ordinaryPiece (a : Fin 3) {p : ℕ} {x : WakModule k}
    (hx : x ∈ ordinaryPiece k p) : J k a 0 x ∈ ordinaryPiece k p := by
  rw [ordinaryPiece] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨w, rfl⟩ := hx
      exact ordinaryPiece_mono w.2 (J_zero_wordStateA k a w.1)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

theorem uZero_apply (a : Fin 3) (x : USpace) : uZero a x = J (-11 / 3) a 0 x :=
  smul_currentState_eq_J (-11 / 3) uNoncritical a 0 x

/-- **The `U` current zero modes preserve the ordinary PBW layers.** -/
theorem uZeroModesPreserveLayers : UZeroModesPreserveLayers := by
  intro a
  refine layerDeg_preserve auxiliaryForm auxiliaryFlag (uZero a) ?_ ?_
  · intro q m x hx
    refine ⟨?_, ?_⟩
    · rw [uZero_apply]; exact J_zero_mem_ordinaryPiece _ a hx.1
    · have h := (universal (-11 / 3) uNoncritical).grading_mode _
        (currentState_mem_grading (-11 / 3) uNoncritical a) x hx.2 0
      have e : (1 : ℤ) + m - 0 - 1 = m := by ring
      rw [e] at h
      exact h
  · intro x y
    rw [uZero_apply, uZero_apply]
    have h := universalForm_current_adj uNoncritical a 0 x y
    simpa only [neg_zero] using h

end Auxiliary

/-! ### The boundary factor `A` -/

section Boundary

/-- The universal current zero mode as a screening derivation. -/
abbrev aUnivZero (a : Fin 3) : Module.End ℂ (WakModule ALevel) :=
  Screening.screening (universal ALevel aNoncritical) (currentState ALevel a)

theorem aUnivZero_apply (a : Fin 3) (x : WakModule ALevel) :
    aUnivZero a x = J ALevel a 0 x :=
  smul_currentState_eq_J ALevel aNoncritical a 0 x

theorem aUnivZero_generator (a : Fin 3) (g : Generator) :
    aUnivZero a (generatorState ALevel aNoncritical g) ∈
      correctedAffineRPiece ALevel aNoncritical 1 := by
  cases g with
  | current b =>
      have hw : aUnivZero a (generatorState ALevel aNoncritical (Generator.current b)) ∈
          (affineSl2VOA_closed ALevel aNoncritical).grading 1 := by
        have h := (universal ALevel aNoncritical).grading_mode _
          (currentState_mem_grading ALevel aNoncritical a) _
          (currentState_mem_grading ALevel aNoncritical b) 0
        have e : (1 : ℤ) + 1 - 0 - 1 = 1 := by ring
        rw [e] at h
        exact h
      rw [← correctedAffineRWeightPiece_one_one] at hw
      exact hw.1
  | sugawara =>
      have h := Screening.screening_conformalVector (universal ALevel aNoncritical)
        (currentState_mem_grading ALevel aNoncritical a)
      change aUnivZero a (universal ALevel aNoncritical).conformalVector ∈ _
      rw [h]
      exact Submodule.zero_mem _

theorem generatorState_mem_piece_one (g : Generator) :
    generatorState ALevel aNoncritical g ∈ correctedAffineRPiece ALevel aNoncritical 1 := by
  cases g with
  | current b => exact currentState_mem_piece_one ALevel aNoncritical b
  | sugawara => exact conformalVector_mem_piece_one ALevel aNoncritical

theorem aUnivZero_word (a : Fin 3) :
    ∀ w : List (Generator × ℕ), aUnivZero a (correctedWordState ALevel aNoncritical w) ∈
      correctedAffineRPiece ALevel aNoncritical w.length
  | [] => by
      change Screening.screening _ _ (universal ALevel aNoncritical).vacuum ∈ _
      rw [Screening.screening_vacuum]
      exact Submodule.zero_mem _
  | (gr :: rest) => by
      rw [correctedWordState_cons]
      change Screening.screening _ _ ((universal ALevel aNoncritical).smul _ _ _) ∈ _
      rw [Screening.screening_leibniz]
      simp only [List.length_cons]
      rw [show rest.length + 1 = 1 + rest.length by omega]
      refine Submodule.add_mem _ ?_ ?_
      · exact mode_piece_mem_piece_add ALevel aNoncritical (aUnivZero_generator a gr.1)
          (correctedWordState_mem_piece ALevel aNoncritical rest le_rfl) _
      · exact mode_piece_mem_piece_add ALevel aNoncritical (generatorState_mem_piece_one gr.1)
          (aUnivZero_word a rest) _

theorem aUnivZero_mem_piece (a : Fin 3) {p : ℕ} {x : WakModule ALevel}
    (hx : x ∈ correctedAffineRPiece ALevel aNoncritical p) :
    aUnivZero a x ∈ correctedAffineRPiece ALevel aNoncritical p := by
  rw [correctedAffineRPiece] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨w, rfl⟩ := hx
      exact correctedAffineRPiece_mono ALevel aNoncritical w.2 (aUnivZero_word a w.1)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

theorem aZero_mkQ (a : Fin 3) (x : WakModule ALevel) :
    aZero a ((QuotVOA.maxGradedIdeal (universal ALevel aNoncritical)).mkQ x) =
      (QuotVOA.maxGradedIdeal (universal ALevel aNoncritical)).mkQ (aUnivZero a x) :=
  SimpleQuot.maxQuotientVOA_mkQ_smul _ _ _ _

/-- **The `A` current zero modes preserve the corrected layers.** -/
theorem aZeroModesPreserveLayers : AZeroModesPreserveLayers := by
  intro a
  refine layerDeg_preserve affineForm affineFlag (aZero a) ?_ ?_
  · intro q m x hx
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
    rw [aZero_mkQ]
    refine Submodule.mem_map_of_mem ⟨aUnivZero_mem_piece a hy.1, ?_⟩
    have h := (universal ALevel aNoncritical).grading_mode _
      (currentState_mem_grading ALevel aNoncritical a) y hy.2 0
    have e : (1 : ℤ) + m - 0 - 1 = m := by ring
    rw [e] at h
    exact h
  · intro x y
    obtain ⟨x, rfl⟩ := (QuotVOA.maxGradedIdeal (universal ALevel aNoncritical)).mkQ_surjective x
    obtain ⟨y, rfl⟩ := (QuotVOA.maxGradedIdeal (universal ALevel aNoncritical)).mkQ_surjective y
    rw [aZero_mkQ, aZero_mkQ]
    change (simpleForm ALevel aNoncritical).form _ _ = -(simpleForm ALevel aNoncritical).form _ _
    rw [simpleForm_mkQ, simpleForm_mkQ, aUnivZero_apply, aUnivZero_apply]
    have h := universalForm_current_adj aNoncritical a 0 x y
    simpa only [neg_zero] using h

end Boundary

end

end VOA.ConcreteHodge
