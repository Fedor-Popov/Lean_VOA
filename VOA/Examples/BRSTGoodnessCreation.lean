/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.BRSTGoodnessEndpoint

/-!
# The coset stress tensor has interpreted degree at most one

* `aY_shifts` — a coefficient of a state of corrected degree one maps the layer `L_q` of `A`
  into `⨁_{q' ≤ q+1} L_{q'}` (mode compatibility of the corrected flag, plus the layer
  decomposition from `hA`); `bY_shifts` — every coefficient of every `B` state stays in `R = 0`.
* `G1` — the span of `s_A ⊗ s_B` with `s_A` of corrected degree `≤ 1`; `cosetOmega_mem_G1`:
  the coset conformal vector `ω_A ⊗ 1 + 1 ⊗ ω_B - Sug_diag` lies in `G1` (the quadratic Casimir
  of `A` is `2(k+2) ω_A`, of corrected degree one; cross terms `J_A ⊗ J_B` have degree one).
* `cosetOmegaMode_shifts` — every coefficient of `ω_C`, acting on the BRST space, raises the
  interpreted `2R` by at most `2` and preserves the ghost number.
-/

namespace VOA.ConcreteHodge

open Sl2CosetConcrete Sl2SemiInfinite AffineSl2GeneralRigidity AffineSl2BelowCritical
open VOA.GradedUnitaryCohomology VOA.LeeYangCosetTransfer VOA.VertexOperatorAlgebra
open VOA.LeeYangTransferAssembly
open scoped TensorProduct

noncomputable section

/-- The `2R`-raising-by-at-most-two, ghost-preserving shifts. -/
def UpTwo (δ : (ℤ × ℤ) × ℂ) : Prop := δ.1.2 = 0 ∧ δ.1.1 ≤ 2

/-- Pieces of a flag step are spanned by the layers up to that step. -/
theorem piece_le_layers {𝒱 : Type*} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
    (B : InvariantForm W) (F : GradedFlag W) (hsymm : B.IsSymmetric)
    (hnd : ∀ m, LayerNondegenerate F m (LiRadical.gradedForm B m)) (P : ℕ) (M : ℤ) {y : 𝒱}
    (hy : y ∈ F.piece P M) :
    y ∈ ⨆ (q : ℕ) (_ : q ≤ P), layerDeg B F (layerIndex q M) := by
  let yW : W.grading M := ⟨y, F.le_grading _ _ hy⟩
  have h := mem_iSup_layer_of_orth B F M hsymm (hnd M) P 0 yW hy (fun z hz => by
    rw [GradedFlag.pieceLT_zero, Submodule.mem_bot] at hz; rw [hz]; simp)
  have hmap := Submodule.mem_map_of_mem (f := (W.grading M).subtype) h
  simp only [Submodule.map_iSup] at hmap
  refine (iSup_le fun q => iSup_le fun hq => ?_ :
    (⨆ (q : ℕ) (_ : 0 ≤ q ∧ q ≤ P),
      (F.layer M (LiRadical.gradedForm B M) q).map (W.grading M).subtype) ≤ _) hmap
  refine le_iSup_of_le q (le_iSup_of_le hq.2 ?_)
  intro z hz
  unfold layerDeg
  exact Submodule.mem_iSup_of_mem M (Submodule.mem_iSup_of_mem q
    (Submodule.mem_iSup_of_mem rfl hz))

/-- Coefficients of corrected-degree-one states of `A` raise the layer index by `≤ 1`. -/
theorem aY_shifts (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    {s : ASpace} {w : ℤ} (hs : s ∈ affineFlag.piece 1 w) (j : ℤ) :
    ShiftsInto aDeg (ASVA.Y s j) UpTwo := by
  intro i x₀ hx₀
  refine Submodule.iSup_induction _ (motive := fun x => ASVA.Y s j x ∈ shiftTarget _ _ i) hx₀
    ?_ (by simp) (fun x y hx hy => by
      beta_reduce at hx hy ⊢; rw [map_add]; exact Submodule.add_mem _ hx hy)
  intro m x₁ hx₁
  refine Submodule.iSup_induction _ (motive := fun x => ASVA.Y s j x ∈ shiftTarget _ _ i) hx₁
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
  have hxp : (xW : ASpace) ∈ affineFlag.piece q m := hxW.1
  have hmode := affineFlag_modeCompatible (k := -j - 1) hs hxp
  have hY : ASVA.Y s j xW = AVOA.smul s (-j - 1) xW := by
    rw [PreVertexAlgebra.smul_def, mode_apply, show -(-j - 1) - 1 = j by ring]; rfl
  change ASVA.Y s j (xW : ASpace) ∈ _
  rw [hY]
  have hl := piece_le_layers affineForm affineFlag (simpleForm_isSymmetric ALevel aNoncritical)
    (fun m => (hA m).1) (1 + q) _ hmode
  refine (iSup_le fun q' => iSup_le fun hq' => ?_ :
    (⨆ (q' : ℕ) (_ : q' ≤ 1 + q), aDeg (layerIndex q' (w + m - (-j - 1) - 1))) ≤ _) hl
  intro z hz
  refine mem_shiftTarget (δ := ((2 * ((q' : ℤ) - q), 0),
    (((w + m - (-j - 1) - 1 : ℤ) : ℂ) - (m : ℂ)))) ⟨rfl, show 2 * ((q' : ℤ) - q) ≤ 2 by omega⟩ ?_
  have e : layerIndex q m + ((2 * ((q' : ℤ) - q), 0),
      (((w + m - (-j - 1) - 1 : ℤ) : ℂ) - (m : ℂ))) = layerIndex q' (w + m - (-j - 1) - 1) := by
    simp only [layerIndex, Prod.mk_add_mk, add_zero]
    congr 2 <;> ring
  rw [e]; exact hz

theorem bSpace_even (y : BSpace) : y ∈ BSVA.parity 0 := by
  change y ∈ (ParityGrading.even BSpace).parity 0; simp [ParityGrading.even]

/-- Every coefficient of every `B` state stays in `R = 0`. -/
theorem bY_shifts (s : BSpace) (j : ℤ) :
    ShiftsInto bDeg (BSVA.Y s j) (fun δ => δ.1 = (0, 0)) := by
  intro i x hx
  unfold bDeg trivialDeg at hx
  split_ifs at hx with hi
  · have htop : BSVA.Y s j x ∈ ⨆ h : ℂ, BSVA.grading h := by
      rw [BSVA.isInternal.submodule_iSup_eq_top]; trivial
    refine (iSup_le fun h => ?_ : (⨆ h : ℂ, BSVA.grading h) ≤ _) htop
    intro z hz
    refine mem_shiftTarget (δ := ((0, 0), h - i.2)) rfl ?_
    unfold bDeg trivialDeg
    rw [if_pos (by simp [hi])]
    simpa using hz
  · rw [Submodule.mem_bot] at hx
    rw [hx, map_zero]; exact Submodule.zero_mem _

/-- The span of `s_A ⊗ s_B` with `s_A` of corrected degree at most one. -/
def G1 : Submodule ℂ (ASpace ⊗[ℂ] BSpace) :=
  Submodule.span ℂ {z | ∃ (sA : ASpace) (sB : BSpace) (w : ℤ),
    sA ∈ affineFlag.piece 1 w ∧ z = sA ⊗ₜ[ℂ] sB}

/-- The `j`-th coefficient of the `A ⊗ B` state-field map, as a linear map. -/
def abYCoeff (j : ℤ) : (ASpace ⊗[ℂ] BSpace) →ₗ[ℂ] Module.End ℂ (ASpace ⊗[ℂ] BSpace) :=
  (LinearMap.proj j : (ℤ → Module.End ℂ (ASpace ⊗[ℂ] BSpace)) →ₗ[ℂ] _) ∘ₗ abSVA.Y

theorem abYCoeff_apply (j : ℤ) (z : ASpace ⊗[ℂ] BSpace) : abYCoeff j z = abSVA.Y z j := rfl

theorem upTwo_add {δ : (ℤ × ℤ) × ℂ}
    (h : addPred UpTwo (fun δ : (ℤ × ℤ) × ℂ => δ.1 = (0, 0)) δ) : UpTwo δ := by
  obtain ⟨a, b, ⟨ha1, ha2⟩, hb, rfl⟩ := h
  refine ⟨?_, ?_⟩ <;> simp only [Prod.fst_add, Prod.snd_add, hb, Prod.fst_zero,
    Prod.snd_zero, add_zero, Prod.mk_zero_zero] <;> simp_all

/-- **Coefficients of `G1` states raise the interpreted `A ⊗ B` degree by at most two.** -/
theorem G1_shifts (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    {s : ASpace ⊗[ℂ] BSpace} (hs : s ∈ G1) (j : ℤ) :
    ShiftsInto (tensorDeg aDeg bDeg) (abSVA.Y s j) UpTwo := by
  rw [G1] at hs
  rw [← abYCoeff_apply]
  induction hs using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨sA, sB, w, hsA, rfl⟩ := hz
      intro i x hx
      refine tensorDeg_induction aDeg bDeg i
        (fun x => abYCoeff j (sA ⊗ₜ[ℂ] sB) x ∈ shiftTarget (tensorDeg aDeg bDeg) UpTwo i)
        (by simp) (fun x y hx hy => by simpa only [map_add] using Submodule.add_mem _ hx hy)
        (fun c x hx => by simpa only [map_smul] using Submodule.smul_mem _ c hx) ?_ x hx
      intro b a ha y hy
      rw [abYCoeff_apply]
      change TensorVA.tenY ASVA BSVA (sA ⊗ₜ[ℂ] sB) j (a ⊗ₜ[ℂ] y) ∈ _
      rw [TensorVA.tenY_tmul_parity ASVA BSVA sA (bSpace_even sB), TensorVA.kappaTen_zero,
        LinearMap.id_apply, TensorVA.rawCoeff_tmul]
      refine finsum_induction (fun u => u ∈ shiftTarget (tensorDeg aDeg bDeg) UpTwo i)
        (Submodule.zero_mem _) (fun _ _ h1 h2 => Submodule.add_mem _ h1 h2) (fun m => ?_)
      have h := tmul_mem_tensor_shiftTarget aDeg bDeg (aY_shifts hA hsA m b a ha)
        (bY_shifts sB (j - m) (i - b) y hy)
      rw [add_sub_cancel] at h
      exact shiftTarget_mono (fun δ hδ => upTwo_add hδ) i h
  | zero => rw [map_zero]; exact ShiftsInto.zero _ _
  | add x y _ _ hx hy => rw [map_add]; exact hx.add hy
  | smul c x _ hx => rw [map_smul]; exact hx.smul c

end

end VOA.ConcreteHodge

namespace VOA.ConcreteHodge

open Sl2CosetConcrete Sl2SemiInfinite AffineSl2GeneralRigidity AffineSl2BelowCritical
open VOA.GradedUnitaryCohomology VOA.LeeYangCosetTransfer VOA.VertexOperatorAlgebra
open VOA.LeeYangTransferAssembly
open scoped TensorProduct

noncomputable section

theorem aVacuum_mem_piece_one : ASVA.vacuum ∈ affineFlag.piece 1 0 := by
  have h : ASVA.vacuum ∈ affineFlag.piece 0 0 := by
    rw [affineFlag.vacuum_zero]; exact Submodule.mem_span_singleton_self _
  exact affineFlag.mono 0 (Nat.zero_le 1) h

theorem aCurrent_mem_piece_one (c : Fin 3) : aAction.current c ∈ affineFlag.piece 1 1 :=
  affineCurrent_mem_flag_one c

theorem tmul_mem_G1 {sA : ASpace} {w : ℤ} (h : sA ∈ affineFlag.piece 1 w) (sB : BSpace) :
    sA ⊗ₜ[ℂ] sB ∈ G1 :=
  Submodule.subset_span ⟨sA, sB, w, h, rfl⟩

/-- The non-Casimir part of one diagonal bilinear lies in `G1`. -/
theorem diag_bilinear_sub_mem_G1 (b c : Fin 3) :
    mode (abSVA.Y (diagonalAction.current b)) (-1) (diagonalAction.current c) -
      mode (ASVA.Y (aAction.current b)) (-1) (aAction.current c) ⊗ₜ[ℂ] BSVA.vacuum ∈ G1 := by
  change mode (TensorVA.tenY ASVA BSVA (tensorCurrentState aAction.toAffineSl2Action
      bAction.toAffineSl2Action b)) (-1) (tensorCurrentState aAction.toAffineSl2Action
      bAction.toAffineSl2Action c) - _ ∈ G1
  rw [show tensorCurrentState aAction.toAffineSl2Action bAction.toAffineSl2Action c =
    aAction.current c ⊗ₜ[ℂ] BSVA.vacuum + ASVA.vacuum ⊗ₜ[ℂ] bAction.current c from rfl,
    map_add, tensorCurrentMode_tmul, tensorCurrentMode_tmul]
  have hvA : mode (ASVA.Y (aAction.current b)) (-1) ASVA.vacuum = aAction.current b :=
    (ASVA.creation _).1
  have hvB : mode (BSVA.Y (bAction.current b)) (-1) BSVA.vacuum = bAction.current b :=
    (BSVA.creation _).1
  rw [hvA, hvB, add_sub_right_comm, add_sub_cancel_left]
  refine Submodule.add_mem _ (tmul_mem_G1 (aCurrent_mem_piece_one c) _)
    (Submodule.add_mem _ (tmul_mem_G1 (aCurrent_mem_piece_one b) _)
      (tmul_mem_G1 aVacuum_mem_piece_one _))

theorem aQuadratic_eq :
    quadraticState aAction.toAffineSl2Action = ((2 : ℂ) * ((-4 / 3 : ℂ) + 2)) • AVOA.conformalVector := by
  rw [← aAction_sugawara, sugawaraState, smul_smul, mul_inv_cancel₀ (by norm_num), one_smul]

/-- **The coset conformal vector has corrected degree at most one.** -/
theorem cosetOmega_mem_G1 : cosetOmega ∈ G1 := by
  have hamb : ambientConformal ∈ G1 :=
    Submodule.add_mem _ (tmul_mem_G1 affineConformal_mem_flag_one _)
      (tmul_mem_G1 aVacuum_mem_piece_one _)
  have hquad : quadraticState diagonalAction.toAffineSl2Action -
      quadraticState aAction.toAffineSl2Action ⊗ₜ[ℂ] BSVA.vacuum ∈ G1 := by
    have e : quadraticState diagonalAction.toAffineSl2Action -
        quadraticState aAction.toAffineSl2Action ⊗ₜ[ℂ] BSVA.vacuum =
        ∑ b : Fin 3, ∑ c : Fin 3, AffineVOA.kappaInv b c •
          (mode (abSVA.Y (diagonalAction.current b)) (-1) (diagonalAction.current c) -
            mode (ASVA.Y (aAction.current b)) (-1) (aAction.current c) ⊗ₜ[ℂ] BSVA.vacuum) := by
      simp only [quadraticState, TensorProduct.sum_tmul, ← TensorProduct.smul_tmul',
        smul_sub, Finset.sum_sub_distrib]
    rw [e]
    exact Submodule.sum_mem _ fun b _ => Submodule.sum_mem _ fun c _ =>
      Submodule.smul_mem _ _ (diag_bilinear_sub_mem_G1 b c)
  have hA2 : quadraticState aAction.toAffineSl2Action ⊗ₜ[ℂ] BSVA.vacuum ∈ G1 := by
    rw [aQuadratic_eq, ← TensorProduct.smul_tmul']
    exact Submodule.smul_mem _ _ (tmul_mem_G1 affineConformal_mem_flag_one _)
  have hdiag : diagonalSugawara ∈ G1 := by
    unfold diagonalSugawara sugawaraState
    refine Submodule.smul_mem _ _ ?_
    have := Submodule.add_mem _ hquad hA2
    rwa [sub_add_cancel] at this
  exact Submodule.sub_mem _ hamb hdiag

end

end VOA.ConcreteHodge

namespace VOA.ConcreteHodge

open Sl2CosetConcrete Sl2SemiInfinite AffineSl2GeneralRigidity AffineSl2BelowCritical
open VOA.GradedUnitaryCohomology VOA.LeeYangCosetTransfer VOA.VertexOperatorAlgebra
open VOA.LeeYangTransferAssembly VOA.SympFerm VOA.Ghost
open scoped TensorProduct

noncomputable section

/-- The BRST image of the coset conformal vector. -/
abbrev omegaB : BRSTSpace := cosetToComplex cosetOmegaState

/-- Coefficients of `ω_C` act on the matter factor `A ⊗ B` only. -/
theorem omegaB_Y_eq (j : ℤ) :
    brstSVA.Y omegaB j = TensorProduct.map
      (TensorProduct.map (abSVA.Y cosetOmega j) LinearMap.id) LinearMap.id := by
  apply TensorProduct.ext'
  intro m g
  change TensorVA.tenY matterSVA sl2GhostSVA
    ((cosetOmega ⊗ₜ[ℂ] USVA.vacuum) ⊗ₜ[ℂ] sl2GhostSVA.vacuum) j (m ⊗ₜ[ℂ] g) = _
  rw [tenY_left_unit matterSVA sl2GhostSVA, TensorProduct.map_tmul, LinearMap.id_apply]
  congr 1
  induction m using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul x u =>
      change TensorVA.tenY abSVA USVA (cosetOmega ⊗ₜ[ℂ] USVA.vacuum) j (x ⊗ₜ[ℂ] u) = _
      rw [tenY_left_unit abSVA USVA, TensorProduct.map_tmul, LinearMap.id_apply]

/-- **Every coefficient of `ω_C` raises the interpreted `2R` by at most two.** -/
theorem omegaB_shifts (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    (w : Finset ModeIdx → ℝ) (j : ℤ) :
    ShiftsInto (brstDeg (ghostRGrading w)) (brstSVA.Y omegaB j) UpTwo := by
  rw [omegaB_Y_eq]
  have h1 := G1_shifts hA cosetOmega_mem_G1 j
  have h2 := tensorDeg_map_shiftTarget (tensorDeg aDeg bDeg) uDeg h1 (shiftsInto_id uDeg)
  have h3 := tensorDeg_map_shiftTarget matterDeg (ghostRGrading w).deg
    (h2.mono fun _ h => addPred_zero_right h) (shiftsInto_id _)
  exact h3.mono fun _ h => addPred_zero_right h

/-! ### Interpreted pieces with negative `2R` vanish -/

/-- A family with no pieces at negative `2R`. -/
def NonnegR {E : Type*} [AddCommGroup E] [Module ℂ E] (d : (ℤ × ℤ) × ℂ → Submodule ℂ E) : Prop :=
  ∀ i, i.1.1 < 0 → d i = ⊥

theorem tensorDeg_nonnegR {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] {dV : (ℤ × ℤ) × ℂ → Submodule ℂ V} {dW : (ℤ × ℤ) × ℂ → Submodule ℂ W}
    (hV : NonnegR dV) (hW : NonnegR dW) : NonnegR (tensorDeg dV dW) := by
  intro i hi
  rw [eq_bot_iff]
  refine iSup_le fun b => ?_
  by_cases hb : b.1.1 < 0
  · rw [hV b hb, Submodule.map₂_bot_left]
  · rw [hW (i - b) (by simp only [Prod.fst_sub]; omega), Submodule.map₂_bot_right]

theorem layerDeg_nonnegR {𝒱 : Type*} [AddCommGroup 𝒱] [Module ℂ 𝒱]
    {W : VertexOperatorAlgebra 𝒱} (B : InvariantForm W) (F : GradedFlag W) :
    NonnegR (layerDeg B F) := by
  intro i hi
  rw [eq_bot_iff]
  refine iSup_le fun m => iSup_le fun p => iSup_le fun h => ?_
  subst h
  simp [layerIndex] at hi
  omega

theorem trivialDeg_nonnegR {𝒱 : Type*} [AddCommGroup 𝒱] [Module ℂ 𝒱]
    (W : VertexOperatorAlgebra 𝒱) : NonnegR (trivialDeg W) := by
  intro i hi
  unfold trivialDeg
  rw [if_neg]
  intro h
  rw [h] at hi
  simp at hi

theorem wordR_nonneg (l : SFWord) : 0 ≤ wordR l := by
  induction l with
  | nil => simp [wordR]
  | cons p rest ih =>
      have : wordR (p :: rest) = modeR p + wordR rest := by simp [wordR]
      rw [this]
      have : 0 ≤ modeR p := by unfold modeR; split_ifs <;> norm_num
      omega

theorem fockDeg_nonnegR : NonnegR fockDeg := by
  intro i hi
  rw [fockDeg, basisDeg, eq_bot_iff, Submodule.span_le]
  rintro _ ⟨s, hs, rfl⟩
  exfalso
  have hs' : fockIndex s = i := hs
  have := wordR_nonneg (fockWord s)
  rw [← hs'] at hi
  exact absurd hi (not_lt.mpr this)

theorem brstDeg_nonnegR (w : Finset ModeIdx → ℝ) : NonnegR (brstDeg (ghostRGrading w)) :=
  tensorDeg_nonnegR (tensorDeg_nonnegR (tensorDeg_nonnegR (layerDeg_nonnegR _ _)
    (trivialDeg_nonnegR _)) (layerDeg_nonnegR _ _))
    (tensorDeg_nonnegR (tensorDeg_nonnegR fockDeg_nonnegR fockDeg_nonnegR) fockDeg_nonnegR)

end

end VOA.ConcreteHodge

namespace VOA.ConcreteHodge

open Sl2CosetConcrete Sl2SemiInfinite AffineSl2GeneralRigidity AffineSl2BelowCritical
open VOA.GradedUnitaryCohomology VOA.LeeYangCosetTransfer VOA.VertexOperatorAlgebra
open VOA.LeeYangTransferAssembly LeeYangShortcut VirModule LeeYang
open scoped TensorProduct

noncomputable section

theorem omegaB_relative : omegaB ∈ relativeCarrier leeYangMatterAction.toAffineSl2Action :=
  cosetToComplex_relative _

theorem omegaB_weight : omegaB ∈ brstSVA.grading ((2 : ℤ) : ℂ) :=
  cosetToComplex_mem_weight 2 _ cosetOmegaState_weight

theorem omegaB_even : omegaB ∈ brstSVA.parity 0 := by
  change (cosetOmega ⊗ₜ[ℂ] USVA.vacuum) ⊗ₜ[ℂ] sl2GhostSVA.vacuum ∈
    TensorVA.tenParity matterSVA sl2GhostSVA 0
  refine TensorVA.tmul_mem_tenParity matterSVA sl2GhostSVA (p₁ := 0) ?_ ?_
  · exact TensorVA.tmul_mem_tenParity abSVA USVA (p₁ := 0) cosetOmega_even
      (by simpa using USVA.vacuum_parity)
  · simpa using sl2GhostSVA.vacuum_parity

/-- `Q` commutes with every mode of `ω_C`. -/
theorem Q_omegaB_mode (m : ℤ) (v : BRSTSpace) :
    semiInfiniteQ leeYangMatterAction.toAffineSl2Action (mode (brstSVA.Y omegaB) m v) =
      mode (brstSVA.Y omegaB) m (semiInfiniteQ leeYangMatterAction.toAffineSl2Action v) := by
  have h := semiInfiniteQ_deriv_of_translation leeYangMatterAction matterParityCompatible
    matterGhostTensorGrading omegaB v m
  change semiInfiniteQ leeYangMatterAction.toAffineSl2Action (mode (brstSVA.Y omegaB) m v) =
    mode (brstSVA.Y (semiInfiniteQ leeYangMatterAction.toAffineSl2Action omegaB)) m v +
      mode (brstSVA.Y (BRST.sgn brstSVA omegaB)) m
        (semiInfiniteQ leeYangMatterAction.toAffineSl2Action v) at h
  have hQ : semiInfiniteQ leeYangMatterAction.toAffineSl2Action omegaB = 0 :=
    cosetToComplex_closed cosetOmegaState
  have hs : BRST.sgn brstSVA omegaB = omegaB := by
    rw [BRST.sgn_homog omegaB_even, parSign_zero, one_smul]
  have h0 : mode (brstSVA.Y (0 : BRSTSpace)) m v = 0 := by
    rw [map_zero]; rfl
  rw [hQ, hs, h0] at h
  exact h.trans (zero_add _)

theorem omegaB_mode_relative (m : ℤ) {v : BRSTSpace}
    (hv : v ∈ relativeCarrier leeYangMatterAction.toAffineSl2Action) :
    mode (brstSVA.Y omegaB) m v ∈ relativeCarrier leeYangMatterAction.toAffineSl2Action :=
  relativeCarrier_mode leeYangMatterAction.toAffineSl2Action leeYangMatterAction.translation
    matterParityCompatible matterGhostTensorGrading omegaB_relative hv m

/-- The creation operator `L_{-i-2}` of the coset, on relative weight spaces. -/
def creationOp (n : ℤ) (i : ℕ) : relativeWeight n →ₗ[ℂ] relativeWeight (n + i + 2) :=
  (mode (brstSVA.Y omegaB) (-(i : ℤ) - 1)).restrict (fun v hv => by
    refine ⟨omegaB_mode_relative _ hv.1, ?_⟩
    have h := brstSVA.grading_mode omegaB omegaB_weight v hv.2 (-(i : ℤ) - 1)
    show _ ∈ brstSVA.grading (((n + i + 2 : ℤ)) : ℂ)
    rw [show (((n + i + 2 : ℤ)) : ℂ) = ((2 : ℤ) : ℂ) + (n : ℂ) - ((-(i : ℤ) - 1 : ℤ) : ℂ) - 1 by
      push_cast; ring]
    exact h)

theorem creationOp_coe (n : ℤ) (i : ℕ) (v : relativeWeight n) :
    (creationOp n i v : BRSTSpace) = mode (brstSVA.Y omegaB) (-(i : ℤ) - 1) v := rfl

theorem creationOp_D (n : ℤ) (i : ℕ) (v : relativeWeight n) :
    relativeDifferential (n + i + 2) (creationOp n i v) =
      creationOp n i (relativeDifferential n v) := by
  apply Subtype.ext
  simp only [relativeDifferential_coe, creationOp_coe]
  have h := Q_omegaB_mode (-(i : ℤ) - 1) (v : BRSTSpace)
  rw [← leeYangBRSTComplex_Q] at h
  exact h

/-- The representative of a Virasoro creation is the coset creation of the representative. -/
theorem representative_creation (n : ℤ) (i : ℕ) (x : UniversalWeight n) :
    universalWeightRepresentative (n + i + 2) (universalCreation n i x) =
      creationOp n i (universalWeightRepresentative n x) := by
  apply Subtype.ext
  rw [creationOp_coe]
  change cosetToComplex (virasoroToCoset (Lop leeYangC (-(i : ℤ) - 2) x)) =
    mode (brstSVA.Y omegaB) (-(i : ℤ) - 1) (cosetToComplex (virasoroToCoset x))
  rw [show virasoroToCoset (Lop leeYangC (-(i : ℤ) - 2) x) =
    cosetVOA.L (-(i : ℤ) - 2) (virasoroToCoset x) from conformalEval_L cosetVOA rfl _ _]
  rw [VertexOperatorAlgebra.L_def, show -(i : ℤ) - 2 + 1 = -(i : ℤ) - 1 by ring,
    ← PreVertexAlgebra.smul_def, cosetVOA_mode, cosetToComplex_mode]
  rfl

end

end VOA.ConcreteHodge

namespace VOA.ConcreteHodge

open Sl2CosetConcrete Sl2SemiInfinite AffineSl2GeneralRigidity AffineSl2BelowCritical
open VOA.GradedUnitaryCohomology VOA.LeeYangCosetTransfer VOA.VertexOperatorAlgebra
open VOA.LeeYangTransferAssembly LeeYangShortcut VirModule LeeYang
open scoped TensorProduct

noncomputable section

section Creation

variable (w : Finset ModeIdx → ℝ) (hw : ∀ s, 0 < w s)
  (hA : GradedUnitary affineForm affineRealStructure affineFlag)
  {BB : InvariantForm BVOA} {RB : RealStructure BVOA} (hB : Unitary BB RB)

/-- Supports in the row set `0 ≤ 2R ≤ 2p`, ghost number `0`. -/
def RowPred (p : ℕ) (k : (ℤ × ℤ) × ℂ) : Prop := k.1.1 ≤ 2 * (p : ℤ) ∧ k.1.2 = 0

/-- A vector of the model at weight `n` supported on rows `≤ 2p` lies in the corresponding
interpreted pieces. -/
theorem degOn_to_brst (hZ : ZeroModesPreserve (ghostRGrading w))
    (hD : RelativeDifferentialGood (ghostRGrading w))
    (hK : InterpretedKahlerAnticomm (ghostRGrading w) hA hB (ghostPos w hw) hZ hD)
    (n : ℤ) (hp : IsPosOn ((interpretedKahler (ghostRGrading w) hA hB (ghostPos w hw) hZ hD hK).geometry n).P ⊤)
    (p : ℕ) (c : relativeWeight n)
    (hc : c ∈ ((interpretedKahler (ghostRGrading w) hA hB (ghostPos w hw) hZ hD hK).model n hp).degOn
      (KahlerComplex.rowSet (Finset.Icc 0 (2 * (p : ℤ))) 0)) :
    (c : BRSTSpace) ∈ ⨆ (k : (ℤ × ℤ) × ℂ) (_ : RowPred p k), brstDeg (ghostRGrading w) k := by
  refine Submodule.iSup_induction _ (motive := fun c : relativeWeight n =>
    (c : BRSTSpace) ∈ ⨆ (k : (ℤ × ℤ) × ℂ) (_ : RowPred p k), brstDeg (ghostRGrading w) k)
    hc ?_ (by simp) (fun x y hx hy => by
      beta_reduce at hx hy ⊢; rw [Submodule.coe_add]; exact Submodule.add_mem _ hx hy)
  rintro ⟨a, ha⟩ y hy
  have hy' : (y : BRSTSpace) ∈ brstDeg (ghostRGrading w) (a, (n : ℂ)) := hy
  obtain ⟨ha1, ha2⟩ := ha
  exact Submodule.mem_iSup_of_mem (a, (n : ℂ))
    (Submodule.mem_iSup_of_mem ⟨(Finset.mem_Icc.mp ha1).2, ha2⟩ hy')

theorem creation_shift (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    (p : ℕ) (j : ℤ) {v : BRSTSpace}
    (hv : v ∈ ⨆ (k : (ℤ × ℤ) × ℂ) (_ : RowPred p k), brstDeg (ghostRGrading w) k) :
    brstSVA.Y omegaB j v ∈
      ⨆ (k : (ℤ × ℤ) × ℂ) (_ : RowPred (p + 1) k), brstDeg (ghostRGrading w) k := by
  refine Submodule.iSup_induction _ (motive := fun v => brstSVA.Y omegaB j v ∈
      ⨆ (k : (ℤ × ℤ) × ℂ) (_ : RowPred (p + 1) k), brstDeg (ghostRGrading w) k)
    hv ?_ (by simp) (fun x y hx hy => by
      beta_reduce at hx hy ⊢; rw [map_add]; exact Submodule.add_mem _ hx hy)
  intro k y hy
  refine Submodule.iSup_induction _ (motive := fun v => brstSVA.Y omegaB j v ∈
      ⨆ (k : (ℤ × ℤ) × ℂ) (_ : RowPred (p + 1) k), brstDeg (ghostRGrading w) k)
    hy ?_ (by simp) (fun x y hx hy => by
      beta_reduce at hx hy ⊢; rw [map_add]; exact Submodule.add_mem _ hx hy)
  intro hk y hy
  have h := omegaB_shifts hA w j k y hy
  refine (iSup_le fun δ => iSup_le fun hδ => ?_ :
    shiftTarget (brstDeg (ghostRGrading w)) UpTwo k ≤ _) h
  refine le_iSup_of_le (k + δ) (le_iSup_of_le ⟨?_, ?_⟩ le_rfl)
  · simp only [Prod.fst_add]; push_cast; have := hk.1; have := hδ.2; omega
  · simp only [Prod.fst_add, Prod.snd_add, hk.2, hδ.1, add_zero]

/-- From interpreted pieces back to the model's `degOn`, inside a relative weight space. -/
theorem brst_to_degOn (hZ : ZeroModesPreserve (ghostRGrading w))
    (hD : RelativeDifferentialGood (ghostRGrading w))
    (hK : InterpretedKahlerAnticomm (ghostRGrading w) hA hB (ghostPos w hw) hZ hD)
    (n : ℤ) (hp : IsPosOn ((interpretedKahler (ghostRGrading w) hA hB (ghostPos w hw) hZ hD hK).geometry n).P ⊤)
    (p : ℕ) (v : relativeWeight n)
    (hv : (v : BRSTSpace) ∈ ⨆ (k : (ℤ × ℤ) × ℂ) (_ : RowPred p k),
      brstDeg (ghostRGrading w) k) :
    v ∈ ((interpretedKahler (ghostRGrading w) hA hB (ghostPos w hw) hZ hD hK).model n hp).degOn
      (KahlerComplex.rowSet (Finset.Icc 0 (2 * (p : ℤ))) 0) := by
  classical
  have hI := brstDeg_isInternal (ghostRGrading w) hA hB (ghostPos w hw)
  have hstab := relativeWeight_stable (ghostRGrading w) hA hB (ghostPos w hw) hZ n
  have hzero := (mem_iSup_pred_iff hI _ _).mp hv
  obtain ⟨s, hs⟩ := sum_iproj hI (v : BRSTSpace)
  have hv' : v = ∑ k ∈ s, (⟨iproj hI k v, hstab k v v.2⟩ : relativeWeight n) := by
    apply Subtype.ext; rw [Submodule.coe_sum]; exact hs.symm
  rw [hv']
  refine Submodule.sum_mem _ fun k _ => ?_
  by_cases hk : RowPred p k ∧ k.2 = (n : ℂ) ∧ 0 ≤ k.1.1
  · obtain ⟨⟨hk1, hk2⟩, hk3, hk4⟩ := hk
    refine KahlerComplex.deg_le_degOn _ (a := k.1)
      (show k.1 ∈ KahlerComplex.rowSet (Finset.Icc 0 (2 * (p : ℤ))) 0 from
        ⟨Finset.mem_Icc.mpr ⟨hk4, hk1⟩, hk2⟩) ?_
    change iproj hI k v ∈ brstDeg (ghostRGrading w) (k.1, (n : ℂ))
    rw [← hk3]
    exact iproj_mem hI k _
  · have h0 : iproj hI k (v : BRSTSpace) = 0 := by
      by_cases h1 : RowPred p k
      · by_cases h2 : k.2 = (n : ℂ)
        · have h3 : k.1.1 < 0 := by
            by_contra h3; exact hk ⟨h1, h2, not_lt.mp h3⟩
          have := iproj_mem hI k (v : BRSTSpace)
          rwa [brstDeg_nonnegR w k h3, Submodule.mem_bot] at this
        · exact iproj_eq_zero_of_weight hI brstSVA.isInternal wtIndex
            (brstDeg_le_weight (ghostRGrading w)) v.2.2 h2
      · exact hzero k h1
    have : (⟨iproj hI k v, hstab k v v.2⟩ : relativeWeight n) = 0 := Subtype.ext h0
    rw [this]; exact Submodule.zero_mem _

/-- Generic transport of the class filtration along a chain map that maps supports into
supports. -/
theorem cohomFilt_transport {K K' : Type*} [AddCommGroup K] [Module ℂ K] [AddCommGroup K']
    [Module ℂ K'] (C : KahlerComplex K) (C' : KahlerComplex K') (Λ : K →ₗ[ℂ] K')
    (hΛ : ∀ v, C'.D (Λ v) = Λ (C.D v)) (A A' : Set (ℤ × ℤ))
    (hdeg : ∀ v, v ∈ C.degOn A → Λ v ∈ C'.degOn A') (u : LinearMap.ker C.D)
    (u' : LinearMap.ker C'.D) (hu : (u' : K') = Λ u)
    (hmem : (boundariesInCycles C.D).mkQ u ∈ C.cohomFilt A) :
    (boundariesInCycles C'.D).mkQ u' ∈ C'.cohomFilt A' := by
  obtain ⟨c, hcdeg, hceq⟩ := Submodule.mem_map.mp hmem
  obtain ⟨z, hz⟩ := (Submodule.Quotient.eq _).mp hceq
  have hcD : C.D (c : K) = 0 := c.2
  have hc'D : Λ (c : K) ∈ LinearMap.ker C'.D := by
    rw [LinearMap.mem_ker, hΛ, hcD, map_zero]
  refine Submodule.mem_map.mpr ⟨⟨Λ c, hc'D⟩, hdeg _ hcdeg, ?_⟩
  apply (Submodule.Quotient.eq _).mpr
  refine ⟨Λ z, ?_⟩
  rw [hΛ, hz]
  change Λ ((c : K) - (u : K)) = Λ (c : K) - (u' : K')
  rw [map_sub, hu]

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
-- Instance search on the cycle spaces of the concrete Kähler model is slow.
/-- **`InterpretedCreation` holds**: the Virasoro creation operators raise the class
filtration of the actual relative cohomology by at most one. -/
theorem interpretedCreation_proved (hZ : ZeroModesPreserve (ghostRGrading w))
    (hD : RelativeDifferentialGood (ghostRGrading w))
    (hK : InterpretedKahlerAnticomm (ghostRGrading w) hA hB (ghostPos w hw) hZ hD)
    (hp : ∀ n, IsPosOn
      ((interpretedKahler (ghostRGrading w) hA hB (ghostPos w hw) hZ hD hK).geometry n).P ⊤) :
    InterpretedCreation w hw hA hB hZ hD hK hp := by
  intro n p i x hx
  set S := interpretedKahler (ghostRGrading w) hA hB (ghostPos w hw) hZ hD hK
  have hDn := S.model_D n (hp n)
  have hDn' := S.model_D (n + i + 2) (hp (n + i + 2))
  refine cohomFilt_transport (S.model n (hp n)) (S.model (n + i + 2) (hp (n + i + 2)))
    (creationOp n i) (fun v => ?_) _ _ (fun v hv => ?_) _ _ ?_ hx
  · rw [LinearMap.congr_fun hDn', LinearMap.congr_fun hDn, creationOp_D]
  · have h1 := degOn_to_brst w hw hA hB hZ hD hK n (hp n) p v hv
    have h2 := creation_shift w hA p (-(-(i : ℤ) - 1) - 1) h1
    have h3 := brst_to_degOn w hw hA hB hZ hD hK (n + i + 2) (hp (n + i + 2)) (p + 1)
      (creationOp n i v) (by rw [creationOp_coe, mode_apply]; exact h2)
    simpa only [Nat.cast_add, Nat.cast_one] using h3
  · have h1 : ((modelUniversalCycles S n (hp n) x : LinearMap.ker (S.model n (hp n)).D) :
        relativeWeight n) = universalWeightRepresentative n x := cyclesCongr_coe _ _ _ _
    have h2 : ((modelUniversalCycles S (n + i + 2) (hp (n + i + 2)) (universalCreation n i x) :
        LinearMap.ker (S.model (n + i + 2) (hp (n + i + 2))).D) : relativeWeight (n + i + 2)) =
        universalWeightRepresentative (n + i + 2) (universalCreation n i x) :=
      cyclesCongr_coe _ _ _ _
    rw [h1, h2]
    exact representative_creation n i x

end Creation

end

end VOA.ConcreteHodge

namespace VOA.ConcreteHodge

open LeeYangTransferAssembly LeeYangShortcut Sl2CosetConcrete Sl2SemiInfinite
open VirGradedUnitarity LeeYang VOA.VertexOperatorAlgebra VOA.GradedUnitaryCohomology

noncomputable section

/-- **Affine GU ⇒ Lee–Yang GU**, with the zero-mode statements, Beem–Garner goodness of the
actual differential and the creation test all proved. `#print axioms`-clean, conditional on:
`hA` (the hypothesis), `hB`, a positive ghost weight `w`, the Kähler relation `hK`, and the
downstream inputs `R`, `symbols`, `character`, `vacuumNormalized`, `creationAdjoint`,
`wordsReal`. -/
theorem leeYang_gradedUnitary_of_affine_kahler
    (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    {BB : InvariantForm BVOA} {RB : RealStructure BVOA} (hB : Unitary BB RB)
    (w : Finset ModeIdx → ℝ) (hw : ∀ s, 0 < w s)
    (hK : InterpretedKahlerAnticomm (ghostRGrading w) hA hB (ghostPos w hw) (hZproved w)
      (relativeDifferentialGood_of_affine hA hB w hw))
    (R : ∀ n hp, GoodComplex.ConjData (concreteGood (interpretedGoodGeometry (ghostRGrading w)
      hA hB (ghostPos w hw) (hZproved w) (relativeDifferentialGood_of_affine hA hB w hw) hK)
        n hp))
    (symbols : LeadingInvariantSymbolDimension (interpretedKahler (ghostRGrading w) hA hB
      (ghostPos w hw) (hZproved w) (relativeDifferentialGood_of_affine hA hB w hw) hK))
    (character : LeeYangPBWCharacter)
    (vacuumNormalized : HarmonicVacuumNormalized (interpretedKahler (ghostRGrading w) hA hB
      (ghostPos w hw) (hZproved w) (relativeDifferentialGood_of_affine hA hB w hw) hK)
        (concreteGUData _ R))
    (creationAdjoint : HarmonicCreationAdjoint (interpretedKahler (ghostRGrading w) hA hB
      (ghostPos w hw) (hZproved w) (relativeDifferentialGood_of_affine hA hB w hw) hK)
        (concreteGUData _ R))
    (wordsReal : HarmonicWordsReal (interpretedKahler (ghostRGrading w) hA hB
      (ghostPos w hw) (hZproved w) (relativeDifferentialGood_of_affine hA hB w hw) hK)
        (concreteGUData _ R)) :
    VirGradedUnitary leeYangC leeYangRealStructure :=
  leeYang_gradedUnitary_of_affine_good hA hB w hw hK R symbols character
    (fun hp => interpretedCreation_proved w hw hA hB _ _ hK hp)
    vacuumNormalized creationAdjoint wordsReal

end

end VOA.ConcreteHodge
