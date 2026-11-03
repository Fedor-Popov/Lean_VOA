/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.BGPackageTensor

/-!
# The matter factor of the Beem–Garner data

The modified carrier form of a graded-unitary factor is the layer-orthogonal sum of `(-1)^p h`,
with `h(x, y) = B(ρx, y)`. Beem–Garner's identity `P = i^{2R} B(ρ ·, ·)` on a layer needs that
**distinct layers are `h`-orthogonal**, which is not part of graded unitarity. It holds as soon as
`ρ` preserves the flag, `B` is symmetric and `ρ`-real, and `ρ² = 1` (`layer_h_orth`): for `p < q`
use that the `q`-th layer is bilinear-orthogonal to `G_{q-1} ∋ ρx`; for `p > q` use symmetry and
that `ρ` preserves the `p`-th layer.

* `CompactLayerData B R F` — these four hypotheses; `CompactLayerData.layerDeg_P_eq` and
  `CompactLayerData.layerDeg_rho` (generic, any VOA);
* `trivialDeg_P_eq`, `trivialDeg_rho` — the unitary factor with the trivial grading (no
  hypotheses);
* `affineCompactLayerData` — **compact conjugation preserves the corrected flag** of
  `L_{-4/3}(sl₂)` (it maps every corrected generator word to `±` a word of the same length) and
  the remaining hypotheses, all proved; `auxiliaryCompactLayerData` for the auxiliary factor.

Everything is proved outright from the listed hypotheses.
-/

namespace VOA.ConcreteHodge

open Sl2CosetConcrete Sl2SemiInfinite AffineSl2GeneralRigidity AffineSl2BelowCritical
open VOA.GradedUnitaryCohomology VOA.LeeYangCosetTransfer VOA.VertexOperatorAlgebra
open VOA.LeeYangTransferAssembly LeeYangShortcut VirModule LeeYang VirGradedUnitarity
open AffineVOA
open scoped TensorProduct

noncomputable section

/-! ### Generic: the layer identity -/

section GenericLayer

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

/-- **Compactness hypotheses for the layer identity**: `ρ` preserves the flag, `B` is `ρ`-real
and symmetric, `ρ² = 1`. -/
structure CompactLayerData (B : InvariantForm W) (R : RealStructure W) (F : GradedFlag W) :
    Prop where
  flag : ∀ (p : ℕ) (n : ℤ), ∀ x ∈ F.piece p n, R.rho x ∈ F.piece p n
  conj : ∀ a b : 𝒱, B.form (R.rho a) (R.rho b) = (starRingEnd ℂ) (B.form a b)
  symm : B.IsSymmetric
  sq : ∀ x : 𝒱, R.rho (R.rho x) = x

namespace CompactLayerData

/-- `ρ` on one weight space. -/
def rhoW (R : RealStructure W) (n : ℤ) (x : W.grading n) : W.grading n :=
  ⟨R.rho x, realStructure_mem_grading R x.2⟩

theorem rhoW_coe (R : RealStructure W) (n : ℤ) (x : W.grading n) :
    (rhoW R n x : 𝒱) = R.rho x := rfl

theorem I_zpow_two_mul (p : ℕ) : Complex.I ^ (2 * (p : ℤ)) = (-1 : ℂ) ^ p := by
  rw [zpow_mul, zpow_two, Complex.I_mul_I, zpow_natCast]

variable {B : InvariantForm W} {R : RealStructure W} {F : GradedFlag W}
  (hC : CompactLayerData B R F)
include hC

theorem rho_pieceLT {p : ℕ} {n : ℤ} {z : W.grading n} (hz : z ∈ F.pieceLT p n) :
    rhoW R n z ∈ F.pieceLT p n := by
  cases p with
  | zero =>
      rw [GradedFlag.pieceLT_zero, Submodule.mem_bot] at hz ⊢
      subst hz
      exact Subtype.ext (by rw [rhoW_coe]; exact R.map_zero)
  | succ q =>
      rw [GradedFlag.pieceLT_succ] at hz ⊢
      exact hC.flag q n _ hz

/-- `ρ` preserves every layer. -/
theorem rho_layer {p : ℕ} {n : ℤ} {x : W.grading n}
    (hx : x ∈ F.layer n (LiRadical.gradedForm B n) p) :
    rhoW R n x ∈ F.layer n (LiRadical.gradedForm B n) p := by
  refine ⟨hC.flag p n _ hx.1, ?_⟩
  change rhoW R n x ∈ (LiRadical.gradedForm B n).orthogonal (F.pieceLT p n)
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  intro z hz
  rw [LinearMap.BilinForm.isOrtho_def, LiRadical.gradedForm_apply, rhoW_coe]
  have h1 : x ∈ (LiRadical.gradedForm B n).orthogonal (F.pieceLT p n) := hx.2
  rw [LinearMap.BilinForm.mem_orthogonal_iff] at h1
  have h2 := h1 _ (hC.rho_pieceLT hz)
  rw [LinearMap.BilinForm.isOrtho_def, LiRadical.gradedForm_apply, rhoW_coe] at h2
  rw [← hC.sq (z : 𝒱), hC.conj, h2, map_zero]

/-- **Distinct layers are `h`-orthogonal.** -/
theorem layer_h_orth {n : ℤ} {p q : ℕ} (hpq : p ≠ q) {x y : W.grading n}
    (hx : x ∈ F.layer n (LiRadical.gradedForm B n) p)
    (hy : y ∈ F.layer n (LiRadical.gradedForm B n) q) :
    B.form (R.rho x) y = 0 := by
  rcases Nat.lt_or_gt_of_ne hpq with h | h
  · have hρx : rhoW R n x ∈ F.pieceLT q n := pieceIn_le_pieceLT F h n (hC.flag p n _ hx.1)
    have h1 : y ∈ (LiRadical.gradedForm B n).orthogonal (F.pieceLT q n) := hy.2
    rw [LinearMap.BilinForm.mem_orthogonal_iff] at h1
    have h2 := h1 _ hρx
    rwa [LinearMap.BilinForm.isOrtho_def, LiRadical.gradedForm_apply, rhoW_coe] at h2
  · have hyl : y ∈ F.pieceLT p n := pieceIn_le_pieceLT F h n hy.1
    have h1 : rhoW R n x ∈ (LiRadical.gradedForm B n).orthogonal (F.pieceLT p n) :=
      (hC.rho_layer hx).2
    rw [LinearMap.BilinForm.mem_orthogonal_iff] at h1
    have h2 := h1 _ hyl
    rw [LinearMap.BilinForm.isOrtho_def, LiRadical.gradedForm_apply, rhoW_coe] at h2
    rw [hC.symm]
    exact h2

/-- **The layer identity** `P = i^{2R} B(ρ ·, ·)` on every layer piece. -/
theorem layerDeg_P_eq (hGU : GradedUnitary B R F) (hrefl : GramRefl B)
    (i : (ℤ × ℤ) × ℂ) (x : 𝒱) (hx : x ∈ layerDeg B F i) (y : 𝒱) :
    carrierForm B R F hGU hrefl x y = Complex.I ^ i.1.1 * B.form (R.rho x) y := by
  refine Submodule.iSup_induction _ (motive := fun x =>
    carrierForm B R F hGU hrefl x y = Complex.I ^ i.1.1 * B.form (R.rho x) y) hx ?_
    (by beta_reduce; rw [SesqForm.zero_left, R.map_zero, map_zero, LinearMap.zero_apply, mul_zero])
    (fun a b ha hb => by
      beta_reduce at ha hb ⊢
      rw [SesqForm.add_left, ha, hb, R.map_add, map_add, LinearMap.add_apply, mul_add])
  intro m x hx
  refine Submodule.iSup_induction _ (motive := fun x =>
    carrierForm B R F hGU hrefl x y = Complex.I ^ i.1.1 * B.form (R.rho x) y) hx ?_
    (by beta_reduce; rw [SesqForm.zero_left, R.map_zero, map_zero, LinearMap.zero_apply, mul_zero])
    (fun a b ha hb => by
      beta_reduce at ha hb ⊢
      rw [SesqForm.add_left, ha, hb, R.map_add, map_add, LinearMap.add_apply, mul_add])
  intro p x hx
  refine Submodule.iSup_induction _ (motive := fun x =>
    carrierForm B R F hGU hrefl x y = Complex.I ^ i.1.1 * B.form (R.rho x) y) hx ?_
    (by beta_reduce; rw [SesqForm.zero_left, R.map_zero, map_zero, LinearMap.zero_apply, mul_zero])
    (fun a b ha hb => by
      beta_reduce at ha hb ⊢
      rw [SesqForm.add_left, ha, hb, R.map_add, map_add, LinearMap.add_apply, mul_add])
  intro hi x hx
  obtain ⟨x', hx', rfl⟩ := Submodule.mem_map.mp hx
  subst hi
  have hy : y ∈ ⨆ n, W.grading n := by
    rw [W.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
  refine Submodule.iSup_induction _ (motive := fun y =>
    carrierForm B R F hGU hrefl ((W.grading m).subtype x') y =
      Complex.I ^ (layerIndex p m).1.1 * B.form (R.rho ((W.grading m).subtype x')) y) hy ?_
    (by beta_reduce; rw [SesqForm.zero_right, map_zero, mul_zero])
    (fun a b ha hb => by
      beta_reduce at ha hb ⊢
      rw [SesqForm.add_right, ha, hb, map_add, mul_add])
  intro n y hy
  simp only [Submodule.subtype_apply]
  by_cases hmn : m = n
  · subst hmn
    rw [carrierForm_weight_same B R F hGU hrefl x'.2 hy]
    haveI := W.finrank m
    have := modForm_eq_signed_of_orth F m (gradedSesq B R m) (hrefl m) (hGU m).1
      (fun p q hpq x hx y hy => by
        rw [gradedSesq_apply]; exact hC.layer_h_orth hpq hx hy) hx' ⟨y, hy⟩
    change weightModForm B R F hGU hrefl m x' ⟨y, hy⟩ = _
    unfold weightModForm
    rw [this, gradedSesq_apply, I_zpow_two_mul]
  · rw [carrierForm_weight_ne B R F hGU hrefl hmn x'.2 hy,
      B.orthogonal_of_ne hmn (realStructure_mem_grading R x'.2) hy, mul_zero]

/-- `ρ` preserves every layer piece. -/
theorem layerDeg_rho (i : (ℤ × ℤ) × ℂ) (x : 𝒱) (hx : x ∈ layerDeg B F i) :
    R.rho x ∈ layerDeg B F i := by
  refine Submodule.iSup_induction _ (motive := fun x => R.rho x ∈ layerDeg B F i) hx ?_
    (by beta_reduce; rw [R.map_zero]; exact Submodule.zero_mem _)
    (fun a b ha hb => by beta_reduce at ha hb ⊢; rw [R.map_add]; exact Submodule.add_mem _ ha hb)
  intro m x hx
  refine Submodule.iSup_induction _ (motive := fun x => R.rho x ∈ layerDeg B F i) hx ?_
    (by beta_reduce; rw [R.map_zero]; exact Submodule.zero_mem _)
    (fun a b ha hb => by beta_reduce at ha hb ⊢; rw [R.map_add]; exact Submodule.add_mem _ ha hb)
  intro p x hx
  refine Submodule.iSup_induction _ (motive := fun x => R.rho x ∈ layerDeg B F i) hx ?_
    (by beta_reduce; rw [R.map_zero]; exact Submodule.zero_mem _)
    (fun a b ha hb => by beta_reduce at ha hb ⊢; rw [R.map_add]; exact Submodule.add_mem _ ha hb)
  intro hi x hx
  obtain ⟨x', hx', rfl⟩ := Submodule.mem_map.mp hx
  exact Submodule.mem_iSup_of_mem m (Submodule.mem_iSup_of_mem p (Submodule.mem_iSup_of_mem hi
    (Submodule.mem_map.mpr ⟨rhoW R m x', hC.rho_layer hx', rfl⟩)))

end CompactLayerData

/-! ### The trivial grading -/

theorem trivialDeg_P_eq (B : InvariantForm W) (R : RealStructure W) (i : (ℤ × ℤ) × ℂ) (x : 𝒱)
    (hx : x ∈ trivialDeg W i) (y : 𝒱) :
    unitaryCarrierForm B R x y = Complex.I ^ i.1.1 * B.form (R.rho x) y := by
  unfold trivialDeg at hx
  split_ifs at hx with h
  · rw [h]
    simp only [zpow_zero, one_mul]
    by_cases hint : ∃ m : ℤ, (m : ℂ) = i.2
    · obtain ⟨m, hm⟩ := hint
      rw [← hm, PreVertexAlgebra.gradingC_intCast] at hx
      change x ∈ W.grading m at hx
      have hy : y ∈ ⨆ n, W.grading n := by
        rw [W.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
      refine Submodule.iSup_induction _ (motive := fun y =>
        unitaryCarrierForm B R x y = B.form (R.rho x) y) hy ?_
        (by beta_reduce; rw [SesqForm.zero_right, map_zero])
        (fun a b ha hb => by
          beta_reduce at ha hb ⊢; rw [SesqForm.add_right, ha, hb, map_add])
      intro n y hy
      by_cases hmn : m = n
      · subst hmn
        rw [unitaryCarrierForm, internalForm_of_mem_same _ _ hx hy, gradedSesq_apply]
      · rw [unitaryCarrierForm, internalForm_of_mem_ne _ _ hmn hx hy,
          B.orthogonal_of_ne hmn (realStructure_mem_grading R hx) hy]
    · rw [PreVertexAlgebra.gradingC_of_not_int _ hint, Submodule.mem_bot] at hx
      rw [hx, SesqForm.zero_left, R.map_zero, map_zero, LinearMap.zero_apply]
  · rw [Submodule.mem_bot] at hx
    rw [hx, SesqForm.zero_left, R.map_zero, map_zero, LinearMap.zero_apply, mul_zero]

theorem trivialDeg_rho (R : RealStructure W) (i : (ℤ × ℤ) × ℂ) (x : 𝒱)
    (hx : x ∈ trivialDeg W i) : R.rho x ∈ trivialDeg W i := by
  unfold trivialDeg at hx ⊢
  split_ifs at hx ⊢ with h
  · by_cases hint : ∃ m : ℤ, (m : ℂ) = i.2
    · obtain ⟨m, hm⟩ := hint
      rw [← hm, PreVertexAlgebra.gradingC_intCast] at hx ⊢
      exact realStructure_mem_grading R hx
    · rw [PreVertexAlgebra.gradingC_of_not_int _ hint, Submodule.mem_bot] at hx ⊢
      rw [hx, R.map_zero]
  · rw [Submodule.mem_bot] at hx ⊢
    rw [hx, R.map_zero]

end GenericLayer

/-! ### Compact conjugation preserves the corrected flag -/

section Corrected

open CorrectedR

variable {k : ℂ} {hk : k + 2 ≠ 0} {R : RealStructure (universal k hk)}
  (hR : IsCompactRealStructure R)
include hR

theorem rho_generatorState (g : Generator) :
    R.rho (generatorState k hk g) = generatorState k hk g ∨
      ∃ g' : Generator, R.rho (generatorState k hk g) = -generatorState k hk g' := by
  cases g with
  | current a => exact Or.inr ⟨.current (AffineVOA.HighestModule.adjointColour a), hR.current a⟩
  | sugawara => exact Or.inl R.map_omega

omit hR in
theorem smul_generator_mem (g : Generator) (r : ℕ) {q : ℕ} {v : WakModule k}
    (hv : v ∈ correctedAffineRPiece k hk q) :
    (affineSl2VOA_closed k hk).smul (generatorState k hk g) (-(r : ℤ) - 1) v ∈
      correctedAffineRPiece k hk (q + 1) := by
  induction hv using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨⟨w, hw⟩, rfl⟩ := hz
      rw [← correctedWordState_cons k hk (g, r) w]
      exact Submodule.subset_span ⟨⟨(g, r) :: w, by simp; omega⟩, rfl⟩
  | zero => rw [PreVertexAlgebra.smul_zero_right]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [PreVertexAlgebra.smul_add_right]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [PreVertexAlgebra.smul_smul_right]; exact Submodule.smul_mem _ _ hx

theorem rho_correctedWordState (w : List (Generator × ℕ)) :
    R.rho (correctedWordState k hk w) ∈ correctedAffineRPiece k hk w.length := by
  induction w with
  | nil =>
      rw [correctedWordState_nil]
      have h := R.map_vacuum
      change R.rho (affineSl2VOA_closed k hk).vacuum = (affineSl2VOA_closed k hk).vacuum at h
      rw [h]
      exact Submodule.subset_span ⟨⟨[], le_rfl⟩, rfl⟩
  | cons gr rest ih =>
      rw [correctedWordState_cons]
      have hs := R.map_smul (generatorState k hk gr.1) (-(gr.2 : ℤ) - 1)
        (correctedWordState k hk rest)
      change R.rho ((affineSl2VOA_closed k hk).smul _ _ _) =
        (affineSl2VOA_closed k hk).smul _ _ _ at hs
      rw [hs, List.length_cons]
      rcases rho_generatorState hR gr.1 with h | ⟨g', h⟩
      · rw [h]; exact smul_generator_mem gr.1 gr.2 ih
      · rw [h, show -generatorState k hk g' = (-1 : ℂ) • generatorState k hk g' by simp,
          PreVertexAlgebra.smul_smul_left]
        exact Submodule.smul_mem _ _ (smul_generator_mem g' gr.2 ih)

/-- **Compact conjugation preserves the corrected filtration.** -/
theorem rho_correctedPiece {p : ℕ} {x : WakModule k} (hx : x ∈ correctedAffineRPiece k hk p) :
    R.rho x ∈ correctedAffineRPiece k hk p := by
  induction hx using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨⟨w, hw⟩, rfl⟩ := hz
      exact correctedAffineRPiece_mono k hk hw (rho_correctedWordState hR w)
  | zero => rw [R.map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [R.map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [R.antilinear]; exact Submodule.smul_mem _ _ hx

end Corrected

/-! ### The affine factor -/

private theorem affineConj_apply_mkQ (x : WakModule ALevel) :
    affineRealStructure.rho ((QuotVOA.maxGradedIdeal (universal ALevel aNoncritical)).mkQ x) =
      (QuotVOA.maxGradedIdeal (universal ALevel aNoncritical)).mkQ
        ((compactRealStructure affineLevel_real aNoncritical).rho x) := rfl

/-- **The compactness hypotheses for `L_{-4/3}(sl₂)`**, all proved. -/
theorem affineCompactLayerData :
    CompactLayerData affineForm affineRealStructure affineFlag where
  flag p n x hx := by
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
    rw [affineConj_apply_mkQ]
    have hR := compactRealStructure_isCompact affineLevel_real aNoncritical
    exact Submodule.mem_map_of_mem ⟨rho_correctedPiece hR hy.1, hR.rho_mem_grading hy.2⟩
  conj a b := by
    obtain ⟨a, rfl⟩ := (QuotVOA.maxGradedIdeal (universal ALevel aNoncritical)).mkQ_surjective a
    obtain ⟨b, rfl⟩ := (QuotVOA.maxGradedIdeal (universal ALevel aNoncritical)).mkQ_surjective b
    rw [affineConj_apply_mkQ, affineConj_apply_mkQ]
    change (simpleForm ALevel aNoncritical).form _ _ =
      (starRingEnd ℂ) ((simpleForm ALevel aNoncritical).form _ _)
    rw [simpleForm_mkQ, simpleForm_mkQ]
    have h := universalForm_compactRho aNoncritical (hreal := affineLevel_real) a b
    rw [← h, Complex.conj_conj]
    rfl
  symm := simpleForm_isSymmetric ALevel aNoncritical
  sq x := by
    obtain ⟨x, rfl⟩ := (QuotVOA.maxGradedIdeal (universal ALevel aNoncritical)).mkQ_surjective x
    rw [affineConj_apply_mkQ, affineConj_apply_mkQ]
    exact congrArg _ (compactRho_compactRho affineLevel_real x)

/-- **The compactness hypotheses for the auxiliary factor**, all proved. -/
theorem auxiliaryCompactLayerData :
    CompactLayerData auxiliaryForm auxiliaryRealStructure auxiliaryFlag where
  flag p n x hx :=
    (compactRealStructure_isCompact auxiliaryLevel_real uNoncritical).rho_mem_ordinaryFlag hx
  conj a b := by
    have h := universalForm_compactRho uNoncritical (hreal := auxiliaryLevel_real) a b
    rw [← h, Complex.conj_conj]
    rfl
  symm := universalForm_isSymmetric (-11 / 3) uNoncritical
  sq x := compactRho_compactRho auxiliaryLevel_real x

/-! ### Generic tensor lemmas with gradings -/

section TensorDeg

variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem tensorP_deg (PV : SesqForm V) (PW : SesqForm W) (BV : LinearMap.BilinForm ℂ V)
    (BW : LinearMap.BilinForm ℂ W) (ρV : V →ₗ⋆[ℂ] V) (ρW : W →ₗ⋆[ℂ] W)
    (dV : (ℤ × ℤ) × ℂ → Submodule ℂ V) (dW : (ℤ × ℤ) × ℂ → Submodule ℂ W)
    (hV : ∀ i, ∀ x ∈ dV i, ∀ y, PV x y = Complex.I ^ i.1.1 * BV (ρV x) y)
    (hW : ∀ i, ∀ x ∈ dW i, ∀ y, PW x y = Complex.I ^ i.1.1 * BW (ρW x) y)
    (i : (ℤ × ℤ) × ℂ) : ∀ z ∈ tensorDeg dV dW i, ∀ Y,
      (PV.tensor PW) z Y = Complex.I ^ i.1.1 * (BV.tmul BW) (TensorProduct.map ρV ρW z) Y := by
  refine tensorDeg_induction dV dW i _ (fun Y => by
      rw [SesqForm.zero_left, map_zero, map_zero, LinearMap.zero_apply, mul_zero])
    (fun z z' hz hz' Y => by
      rw [SesqForm.add_left, hz, hz', map_add, map_add, LinearMap.add_apply, mul_add])
    (fun c z hz Y => by
      rw [SesqForm.smul_left, hz, LinearMap.map_smulₛₗ, map_smul, LinearMap.smul_apply,
        smul_eq_mul]
      ring) ?_
  intro b x hx y hy Y
  rw [tensorP_tmul PV PW BV BW ρV ρW (hV b x hx) (hW (i - b) y hy) Y, ← zpow_add₀ Complex.I_ne_zero]
  congr 2
  simp only [Prod.fst_sub]
  ring

theorem tensorMap_deg (ρV : V →ₗ⋆[ℂ] V) (ρW : W →ₗ⋆[ℂ] W)
    (dV : (ℤ × ℤ) × ℂ → Submodule ℂ V) (dW : (ℤ × ℤ) × ℂ → Submodule ℂ W)
    (hV : ∀ i, ∀ x ∈ dV i, ρV x ∈ dV i) (hW : ∀ i, ∀ x ∈ dW i, ρW x ∈ dW i)
    (i : (ℤ × ℤ) × ℂ) : ∀ z ∈ tensorDeg dV dW i, TensorProduct.map ρV ρW z ∈ tensorDeg dV dW i := by
  refine tensorDeg_induction dV dW i _ (by rw [map_zero]; exact Submodule.zero_mem _)
    (fun z z' hz hz' => by rw [map_add]; exact Submodule.add_mem _ hz hz')
    (fun c z hz => by rw [LinearMap.map_smulₛₗ]; exact Submodule.smul_mem _ _ hz) ?_
  intro b x hx y hy
  rw [TensorProduct.map_tmul]
  have := tmul_mem_tensorDeg dV dW (hV b x hx) (hW (i - b) y hy)
  rwa [add_sub_cancel] at this

theorem tensorMap_sq (ρV : V →ₗ⋆[ℂ] V) (ρW : W →ₗ⋆[ℂ] W) {sV sW : ℂ}
    (hV : ∀ x, ρV (ρV x) = sV • x) (hW : ∀ y, ρW (ρW y) = sW • y) (z : V ⊗[ℂ] W) :
    TensorProduct.map ρV ρW (TensorProduct.map ρV ρW z) = (sV * sW) • z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => exact tensorMap_sq_tmul ρV ρW (hV x) (hW y)
  | add z z' hz hz' => rw [map_add, map_add, hz, hz', smul_add]

end TensorDeg

/-! ### The three matter conjugations -/

/-- A real structure as a semilinear map. -/
def rsLin {𝒱 : Type*} [AddCommGroup 𝒱] [Module ℂ 𝒱]
    {W : VertexOperatorAlgebra 𝒱} (R : RealStructure W) : 𝒱 →ₗ⋆[ℂ] 𝒱 where
  toFun := R.rho
  map_add' := R.map_add
  map_smul' := R.antilinear

@[simp] theorem rsLin_apply {𝒱 : Type*} [AddCommGroup 𝒱] [Module ℂ 𝒱]
    {W : VertexOperatorAlgebra 𝒱} (R : RealStructure W) (x : 𝒱) :
    rsLin R x = R.rho x := rfl

/-- **The hypotheses on the unitary factor `B = L_1(sl₂)`**: `ρ_B² = 1`, compact conjugation of
the current modes, and `B_B`-skewness of the current modes. -/
structure CompactUnitaryB (BB : InvariantForm BVOA) (RB : RealStructure BVOA) : Prop where
  sq : ∀ x : BSpace, RB.rho (RB.rho x) = x
  rho_mode : ∀ (a : Fin 3) (n : ℤ) (x : BSpace),
    RB.rho (bMode a n x) = -bMode (AffineVOA.HighestModule.adjointColour a) n (RB.rho x)
  skew : ∀ (a : Fin 3) (n : ℤ) (x y : BSpace), BB.form (bMode a n x) y = -BB.form x (bMode a (-n) y)

/-- The matter conjugation `ρ_A ⊗ ρ_B ⊗ ρ_U`. -/
def matterRho (RB : RealStructure BVOA) : MatterSpace →ₗ⋆[ℂ] MatterSpace :=
  TensorProduct.map (TensorProduct.map (rsLin affineRealStructure) (rsLin RB))
    (rsLin auxiliaryRealStructure)

/-- The matter bilinear form `B_A ⊗ B_B ⊗ B_U`. -/
def matterB (BB : InvariantForm BVOA) : LinearMap.BilinForm ℂ MatterSpace :=
  LinearMap.BilinForm.tmul (LinearMap.BilinForm.tmul affineForm.form BB.form) auxiliaryForm.form

theorem aMode_rho (a : Fin 3) (n : ℤ) (x : ASpace) :
    affineRealStructure.rho (aMode a n x) =
      -aMode (AffineVOA.HighestModule.adjointColour a) n (affineRealStructure.rho x) := by
  obtain ⟨x, rfl⟩ := (QuotVOA.maxGradedIdeal (universal ALevel aNoncritical)).mkQ_surjective x
  rw [aMode_mkQ, affineConj_apply_mkQ, affineConj_apply_mkQ, aMode_mkQ, ← map_neg]
  exact congrArg _ (compactRho_J affineLevel_real (k := ALevel) a n x)

theorem uMode_rho (a : Fin 3) (n : ℤ) (x : USpace) :
    auxiliaryRealStructure.rho (uMode a n x) =
      -uMode (AffineVOA.HighestModule.adjointColour a) n (auxiliaryRealStructure.rho x) := by
  rw [uMode_apply, uMode_apply]
  exact compactRho_J auxiliaryLevel_real a n x

theorem uMode_skew (a : Fin 3) (n : ℤ) (x y : USpace) :
    auxiliaryForm.form (uMode a n x) y = -auxiliaryForm.form x (uMode a (-n) y) := by
  rw [uMode_apply, uMode_apply]
  exact universalForm_current_adj uNoncritical a n x y

theorem matterJ_eq (a : Fin 3) (n : ℤ) :
    matterJ a n = ((aMode a n).rTensor BSpace + (bMode a n).lTensor ASpace).rTensor USpace +
      (uMode a n).lTensor (ASpace ⊗[ℂ] BSpace) := by
  rw [matterJ, matterMode_eq, LinearMap.rTensor_add]
  rfl

/-! ### The matter factor data -/

theorem matterRho_J0 (RB : RealStructure BVOA) (hCB : ∀ (a : Fin 3) (n : ℤ) (x : BSpace),
    RB.rho (bMode a n x) = -bMode (AffineVOA.HighestModule.adjointColour a) n (RB.rho x))
    (a : Fin 3) (x : MatterSpace) :
    matterRho RB (matterJ a 0 x) =
      -matterJ (AffineVOA.HighestModule.adjointColour a) 0 (matterRho RB x) := by
  rw [matterJ_eq, matterJ_eq]
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x x' hx hx' => rw [map_add, map_add, hx, hx', map_add, map_add, neg_add]
  | tmul w z =>
      induction w using TensorProduct.induction_on with
      | zero => simp
      | add w w' hw hw' =>
          rw [TensorProduct.add_tmul, map_add, map_add, hw, hw', map_add, map_add, neg_add]
      | tmul x y =>
          simp only [matterRho, LinearMap.add_apply, LinearMap.rTensor_tmul,
            LinearMap.lTensor_tmul, map_add, TensorProduct.map_tmul, rsLin_apply, aMode_rho,
            uMode_rho, hCB, TensorProduct.neg_tmul, TensorProduct.tmul_neg, TensorProduct.add_tmul,
            neg_add]

/-- **The matter factor of the Beem–Garner data**, from `hA` and the hypotheses on the unitary
factor `B` only: the affine and auxiliary factors are fully proved (`affineCompactLayerData`,
`auxiliaryCompactLayerData`, current skewness and compact conjugation of the current modes). -/
def matterBGData (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    {BB : InvariantForm BVOA} {RB : RealStructure BVOA} (hCB : CompactUnitaryB BB RB) :
    MatterBGData hA BB RB where
  B := matterB BB
  ρ := matterRho RB
  s := 1
  ρ_sq x := by
    have h := tensorMap_sq (TensorProduct.map (rsLin affineRealStructure) (rsLin RB))
      (rsLin auxiliaryRealStructure) (sV := 1 * 1) (sW := 1)
      (fun z => tensorMap_sq _ _ (fun x => by simp [affineCompactLayerData.sq])
        (fun y => by simp [hCB.sq]) z)
      (fun y => by simp [auxiliaryCompactLayerData.sq]) x
    simpa using h
  P_eq i x hx y :=
    tensorP_deg _ _ _ _ (TensorProduct.map (rsLin affineRealStructure) (rsLin RB))
      (rsLin auxiliaryRealStructure) _ _
      (tensorP_deg _ _ affineForm.form BB.form (rsLin affineRealStructure) (rsLin RB) aDeg bDeg
        (affineCompactLayerData.layerDeg_P_eq hA affineGramRefl)
        (trivialDeg_P_eq BB RB))
      (auxiliaryCompactLayerData.layerDeg_P_eq auxiliaryGradedUnitary auxiliaryGramRefl) i x hx y
  ρ_deg i x hx := by
    have h := tensorMap_deg (TensorProduct.map (rsLin affineRealStructure) (rsLin RB))
      (rsLin auxiliaryRealStructure) _ _
      (tensorMap_deg (rsLin affineRealStructure) (rsLin RB) aDeg bDeg
        (affineCompactLayerData.layerDeg_rho) (trivialDeg_rho RB))
      (auxiliaryCompactLayerData.layerDeg_rho) i x hx
    by_cases hg : i.1.2 = 0
    · have e : conjIdx i = i := by
        obtain ⟨⟨j, g⟩, h'⟩ := i
        simp only at hg
        simp [conjIdx, hg]
      rw [e]; exact h
    · have h0 := matterDeg_le_zeroGhost i hx
      rw [eq_zero_of_mem_zeroGhost (by simpa using hg) h0, map_zero]
      exact Submodule.zero_mem _
  ρ_J0 a x := matterRho_J0 RB hCB.rho_mode a x

/-- The matter currents are `B_M`-skew (proved; recorded for the `B_E` route through mode
transposes on the `c₀`-free subspace). -/
theorem matterB_current_skew {BB : InvariantForm BVOA} {RB : RealStructure BVOA}
    (hCB : CompactUnitaryB BB RB) (a : Fin 3) (k : ℤ) (x y : MatterSpace) :
    matterB BB (matterJ a k x) y = -matterB BB x (matterJ a (-k) y) := by
  rw [matterJ_eq, matterJ_eq]
  exact tensorB_add_rTensor_lTensor _ _ _ _ _ _
    (fun u v => tensorB_add_rTensor_lTensor _ _ _ _ _ _ (aMode_adj a k) (hCB.skew a k) u v)
    (uMode_skew a k) x y

end

end VOA.ConcreteHodge
