/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.BGPackageReduced

/-!
# Splitting the reduced Beem–Garner data into matter and ghost factors

The BRST space is `MatterSpace ⊗ Sl2GhostSpace`, the form is `P_matter ⊗ P_ghost`, and the
matter is purely even. Beem–Garner's bilinear form and conjugation are products,
`B = B_M ⊗ B_G`, `ρ = ρ_M ⊗ ρ_G`. This file proves that the conjugation clauses of the reduced
data (`BGReducedData`: `ρ_maps`, `P_eq`, `ρ_deg`, `ρ² = s`) follow from **factor-local**
statements; `ρ_D` and `B_E` stay statements about the BRST differential:

* matter (`MatterBGData`): `P_M = i^{2R} B_M(ρ_M ·, ·)` on every interpreted matter piece,
  `ρ_M` preserves the pieces (matter has ghost number `0`), `ρ_M² = s_M`, and
  `ρ_M J^a_{(0)} = -J^{ā}_{(0)} ρ_M` (compact conjugation);
* ghosts (`GhostBGData`): the same on the **`c₀`-free** fine ghost pieces (relative states have no
  `c₀`; on `c₀`-states the conjugation cannot both flip the ghost number and square to a nonzero
  scalar — `c₀|0⟩` has weight `0` and ghost number `1`, and there is no weight-`0` state of ghost
  number `-1`), and `ρ_G` maps `c₀`-free pieces to `c₀`-free pieces;
* `BGFactorData.toReduced` — the reduced data, hence (`BGReducedData.toGlobal`) the full
  per-weight package, from the two factor data, `ρ_D` and `B_E`.

Generic lemmas (`tensorP_tmul`, `tensorB_lTensor`, `tensorB_add_rTensor_lTensor`, …) are proved
for arbitrary tensor products. Everything is proved outright from the listed hypotheses.
-/

namespace VOA.ConcreteHodge

open Sl2CosetConcrete Sl2SemiInfinite AffineSl2GeneralRigidity AffineSl2BelowCritical
open VOA.GradedUnitaryCohomology VOA.LeeYangCosetTransfer VOA.VertexOperatorAlgebra
open VOA.LeeYangTransferAssembly LeeYangShortcut VirModule LeeYang VirGradedUnitarity
open VOA.SympFerm VOA.Ghost AffineVOA
open scoped TensorProduct

noncomputable section

/-! ### Generic tensor lemmas -/

section GenericTensor

variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem bilinTmul_tmul (BV : LinearMap.BilinForm ℂ V) (BW : LinearMap.BilinForm ℂ W)
    (x x' : V) (y y' : W) : (BV.tmul BW) (x ⊗ₜ[ℂ] y) (x' ⊗ₜ[ℂ] y') = BV x x' * BW y y' := by
  rw [LinearMap.BilinForm.tensorDistrib_tmul, smul_eq_mul, mul_comm]

/-- `P = c B(ρ ·, ·)` on a pure tensor from the factor identities. -/
theorem tensorP_tmul (PV : SesqForm V) (PW : SesqForm W) (BV : LinearMap.BilinForm ℂ V)
    (BW : LinearMap.BilinForm ℂ W) (ρV : V →ₗ⋆[ℂ] V) (ρW : W →ₗ⋆[ℂ] W) {x : V} {y : W}
    {cV cW : ℂ} (hV : ∀ x', PV x x' = cV * BV (ρV x) x') (hW : ∀ y', PW y y' = cW * BW (ρW y) y')
    (Z : V ⊗[ℂ] W) :
    (PV.tensor PW) (x ⊗ₜ[ℂ] y) Z =
      (cV * cW) * (BV.tmul BW) (TensorProduct.map ρV ρW (x ⊗ₜ[ℂ] y)) Z := by
  induction Z using TensorProduct.induction_on with
  | zero => rw [SesqForm.zero_right, map_zero, mul_zero]
  | tmul x' y' =>
      rw [SesqForm.tensor_tmul, TensorProduct.map_tmul, bilinTmul_tmul, hV, hW]
      ring
  | add Z Z' hZ hZ' => rw [(PV.tensor PW).add_right, hZ, hZ', map_add, mul_add]

theorem tensorMap_sq_tmul (ρV : V →ₗ⋆[ℂ] V) (ρW : W →ₗ⋆[ℂ] W) {x : V} {y : W} {sV sW : ℂ}
    (hx : ρV (ρV x) = sV • x) (hy : ρW (ρW y) = sW • y) :
    TensorProduct.map ρV ρW (TensorProduct.map ρV ρW (x ⊗ₜ[ℂ] y)) = (sV * sW) • (x ⊗ₜ[ℂ] y) := by
  rw [TensorProduct.map_tmul, TensorProduct.map_tmul, hx, hy, TensorProduct.smul_tmul_smul]

/-- Transposition of `id ⊗ T` for the product form, on `V ⊗ S`. -/
theorem tensorB_lTensor (BV : LinearMap.BilinForm ℂ V) (BW : LinearMap.BilinForm ℂ W)
    (T T' : Module.End ℂ W) (c : ℂ) (S : Submodule ℂ W)
    (hT : ∀ y ∈ S, ∀ y', BW (T y) y' = c * BW y (T' y')) :
    ∀ u ∈ TensorVA.tenSub (⊤ : Submodule ℂ V) S, ∀ v,
      (BV.tmul BW) (T.lTensor V u) v = c * (BV.tmul BW) u (T'.lTensor V v) := by
  intro u hu
  refine TensorVA.tenSub_induction (motive := fun u => ∀ v,
      (BV.tmul BW) (T.lTensor V u) v = c * (BV.tmul BW) u (T'.lTensor V v))
    (fun v => by simp) (fun u u' hu hu' v => by
      beta_reduce at hu hu'
      simp only [map_add, LinearMap.add_apply, hu, hu', mul_add])
    (fun a u hu v => by
      beta_reduce at hu
      simp only [map_smul, LinearMap.smul_apply, hu, smul_eq_mul]; ring) ?_ hu
  intro x _ y hy v
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul x' y' =>
      rw [LinearMap.lTensor_tmul, LinearMap.lTensor_tmul, bilinTmul_tmul, bilinTmul_tmul,
        hT y hy y']
      ring
  | add v v' hv hv' => rw [map_add, map_add, map_add, hv, hv', mul_add]

/-- Transposition of `A ⊗ 1 + 1 ⊗ C` for the product form, from factor skewness. -/
theorem tensorB_add_rTensor_lTensor (BV : LinearMap.BilinForm ℂ V) (BW : LinearMap.BilinForm ℂ W)
    (A A' : Module.End ℂ V) (C C' : Module.End ℂ W)
    (hA : ∀ x x', BV (A x) x' = -BV x (A' x')) (hC : ∀ y y', BW (C y) y' = -BW y (C' y'))
    (u v : V ⊗[ℂ] W) :
    (BV.tmul BW) ((A.rTensor W + C.lTensor V) u) v =
      -(BV.tmul BW) u ((A'.rTensor W + C'.lTensor V) v) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add u u' hu hu' =>
      simp only [map_add, LinearMap.add_apply] at hu hu' ⊢
      linear_combination hu + hu'
  | tmul x y =>
      induction v using TensorProduct.induction_on with
      | zero => simp
      | add v v' hv hv' =>
          simp only [map_add, LinearMap.add_apply] at hv hv' ⊢
          linear_combination hv + hv'
      | tmul x' y' =>
          simp only [LinearMap.add_apply, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul,
            map_add, LinearMap.add_apply, bilinTmul_tmul, hA, hC]
          ring

end GenericTensor

/-! ### The total current modes split -/

/-- The matter current mode `J^a_{(k)}`. -/
abbrev matterJ (a : Fin 3) (k : ℤ) : Module.End ℂ MatterSpace :=
  mode (matterSVA.Y (leeYangA.current a)) k

/-- The ghost current mode `J^a_{gh,(k)}`. -/
abbrev ghostJ (a : Fin 3) (k : ℤ) : Module.End ℂ Sl2GhostSpace := mode (ghostCurrentField a) k

theorem JT_eq (a : Fin 3) (k : ℤ) :
    JT a k = (matterJ a k).rTensor Sl2GhostSpace + (ghostJ a k).lTensor MatterSpace := by
  apply TensorProduct.ext'
  intro x y
  unfold JT totalCurrentState
  rw [map_add, mode_add, LinearMap.add_apply, mode_apply, mode_apply]
  rw [tenY_left_unit, tenY_right_unit_even matterSVA sl2GhostSVA (ghostCurrent_even a)]
  rfl

/-! ### `c₀`-freeness -/

theorem fockDegF_eq_bot {k : KF} (hk : k.2 < 0) : fockDegF k = ⊥ := by
  rw [fockDegF, Submodule.span_eq_bot]
  rintro _ ⟨l, hl, rfl⟩
  exfalso
  have h : (wordIdxF l).2 = k.2 := congrArg Prod.snd hl
  simp only [wordIdxF] at h
  omega

theorem tensorDeg_eq_bot {ι V W : Type*} [AddCommGroup ι] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (dV : ι → Submodule ℂ V) (dW : ι → Submodule ℂ W) (a : ι)
    (h : ∀ b, dV b = ⊥ ∨ dW (a - b) = ⊥) : tensorDeg dV dW a = ⊥ := by
  refine eq_bot_iff.mpr (iSup_le fun b => ?_)
  rcases h b with h | h
  · rw [h, Submodule.map₂_bot_left]
  · rw [h, Submodule.map₂_bot_right]

theorem pairDegF_eq_bot {k : KF} (hk : k.2 < 0) : pairDegF k = ⊥ :=
  tensorDeg_eq_bot _ _ _ fun b => by
    by_cases hb : b.2 < 0
    · exact Or.inl (fockDegF_eq_bot hb)
    · exact Or.inr (fockDegF_eq_bot (by simp only [Prod.snd_sub]; omega))

theorem ghostDegF_eq_bot {k : KF} (hk : k.2 < 0) : ghostDegF k = ⊥ :=
  tensorDeg_eq_bot _ _ _ fun b => by
    by_cases hb : b.2 < 0
    · exact Or.inl (pairDegF_eq_bot hb)
    · exact Or.inr (fockDegF_eq_bot (by simp only [Prod.snd_sub]; omega))

/-- The antighost zero modes kill `c₀`-free ghost states. -/
theorem antiMode_zero_c0free (a : Fin 3) {k : KF} (hk : k.2 = 0) {y : Sl2GhostSpace}
    (hy : y ∈ ghostDegF k) : antiMode a 0 y = 0 := by
  have h := ghostModeF_mem a 0 0 hy
  have hneg : (k + ghShiftF 0 (-0 - 1)).2 < 0 := by
    have : ghShiftF 0 (-0 - 1) = -modeIdxF (0, 1) := by
      simp [ghShiftF]
    rw [this]
    simp [modeIdxF, hk]
  rw [ghostDegF_eq_bot hneg, Submodule.mem_bot] at h
  exact h

/-! ### The fine decomposition of relative states -/

section Decomp

variable (hA : GradedUnitary affineForm affineRealStructure affineFlag)
  {BB : InvariantForm BVOA} {RB : RealStructure BVOA} (hB : Unitary BB RB)

include hA hB

theorem relative_fine_c0 {n : ℤ} {x : BRSTSpace} (hx : x ∈ relativeWeight n) :
    x ∈ ⨆ (k : KF) (_ : k.2 = 0), brstDegF k :=
  relative_c0free hA hB unitWeight unitWeight_pos fun a =>
    ((mem_relativeCarrier _ x).mp hx.1).2 a

theorem relative_fine_weight {n : ℤ} {x : BRSTSpace} (hx : x ∈ relativeWeight n) :
    x ∈ ⨆ (k : KF) (_ : k.1.2 = (n : ℂ) ∧ k.2 = 0), brstDegF k := by
  classical
  have hI := brstDegF_isInternal hA hB unitWeight unitWeight_pos
  refine mem_iSup_pred_inf hI ?_ (relative_fine_c0 hA hB hx)
  rw [mem_iSup_pred_iff hI]
  intro k hk
  exact iproj_eq_zero_of_weight hI brstSVA.isInternal (fun k : KF => k.1.2)
    (fun k => (brstDegF_le_brstDeg unitWeight k).trans
      (brstDeg_le_weight (ghostRGrading unitWeight) (fstF k))) hx.2 hk

theorem relative_fine_deg {PG : SesqForm Sl2GhostSpace} {Gh : GhostRGrading PG} (hs : Gh.IsStd)
    {n : ℤ} {i : (ℤ × ℤ) × ℂ} {x : BRSTSpace} (hx : x ∈ relativeWeight n)
    (hxd : x ∈ brstDeg Gh i) :
    x ∈ ⨆ (k : KF) (_ : fstF k = i ∧ k.2 = 0), brstDegF k := by
  have hI := brstDegF_isInternal hA hB unitWeight unitWeight_pos
  rw [brstDeg_std hs] at hxd
  exact mem_iSup_pred_inf hI (brstDeg_le_coarsenF unitWeight i hxd) (relative_fine_c0 hA hB hx)

end Decomp

/-! ### The factor data -/

/-- The product form on the matter factor. -/
def matterForm (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    (BB : InvariantForm BVOA) (RB : RealStructure BVOA) : SesqForm MatterSpace :=
  ((carrierForm affineForm affineRealStructure affineFlag hA affineGramRefl).tensor
    (unitaryCarrierForm BB RB)).tensor
    (carrierForm auxiliaryForm auxiliaryRealStructure auxiliaryFlag auxiliaryGradedUnitary
      auxiliaryGramRefl)

theorem matterGhostForm_eq (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    (BB : InvariantForm BVOA) (RB : RealStructure BVOA) (PG : SesqForm Sl2GhostSpace) :
    matterGhostForm hA BB RB PG = (matterForm hA BB RB).tensor PG := rfl

/-- The conjugate index `((2R, gh), h) ↦ ((2R, -gh), h)`. -/
def conjIdx (i : (ℤ × ℤ) × ℂ) : (ℤ × ℤ) × ℂ := ((i.1.1, -i.1.2), i.2)

/-- The conjugate fine index. -/
def conjF (k : KF) : KF := (conjIdx k.1, k.2)

theorem conjF_add (k k' : KF) : conjF (k + k') = conjF k + conjF k' := by
  simp only [conjF, conjIdx, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk, neg_add]

/-- **The matter factor of the Beem–Garner data.** -/
structure MatterBGData (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    (BB : InvariantForm BVOA) (RB : RealStructure BVOA) where
  B : LinearMap.BilinForm ℂ MatterSpace
  ρ : MatterSpace →ₗ⋆[ℂ] MatterSpace
  s : ℂ
  ρ_sq : ∀ x, ρ (ρ x) = s • x
  /-- `P_M = i^{2R} B_M(ρ_M ·, ·)` on every interpreted matter piece. -/
  P_eq : ∀ i, ∀ x ∈ matterDeg i, ∀ y, matterForm hA BB RB x y = Complex.I ^ i.1.1 * B (ρ x) y
  ρ_deg : ∀ i, ∀ x ∈ matterDeg i, ρ x ∈ matterDeg (conjIdx i)
  /-- Compact conjugation of the current zero modes. -/
  ρ_J0 : ∀ (a : Fin 3) (x : MatterSpace),
    ρ (matterJ a 0 x) = -matterJ (AffineVOA.HighestModule.adjointColour a) 0 (ρ x)

/-- **The ghost factor of the Beem–Garner data** (conjugation clauses on `c₀`-free pieces). -/
structure GhostBGData (PG : SesqForm Sl2GhostSpace) where
  B : LinearMap.BilinForm ℂ Sl2GhostSpace
  ρ : Sl2GhostSpace →ₗ⋆[ℂ] Sl2GhostSpace
  s : ℂ
  ρ_sq : ∀ k : KF, k.2 = 0 → ∀ y ∈ ghostDegF k, ρ (ρ y) = s • y
  P_eq : ∀ k : KF, k.2 = 0 → ∀ y ∈ ghostDegF k, ∀ y', PG y y' = Complex.I ^ k.1.1.1 * B (ρ y) y'
  ρ_deg : ∀ k : KF, k.2 = 0 → ∀ y ∈ ghostDegF k, ρ y ∈ ghostDegF (conjF k)
  /-- Compact conjugation of the ghost current zero modes, on `c₀`-free pieces. -/
  ρ_J0 : ∀ k : KF, k.2 = 0 → ∀ y ∈ ghostDegF k, ∀ a : Fin 3,
    ρ (ghostJ a 0 y) = -ghostJ (AffineVOA.HighestModule.adjointColour a) 0 (ρ y)

/-! ### The product data on the fine pieces -/

section Assembly

variable {hA : GradedUnitary affineForm affineRealStructure affineFlag}
  {BB : InvariantForm BVOA} {RB : RealStructure BVOA} {PG : SesqForm Sl2GhostSpace}

/-- The product conjugation `ρ_M ⊗ ρ_G`. -/
def brstρ (M : MatterBGData hA BB RB) (G : GhostBGData PG) : BRSTSpace →ₗ⋆[ℂ] BRSTSpace :=
  TensorProduct.map M.ρ G.ρ

/-- The product bilinear form `B_M ⊗ B_G`. -/
def brstB (M : MatterBGData hA BB RB) (G : GhostBGData PG) : LinearMap.BilinForm ℂ BRSTSpace :=
  M.B.tmul G.B

theorem matterF_cases {b : KF} {x : MatterSpace} (hx : x ∈ matterF b) :
    x = 0 ∨ (b.2 = 0 ∧ x ∈ matterDeg b.1) := by
  unfold matterF at hx
  split_ifs at hx with h
  · exact Or.inr ⟨h, hx⟩
  · exact Or.inl ((Submodule.mem_bot ℂ).mp hx)

theorem sub_snd_zero {k b : KF} (hk : k.2 = 0) (hb : b.2 = 0) : (k - b).2 = 0 := by
  simp [Prod.snd_sub, hk, hb]

variable (M : MatterBGData hA BB RB) (G : GhostBGData PG)

theorem fine_P (k : KF) (hk : k.2 = 0) : ∀ z ∈ brstDegF k, ∀ Y,
    matterGhostForm hA BB RB PG z Y = Complex.I ^ k.1.1.1 * brstB M G (brstρ M G z) Y := by
  refine tensorDeg_induction matterF ghostDegF k _ (fun Y => by
      rw [SesqForm.zero_left, map_zero, map_zero, LinearMap.zero_apply, mul_zero])
    (fun z z' hz hz' Y => by
      rw [SesqForm.add_left, hz, hz', map_add, map_add, LinearMap.add_apply, mul_add])
    (fun c z hz Y => by
      rw [SesqForm.smul_left, hz, LinearMap.map_smulₛₗ, map_smul, LinearMap.smul_apply,
        smul_eq_mul]
      ring) ?_
  intro b x hx y hy Y
  rcases matterF_cases hx with rfl | ⟨hb, hx⟩
  · rw [TensorProduct.zero_tmul, SesqForm.zero_left, map_zero, map_zero, LinearMap.zero_apply,
      mul_zero]
  · rw [matterGhostForm_eq, tensorP_tmul (matterForm hA BB RB) PG M.B G.B M.ρ G.ρ
      (M.P_eq b.1 x hx) (G.P_eq (k - b) (sub_snd_zero hk hb) y hy) Y]
    congr 1
    rw [← zpow_add₀ Complex.I_ne_zero]
    congr 1
    simp only [Prod.fst_sub]
    ring

theorem fine_D (k : KF) (hk : k.2 = 0) : ∀ z ∈ brstDegF k, brstρ M G z ∈ brstDegF (conjF k) := by
  refine tensorDeg_induction matterF ghostDegF k _ (by rw [map_zero]; exact Submodule.zero_mem _)
    (fun z z' hz hz' => by rw [map_add]; exact Submodule.add_mem _ hz hz')
    (fun c z hz => by rw [LinearMap.map_smulₛₗ]; exact Submodule.smul_mem _ _ hz) ?_
  intro b x hx y hy
  rcases matterF_cases hx with rfl | ⟨hb, hx⟩
  · rw [TensorProduct.zero_tmul, map_zero]; exact Submodule.zero_mem _
  · have h1 : M.ρ x ∈ matterF (conjF b) := by
      have : matterF (conjF b) = matterDeg (conjIdx b.1) := by
        simp [matterF, conjF, hb]
      rw [this]; exact M.ρ_deg b.1 x hx
    have h2 := G.ρ_deg (k - b) (sub_snd_zero hk hb) y hy
    have h3 := tmul_mem_tensorDeg matterF ghostDegF h1 h2
    rw [← conjF_add, add_sub_cancel] at h3
    exact h3

theorem fine_S (k : KF) (hk : k.2 = 0) : ∀ z ∈ brstDegF k,
    brstρ M G (brstρ M G z) = (M.s * G.s) • z := by
  refine tensorDeg_induction matterF ghostDegF k _ (by simp)
    (fun z z' hz hz' => by rw [map_add, map_add, hz, hz', smul_add])
    (fun c z hz => by
      rw [LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, hz, smul_comm]
      simp) ?_
  intro b x hx y hy
  rcases matterF_cases hx with rfl | ⟨hb, hx⟩
  · simp
  · exact tensorMap_sq_tmul M.ρ G.ρ (M.ρ_sq x) (G.ρ_sq (k - b) (sub_snd_zero hk hb) y hy)

theorem fine_J (k : KF) (hk : k.2 = 0) (a : Fin 3) : ∀ z ∈ brstDegF k,
    totalCurrentZero leeYangA a (brstρ M G z) =
      -brstρ M G (totalCurrentZero leeYangA (AffineVOA.HighestModule.adjointColour a) z) := by
  refine tensorDeg_induction matterF ghostDegF k _ (by simp)
    (fun z z' hz hz' => by rw [map_add, map_add, hz, hz', map_add, map_add, neg_add])
    (fun c z hz => by
      rw [LinearMap.map_smulₛₗ, map_smul, hz, map_smul, LinearMap.map_smulₛₗ, smul_neg]) ?_
  intro b x hx y hy
  rcases matterF_cases hx with rfl | ⟨hb, _⟩
  · simp
  · have hy' := G.ρ_J0 (k - b) (sub_snd_zero hk hb) y hy
      (AffineVOA.HighestModule.adjointColour a)
    rw [AffineVOA.HighestModule.adjointColour_involutive] at hy'
    have hx' := M.ρ_J0 (AffineVOA.HighestModule.adjointColour a) x
    rw [AffineVOA.HighestModule.adjointColour_involutive] at hx'
    simp only [brstρ, TensorProduct.map_tmul, totalCurrentZero_tmul, map_add]
    change matterJ a 0 (M.ρ x) ⊗ₜ[ℂ] G.ρ y + M.ρ x ⊗ₜ[ℂ] ghostJ a 0 (G.ρ y) =
      -(M.ρ (matterJ _ 0 x) ⊗ₜ[ℂ] G.ρ y + M.ρ x ⊗ₜ[ℂ] G.ρ (ghostJ _ 0 y))
    rw [hx', hy', TensorProduct.neg_tmul, TensorProduct.tmul_neg, neg_add, neg_neg, neg_neg]

/-- The antighost zero modes kill the `c₀`-free fine BRST pieces. -/
theorem antighostZero_fine (k : KF) (hk : k.2 = 0) (a : Fin 3) :
    ∀ z ∈ brstDegF k, antighostZero matterSVA a z = 0 := by
  rw [antighostZero_eq]
  refine tensorDeg_induction matterF ghostDegF k _ (by simp)
    (fun z z' hz hz' => by rw [map_add, hz, hz', add_zero])
    (fun c z hz => by rw [map_smul, hz, smul_zero]) ?_
  intro b x hx y hy
  rcases matterF_cases hx with rfl | ⟨hb, _⟩
  · simp
  · rw [TensorProduct.map_tmul]
    change x ⊗ₜ[ℂ] antiMode a 0 y = 0
    rw [antiMode_zero_c0free a (sub_snd_zero hk hb) hy, TensorProduct.tmul_zero]

/-- Extending a statement from the `c₀`-free fine pieces to their span. -/
theorem iSup_fine_induction {S : KF → Prop} (Φ : BRSTSpace → Prop) (h0 : Φ 0)
    (hadd : ∀ x y, Φ x → Φ y → Φ (x + y)) (hpiece : ∀ k, S k → ∀ z ∈ brstDegF k, Φ z)
    {x : BRSTSpace} (hx : x ∈ ⨆ (k : KF) (_ : S k), brstDegF k) : Φ x := by
  refine Submodule.iSup_induction _ (motive := Φ) hx ?_ h0 hadd
  intro k z hz
  refine Submodule.iSup_induction _ (motive := Φ) hz ?_ h0 hadd
  intro hk z hz
  exact hpiece k hk z hz

end Assembly

/-! ### The reduced data from the factors -/

/-- **The factor data**: matter and ghost factors and the remaining statement `ρ_D` about the
BRST differential, for the product conjugation `ρ_M ⊗ ρ_G`. -/
structure BGFactorData {PG : SesqForm Sl2GhostSpace} (Gh : GhostRGrading PG)
    (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    (BB : InvariantForm BVOA) (RB : RealStructure BVOA) where
  M : MatterBGData hA BB RB
  G : GhostBGData PG
  hsM : M.s ≠ 0
  hsG : G.s ≠ 0
  κ : ℂ
  hκ : κ ≠ 0
  /-- `ρ Q = κ (-1)^{gh} [Λ, Q] ρ` on relative states, for `ρ = ρ_M ⊗ ρ_G`. -/
  ρ_D : ∀ (n j g : ℤ), ∀ x ∈ relativeWeight n, x ∈ brstDeg Gh ((j, g), (n : ℂ)) →
    brstρ M G (brstQ x) = (κ * (-1 : ℂ) ^ g) • brstE n (brstρ M G x)
  /-- Super-skewness of `B_M ⊗ B_G` for `E = [Λ, Q]` on relative states. -/
  B_E : ∀ (n j g : ℤ), ∀ u ∈ relativeWeight n, u ∈ brstDeg Gh ((j, g), (n : ℂ)) →
    ∀ v ∈ relativeWeight n,
      brstB M G (brstE n u) v = -((-1 : ℂ) ^ g) * brstB M G u (brstE n v)

namespace BGFactorData

variable {PG : SesqForm Sl2GhostSpace} {Gh : GhostRGrading PG}
  {hA : GradedUnitary affineForm affineRealStructure affineFlag}
  {BB : InvariantForm BVOA} {RB : RealStructure BVOA}

theorem ρ_maps (F : BGFactorData Gh hA BB RB) (hB : Unitary BB RB) (n : ℤ) (x : BRSTSpace)
    (hx : x ∈ relativeWeight n) : brstρ F.M F.G x ∈ relativeWeight n := by
  have key : ∀ z ∈ ⨆ (k : KF) (_ : k.1.2 = (n : ℂ) ∧ k.2 = 0), brstDegF k,
      brstρ F.M F.G z ∈ brstSVA.grading (n : ℂ) ∧
        (∀ a, antighostZero matterSVA a (brstρ F.M F.G z) = 0) ∧
        (∀ a, totalCurrentZero leeYangA a (brstρ F.M F.G z) =
          -brstρ F.M F.G (totalCurrentZero leeYangA
            (AffineVOA.HighestModule.adjointColour a) z)) := by
    intro z hz
    refine iSup_fine_induction (fun z => brstρ F.M F.G z ∈ brstSVA.grading (n : ℂ) ∧
        (∀ a, antighostZero matterSVA a (brstρ F.M F.G z) = 0) ∧
        (∀ a, totalCurrentZero leeYangA a (brstρ F.M F.G z) =
          -brstρ F.M F.G (totalCurrentZero leeYangA
            (AffineVOA.HighestModule.adjointColour a) z)))
      ⟨by simp, fun a => by simp, fun a => by simp⟩
      (fun x y hx hy => ⟨by rw [map_add]; exact Submodule.add_mem _ hx.1 hy.1,
        fun a => by rw [map_add, map_add, hx.2.1 a, hy.2.1 a, add_zero],
        fun a => by rw [map_add, map_add, hx.2.2 a, hy.2.2 a, map_add, map_add, neg_add]⟩)
      ?_ hz
    rintro k ⟨hkn, hk⟩ z hz
    have hD := fine_D F.M F.G k hk z hz
    refine ⟨?_, fun a => antighostZero_fine (conjF k) (by simp [conjF, hk]) a _ hD,
      fun a => fine_J F.M F.G k hk a z hz⟩
    have h1 := (brstDegF_le_brstDeg unitWeight (conjF k)).trans
      (brstDeg_le_weight (ghostRGrading unitWeight) (fstF (conjF k))) hD
    have e : wtIndex (fstF (conjF k)) = (n : ℂ) := by
      simp [conjF, conjIdx, wtIndex, hkn]
    rwa [e] at h1
  obtain ⟨h1, h2, h3⟩ := key x (relative_fine_weight hA hB hx)
  refine ⟨(mem_relativeCarrier _ _).mpr ⟨fun a => ?_, h2⟩, h1⟩
  rw [h3 a, ((mem_relativeCarrier _ x).mp hx.1).1, map_zero, neg_zero]

/-- **The reduced data from the factor data** (standard ghost grading). -/
def toReduced (F : BGFactorData Gh hA BB RB) (hB : Unitary BB RB) (hs : Gh.IsStd) :
    BGReducedData Gh hA BB RB where
  B := brstB F.M F.G
  ρ := brstρ F.M F.G
  ρ_maps := fun n x hx => F.ρ_maps hB n x hx
  P_eq := fun n j g x hxr hx y _ => by
    refine iSup_fine_induction (fun z => ∀ Y, matterGhostForm hA BB RB PG z Y =
        Complex.I ^ j * brstB F.M F.G (brstρ F.M F.G z) Y)
      (fun Y => by rw [SesqForm.zero_left, map_zero, map_zero, LinearMap.zero_apply, mul_zero])
      (fun z z' hz hz' Y => by
        rw [SesqForm.add_left, hz, hz', map_add, map_add, LinearMap.add_apply, mul_add])
      ?_ (relative_fine_deg hA hB hs hxr hx) y
    rintro k ⟨hki, hk⟩ z hz Y
    rw [fine_P F.M F.G k hk z hz Y]
    have : k.1.1.1 = j := by
      have := congrArg (fun i : (ℤ × ℤ) × ℂ => i.1.1) hki
      simpa [fstF] using this
    rw [this]
  ρ_deg := fun n j g x hxr hx => by
    rw [brstDeg_std hs]
    refine iSup_fine_induction (fun z => brstρ F.M F.G z ∈
        brstDeg (ghostRGrading unitWeight) ((j, -g), (n : ℂ)))
      (by beta_reduce; rw [map_zero]; exact Submodule.zero_mem _)
      (fun z z' hz hz' => by
        beta_reduce at hz hz' ⊢; rw [map_add]; exact Submodule.add_mem _ hz hz')
      ?_ (relative_fine_deg hA hB hs hxr hx)
    rintro k ⟨hki, hk⟩ z hz
    have h1 := brstDegF_le_brstDeg unitWeight (conjF k) (fine_D F.M F.G k hk z hz)
    have e : fstF (conjF k) = ((j, -g), (n : ℂ)) := by
      have h := hki
      simp only [fstF, AddMonoidHom.coe_fst] at h
      simp [fstF, conjF, conjIdx, h]
    rwa [e] at h1
  s := F.M.s * F.G.s
  hs := mul_ne_zero F.hsM F.hsG
  ρ_sq := fun n x hx => by
    refine iSup_fine_induction (fun z => brstρ F.M F.G (brstρ F.M F.G z) = (F.M.s * F.G.s) • z)
      (by simp) (fun z z' hz hz' => by
        beta_reduce at hz hz' ⊢; rw [map_add, map_add, hz, hz', smul_add])
      ?_ (relative_fine_c0 hA hB hx)
    intro k hk z hz
    exact fine_S F.M F.G k hk z hz
  κ := F.κ
  hκ := F.hκ
  ρ_D := F.ρ_D
  B_E := F.B_E

end BGFactorData

/-- **Affine GU ⇒ Lee–Yang GU from the factor data**, for the Beem–Garner colour-weighted ghost
form. `#print axioms`-clean, conditional on: `hA` (the hypothesis), `hB`, `F` (matter factor data,
ghost factor data, `ρ_D`) and the downstream `symbols`, `character`, `vacuumNormalized`,
`creationAdjoint`, `wordsReal`. -/
theorem leeYang_gradedUnitary_of_affine_bgFactor_colour
    (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    {BB : InvariantForm BVOA} {RB : RealStructure BVOA} (hB : Unitary BB RB)
    (F : BGFactorData bgGh hA BB RB)
    (symbols : LeadingInvariantSymbolDimension
      (sp2Kahler hA hB bgPG_pos bgGh bgGh_isStd
        (((F.toReduced hB bgGh_isStd).toGlobal bgGh_isStd).toInterpreted hB bgPG_pos
          (stdZ bgGh_isStd) (stdD hA hB bgGh_isStd)).sp2))
    (character : LeeYangPBWCharacter)
    (vacuumNormalized : HarmonicVacuumNormalized
      (sp2Kahler hA hB bgPG_pos bgGh bgGh_isStd
        (((F.toReduced hB bgGh_isStd).toGlobal bgGh_isStd).toInterpreted hB bgPG_pos
          (stdZ bgGh_isStd) (stdD hA hB bgGh_isStd)).sp2)
      (sp2GUData0 hA hB bgPG_pos bgGh bgGh_isStd
        (((F.toReduced hB bgGh_isStd).toGlobal bgGh_isStd).toInterpreted hB bgPG_pos
          (stdZ bgGh_isStd) (stdD hA hB bgGh_isStd)).sp2
        (((F.toReduced hB bgGh_isStd).toGlobal bgGh_isStd).toInterpreted hB bgPG_pos
          (stdZ bgGh_isStd) (stdD hA hB bgGh_isStd)).conj0))
    (creationAdjoint : HarmonicCreationAdjoint
      (sp2Kahler hA hB bgPG_pos bgGh bgGh_isStd
        (((F.toReduced hB bgGh_isStd).toGlobal bgGh_isStd).toInterpreted hB bgPG_pos
          (stdZ bgGh_isStd) (stdD hA hB bgGh_isStd)).sp2)
      (sp2GUData0 hA hB bgPG_pos bgGh bgGh_isStd
        (((F.toReduced hB bgGh_isStd).toGlobal bgGh_isStd).toInterpreted hB bgPG_pos
          (stdZ bgGh_isStd) (stdD hA hB bgGh_isStd)).sp2
        (((F.toReduced hB bgGh_isStd).toGlobal bgGh_isStd).toInterpreted hB bgPG_pos
          (stdZ bgGh_isStd) (stdD hA hB bgGh_isStd)).conj0))
    (wordsReal : HarmonicWordsReal
      (sp2Kahler hA hB bgPG_pos bgGh bgGh_isStd
        (((F.toReduced hB bgGh_isStd).toGlobal bgGh_isStd).toInterpreted hB bgPG_pos
          (stdZ bgGh_isStd) (stdD hA hB bgGh_isStd)).sp2)
      (sp2GUData0 hA hB bgPG_pos bgGh bgGh_isStd
        (((F.toReduced hB bgGh_isStd).toGlobal bgGh_isStd).toInterpreted hB bgPG_pos
          (stdZ bgGh_isStd) (stdD hA hB bgGh_isStd)).sp2
        (((F.toReduced hB bgGh_isStd).toGlobal bgGh_isStd).toInterpreted hB bgPG_pos
          (stdZ bgGh_isStd) (stdD hA hB bgGh_isStd)).conj0)) :
    VirGradedUnitary leeYangC leeYangRealStructure :=
  leeYang_gradedUnitary_of_affine_bgReduced_colour hA hB (F.toReduced hB bgGh_isStd) symbols
    character vacuumNormalized creationAdjoint wordsReal

end

end VOA.ConcreteHodge
