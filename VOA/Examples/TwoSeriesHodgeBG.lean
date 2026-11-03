/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.TwoSeriesHodgeKahler
import VOA.Examples.BGPackageBFactor

/-!
# Level-generic port of the level-specific parts of `BGPackage*`

The Beem–Garner conjugation package on the actual level-`L` matter–ghost complex: the BRST
charge decomposition, the `Λ` operator, the reduced and tensor packages, the matter factor data.
Level-independent declarations are reused from `BGPackageGlobal`, `BGPackageLambda`,
`BGPackageReduced`, `BGPackageTensor`, `BGPackageMatter`, `BGPackageBFactor`.
-/

namespace VOA.TwoSeries

open VOA.ConcreteHodge Sl2CosetConcrete Sl2SemiInfinite AffineSl2GeneralRigidity
open AffineSl2BelowCritical VOA.GradedUnitaryCohomology VOA.LeeYangCosetTransfer
open VOA.VertexOperatorAlgebra VOA.LeeYangTransferAssembly LeeYangShortcut VirModule LeeYang
open VirGradedUnitarity VOA.SympFerm VOA.Ghost AffineVOA CorrectedR AffineVOA.Inst
open scoped TensorProduct

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

universe u v w uM

variable (L : CosetLevels)

/-! ## Port of `BGPackageGlobal` -/


/-- The BRST differential on the whole space. -/
abbrev brstQ : Module.End ℂ (BRSTSpace L) := (brstComplex L).Q

namespace GlobalBGPackage

variable {PG : SesqForm Sl2GhostSpace} {Gh : GhostRGrading PG}
  {hA : GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag L)}
  {BB : InvariantForm BVOA} {RB : RealStructure BVOA} (hB : ConcreteHodge.Unitary BB RB)
  (hG : IsPosOn PG ⊤) (hZ : (ZeroModesPreserve L) Gh) (hD : (RelativeDifferentialGood L) Gh)

end GlobalBGPackage


/-! ## Port of `BGPackageLambda` -/


/-! ### The Casimir tensor -/

/-! ### Generic algebra -/

section Generic

variable {A : Type*} [Ring A] [Algebra ℂ A]

end Generic

/-! ### The ghost operator -/

/-- **Beem–Garner's `Λ` on the BRST space at weight `n`.** -/
def lamBRST (n : ℤ) : Module.End ℂ (BRSTSpace L) :=
  TensorProduct.map LinearMap.id (lamG n.toNat)

/-! ### `Λ` on the BRST space -/

theorem lamBRST_tmul (n : ℤ) (x : (MatterSpace L)) (y : Sl2GhostSpace) :
    (lamBRST L) n (x ⊗ₜ[ℂ] y) = x ⊗ₜ[ℂ] lamG n.toNat y := by
  simp [lamBRST]

/-- `Λ` commutes with the antighost zero modes on the BRST space. -/
theorem lamBRST_antighostZero (n : ℤ) (c : Fin 3) (z : (BRSTSpace L)) :
    antighostZero (matterSVA L) c ((lamBRST L) n z) = (lamBRST L) n (antighostZero (matterSVA L) c
        z) := by
  rw [antighostZero_eq]
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
      simp only [lamBRST, TensorProduct.map_tmul, LinearMap.id_apply]
      congr 1
      exact LinearMap.congr_fun (lamG_comm_antiMode_zero c n.toNat) y
  | add u v hu hv => rw [map_add, map_add, hu, hv, map_add, map_add]

/-- `Λ` commutes with the total current zero modes on the BRST space. -/
theorem lamBRST_totalCurrentZero (n : ℤ) (a : Fin 3) (z : (BRSTSpace L)) :
    totalCurrentZero (matterAction L).toAffineSl2Action a ((lamBRST L) n z) =
      (lamBRST L) n (totalCurrentZero (matterAction L).toAffineSl2Action a z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
      rw [lamBRST_tmul, totalCurrentZero_tmul, totalCurrentZero_tmul, map_add, lamBRST_tmul,
        lamBRST_tmul]
      congr 2
      exact LinearMap.congr_fun (lamG_comm_ghostCurrent a n.toNat) y
  | add u v hu hv => rw [map_add, map_add, hu, hv, map_add, map_add]

/-- `Λ` preserves the relative carrier. -/
theorem lamBRST_mem_relativeCarrier (n : ℤ) {z : (BRSTSpace L)}
    (hz : z ∈ relativeCarrier (matterAction L).toAffineSl2Action) :
    (lamBRST L) n z ∈ relativeCarrier (matterAction L).toAffineSl2Action := by
  rw [mem_relativeCarrier] at hz ⊢
  refine ⟨fun a => ?_, fun a => ?_⟩
  · rw [lamBRST_totalCurrentZero, hz.1 a, map_zero]
  · rw [lamBRST_antighostZero, hz.2 a, map_zero]

/-- `Λ` preserves the BRST weight grading. -/
theorem lamBRST_mem_grading (n : ℤ) {h : ℂ} {z : (BRSTSpace L)} (hz : z ∈ (brstSVA L).grading h) :
    (lamBRST L) n z ∈ (brstSVA L).grading h := by
  change z ∈ TensorVA.tenGrading (matterSVA L) sl2GhostSVA h at hz
  change (lamBRST L) n z ∈ TensorVA.tenGrading (matterSVA L) sl2GhostSVA h
  refine TensorVA.tenGrading_induction (matterSVA L) sl2GhostSVA
    (motive := fun z => (lamBRST L) n z ∈ TensorVA.tenGrading (matterSVA L) sl2GhostSVA h)
    (by simp) (fun x y hx hy => by
      beta_reduce at hx hy ⊢; rw [map_add]; exact Submodule.add_mem _ hx hy)
    (fun c x hx => by beta_reduce at hx ⊢; rw [map_smul]; exact Submodule.smul_mem _ c hx) ?_ hz
  intro h₁ x hx y hy
  rw [lamBRST_tmul]
  exact TensorVA.tmul_mem_tenGrading (matterSVA L) sl2GhostSVA hx (lamG_mem_grading _ hy)

/-- **`Λ` preserves every relative weight space.** -/
theorem lamBRST_mem_relativeWeight (n : ℤ) {z : (BRSTSpace L)} (hz : z ∈ (relativeWeight L) n) :
    (lamBRST L) n z ∈ (relativeWeight L) n :=
  ⟨(lamBRST_mem_relativeCarrier L) n hz.1, (lamBRST_mem_grading L) n hz.2⟩

/-! ### The `(0, -2)` shift -/

/-- `Λ` shifts the fine BRST grading by `lamShiftF`. -/
theorem lamBRST_shiftF (n : ℤ) (k : KF) {z : (BRSTSpace L)} (hz : z ∈ (brstDegF L) k) :
    (lamBRST L) n z ∈ (brstDegF L) (k + lamShiftF) := by
  have := tensorDeg_map_shift (matterF L) ghostDegF LinearMap.id (lamG n.toNat) 0 lamShiftF
    (fun i x hx => by rw [add_zero]; exact hx) (fun i y hy => lamG_shiftF _ i hy) k z hz
  rwa [zero_add] at this

/-- **`Λ` shifts the interpreted `(2R, gh)` grading by `(0, -2)`**, for every standard ghost
grading. -/
theorem lamBRST_shift {PG : SesqForm Sl2GhostSpace} {Gh : GhostRGrading PG} (hs : Gh.IsStd)
    (n j g : ℤ) (h : ℂ) {z : (BRSTSpace L)} (hz : z ∈ (brstDeg L) Gh ((j, g), h)) :
    (lamBRST L) n z ∈ (brstDeg L) Gh ((j, g - 2), h) := by
  rw [(brstDeg_std L) hs] at hz ⊢
  have hz' := (brstDeg_le_coarsenF L) unitWeight _ hz
  refine Submodule.iSup_induction _ (motive := fun z =>
    (lamBRST L) n z ∈ (brstDeg L) (ghostRGrading unitWeight) ((j, g - 2), h)) hz' ?_ (by simp)
    (fun x y hx hy => by beta_reduce at hx hy ⊢; rw [map_add]; exact Submodule.add_mem _ hx hy)
  intro k y hy
  refine Submodule.iSup_induction _ (motive := fun y =>
    (lamBRST L) n y ∈ (brstDeg L) (ghostRGrading unitWeight) ((j, g - 2), h)) hy ?_ (by simp)
    (fun x y hx hy => by beta_reduce at hx hy ⊢; rw [map_add]; exact Submodule.add_mem _ hx hy)
  intro hk y hy
  have h1 := (brstDegF_le_brstDeg L) unitWeight _ ((lamBRST_shiftF L) n k hy)
  have e : fstF (k + lamShiftF) = ((j, g - 2), h) := by
    rw [map_add, hk]
    change ((j, g), h) + (((0, -2), 0) : (ℤ × ℤ) × ℂ) = _
    simp only [Prod.mk_add_mk, add_zero]
    congr 2
  rwa [e] at h1


/-! ## Port of `BGPackageReduced` -/


/-! ### Generic algebra -/

section GenericRing

variable {A : Type*} [Ring A] [Algebra ℂ A]

end GenericRing

section GenericForm

variable {K : Type*} [AddCommGroup K] [Module ℂ K]

end GenericForm

section GenericSVA

variable {M : Type uM} [AddCommGroup M] [Module ℂ M] {V : SuperVertexAlgebra M} {k : ℂ}

end GenericSVA

/-! ### The modes on the BRST space -/

/-- The matter action of the Lee–Yang complex. -/
abbrev matterAffineAction : AffineSl2Action (matterSVA L) (-4) := (matterAction L).toAffineSl2Action

/-- The antighost mode `b^a_{(m)}` on the BRST space. -/
def bB (a : Fin 3) (m : ℤ) : Module.End ℂ (BRSTSpace L) := (antiMode a m).lTensor (MatterSpace L)

/-- The total current mode `J^a_{tot,(m)}` on the BRST space. -/
def JT (a : Fin 3) (m : ℤ) : Module.End ℂ (BRSTSpace L) :=
  mode (TensorVA.tenY (matterSVA L) sl2GhostSVA (totalCurrentState (matterAffineAction L) a)) m

theorem bB_eq_mode (a : Fin 3) (m : ℤ) :
    (bB L) a m = mode (TensorVA.tenY (matterSVA L) sl2GhostSVA (tensorAntighost (matterSVA L) a))
        m := by
  apply TensorProduct.ext'
  intro x y
  rw [mode_apply]
  change _ = TensorVA.tenY (matterSVA L) sl2GhostSVA ((matterSVA L).vacuum ⊗ₜ[ℂ] bGhost a) (-m - 1)
    (x ⊗ₜ[ℂ] y)
  rw [tenY_right_unit_parity (matterSVA L) sl2GhostSVA (bGhost_odd a) ((matter_mem_parity_zero L)
      x) y
    (-m - 1)]
  simp [bB, koszul, antiMode, ConcreteHodge.gMode]

/-- **`{Q, b^a_{(m)}} = J^a_{tot,(m)}` on the BRST space.** -/
theorem brstQ_bB (a : Fin 3) (m : ℤ) : (brstQ L) * (bB L) a m + (bB L) a m * (brstQ L) = (JT L) a
    m := by
  change semiInfiniteQ (matterAffineAction L) * (bB L) a m +
      (bB L) a m * semiInfiniteQ (matterAffineAction L) = (JT L)
      a m
  rw [bB_eq_mode]
  exact semiInfiniteQ_antighost_mode (matterAffineAction L) (matterParityCompatible L)
      (matterGhostTensorGrading L)
    (matterGhost_zeroModeCommutator (matterAction L).translation
      (matterParityCompatible L) (matterGhostTensorGrading L)) a m

/-- `Λ` on the BRST space as a combination of BRST antighost modes. -/
theorem lamBRST_eq (n : ℤ) :
    (lamBRST L) n = ∑ m ∈ Finset.Icc 1 n.toNat, (1 / (m : ℂ)) •
      casContract (fun a => (bB L) a (-(m : ℤ))) (fun b => (bB L) b m) := by
  apply TensorProduct.ext'
  intro x y
  simp only [lamBRST_tmul, lamG, lamTerm, casContract, bB, LinearMap.sum_apply,
    LinearMap.smul_apply, Module.End.mul_apply, LinearMap.lTensor_tmul, TensorProduct.tmul_sum,
    TensorProduct.tmul_smul]

/-- `E = [Λ, Q]` on the BRST space. -/
def brstE (n : ℤ) : Module.End ℂ (BRSTSpace L) := (lamBRST L) n * (brstQ L) - (brstQ L) * (lamBRST
    L) n

/-- **The closed form of `E = [Λ, Q]`.** -/
theorem brstE_eq (n : ℤ) :
    (brstE L) n = closedE (bB L) (JT L) (Finset.Icc 1 n.toNat) (fun m => 1 / (m : ℂ)) := by
  have hterm : ∀ m : ℕ, casContract (fun a => (bB L) a (-(m : ℤ))) (fun b => (bB L) b m) * (brstQ
      L) -
      (brstQ L) * casContract (fun a => (bB L) a (-(m : ℤ))) (fun b => (bB L) b m) =
      casContract (fun a => (bB L) a (-(m : ℤ))) (fun b => (JT L) b m) -
        casContract (fun a => (JT L) a (-(m : ℤ))) (fun b => (bB L) b m) := fun m =>
    casContract_comm_Q (brstQ L) _ _ _ _ (fun a => (brstQ_bB L) a _) (fun a => (brstQ_bB L) a _)
  apply LinearMap.ext
  intro z
  have hz : ∀ m : ℕ, casContract (fun a => (bB L) a (-(m : ℤ))) (fun b => (bB L) b m) ((brstQ L) z)
      -
      (brstQ L) (casContract (fun a => (bB L) a (-(m : ℤ))) (fun b => (bB L) b m) z) =
      casContract (fun a => (bB L) a (-(m : ℤ))) (fun b => (JT L) b m) z -
        casContract (fun a => (JT L) a (-(m : ℤ))) (fun b => (bB L) b m) z := fun m =>
    LinearMap.congr_fun (hterm m) z
  simp only [brstE, closedE, lamBRST_eq, LinearMap.sub_apply, Module.End.mul_apply,
    LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← smul_sub, hz]

/-! ### Dead end: the antighost zero modes are not `B`-skew -/

/-! ### The reduced package -/

namespace BGReducedData

variable {PG : SesqForm Sl2GhostSpace} {Gh : GhostRGrading PG}
  {hA : GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag L)}
  {BB : InvariantForm BVOA} {RB : RealStructure BVOA}

end BGReducedData

/-! ### The Beem–Garner colour-weighted ghost form -/


/-! ## Port of `BGPackageTensor` -/


/-! ### Generic tensor lemmas -/

section GenericTensor

variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

end GenericTensor

/-! ### The total current modes split -/

/-- The matter current mode `J^a_{(k)}`. -/
abbrev matterJ (a : Fin 3) (k : ℤ) : Module.End ℂ (MatterSpace L) :=
  mode ((matterSVA L).Y ((matterAffineAction L).current a)) k

theorem JT_eq (a : Fin 3) (k : ℤ) :
    (JT L) a k = ((matterJ L) a k).rTensor Sl2GhostSpace + (ghostJ a k).lTensor (MatterSpace L) :=
        by
  apply TensorProduct.ext'
  intro x y
  unfold JT totalCurrentState
  rw [map_add, mode_add, LinearMap.add_apply, mode_apply, mode_apply]
  rw [tenY_left_unit, tenY_right_unit_even (matterSVA L) sl2GhostSVA (ghostCurrent_even a)]
  rfl

/-! ### `c₀`-freeness -/

/-! ### The fine decomposition of relative states -/

section Decomp

variable (hA : GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag L))
  {BB : InvariantForm BVOA} {RB : RealStructure BVOA} (hB : ConcreteHodge.Unitary BB RB)

include hA hB

theorem relative_fine_c0 {n : ℤ} {x : (BRSTSpace L)} (hx : x ∈ (relativeWeight L) n) :
    x ∈ ⨆ (k : KF) (_ : k.2 = 0), (brstDegF L) k :=
  (relative_c0free L) hA hB unitWeight unitWeight_pos fun a =>
    ((mem_relativeCarrier _ x).mp hx.1).2 a

theorem relative_fine_weight {n : ℤ} {x : (BRSTSpace L)} (hx : x ∈ (relativeWeight L) n) :
    x ∈ ⨆ (k : KF) (_ : k.1.2 = (n : ℂ) ∧ k.2 = 0), (brstDegF L) k := by
  classical
  have hI := (brstDegF_isInternal L) hA hB unitWeight unitWeight_pos
  refine mem_iSup_pred_inf hI ?_ ((relative_fine_c0 L) hA hB hx)
  rw [mem_iSup_pred_iff hI]
  intro k hk
  exact iproj_eq_zero_of_weight hI (brstSVA L).isInternal (fun k : KF => k.1.2)
    (fun k => ((brstDegF_le_brstDeg L) unitWeight k).trans
      ((brstDeg_le_weight L) (ghostRGrading unitWeight) (fstF k))) hx.2 hk

theorem relative_fine_deg {PG : SesqForm Sl2GhostSpace} {Gh : GhostRGrading PG} (hs : Gh.IsStd)
    {n : ℤ} {i : (ℤ × ℤ) × ℂ} {x : (BRSTSpace L)} (hx : x ∈ (relativeWeight L) n)
    (hxd : x ∈ (brstDeg L) Gh i) :
    x ∈ ⨆ (k : KF) (_ : fstF k = i ∧ k.2 = 0), (brstDegF L) k := by
  have hI := (brstDegF_isInternal L) hA hB unitWeight unitWeight_pos
  rw [(brstDeg_std L) hs] at hxd
  exact mem_iSup_pred_inf hI ((brstDeg_le_coarsenF L) unitWeight i hxd) ((relative_fine_c0 L) hA hB
      hx)

end Decomp

/-! ### The factor data -/

/-- The product form on the matter factor. -/
def matterForm (hA : GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag L))
    (BB : InvariantForm BVOA) (RB : RealStructure BVOA) : SesqForm (MatterSpace L) :=
  ((carrierForm (affineForm L) (affineRealStructure L) (affineFlag L) hA (affineGramRefl L)).tensor
    (unitaryCarrierForm BB RB)).tensor
    (carrierForm (auxiliaryForm L) (auxiliaryRealStructure L) (auxiliaryFlag L)
        (auxiliaryGradedUnitary L)
      (auxiliaryGramRefl L))

theorem matterGhostForm_eq (hA : GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag
    L))
    (BB : InvariantForm BVOA) (RB : RealStructure BVOA) (PG : SesqForm Sl2GhostSpace) :
    (matterGhostForm L) hA BB RB PG = ((matterForm L) hA BB RB).tensor PG := rfl

/-- **The matter factor of the Beem–Garner data.** -/
structure MatterBGData (hA : GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag L))
    (BB : InvariantForm BVOA) (RB : RealStructure BVOA) where
  B : LinearMap.BilinForm ℂ (MatterSpace L)
  ρ : (MatterSpace L) →ₗ⋆[ℂ] (MatterSpace L)
  s : ℂ
  ρ_sq : ∀ x, ρ (ρ x) = s • x
  /-- `P_M = i^{2R} B_M(ρ_M ·, ·)` on every interpreted matter piece. -/
  P_eq : ∀ i, ∀ x ∈ (matterDeg L) i, ∀ y, (matterForm L) hA BB RB x y = Complex.I ^ i.1.1 * B (ρ x)
      y
  ρ_deg : ∀ i, ∀ x ∈ (matterDeg L) i, ρ x ∈ (matterDeg L) (conjIdx i)
  /-- Compact conjugation of the current zero modes. -/
  ρ_J0 : ∀ (a : Fin 3) (x : (MatterSpace L)),
    ρ ((matterJ L) a 0 x) = -(matterJ L) (AffineVOA.HighestModule.adjointColour a) 0 (ρ x)

/-! ### The product data on the fine pieces -/

section Assembly

variable {hA : GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag L)}
  {BB : InvariantForm BVOA} {RB : RealStructure BVOA} {PG : SesqForm Sl2GhostSpace}

/-- The product conjugation `ρ_M ⊗ ρ_G`. -/
def brstρ (M : (MatterBGData L) hA BB RB) (G : GhostBGData PG) : (BRSTSpace L) →ₗ⋆[ℂ] (BRSTSpace
    L) :=
  TensorProduct.map M.ρ G.ρ

/-- The product bilinear form `B_M ⊗ B_G`. -/
def brstB (M : (MatterBGData L) hA BB RB) (G : GhostBGData PG) : LinearMap.BilinForm ℂ (BRSTSpace
    L) :=
  M.B.tmul G.B

theorem matterF_cases {b : KF} {x : (MatterSpace L)} (hx : x ∈ (matterF L) b) :
    x = 0 ∨ (b.2 = 0 ∧ x ∈ (matterDeg L) b.1) := by
  unfold matterF at hx
  split_ifs at hx with h
  · exact Or.inr ⟨h, hx⟩
  · exact Or.inl ((Submodule.mem_bot ℂ).mp hx)

variable (M : (MatterBGData L) hA BB RB) (G : GhostBGData PG)

theorem fine_P (k : KF) (hk : k.2 = 0) : ∀ z ∈ (brstDegF L) k, ∀ Y,
    (matterGhostForm L) hA BB RB PG z Y = Complex.I ^ k.1.1.1 * (brstB L) M G ((brstρ L) M G z)
        Y := by
  refine tensorDeg_induction (matterF L) ghostDegF k _ (fun Y => by
      rw [SesqForm.zero_left, map_zero, map_zero, LinearMap.zero_apply, mul_zero])
    (fun z z' hz hz' Y => by
      rw [SesqForm.add_left, hz, hz', map_add, map_add, LinearMap.add_apply, mul_add])
    (fun c z hz Y => by
      rw [SesqForm.smul_left, hz, LinearMap.map_smulₛₗ, map_smul, LinearMap.smul_apply,
        smul_eq_mul]
      ring) ?_
  intro b x hx y hy Y
  rcases (matterF_cases L) hx with rfl | ⟨hb, hx⟩
  · rw [TensorProduct.zero_tmul, SesqForm.zero_left, map_zero, map_zero, LinearMap.zero_apply,
      mul_zero]
  · rw [matterGhostForm_eq, tensorP_tmul ((matterForm L) hA BB RB) PG M.B G.B M.ρ G.ρ
      (M.P_eq b.1 x hx) (G.P_eq (k - b) (sub_snd_zero hk hb) y hy) Y]
    congr 1
    rw [← zpow_add₀ Complex.I_ne_zero]
    congr 1
    simp only [Prod.fst_sub]
    ring

theorem fine_D (k : KF) (hk : k.2 = 0) : ∀ z ∈ (brstDegF L) k, (brstρ L) M G z ∈ (brstDegF L)
    (conjF k) := by
  refine tensorDeg_induction (matterF L) ghostDegF k _
    (by rw [map_zero]; exact Submodule.zero_mem _)
    (fun z z' hz hz' => by rw [map_add]; exact Submodule.add_mem _ hz hz')
    (fun c z hz => by rw [LinearMap.map_smulₛₗ]; exact Submodule.smul_mem _ _ hz) ?_
  intro b x hx y hy
  rcases (matterF_cases L) hx with rfl | ⟨hb, hx⟩
  · rw [TensorProduct.zero_tmul, map_zero]; exact Submodule.zero_mem _
  · have h1 : M.ρ x ∈ (matterF L) (conjF b) := by
      have : (matterF L) (conjF b) = (matterDeg L) (conjIdx b.1) := by
        simp [matterF, conjF, hb]
      rw [this]; exact M.ρ_deg b.1 x hx
    have h2 := G.ρ_deg (k - b) (sub_snd_zero hk hb) y hy
    have h3 := tmul_mem_tensorDeg (matterF L) ghostDegF h1 h2
    rw [← conjF_add, add_sub_cancel] at h3
    exact h3

theorem fine_S (k : KF) (hk : k.2 = 0) : ∀ z ∈ (brstDegF L) k,
    (brstρ L) M G ((brstρ L) M G z) = (M.s * G.s) • z := by
  refine tensorDeg_induction (matterF L) ghostDegF k _ (by simp)
    (fun z z' hz hz' => by rw [map_add, map_add, hz, hz', smul_add])
    (fun c z hz => by
      rw [LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, hz, smul_comm]
      simp) ?_
  intro b x hx y hy
  rcases (matterF_cases L) hx with rfl | ⟨hb, hx⟩
  · simp
  · exact tensorMap_sq_tmul M.ρ G.ρ (M.ρ_sq x) (G.ρ_sq (k - b) (sub_snd_zero hk hb) y hy)

theorem fine_J (k : KF) (hk : k.2 = 0) (a : Fin 3) : ∀ z ∈ (brstDegF L) k,
    totalCurrentZero (matterAffineAction L) a ((brstρ L) M G z) =
      -(brstρ L) M G (totalCurrentZero (matterAffineAction L)
        (AffineVOA.HighestModule.adjointColour a) z) :=
          by
  refine tensorDeg_induction (matterF L) ghostDegF k _ (by simp)
    (fun z z' hz hz' => by rw [map_add, map_add, hz, hz', map_add, map_add, neg_add])
    (fun c z hz => by
      rw [LinearMap.map_smulₛₗ, map_smul, hz, map_smul, LinearMap.map_smulₛₗ, smul_neg]) ?_
  intro b x hx y hy
  rcases (matterF_cases L) hx with rfl | ⟨hb, _⟩
  · simp
  · have hy' := G.ρ_J0 (k - b) (sub_snd_zero hk hb) y hy
      (AffineVOA.HighestModule.adjointColour a)
    rw [AffineVOA.HighestModule.adjointColour_involutive] at hy'
    have hx' := M.ρ_J0 (AffineVOA.HighestModule.adjointColour a) x
    rw [AffineVOA.HighestModule.adjointColour_involutive] at hx'
    simp only [brstρ, TensorProduct.map_tmul, totalCurrentZero_tmul, map_add]
    change (matterJ L) a 0 (M.ρ x) ⊗ₜ[ℂ] G.ρ y + M.ρ x ⊗ₜ[ℂ] ghostJ a 0 (G.ρ y) =
      -(M.ρ ((matterJ L) _ 0 x) ⊗ₜ[ℂ] G.ρ y + M.ρ x ⊗ₜ[ℂ] G.ρ (ghostJ _ 0 y))
    rw [hx', hy', TensorProduct.neg_tmul, TensorProduct.tmul_neg, neg_add, neg_neg, neg_neg]

/-- The antighost zero modes kill the `c₀`-free fine BRST pieces. -/
theorem antighostZero_fine (k : KF) (hk : k.2 = 0) (a : Fin 3) :
    ∀ z ∈ (brstDegF L) k, antighostZero (matterSVA L) a z = 0 := by
  rw [antighostZero_eq]
  refine tensorDeg_induction (matterF L) ghostDegF k _ (by simp)
    (fun z z' hz hz' => by rw [map_add, hz, hz', add_zero])
    (fun c z hz => by rw [map_smul, hz, smul_zero]) ?_
  intro b x hx y hy
  rcases (matterF_cases L) hx with rfl | ⟨hb, _⟩
  · simp
  · rw [TensorProduct.map_tmul]
    change x ⊗ₜ[ℂ] antiMode a 0 y = 0
    rw [antiMode_zero_c0free a (sub_snd_zero hk hb) hy, TensorProduct.tmul_zero]

/-- Extending a statement from the `c₀`-free fine pieces to their span. -/
theorem iSup_fine_induction {S : KF → Prop} (Φ : (BRSTSpace L) → Prop) (h0 : Φ 0)
    (hadd : ∀ x y, Φ x → Φ y → Φ (x + y)) (hpiece : ∀ k, S k → ∀ z ∈ (brstDegF L) k, Φ z)
    {x : (BRSTSpace L)} (hx : x ∈ ⨆ (k : KF) (_ : S k), (brstDegF L) k) : Φ x := by
  refine Submodule.iSup_induction _ (motive := Φ) hx ?_ h0 hadd
  intro k z hz
  refine Submodule.iSup_induction _ (motive := Φ) hz ?_ h0 hadd
  intro hk z hz
  exact hpiece k hk z hz

end Assembly

/-! ### The reduced data from the factors -/

namespace BGFactorData

variable {PG : SesqForm Sl2GhostSpace} {Gh : GhostRGrading PG}
  {hA : GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag L)}
  {BB : InvariantForm BVOA} {RB : RealStructure BVOA}

end BGFactorData


/-! ## Port of `BGPackageMatter` -/


/-! ### Generic: the layer identity -/

section GenericLayer

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

namespace CompactLayerData

variable {B : InvariantForm W} {R : RealStructure W} {F : GradedFlag W}
  (hC : CompactLayerData B R F)
include hC

end CompactLayerData

/-! ### The trivial grading -/

end GenericLayer

/-! ### Compact conjugation preserves the corrected flag -/

section Corrected

variable {k : ℂ} {hk : k + 2 ≠ 0} {R : RealStructure (universal k hk)}
  (hR : IsCompactRealStructure R)
include hR

end Corrected

/-! ### The affine factor -/

private theorem affineConj_apply_mkQ (x : WakModule L.kA) :
    (affineRealStructure L).rho ((QuotVOA.maxGradedIdeal (universal L.kA L.aNoncritical)).mkQ x) =
      (QuotVOA.maxGradedIdeal (universal L.kA L.aNoncritical)).mkQ
        ((compactRealStructure L.aReal L.aNoncritical).rho x) := rfl

/-- **The compactness hypotheses for `L_{-4/3}(sl₂)`**, all proved. -/
theorem affineCompactLayerData :
    CompactLayerData (affineForm L) (affineRealStructure L) (affineFlag L) where
  flag p n x hx := by
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
    rw [affineConj_apply_mkQ]
    have hR := compactRealStructure_isCompact L.aReal L.aNoncritical
    exact Submodule.mem_map_of_mem ⟨rho_correctedPiece hR hy.1, hR.rho_mem_grading hy.2⟩
  conj a b := by
    obtain ⟨a, rfl⟩ := (QuotVOA.maxGradedIdeal (universal L.kA L.aNoncritical)).mkQ_surjective a
    obtain ⟨b, rfl⟩ := (QuotVOA.maxGradedIdeal (universal L.kA L.aNoncritical)).mkQ_surjective b
    rw [affineConj_apply_mkQ, affineConj_apply_mkQ]
    change (simpleForm L.kA L.aNoncritical).form _ _ =
      (starRingEnd ℂ) ((simpleForm L.kA L.aNoncritical).form _ _)
    rw [simpleForm_mkQ, simpleForm_mkQ]
    have h := universalForm_compactRho L.aNoncritical (hreal := L.aReal) a b
    rw [← h, Complex.conj_conj]
    rfl
  symm := simpleForm_isSymmetric L.kA L.aNoncritical
  sq x := by
    obtain ⟨x, rfl⟩ := (QuotVOA.maxGradedIdeal (universal L.kA L.aNoncritical)).mkQ_surjective x
    rw [affineConj_apply_mkQ, affineConj_apply_mkQ]
    exact congrArg _ (compactRho_compactRho L.aReal x)

/-- **The compactness hypotheses for the auxiliary factor**, all proved. -/
theorem auxiliaryCompactLayerData :
    CompactLayerData (auxiliaryForm L) (auxiliaryRealStructure L) (auxiliaryFlag L) where
  flag p n x hx :=
    (compactRealStructure_isCompact L.uReal L.uNoncritical).rho_mem_ordinaryFlag hx
  conj a b := by
    have h := universalForm_compactRho L.uNoncritical (hreal := L.uReal) a b
    rw [← h, Complex.conj_conj]
    rfl
  symm := universalForm_isSymmetric L.kU L.uNoncritical
  sq x := compactRho_compactRho L.uReal x

/-! ### Generic tensor lemmas with gradings -/

section TensorDeg

variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

end TensorDeg

/-! ### The three matter conjugations -/

/-- The matter conjugation `ρ_A ⊗ ρ_B ⊗ ρ_U`. -/
def matterRho (RB : RealStructure BVOA) : (MatterSpace L) →ₗ⋆[ℂ] (MatterSpace L) :=
  TensorProduct.map (TensorProduct.map (rsLin (affineRealStructure L)) (rsLin RB))
    (rsLin (auxiliaryRealStructure L))

/-- The matter bilinear form `B_A ⊗ B_B ⊗ B_U`. -/
def matterB (BB : InvariantForm BVOA) : LinearMap.BilinForm ℂ (MatterSpace L) :=
  LinearMap.BilinForm.tmul (LinearMap.BilinForm.tmul (affineForm L).form BB.form) (auxiliaryForm
      L).form

theorem aMode_rho (a : Fin 3) (n : ℤ) (x : (ASpace L)) :
    (affineRealStructure L).rho ((aMode L) a n x) =
      -(aMode L) (AffineVOA.HighestModule.adjointColour a) n ((affineRealStructure L).rho x) := by
  obtain ⟨x, rfl⟩ := (QuotVOA.maxGradedIdeal (universal L.kA L.aNoncritical)).mkQ_surjective x
  rw [aMode_mkQ, affineConj_apply_mkQ, affineConj_apply_mkQ, aMode_mkQ, ← map_neg]
  exact congrArg _ (compactRho_J L.aReal (k := L.kA) a n x)

theorem uMode_rho (a : Fin 3) (n : ℤ) (x : (USpace L)) :
    (auxiliaryRealStructure L).rho ((uMode L) a n x) =
      -(uMode L) (AffineVOA.HighestModule.adjointColour a) n ((auxiliaryRealStructure L).rho x) :=
          by
  rw [uMode_apply, uMode_apply]
  exact compactRho_J L.uReal a n x

theorem uMode_skew (a : Fin 3) (n : ℤ) (x y : (USpace L)) :
    (auxiliaryForm L).form ((uMode L) a n x) y = -(auxiliaryForm L).form x ((uMode L) a (-n) y) :=
        by
  rw [uMode_apply, uMode_apply]
  exact universalForm_current_adj L.uNoncritical a n x y

theorem matterJ_eq (a : Fin 3) (n : ℤ) :
    (matterJ L) a n = (((aMode L) a n).rTensor BSpace + (bMode a n).lTensor (ASpace L)).rTensor
        (USpace L) +
      ((uMode L) a n).lTensor ((ASpace L) ⊗[ℂ] BSpace) := by
  rw [matterJ, matterMode_eq, LinearMap.rTensor_add]
  rfl

/-! ### The matter factor data -/

theorem matterRho_J0 (RB : RealStructure BVOA) (hCB : ∀ (a : Fin 3) (n : ℤ) (x : BSpace),
    RB.rho (bMode a n x) = -bMode (AffineVOA.HighestModule.adjointColour a) n (RB.rho x))
    (a : Fin 3) (x : (MatterSpace L)) :
    (matterRho L) RB ((matterJ L) a 0 x) =
      -(matterJ L) (AffineVOA.HighestModule.adjointColour a) 0 ((matterRho L) RB x) := by
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
factor `B` only: the affine and auxiliary factors are fully proved (`affineCompactLayerData L`,
`auxiliaryCompactLayerData L`, current skewness and compact conjugation of the current modes). -/
def matterBGData (hA : GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag L))
    {BB : InvariantForm BVOA} {RB : RealStructure BVOA} (hCB : CompactUnitaryB BB RB) :
    (MatterBGData L) hA BB RB where
  B := (matterB L) BB
  ρ := (matterRho L) RB
  s := 1
  ρ_sq x := by
    have h := tensorMap_sq (TensorProduct.map (rsLin (affineRealStructure L)) (rsLin RB))
      (rsLin (auxiliaryRealStructure L)) (sV := 1 * 1) (sW := 1)
      (fun z => tensorMap_sq _ _ (fun x => by simp [(affineCompactLayerData L).sq])
        (fun y => by simp [hCB.sq]) z)
      (fun y => by simp [(auxiliaryCompactLayerData L).sq]) x
    simpa using h
  P_eq i x hx y :=
    tensorP_deg _ _ _ _ (TensorProduct.map (rsLin (affineRealStructure L)) (rsLin RB))
      (rsLin (auxiliaryRealStructure L)) _ _
      (tensorP_deg _ _ (affineForm L).form BB.form (rsLin (affineRealStructure L)) (rsLin RB) (aDeg
          L) bDeg
        ((affineCompactLayerData L).layerDeg_P_eq hA (affineGramRefl L))
        (trivialDeg_P_eq BB RB))
      ((auxiliaryCompactLayerData L).layerDeg_P_eq (auxiliaryGradedUnitary L) (auxiliaryGramRefl
          L)) i x hx y
  ρ_deg i x hx := by
    have h := tensorMap_deg (TensorProduct.map (rsLin (affineRealStructure L)) (rsLin RB))
      (rsLin (auxiliaryRealStructure L)) _ _
      (tensorMap_deg (rsLin (affineRealStructure L)) (rsLin RB) (aDeg L) bDeg
        ((affineCompactLayerData L).layerDeg_rho) (trivialDeg_rho RB))
      ((auxiliaryCompactLayerData L).layerDeg_rho) i x hx
    by_cases hg : i.1.2 = 0
    · have e : conjIdx i = i := by
        obtain ⟨⟨j, g⟩, h'⟩ := i
        simp only at hg
        simp [conjIdx, hg]
      rw [e]; exact h
    · have h0 := (matterDeg_le_zeroGhost L) i hx
      rw [eq_zero_of_mem_zeroGhost (by simpa using hg) h0, map_zero]
      exact Submodule.zero_mem _
  ρ_J0 a x := (matterRho_J0 L) RB hCB.rho_mode a x

/-- The matter currents are `B_M`-skew (proved; recorded for the `B_E` route through mode
transposes on the `c₀`-free subspace). -/
theorem matterB_current_skew {BB : InvariantForm BVOA} {RB : RealStructure BVOA}
    (hCB : CompactUnitaryB BB RB) (a : Fin 3) (k : ℤ) (x y : (MatterSpace L)) :
    (matterB L) BB ((matterJ L) a k x) y = -(matterB L) BB x ((matterJ L) a (-k) y) := by
  rw [matterJ_eq, matterJ_eq]
  exact tensorB_add_rTensor_lTensor _ _ _ _ _ _
    (fun u v => tensorB_add_rTensor_lTensor _ _ _ _ _ _ ((aMode_adj L) a k) (hCB.skew a k) u v)
    ((uMode_skew L) a k) x y


/-! ## Port of `BGPackageBFactor` -/


/-- **The matter factor of the Beem–Garner data, with no hypothesis besides `hA`.** -/
def bgMatterData (hA : GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag L)) :
    (MatterBGData L) hA bForm bRealStructure :=
  (matterBGData L) hA bCompactUnitary

/-! ### The remaining data -/


end

end VOA.TwoSeries
