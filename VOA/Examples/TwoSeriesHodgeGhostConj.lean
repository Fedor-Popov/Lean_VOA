/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.TwoSeriesHodgeBG
import VOA.Examples.GhostConjEndpoint

/-!
# Level-generic port of the level-specific parts of `GhostConj*`

The interpreted Beem–Garner packages `InterpretedBGPackageI L …`, the factor/reduced/global
chain `BGFactorDataI L` → `BGReducedDataI L` → `GlobalBGPackageI L`, and the ghost remainder
`bgGhostRemainderI L hA …` on the actual level-`L` complex.  Level-independent declarations
(the ghost Fock conjugation, `GhostConjFock`, `GhostConjJ0`) are reused directly.
-/

namespace VOA.TwoSeries

open VOA.ConcreteHodge Sl2CosetConcrete Sl2SemiInfinite AffineSl2GeneralRigidity
open AffineSl2BelowCritical VOA.GradedUnitaryCohomology VOA.LeeYangCosetTransfer
open VOA.VertexOperatorAlgebra VOA.LeeYangTransferAssembly LeeYangShortcut VirModule LeeYang
open VirGradedUnitarity VOA.SympFerm VOA.Ghost AffineVOA
open scoped TensorProduct

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

universe u v w

variable (L : CosetLevels)

/-! ## Port of `None` -/


variable {K : Type u} [AddCommGroup K] [Module ℂ K]

/-! ### The interpreted complex -/

section Interpreted

variable {PG : SesqForm Sl2GhostSpace} (Gh : GhostRGrading PG)
  (hA : GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag L))
  {BB : InvariantForm BVOA} {RB : RealStructure BVOA} (hB : ConcreteHodge.Unitary BB RB)
  (hG : IsPosOn PG ⊤) (hZ : (ZeroModesPreserve L) Gh) (hD : (RelativeDifferentialGood L) Gh)

/-- **The corrected Beem–Garner package for the actual relative complex**, at every weight. -/
abbrev InterpretedBGPackageI : Type :=
  ∀ n : ℤ, ((interpretedHalf L) Gh hA hB hG hZ hD n).Sp2PackageI

variable {Gh hA hB hG hZ hD}

section
variable {L}

/-- The `sp(2)` adjoint input from the corrected package. -/
def InterpretedBGPackageI.sp2 (Pk : (InterpretedBGPackageI L) Gh hA hB hG hZ hD) :
    (InterpretedSp2 L) Gh hA hB hG hZ hD :=
  fun n => (Pk n).toSp2Adjoint ((interpretedHalf_pos L) Gh hA hB hG hZ hD n)

end
section
variable {L}

/-- The ghost-number-zero conjugation input from the corrected package. -/
def InterpretedBGPackageI.conj0 (Pk : (InterpretedBGPackageI L) Gh hA hB hG hZ hD) (n : ℤ) hp :
    Sp2Conj0 (concreteGood ((interpretedGoodGeometry L) Gh hA hB hG hZ hD
      ((interpretedKahlerAnticomm_of_sp2 L) Gh hA hB hG hZ hD Pk.sp2)) n hp) (Pk.sp2 n).E :=
  (Pk n).toSp2Conj0 ((interpretedHalf_pos L) Gh hA hB hG hZ hD n) _ rfl rfl rfl

end
end Interpreted


/-! ## Port of `None` -/


/-! ### The global package -/

/-- **The corrected Beem–Garner package on the whole BRST space.** -/
structure GlobalBGPackageI {PG : SesqForm Sl2GhostSpace} (Gh : GhostRGrading PG)
    (hA : GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag L))
    (BB : InvariantForm BVOA) (RB : RealStructure BVOA) where
  Λ : ℤ → Module.End ℂ (BRSTSpace L)
  Λ_maps : ∀ n : ℤ, ∀ x ∈ (relativeWeight L) n, Λ n x ∈ (relativeWeight L) n
  Λ_shift : ∀ (n j g : ℤ), ∀ x ∈ (relativeWeight L) n, x ∈ (brstDeg L) Gh ((j, g), (n : ℂ)) →
    Λ n x ∈ (brstDeg L) Gh ((j, g - 2), (n : ℂ))
  B : LinearMap.BilinForm ℂ (BRSTSpace L)
  ρ : (BRSTSpace L) →ₗ⋆[ℂ] (BRSTSpace L)
  ρ_maps : ∀ n : ℤ, ∀ x ∈ (relativeWeight L) n, ρ x ∈ (relativeWeight L) n
  P_eq : ∀ (n j g : ℤ), ∀ x ∈ (relativeWeight L) n, x ∈ (brstDeg L) Gh ((j, g), (n : ℂ)) →
    ∀ y ∈ (relativeWeight L) n, (matterGhostForm L) hA BB RB PG x y = Complex.I ^ j * B (ρ x) y
  ρ_deg : ∀ (n j g : ℤ), ∀ x ∈ (relativeWeight L) n, x ∈ (brstDeg L) Gh ((j, g), (n : ℂ)) →
    ρ x ∈ (brstDeg L) Gh ((j, -g), (n : ℂ))
  s : ℂ
  hs : s ≠ 0
  ρ_sq : ∀ n : ℤ, ∀ x ∈ (relativeWeight L) n, ρ (ρ x) = s • x
  κ : ℂ
  hκ : κ ≠ 0
  ρ_D : ∀ (n j g : ℤ), ∀ x ∈ (relativeWeight L) n, x ∈ (brstDeg L) Gh ((j, g), (n : ℂ)) →
    ρ ((brstQ L) x) = (κ * (-1 : ℂ) ^ g) • (Λ n ((brstQ L) (ρ x)) - (brstQ L) (Λ n (ρ x)))
  B_E : ∀ (n j g : ℤ), ∀ u ∈ (relativeWeight L) n, u ∈ (brstDeg L) Gh ((j, g), (n : ℂ)) →
    ∀ v ∈ (relativeWeight L) n,
      B (Λ n ((brstQ L) u) - (brstQ L) (Λ n u)) v =
        Complex.I * (-1 : ℂ) ^ g * B u (Λ n ((brstQ L) v) - (brstQ L) (Λ n v))

namespace GlobalBGPackageI

variable {L}

variable {PG : SesqForm Sl2GhostSpace} {Gh : GhostRGrading PG}
  {hA : GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag L)}
  {BB : InvariantForm BVOA} {RB : RealStructure BVOA} (hB : ConcreteHodge.Unitary BB RB)
  (hG : IsPosOn PG ⊤) (hZ : (ZeroModesPreserve L) Gh) (hD : (RelativeDifferentialGood L) Gh)

/-- `Λ n` restricted to the relative weight space. -/
def Λr (Pk : (GlobalBGPackageI L) Gh hA BB RB) (n : ℤ) : (relativeWeight L) n →ₗ[ℂ] (relativeWeight
    L) n :=
  (Pk.Λ n).restrict (fun x hx => Pk.Λ_maps n x hx)

/-- `ρ` restricted to the relative weight space. -/
def ρr (Pk : (GlobalBGPackageI L) Gh hA BB RB) (n : ℤ) : (relativeWeight L) n →ₗ⋆[ℂ]
    (relativeWeight L) n :=
  LinearMap.codRestrict ((relativeWeight L) n) (Pk.ρ.comp ((relativeWeight L) n).subtype)
    (fun x => Pk.ρ_maps n x x.2)

/-- `B` restricted to the relative weight space. -/
def Br (Pk : (GlobalBGPackageI L) Gh hA BB RB) (n : ℤ) :
    LinearMap.BilinForm ℂ ((relativeWeight L) n) :=
  Pk.B.compl₁₂ ((relativeWeight L) n).subtype ((relativeWeight L) n).subtype

/-- **The per-weight corrected package by restriction.** -/
def toInterpreted (Pk : (GlobalBGPackageI L) Gh hA BB RB) :
    (InterpretedBGPackageI L) Gh hA hB hG hZ hD := fun n =>
  { Λ := Pk.Λr n
    shift := fun j g x hx => Pk.Λ_shift n j g x x.2 hx
    B := Pk.Br n
    ρ := Pk.ρr n
    P_eq := fun j g x hx y => by
      change (assemblyForm L) BB RB PG n x y = _
      rw [(assemblyForm_eq L) hA, SesqForm.restrict_apply]
      exact Pk.P_eq n j g x x.2 hx y y.2
    ρ_deg := fun j g x hx => Pk.ρ_deg n j g x x.2 hx
    s := Pk.s
    hs := Pk.hs
    ρ_sq := fun x => Subtype.ext (Pk.ρ_sq n x x.2)
    κ := Pk.κ
    hκ := Pk.hκ
    ρ_D := fun j g x hx => Subtype.ext (by
      change Pk.ρ ((brstQ L) x) = _
      rw [Pk.ρ_D n j g x x.2 hx]
      rfl)
    B_E := fun j g u hu v => Pk.B_E n j g u u.2 hu v v.2 }

end GlobalBGPackageI

/-! ### The reduced data -/

/-- **The corrected remaining data with `Λ = lamBRST L` constructed.** -/
structure BGReducedDataI {PG : SesqForm Sl2GhostSpace} (Gh : GhostRGrading PG)
    (hA : GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag L))
    (BB : InvariantForm BVOA) (RB : RealStructure BVOA) where
  B : LinearMap.BilinForm ℂ (BRSTSpace L)
  ρ : (BRSTSpace L) →ₗ⋆[ℂ] (BRSTSpace L)
  ρ_maps : ∀ n : ℤ, ∀ x ∈ (relativeWeight L) n, ρ x ∈ (relativeWeight L) n
  P_eq : ∀ (n j g : ℤ), ∀ x ∈ (relativeWeight L) n, x ∈ (brstDeg L) Gh ((j, g), (n : ℂ)) →
    ∀ y ∈ (relativeWeight L) n, (matterGhostForm L) hA BB RB PG x y = Complex.I ^ j * B (ρ x) y
  ρ_deg : ∀ (n j g : ℤ), ∀ x ∈ (relativeWeight L) n, x ∈ (brstDeg L) Gh ((j, g), (n : ℂ)) →
    ρ x ∈ (brstDeg L) Gh ((j, -g), (n : ℂ))
  s : ℂ
  hs : s ≠ 0
  ρ_sq : ∀ n : ℤ, ∀ x ∈ (relativeWeight L) n, ρ (ρ x) = s • x
  κ : ℂ
  hκ : κ ≠ 0
  ρ_D : ∀ (n j g : ℤ), ∀ x ∈ (relativeWeight L) n, x ∈ (brstDeg L) Gh ((j, g), (n : ℂ)) →
    ρ ((brstQ L) x) = (κ * (-1 : ℂ) ^ g) • (brstE L) n (ρ x)
  B_E : ∀ (n j g : ℤ), ∀ u ∈ (relativeWeight L) n, u ∈ (brstDeg L) Gh ((j, g), (n : ℂ)) →
    ∀ v ∈ (relativeWeight L) n, B ((brstE L) n u) v = Complex.I * (-1 : ℂ) ^ g * B u ((brstE L) n v)

section
variable {L}

/-- **The corrected global package from the reduced data**, with `Λ = lamBRST L`. -/
def BGReducedDataI.toGlobal {PG : SesqForm Sl2GhostSpace} {Gh : GhostRGrading PG}
    {hA : GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag L)}
    {BB : InvariantForm BVOA} {RB : RealStructure BVOA}
    (R : (BGReducedDataI L) Gh hA BB RB) (hs : Gh.IsStd) : (GlobalBGPackageI L) Gh hA BB RB where
  Λ := (lamBRST L)
  Λ_maps := fun n x hx => (lamBRST_mem_relativeWeight L) n hx
  Λ_shift := fun n j g x _ hx => (lamBRST_shift L) hs n j g _ hx
  B := R.B
  ρ := R.ρ
  ρ_maps := R.ρ_maps
  P_eq := R.P_eq
  ρ_deg := R.ρ_deg
  s := R.s
  hs := R.hs
  ρ_sq := R.ρ_sq
  κ := R.κ
  hκ := R.hκ
  ρ_D := fun n j g x hxr hx => by
    rw [R.ρ_D n j g x hxr hx]
    rfl
  B_E := fun n j g u hur hu v hv => R.B_E n j g u hur hu v hv

end
/-! ### The factor data -/

/-- **The corrected factor data**: matter and ghost factors, `ρ_D` and the corrected `B_E` for
the product conjugation and the product form. -/
structure BGFactorDataI {PG : SesqForm Sl2GhostSpace} (Gh : GhostRGrading PG)
    (hA : GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag L))
    (BB : InvariantForm BVOA) (RB : RealStructure BVOA) where
  M : (MatterBGData L) hA BB RB
  G : GhostBGData PG
  hsM : M.s ≠ 0
  hsG : G.s ≠ 0
  κ : ℂ
  hκ : κ ≠ 0
  ρ_D : ∀ (n j g : ℤ), ∀ x ∈ (relativeWeight L) n, x ∈ (brstDeg L) Gh ((j, g), (n : ℂ)) →
    (brstρ L) M G ((brstQ L) x) = (κ * (-1 : ℂ) ^ g) • (brstE L) n ((brstρ L) M G x)
  B_E : ∀ (n j g : ℤ), ∀ u ∈ (relativeWeight L) n, u ∈ (brstDeg L) Gh ((j, g), (n : ℂ)) →
    ∀ v ∈ (relativeWeight L) n,
      (brstB L) M G ((brstE L) n u) v = Complex.I * (-1 : ℂ) ^ g * (brstB L) M G u ((brstE L) n v)

namespace BGFactorDataI

variable {L}

variable {PG : SesqForm Sl2GhostSpace} {Gh : GhostRGrading PG}
  {hA : GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag L)}
  {BB : InvariantForm BVOA} {RB : RealStructure BVOA}

/-- `ρ_M ⊗ ρ_G` preserves the relative weight spaces (only the factor data are used). -/
theorem ρ_maps (M : (MatterBGData L) hA BB RB) (G : GhostBGData PG) (hB : ConcreteHodge.Unitary BB
    RB) (n : ℤ)
    (x : (BRSTSpace L)) (hx : x ∈ (relativeWeight L) n) : (brstρ L) M G x ∈ (relativeWeight L) n :=
        by
  have key : ∀ z ∈ ⨆ (k : KF) (_ : k.1.2 = (n : ℂ) ∧ k.2 = 0), (brstDegF L) k,
      (brstρ L) M G z ∈ (brstSVA L).grading (n : ℂ) ∧
        (∀ a, antighostZero (matterSVA L) a ((brstρ L) M G z) = 0) ∧
        (∀ a, totalCurrentZero (matterAffineAction L) a ((brstρ L) M G z) =
          -(brstρ L) M G (totalCurrentZero (matterAffineAction L)
            (AffineVOA.HighestModule.adjointColour a) z)) := by
    intro z hz
    refine (iSup_fine_induction L) (fun z => (brstρ L) M G z ∈ (brstSVA L).grading (n : ℂ) ∧
        (∀ a, antighostZero (matterSVA L) a ((brstρ L) M G z) = 0) ∧
        (∀ a, totalCurrentZero (matterAffineAction L) a ((brstρ L) M G z) =
          -(brstρ L) M G (totalCurrentZero (matterAffineAction L)
            (AffineVOA.HighestModule.adjointColour a) z)))
      ⟨by simp, fun a => by simp, fun a => by simp⟩
      (fun x y hx hy => ⟨by rw [map_add]; exact Submodule.add_mem _ hx.1 hy.1,
        fun a => by rw [map_add, map_add, hx.2.1 a, hy.2.1 a, add_zero],
        fun a => by rw [map_add, map_add, hx.2.2 a, hy.2.2 a, map_add, map_add, neg_add]⟩)
      ?_ hz
    rintro k ⟨hkn, hk⟩ z hz
    have hD := (fine_D L) M G k hk z hz
    refine ⟨?_, fun a => (antighostZero_fine L) (conjF k) (by simp [conjF, hk]) a _ hD,
      fun a => (fine_J L) M G k hk a z hz⟩
    have h1 := ((brstDegF_le_brstDeg L) unitWeight (conjF k)).trans
      ((brstDeg_le_weight L) (ghostRGrading unitWeight) (fstF (conjF k))) hD
    have e : wtIndex (fstF (conjF k)) = (n : ℂ) := by
      simp [conjF, conjIdx, wtIndex, hkn]
    rwa [e] at h1
  obtain ⟨h1, h2, h3⟩ := key x ((relative_fine_weight L) hA hB hx)
  refine ⟨(mem_relativeCarrier _ _).mpr ⟨fun a => ?_, h2⟩, h1⟩
  rw [h3 a, ((mem_relativeCarrier _ x).mp hx.1).1, map_zero, neg_zero]

/-- **The corrected reduced data from the factor data** (standard ghost grading). -/
def toReduced (F : (BGFactorDataI L) Gh hA BB RB) (hB : ConcreteHodge.Unitary BB RB) (hs :
    Gh.IsStd) :
    (BGReducedDataI L) Gh hA BB RB where
  B := (brstB L) F.M F.G
  ρ := (brstρ L) F.M F.G
  ρ_maps := fun n x hx => ρ_maps F.M F.G hB n x hx
  P_eq := fun n j g x hxr hx y _ => by
    refine (iSup_fine_induction L) (fun z => ∀ Y, (matterGhostForm L) hA BB RB PG z Y =
        Complex.I ^ j * (brstB L) F.M F.G ((brstρ L) F.M F.G z) Y)
      (fun Y => by rw [SesqForm.zero_left, map_zero, map_zero, LinearMap.zero_apply, mul_zero])
      (fun z z' hz hz' Y => by
        rw [SesqForm.add_left, hz, hz', map_add, map_add, LinearMap.add_apply, mul_add])
      ?_ ((relative_fine_deg L) hA hB hs hxr hx) y
    rintro k ⟨hki, hk⟩ z hz Y
    rw [(fine_P L) F.M F.G k hk z hz Y]
    have : k.1.1.1 = j := by
      have := congrArg (fun i : (ℤ × ℤ) × ℂ => i.1.1) hki
      simpa [fstF] using this
    rw [this]
  ρ_deg := fun n j g x hxr hx => by
    rw [(brstDeg_std L) hs]
    refine (iSup_fine_induction L) (fun z => (brstρ L) F.M F.G z ∈
        (brstDeg L) (ghostRGrading unitWeight) ((j, -g), (n : ℂ)))
      (by beta_reduce; rw [map_zero]; exact Submodule.zero_mem _)
      (fun z z' hz hz' => by
        beta_reduce at hz hz' ⊢; rw [map_add]; exact Submodule.add_mem _ hz hz')
      ?_ ((relative_fine_deg L) hA hB hs hxr hx)
    rintro k ⟨hki, hk⟩ z hz
    have h1 := (brstDegF_le_brstDeg L) unitWeight (conjF k) ((fine_D L) F.M F.G k hk z hz)
    have e : fstF (conjF k) = ((j, -g), (n : ℂ)) := by
      have h := hki
      simp only [fstF, AddMonoidHom.coe_fst] at h
      simp [fstF, conjF, conjIdx, h]
    rwa [e] at h1
  s := F.M.s * F.G.s
  hs := mul_ne_zero F.hsM F.hsG
  ρ_sq := fun n x hx => by
    refine (iSup_fine_induction L) (fun z => (brstρ L) F.M F.G ((brstρ L) F.M F.G z) = (F.M.s *
        F.G.s) • z)
      (by simp) (fun z z' hz hz' => by
        beta_reduce at hz hz' ⊢; rw [map_add, map_add, hz, hz', smul_add])
      ?_ ((relative_fine_c0 L) hA hB hx)
    intro k hk z hz
    exact (fine_S L) F.M F.G k hk z hz
  κ := F.κ
  hκ := F.hκ
  ρ_D := F.ρ_D
  B_E := F.B_E

end BGFactorDataI

/-! ### The corrected remainder and the endpoint -/

/-- **What remains of the corrected Beem–Garner package** once `Λ`, the matter factor
(`bgMatterData L`), the ghost form (`bgPG`) and the grading are fixed. -/
structure BGGhostRemainderI (hA : GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag
    L)) where
  G : GhostBGData bgPG
  hsG : G.s ≠ 0
  κ : ℂ
  hκ : κ ≠ 0
  ρ_D : ∀ (n j g : ℤ), ∀ x ∈ (relativeWeight L) n, x ∈ (brstDeg L) bgGh ((j, g), (n : ℂ)) →
    (brstρ L) ((bgMatterData L) hA) G ((brstQ L) x) =
      (κ * (-1 : ℂ) ^ g) • (brstE L) n ((brstρ L) ((bgMatterData L) hA) G x)
  B_E : ∀ (n j g : ℤ), ∀ u ∈ (relativeWeight L) n, u ∈ (brstDeg L) bgGh ((j, g), (n : ℂ)) →
    ∀ v ∈ (relativeWeight L) n,
      (brstB L) ((bgMatterData L) hA) G ((brstE L) n u) v =
        Complex.I * (-1 : ℂ) ^ g * (brstB L) ((bgMatterData L) hA) G u ((brstE L) n v)

section
variable {L}

/-- The corrected factor data from the corrected remainder. -/
def BGGhostRemainderI.toFactor {hA : GradedUnitary (affineForm L) (affineRealStructure L)
    (affineFlag L)}
    (Rm : (BGGhostRemainderI L) hA) : (BGFactorDataI L) bgGh hA bForm bRealStructure where
  M := (bgMatterData L) hA
  G := Rm.G
  hsM := one_ne_zero
  hsG := Rm.hsG
  κ := Rm.κ
  hκ := Rm.hκ
  ρ_D := Rm.ρ_D
  B_E := Rm.B_E

end
section
variable {L}

/-- The corrected per-weight package from the corrected remainder. -/
abbrev BGGhostRemainderI.pkg {hA : GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag
    L)}
    (hB : ConcreteHodge.Unitary bForm bRealStructure) (Rm : (BGGhostRemainderI L) hA) :
    (InterpretedBGPackageI L) bgGh hA hB bgPG_pos ((stdZ L) bgGh_isStd) ((stdD L) hA hB
        bgGh_isStd) :=
  ((Rm.toFactor.toReduced hB bgGh_isStd).toGlobal bgGh_isStd).toInterpreted hB bgPG_pos
    ((stdZ L) bgGh_isStd) ((stdD L) hA hB bgGh_isStd)

end


/-! ## Port of `None` -/


/-- The product conjugation `ρ_M ⊗ ρ_G` on the BRST space. -/
def ghConjBRST : (BRSTSpace L) →ₗ⋆[ℂ] (BRSTSpace L) :=
  TensorProduct.map ((matterRho L) bRealStructure) ghostConj

/-- The product bilinear form `B_M ⊗ B_G` on the BRST space. -/
def ghBBRST : LinearMap.BilinForm ℂ (BRSTSpace L) := ((matterB L) bForm).tmul ghostB

/-- **OPEN (numerically verified, relative weights `≤ 4`)**: `ρ 𝐐 = (-1)^{gh} [Λ, 𝐐] ρ` on relative
states, for `ρ = ρ_M ⊗ ρ_G`. -/
def GhostConjRhoD : Prop :=
  ∀ (n j g : ℤ), ∀ x ∈ (relativeWeight L) n, x ∈ (brstDeg L) bgGh ((j, g), (n : ℂ)) →
    (ghConjBRST L) ((brstQ L) x) = ((-1 : ℂ) ^ g) • (brstE L) n ((ghConjBRST L) x)

/-- **OPEN (numerically verified, relative weights `≤ 4`)**:
`B(E u, v) = i (-1)^{gh u} B(u, E v)` on
relative states, for `B = B_M ⊗ B_G`, `E = [Λ, 𝐐]`. -/
def GhostConjBE : Prop :=
  ∀ (n j g : ℤ), ∀ u ∈ (relativeWeight L) n, u ∈ (brstDeg L) bgGh ((j, g), (n : ℂ)) →
    ∀ v ∈ (relativeWeight L) n,
      (ghBBRST L) ((brstE L) n u) v = Complex.I * (-1 : ℂ) ^ g * (ghBBRST L) u ((brstE L) n v)

theorem brstρ_bgGhostData (hA : GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag
    L)) :
    (brstρ L) ((bgMatterData L) hA) bgGhostData = (ghConjBRST L) := rfl

theorem brstB_bgGhostData (hA : GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag
    L)) :
    (brstB L) ((bgMatterData L) hA) bgGhostData = (ghBBRST L) := rfl

/-- **The corrected remainder from the two concrete statements** (`κ = 1`). -/
def bgGhostRemainderI (hA : GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag L))
    (hD : (GhostConjRhoD L)) (hE : (GhostConjBE L)) : (BGGhostRemainderI L) hA where
  G := bgGhostData
  hsG := bgGhostData_s
  κ := 1
  hκ := one_ne_zero
  ρ_D := fun n j g x hxr hx => by
    rw [brstρ_bgGhostData, one_mul]
    exact hD n j g x hxr hx
  B_E := fun n j g u hur hu v hv => by
    rw [brstB_bgGhostData]
    exact hE n j g u hur hu v hv


end

end VOA.TwoSeries
