/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.BGPackageBFactor
import VOA.Examples.GhostConjPackage

/-!
# The corrected Beem–Garner chain: global, reduced, factor and remainder data

The chain `GlobalBGPackage → BGReducedData → BGFactorData → BGGhostRemainder` carries the clause
`B_E` with the constant `-(-1)^{gh}`, which the actual complex does not satisfy together with
`ρ² = s` (see `GhostConjPackage`). This file repeats the chain with the corrected constant
`i (-1)^{gh}`; all other clauses, and all the proofs that do not touch `B_E` (restriction to the
relative weight spaces, `Λ` constructed, the product form and conjugation on the `c₀`-free fine
pieces), are reused verbatim.

* `GlobalBGPackageI` and `GlobalBGPackageI.toInterpreted`;
* `BGReducedDataI` (with `Λ = lamBRST`) and `BGReducedDataI.toGlobal`;
* `BGFactorDataI` and `BGFactorDataI.toReduced`;
* `BGGhostRemainderI hA` — the ghost data, `κ`, `ρ_D` and the corrected `B_E` for
  `ρ = ρ_M ⊗ ρ_G`, `B = B_M ⊗ B_G` with the proved matter factor `bgMatterData hA`;
* `leeYang_gradedUnitary_of_affine_bgRemainderI` — **Affine GU ⇒ Lee–Yang GU** from it.

Everything is proved outright from the listed hypotheses.
-/

namespace VOA.ConcreteHodge

open Sl2CosetConcrete Sl2SemiInfinite AffineSl2GeneralRigidity AffineSl2BelowCritical
open VOA.GradedUnitaryCohomology VOA.LeeYangCosetTransfer VOA.VertexOperatorAlgebra
open VOA.LeeYangTransferAssembly LeeYangShortcut VirModule LeeYang VirGradedUnitarity
open VOA.SympFerm VOA.Ghost AffineVOA
open scoped TensorProduct

noncomputable section

/-! ### The global package -/

/-- **The corrected Beem–Garner package on the whole BRST space.** -/
structure GlobalBGPackageI {PG : SesqForm Sl2GhostSpace} (Gh : GhostRGrading PG)
    (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    (BB : InvariantForm BVOA) (RB : RealStructure BVOA) where
  Λ : ℤ → Module.End ℂ BRSTSpace
  Λ_maps : ∀ n : ℤ, ∀ x ∈ relativeWeight n, Λ n x ∈ relativeWeight n
  Λ_shift : ∀ (n j g : ℤ), ∀ x ∈ relativeWeight n, x ∈ brstDeg Gh ((j, g), (n : ℂ)) →
    Λ n x ∈ brstDeg Gh ((j, g - 2), (n : ℂ))
  B : LinearMap.BilinForm ℂ BRSTSpace
  ρ : BRSTSpace →ₗ⋆[ℂ] BRSTSpace
  ρ_maps : ∀ n : ℤ, ∀ x ∈ relativeWeight n, ρ x ∈ relativeWeight n
  P_eq : ∀ (n j g : ℤ), ∀ x ∈ relativeWeight n, x ∈ brstDeg Gh ((j, g), (n : ℂ)) →
    ∀ y ∈ relativeWeight n, matterGhostForm hA BB RB PG x y = Complex.I ^ j * B (ρ x) y
  ρ_deg : ∀ (n j g : ℤ), ∀ x ∈ relativeWeight n, x ∈ brstDeg Gh ((j, g), (n : ℂ)) →
    ρ x ∈ brstDeg Gh ((j, -g), (n : ℂ))
  s : ℂ
  hs : s ≠ 0
  ρ_sq : ∀ n : ℤ, ∀ x ∈ relativeWeight n, ρ (ρ x) = s • x
  κ : ℂ
  hκ : κ ≠ 0
  ρ_D : ∀ (n j g : ℤ), ∀ x ∈ relativeWeight n, x ∈ brstDeg Gh ((j, g), (n : ℂ)) →
    ρ (brstQ x) = (κ * (-1 : ℂ) ^ g) • (Λ n (brstQ (ρ x)) - brstQ (Λ n (ρ x)))
  B_E : ∀ (n j g : ℤ), ∀ u ∈ relativeWeight n, u ∈ brstDeg Gh ((j, g), (n : ℂ)) →
    ∀ v ∈ relativeWeight n,
      B (Λ n (brstQ u) - brstQ (Λ n u)) v =
        Complex.I * (-1 : ℂ) ^ g * B u (Λ n (brstQ v) - brstQ (Λ n v))

namespace GlobalBGPackageI

variable {PG : SesqForm Sl2GhostSpace} {Gh : GhostRGrading PG}
  {hA : GradedUnitary affineForm affineRealStructure affineFlag}
  {BB : InvariantForm BVOA} {RB : RealStructure BVOA} (hB : Unitary BB RB)
  (hG : IsPosOn PG ⊤) (hZ : ZeroModesPreserve Gh) (hD : RelativeDifferentialGood Gh)

/-- `Λ n` restricted to the relative weight space. -/
def Λr (Pk : GlobalBGPackageI Gh hA BB RB) (n : ℤ) : relativeWeight n →ₗ[ℂ] relativeWeight n :=
  (Pk.Λ n).restrict (fun x hx => Pk.Λ_maps n x hx)

/-- `ρ` restricted to the relative weight space. -/
def ρr (Pk : GlobalBGPackageI Gh hA BB RB) (n : ℤ) : relativeWeight n →ₗ⋆[ℂ] relativeWeight n :=
  LinearMap.codRestrict (relativeWeight n) (Pk.ρ.comp (relativeWeight n).subtype)
    (fun x => Pk.ρ_maps n x x.2)

/-- `B` restricted to the relative weight space. -/
def Br (Pk : GlobalBGPackageI Gh hA BB RB) (n : ℤ) :
    LinearMap.BilinForm ℂ (relativeWeight n) :=
  Pk.B.compl₁₂ (relativeWeight n).subtype (relativeWeight n).subtype

/-- **The per-weight corrected package by restriction.** -/
def toInterpreted (Pk : GlobalBGPackageI Gh hA BB RB) :
    InterpretedBGPackageI Gh hA hB hG hZ hD := fun n =>
  { Λ := Pk.Λr n
    shift := fun j g x hx => Pk.Λ_shift n j g x x.2 hx
    B := Pk.Br n
    ρ := Pk.ρr n
    P_eq := fun j g x hx y => by
      change assemblyForm BB RB PG n x y = _
      rw [assemblyForm_eq hA, SesqForm.restrict_apply]
      exact Pk.P_eq n j g x x.2 hx y y.2
    ρ_deg := fun j g x hx => Pk.ρ_deg n j g x x.2 hx
    s := Pk.s
    hs := Pk.hs
    ρ_sq := fun x => Subtype.ext (Pk.ρ_sq n x x.2)
    κ := Pk.κ
    hκ := Pk.hκ
    ρ_D := fun j g x hx => Subtype.ext (by
      change Pk.ρ (brstQ x) = _
      rw [Pk.ρ_D n j g x x.2 hx]
      rfl)
    B_E := fun j g u hu v => Pk.B_E n j g u u.2 hu v v.2 }

end GlobalBGPackageI

/-! ### The reduced data -/

/-- **The corrected remaining data with `Λ = lamBRST` constructed.** -/
structure BGReducedDataI {PG : SesqForm Sl2GhostSpace} (Gh : GhostRGrading PG)
    (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    (BB : InvariantForm BVOA) (RB : RealStructure BVOA) where
  B : LinearMap.BilinForm ℂ BRSTSpace
  ρ : BRSTSpace →ₗ⋆[ℂ] BRSTSpace
  ρ_maps : ∀ n : ℤ, ∀ x ∈ relativeWeight n, ρ x ∈ relativeWeight n
  P_eq : ∀ (n j g : ℤ), ∀ x ∈ relativeWeight n, x ∈ brstDeg Gh ((j, g), (n : ℂ)) →
    ∀ y ∈ relativeWeight n, matterGhostForm hA BB RB PG x y = Complex.I ^ j * B (ρ x) y
  ρ_deg : ∀ (n j g : ℤ), ∀ x ∈ relativeWeight n, x ∈ brstDeg Gh ((j, g), (n : ℂ)) →
    ρ x ∈ brstDeg Gh ((j, -g), (n : ℂ))
  s : ℂ
  hs : s ≠ 0
  ρ_sq : ∀ n : ℤ, ∀ x ∈ relativeWeight n, ρ (ρ x) = s • x
  κ : ℂ
  hκ : κ ≠ 0
  ρ_D : ∀ (n j g : ℤ), ∀ x ∈ relativeWeight n, x ∈ brstDeg Gh ((j, g), (n : ℂ)) →
    ρ (brstQ x) = (κ * (-1 : ℂ) ^ g) • brstE n (ρ x)
  B_E : ∀ (n j g : ℤ), ∀ u ∈ relativeWeight n, u ∈ brstDeg Gh ((j, g), (n : ℂ)) →
    ∀ v ∈ relativeWeight n, B (brstE n u) v = Complex.I * (-1 : ℂ) ^ g * B u (brstE n v)

/-- **The corrected global package from the reduced data**, with `Λ = lamBRST`. -/
def BGReducedDataI.toGlobal {PG : SesqForm Sl2GhostSpace} {Gh : GhostRGrading PG}
    {hA : GradedUnitary affineForm affineRealStructure affineFlag}
    {BB : InvariantForm BVOA} {RB : RealStructure BVOA}
    (R : BGReducedDataI Gh hA BB RB) (hs : Gh.IsStd) : GlobalBGPackageI Gh hA BB RB where
  Λ := lamBRST
  Λ_maps := fun n x hx => lamBRST_mem_relativeWeight n hx
  Λ_shift := fun n j g x _ hx => lamBRST_shift hs n j g _ hx
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

/-! ### The factor data -/

/-- **The corrected factor data**: matter and ghost factors, `ρ_D` and the corrected `B_E` for
the product conjugation and the product form. -/
structure BGFactorDataI {PG : SesqForm Sl2GhostSpace} (Gh : GhostRGrading PG)
    (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    (BB : InvariantForm BVOA) (RB : RealStructure BVOA) where
  M : MatterBGData hA BB RB
  G : GhostBGData PG
  hsM : M.s ≠ 0
  hsG : G.s ≠ 0
  κ : ℂ
  hκ : κ ≠ 0
  ρ_D : ∀ (n j g : ℤ), ∀ x ∈ relativeWeight n, x ∈ brstDeg Gh ((j, g), (n : ℂ)) →
    brstρ M G (brstQ x) = (κ * (-1 : ℂ) ^ g) • brstE n (brstρ M G x)
  B_E : ∀ (n j g : ℤ), ∀ u ∈ relativeWeight n, u ∈ brstDeg Gh ((j, g), (n : ℂ)) →
    ∀ v ∈ relativeWeight n,
      brstB M G (brstE n u) v = Complex.I * (-1 : ℂ) ^ g * brstB M G u (brstE n v)

namespace BGFactorDataI

variable {PG : SesqForm Sl2GhostSpace} {Gh : GhostRGrading PG}
  {hA : GradedUnitary affineForm affineRealStructure affineFlag}
  {BB : InvariantForm BVOA} {RB : RealStructure BVOA}

/-- `ρ_M ⊗ ρ_G` preserves the relative weight spaces (only the factor data are used). -/
theorem ρ_maps (M : MatterBGData hA BB RB) (G : GhostBGData PG) (hB : Unitary BB RB) (n : ℤ)
    (x : BRSTSpace) (hx : x ∈ relativeWeight n) : brstρ M G x ∈ relativeWeight n := by
  have key : ∀ z ∈ ⨆ (k : KF) (_ : k.1.2 = (n : ℂ) ∧ k.2 = 0), brstDegF k,
      brstρ M G z ∈ brstSVA.grading (n : ℂ) ∧
        (∀ a, antighostZero matterSVA a (brstρ M G z) = 0) ∧
        (∀ a, totalCurrentZero leeYangA a (brstρ M G z) =
          -brstρ M G (totalCurrentZero leeYangA
            (AffineVOA.HighestModule.adjointColour a) z)) := by
    intro z hz
    refine iSup_fine_induction (fun z => brstρ M G z ∈ brstSVA.grading (n : ℂ) ∧
        (∀ a, antighostZero matterSVA a (brstρ M G z) = 0) ∧
        (∀ a, totalCurrentZero leeYangA a (brstρ M G z) =
          -brstρ M G (totalCurrentZero leeYangA
            (AffineVOA.HighestModule.adjointColour a) z)))
      ⟨by simp, fun a => by simp, fun a => by simp⟩
      (fun x y hx hy => ⟨by rw [map_add]; exact Submodule.add_mem _ hx.1 hy.1,
        fun a => by rw [map_add, map_add, hx.2.1 a, hy.2.1 a, add_zero],
        fun a => by rw [map_add, map_add, hx.2.2 a, hy.2.2 a, map_add, map_add, neg_add]⟩)
      ?_ hz
    rintro k ⟨hkn, hk⟩ z hz
    have hD := fine_D M G k hk z hz
    refine ⟨?_, fun a => antighostZero_fine (conjF k) (by simp [conjF, hk]) a _ hD,
      fun a => fine_J M G k hk a z hz⟩
    have h1 := (brstDegF_le_brstDeg unitWeight (conjF k)).trans
      (brstDeg_le_weight (ghostRGrading unitWeight) (fstF (conjF k))) hD
    have e : wtIndex (fstF (conjF k)) = (n : ℂ) := by
      simp [conjF, conjIdx, wtIndex, hkn]
    rwa [e] at h1
  obtain ⟨h1, h2, h3⟩ := key x (relative_fine_weight hA hB hx)
  refine ⟨(mem_relativeCarrier _ _).mpr ⟨fun a => ?_, h2⟩, h1⟩
  rw [h3 a, ((mem_relativeCarrier _ x).mp hx.1).1, map_zero, neg_zero]

/-- **The corrected reduced data from the factor data** (standard ghost grading). -/
def toReduced (F : BGFactorDataI Gh hA BB RB) (hB : Unitary BB RB) (hs : Gh.IsStd) :
    BGReducedDataI Gh hA BB RB where
  B := brstB F.M F.G
  ρ := brstρ F.M F.G
  ρ_maps := fun n x hx => ρ_maps F.M F.G hB n x hx
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

end BGFactorDataI

/-! ### The corrected remainder and the endpoint -/

/-- **What remains of the corrected Beem–Garner package** once `Λ`, the matter factor
(`bgMatterData`), the ghost form (`bgPG`) and the grading are fixed. -/
structure BGGhostRemainderI (hA : GradedUnitary affineForm affineRealStructure affineFlag) where
  G : GhostBGData bgPG
  hsG : G.s ≠ 0
  κ : ℂ
  hκ : κ ≠ 0
  ρ_D : ∀ (n j g : ℤ), ∀ x ∈ relativeWeight n, x ∈ brstDeg bgGh ((j, g), (n : ℂ)) →
    brstρ (bgMatterData hA) G (brstQ x) =
      (κ * (-1 : ℂ) ^ g) • brstE n (brstρ (bgMatterData hA) G x)
  B_E : ∀ (n j g : ℤ), ∀ u ∈ relativeWeight n, u ∈ brstDeg bgGh ((j, g), (n : ℂ)) →
    ∀ v ∈ relativeWeight n,
      brstB (bgMatterData hA) G (brstE n u) v =
        Complex.I * (-1 : ℂ) ^ g * brstB (bgMatterData hA) G u (brstE n v)

/-- The corrected factor data from the corrected remainder. -/
def BGGhostRemainderI.toFactor {hA : GradedUnitary affineForm affineRealStructure affineFlag}
    (Rm : BGGhostRemainderI hA) : BGFactorDataI bgGh hA bForm bRealStructure where
  M := bgMatterData hA
  G := Rm.G
  hsM := one_ne_zero
  hsG := Rm.hsG
  κ := Rm.κ
  hκ := Rm.hκ
  ρ_D := Rm.ρ_D
  B_E := Rm.B_E

/-- The corrected per-weight package from the corrected remainder. -/
abbrev BGGhostRemainderI.pkg {hA : GradedUnitary affineForm affineRealStructure affineFlag}
    (hB : Unitary bForm bRealStructure) (Rm : BGGhostRemainderI hA) :
    InterpretedBGPackageI bgGh hA hB bgPG_pos (stdZ bgGh_isStd) (stdD hA hB bgGh_isStd) :=
  ((Rm.toFactor.toReduced hB bgGh_isStd).toGlobal bgGh_isStd).toInterpreted hB bgPG_pos
    (stdZ bgGh_isStd) (stdD hA hB bgGh_isStd)

/-- **Affine GU ⇒ Lee–Yang GU from the corrected remainder.** `#print axioms`-clean,
conditional on: `hA` (the hypothesis), `hB` (unitarity of `L_1(sl₂)` for the canonical pair),
`Rm` (ghost conjugation data, `ρ_D`, corrected `B_E`) and the downstream `symbols`, `character`,
`vacuumNormalized`, `creationAdjoint`, `wordsReal`. -/
theorem leeYang_gradedUnitary_of_affine_bgRemainderI
    (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    (hB : Unitary bForm bRealStructure) (Rm : BGGhostRemainderI hA)
    (symbols : LeadingInvariantSymbolDimension
      (sp2Kahler hA hB bgPG_pos bgGh bgGh_isStd (Rm.pkg hB).sp2))
    (character : LeeYangPBWCharacter)
    (vacuumNormalized : HarmonicVacuumNormalized
      (sp2Kahler hA hB bgPG_pos bgGh bgGh_isStd (Rm.pkg hB).sp2)
      (sp2GUData0 hA hB bgPG_pos bgGh bgGh_isStd (Rm.pkg hB).sp2 (Rm.pkg hB).conj0))
    (creationAdjoint : HarmonicCreationAdjoint
      (sp2Kahler hA hB bgPG_pos bgGh bgGh_isStd (Rm.pkg hB).sp2)
      (sp2GUData0 hA hB bgPG_pos bgGh bgGh_isStd (Rm.pkg hB).sp2 (Rm.pkg hB).conj0))
    (wordsReal : HarmonicWordsReal
      (sp2Kahler hA hB bgPG_pos bgGh bgGh_isStd (Rm.pkg hB).sp2)
      (sp2GUData0 hA hB bgPG_pos bgGh bgGh_isStd (Rm.pkg hB).sp2 (Rm.pkg hB).conj0)) :
    VirGradedUnitary leeYangC leeYangRealStructure :=
  leeYang_gradedUnitary_of_affine_bgPackageI hA hB bgPG_pos bgGh bgGh_isStd (Rm.pkg hB) symbols
    character vacuumNormalized creationAdjoint wordsReal

end

end VOA.ConcreteHodge
