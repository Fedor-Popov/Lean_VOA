/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.BRSTKahlerPackage

/-!
# The Beem–Garner package stated once on the whole BRST space

`InterpretedBGPackage` asks, at every weight `n`, for data on the finite-dimensional relative
weight space `relativeWeight n`. Beem–Garner's data are operators on the whole BRST space: the
`Sp(2)` raising operator `Λ` (a finite sum of antighost bilinears at each weight), one bilinear
form `B` and one conjugation `ρ`. This file states the package in that global form and proves
that it restricts to the per-weight package.

* `GlobalBGPackage Gh hA hB hG hs` — global operators on `BRSTSpace`:
  `Λ n` (a family indexed by the weight, because the natural `Λ` on weight `n` is a finite sum of
  modes up to `n`), `B`, `ρ`, all preserving the relative weight spaces where needed, with the
  clauses of `GoodHalf.Sp2Package` stated for vectors of the relative weight spaces, the actual
  BRST differential `leeYangBRSTComplex.Q`, the actual product form `matterGhostForm` and the
  actual interpreted grading `brstDeg Gh`.
* `GlobalBGPackage.toInterpreted` — **the per-weight package by restriction**.
* `leeYang_gradedUnitary_of_affine_globalBGPackage` — **Affine GU ⇒ Lee–Yang GU** from one
  global package.

Everything is proved outright from the listed hypotheses.
-/

namespace VOA.ConcreteHodge

open Sl2CosetConcrete Sl2SemiInfinite AffineSl2GeneralRigidity AffineSl2BelowCritical
open VOA.GradedUnitaryCohomology VOA.LeeYangCosetTransfer VOA.VertexOperatorAlgebra
open VOA.LeeYangTransferAssembly LeeYangShortcut VirModule LeeYang VirGradedUnitarity
open scoped TensorProduct

noncomputable section

/-- The BRST differential on the whole space. -/
abbrev brstQ : Module.End ℂ BRSTSpace := leeYangBRSTComplex.Q

/-- **The Beem–Garner package on the whole BRST space** (see the module docstring). All clauses
are required only on the relative weight spaces. -/
structure GlobalBGPackage {PG : SesqForm Sl2GhostSpace} (Gh : GhostRGrading PG)
    (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    (BB : InvariantForm BVOA) (RB : RealStructure BVOA) where
  /-- The `Sp(2)` raising operator at weight `n`. -/
  Λ : ℤ → Module.End ℂ BRSTSpace
  Λ_maps : ∀ n : ℤ, ∀ x ∈ relativeWeight n, Λ n x ∈ relativeWeight n
  Λ_shift : ∀ (n j g : ℤ), ∀ x ∈ relativeWeight n, x ∈ brstDeg Gh ((j, g), (n : ℂ)) →
    Λ n x ∈ brstDeg Gh ((j, g - 2), (n : ℂ))
  /-- The invariant bilinear form. -/
  B : LinearMap.BilinForm ℂ BRSTSpace
  /-- The conjugation. -/
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
      B (Λ n (brstQ u) - brstQ (Λ n u)) v = -((-1 : ℂ) ^ g) * B u (Λ n (brstQ v) - brstQ (Λ n v))

namespace GlobalBGPackage

variable {PG : SesqForm Sl2GhostSpace} {Gh : GhostRGrading PG}
  {hA : GradedUnitary affineForm affineRealStructure affineFlag}
  {BB : InvariantForm BVOA} {RB : RealStructure BVOA} (hB : Unitary BB RB)
  (hG : IsPosOn PG ⊤) (hZ : ZeroModesPreserve Gh) (hD : RelativeDifferentialGood Gh)

/-- `Λ n` restricted to the relative weight space. -/
def Λr (Pk : GlobalBGPackage Gh hA BB RB) (n : ℤ) : relativeWeight n →ₗ[ℂ] relativeWeight n :=
  (Pk.Λ n).restrict (fun x hx => Pk.Λ_maps n x hx)

@[simp] theorem Λr_coe (Pk : GlobalBGPackage Gh hA BB RB) (n : ℤ) (x : relativeWeight n) :
    (Pk.Λr n x : BRSTSpace) = Pk.Λ n x := rfl

/-- `ρ` restricted to the relative weight space. -/
def ρr (Pk : GlobalBGPackage Gh hA BB RB) (n : ℤ) : relativeWeight n →ₗ⋆[ℂ] relativeWeight n :=
  LinearMap.codRestrict (relativeWeight n) (Pk.ρ.comp (relativeWeight n).subtype)
    (fun x => Pk.ρ_maps n x x.2)

@[simp] theorem ρr_coe (Pk : GlobalBGPackage Gh hA BB RB) (n : ℤ) (x : relativeWeight n) :
    (Pk.ρr n x : BRSTSpace) = Pk.ρ x := rfl

/-- `B` restricted to the relative weight space. -/
def Br (Pk : GlobalBGPackage Gh hA BB RB) (n : ℤ) : LinearMap.BilinForm ℂ (relativeWeight n) :=
  Pk.B.compl₁₂ (relativeWeight n).subtype (relativeWeight n).subtype

@[simp] theorem Br_apply (Pk : GlobalBGPackage Gh hA BB RB) (n : ℤ) (x y : relativeWeight n) :
    Pk.Br n x y = Pk.B x y := rfl

/-- **The per-weight package by restriction.** -/
def toInterpreted (Pk : GlobalBGPackage Gh hA BB RB) :
    InterpretedBGPackage Gh hA hB hG hZ hD := fun n =>
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

end GlobalBGPackage

/-- **Affine GU ⇒ Lee–Yang GU from one global Beem–Garner package**, for an arbitrary
positive ghost form with the standard grading. `#print axioms`-clean, conditional on: `hA` (the
hypothesis), `hB`, `hG`, `hs`, `Pk` (the global package) and the downstream `symbols`,
`character`, `vacuumNormalized`, `creationAdjoint`, `wordsReal`. -/
theorem leeYang_gradedUnitary_of_affine_globalBGPackage
    (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    {BB : InvariantForm BVOA} {RB : RealStructure BVOA} (hB : Unitary BB RB)
    {PG : SesqForm Sl2GhostSpace} (hG : IsPosOn PG ⊤) (Gh : GhostRGrading PG) (hs : Gh.IsStd)
    (Pk : GlobalBGPackage Gh hA BB RB)
    (symbols : LeadingInvariantSymbolDimension
      (sp2Kahler hA hB hG Gh hs (Pk.toInterpreted hB hG (stdZ hs) (stdD hA hB hs)).sp2))
    (character : LeeYangPBWCharacter)
    (vacuumNormalized : HarmonicVacuumNormalized
      (sp2Kahler hA hB hG Gh hs (Pk.toInterpreted hB hG (stdZ hs) (stdD hA hB hs)).sp2)
      (sp2GUData0 hA hB hG Gh hs (Pk.toInterpreted hB hG (stdZ hs) (stdD hA hB hs)).sp2
        (Pk.toInterpreted hB hG (stdZ hs) (stdD hA hB hs)).conj0))
    (creationAdjoint : HarmonicCreationAdjoint
      (sp2Kahler hA hB hG Gh hs (Pk.toInterpreted hB hG (stdZ hs) (stdD hA hB hs)).sp2)
      (sp2GUData0 hA hB hG Gh hs (Pk.toInterpreted hB hG (stdZ hs) (stdD hA hB hs)).sp2
        (Pk.toInterpreted hB hG (stdZ hs) (stdD hA hB hs)).conj0))
    (wordsReal : HarmonicWordsReal
      (sp2Kahler hA hB hG Gh hs (Pk.toInterpreted hB hG (stdZ hs) (stdD hA hB hs)).sp2)
      (sp2GUData0 hA hB hG Gh hs (Pk.toInterpreted hB hG (stdZ hs) (stdD hA hB hs)).sp2
        (Pk.toInterpreted hB hG (stdZ hs) (stdD hA hB hs)).conj0)) :
    VirGradedUnitary leeYangC leeYangRealStructure :=
  leeYang_gradedUnitary_of_affine_bgPackage hA hB hG Gh hs
    (Pk.toInterpreted hB hG (stdZ hs) (stdD hA hB hs)) symbols character vacuumNormalized
    creationAdjoint wordsReal

end

end VOA.ConcreteHodge
