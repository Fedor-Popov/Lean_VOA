/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.BRSTKahlerGhost

/-!
# The conjugation input is only needed at ghost number zero

`GoodComplex.ConjData` asks for `ρ 𝐐⁻ = κ 𝐐⁺ ρ` and `ρ 𝐐⁺ = κ' 𝐐⁻ ρ` on the **whole** complex,
with constant `κ`, `κ'`. Beem–Garner's conjugation satisfies `ρ(x_n y) = (-1)^{|x||y|} ρ(x)_n ρ(y)`
(their Definition 2.12), so on states of ghost parity `|y|` it intertwines the two differentials
only up to the sign `(-1)^{|y|}`: a constant `κ` is a convention mismatch away from ghost number
zero. The consumer `GUData` only needs `ρ` to map the harmonic space of ghost number `0` onto
itself, so:

* `GoodComplex.ConjData0` — the conjugation input with `ρ_D` required **only on ghost number
  zero** and `ρ_Dp` dropped altogether; `ConjData.toConjData0` (it is weaker than `ConjData`);
* `GoodComplex.guData0` — the `GUData` of Beem–Garner Theorem 4.1 from `ConjData0`
  (`ρ_maps0`, `ρ_onto0` proved);
* `Sp2Conj0` — the same, with `ρ 𝐐⁻ = κ [Λ, 𝐐⁻] ρ` on ghost number zero for the explicit
  `sp(2)` image; `Sp2Conj0.toConjData0`;
* `leeYang_gradedUnitary_of_affine_sp2_conj0` — **Affine GU ⇒ Lee–Yang GU** for an arbitrary
  positive ghost form with the standard grading, from the `sp(2)` adjoint relation and the
  ghost-number-zero conjugation input.

Everything is proved outright from the listed hypotheses.
-/

namespace VOA.ConcreteHodge

open Sl2CosetConcrete Sl2SemiInfinite AffineSl2GeneralRigidity AffineSl2BelowCritical
open VOA.GradedUnitaryCohomology VOA.LeeYangCosetTransfer VOA.VertexOperatorAlgebra
open VOA.LeeYangTransferAssembly LeeYangShortcut VirModule LeeYang VirGradedUnitarity
open scoped TensorProduct

noncomputable section

universe u

namespace GoodComplex

variable {K : Type u} [AddCommGroup K] [Module ℂ K]

/-- **The conjugation input at ghost number zero.** `ρ 𝐐⁻ = κ 𝐐⁺ ρ` is required only on vectors
of ghost number `0`; there is no `ρ_Dp`. -/
structure ConjData0 (G : GoodComplex K) where
  B : LinearMap.BilinForm ℂ K
  ρ : K →ₗ⋆[ℂ] K
  h : SesqForm K
  h_eq : ∀ x y, h x y = B (ρ x) y
  P_eq : ∀ j g : ℤ, ∀ x ∈ G.deg (j, g), ∀ y, G.P x y = Complex.I ^ j * h x y
  ρ_deg : ∀ j g : ℤ, ∀ x ∈ G.deg (j, g), ρ x ∈ G.deg (j, -g)
  κ : ℂ
  hκ : κ ≠ 0
  ρ_D0 : ∀ j : ℤ, ∀ x ∈ G.deg (j, 0), ρ (G.D x) = κ • G.Dp (ρ x)
  s : ℂ
  hs : s ≠ 0
  ρ_sq : ∀ x, ρ (ρ x) = s • x

variable {G : GoodComplex K}

/-- `ConjData` is stronger. -/
def ConjData.toConjData0 (R : ConjData G) : ConjData0 G where
  B := R.B
  ρ := R.ρ
  h := R.h
  h_eq := R.h_eq
  P_eq := R.P_eq
  ρ_deg := R.ρ_deg
  κ := R.κ
  hκ := R.hκ
  ρ_D0 := fun _ x _ => R.ρ_D x
  s := R.s
  hs := R.hs
  ρ_sq := R.ρ_sq

variable (G)

theorem ρ_maps0 (R : ConjData0 G) (j : ℤ) (x : K) (hx : x ∈ G.toKahler.harmDeg (j, 0)) :
    R.ρ x ∈ G.toKahler.harmDeg (j, 0) := by
  obtain ⟨hxh, hxd⟩ := hx
  change x ∈ G.deg (j, 0) at hxd
  obtain ⟨hD, hDp⟩ := G.D_Dp_of_harm hxh
  have hρd : R.ρ x ∈ G.deg (j, 0) := by
    have := R.ρ_deg j 0 x hxd; rwa [neg_zero] at this
  have h2 : G.Dp (R.ρ x) = 0 := by
    have := R.ρ_D0 j x hxd
    rw [hD, map_zero] at this
    exact (smul_eq_zero.mp this.symm).resolve_left R.hκ
  have h1 : G.D (R.ρ x) = 0 := by
    have h3 : R.ρ (G.D (R.ρ x)) = 0 := by
      rw [R.ρ_D0 j _ hρd, R.ρ_sq, map_smul, hDp, smul_zero, smul_zero]
    have h4 : R.s • G.D (R.ρ x) = 0 := by rw [← R.ρ_sq, h3, map_zero]
    exact (smul_eq_zero.mp h4).resolve_left R.hs
  exact ⟨G.mem_harm_of_D_Dp hρd h1 h2, hρd⟩

theorem ρ_onto0 (R : ConjData0 G) (j : ℤ) (y : K) (hy : y ∈ G.toKahler.harmDeg (j, 0)) :
    ∃ x ∈ G.toKahler.harmDeg (j, 0), R.ρ x = y := by
  refine ⟨(starRingEnd ℂ) R.s⁻¹ • R.ρ y,
    Submodule.smul_mem _ _ (G.ρ_maps0 R j y hy), ?_⟩
  rw [LinearMap.map_smulₛₗ, R.ρ_sq, smul_smul]
  simp only [starRingEnd_apply, star_star]
  rw [inv_mul_cancel₀ R.hs, one_smul]

/-- **The `GUData` of Beem–Garner Theorem 4.1 from the ghost-number-zero conjugation input.** -/
def guData0 (R : ConjData0 G) : GUData G.toKahler where
  B := R.B
  ρ := R.ρ
  h := R.h
  h_eq := R.h_eq
  P_eq := R.P_eq
  ρ_maps := G.ρ_maps0 R
  ρ_onto := G.ρ_onto0 R

/-- On `ConjData`, the two constructions agree. -/
theorem guData0_toConjData0 (R : ConjData G) :
    (G.guData0 R.toConjData0).B = (G.guData R).B ∧ (G.guData0 R.toConjData0).ρ = (G.guData R).ρ :=
  ⟨rfl, rfl⟩

end GoodComplex

/-- **The ghost-number-zero conjugation input for the `sp(2)` image**: `ρ 𝐐⁻ = κ E ρ` on ghost
number `0`, for an explicit operator `E` (in use `E = [Λ, 𝐐⁻]`). -/
structure Sp2Conj0 {K : Type u} [AddCommGroup K] [Module ℂ K] (G : GoodComplex K)
    (E : K →ₗ[ℂ] K) where
  B : LinearMap.BilinForm ℂ K
  ρ : K →ₗ⋆[ℂ] K
  h : SesqForm K
  h_eq : ∀ x y, h x y = B (ρ x) y
  P_eq : ∀ j g : ℤ, ∀ x ∈ G.deg (j, g), ∀ y, G.P x y = Complex.I ^ j * h x y
  ρ_deg : ∀ j g : ℤ, ∀ x ∈ G.deg (j, g), ρ x ∈ G.deg (j, -g)
  κ : ℂ
  hκ : κ ≠ 0
  ρ_D0 : ∀ j : ℤ, ∀ x ∈ G.deg (j, 0), ρ (G.D x) = κ • E (ρ x)
  s : ℂ
  hs : s ≠ 0
  ρ_sq : ∀ x, ρ (ρ x) = s • x

/-- The ghost-number-zero conjugation input of a good complex whose second differential is `E`. -/
def Sp2Conj0.toConjData0 {K : Type u} [AddCommGroup K] [Module ℂ K] {G : GoodComplex K}
    {E : K →ₗ[ℂ] K} (R : Sp2Conj0 G E) (hE : G.Dp = E) : GoodComplex.ConjData0 G where
  B := R.B
  ρ := R.ρ
  h := R.h
  h_eq := R.h_eq
  P_eq := R.P_eq
  ρ_deg := R.ρ_deg
  κ := R.κ
  hκ := R.hκ
  ρ_D0 := fun j x hx => by rw [hE]; exact R.ρ_D0 j x hx
  s := R.s
  hs := R.hs
  ρ_sq := R.ρ_sq

/-- The `ConcreteGUData` of the `sp(2)` geometry from the ghost-number-zero inputs. -/
def sp2GUData0 (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    {BB : InvariantForm BVOA} {RB : RealStructure BVOA} (hB : Unitary BB RB)
    {PG : SesqForm Sl2GhostSpace} (hG : IsPosOn PG ⊤) (Gh : GhostRGrading PG) (hs : Gh.IsStd)
    (S : InterpretedSp2 Gh hA hB hG (stdZ hs) (stdD hA hB hs))
    (R : ∀ n hp, Sp2Conj0 (concreteGood (interpretedGoodGeometry Gh hA hB hG (stdZ hs)
      (stdD hA hB hs) (interpretedKahlerAnticomm_of_sp2 Gh hA hB hG _ _ S)) n hp) (S n).E) :
    ConcreteGUData (sp2Kahler hA hB hG Gh hs S) where
  data n hp := (concreteGood _ n hp).guData0
    ((R n hp).toConjData0 (concreteGood_Dp_eq Gh hA hB hG _ _ S n hp))

/-- **Affine GU ⇒ Lee–Yang GU from the `sp(2)` adjoint relation and the ghost-number-zero
conjugation input**, for an arbitrary positive ghost form with the standard grading.
`#print axioms`-clean, conditional on: `hA` (the hypothesis), `hB`, `hG`, `hs`, `S` (Beem–Garner
Lemma 3.16 for the `sp(2)` image), `R` (`ρ` at ghost number zero), and the downstream `symbols`,
`character`, `vacuumNormalized`, `creationAdjoint`, `wordsReal`. -/
theorem leeYang_gradedUnitary_of_affine_sp2_conj0
    (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    {BB : InvariantForm BVOA} {RB : RealStructure BVOA} (hB : Unitary BB RB)
    {PG : SesqForm Sl2GhostSpace} (hG : IsPosOn PG ⊤) (Gh : GhostRGrading PG) (hs : Gh.IsStd)
    (S : InterpretedSp2 Gh hA hB hG (stdZ hs) (stdD hA hB hs))
    (R : ∀ n hp, Sp2Conj0 (concreteGood (interpretedGoodGeometry Gh hA hB hG (stdZ hs)
      (stdD hA hB hs) (interpretedKahlerAnticomm_of_sp2 Gh hA hB hG _ _ S)) n hp) (S n).E)
    (symbols : LeadingInvariantSymbolDimension (sp2Kahler hA hB hG Gh hs S))
    (character : LeeYangPBWCharacter)
    (vacuumNormalized : HarmonicVacuumNormalized (sp2Kahler hA hB hG Gh hs S)
      (sp2GUData0 hA hB hG Gh hs S R))
    (creationAdjoint : HarmonicCreationAdjoint (sp2Kahler hA hB hG Gh hs S)
      (sp2GUData0 hA hB hG Gh hs S R))
    (wordsReal : HarmonicWordsReal (sp2Kahler hA hB hG Gh hs S)
      (sp2GUData0 hA hB hG Gh hs S R)) :
    VirGradedUnitary leeYangC leeYangRealStructure :=
  leeYang_gradedUnitary_of_affine' hA
    { kahler := sp2Kahler hA hB hG Gh hs S
      weakGU := concreteKahler_weakGU hB hG _
      gu := sp2GUData0 hA hB hG Gh hs S R
      symbols := symbols
      character := character
      generators := fun hp => interpretedGenerators_std Gh hA hB hG _ _ _ hs hp
      vacuumNormalized := vacuumNormalized
      creationAdjoint := creationAdjoint
      wordsReal := wordsReal }

end

end VOA.ConcreteHodge
