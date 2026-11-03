/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.BRSTKahlerCommutator
import VOA.Examples.BRSTGoodnessCreation

/-!
# The Kähler relation of the actual relative complex from the `sp(2)` adjoint relation

The abstract `Sp(2)` argument of `BRSTKahlerCommutator`, instantiated on the interpreted minimal
input `interpretedHalf` (the actual relative weight spaces `relativeWeight n`, the actual
differential `relativeDifferential n`, the form `assemblyForm`, the interpreted `(2R, gh)`
grading).

* `InterpretedSp2 Gh …` — **OPEN input** (data): at every weight `n`, an operator `Λ` on
  `relativeWeight n` shifting `(2R, gh)` by `(0, -2)` such that `[Λ, 𝐐⁻]` satisfies Beem–Garner's
  adjoint relation `(Q⁻)† = S⁺`, `(S⁻)† = -Q⁺` (`GoodHalf.Sp2Adjoint`). Beem–Garner's `Λ` is the
  raising operator `η⁻ ↦ η⁺` of the `Sp(2)` acting on `η⁺ = b`, `η⁻ = ∂c`, i.e. a multiple of
  `Σ_a Σ_{n ≥ 1} (1/n) K_{ab} b^a_{-n} b^b_n` restricted to relative states; their Lemma 3.16
  (`(Q^α)† = ε_{αβ} S^β`) is exactly the adjoint clause.
* `interpretedKahlerAnticomm_of_sp2` — **`InterpretedKahlerAnticomm` follows** (the
  anticommutation itself is not an input).
* `interpretedDerived_eq` — the derived second differential *is* `[Λ, 𝐐⁻]`.
* `ReducedConj` — the conjugation input with `ρ_Dp` removed and `ρ_D` stated for the explicit
  operator `[Λ, 𝐐⁻]`; `ReducedConj.toConjData` builds the `ConjData` of the endpoint.
* `leeYang_gradedUnitary_of_affine_sp2_uniform` — the endpoint
  `leeYang_gradedUnitary_of_affine_kahler` with `hK` replaced by `InterpretedSp2` and `R` by
  `ReducedConj`, for the colour-uniform ghost forms `ghostForm w` of that endpoint.

**Caveat on the colour-uniform ghost form (not machine-checked).** The adjoint relation forces
`(c^a_{-n})† ∝ b^a_n` with the colour weights of the ghost form; matching `Σ_a J^{ā}_{-n} b^a_n`
against the `sl₂`-invariant contraction `Σ K^{ab} J_a b_b` (Chevalley basis, `ρ J^a = -J^{ā}`)
requires the `h`-colour `c`-modes to have half the norm of the `e`, `f` colours. `ghostForm w`
gives all colours the same norm, so `InterpretedSp2 (ghostRGrading w) …` is expected to fail; the
corrected endpoint for colour-weighted ghost forms is in `BRSTKahlerGhost`.

Everything is proved outright from the listed hypotheses.
-/

namespace VOA.ConcreteHodge

open Sl2CosetConcrete Sl2SemiInfinite AffineSl2GeneralRigidity AffineSl2BelowCritical
open VOA.GradedUnitaryCohomology VOA.LeeYangCosetTransfer VOA.VertexOperatorAlgebra
open VOA.LeeYangTransferAssembly
open scoped TensorProduct

noncomputable section

section Interpreted

variable {PG : SesqForm Sl2GhostSpace} (Gh : GhostRGrading PG)
  (hA : GradedUnitary affineForm affineRealStructure affineFlag)
  {BB : InvariantForm BVOA} {RB : RealStructure BVOA} (hB : Unitary BB RB)
  (hG : IsPosOn PG ⊤) (hZ : ZeroModesPreserve Gh) (hD : RelativeDifferentialGood Gh)

/-- **OPEN input: Beem–Garner Lemma 3.16 for the `sp(2)` image, on the actual relative complex.**
At every weight `n`: `Λ` on `relativeWeight n` with `Λ (relDeg (j, g)) ⊆ relDeg (j, g - 2)` and,
whenever `[Λ, 𝐐⁻] y = u + v` (`y` of bidegree `(j, g)`, `u`, `v` of bidegrees `(j ± 1, g - 1)`),
`assemblyForm (𝐐⁻ x) y = assemblyForm x (v - u)`. -/
abbrev InterpretedSp2 : Type :=
  ∀ n : ℤ, (interpretedHalf Gh hA hB hG hZ hD n).Sp2Adjoint

/-- **The Kähler relation of the actual relative complex from the `sp(2)` adjoint relation.** -/
theorem interpretedKahlerAnticomm_of_sp2 (S : InterpretedSp2 Gh hA hB hG hZ hD) :
    InterpretedKahlerAnticomm Gh hA hB hG hZ hD :=
  fun n => (S n).kahlerAnticomm (interpretedHalf_pos Gh hA hB hG hZ hD n)

/-- The Prop-valued form of the input also suffices. -/
theorem interpretedKahlerAnticomm_of_nonempty_sp2
    (S : ∀ n, Nonempty (interpretedHalf Gh hA hB hG hZ hD n).Sp2Adjoint) :
    InterpretedKahlerAnticomm Gh hA hB hG hZ hD :=
  fun n => (S n).some.kahlerAnticomm (interpretedHalf_pos Gh hA hB hG hZ hD n)

/-- The derived second differential of the actual complex is the `sp(2)` image `[Λ, 𝐐⁻]`. -/
theorem interpretedDerived_eq (S : InterpretedSp2 Gh hA hB hG hZ hD) (n : ℤ) :
    (interpretedHalf Gh hA hB hG hZ hD n).derivedDp (interpretedHalf_pos Gh hA hB hG hZ hD n) =
      (S n).E :=
  (S n).derivedDp_eq (interpretedHalf_pos Gh hA hB hG hZ hD n)

end Interpreted

/-! ### The reduced conjugation input -/

universe u

/-- **The conjugation input with `ρ_Dp` removed**, and `ρ_D` stated for an explicit operator `E`
(in use: `E = [Λ, 𝐐⁻]`, so that `ρ 𝐐⁻ = κ [Λ, 𝐐⁻] ρ` — Beem–Garner's statement that the real
structure exchanges the two members of the `Sp(2)` doublet). -/
structure ReducedConj {K : Type u} [AddCommGroup K] [Module ℂ K] (G : GoodComplex K)
    (E : K →ₗ[ℂ] K) where
  B : LinearMap.BilinForm ℂ K
  ρ : K →ₗ⋆[ℂ] K
  h : SesqForm K
  h_eq : ∀ x y, h x y = B (ρ x) y
  P_eq : ∀ j g : ℤ, ∀ x ∈ G.deg (j, g), ∀ y, G.P x y = Complex.I ^ j * h x y
  ρ_deg : ∀ j g : ℤ, ∀ x ∈ G.deg (j, g), ρ x ∈ G.deg (j, -g)
  κ : ℂ
  hκ : κ ≠ 0
  ρ_D : ∀ x, ρ (G.D x) = κ • E (ρ x)
  s : ℂ
  hs : s ≠ 0
  ρ_sq : ∀ x, ρ (ρ x) = s • x

/-- The `ConjData` of a good complex whose second differential is `E`. -/
def ReducedConj.toConjData {K : Type u} [AddCommGroup K] [Module ℂ K] {G : GoodComplex K}
    {E : K →ₗ[ℂ] K} (R : ReducedConj G E) (hE : G.Dp = E) : GoodComplex.ConjData G :=
  GoodComplex.ConjData.ofRhoD R.B R.ρ R.h R.h_eq R.P_eq R.ρ_deg R.κ R.hκ
    (fun x => by rw [hE]; exact R.ρ_D x) R.s R.hs R.ρ_sq

@[simp] theorem ReducedConj.toConjData_B {K : Type u} [AddCommGroup K] [Module ℂ K]
    {G : GoodComplex K} {E : K →ₗ[ℂ] K} (R : ReducedConj G E) (hE : G.Dp = E) :
    (R.toConjData hE).B = R.B := rfl

@[simp] theorem ReducedConj.toConjData_ρ {K : Type u} [AddCommGroup K] [Module ℂ K]
    {G : GoodComplex K} {E : K →ₗ[ℂ] K} (R : ReducedConj G E) (hE : G.Dp = E) :
    (R.toConjData hE).ρ = R.ρ := rfl

section Endpoint

variable {PG : SesqForm Sl2GhostSpace} (Gh : GhostRGrading PG)
  (hA : GradedUnitary affineForm affineRealStructure affineFlag)
  {BB : InvariantForm BVOA} {RB : RealStructure BVOA} (hB : Unitary BB RB)
  (hG : IsPosOn PG ⊤) (hZ : ZeroModesPreserve Gh) (hD : RelativeDifferentialGood Gh)

/-- The second differential of the interpreted good complex is the `sp(2)` image. -/
theorem concreteGood_Dp_eq (S : InterpretedSp2 Gh hA hB hG hZ hD) (n : ℤ) hp :
    (concreteGood (interpretedGoodGeometry Gh hA hB hG hZ hD
      (interpretedKahlerAnticomm_of_sp2 Gh hA hB hG hZ hD S)) n hp).Dp = (S n).E :=
  interpretedDerived_eq Gh hA hB hG hZ hD S n

/-- The `ConjData` family of the endpoint from the reduced conjugation inputs. -/
def sp2ConjData (S : InterpretedSp2 Gh hA hB hG hZ hD)
    (R : ∀ n hp, ReducedConj (concreteGood (interpretedGoodGeometry Gh hA hB hG hZ hD
      (interpretedKahlerAnticomm_of_sp2 Gh hA hB hG hZ hD S)) n hp) (S n).E) :
    ∀ n hp, GoodComplex.ConjData (concreteGood (interpretedGoodGeometry Gh hA hB hG hZ hD
      (interpretedKahlerAnticomm_of_sp2 Gh hA hB hG hZ hD S)) n hp) :=
  fun n hp => (R n hp).toConjData (concreteGood_Dp_eq Gh hA hB hG hZ hD S n hp)

end Endpoint

open LeeYangShortcut VirGradedUnitarity LeeYang in
/-- **Affine GU ⇒ Lee–Yang GU, with the Kähler relation replaced by the `sp(2)` adjoint
relation and `ρ_Dp` removed** (colour-uniform ghost forms `ghostForm w`; see the caveat in the
module docstring and `BRSTKahlerGhost` for colour-weighted forms). `#print axioms`-clean,
conditional on: `hA` (the hypothesis), `hB`, `w > 0`, `S` (the `sp(2)` adjoint relation),
`R` (reduced conjugation data), `symbols`, `character`, `vacuumNormalized`, `creationAdjoint`,
`wordsReal`. -/
theorem leeYang_gradedUnitary_of_affine_sp2_uniform
    (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    {BB : InvariantForm BVOA} {RB : RealStructure BVOA} (hB : Unitary BB RB)
    (w : Finset ModeIdx → ℝ) (hw : ∀ s, 0 < w s)
    (S : InterpretedSp2 (ghostRGrading w) hA hB (ghostPos w hw) (hZproved w)
      (relativeDifferentialGood_of_affine hA hB w hw))
    (R : ∀ n hp, ReducedConj (concreteGood (interpretedGoodGeometry (ghostRGrading w) hA hB
      (ghostPos w hw) (hZproved w) (relativeDifferentialGood_of_affine hA hB w hw)
      (interpretedKahlerAnticomm_of_sp2 _ hA hB _ _ _ S)) n hp) (S n).E)
    (symbols : LeadingInvariantSymbolDimension (interpretedKahler (ghostRGrading w) hA hB
      (ghostPos w hw) (hZproved w) (relativeDifferentialGood_of_affine hA hB w hw)
      (interpretedKahlerAnticomm_of_sp2 _ hA hB _ _ _ S)))
    (character : LeeYangPBWCharacter)
    (vacuumNormalized : HarmonicVacuumNormalized (interpretedKahler (ghostRGrading w) hA hB
      (ghostPos w hw) (hZproved w) (relativeDifferentialGood_of_affine hA hB w hw)
      (interpretedKahlerAnticomm_of_sp2 _ hA hB _ _ _ S))
      (concreteGUData _ (sp2ConjData _ hA hB _ _ _ S R)))
    (creationAdjoint : HarmonicCreationAdjoint (interpretedKahler (ghostRGrading w) hA hB
      (ghostPos w hw) (hZproved w) (relativeDifferentialGood_of_affine hA hB w hw)
      (interpretedKahlerAnticomm_of_sp2 _ hA hB _ _ _ S))
      (concreteGUData _ (sp2ConjData _ hA hB _ _ _ S R)))
    (wordsReal : HarmonicWordsReal (interpretedKahler (ghostRGrading w) hA hB
      (ghostPos w hw) (hZproved w) (relativeDifferentialGood_of_affine hA hB w hw)
      (interpretedKahlerAnticomm_of_sp2 _ hA hB _ _ _ S))
      (concreteGUData _ (sp2ConjData _ hA hB _ _ _ S R))) :
    VirGradedUnitary leeYangC leeYangRealStructure :=
  leeYang_gradedUnitary_of_affine_kahler hA hB w hw
    (interpretedKahlerAnticomm_of_sp2 _ hA hB _ _ _ S) (sp2ConjData _ hA hB _ _ _ S R)
    symbols character vacuumNormalized creationAdjoint wordsReal

end

end VOA.ConcreteHodge
