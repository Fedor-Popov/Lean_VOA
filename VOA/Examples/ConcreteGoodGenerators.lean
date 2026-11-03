/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.ConcreteGoodEndpoint
import VOA.Examples.ConcreteGoodLayers

/-!
# The vacuum generator test, and the concrete endpoint

* `brstVacuum_mem` — the BRST vacuum `((𝟙_A ⊗ 𝟙_B) ⊗ 𝟙_U) ⊗ 𝟙_gh` lies in the interpreted piece
  `((2R, gh), weight) = ((0, 0), 0)` (for the concrete ghost grading `ghostRGrading w`).
* `interpretedGenerators` — the `vacuum` field of `ClassGeneratorFiltration` is **proved**
  for the interpreted geometry; only the `creation` field (`L_{-i-2}` raises the class filtration
  by at most one, i.e. `ω_C` has interpreted degree `≤ 1`) remains an input.
* `leeYang_gradedUnitary_of_affine_ghost` — the Lee–Yang endpoint with the concrete ghost
  form `ghostForm w` (`w > 0`), the concrete ghost grading, the matter factor zero-mode
  statements discharged (`aZeroModesPreserveLayers`, `uZeroModesPreserveLayers`), and the vacuum
  generator test discharged.
-/

namespace VOA.ConcreteHodge

open LeeYangTransferAssembly LeeYangShortcut Sl2CosetConcrete Sl2SemiInfinite
open VirGradedUnitarity LeeYang VOA.VertexOperatorAlgebra VOA.GradedUnitaryCohomology
open VOA.SympFerm VOA.Ghost
open scoped TensorProduct

noncomputable section

theorem cyclesCongr_coe {K : Type*} [AddCommGroup K] [Module ℂ K] (d d' : K →ₗ[ℂ] K)
    (hd : d = d') (x : LinearMap.ker d) : ((cyclesCongr d d' hd x : LinearMap.ker d') : K) = x := by
  subst hd; rfl

/-- A cycle whose underlying vector lies in `degOn A` has its class in `cohomFilt A`. -/
theorem class_mem_cohomFilt {K M : Type*} [AddCommGroup K] [Module ℂ K] [AddCommGroup M]
    [Module ℂ M] [FiniteDimensional ℂ K] (C : KahlerComplex K) (f : M →ₗ[ℂ] LinearMap.ker C.D)
    (x : M) (A : Set (ℤ × ℤ)) (h : ((f x : LinearMap.ker C.D) : K) ∈ C.degOn A) :
    cycleClassOfCycles C.D f x ∈ C.cohomFilt A :=
  Submodule.mem_map.mpr ⟨f x, h, rfl⟩

/-! ### Vacua in the interpreted grading -/

theorem vacuum_mem_layerDeg {𝒱 : Type*} [AddCommGroup 𝒱] [Module ℂ 𝒱]
    {W : VertexOperatorAlgebra 𝒱} (B : InvariantForm W) (F : GradedFlag W) :
    W.vacuum ∈ layerDeg B F ((0, 0), 0) := by
  have hv : (⟨W.vacuum, W.vacuum_mem⟩ : W.grading 0) ∈ F.layer 0 (LiRadical.gradedForm B 0) 0 := by
    rw [GradedFlag.layer_zero]
    change W.vacuum ∈ F.piece 0 0
    rw [F.vacuum_zero]
    exact Submodule.mem_span_singleton_self _
  refine Submodule.mem_iSup_of_mem 0 (Submodule.mem_iSup_of_mem 0
    (Submodule.mem_iSup_of_mem ?_ (Submodule.mem_map_of_mem hv)))
  simp [layerIndex]

theorem vacuum_mem_trivialDeg {𝒱 : Type*} [AddCommGroup 𝒱] [Module ℂ 𝒱]
    (W : VertexOperatorAlgebra 𝒱) : W.vacuum ∈ trivialDeg W ((0, 0), 0) := by
  simp only [trivialDeg, if_true]
  rw [show (0 : ℂ) = ((0 : ℤ) : ℂ) by norm_num, PreVertexAlgebra.gradingC_intCast]
  exact W.vacuum_mem

theorem fockIndex_empty : fockIndex ∅ = ((0, 0), 0) := by
  simp [fockIndex, fockWord_empty, wordR, ghNum, ghWeight]

theorem vacSF_mem_fockDeg : vacSF ∈ fockDeg ((0, 0), 0) := by
  have h := basis_mem_basisDeg fockBasis fockIndex ∅
  rw [fockIndex_empty, fockBasis_eq_word, fockWord_empty] at h
  exact h

theorem ghostVacuum_mem_ghostDeg : sl2GhostSVA.vacuum ∈ ghostDeg ((0, 0), 0) := by
  rw [sl2GhostSVA_vacuum]
  have h := tmul_mem_tensorDeg _ _ (tmul_mem_tensorDeg _ _ vacSF_mem_fockDeg vacSF_mem_fockDeg)
    vacSF_mem_fockDeg
  simpa using h

/-- **The BRST vacuum has interpreted bidegree `(0, 0)` at weight `0`.** -/
theorem brstVacuum_mem (w : Finset ModeIdx → ℝ) :
    ((ASVA.vacuum ⊗ₜ[ℂ] BSVA.vacuum) ⊗ₜ[ℂ] USVA.vacuum) ⊗ₜ[ℂ] sl2GhostSVA.vacuum ∈
      brstDeg (ghostRGrading w) ((0, 0), 0) := by
  have hA : ASVA.vacuum ∈ aDeg ((0, 0), 0) := vacuum_mem_layerDeg affineForm affineFlag
  have hB : BSVA.vacuum ∈ bDeg ((0, 0), 0) := vacuum_mem_trivialDeg BVOA
  have hU : USVA.vacuum ∈ uDeg ((0, 0), 0) := vacuum_mem_layerDeg auxiliaryForm auxiliaryFlag
  have h := tmul_mem_tensorDeg matterDeg (ghostRGrading w).deg
    (tmul_mem_tensorDeg _ _ (tmul_mem_tensorDeg _ _ hA hB) hU) ghostVacuum_mem_ghostDeg
  simpa using h

/-! ### The vacuum generator test -/

section Interpreted

variable (w : Finset ModeIdx → ℝ) (hw : ∀ s, 0 < w s)
  (hA : GradedUnitary affineForm affineRealStructure affineFlag)
  {BB : InvariantForm BVOA} {RB : RealStructure BVOA} (hB : Unitary BB RB)

/-- The concrete ghost-form positivity. -/
abbrev ghostPos : IsPosOn (ghostForm w) ⊤ := ghostForm_pos w hw

theorem representative_vacuum :
    ((universalWeightRepresentative 0 universalVacuum : relativeWeight 0) : BRSTSpace) =
      ((ASVA.vacuum ⊗ₜ[ℂ] BSVA.vacuum) ⊗ₜ[ℂ] USVA.vacuum) ⊗ₜ[ℂ] sl2GhostSVA.vacuum := by
  change cosetToComplex (virasoroToCoset (VirModule.vacVec leeYangC)) = _
  rw [virasoroToCoset_vacuum, cosetToComplex_apply]
  rfl

set_option synthInstance.maxHeartbeats 200000 in
-- Instance search on the cycle space of the concrete Kähler model is slow.
/-- **The vacuum test of `ClassGeneratorFiltration`, proved for the interpreted geometry.** -/
theorem interpreted_vacuum (hZ : ZeroModesPreserve (ghostRGrading w))
    (hD : RelativeDifferentialGood (ghostRGrading w))
    (hK : InterpretedKahlerAnticomm (ghostRGrading w) hA hB (ghostPos w hw) hZ hD)
    (hp : ∀ n, IsPosOn
      ((interpretedKahler (ghostRGrading w) hA hB (ghostPos w hw) hZ hD hK).geometry n).P ⊤) :
    universalVacuum ∈
      generatorPullback (interpretedKahler (ghostRGrading w) hA hB (ghostPos w hw) hZ hD hK)
        hp 0 0 := by
  set S := interpretedKahler (ghostRGrading w) hA hB (ghostPos w hw) hZ hD hK
  change modelUniversalClass S 0 (hp 0) universalVacuum ∈ generatorCohomPrefix S hp 0 0
  refine class_mem_cohomFilt (S.model 0 (hp 0)) (modelUniversalCycles S 0 (hp 0))
    universalVacuum _ ?_
  have hcoe : ((modelUniversalCycles S 0 (hp 0) universalVacuum :
      LinearMap.ker (S.model 0 (hp 0)).D) : relativeWeight 0) =
      universalWeightRepresentative 0 universalVacuum :=
    cyclesCongr_coe _ _ _ _
  rw [hcoe]
  have hrow : ((0 : ℤ), (0 : ℤ)) ∈
      KahlerComplex.rowSet (Finset.Icc 0 (2 * ((0 : ℕ) : ℤ))) 0 := ⟨by simp, rfl⟩
  refine KahlerComplex.deg_le_degOn (S.model 0 (hp 0)) hrow ?_
  change (universalWeightRepresentative 0 universalVacuum : BRSTSpace) ∈
    brstDeg (ghostRGrading w) ((0, 0), ((0 : ℤ) : ℂ))
  rw [representative_vacuum, Int.cast_zero]
  exact brstVacuum_mem w

/-- **OPEN: the creation test** — for the interpreted geometry, `L_{-i-2}` raises the class
filtration by at most one (equivalently, the representative of an `r`-fold Virasoro word has
interpreted `2R ≤ 2r`; the coset stress tensor has interpreted degree `≤ 1`). -/
def InterpretedCreation (hZ : ZeroModesPreserve (ghostRGrading w))
    (hD : RelativeDifferentialGood (ghostRGrading w))
    (hK : InterpretedKahlerAnticomm (ghostRGrading w) hA hB (ghostPos w hw) hZ hD)
    (hp : ∀ n, IsPosOn
      ((interpretedKahler (ghostRGrading w) hA hB (ghostPos w hw) hZ hD hK).geometry n).P ⊤) :
    Prop :=
  ∀ (n : ℤ) (p i : ℕ) (x : UniversalWeight n),
    x ∈ generatorPullback (interpretedKahler (ghostRGrading w) hA hB (ghostPos w hw) hZ hD hK)
      hp n p →
      universalCreation n i x ∈
        generatorPullback (interpretedKahler (ghostRGrading w) hA hB (ghostPos w hw) hZ hD hK)
          hp (n + i + 2) (p + 1)

/-- **`ClassGeneratorFiltration` from the creation test alone.** -/
theorem interpretedGenerators (hZ : ZeroModesPreserve (ghostRGrading w))
    (hD : RelativeDifferentialGood (ghostRGrading w))
    (hK : InterpretedKahlerAnticomm (ghostRGrading w) hA hB (ghostPos w hw) hZ hD)
    (hp : ∀ n, IsPosOn
      ((interpretedKahler (ghostRGrading w) hA hB (ghostPos w hw) hZ hD hK).geometry n).P ⊤)
    (hc : InterpretedCreation w hw hA hB hZ hD hK hp) :
    ClassGeneratorFiltration
      (interpretedKahler (ghostRGrading w) hA hB (ghostPos w hw) hZ hD hK) hp where
  vacuum := interpreted_vacuum w hw hA hB hZ hD hK hp
  creation := hc

end Interpreted

/-! ### The ghost zero-mode inputs -/

/-- **OPEN (ghosts)**: the ghost current zero modes preserve the concrete ghost grading
(`J^gh_0 = Σ f :c b:_0` moves one mode between pairs at the same level). -/
def GhostCurrentZeroPreserve : Prop :=
  ∀ a i, ∀ y ∈ ghostDeg i, ghZero a y ∈ ghostDeg i

/-- **OPEN (ghosts)**: the antighost zero modes `b_0` (which remove `c_0`, of `R = 0`, weight `0`,
ghost number `+1`) map `ghostDeg i` into `ghostDeg (ghDown i)`. -/
def AntighostZeroShift : Prop :=
  ∀ a i, ∀ y ∈ ghostDeg i, antiZero a y ∈ ghostDeg (ghDown i)

/-- `ZeroModesPreserve` for the concrete ghost grading, from the two ghost statements (the matter
statements are proved). -/
theorem zeroModesPreserve_concrete (w : Finset ModeIdx → ℝ) (hG0 : GhostCurrentZeroPreserve)
    (hb0 : AntighostZeroShift) : ZeroModesPreserve (ghostRGrading w) :=
  zeroModesPreserve_of_factors (ghostRGrading w) aZeroModesPreserveLayers
    uZeroModesPreserveLayers hG0 hb0

/-! ### The concrete endpoint -/

/-- **Affine GU ⇒ Lee–Yang GU, with the interpreted geometry and the concrete ghost form.**
`#print axioms`-clean, conditional on the listed inputs. Compared with
`leeYang_gradedUnitary_of_affine_concrete'`: the uninterpreted geometry `I`, the ghost form, its
positivity `hG`, the ghost grading, the matter zero-mode homogeneity and the vacuum generator test
are gone; they are replaced by the precise open statements `hG0`, `hb0`, `hD`, `hK`, `hc`. -/
theorem leeYang_gradedUnitary_of_affine_ghost
    (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    {BB : InvariantForm BVOA} {RB : RealStructure BVOA} (hB : Unitary BB RB)
    (w : Finset ModeIdx → ℝ) (hw : ∀ s, 0 < w s)
    (hG0 : GhostCurrentZeroPreserve) (hb0 : AntighostZeroShift)
    (hD : RelativeDifferentialGood (ghostRGrading w))
    (hK : InterpretedKahlerAnticomm (ghostRGrading w) hA hB (ghostPos w hw)
      (zeroModesPreserve_concrete w hG0 hb0) hD)
    (R : ∀ n hp, GoodComplex.ConjData (concreteGood (interpretedGoodGeometry (ghostRGrading w)
      hA hB (ghostPos w hw) (zeroModesPreserve_concrete w hG0 hb0) hD hK) n hp))
    (symbols : LeadingInvariantSymbolDimension (interpretedKahler (ghostRGrading w) hA hB
      (ghostPos w hw) (zeroModesPreserve_concrete w hG0 hb0) hD hK))
    (character : LeeYangPBWCharacter)
    (creation : ∀ hp, InterpretedCreation w hw hA hB (zeroModesPreserve_concrete w hG0 hb0)
      hD hK hp)
    (vacuumNormalized : HarmonicVacuumNormalized (interpretedKahler (ghostRGrading w) hA hB
      (ghostPos w hw) (zeroModesPreserve_concrete w hG0 hb0) hD hK) (concreteGUData _ R))
    (creationAdjoint : HarmonicCreationAdjoint (interpretedKahler (ghostRGrading w) hA hB
      (ghostPos w hw) (zeroModesPreserve_concrete w hG0 hb0) hD hK) (concreteGUData _ R))
    (wordsReal : HarmonicWordsReal (interpretedKahler (ghostRGrading w) hA hB
      (ghostPos w hw) (zeroModesPreserve_concrete w hG0 hb0) hD hK) (concreteGUData _ R)) :
    VirGradedUnitary leeYangC leeYangRealStructure :=
  leeYang_gradedUnitary_of_affine_interpreted hA hB (ghostPos w hw) (ghostRGrading w)
    (zeroModesPreserve_concrete w hG0 hb0) hD hK R symbols character
    (fun hp => interpretedGenerators w hw hA hB _ hD hK hp (creation hp))
    vacuumNormalized creationAdjoint wordsReal

end

end VOA.ConcreteHodge
