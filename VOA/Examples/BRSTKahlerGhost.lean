/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.BRSTKahlerInterpreted

/-!
# The Lee–Yang endpoint for an arbitrary positive ghost form with the standard ghost grading

The endpoint `leeYang_gradedUnitary_of_affine_kahler` fixes the ghost form to be `ghostForm w`,
which gives the three colours of `bc` ghosts (Chevalley colours `e, f, h`) the **same** mode norms.
Beem–Garner's form on `Sf[ℂ² ⊗ sl₂]` is `sl₂`-invariant; in the Chevalley basis an invariant
Hermitian form on `sl₂*` (where the `c`'s live) gives `h*` half the norm of `e*`, `f*`. The
`sp(2)` adjoint relation is therefore expected only for colour-weighted forms (module docstring of
`BRSTKahlerInterpreted`). This file removes the colour-uniformity from the endpoint:

* `brstDeg_std` — every `GhostRGrading` whose grading is the standard `ghostDeg` has the same BRST
  grading as `ghostRGrading w`; hence `zeroModesPreserve_std` and
  `relativeDifferentialGood_std`: the zero-mode and goodness inputs hold for **every** positive
  ghost form with the standard grading (from the proved `w`-statements).
* `interpretedGenerators_std` — the vacuum and creation tests (`ClassGeneratorFiltration`) for
  every such ghost form (generalizing `interpretedGenerators` + `interpretedCreation_proved`).
* `ghostFormC w` — the colour-weighted ghost form (one weight function per colour),
  `ghostFormC_pos`, and `ghostRGradingC w` (standard grading, orthogonal for `ghostFormC w`);
  `bgColourWeight` — the expected Beem–Garner normalization (`b^h` norms doubled, `c^h` norms
  halved; *expected, not verified here*).
* `leeYang_gradedUnitary_of_affine_sp2` — **Affine GU ⇒ Lee–Yang GU** for an arbitrary positive
  ghost form with the standard grading, with the Kähler relation replaced by the `sp(2)` adjoint
  relation (`InterpretedSp2`), `ρ_Dp` removed (`ReducedConj`), and the zero-mode, goodness and
  generator inputs proved; `leeYang_gradedUnitary_of_affine_sp2_colour` — the specialization to
  colour-weighted forms.

Everything is proved outright from the listed hypotheses.
-/

namespace VOA.ConcreteHodge

open Sl2CosetConcrete Sl2SemiInfinite AffineSl2GeneralRigidity AffineSl2BelowCritical
open VOA.GradedUnitaryCohomology VOA.LeeYangCosetTransfer VOA.VertexOperatorAlgebra
open VOA.LeeYangTransferAssembly LeeYangShortcut VirModule LeeYang VirGradedUnitarity
open VOA.SympFerm VOA.Ghost
open scoped TensorProduct

noncomputable section

/-- The unit ghost weight. -/
def unitWeight : Finset ModeIdx → ℝ := fun _ => 1

theorem unitWeight_pos : ∀ s, 0 < unitWeight s := fun _ => one_pos

/-! ### The standard ghost grading -/

section Std

variable {PG : SesqForm Sl2GhostSpace} (Gh : GhostRGrading PG)

/-- A ghost grading is **standard** if it is `ghostDeg`. -/
def GhostRGrading.IsStd : Prop := Gh.deg = ghostDeg

variable {Gh}

theorem brstDeg_std (hs : Gh.IsStd) : brstDeg Gh = brstDeg (ghostRGrading unitWeight) := by
  unfold brstDeg; rw [hs]; rfl

/-- The zero-mode input for every standard ghost grading. -/
theorem zeroModesPreserve_std (hs : Gh.IsStd) : ZeroModesPreserve Gh := by
  unfold ZeroModesPreserve; rw [brstDeg_std hs]; exact hZproved unitWeight

/-- Goodness of the actual differential for every standard ghost grading. -/
theorem relativeDifferentialGood_std (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    {BB : InvariantForm BVOA} {RB : RealStructure BVOA} (hB : Unitary BB RB) (hs : Gh.IsStd) :
    RelativeDifferentialGood Gh := by
  unfold RelativeDifferentialGood; rw [brstDeg_std hs]
  exact relativeDifferentialGood_of_affine hA hB unitWeight unitWeight_pos

theorem brstDeg_nonnegR_std (hs : Gh.IsStd) : NonnegR (brstDeg Gh) := by
  rw [brstDeg_std hs]; exact brstDeg_nonnegR unitWeight

theorem brstVacuum_mem_std (hs : Gh.IsStd) :
    ((ASVA.vacuum ⊗ₜ[ℂ] BSVA.vacuum) ⊗ₜ[ℂ] USVA.vacuum) ⊗ₜ[ℂ] sl2GhostSVA.vacuum ∈
      brstDeg Gh ((0, 0), 0) := by
  rw [brstDeg_std hs]; exact brstVacuum_mem unitWeight

theorem creation_shift_std (hs : Gh.IsStd)
    (hA : GradedUnitary affineForm affineRealStructure affineFlag) (p : ℕ) (j : ℤ)
    {v : BRSTSpace} (hv : v ∈ ⨆ (k : (ℤ × ℤ) × ℂ) (_ : RowPred p k), brstDeg Gh k) :
    brstSVA.Y omegaB j v ∈ ⨆ (k : (ℤ × ℤ) × ℂ) (_ : RowPred (p + 1) k), brstDeg Gh k := by
  rw [brstDeg_std hs] at hv ⊢
  exact creation_shift unitWeight hA p j hv

end Std

/-! ### The generator tests for a standard ghost grading -/

section Generators

variable {PG : SesqForm Sl2GhostSpace} (Gh : GhostRGrading PG)
  (hA : GradedUnitary affineForm affineRealStructure affineFlag)
  {BB : InvariantForm BVOA} {RB : RealStructure BVOA} (hB : Unitary BB RB)
  (hG : IsPosOn PG ⊤) (hZ : ZeroModesPreserve Gh) (hD : RelativeDifferentialGood Gh)
  (hK : InterpretedKahlerAnticomm Gh hA hB hG hZ hD)

theorem degOn_to_brst_std (n : ℤ)
    (hp : IsPosOn ((interpretedKahler Gh hA hB hG hZ hD hK).geometry n).P ⊤)
    (p : ℕ) (c : relativeWeight n)
    (hc : c ∈ ((interpretedKahler Gh hA hB hG hZ hD hK).model n hp).degOn
      (KahlerComplex.rowSet (Finset.Icc 0 (2 * (p : ℤ))) 0)) :
    (c : BRSTSpace) ∈ ⨆ (k : (ℤ × ℤ) × ℂ) (_ : RowPred p k), brstDeg Gh k := by
  refine Submodule.iSup_induction _ (motive := fun c : relativeWeight n =>
    (c : BRSTSpace) ∈ ⨆ (k : (ℤ × ℤ) × ℂ) (_ : RowPred p k), brstDeg Gh k)
    hc ?_ (by simp) (fun x y hx hy => by
      beta_reduce at hx hy ⊢; rw [Submodule.coe_add]; exact Submodule.add_mem _ hx hy)
  rintro ⟨a, ha⟩ y hy
  have hy' : (y : BRSTSpace) ∈ brstDeg Gh (a, (n : ℂ)) := hy
  obtain ⟨ha1, ha2⟩ := ha
  exact Submodule.mem_iSup_of_mem (a, (n : ℂ))
    (Submodule.mem_iSup_of_mem ⟨(Finset.mem_Icc.mp ha1).2, ha2⟩ hy')

theorem brst_to_degOn_std (hs : Gh.IsStd) (n : ℤ)
    (hp : IsPosOn ((interpretedKahler Gh hA hB hG hZ hD hK).geometry n).P ⊤)
    (p : ℕ) (v : relativeWeight n)
    (hv : (v : BRSTSpace) ∈ ⨆ (k : (ℤ × ℤ) × ℂ) (_ : RowPred p k), brstDeg Gh k) :
    v ∈ ((interpretedKahler Gh hA hB hG hZ hD hK).model n hp).degOn
      (KahlerComplex.rowSet (Finset.Icc 0 (2 * (p : ℤ))) 0) := by
  classical
  have hI := brstDeg_isInternal Gh hA hB hG
  have hstab := relativeWeight_stable Gh hA hB hG hZ n
  have hzero := (mem_iSup_pred_iff hI _ _).mp hv
  obtain ⟨s, hs'⟩ := sum_iproj hI (v : BRSTSpace)
  have hv' : v = ∑ k ∈ s, (⟨iproj hI k v, hstab k v v.2⟩ : relativeWeight n) := by
    apply Subtype.ext; rw [Submodule.coe_sum]; exact hs'.symm
  rw [hv']
  refine Submodule.sum_mem _ fun k _ => ?_
  by_cases hk : RowPred p k ∧ k.2 = (n : ℂ) ∧ 0 ≤ k.1.1
  · obtain ⟨⟨hk1, hk2⟩, hk3, hk4⟩ := hk
    refine KahlerComplex.deg_le_degOn _ (a := k.1)
      (show k.1 ∈ KahlerComplex.rowSet (Finset.Icc 0 (2 * (p : ℤ))) 0 from
        ⟨Finset.mem_Icc.mpr ⟨hk4, hk1⟩, hk2⟩) ?_
    change iproj hI k v ∈ brstDeg Gh (k.1, (n : ℂ))
    rw [← hk3]
    exact iproj_mem hI k _
  · have h0 : iproj hI k (v : BRSTSpace) = 0 := by
      by_cases h1 : RowPred p k
      · by_cases h2 : k.2 = (n : ℂ)
        · have h3 : k.1.1 < 0 := by
            by_contra h3; exact hk ⟨h1, h2, not_lt.mp h3⟩
          have := iproj_mem hI k (v : BRSTSpace)
          rwa [brstDeg_nonnegR_std hs k h3, Submodule.mem_bot] at this
        · exact iproj_eq_zero_of_weight hI brstSVA.isInternal wtIndex
            (brstDeg_le_weight Gh) v.2.2 h2
      · exact hzero k h1
    have : (⟨iproj hI k v, hstab k v v.2⟩ : relativeWeight n) = 0 := Subtype.ext h0
    rw [this]; exact Submodule.zero_mem _

set_option synthInstance.maxHeartbeats 400000 in
-- Instance search on the cycle spaces of the concrete Kähler model is slow.
set_option maxHeartbeats 1000000 in
-- The transport proof elaborates the heavy concrete model twice.
/-- The creation test for a standard ghost grading. -/
theorem interpretedCreation_std (hs : Gh.IsStd)
    (hp : ∀ n, IsPosOn ((interpretedKahler Gh hA hB hG hZ hD hK).geometry n).P ⊤) :
    ∀ (n : ℤ) (p i : ℕ) (x : UniversalWeight n),
      x ∈ generatorPullback (interpretedKahler Gh hA hB hG hZ hD hK) hp n p →
        universalCreation n i x ∈
          generatorPullback (interpretedKahler Gh hA hB hG hZ hD hK) hp (n + i + 2) (p + 1) := by
  intro n p i x hx
  set S := interpretedKahler Gh hA hB hG hZ hD hK
  have hDn := S.model_D n (hp n)
  have hDn' := S.model_D (n + i + 2) (hp (n + i + 2))
  refine cohomFilt_transport (S.model n (hp n)) (S.model (n + i + 2) (hp (n + i + 2)))
    (creationOp n i) (fun v => ?_) _ _ (fun v hv => ?_) _ _ ?_ hx
  · rw [LinearMap.congr_fun hDn', LinearMap.congr_fun hDn, creationOp_D]
  · have h1 := degOn_to_brst_std Gh hA hB hG hZ hD hK n (hp n) p v hv
    have h2 := creation_shift_std hs hA p (-(-(i : ℤ) - 1) - 1) h1
    have h3 := brst_to_degOn_std Gh hA hB hG hZ hD hK hs (n + i + 2) (hp (n + i + 2)) (p + 1)
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

set_option synthInstance.maxHeartbeats 200000 in
-- Instance search on the cycle space of the concrete Kähler model is slow.
/-- The vacuum test for a standard ghost grading. -/
theorem interpreted_vacuum_std (hs : Gh.IsStd)
    (hp : ∀ n, IsPosOn ((interpretedKahler Gh hA hB hG hZ hD hK).geometry n).P ⊤) :
    universalVacuum ∈ generatorPullback (interpretedKahler Gh hA hB hG hZ hD hK) hp 0 0 := by
  set S := interpretedKahler Gh hA hB hG hZ hD hK
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
    brstDeg Gh ((0, 0), ((0 : ℤ) : ℂ))
  rw [representative_vacuum, Int.cast_zero]
  exact brstVacuum_mem_std hs

/-- **`ClassGeneratorFiltration` for every standard ghost grading** (both tests proved). -/
theorem interpretedGenerators_std (hs : Gh.IsStd)
    (hp : ∀ n, IsPosOn ((interpretedKahler Gh hA hB hG hZ hD hK).geometry n).P ⊤) :
    ClassGeneratorFiltration (interpretedKahler Gh hA hB hG hZ hD hK) hp where
  vacuum := interpreted_vacuum_std Gh hA hB hG hZ hD hK hs hp
  creation := interpretedCreation_std Gh hA hB hG hZ hD hK hs hp

end Generators

/-! ### The endpoint for an arbitrary positive ghost form -/

/-- The proved inputs, bundled: zero modes and goodness for a standard ghost grading. -/
abbrev stdZ {PG : SesqForm Sl2GhostSpace} {Gh : GhostRGrading PG} (hs : Gh.IsStd) :
    ZeroModesPreserve Gh := zeroModesPreserve_std hs

abbrev stdD (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    {BB : InvariantForm BVOA} {RB : RealStructure BVOA} (hB : Unitary BB RB)
    {PG : SesqForm Sl2GhostSpace} {Gh : GhostRGrading PG} (hs : Gh.IsStd) :
    RelativeDifferentialGood Gh := relativeDifferentialGood_std hA hB hs

/-- The interpreted Kähler geometry from the `sp(2)` input, for a standard ghost grading. -/
abbrev sp2Kahler (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    {BB : InvariantForm BVOA} {RB : RealStructure BVOA} (hB : Unitary BB RB)
    {PG : SesqForm Sl2GhostSpace} (hG : IsPosOn PG ⊤) (Gh : GhostRGrading PG) (hs : Gh.IsStd)
    (S : InterpretedSp2 Gh hA hB hG (stdZ hs) (stdD hA hB hs)) : ConcreteKahlerGeometry :=
  interpretedKahler Gh hA hB hG (stdZ hs) (stdD hA hB hs)
    (interpretedKahlerAnticomm_of_sp2 Gh hA hB hG _ _ S)

/-- **Affine GU ⇒ Lee–Yang GU, for an arbitrary positive ghost form with the standard
grading**, with the Kähler relation replaced by the `sp(2)` adjoint relation, `ρ_Dp` removed,
and the zero-mode, goodness, vacuum and creation inputs proved. `#print axioms`-clean,
conditional on: `hA` (the hypothesis), `hB` (unitarity of `L_1`), `hG` (positivity of the ghost
form), `hs` (the grading is `ghostDeg`), `S` (Beem–Garner Lemma 3.16 for the `sp(2)` image),
`R` (reduced conjugation data), and the downstream `symbols`, `character`, `vacuumNormalized`,
`creationAdjoint`, `wordsReal`. -/
theorem leeYang_gradedUnitary_of_affine_sp2
    (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    {BB : InvariantForm BVOA} {RB : RealStructure BVOA} (hB : Unitary BB RB)
    {PG : SesqForm Sl2GhostSpace} (hG : IsPosOn PG ⊤) (Gh : GhostRGrading PG) (hs : Gh.IsStd)
    (S : InterpretedSp2 Gh hA hB hG (stdZ hs) (stdD hA hB hs))
    (R : ∀ n hp, ReducedConj (concreteGood (interpretedGoodGeometry Gh hA hB hG (stdZ hs)
      (stdD hA hB hs) (interpretedKahlerAnticomm_of_sp2 Gh hA hB hG _ _ S)) n hp) (S n).E)
    (symbols : LeadingInvariantSymbolDimension (sp2Kahler hA hB hG Gh hs S))
    (character : LeeYangPBWCharacter)
    (vacuumNormalized : HarmonicVacuumNormalized (sp2Kahler hA hB hG Gh hs S)
      (concreteGUData _ (sp2ConjData Gh hA hB hG _ _ S R)))
    (creationAdjoint : HarmonicCreationAdjoint (sp2Kahler hA hB hG Gh hs S)
      (concreteGUData _ (sp2ConjData Gh hA hB hG _ _ S R)))
    (wordsReal : HarmonicWordsReal (sp2Kahler hA hB hG Gh hs S)
      (concreteGUData _ (sp2ConjData Gh hA hB hG _ _ S R))) :
    VirGradedUnitary leeYangC leeYangRealStructure :=
  leeYang_gradedUnitary_of_affine_interpreted hA hB hG Gh (stdZ hs) (stdD hA hB hs)
    (interpretedKahlerAnticomm_of_sp2 Gh hA hB hG _ _ S) (sp2ConjData Gh hA hB hG _ _ S R)
    symbols character
    (fun hp => interpretedGenerators_std Gh hA hB hG _ _ _ hs hp)
    vacuumNormalized creationAdjoint wordsReal

/-! ### Colour-weighted ghost forms -/

/-- **The colour-weighted ghost form**: one weight function per colour `a : Fin 3`
(the three factors of `Sl2GhostSpace = (FockSF ⊗ FockSF) ⊗ FockSF`). -/
def ghostFormC (w : Fin 3 → Finset ModeIdx → ℝ) : SesqForm Sl2GhostSpace :=
  ((fockForm (w 0)).tensor (fockForm (w 1))).tensor (fockForm (w 2))

theorem ghostFormC_pos (w : Fin 3 → Finset ModeIdx → ℝ) (hw : ∀ a s, 0 < w a s) :
    IsPosOn (ghostFormC w) ⊤ :=
  SesqForm.isPosOn_tensor _ _ (SesqForm.isPosOn_tensor _ _ (basisForm_pos _ _ (hw 0))
    (basisForm_pos _ _ (hw 1))) (basisForm_pos _ _ (hw 2))

/-- The colour-uniform form is the special case of constant colour weights. -/
theorem ghostFormC_const (w : Finset ModeIdx → ℝ) : ghostFormC (fun _ => w) = ghostForm w := rfl

/-- The standard ghost grading, orthogonal for every colour-weighted form. -/
def ghostRGradingC (w : Fin 3 → Finset ModeIdx → ℝ) : GhostRGrading (ghostFormC w) where
  deg := ghostDeg
  span := tensorDeg_span _ _ (tensorDeg_span _ _ (basisDeg_span _ _) (basisDeg_span _ _))
    (basisDeg_span _ _)
  orth := tensorDeg_orth _ _ _ _ (tensorDeg_orth _ _ _ _ (basisDeg_orth _ _ _)
    (basisDeg_orth _ _ _)) (basisDeg_orth _ _ _)
  le_weight := ghostDeg_le_weight
  le_ghost := ghostDeg_le_ghost

theorem ghostRGradingC_isStd (w : Fin 3 → Finset ModeIdx → ℝ) : (ghostRGradingC w).IsStd := rfl

/-- The expected Beem–Garner colour normalization of one mode: `bgModeNorm` on the `e`, `f`
colours (`a = 0, 1`); on the `h` colour (`a = 2`) the `b`-mode norm is doubled and the `c`-mode
norm halved (the `sl₂`-invariant Hermitian form on `sl₂ ⊕ sl₂*` in the Chevalley basis).
*Expected, not verified here*: whether this exact choice satisfies `InterpretedSp2` is open. -/
def bgColourNorm (a : Fin 3) (p : ℕ × Fin 2) : ℝ :=
  bgModeNorm p * (if a = 2 then (if p.2 = 0 then 2 else 1 / 2) else 1)

theorem bgColourNorm_pos (a : Fin 3) (p : ℕ × Fin 2) : 0 < bgColourNorm a p := by
  unfold bgColourNorm
  have := bgModeNorm_pos p
  split_ifs <;> positivity

/-- The expected Beem–Garner colour weight of a monomial. -/
def bgColourWeight (a : Fin 3) (s : Finset ModeIdx) : ℝ := ∏ p ∈ s, bgColourNorm a (ofLex p)

theorem bgColourWeight_pos (a : Fin 3) (s : Finset ModeIdx) : 0 < bgColourWeight a s :=
  Finset.prod_pos fun _ _ => bgColourNorm_pos _ _

/-- **The endpoint for colour-weighted ghost forms.** -/
theorem leeYang_gradedUnitary_of_affine_sp2_colour
    (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    {BB : InvariantForm BVOA} {RB : RealStructure BVOA} (hB : Unitary BB RB)
    (w : Fin 3 → Finset ModeIdx → ℝ) (hw : ∀ a s, 0 < w a s)
    (S : InterpretedSp2 (ghostRGradingC w) hA hB (ghostFormC_pos w hw)
      (stdZ (ghostRGradingC_isStd w)) (stdD hA hB (ghostRGradingC_isStd w)))
    (R : ∀ n hp, ReducedConj (concreteGood (interpretedGoodGeometry (ghostRGradingC w) hA hB
      (ghostFormC_pos w hw) (stdZ (ghostRGradingC_isStd w)) (stdD hA hB (ghostRGradingC_isStd w))
      (interpretedKahlerAnticomm_of_sp2 _ hA hB _ _ _ S)) n hp) (S n).E)
    (symbols : LeadingInvariantSymbolDimension
      (sp2Kahler hA hB (ghostFormC_pos w hw) _ (ghostRGradingC_isStd w) S))
    (character : LeeYangPBWCharacter)
    (vacuumNormalized : HarmonicVacuumNormalized
      (sp2Kahler hA hB (ghostFormC_pos w hw) _ (ghostRGradingC_isStd w) S)
      (concreteGUData _ (sp2ConjData _ hA hB _ _ _ S R)))
    (creationAdjoint : HarmonicCreationAdjoint
      (sp2Kahler hA hB (ghostFormC_pos w hw) _ (ghostRGradingC_isStd w) S)
      (concreteGUData _ (sp2ConjData _ hA hB _ _ _ S R)))
    (wordsReal : HarmonicWordsReal
      (sp2Kahler hA hB (ghostFormC_pos w hw) _ (ghostRGradingC_isStd w) S)
      (concreteGUData _ (sp2ConjData _ hA hB _ _ _ S R))) :
    VirGradedUnitary leeYangC leeYangRealStructure :=
  leeYang_gradedUnitary_of_affine_sp2 hA hB (ghostFormC_pos w hw) (ghostRGradingC w)
    (ghostRGradingC_isStd w) S R symbols character vacuumNormalized creationAdjoint wordsReal

end

end VOA.ConcreteHodge
