/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.TwoSeriesHodgeGeometry
import VOA.Examples.ConcreteGoodGenerators

/-!
# Level-generic port of the zero-mode, layer and vacuum-generator parts of `ConcreteGood*`

Only the declarations mentioning the actual level-`L` factors are restated (with an explicit
`L : CosetLevels`); everything level-independent is reused from `ConcreteGoodZeroModes`,
`ConcreteGoodLayers`, `ConcreteGoodGenerators`.
-/

namespace VOA.TwoSeries

open VOA.ConcreteHodge Sl2CosetConcrete Sl2SemiInfinite AffineSl2GeneralRigidity
open AffineSl2BelowCritical VOA.GradedUnitaryCohomology VOA.LeeYangCosetTransfer
open VOA.VertexOperatorAlgebra VOA.LeeYangTransferAssembly AffineVOA AffineVOA.Inst
open AffineVOA.CorrectedR LeeYangTransferAssembly LeeYangShortcut VirGradedUnitarity LeeYang
open VOA.SympFerm VOA.Ghost
open scoped TensorProduct

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

variable (L : CosetLevels)

/-! ## Port of `ConcreteGoodZeroModes` -/


/-! ### Generic tensor-operator lemmas -/

section Generic

universe u v w

variable {ι : Type w} [AddCommGroup ι]
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : Type v} [AddCommGroup W] [Module ℂ W]

end Generic

/-! ### The factor statements -/

/-- The `A` current zero mode. -/
def aZero (a : Fin 3) : Module.End ℂ (ASpace L) := mode ((ASVA L).Y ((aAction L).current a)) 0

/-- The `U` current zero mode. -/
def uZero (a : Fin 3) : Module.End ℂ (USpace L) := mode ((USVA L).Y ((uAction L).current a)) 0

/-- **OPEN (factor `A`)**: the current zero modes preserve the orthogonal layers of the corrected
flag. Mathematically: `J₀` preserves each corrected filtration step (Li-goodness of zero modes)
and is skew for the invariant form, hence preserves `F_p ∩ F_{p-1}^⊥`. -/
def AZeroModesPreserveLayers : Prop := ∀ a i, ∀ x ∈ (aDeg L) i, (aZero L) a x ∈ (aDeg L) i

/-- **OPEN (factor `U`)**: the same for the ordinary PBW layers of `auxiliaryFlag L`. -/
def UZeroModesPreserveLayers : Prop := ∀ a i, ∀ x ∈ (uDeg L) i, (uZero L) a x ∈ (uDeg L) i

theorem matter_mem_parity_zero (x : (MatterSpace L)) : x ∈ (matterSVA L).parity 0 := by
  induction x using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | add x y hx hy => exact Submodule.add_mem _ hx hy
  | tmul w z =>
      induction w using TensorProduct.induction_on with
      | zero => rw [TensorProduct.zero_tmul]; exact Submodule.zero_mem _
      | add w w' hw hw' => rw [TensorProduct.add_tmul]; exact Submodule.add_mem _ hw hw'
      | tmul x y =>
          have hx : x ∈ (ASVA L).parity 0 := by
            change x ∈ (ParityGrading.even (ASpace L)).parity 0; simp [ParityGrading.even]
          have hy : y ∈ BSVA.parity (0 - 0) := by
            change y ∈ (ParityGrading.even BSpace).parity (0 - 0); simp [ParityGrading.even]
          have hz : z ∈ (USVA L).parity (0 - 0) := by
            change z ∈ (ParityGrading.even (USpace L)).parity (0 - 0); simp [ParityGrading.even]
          exact TensorVA.tmul_mem_tenParity (abSVA L) (USVA L)
            (TensorVA.tmul_mem_tenParity (ASVA L) BSVA hx hy) hz

/-- The matter current zero mode on pure triple tensors. -/
theorem matterZero_tmul (a : Fin 3) (x : (ASpace L)) (y : BSpace) (z : (USpace L)) :
    mode ((matterSVA L).Y ((matterAction L).toAffineSl2Action.current a)) 0
        ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] z) =
      (((aZero L) a x ⊗ₜ[ℂ] y + x ⊗ₜ[ℂ] bZero a y) ⊗ₜ[ℂ] z) +
        (x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (uZero L) a z := by
  have h1 := tensorCurrentMode_tmul
    (tensorAffineAction (aAction L).toAffineSl2Action bAction.toAffineSl2Action
      (aParityCompatible L) bParityCompatible (abTensorGrading L)) (uAction L).toAffineSl2Action a 0
    (x ⊗ₜ[ℂ] y) z
  have h2 : mode ((TensorVA.tensorSVA (ASVA L) BSVA (aParityCompatible L) bParityCompatible
      (abTensorGrading L)).Y ((tensorAffineAction (aAction L).toAffineSl2Action
          bAction.toAffineSl2Action
        (aParityCompatible L) bParityCompatible (abTensorGrading L)).current a)) 0 (x ⊗ₜ[ℂ] y) =
      (aZero L) a x ⊗ₜ[ℂ] y + x ⊗ₜ[ℂ] bZero a y :=
    tensorCurrentMode_tmul (aAction L).toAffineSl2Action bAction.toAffineSl2Action a 0 x y
  refine h1.trans ?_
  change mode ((TensorVA.tensorSVA (ASVA L) BSVA (aParityCompatible L) bParityCompatible
      (abTensorGrading L)).Y ((tensorAffineAction (aAction L).toAffineSl2Action
          bAction.toAffineSl2Action
        (aParityCompatible L) bParityCompatible (abTensorGrading L)).current a)) 0 (x ⊗ₜ[ℂ] y)
            ⊗ₜ[ℂ] z +
      (x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (uZero L) a z = _
  rw [h2]

theorem matterDeg_zero_preserve (hA0 : (AZeroModesPreserveLayers L))
    (hU0 : (UZeroModesPreserveLayers L)) (a : Fin 3) (i : (ℤ × ℤ) × ℂ) :
    ∀ x ∈ (matterDeg L) i,
      mode ((matterSVA L).Y ((matterAction L).toAffineSl2Action.current a)) 0 x ∈ (matterDeg L)
          i := by
  let AB : Module.End ℂ ((ASpace L) ⊗[ℂ] BSpace) :=
    TensorProduct.map ((aZero L) a) LinearMap.id + TensorProduct.map LinearMap.id (bZero a)
  have hAB : ∀ j, ∀ w ∈ tensorDeg (aDeg L) bDeg j, AB w ∈ tensorDeg (aDeg L) bDeg j :=
    tensorDeg_preserve_sum (aDeg L) bDeg AB ((aZero L) a) (bZero a)
      (fun x y => by simp [AB, TensorProduct.map_tmul]) (hA0 a)
      (fun j y hy => bZero_preserve a j y hy)
  exact tensorDeg_preserve_sum _ (uDeg L) _ AB ((uZero L) a)
    (fun w z => by
      induction w using TensorProduct.induction_on with
      | zero => simp
      | add w w' hw hw' =>
          rw [TensorProduct.add_tmul, map_add, hw, hw', map_add, TensorProduct.add_tmul,
            TensorProduct.add_tmul]
          abel
      | tmul x y =>
          rw [matterZero_tmul]
          simp [AB, TensorProduct.map_tmul])
    hAB (hU0 a) i

/-- **`ZeroModesPreserve L` from the factors.** -/
theorem zeroModesPreserve_of_factors {PG : SesqForm Sl2GhostSpace} (Gh : GhostRGrading PG)
    (hA0 : (AZeroModesPreserveLayers L)) (hU0 : (UZeroModesPreserveLayers L))
    (hG0 : ∀ a i, ∀ y ∈ Gh.deg i, ghZero a y ∈ Gh.deg i)
    (hb0 : ∀ a i, ∀ y ∈ Gh.deg i, antiZero a y ∈ Gh.deg (ghDown i)) :
    (ZeroModesPreserve L) Gh := by
  intro a i x hx
  constructor
  · refine tensorDeg_preserve_sum (matterDeg L) Gh.deg _
      (mode ((matterSVA L).Y ((matterAction L).toAffineSl2Action.current a)) 0) (ghZero a)
      (fun m g => totalCurrentZero_tmul _ a m g) ((matterDeg_zero_preserve L) hA0 hU0 a)
      (hG0 a) i x hx
  · have hshift : ∀ j, ghDown j = j + ((0, -1), 0) := by
      rintro ⟨⟨j1, j2⟩, j3⟩
      simp only [ghDown, Prod.mk_add_mk, add_zero]
      rfl
    rw [hshift]
    refine tensorDeg_shift_right (matterDeg L) Gh.deg _ (antiZero a) ((0, -1), 0)
      (fun m g => ?_) (fun j y hy => by rw [← hshift]; exact hb0 a j y hy) i x hx
    rw [antighostZero_tmul a ((matter_mem_parity_zero L) m) g]
    simp [koszul, antiZero]


/-! ## Port of `ConcreteGoodLayers` -/


/-! ### Generic: skew flag-preserving operators preserve layers -/

section Generic

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

end Generic

/-! ### The auxiliary factor `U` -/

section Auxiliary

variable (k : ℂ)

theorem uZero_apply (a : Fin 3) (x : (USpace L)) : (uZero L) a x = J L.kU a 0 x :=
  smul_currentState_eq_J L.kU L.uNoncritical a 0 x

/-- **The `U` current zero modes preserve the ordinary PBW layers.** -/
theorem uZeroModesPreserveLayers : (UZeroModesPreserveLayers L) := by
  intro a
  refine layerDeg_preserve (auxiliaryForm L) (auxiliaryFlag L) ((uZero L) a) ?_ ?_
  · intro q m x hx
    refine ⟨?_, ?_⟩
    · rw [uZero_apply]; exact J_zero_mem_ordinaryPiece _ a hx.1
    · have h := (universal L.kU L.uNoncritical).grading_mode _
        (currentState_mem_grading L.kU L.uNoncritical a) x hx.2 0
      have e : (1 : ℤ) + m - 0 - 1 = m := by ring
      rw [e] at h
      exact h
  · intro x y
    rw [uZero_apply, uZero_apply]
    have h := universalForm_current_adj L.uNoncritical a 0 x y
    simpa only [neg_zero] using h

end Auxiliary

/-! ### The boundary factor `A` -/

section Boundary

/-- The universal current zero mode as a screening derivation. -/
abbrev aUnivZero (a : Fin 3) : Module.End ℂ (WakModule L.kA) :=
  Screening.screening (universal L.kA L.aNoncritical) (currentState L.kA a)

theorem aUnivZero_apply (a : Fin 3) (x : WakModule L.kA) :
    (aUnivZero L) a x = J L.kA a 0 x :=
  smul_currentState_eq_J L.kA L.aNoncritical a 0 x

theorem aUnivZero_generator (a : Fin 3) (g : Generator) :
    (aUnivZero L) a (generatorState L.kA L.aNoncritical g) ∈
      correctedAffineRPiece L.kA L.aNoncritical 1 := by
  cases g with
  | current b =>
      have hw : (aUnivZero L) a (generatorState L.kA L.aNoncritical (Generator.current b)) ∈
          (affineSl2VOA_closed L.kA L.aNoncritical).grading 1 := by
        have h := (universal L.kA L.aNoncritical).grading_mode _
          (currentState_mem_grading L.kA L.aNoncritical a) _
          (currentState_mem_grading L.kA L.aNoncritical b) 0
        have e : (1 : ℤ) + 1 - 0 - 1 = 1 := by ring
        rw [e] at h
        exact h
      rw [← correctedAffineRWeightPiece_one_one] at hw
      exact hw.1
  | sugawara =>
      have h := Screening.screening_conformalVector (universal L.kA L.aNoncritical)
        (currentState_mem_grading L.kA L.aNoncritical a)
      change (aUnivZero L) a (universal L.kA L.aNoncritical).conformalVector ∈ _
      rw [h]
      exact Submodule.zero_mem _

theorem generatorState_mem_piece_one (g : Generator) :
    generatorState L.kA L.aNoncritical g ∈ correctedAffineRPiece L.kA L.aNoncritical 1 := by
  cases g with
  | current b => exact currentState_mem_piece_one L.kA L.aNoncritical b
  | sugawara => exact conformalVector_mem_piece_one L.kA L.aNoncritical

theorem aUnivZero_word (a : Fin 3) :
    ∀ w : List (Generator × ℕ), (aUnivZero L) a (correctedWordState L.kA L.aNoncritical w) ∈
      correctedAffineRPiece L.kA L.aNoncritical w.length
  | [] => by
      change Screening.screening _ _ (universal L.kA L.aNoncritical).vacuum ∈ _
      rw [Screening.screening_vacuum]
      exact Submodule.zero_mem _
  | (gr :: rest) => by
      rw [correctedWordState_cons]
      change Screening.screening _ _ ((universal L.kA L.aNoncritical).smul _ _ _) ∈ _
      rw [Screening.screening_leibniz]
      simp only [List.length_cons]
      rw [show rest.length + 1 = 1 + rest.length by omega]
      refine Submodule.add_mem _ ?_ ?_
      · exact mode_piece_mem_piece_add L.kA L.aNoncritical ((aUnivZero_generator L) a gr.1)
          (correctedWordState_mem_piece L.kA L.aNoncritical rest le_rfl) _
      · exact mode_piece_mem_piece_add L.kA L.aNoncritical ((generatorState_mem_piece_one L) gr.1)
          (aUnivZero_word a rest) _

theorem aUnivZero_mem_piece (a : Fin 3) {p : ℕ} {x : WakModule L.kA}
    (hx : x ∈ correctedAffineRPiece L.kA L.aNoncritical p) :
    (aUnivZero L) a x ∈ correctedAffineRPiece L.kA L.aNoncritical p := by
  rw [correctedAffineRPiece] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨w, rfl⟩ := hx
      exact correctedAffineRPiece_mono L.kA L.aNoncritical w.2 ((aUnivZero_word L) a w.1)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

theorem aZero_mkQ (a : Fin 3) (x : WakModule L.kA) :
    (aZero L) a ((QuotVOA.maxGradedIdeal (universal L.kA L.aNoncritical)).mkQ x) =
      (QuotVOA.maxGradedIdeal (universal L.kA L.aNoncritical)).mkQ ((aUnivZero L) a x) :=
  SimpleQuot.maxQuotientVOA_mkQ_smul _ _ _ _

/-- **The `A` current zero modes preserve the corrected layers.** -/
theorem aZeroModesPreserveLayers : (AZeroModesPreserveLayers L) := by
  intro a
  refine layerDeg_preserve (affineForm L) (affineFlag L) ((aZero L) a) ?_ ?_
  · intro q m x hx
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
    rw [aZero_mkQ]
    refine Submodule.mem_map_of_mem ⟨(aUnivZero_mem_piece L) a hy.1, ?_⟩
    have h := (universal L.kA L.aNoncritical).grading_mode _
      (currentState_mem_grading L.kA L.aNoncritical a) y hy.2 0
    have e : (1 : ℤ) + m - 0 - 1 = m := by ring
    rw [e] at h
    exact h
  · intro x y
    obtain ⟨x, rfl⟩ := (QuotVOA.maxGradedIdeal (universal L.kA L.aNoncritical)).mkQ_surjective x
    obtain ⟨y, rfl⟩ := (QuotVOA.maxGradedIdeal (universal L.kA L.aNoncritical)).mkQ_surjective y
    rw [aZero_mkQ, aZero_mkQ]
    change (simpleForm L.kA L.aNoncritical).form _ _ = -(simpleForm L.kA L.aNoncritical).form _ _
    rw [simpleForm_mkQ, simpleForm_mkQ, aUnivZero_apply, aUnivZero_apply]
    have h := universalForm_current_adj L.aNoncritical a 0 x y
    simpa only [neg_zero] using h

end Boundary


/-! ## Port of `ConcreteGoodEndpoint` -/


/-- The `BRSTKahlerGeometry L` of the interpreted inputs. -/
noncomputable abbrev interpretedKahler {PG : SesqForm Sl2GhostSpace} (Gh : GhostRGrading PG)
    (hA : GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag L))
    {BB : InvariantForm BVOA} {RB : RealStructure BVOA} (hB : ConcreteHodge.Unitary BB RB)
    (hG : IsPosOn PG ⊤) (hZ : (ZeroModesPreserve L) Gh) (hD : (RelativeDifferentialGood L) Gh)
    (hK : (InterpretedKahlerAnticomm L) Gh hA hB hG hZ hD) : (BRSTKahlerGeometry L) :=
  concreteKahler ((interpretedGoodGeometry L) Gh hA hB hG hZ hD hK)


/-! ## Port of `ConcreteGoodGenerators` -/


/-! ### Vacua in the interpreted grading -/

/-- **The BRST vacuum has interpreted bidegree `(0, 0)` at weight `0`.** -/
theorem brstVacuum_mem (w : Finset ModeIdx → ℝ) :
    (((ASVA L).vacuum ⊗ₜ[ℂ] BSVA.vacuum) ⊗ₜ[ℂ] (USVA L).vacuum) ⊗ₜ[ℂ] sl2GhostSVA.vacuum ∈
      (brstDeg L) (ghostRGrading w) ((0, 0), 0) := by
  have hA : (ASVA L).vacuum ∈ (aDeg L) ((0, 0), 0) := vacuum_mem_layerDeg (affineForm L)
      (affineFlag L)
  have hB : BSVA.vacuum ∈ bDeg ((0, 0), 0) := vacuum_mem_trivialDeg BVOA
  have hU : (USVA L).vacuum ∈ (uDeg L) ((0, 0), 0) := vacuum_mem_layerDeg (auxiliaryForm L)
      (auxiliaryFlag L)
  have h := tmul_mem_tensorDeg (matterDeg L) (ghostRGrading w).deg
    (tmul_mem_tensorDeg _ _ (tmul_mem_tensorDeg _ _ hA hB) hU) ghostVacuum_mem_ghostDeg
  simpa using h

/-! ### The vacuum generator test -/

section Interpreted

variable (w : Finset ModeIdx → ℝ) (hw : ∀ s, 0 < w s)
  (hA : GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag L))
  {BB : InvariantForm BVOA} {RB : RealStructure BVOA} (hB : ConcreteHodge.Unitary BB RB)

theorem representative_vacuum :
    (((universalWeightRepresentative L) 0 (universalVacuum L) : (relativeWeight L) 0) : (BRSTSpace
        L)) =
      (((ASVA L).vacuum ⊗ₜ[ℂ] BSVA.vacuum) ⊗ₜ[ℂ] (USVA L).vacuum) ⊗ₜ[ℂ] sl2GhostSVA.vacuum := by
  change (cosetToComplex L) ((virasoroToCoset L) (VirModule.vacVec L.c)) = _
  rw [virasoroToCoset_vacuum, cosetToComplex_apply]
  rfl

end Interpreted

/-! ### The ghost zero-mode inputs -/

/-- `ZeroModesPreserve L` for the concrete ghost grading, from the two ghost statements (the matter
statements are proved). -/
theorem zeroModesPreserve_concrete (w : Finset ModeIdx → ℝ) (hG0 : GhostCurrentZeroPreserve)
    (hb0 : AntighostZeroShift) : (ZeroModesPreserve L) (ghostRGrading w) :=
  (zeroModesPreserve_of_factors L) (ghostRGrading w) (aZeroModesPreserveLayers L)
    (uZeroModesPreserveLayers L) hG0 hb0

/-! ### The concrete endpoint -/


end

end VOA.TwoSeries
