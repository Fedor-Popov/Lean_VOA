/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.TwoSeriesAssembly
import VOA.Examples.ConcreteGoodInterpreted

/-!
# The product form and the interpreted grading on the level-`L` relative complexes

Level-generic port of the level-specific parts of `ConcreteHodgeAssembly` and
`ConcreteGoodInterpreted`.  Every level-independent declaration of those files (`brstForm`'s
positivity machinery, `GhostRGrading`, `zeroGhost`, `ghDown`, the `GoodHalf`/`GoodGeometry`
API, …) is reused directly; only the declarations mentioning the actual factors are restated with
an explicit `L : CosetLevels`.

* `matterGhostForm L hA BB RB PG`, `weakGU_matterGhostForm`, `assemblyForm L`, `assemblyForm_pos`;
* `ConcreteGoodGeometry L n P`, `concreteKahler L I : BRSTKahlerGeometry L`,
  `concreteKahler_weakGU`;
* the interpreted grading `brstDeg L Gh`, `ZeroModesPreserve L Gh`,
  `RelativeDifferentialGood L Gh`, `interpretedHalf`, `InterpretedKahlerAnticomm`,
  `interpretedGoodGeometry`.
-/

namespace VOA.TwoSeries

open Sl2SemiInfinite AffineSl2GeneralRigidity AffineSl2BelowCritical
open VOA.Sl2CosetConcrete VOA.ConcreteHodge VOA.Sl2Coset AffineVOA AffineVOA.Inst
open VOA.GradedUnitaryCohomology VOA.LeeYangCosetTransfer VOA.VertexOperatorAlgebra
open scoped TensorProduct

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

variable (L : CosetLevels)

/-! ### Small missing pieces of the level-`L` base -/

theorem relativeDifferential_sq (n : ℤ) :
    (relativeDifferential L n).comp (relativeDifferential L n) = 0 := by
  ext x
  exact (brstComplex L).Q_apply_Q x

theorem brstComplex_Q_apply (x : BRSTSpace L) :
    (brstComplex L).Q x = semiInfiniteQ (matterAction L).toAffineSl2Action x := rfl

theorem cosetToComplex_mode (x y : CosetSpace L) (n : ℤ) :
    cosetToComplex L (cosetMode (diagonalAction L).toAffineSl2Action
        (diagonalAction L).translation x n y) =
      mode ((brstSVA L).Y (cosetToComplex L x)) n (cosetToComplex L y) :=
  auxiliaryCosetToComplex_mode (diagonalAction L) (uAction L) (abParityCompatible L)
    (uParityCompatible L) (abuTensorGrading L) L.sum x y n

@[simp] theorem cosetVOA_mode (x y : CosetSpace L) (n : ℤ) :
    (cosetVOA L).smul x n y =
      cosetMode (diagonalAction L).toAffineSl2Action (diagonalAction L).translation x n y := rfl

theorem cosetOmega_even : cosetOmega L ∈ (abSVA L).parity 0 := by
  rw [cosetOmega, ambientConformal_eq_tensorSugawara]
  exact tensorCosetConformalState_even (aAction L).toAffineSl2Action bAction.toAffineSl2Action
    (kAct_noncritical L) (by norm_num) L.diagNoncritical
    (aParityCompatible L) bParityCompatible (abTensorGrading L)

theorem affineForm_normalized : (affineForm L).Normalized :=
  simpleForm_normalized L.kA L.aNoncritical

theorem affineFlag_modeCompatible : (affineFlag L).ModeCompatible :=
  CorrectedR.correctedAffineRQuotientFlag_modeCompatible L.kA L.aNoncritical
    (QuotVOA.maxGradedIdeal (universal L.kA L.aNoncritical))
    (QuotVOA.maxGradedIdeal_isIdeal _)
    (QuotVOA.maxGradedIdeal_isGradedIdeal _)

theorem affineCurrent_mem_flag_one (a : Fin 3) :
    simpleCurrent L.kA L.aNoncritical a ∈ (affineFlag L).piece 1 1 := by
  apply Submodule.mem_map.mpr
  refine ⟨currentState L.kA a, ?_, rfl⟩
  exact ⟨CorrectedR.currentState_mem_piece_one L.kA L.aNoncritical a,
    currentState_mem_grading L.kA L.aNoncritical a⟩

theorem affineConformal_mem_flag_one : (AVOA L).conformalVector ∈ (affineFlag L).piece 1 2 := by
  apply Submodule.mem_map.mpr
  refine ⟨(universal L.kA L.aNoncritical).conformalVector, ?_, rfl⟩
  exact ⟨CorrectedR.conformalVector_mem_piece_one L.kA L.aNoncritical,
    (universal L.kA L.aNoncritical).conformalVector_mem_grading_two⟩

/-- Weak graded unitarity of a level-`L` Kähler geometry, from the two factor hypotheses. -/
def WeakGUTensorPositivity (S : BRSTKahlerGeometry L) : Prop :=
  GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag L) →
  GradedUnitary (auxiliaryForm L) (auxiliaryRealStructure L) (auxiliaryFlag L) →
  ∀ n, IsPosOn (S.geometry n).P ⊤

/-! ### The product form -/

/-- The product of four forms on `((A ⊗ B) ⊗ U) ⊗ ghosts`. -/
def brstForm (PA : SesqForm (ASpace L)) (PB : SesqForm BSpace) (PU : SesqForm (USpace L))
    (PG : SesqForm Sl2GhostSpace) : SesqForm (MatterSpace L ⊗[ℂ] Sl2GhostSpace) :=
  ((PA.tensor PB).tensor PU).tensor PG

theorem isPosOn_brstForm (PA : SesqForm (ASpace L)) (PB : SesqForm BSpace)
    (PU : SesqForm (USpace L))
    (PG : SesqForm Sl2GhostSpace) (hA : IsPosOn PA ⊤) (hB : IsPosOn PB ⊤) (hU : IsPosOn PU ⊤)
    (hG : IsPosOn PG ⊤) : IsPosOn (brstForm L PA PB PU PG) ⊤ :=
  SesqForm.isPosOn_tensor _ _ (SesqForm.isPosOn_tensor _ _
    (SesqForm.isPosOn_tensor _ _ hA hB) hU) hG

theorem affineGramRefl : GramRefl (affineForm L) := gramRefl_simpleForm L.kA L.aNoncritical

theorem auxiliaryGramRefl : GramRefl (auxiliaryForm L) :=
  gramRefl_universalForm L.kU L.uNoncritical

/-- **The modified product form** of the level-`L` matter-ghost system. -/
def matterGhostForm (hA : GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag L))
    (BB : InvariantForm BVOA) (RB : RealStructure BVOA) (PG : SesqForm Sl2GhostSpace) :
    SesqForm (MatterSpace L ⊗[ℂ] Sl2GhostSpace) :=
  brstForm L (carrierForm (affineForm L) (affineRealStructure L) (affineFlag L) hA
      (affineGramRefl L))
    (unitaryCarrierForm BB RB)
    (carrierForm (auxiliaryForm L) (auxiliaryRealStructure L) (auxiliaryFlag L)
      (auxiliaryGradedUnitary L) (auxiliaryGramRefl L))
    PG

/-- **Weak graded unitarity of `A ⊗ B ⊗ U ⊗ ghosts`** at level `L`. -/
theorem weakGU_matterGhostForm
    (hA : GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag L))
    {BB : InvariantForm BVOA}
    {RB : RealStructure BVOA} (hB : ConcreteHodge.Unitary BB RB) {PG : SesqForm Sl2GhostSpace}
    (hG : IsPosOn PG ⊤) : IsPosOn (matterGhostForm L hA BB RB PG) ⊤ :=
  isPosOn_brstForm L _ _ _ _ (isPosOn_carrierForm _ _ _ hA (affineGramRefl L))
    (isPosOn_unitaryCarrierForm BB RB hB)
    (isPosOn_carrierForm _ _ _ (auxiliaryGradedUnitary L) (auxiliaryGramRefl L)) hG

open Classical in
/-- The form on `relativeWeight L n`: the restricted product form under `hA`, `0` otherwise. -/
def assemblyForm (BB : InvariantForm BVOA) (RB : RealStructure BVOA)
    (PG : SesqForm Sl2GhostSpace) (n : ℤ) : SesqForm (relativeWeight L n) :=
  if hA : GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag L) then
    (matterGhostForm L hA BB RB PG).restrict (relativeWeight L n)
  else SesqForm.zero _

theorem assemblyForm_eq (hA : GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag L))
    (BB : InvariantForm BVOA) (RB : RealStructure BVOA) (PG : SesqForm Sl2GhostSpace) (n : ℤ) :
    assemblyForm L BB RB PG n =
      (matterGhostForm L hA BB RB PG).restrict (relativeWeight L n) := by
  classical
  unfold assemblyForm
  rw [dif_pos hA]

theorem assemblyForm_pos
    (hA : GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag L))
    {BB : InvariantForm BVOA}
    {RB : RealStructure BVOA} (hB : ConcreteHodge.Unitary BB RB) {PG : SesqForm Sl2GhostSpace}
    (hG : IsPosOn PG ⊤) (n : ℤ) : IsPosOn (assemblyForm L BB RB PG n) ⊤ := by
  rw [assemblyForm_eq L hA]
  exact SesqForm.isPosOn_restrict _ (weakGU_matterGhostForm L hA hB hG) _

set_option maxHeartbeats 4000000 in
/-- A good geometry on `relativeWeight L n` with the given form, the actual differential and the
actual ghost number. -/
structure ConcreteGoodGeometry (n : ℤ) (P : SesqForm (relativeWeight L n)) where
  geom : GoodGeometry (relativeWeight L n)
  P_eq : geom.P = P
  D_eq : geom.D = relativeDifferential L n
  ghost : ∀ a, geom.deg a ≤ ((brstComplex L).ghost a.2).comap (relativeWeight L n).subtype

section Interface

variable {L}
variable {BB : InvariantForm BVOA} {RB : RealStructure BVOA} {PG : SesqForm Sl2GhostSpace}

/-- The Kähler geometry of `BRSTHodgeInputs`, from a good geometry at every weight. -/
def concreteKahler (I : ∀ n, ConcreteGoodGeometry L n (assemblyForm L BB RB PG n)) :
    BRSTKahlerGeometry L where
  geometry n := (I n).geom.toKahlerGeometry
  differential n := (I n).geom.Qm_add_Sm.trans (I n).D_eq
  ghost n := (I n).ghost

theorem concreteKahler_weakGU (hB : ConcreteHodge.Unitary BB RB) (hG : IsPosOn PG ⊤)
    (I : ∀ n, ConcreteGoodGeometry L n (assemblyForm L BB RB PG n)) :
    WeakGUTensorPositivity L (concreteKahler I) := by
  intro hA _ n
  change IsPosOn (I n).geom.P ⊤
  rw [(I n).P_eq]
  exact assemblyForm_pos L hA hB hG n

/-- The good complex at weight `n` once positivity is known. -/
def concreteGood (I : ∀ n, ConcreteGoodGeometry L n (assemblyForm L BB RB PG n)) (n : ℤ)
    (hp : IsPosOn ((concreteKahler I).geometry n).P ⊤) : GoodComplex (relativeWeight L n) :=
  { (I n).geom with pos := hp }

theorem concreteKahler_model (I : ∀ n, ConcreteGoodGeometry L n (assemblyForm L BB RB PG n))
    (n : ℤ) (hp : IsPosOn ((concreteKahler I).geometry n).P ⊤) :
    (concreteKahler I).model n hp = (concreteGood I n hp).toKahler := rfl

end Interface

/-! ### The interpreted grading -/

/-- `A`: the orthogonal layers of the corrected flag. -/
def aDeg : (ℤ × ℤ) × ℂ → Submodule ℂ (ASpace L) := layerDeg (affineForm L) (affineFlag L)

/-- `U`: the orthogonal layers of the ordinary PBW flag. -/
def uDeg : (ℤ × ℤ) × ℂ → Submodule ℂ (USpace L) := layerDeg (auxiliaryForm L) (auxiliaryFlag L)

/-- The matter grading on `(A ⊗ B) ⊗ U`. -/
def matterDeg : (ℤ × ℤ) × ℂ → Submodule ℂ (MatterSpace L) :=
  tensorDeg (tensorDeg (aDeg L) bDeg) (uDeg L)

/-- The interpreted `((2R, gh), weight)` grading of the level-`L` BRST space. -/
def brstDeg {PG : SesqForm Sl2GhostSpace} (Gh : GhostRGrading PG) :
    (ℤ × ℤ) × ℂ → Submodule ℂ (BRSTSpace L) :=
  tensorDeg (matterDeg L) Gh.deg

section Grading

variable {PG : SesqForm Sl2GhostSpace} (Gh : GhostRGrading PG)

theorem matterDeg_span
    (hA : GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag L)) :
    iSup (matterDeg L) = ⊤ :=
  tensorDeg_span _ _ (tensorDeg_span _ _
    (layerDeg_span (affineForm L) (affineRealStructure L) (affineFlag L) hA (affineGramRefl L))
    trivialDeg_span) (layerDeg_span _ _ _ (auxiliaryGradedUnitary L) (auxiliaryGramRefl L))

theorem brstDeg_span (hA : GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag L)) :
    iSup (brstDeg L Gh) = ⊤ :=
  tensorDeg_span _ _ (matterDeg_span L hA) Gh.span

theorem brstDeg_orth (hA : GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag L))
    (BB : InvariantForm BVOA) (RB : RealStructure BVOA) :
    ∀ a b, a ≠ b → ∀ x ∈ brstDeg L Gh a, ∀ y ∈ brstDeg L Gh b,
      matterGhostForm L hA BB RB PG x y = 0 :=
  tensorDeg_orth _ _ _ _
    (tensorDeg_orth _ _ _ _
      (tensorDeg_orth _ _ _ _
        (layerDeg_orth (affineForm L) (affineRealStructure L) (affineFlag L) hA
          (affineGramRefl L))
        (trivialDeg_orth _ (unitaryCarrierForm_weight_orth BB RB)))
      (layerDeg_orth _ _ _ (auxiliaryGradedUnitary L) (auxiliaryGramRefl L)))
    Gh.orth

theorem matterDeg_le_weight (i : (ℤ × ℤ) × ℂ) :
    matterDeg L i ≤ (matterSVA L).grading (wtIndex i) := by
  refine tensorDeg_le wtIndex _ _ (abSVA L).grading (USVA L).grading (matterSVA L).grading
    ?_ ?_ ?_ i
  · intro k k' x y hx hy
    exact TensorVA.tmul_mem_tenGrading (abSVA L) (USVA L) hx (by rwa [add_sub_cancel_left])
  · intro j
    refine tensorDeg_le wtIndex _ _ (ASVA L).grading BSVA.grading (abSVA L).grading ?_ ?_ ?_ j
    · intro k k' x y hx hy
      exact TensorVA.tmul_mem_tenGrading (ASVA L) BSVA hx (by rwa [add_sub_cancel_left])
    · intro l; exact layerDeg_le_gradingC _ _ l
    · intro l; exact trivialDeg_le_gradingC l
  · intro j; exact layerDeg_le_gradingC _ _ j

theorem brstDeg_le_weight (i : (ℤ × ℤ) × ℂ) :
    brstDeg L Gh i ≤ (brstSVA L).grading (wtIndex i) := by
  refine tensorDeg_le wtIndex _ _ (matterSVA L).grading sl2GhostSVA.grading (brstSVA L).grading
    ?_ (matterDeg_le_weight L) Gh.le_weight i
  intro k k' x y hx hy
  exact TensorVA.tmul_mem_tenGrading (matterSVA L) sl2GhostSVA hx (by rwa [add_sub_cancel_left])

theorem matterDeg_le_zeroGhost (i : (ℤ × ℤ) × ℂ) :
    matterDeg L i ≤ zeroGhost (MatterSpace L) (ghIndex i) :=
  tensorDeg_le ghIndex _ _ _ _ _ (tmul_mem_zeroGhost)
    (tensorDeg_le ghIndex _ _ _ _ _ (tmul_mem_zeroGhost)
      (layerDeg_le_zeroGhost _ _) trivialDeg_le_zeroGhost)
    (layerDeg_le_zeroGhost _ _) i

theorem brstDeg_le_ghost (i : (ℤ × ℤ) × ℂ) :
    brstDeg L Gh i ≤ (brstComplex L).ghost (ghIndex i) := by
  refine tensorDeg_le ghIndex _ _ (zeroGhost (MatterSpace L)) sl2GhostGrading
    (matterGhostGrading (MatterSpace L)) ?_ (matterDeg_le_zeroGhost L) Gh.le_ghost i
  intro k k' x y hx hy
  by_cases hk : k = 0
  · subst hk
    rw [zero_add]
    exact tmul_mem_matterGhostGrading (MatterSpace L) x hy
  · rw [eq_zero_of_mem_zeroGhost hk hx, TensorProduct.zero_tmul]
    exact Submodule.zero_mem _

theorem brstDeg_isInternal
    (hA : GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag L))
    {BB : InvariantForm BVOA} {RB : RealStructure BVOA} (hB : ConcreteHodge.Unitary BB RB)
    (hG : IsPosOn PG ⊤) : DirectSum.IsInternal (brstDeg L Gh) := by
  classical
  have hpos := weakGU_matterGhostForm L hA hB hG
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top _ (brstDeg_span L Gh hA)
  rw [iSupIndep_def]
  intro a
  rw [Submodule.disjoint_def]
  intro x hx hx'
  apply eq_zero_of_sesq_self_eq_zero _ hpos
  refine sesq_iSup_right' _ (fun b => ⨆ (_ : b ≠ a), brstDeg L Gh b) (fun b y hy => ?_) x hx'
  by_cases hba : b = a
  · subst hba
    simp only [ne_eq, not_true_eq_false, iSup_false, Submodule.mem_bot] at hy
    rw [hy, SesqForm.zero_right]
  · beta_reduce at hy
    rw [iSup_pos (show b ≠ a from hba)] at hy
    exact brstDeg_orth L Gh hA BB RB a b (Ne.symm hba) x hx y hy

end Grading

/-- The relative constraints are `R`-homogeneous of degree `0` (level `L`). -/
def ZeroModesPreserve {PG : SesqForm Sl2GhostSpace} (Gh : GhostRGrading PG) : Prop :=
  ∀ (a : Fin 3) (i : (ℤ × ℤ) × ℂ), ∀ x ∈ brstDeg L Gh i,
    totalCurrentZero (matterAction L).toAffineSl2Action a x ∈ brstDeg L Gh i ∧
      antighostZero (matterSVA L) a x ∈ brstDeg L Gh (ghDown i)

/-- Goodness of the actual level-`L` differential for the interpreted grading. -/
def RelativeDifferentialGood {PG : SesqForm Sl2GhostSpace} (Gh : GhostRGrading PG) : Prop :=
  ∀ (n j g : ℤ) (x : BRSTSpace L), x ∈ relativeWeight L n →
    x ∈ brstDeg L Gh ((j, g), (n : ℂ)) →
    (brstComplex L).Q x ∈
      brstDeg L Gh ((j + 1, g + 1), (n : ℂ)) ⊔ brstDeg L Gh ((j - 1, g + 1), (n : ℂ))

section Relative

variable {PG : SesqForm Sl2GhostSpace} (Gh : GhostRGrading PG)
  {BB : InvariantForm BVOA} {RB : RealStructure BVOA}

theorem relativeWeight_stable
    (hA : GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag L))
    (hB : ConcreteHodge.Unitary BB RB) (hG : IsPosOn PG ⊤) (hZ : ZeroModesPreserve L Gh) (n : ℤ) :
    ProjStable (brstDeg_isInternal L Gh hA hB hG) (relativeWeight L n) := by
  classical
  have hI := brstDeg_isInternal L Gh hA hB hG
  refine projStable_inf hI (projStable_inf hI ?_ ?_) ?_
  · exact projStable_iInf hI fun a => projStable_ker hI _ fun i x hx => (hZ a i x hx).1
  · exact projStable_iInf hI fun a =>
      projStable_ker_shift hI _ ghDown ghDown_injective fun i x hx => (hZ a i x hx).2
  · exact projStable_weight hI (brstSVA L).isInternal wtIndex (brstDeg_le_weight L Gh) (n : ℂ)

/-- The interpreted grading at weight `n`, as subspaces of `relativeWeight L n`. -/
def relDeg (n : ℤ) (a : ℤ × ℤ) : Submodule ℂ (relativeWeight L n) :=
  (brstDeg L Gh (a, (n : ℂ))).comap (relativeWeight L n).subtype

theorem relDeg_span (hA : GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag L))
    (hB : ConcreteHodge.Unitary BB RB) (hG : IsPosOn PG ⊤) (hZ : ZeroModesPreserve L Gh) (n : ℤ) :
    iSup (relDeg L Gh n) = ⊤ := by
  classical
  have hI := brstDeg_isInternal L Gh hA hB hG
  have htop := iSup_comap_eq_top_of_stable hI (relativeWeight_stable L Gh hA hB hG hZ n)
  rw [eq_top_iff, ← htop]
  refine iSup_le fun i => ?_
  by_cases hi : i.2 = (n : ℂ)
  · obtain ⟨a, h⟩ := i
    simp only at hi
    subst hi
    exact le_iSup (relDeg L Gh n) a
  · intro x hx
    have h1 : (x : BRSTSpace L) ∈ (brstSVA L).grading i.2 := brstDeg_le_weight L Gh i hx
    have h2 : (x : BRSTSpace L) ∈ (brstSVA L).grading (n : ℂ) := x.2.2
    have hd := (brstSVA L).isInternal.submodule_iSupIndep.pairwiseDisjoint hi
    have : (x : BRSTSpace L) = 0 := (Submodule.disjoint_def.mp hd) _ h1 h2
    have hx0 : x = 0 := Subtype.ext this
    rw [hx0]; exact Submodule.zero_mem _

theorem relDeg_orth (hA : GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag L))
    (n : ℤ) :
    ∀ a b, a ≠ b → ∀ x ∈ relDeg L Gh n a, ∀ y ∈ relDeg L Gh n b,
      assemblyForm L BB RB PG n x y = 0 := by
  intro a b hab x hx y hy
  rw [assemblyForm_eq L hA]
  exact brstDeg_orth L Gh hA BB RB (a, (n : ℂ)) (b, (n : ℂ))
    (fun h => hab (congrArg Prod.fst h)) x hx y hy

theorem relDeg_good (hA : GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag L))
    (hB : ConcreteHodge.Unitary BB RB) (hG : IsPosOn PG ⊤) (hZ : ZeroModesPreserve L Gh)
    (hD : RelativeDifferentialGood L Gh) (n : ℤ) :
    ∀ a, ∀ x ∈ relDeg L Gh n a,
      relativeDifferential L n x ∈ relDeg L Gh n (a + shQm) ⊔ relDeg L Gh n (a + shSm) := by
  rintro ⟨j, g⟩ x hx
  have hI := brstDeg_isInternal L Gh hA hB hG
  have hy := hD n j g x x.2 hx
  have hne : (((j, g) + shQm, (n : ℂ)) : (ℤ × ℤ) × ℂ) ≠ ((j, g) + shSm, (n : ℂ)) := by
    intro h
    have := congrArg (fun z => z.1.1) h
    simp only [shQm, shSm, Prod.mk_add_mk] at this
    omega
  have hQ : ((j, g) + shQm : ℤ × ℤ) = (j + 1, g + 1) := rfl
  have hS : ((j, g) + shSm : ℤ × ℤ) = (j - 1, g + 1) :=
    Prod.ext (show j + -1 = j - 1 by omega) rfl
  rw [← hQ, ← hS] at hy
  exact mem_sup_comap_of_stable hI (relativeWeight_stable L Gh hA hB hG hZ n) hne
    (relativeDifferential L n x) hy

/-- The minimal Lemma 3.16 input for the actual level-`L` relative complex at weight `n`. -/
def interpretedHalf (hA : GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag L))
    (hB : ConcreteHodge.Unitary BB RB) (hG : IsPosOn PG ⊤) (hZ : ZeroModesPreserve L Gh)
    (hD : RelativeDifferentialGood L Gh) (n : ℤ) :
    GoodHalf (relativeWeight L n) where
  P := assemblyForm L BB RB PG n
  deg := relDeg L Gh n
  span := relDeg_span L Gh hA hB hG hZ n
  orth := relDeg_orth L Gh hA n
  D := relativeDifferential L n
  D_good := relDeg_good L Gh hA hB hG hZ hD n
  sq_zero := relativeDifferential_sq L n

theorem interpretedHalf_pos
    (hA : GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag L))
    (hB : ConcreteHodge.Unitary BB RB) (hG : IsPosOn PG ⊤) (hZ : ZeroModesPreserve L Gh)
    (hD : RelativeDifferentialGood L Gh)
    (n : ℤ) : IsPosOn (interpretedHalf L Gh hA hB hG hZ hD n).P ⊤ :=
  assemblyForm_pos L hA hB hG n

end Relative

/-- The Kähler relation for the derived second differential at every weight (level `L`). -/
def InterpretedKahlerAnticomm {PG : SesqForm Sl2GhostSpace} (Gh : GhostRGrading PG)
    (hA : GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag L))
    {BB : InvariantForm BVOA} {RB : RealStructure BVOA} (hB : ConcreteHodge.Unitary BB RB)
    (hG : IsPosOn PG ⊤) (hZ : ZeroModesPreserve L Gh) (hD : RelativeDifferentialGood L Gh) :
    Prop :=
  ∀ n, (interpretedHalf L Gh hA hB hG hZ hD n).KahlerAnticomm
    (interpretedHalf_pos L Gh hA hB hG hZ hD n)

/-- The level-`L` Lemma 3.16 geometry from the interpreted inputs. -/
def interpretedGoodGeometry {PG : SesqForm Sl2GhostSpace} (Gh : GhostRGrading PG)
    (hA : GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag L))
    {BB : InvariantForm BVOA} {RB : RealStructure BVOA} (hB : ConcreteHodge.Unitary BB RB)
    (hG : IsPosOn PG ⊤) (hZ : ZeroModesPreserve L Gh) (hD : RelativeDifferentialGood L Gh)
    (hK : InterpretedKahlerAnticomm L Gh hA hB hG hZ hD) (n : ℤ) :
    ConcreteGoodGeometry L n (assemblyForm L BB RB PG n) where
  geom := (interpretedHalf L Gh hA hB hG hZ hD n).toGoodGeometry
    (interpretedHalf_pos L Gh hA hB hG hZ hD n) (hK n)
  P_eq := rfl
  D_eq := rfl
  ghost := fun a _ hx => brstDeg_le_ghost L Gh (a, (n : ℂ)) hx

theorem interpretedGoodGeometry_deg {PG : SesqForm Sl2GhostSpace} (Gh : GhostRGrading PG)
    (hA : GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag L))
    {BB : InvariantForm BVOA} {RB : RealStructure BVOA} (hB : ConcreteHodge.Unitary BB RB)
    (hG : IsPosOn PG ⊤) (hZ : ZeroModesPreserve L Gh) (hD : RelativeDifferentialGood L Gh)
    (hK : InterpretedKahlerAnticomm L Gh hA hB hG hZ hD) (n : ℤ) (a : ℤ × ℤ) :
    (interpretedGoodGeometry L Gh hA hB hG hZ hD hK n).geom.deg a =
      (brstDeg L Gh (a, (n : ℂ))).comap (relativeWeight L n).subtype := rfl

end

end VOA.TwoSeries
