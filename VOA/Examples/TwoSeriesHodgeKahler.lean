/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.TwoSeriesHodgeGoodness
import VOA.Examples.BRSTKahlerPackage

/-!
# Level-generic port of the level-specific parts of `BRSTKahler*`

The Kähler geometry `sp2Kahler L …` on the actual level-`L` relative complexes, the generator
tests for the standard ghost grading, and the `GUData` `sp2GUData0 L …`.  Level-independent
declarations are reused from `BRSTKahlerInterpreted`, `BRSTKahlerGhost`, `BRSTKahlerConj`.
-/

namespace VOA.TwoSeries

open VOA.ConcreteHodge Sl2CosetConcrete Sl2SemiInfinite AffineSl2GeneralRigidity
open AffineSl2BelowCritical VOA.GradedUnitaryCohomology VOA.LeeYangCosetTransfer
open VOA.VertexOperatorAlgebra VOA.LeeYangTransferAssembly LeeYangShortcut VirModule LeeYang
open VirGradedUnitarity VOA.SympFerm VOA.Ghost
open scoped TensorProduct

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

universe u v w

variable (L : CosetLevels)

/-! ## Port of `BRSTKahlerInterpreted` -/


section Interpreted

variable {PG : SesqForm Sl2GhostSpace} (Gh : GhostRGrading PG)
  (hA : GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag L))
  {BB : InvariantForm BVOA} {RB : RealStructure BVOA} (hB : ConcreteHodge.Unitary BB RB)
  (hG : IsPosOn PG ⊤) (hZ : (ZeroModesPreserve L) Gh) (hD : (RelativeDifferentialGood L) Gh)

/-- **OPEN input: Beem–Garner Lemma 3.16 for the `sp(2)` image, on the actual relative complex.**
At every weight `n`: `Λ` on `relativeWeight L n` with `Λ (relDeg L (j, g)) ⊆ relDeg L (j, g -
    2)` and,
whenever `[Λ, 𝐐⁻] y = u + v` (`y` of bidegree `(j, g)`, `u`, `v` of bidegrees `(j ± 1, g - 1)`),
`assemblyForm L (𝐐⁻ x) y = assemblyForm L x (v - u)`. -/
abbrev InterpretedSp2 : Type :=
  ∀ n : ℤ, ((interpretedHalf L) Gh hA hB hG hZ hD n).Sp2Adjoint

/-- **The Kähler relation of the actual relative complex from the `sp(2)` adjoint relation.** -/
theorem interpretedKahlerAnticomm_of_sp2 (S : (InterpretedSp2 L) Gh hA hB hG hZ hD) :
    (InterpretedKahlerAnticomm L) Gh hA hB hG hZ hD :=
  fun n => (S n).kahlerAnticomm ((interpretedHalf_pos L) Gh hA hB hG hZ hD n)

/-- The derived second differential of the actual complex is the `sp(2)` image `[Λ, 𝐐⁻]`. -/
theorem interpretedDerived_eq (S : (InterpretedSp2 L) Gh hA hB hG hZ hD) (n : ℤ) :
    ((interpretedHalf L) Gh hA hB hG hZ hD n).derivedDp ((interpretedHalf_pos L) Gh hA hB hG hZ hD
        n) =
      (S n).E :=
  (S n).derivedDp_eq ((interpretedHalf_pos L) Gh hA hB hG hZ hD n)

end Interpreted

/-! ### The reduced conjugation input -/

section Endpoint

variable {PG : SesqForm Sl2GhostSpace} (Gh : GhostRGrading PG)
  (hA : GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag L))
  {BB : InvariantForm BVOA} {RB : RealStructure BVOA} (hB : ConcreteHodge.Unitary BB RB)
  (hG : IsPosOn PG ⊤) (hZ : (ZeroModesPreserve L) Gh) (hD : (RelativeDifferentialGood L) Gh)

/-- The second differential of the interpreted good complex is the `sp(2)` image. -/
theorem concreteGood_Dp_eq (S : (InterpretedSp2 L) Gh hA hB hG hZ hD) (n : ℤ) hp :
    (concreteGood ((interpretedGoodGeometry L) Gh hA hB hG hZ hD
      ((interpretedKahlerAnticomm_of_sp2 L) Gh hA hB hG hZ hD S)) n hp).Dp = (S n).E :=
  (interpretedDerived_eq L) Gh hA hB hG hZ hD S n

end Endpoint

open LeeYangShortcut VirGradedUnitarity LeeYang in


/-! ## Port of `BRSTKahlerGhost` -/


/-! ### The standard ghost grading -/

section Std

variable {PG : SesqForm Sl2GhostSpace} (Gh : GhostRGrading PG)

variable {Gh}

theorem brstDeg_std (hs : Gh.IsStd) : (brstDeg L) Gh = (brstDeg L) (ghostRGrading unitWeight) := by
  unfold brstDeg; rw [hs]; rfl

/-- The zero-mode input for every standard ghost grading. -/
theorem zeroModesPreserve_std (hs : Gh.IsStd) : (ZeroModesPreserve L) Gh := by
  unfold ZeroModesPreserve; rw [(brstDeg_std L) hs]; exact (hZproved L) unitWeight

/-- Goodness of the actual differential for every standard ghost grading. -/
theorem relativeDifferentialGood_std (hA : GradedUnitary (affineForm L) (affineRealStructure L)
    (affineFlag L))
    {BB : InvariantForm BVOA} {RB : RealStructure BVOA} (hB : ConcreteHodge.Unitary BB RB) (hs :
        Gh.IsStd) :
    (RelativeDifferentialGood L) Gh := by
  unfold RelativeDifferentialGood; rw [(brstDeg_std L) hs]
  exact (relativeDifferentialGood_of_affine L) hA hB unitWeight unitWeight_pos

theorem brstDeg_nonnegR_std (hs : Gh.IsStd) : NonnegR ((brstDeg L) Gh) := by
  rw [(brstDeg_std L) hs]; exact (brstDeg_nonnegR L) unitWeight

theorem brstVacuum_mem_std (hs : Gh.IsStd) :
    (((ASVA L).vacuum ⊗ₜ[ℂ] BSVA.vacuum) ⊗ₜ[ℂ] (USVA L).vacuum) ⊗ₜ[ℂ] sl2GhostSVA.vacuum ∈
      (brstDeg L) Gh ((0, 0), 0) := by
  rw [(brstDeg_std L) hs]; exact (brstVacuum_mem L) unitWeight

theorem creation_shift_std (hs : Gh.IsStd)
    (hA : GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag L)) (p : ℕ) (j : ℤ)
    {v : (BRSTSpace L)} (hv : v ∈ ⨆ (k : (ℤ × ℤ) × ℂ) (_ : RowPred p k), (brstDeg L) Gh k) :
    (brstSVA L).Y (omegaB L) j v ∈ ⨆ (k : (ℤ × ℤ) × ℂ) (_ : RowPred (p + 1) k), (brstDeg L) Gh k :=
        by
  rw [(brstDeg_std L) hs] at hv ⊢
  exact (creation_shift L) unitWeight hA p j hv

end Std

/-! ### The generator tests for a standard ghost grading -/

section Generators

variable {PG : SesqForm Sl2GhostSpace} (Gh : GhostRGrading PG)
  (hA : GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag L))
  {BB : InvariantForm BVOA} {RB : RealStructure BVOA} (hB : ConcreteHodge.Unitary BB RB)
  (hG : IsPosOn PG ⊤) (hZ : (ZeroModesPreserve L) Gh) (hD : (RelativeDifferentialGood L) Gh)
  (hK : (InterpretedKahlerAnticomm L) Gh hA hB hG hZ hD)

theorem degOn_to_brst_std (n : ℤ)
    (hp : IsPosOn (((interpretedKahler L) Gh hA hB hG hZ hD hK).geometry n).P ⊤)
    (p : ℕ) (c : (relativeWeight L) n)
    (hc : c ∈ (((interpretedKahler L) Gh hA hB hG hZ hD hK).model n hp).degOn
      (KahlerComplex.rowSet (Finset.Icc 0 (2 * (p : ℤ))) 0)) :
    (c : (BRSTSpace L)) ∈ ⨆ (k : (ℤ × ℤ) × ℂ) (_ : RowPred p k), (brstDeg L) Gh k := by
  refine Submodule.iSup_induction _ (motive := fun c : (relativeWeight L) n =>
    (c : (BRSTSpace L)) ∈ ⨆ (k : (ℤ × ℤ) × ℂ) (_ : RowPred p k), (brstDeg L) Gh k)
    hc ?_ (by simp) (fun x y hx hy => by
      beta_reduce at hx hy ⊢; rw [Submodule.coe_add]; exact Submodule.add_mem _ hx hy)
  rintro ⟨a, ha⟩ y hy
  have hy' : (y : (BRSTSpace L)) ∈ (brstDeg L) Gh (a, (n : ℂ)) := hy
  obtain ⟨ha1, ha2⟩ := ha
  exact Submodule.mem_iSup_of_mem (a, (n : ℂ))
    (Submodule.mem_iSup_of_mem ⟨(Finset.mem_Icc.mp ha1).2, ha2⟩ hy')

theorem brst_to_degOn_std (hs : Gh.IsStd) (n : ℤ)
    (hp : IsPosOn (((interpretedKahler L) Gh hA hB hG hZ hD hK).geometry n).P ⊤)
    (p : ℕ) (v : (relativeWeight L) n)
    (hv : (v : (BRSTSpace L)) ∈ ⨆ (k : (ℤ × ℤ) × ℂ) (_ : RowPred p k), (brstDeg L) Gh k) :
    v ∈ (((interpretedKahler L) Gh hA hB hG hZ hD hK).model n hp).degOn
      (KahlerComplex.rowSet (Finset.Icc 0 (2 * (p : ℤ))) 0) := by
  classical
  have hI := (brstDeg_isInternal L) Gh hA hB hG
  have hstab := (relativeWeight_stable L) Gh hA hB hG hZ n
  have hzero := (mem_iSup_pred_iff hI _ _).mp hv
  obtain ⟨s, hs'⟩ := sum_iproj hI (v : (BRSTSpace L))
  have hv' : v = ∑ k ∈ s, (⟨iproj hI k v, hstab k v v.2⟩ : (relativeWeight L) n) := by
    apply Subtype.ext; rw [Submodule.coe_sum]; exact hs'.symm
  rw [hv']
  refine Submodule.sum_mem _ fun k _ => ?_
  by_cases hk : RowPred p k ∧ k.2 = (n : ℂ) ∧ 0 ≤ k.1.1
  · obtain ⟨⟨hk1, hk2⟩, hk3, hk4⟩ := hk
    refine KahlerComplex.deg_le_degOn _ (a := k.1)
      (show k.1 ∈ KahlerComplex.rowSet (Finset.Icc 0 (2 * (p : ℤ))) 0 from
        ⟨Finset.mem_Icc.mpr ⟨hk4, hk1⟩, hk2⟩) ?_
    change iproj hI k v ∈ (brstDeg L) Gh (k.1, (n : ℂ))
    rw [← hk3]
    exact iproj_mem hI k _
  · have h0 : iproj hI k (v : (BRSTSpace L)) = 0 := by
      by_cases h1 : RowPred p k
      · by_cases h2 : k.2 = (n : ℂ)
        · have h3 : k.1.1 < 0 := by
            by_contra h3; exact hk ⟨h1, h2, not_lt.mp h3⟩
          have := iproj_mem hI k (v : (BRSTSpace L))
          rwa [(brstDeg_nonnegR_std L) hs k h3, Submodule.mem_bot] at this
        · exact iproj_eq_zero_of_weight hI (brstSVA L).isInternal wtIndex
            ((brstDeg_le_weight L) Gh) v.2.2 h2
      · exact hzero k h1
    have : (⟨iproj hI k v, hstab k v v.2⟩ : (relativeWeight L) n) = 0 := Subtype.ext h0
    rw [this]; exact Submodule.zero_mem _

set_option synthInstance.maxHeartbeats 400000 in
-- Instance search on the cycle spaces of the concrete Kähler model is slow.
set_option maxHeartbeats 1000000 in
-- The transport proof elaborates the heavy concrete model twice.
/-- The creation test for a standard ghost grading. -/
theorem interpretedCreation_std (hs : Gh.IsStd)
    (hp : ∀ n, IsPosOn (((interpretedKahler L) Gh hA hB hG hZ hD hK).geometry n).P ⊤) :
    ∀ (n : ℤ) (p i : ℕ) (x : (UniversalWeight L) n),
      x ∈ BRSTKahlerGeometry.generatorPullback ((interpretedKahler L) Gh hA hB hG hZ hD hK) hp n p →
        (universalCreation L) n i x ∈
          BRSTKahlerGeometry.generatorPullback ((interpretedKahler L) Gh hA hB hG hZ hD hK) hp (n +
              i + 2) (p + 1) := by
  intro n p i x hx
  set S := (interpretedKahler L) Gh hA hB hG hZ hD hK
  have hDn := S.model_D n (hp n)
  have hDn' := S.model_D (n + i + 2) (hp (n + i + 2))
  refine cohomFilt_transport (S.model n (hp n)) (S.model (n + i + 2) (hp (n + i + 2)))
    ((creationOp L) n i) (fun v => ?_) _ _ (fun v hv => ?_) _ _ ?_ hx
  · rw [LinearMap.congr_fun hDn', LinearMap.congr_fun hDn, creationOp_D]
  · have h1 := (degOn_to_brst_std L) Gh hA hB hG hZ hD hK n (hp n) p v hv
    have h2 := (creation_shift_std L) hs hA p (-(-(i : ℤ) - 1) - 1) h1
    have h3 := (brst_to_degOn_std L) Gh hA hB hG hZ hD hK hs (n + i + 2) (hp (n + i + 2)) (p + 1)
      ((creationOp L) n i v) (by rw [creationOp_coe, mode_apply]; exact h2)
    simpa only [Nat.cast_add, Nat.cast_one] using h3
  · have h1 : ((BRSTKahlerGeometry.modelUniversalCycles S n (hp n) x : LinearMap.ker (S.model n (hp
      n)).D) :
        (relativeWeight L) n) = (universalWeightRepresentative L) n x := cyclesCongr_coe _ _ _ _
    have h2 : ((BRSTKahlerGeometry.modelUniversalCycles S (n + i + 2) (hp (n + i + 2))
        ((universalCreation L) n i x) :
        LinearMap.ker (S.model (n + i + 2) (hp (n + i + 2))).D) : (relativeWeight L) (n + i + 2)) =
        (universalWeightRepresentative L) (n + i + 2) ((universalCreation L) n i x) :=
      cyclesCongr_coe _ _ _ _
    rw [h1, h2]
    exact (representative_creation L) n i x

set_option synthInstance.maxHeartbeats 200000 in
-- Instance search on the cycle space of the concrete Kähler model is slow.
/-- The vacuum test for a standard ghost grading. -/
theorem interpreted_vacuum_std (hs : Gh.IsStd)
    (hp : ∀ n, IsPosOn (((interpretedKahler L) Gh hA hB hG hZ hD hK).geometry n).P ⊤) :
    (universalVacuum L) ∈ BRSTKahlerGeometry.generatorPullback ((interpretedKahler L) Gh hA hB hG
        hZ hD hK) hp 0 0 := by
  set S := (interpretedKahler L) Gh hA hB hG hZ hD hK
  change BRSTKahlerGeometry.modelUniversalClass S 0 (hp 0) (universalVacuum L) ∈
      BRSTKahlerGeometry.generatorCohomPrefix S hp 0 0
  refine class_mem_cohomFilt (S.model 0 (hp 0)) (BRSTKahlerGeometry.modelUniversalCycles S 0 (hp 0))
    (universalVacuum L) _ ?_
  have hcoe : ((BRSTKahlerGeometry.modelUniversalCycles S 0 (hp 0) (universalVacuum L) :
      LinearMap.ker (S.model 0 (hp 0)).D) : (relativeWeight L) 0) =
      (universalWeightRepresentative L) 0 (universalVacuum L) :=
    cyclesCongr_coe _ _ _ _
  rw [hcoe]
  have hrow : ((0 : ℤ), (0 : ℤ)) ∈
      KahlerComplex.rowSet (Finset.Icc 0 (2 * ((0 : ℕ) : ℤ))) 0 := ⟨by simp, rfl⟩
  refine KahlerComplex.deg_le_degOn (S.model 0 (hp 0)) hrow ?_
  change ((universalWeightRepresentative L) 0 (universalVacuum L) : (BRSTSpace L)) ∈
    (brstDeg L) Gh ((0, 0), ((0 : ℤ) : ℂ))
  rw [representative_vacuum, Int.cast_zero]
  exact (brstVacuum_mem_std L) hs

/-- **`ClassGeneratorFiltration L` for every standard ghost grading** (both tests proved). -/
theorem interpretedGenerators_std (hs : Gh.IsStd)
    (hp : ∀ n, IsPosOn (((interpretedKahler L) Gh hA hB hG hZ hD hK).geometry n).P ⊤) :
    (ClassGeneratorFiltration L) ((interpretedKahler L) Gh hA hB hG hZ hD hK) hp where
  vacuum := (interpreted_vacuum_std L) Gh hA hB hG hZ hD hK hs hp
  creation := (interpretedCreation_std L) Gh hA hB hG hZ hD hK hs hp

end Generators

/-! ### The endpoint for an arbitrary positive ghost form -/

/-- The proved inputs, bundled: zero modes and goodness for a standard ghost grading. -/
abbrev stdZ {PG : SesqForm Sl2GhostSpace} {Gh : GhostRGrading PG} (hs : Gh.IsStd) :
    (ZeroModesPreserve L) Gh := (zeroModesPreserve_std L) hs

abbrev stdD (hA : GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag L))
    {BB : InvariantForm BVOA} {RB : RealStructure BVOA} (hB : ConcreteHodge.Unitary BB RB)
    {PG : SesqForm Sl2GhostSpace} {Gh : GhostRGrading PG} (hs : Gh.IsStd) :
    (RelativeDifferentialGood L) Gh := (relativeDifferentialGood_std L) hA hB hs

/-- The interpreted Kähler geometry from the `sp(2)` input, for a standard ghost grading. -/
abbrev sp2Kahler (hA : GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag L))
    {BB : InvariantForm BVOA} {RB : RealStructure BVOA} (hB : ConcreteHodge.Unitary BB RB)
    {PG : SesqForm Sl2GhostSpace} (hG : IsPosOn PG ⊤) (Gh : GhostRGrading PG) (hs : Gh.IsStd)
    (S : (InterpretedSp2 L) Gh hA hB hG ((stdZ L) hs) ((stdD L) hA hB hs)) : (BRSTKahlerGeometry
        L) :=
  (interpretedKahler L) Gh hA hB hG ((stdZ L) hs) ((stdD L) hA hB hs)
    ((interpretedKahlerAnticomm_of_sp2 L) Gh hA hB hG _ _ S)

/-! ### Colour-weighted ghost forms -/


/-! ## Port of `BRSTKahlerConj` -/


namespace GoodComplex

variable {K : Type u} [AddCommGroup K] [Module ℂ K]

variable {G : GoodComplex K}

variable (G)

end GoodComplex

/-- The `BRSTGUData L` of the `sp(2)` geometry from the ghost-number-zero inputs. -/
def sp2GUData0 (hA : GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag L))
    {BB : InvariantForm BVOA} {RB : RealStructure BVOA} (hB : ConcreteHodge.Unitary BB RB)
    {PG : SesqForm Sl2GhostSpace} (hG : IsPosOn PG ⊤) (Gh : GhostRGrading PG) (hs : Gh.IsStd)
    (S : (InterpretedSp2 L) Gh hA hB hG ((stdZ L) hs) ((stdD L) hA hB hs))
    (R : ∀ n hp, Sp2Conj0 (concreteGood ((interpretedGoodGeometry L) Gh hA hB hG ((stdZ L) hs)
      ((stdD L) hA hB hs) ((interpretedKahlerAnticomm_of_sp2 L) Gh hA hB hG _ _ S)) n hp) (S n).E) :
    (BRSTGUData L) ((sp2Kahler L) hA hB hG Gh hs S) where
  data n hp := (concreteGood _ n hp).guData0
    ((R n hp).toConjData0 ((concreteGood_Dp_eq L) Gh hA hB hG _ _ S n hp))


end

end VOA.TwoSeries
