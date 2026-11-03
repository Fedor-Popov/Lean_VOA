/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.TwoSeriesHodgeConjIdentity
import VOA.Examples.HarmonicMetricEndpoint

/-!
# Level-generic port of the level-specific parts of `HarmonicMetric*`

The three harmonic-metric bridges (vacuum normalization, creation adjointness, word reality) on
the actual level-`L` complex, proved from explicit representatives.  Level-independent
declarations (`HarmonicMetricGeneric`, the ghost-side lemmas) are reused directly.
-/

namespace VOA.TwoSeries

open VOA.ConcreteHodge Sl2CosetConcrete Sl2SemiInfinite AffineSl2GeneralRigidity
open AffineSl2BelowCritical VOA.GradedUnitaryCohomology VOA.LeeYangCosetTransfer
open VOA.VertexOperatorAlgebra VOA.LeeYangTransferAssembly LeeYangShortcut VirModule LeeYang
open VirGradedUnitarity VOA.SympFerm VOA.Ghost AffineVOA Sl2Coset
open scoped TensorProduct

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

universe u v w

variable (L : CosetLevels)

/-! ## Port of `None` -/


/-! ### Harmonic and explicit representatives differ by boundaries -/

theorem universalHarmonic_sub_mem_range (S : (BRSTKahlerGeometry L)) (n : ℤ)
    (hp : IsPosOn (S.geometry n).P ⊤) (x : (UniversalWeight L) n) :
    ((BRSTKahlerGeometry.universalHarmonic S n hp x : (S.model n hp).harm) : (relativeWeight L) n) -
        (universalWeightRepresentative L) n x ∈ LinearMap.range (S.model n hp).D := by
  have h := harmonicClassLift_sub_mem_range (K := (relativeWeight L) n) (U := (UniversalWeight L) n)
    (S.model n hp) (BRSTKahlerGeometry.modelUniversalCycles S n hp) x
  have e : ((BRSTKahlerGeometry.modelUniversalCycles S n hp x : LinearMap.ker (S.model n hp).D) :
      (relativeWeight L) n) = (universalWeightRepresentative L) n x :=
    transportCyclesMap_coe (K := (relativeWeight L) n) (E := (UniversalWeight L) n) _ _ _ _ x
  rw [← e]
  exact h

/-! ### The bridge for an arbitrary corrected package -/

section Bridge

variable {hA : GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag L)}
  {BB : InvariantForm BVOA} {RB : RealStructure BVOA} {hB : ConcreteHodge.Unitary BB RB}
  {PG : SesqForm Sl2GhostSpace} {hG : IsPosOn PG ⊤} {Gh : GhostRGrading PG} {hs : Gh.IsStd}

/-- The all-ghost datum of the endpoint complex at weight `n`. -/
abbrev pkgAllGhost (Pk : (InterpretedBGPackageI L) Gh hA hB hG ((stdZ L) hs) ((stdD L) hA hB hs))
    (n : ℤ)
    (hp : IsPosOn (((sp2Kahler L) hA hB hG Gh hs Pk.sp2).geometry n).P ⊤) :
    AllGhostConj (concreteGood ((interpretedGoodGeometry L) Gh hA hB hG ((stdZ L) hs) ((stdD L) hA
        hB hs)
      ((interpretedKahlerAnticomm_of_sp2 L) Gh hA hB hG _ _ Pk.sp2)) n hp) :=
  (Pk n).toAllGhostConj ((interpretedHalf_pos L) Gh hA hB hG _ _ n) _ rfl rfl rfl
    ((concreteGood_Dp_eq L) Gh hA hB hG _ _ Pk.sp2 n hp)

theorem pkg_closed (Pk : (InterpretedBGPackageI L) Gh hA hB hG ((stdZ L) hs) ((stdD L) hA hB hs))
    (n : ℤ)
    (hp : IsPosOn (((sp2Kahler L) hA hB hG Gh hs Pk.sp2).geometry n).P ⊤) (x : (UniversalWeight L)
        n) :
    (concreteGood ((interpretedGoodGeometry L) Gh hA hB hG ((stdZ L) hs) ((stdD L) hA hB hs)
      ((interpretedKahlerAnticomm_of_sp2 L) Gh hA hB hG _ _ Pk.sp2)) n hp).D
        ((universalWeightRepresentative L) n x) = 0 := by
  have h := ((sp2Kahler L) hA hB hG Gh hs Pk.sp2).model_D n hp
  have e := GoodComplex.toKahler_D (concreteGood ((interpretedGoodGeometry L) Gh hA hB hG ((stdZ L)
      hs)
    ((stdD L) hA hB hs) ((interpretedKahlerAnticomm_of_sp2 L) Gh hA hB hG _ _ Pk.sp2)) n hp)
  rw [← e]
  change (((sp2Kahler L) hA hB hG Gh hs Pk.sp2).model n hp).D _ = 0
  rw [h]
  exact (universalWeightRepresentative_closed L) n x

theorem pkg_sub_mem_range (Pk : (InterpretedBGPackageI L) Gh hA hB hG ((stdZ L) hs) ((stdD L) hA hB
    hs))
    (n : ℤ) (hp : IsPosOn (((sp2Kahler L) hA hB hG Gh hs Pk.sp2).geometry n).P ⊤)
    (x : (UniversalWeight L) n) :
    ((BRSTKahlerGeometry.universalHarmonic ((sp2Kahler L) hA hB hG Gh hs Pk.sp2) n hp x : _) :
        (relativeWeight L) n) -
        (universalWeightRepresentative L) n x ∈
      LinearMap.range (concreteGood ((interpretedGoodGeometry L) Gh hA hB hG ((stdZ L) hs)
        ((stdD L) hA hB hs) ((interpretedKahlerAnticomm_of_sp2 L) Gh hA hB hG _ _ Pk.sp2)) n
            hp).D := by
  have h := (universalHarmonic_sub_mem_range L) ((sp2Kahler L) hA hB hG Gh hs Pk.sp2) n hp x
  have e := GoodComplex.toKahler_D (concreteGood ((interpretedGoodGeometry L) Gh hA hB hG ((stdZ L)
      hs)
    ((stdD L) hA hB hs) ((interpretedKahlerAnticomm_of_sp2 L) Gh hA hB hG _ _ Pk.sp2)) n hp)
  rw [← e]
  exact h

/-- The form on harmonic representatives of universal classes is the form on the explicit
representatives. -/
theorem pkg_B_harmonic (Pk : (InterpretedBGPackageI L) Gh hA hB hG ((stdZ L) hs) ((stdD L) hA hB
    hs))
    (n : ℤ) (hp : IsPosOn (((sp2Kahler L) hA hB hG Gh hs Pk.sp2).geometry n).P ⊤)
    (x y : (UniversalWeight L) n) :
    (((sp2GUData0 L) hA hB hG Gh hs Pk.sp2 Pk.conj0).data n hp).B
        (BRSTKahlerGeometry.universalHarmonic ((sp2Kahler L) hA hB hG Gh hs Pk.sp2) n hp x)
        (BRSTKahlerGeometry.universalHarmonic ((sp2Kahler L) hA hB hG Gh hs Pk.sp2) n hp y) =
      (Pk n).B ((universalWeightRepresentative L) n x) ((universalWeightRepresentative L) n y) :=
  ((pkgAllGhost L) Pk n hp).B_eq_of_classes
    (BRSTKahlerGeometry.universalHarmonic ((sp2Kahler L) hA hB hG Gh hs Pk.sp2) n hp x).2
        ((pkg_closed L) Pk n hp y)
    ((pkg_sub_mem_range L) Pk n hp x) ((pkg_sub_mem_range L) Pk n hp y)

/-- **Vacuum normalization from the explicit vacuum representative.** -/
theorem harmonicVacuumNormalized_of_rep
    (Pk : (InterpretedBGPackageI L) Gh hA hB hG ((stdZ L) hs) ((stdD L) hA hB hs))
    (h : (Pk 0).B ((universalWeightRepresentative L) 0 (vacuumWeight L.c))
      ((universalWeightRepresentative L) 0 (vacuumWeight L.c)) = 1) :
    (HarmonicVacuumNormalized L) ((sp2Kahler L) hA hB hG Gh hs Pk.sp2)
      ((sp2GUData0 L) hA hB hG Gh hs Pk.sp2 Pk.conj0) := fun hp => by
  rw [pkg_B_harmonic]; exact h

/-- **Creation adjointness from the explicit representatives.** -/
theorem harmonicCreationAdjoint_of_rep
    (Pk : (InterpretedBGPackageI L) Gh hA hB hG ((stdZ L) hs) ((stdD L) hA hB hs))
    (h : ∀ (i : ℕ) (n m : ℤ) (x : (UniversalWeight L) n) (y : (UniversalWeight L) m)
      (hx : Lop L.c (-(i : ℤ) - 2) x ∈ (virasoroVOA L.c).grading m)
      (hy : Lop L.c ((i : ℤ) + 2) y ∈ (virasoroVOA L.c).grading n),
      (Pk m).B ((universalWeightRepresentative L) m ⟨_, hx⟩) ((universalWeightRepresentative L) m
          y) =
        (Pk n).B ((universalWeightRepresentative L) n x) ((universalWeightRepresentative L) n ⟨_,
            hy⟩)) :
    (HarmonicCreationAdjoint L) ((sp2Kahler L) hA hB hG Gh hs Pk.sp2)
      ((sp2GUData0 L) hA hB hG Gh hs Pk.sp2 Pk.conj0) := by
  intro i n m hpn hpm x y hx hy
  rw [pkg_B_harmonic, pkg_B_harmonic]
  exact h i n m x y hx hy

/-- **Reality of the harmonic word representatives from the explicit representatives.** -/
theorem harmonicWordsReal_of_rep
    (Pk : (InterpretedBGPackageI L) Gh hA hB hG ((stdZ L) hs) ((stdD L) hA hB hs))
    (h : ∀ (n : ℤ) (w : List ℕ) (hw : negWordVir L.c w ∈ (virasoroVOA L.c).grading n),
      (Pk n).ρ ((universalWeightRepresentative L) n ⟨_, hw⟩) =
        (universalWeightRepresentative L) n ⟨_, hw⟩) :
    (HarmonicWordsReal L) ((sp2Kahler L) hA hB hG Gh hs Pk.sp2)
      ((sp2GUData0 L) hA hB hG Gh hs Pk.sp2 Pk.conj0) := by
  intro n hp w hw
  exact ((pkgAllGhost L) Pk n hp).rho_fix_of_class
    (BRSTKahlerGeometry.universalHarmonic ((sp2Kahler L) hA hB hG Gh hs Pk.sp2) n hp ⟨_, hw⟩).2
    ((pkg_sub_mem_range L) Pk n hp _) (h n w hw)

end Bridge

/-! ### The statements on the explicit representatives in `BRSTSpace L` -/

/-- The explicit representative `(x_C ⊗ |0⟩_U) ⊗ |0⟩_gh` of a universal Virasoro state. -/
def repVec (x : VirUniv L.c) : (BRSTSpace L) := (cosetToComplex L) ((virasoroToCoset L) x)

/-- OPEN: the explicit vacuum representative has `B_M ⊗ B_G`-norm one. -/
def RepVacuumNormalized : Prop := (ghBBRST L) ((repVec L) (vacVec L.c)) ((repVec L) (vacVec L.c)) =
    1

/-- OPEN: on explicit representatives, `L_{-i-2}` is `B_M ⊗ B_G`-adjoint to `L_{i+2}`. -/
def RepCreationAdjoint : Prop :=
  ∀ (i : ℕ) (u v : VirUniv L.c),
    (ghBBRST L) ((repVec L) (Lop L.c (-(i : ℤ) - 2) u)) ((repVec L) v) =
      (ghBBRST L) ((repVec L) u) ((repVec L) (Lop L.c ((i : ℤ) + 2) v))

/-- OPEN: `ρ_M ⊗ ρ_G` fixes the explicit representative of every creation word. -/
def RepWordsReal : Prop :=
  ∀ w : List ℕ, (ghConjBRST L) ((repVec L) (negWordVir L.c w)) = (repVec L) (negWordVir L.c w)


/-! ## Port of `None` -/


theorem cosetVacuum_val : (((cosetVOA L).vacuum : (CosetSpace L)) : (ASpace L) ⊗[ℂ] BSpace) =
    (ASVA L).vacuum ⊗ₜ[ℂ] BSVA.vacuum := rfl

/-- **The explicit vacuum representative has norm one.** -/
theorem repVacuumNormalized_proved : (RepVacuumNormalized L) := by
  rw [RepVacuumNormalized, repVec, virasoroToCoset_vacuum, cosetToComplex_apply,
    cosetVacuum_val, ← gvac_eq]
  rw [ghBBRST, bilinTmul_tmul, ghostB_gvac, mul_one, matterB, bilinTmul_tmul, bilinTmul_tmul]
  rw [show (affineForm L).form (ASVA L).vacuum (ASVA L).vacuum = 1 from (affineForm_normalized L),
    show bForm.form BSVA.vacuum BSVA.vacuum = 1 from simpleForm_normalized 1 bNoncritical,
    show (auxiliaryForm L).form (USVA L).vacuum (USVA L).vacuum = 1 from
      universalForm_normalized L.kU L.uNoncritical]
  norm_num


/-! ## Port of `None` -/


/-! ### Mode compatibility on a tensor product -/

/-! ### The conjugation of the two simple affine factors -/

/-- `ρ_A ⊗ ρ_B` on `A ⊗ B`. -/
abbrev rhoAB : (ASpace L) ⊗[ℂ] BSpace →ₗ⋆[ℂ] (ASpace L) ⊗[ℂ] BSpace :=
  TensorProduct.map (rsLin (affineRealStructure L)) (rsLin bRealStructure)

theorem rhoAB_mode (u z : (ASpace L) ⊗[ℂ] BSpace) (m : ℤ) :
    (rhoAB L) (mode ((abSVA L).Y u) m z) = mode ((abSVA L).Y ((rhoAB L) u)) m ((rhoAB L) z) := by
  rw [mode_apply, mode_apply]
  exact tenY_map_toSuper (AVOA L).toPreVertexAlgebra BVOA.toPreVertexAlgebra _ _
    (rsLin_Y (affineRealStructure L)) (rsLin_Y bRealStructure) u z _

theorem rhoA_current (a : Fin 3) :
    rsLin (affineRealStructure L) ((aAction L).current a) =
      -(aAction L).current (HighestModule.adjointColour a) := by
  have h1 : (aAction L).current a = (aMode L) a (-1) (ASVA L).vacuum := ((ASVA L).creation _).1.symm
  have h2 : (aAction L).current (HighestModule.adjointColour a) =
      (aMode L) (HighestModule.adjointColour a) (-1) (ASVA L).vacuum := ((ASVA L).creation _).1.symm
  rw [h1, h2, rsLin_apply, aMode_rho]
  congr 2
  exact (affineRealStructure L).map_vacuum

theorem rhoAB_diagCurrent (a : Fin 3) :
    (rhoAB L) ((diagonalAction L).current a) = -(diagonalAction L).current
        (HighestModule.adjointColour a) := by
  change (rhoAB L) ((aAction L).current a ⊗ₜ[ℂ] BSVA.vacuum + (ASVA L).vacuum ⊗ₜ[ℂ] bAction.current
      a) =
    -((aAction L).current _ ⊗ₜ[ℂ] BSVA.vacuum + (ASVA L).vacuum ⊗ₜ[ℂ] bAction.current _)
  rw [map_add, TensorProduct.map_tmul, TensorProduct.map_tmul, rhoA_current, rhoB_current]
  rw [show rsLin bRealStructure BSVA.vacuum = BSVA.vacuum from bRealStructure.map_vacuum,
    show rsLin (affineRealStructure L) (ASVA L).vacuum = (ASVA L).vacuum from
      (affineRealStructure L).map_vacuum]
  rw [TensorProduct.neg_tmul, TensorProduct.tmul_neg, neg_add]

theorem rhoAB_diagQuad (b c : Fin 3) :
    (rhoAB L) (mode ((abSVA L).Y ((diagonalAction L).current b)) (-1) ((diagonalAction L).current
        c)) =
      mode ((abSVA L).Y ((diagonalAction L).current (HighestModule.adjointColour b))) (-1)
        ((diagonalAction L).current (HighestModule.adjointColour c)) := by
  rw [rhoAB_mode, rhoAB_diagCurrent, rhoAB_diagCurrent, mode_apply, mode_apply, map_neg, map_neg]
  set X := (abSVA L).Y ((diagonalAction L).current (HighestModule.adjointColour b))
  have e : (-X) (-(-1 : ℤ) - 1) = -(X (-(-1 : ℤ) - 1)) := rfl
  rw [e, LinearMap.neg_apply, neg_neg]

theorem rhoAB_diagonalSugawara : (rhoAB L) (diagonalSugawara L) = (diagonalSugawara L) := by
  have hs : (starRingEnd ℂ) ((2 * (L.kAct + 1 + 2))⁻¹) = (2 * (L.kAct + 1 + 2))⁻¹ := by
    have hk : (starRingEnd ℂ) L.kAct = L.kAct := by rw [L.kAct_eq]; exact L.aReal
    simp only [map_inv₀, map_mul, map_add, map_ofNat, map_one, hk]
  change (rhoAB L) ((2 * (L.kAct + 1 + 2))⁻¹ • ∑ b : Fin 3, ∑ c : Fin 3,
      kappaInv b c • mode ((abSVA L).Y ((diagonalAction L).current b)) (-1)
        ((diagonalAction L).current c)) = (2 * (L.kAct + 1 + 2))⁻¹ • ∑ b : Fin 3, ∑ c : Fin 3,
      kappaInv b c • mode ((abSVA L).Y ((diagonalAction L).current b)) (-1) ((diagonalAction
          L).current c)
  rw [LinearMap.map_smulₛₗ, hs]
  congr 1
  have a0 : HighestModule.adjointColour 0 = 1 := rfl
  have a1 : HighestModule.adjointColour 1 = 0 := rfl
  have a2 : HighestModule.adjointColour 2 = 2 := rfl
  have k01 : kappaInv 0 1 = 1 := rfl
  have k10 : kappaInv 1 0 = 1 := rfl
  have k22 : kappaInv 2 2 = 1 / 2 := rfl
  have k00 : kappaInv 0 0 = 0 := rfl
  have k02 : kappaInv 0 2 = 0 := rfl
  have k11 : kappaInv 1 1 = 0 := rfl
  have k12 : kappaInv 1 2 = 0 := rfl
  have k20 : kappaInv 2 0 = 0 := rfl
  have k21 : kappaInv 2 1 = 0 := rfl
  simp only [Fin.sum_univ_three, k00, k01, k02, k10, k11, k12, k20, k21, k22, zero_smul,
    one_smul, add_zero, zero_add, map_add, LinearMap.map_smulₛₗ, rhoAB_diagQuad, a0, a1, a2]
  rw [show (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, Complex.conj_ofReal]]
  abel

theorem rhoAB_ambient : (rhoAB L) (ambientConformal L) = (ambientConformal L) := by
  change (rhoAB L) ((AVOA L).conformalVector ⊗ₜ[ℂ] BSVA.vacuum + (ASVA L).vacuum ⊗ₜ[ℂ]
      BVOA.conformalVector) = _
  rw [map_add, TensorProduct.map_tmul, TensorProduct.map_tmul]
  rw [show rsLin bRealStructure BSVA.vacuum = BSVA.vacuum from bRealStructure.map_vacuum,
    show rsLin (affineRealStructure L) (ASVA L).vacuum = (ASVA L).vacuum from
      (affineRealStructure L).map_vacuum,
    show rsLin (affineRealStructure L) (AVOA L).conformalVector = (AVOA L).conformalVector from
      (affineRealStructure L).map_omega,
    show rsLin bRealStructure BVOA.conformalVector = BVOA.conformalVector from
      bRealStructure.map_omega]
  rfl

/-- **`ρ_A ⊗ ρ_B` fixes the coset conformal vector.** -/
theorem rhoAB_cosetOmega : (rhoAB L) (cosetOmega L) = (cosetOmega L) := by
  rw [cosetOmega, map_sub, rhoAB_ambient, rhoAB_diagonalSugawara]

/-- `ρ_A ⊗ ρ_B` fixes the coset image of every creation word. -/
theorem rhoAB_word (w : List ℕ) :
    (rhoAB L) (((virasoroToCoset L) (negWordVir L.c w) : (CosetSpace L)) : (ASpace L) ⊗[ℂ] BSpace) =
      (((virasoroToCoset L) (negWordVir L.c w) : (CosetSpace L)) : (ASpace L) ⊗[ℂ] BSpace) := by
  induction w with
  | nil =>
      rw [negWordVir_nil, virasoroToCoset_vacuum]
      change (rhoAB L) ((ASVA L).vacuum ⊗ₜ[ℂ] BSVA.vacuum) = (ASVA L).vacuum ⊗ₜ[ℂ] BSVA.vacuum
      rw [TensorProduct.map_tmul]
      rw [show rsLin bRealStructure BSVA.vacuum = BSVA.vacuum from bRealStructure.map_vacuum,
        show rsLin (affineRealStructure L) (ASVA L).vacuum = (ASVA L).vacuum from
          (affineRealStructure L).map_vacuum]
  | cons i w ih =>
      rw [negWordVir_cons]
      rw [show (virasoroToCoset L) (Lop L.c (-(i : ℤ) - 2) (negWordVir L.c w)) =
        (cosetVOA L).L (-(i : ℤ) - 2) ((virasoroToCoset L) (negWordVir L.c w)) from
          conformalEval_L (cosetVOA L) rfl _ _]
      rw [VertexOperatorAlgebra.L_def, ← PreVertexAlgebra.smul_def, cosetVOA_mode, cosetMode_coe]
      change (rhoAB L) (mode ((abSVA L).Y (cosetOmega L)) _ _) = mode ((abSVA L).Y (cosetOmega L))
          _ _
      rw [rhoAB_mode, rhoAB_cosetOmega, ih]

/-- **`ρ_M ⊗ ρ_G` fixes the explicit representative of every creation word.** -/
theorem repWordsReal_proved : (RepWordsReal L) := by
  intro w
  rw [repVec, cosetToComplex_apply]
  change TensorProduct.map ((matterRho L) bRealStructure) ghostConj _ = _
  rw [TensorProduct.map_tmul, ← gvac_eq, ghostConj_gvac]
  congr 1
  change TensorProduct.map (rhoAB L) (rsLin (auxiliaryRealStructure L)) _ = _
  rw [TensorProduct.map_tmul, rhoAB_word,
    show rsLin (auxiliaryRealStructure L) (USVA L).vacuum = (USVA L).vacuum from
      (auxiliaryRealStructure L).map_vacuum]


/-! ## Port of `None` -/


/-! ### Adjoint operators on a tensor product -/

/-- `B_A ⊗ B_B`. -/
abbrev BAB : LinearMap.BilinForm ℂ ((ASpace L) ⊗[ℂ] BSpace) := (affineForm L).form.tmul bForm.form

/-! ### The ambient Virasoro modes -/

theorem ambient_mode_eq (n : ℤ) (z : (ASpace L) ⊗[ℂ] BSpace) :
    mode ((abSVA L).Y (ambientConformal L)) (n + 1) z =
      (((AVOA L).L n).rTensor BSpace + (BVOA.L n).lTensor (ASpace L)) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z z' hz hz' => rw [map_add, hz, hz', map_add]
  | tmul x y =>
      change mode (TensorVA.tenY (ASVA L) BSVA ((AVOA L).conformalVector ⊗ₜ[ℂ] BSVA.vacuum +
        (ASVA L).vacuum ⊗ₜ[ℂ] BVOA.conformalVector)) (n + 1) (x ⊗ₜ[ℂ] y) = _
      rw [map_add, mode_add, LinearMap.add_apply, mode_apply, mode_apply, tenY_left_unit,
        tenY_right_unit_even (ASVA L) BSVA (bSpace_parity_zero _)]
      simp only [LinearMap.add_apply, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul]
      rw [VertexOperatorAlgebra.L_def, VertexOperatorAlgebra.L_def, ← PreVertexAlgebra.smul_def,
        ← PreVertexAlgebra.smul_def, PreVertexAlgebra.smul_def, PreVertexAlgebra.smul_def, mode_apply,
        mode_apply]
      rfl

theorem BAB_ambient_adj (n : ℤ) (u v : (ASpace L) ⊗[ℂ] BSpace) :
    (BAB L) (mode ((abSVA L).Y (ambientConformal L)) (n + 1) u) v =
      (BAB L) u (mode ((abSVA L).Y (ambientConformal L)) (-n + 1) v) := by
  rw [ambient_mode_eq, ambient_mode_eq]
  exact tensorB_adj_rTensor_lTensor _ _ _ _ _ _ ((affineForm L).virasoro_adj n)
    (bForm.virasoro_adj n) u v

/-! ### Diagonal-current creation span -/

/-- The diagonal current coefficient `J^a_{(-1-m)}` on `A ⊗ B`. -/
abbrev Jd (a : Fin 3) (m : ℤ) : Module.End ℂ ((ASpace L) ⊗[ℂ] BSpace) :=
  (abSVA L).Y ((diagonalAction L).current a) m

theorem Jd_mode_eq (a : Fin 3) (n : ℤ) (z : (ASpace L) ⊗[ℂ] BSpace) :
    mode ((abSVA L).Y ((diagonalAction L).current a)) n z =
      (((aMode L) a n).rTensor BSpace + (bMode a n).lTensor (ASpace L)) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z z' hz hz' => rw [map_add, hz, hz', map_add]
  | tmul x y =>
      have h := tensorCurrentMode_tmul (aAction L).toAffineSl2Action bAction.toAffineSl2Action a n
          x y
      exact h

theorem BAB_Jd_skew (a : Fin 3) (n : ℤ) (u v : (ASpace L) ⊗[ℂ] BSpace) :
    (BAB L) (mode ((abSVA L).Y ((diagonalAction L).current a)) n u) v =
      -(BAB L) u (mode ((abSVA L).Y ((diagonalAction L).current a)) (-n) v) := by
  rw [Jd_mode_eq, Jd_mode_eq]
  exact tensorB_add_rTensor_lTensor _ _ _ _ _ _ ((aMode_adj L) a n) (bCompactUnitary.skew a n) u v

/-- The span of the diagonal-current creation coefficients. -/
def creationSpan : Submodule ℂ ((ASpace L) ⊗[ℂ] BSpace) :=
  Submodule.span ℂ {z | ∃ (a : Fin 3) (m : ℕ) (w : (ASpace L) ⊗[ℂ] BSpace), z = (Jd L) a m w}

theorem Jd_mem_creationSpan (a : Fin 3) (m : ℕ) (w : (ASpace L) ⊗[ℂ] BSpace) :
    (Jd L) a m w ∈ (creationSpan L) :=
  Submodule.subset_span ⟨a, m, w, rfl⟩

theorem BAB_creationSpan_coset {z : (ASpace L) ⊗[ℂ] BSpace} (hz : z ∈ (creationSpan L))
    {y : (ASpace L) ⊗[ℂ] BSpace} (hy : y ∈ cosetSubspace (diagonalAction L).toAffineSl2Action) :
    (BAB L) z y = 0 := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨a, m, w, rfl⟩ := hz
      have e : (Jd L) a m w = mode ((abSVA L).Y ((diagonalAction L).current a)) (-(m : ℤ) - 1) w :=
          by
        rw [mode_apply, show -(-(m : ℤ) - 1) - 1 = m by ring]
      rw [e, BAB_Jd_skew, hy a _ (by omega), map_zero, neg_zero]
  | zero => simp
  | add x x' _ _ hx hx' => rw [map_add, LinearMap.add_apply, hx, hx', add_zero]
  | smul c x _ hx => rw [map_smul, LinearMap.smul_apply, hx, smul_zero]

theorem T_mem_creationSpan {z : (ASpace L) ⊗[ℂ] BSpace} (hz : z ∈ (creationSpan L)) :
    (diagonalAction L).translation.T z ∈ (creationSpan L) := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨a, m, w, rfl⟩ := hz
      have h := (diagonalAction L).translation.comm_Ycoeff ((diagonalAction L).current a) m
      rw [LieRing.of_associative_ring_bracket] at h
      have h' := LinearMap.congr_fun h w
      rw [← Int.cast_smul_eq_zsmul ℂ] at h'
      simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] at h'
      have e : (diagonalAction L).translation.T ((Jd L) a m w) =
          (Jd L) a m ((diagonalAction L).translation.T w) +
            (((m : ℤ) + 1 : ℤ) : ℂ) • (Jd L) a ((m : ℤ) + 1) w := by
        rw [← h']; abel
      rw [e]
      refine Submodule.add_mem _ ((Jd_mem_creationSpan L) _ _ _) (Submodule.smul_mem _ _ ?_)
      exact_mod_cast (Jd_mem_creationSpan L) a (m + 1) w
  | zero => simp
  | add x x' _ _ hx hx' => rw [map_add]; exact Submodule.add_mem _ hx hx'
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

theorem coset_mem_creationSpan {x : (ASpace L) ⊗[ℂ] BSpace}
    (hx : x ∈ cosetSubspace (diagonalAction L).toAffineSl2Action) {z : (ASpace L) ⊗[ℂ] BSpace}
    (hz : z ∈ (creationSpan L)) : mode ((abSVA L).Y x) (-1) z ∈ (creationSpan L) := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨a, m, w, rfl⟩ := hz
      have h := current_mode_coset_mode_commute (diagonalAction L).toAffineSl2Action
        (diagonalAction L).translation hx a (-(m : ℤ) - 1) (-1)
      have h' := LinearMap.congr_fun h w
      rw [Module.End.mul_apply, Module.End.mul_apply, mode_apply ((abSVA L).Y _) (-(m : ℤ) - 1),
        show -(-(m : ℤ) - 1) - 1 = m by ring] at h'
      change mode ((abSVA L).Y x) (-1) ((abSVA L).Y ((diagonalAction L).current a) m w) ∈
          (creationSpan L)
      rw [← h']
      exact (Jd_mem_creationSpan L) _ _ _
  | zero => simp
  | add x x' _ _ hx hx' => rw [map_add]; exact Submodule.add_mem _ hx hx'
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

theorem diagonalSugawara_mem : (diagonalSugawara L) ∈ (creationSpan L) := by
  change (2 * (L.kAct + 1 + 2))⁻¹ • ∑ b : Fin 3, ∑ c : Fin 3,
      kappaInv b c • mode ((abSVA L).Y ((diagonalAction L).current b)) (-1)
        ((diagonalAction L).current c) ∈ (creationSpan L)
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun b _ => Submodule.sum_mem _ fun c _ =>
    Submodule.smul_mem _ _ ?_)
  rw [mode_apply, show -(-1 : ℤ) - 1 = ((0 : ℕ) : ℤ) by norm_num]
  exact (Jd_mem_creationSpan L) _ _ _

theorem sugawara_vacuum_mem (m : ℕ) :
    (abSVA L).Y (diagonalSugawara L) m (abSVA L).vacuum ∈ (creationSpan L) := by
  induction m with
  | zero =>
      have h := ((abSVA L).creation (diagonalSugawara L)).1
      rw [mode_apply, show -(-1 : ℤ) - 1 = 0 by norm_num] at h
      rw [Nat.cast_zero, h]
      exact (diagonalSugawara_mem L)
  | succ m ih =>
      have h := (diagonalAction L).translation.comm_Ycoeff (diagonalSugawara L) m
      rw [LieRing.of_associative_ring_bracket] at h
      have h' := LinearMap.congr_fun h (abSVA L).vacuum
      rw [← Int.cast_smul_eq_zsmul ℂ] at h'
      simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
        (diagonalAction L).translation.vacuum_zero, map_zero, sub_zero] at h'
      have hT := (T_mem_creationSpan L) ih
      rw [h'] at hT
      have hne : (((m : ℤ) + 1 : ℤ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : (m : ℤ) + 1 ≠ 0)
      have := Submodule.smul_mem (creationSpan L) ((((m : ℤ) + 1 : ℤ) : ℂ)⁻¹) hT
      rw [smul_smul, inv_mul_cancel₀ hne, one_smul] at this
      exact_mod_cast this

/-- **The negative Sugawara modes of a coset vector are orthogonal to the coset.** -/
theorem BAB_sugawara_neg_coset {x y : (ASpace L) ⊗[ℂ] BSpace}
    (hx : x ∈ cosetSubspace (diagonalAction L).toAffineSl2Action)
    (hy : y ∈ cosetSubspace (diagonalAction L).toAffineSl2Action) (m : ℕ) :
    (BAB L) (mode ((abSVA L).Y (diagonalSugawara L)) (-(m : ℤ) - 1) x) y = 0 := by
  have hc := sugawara_mode_coset_mode_commute (diagonalAction L).toAffineSl2Action
    (diagonalAction L).translation hx (-(m : ℤ) - 1) (-1)
  have h := LinearMap.congr_fun hc (abSVA L).vacuum
  simp only [Module.End.mul_apply, ((abSVA L).creation x).1] at h
  change (BAB L) (mode ((abSVA L).Y (sugawaraState (diagonalAction L).toAffineSl2Action)) _ x) y = 0
  rw [h]
  apply (BAB_creationSpan_coset L) _ hy
  apply (coset_mem_creationSpan L) hx
  have := (sugawara_vacuum_mem L) m
  rwa [mode_apply, show -(-(m : ℤ) - 1) - 1 = m by ring]

/-- **Coset creation modes are adjoint to annihilation modes on the coset.** -/
theorem BAB_coset_creation_adj (i : ℕ) {x y : (ASpace L) ⊗[ℂ] BSpace}
    (hx : x ∈ cosetSubspace (diagonalAction L).toAffineSl2Action)
    (hy : y ∈ cosetSubspace (diagonalAction L).toAffineSl2Action) :
    (BAB L) (mode ((abSVA L).Y (cosetOmega L)) (-(i : ℤ) - 1) x) y =
      (BAB L) x (mode ((abSVA L).Y (cosetOmega L)) ((i : ℤ) + 3) y) := by
  rw [cosetOmega, map_sub, mode_sub, mode_sub, LinearMap.sub_apply, LinearMap.sub_apply,
    map_sub, LinearMap.sub_apply, map_sub]
  have h1 := (BAB_sugawara_neg_coset L) hx hy (i + 0)
  rw [show -((i + 0 : ℕ) : ℤ) - 1 = -(i : ℤ) - 1 by push_cast; ring] at h1
  have h2 : mode ((abSVA L).Y (diagonalSugawara L)) ((i : ℤ) + 3) y = 0 :=
    sugawara_mode_coset (diagonalAction L).toAffineSl2Action (diagonalAction L).translation hy _
      (by omega)
  rw [h1, h2, map_zero, sub_zero, sub_zero]
  have h3 := (BAB_ambient_adj L) (-(i : ℤ) - 2) x y
  rw [show -(i : ℤ) - 2 + 1 = -(i : ℤ) - 1 by ring,
    show -(-(i : ℤ) - 2) + 1 = (i : ℤ) + 3 by ring] at h3
  exact h3

/-! ### The explicit representatives -/

theorem ghBBRST_repVec (p q : (ASpace L) ⊗[ℂ] BSpace) :
    (ghBBRST L) ((p ⊗ₜ[ℂ] (USVA L).vacuum) ⊗ₜ[ℂ] sl2GhostSVA.vacuum)
        ((q ⊗ₜ[ℂ] (USVA L).vacuum) ⊗ₜ[ℂ] sl2GhostSVA.vacuum) = (BAB L) p q := by
  rw [← gvac_eq, ghBBRST, bilinTmul_tmul, ghostB_gvac, mul_one, matterB, bilinTmul_tmul,
    show (auxiliaryForm L).form (USVA L).vacuum (USVA L).vacuum = 1 from
      universalForm_normalized L.kU L.uNoncritical, mul_one]

theorem virasoroToCoset_Lop_val (n : ℤ) (u : VirUniv L.c) :
    (((virasoroToCoset L) (Lop L.c n u) : (CosetSpace L)) : (ASpace L) ⊗[ℂ] BSpace) =
      mode ((abSVA L).Y (cosetOmega L)) (n + 1) ((virasoroToCoset L) u : (CosetSpace L)) := by
  rw [show (virasoroToCoset L) (Lop L.c n u) = (cosetVOA L).L n ((virasoroToCoset L) u) from
    conformalEval_L (cosetVOA L) rfl _ _]
  rw [VertexOperatorAlgebra.L_def, ← PreVertexAlgebra.smul_def, cosetVOA_mode, cosetMode_coe]
  rfl

/-- **`RepCreationAdjoint L` is proved.** -/
theorem repCreationAdjoint_proved : (RepCreationAdjoint L) := by
  intro i u v
  rw [repVec, repVec, repVec, repVec, cosetToComplex_apply, cosetToComplex_apply,
    cosetToComplex_apply, cosetToComplex_apply, ghBBRST_repVec, ghBBRST_repVec,
    virasoroToCoset_Lop_val, virasoroToCoset_Lop_val,
    show -(i : ℤ) - 2 + 1 = -(i : ℤ) - 1 by ring, show (i : ℤ) + 2 + 1 = (i : ℤ) + 3 by ring]
  exact (BAB_coset_creation_adj L) i ((virasoroToCoset L) u).2 ((virasoroToCoset L) v).2


/-! ## Port of `None` -/


theorem harmonicVacuumNormalized_proved
    (hA : GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag L))
    (hB : ConcreteHodge.Unitary bForm bRealStructure) :
    (HarmonicVacuumNormalized L)
      ((sp2Kahler L) hA hB bgPG_pos bgGh bgGh_isStd
        (((bgGhostRemainderI L) hA (ghostConjRhoD_proved L) (ghostConjBE_proved L)).pkg hB).sp2)
      ((sp2GUData0 L) hA hB bgPG_pos bgGh bgGh_isStd
        (((bgGhostRemainderI L) hA (ghostConjRhoD_proved L) (ghostConjBE_proved L)).pkg hB).sp2
        (((bgGhostRemainderI L) hA (ghostConjRhoD_proved L) (ghostConjBE_proved L)).pkg
            hB).conj0) :=
  (harmonicVacuumNormalized_of_rep L) _ (repVacuumNormalized_proved L)

theorem harmonicCreationAdjoint_proved
    (hA : GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag L))
    (hB : ConcreteHodge.Unitary bForm bRealStructure) :
    (HarmonicCreationAdjoint L)
      ((sp2Kahler L) hA hB bgPG_pos bgGh bgGh_isStd
        (((bgGhostRemainderI L) hA (ghostConjRhoD_proved L) (ghostConjBE_proved L)).pkg hB).sp2)
      ((sp2GUData0 L) hA hB bgPG_pos bgGh bgGh_isStd
        (((bgGhostRemainderI L) hA (ghostConjRhoD_proved L) (ghostConjBE_proved L)).pkg hB).sp2
        (((bgGhostRemainderI L) hA (ghostConjRhoD_proved L) (ghostConjBE_proved L)).pkg
            hB).conj0) :=
  (harmonicCreationAdjoint_of_rep L) _ fun i _ _ x y _ _ => (repCreationAdjoint_proved L) i x y

theorem harmonicWordsReal_proved
    (hA : GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag L))
    (hB : ConcreteHodge.Unitary bForm bRealStructure) :
    (HarmonicWordsReal L)
      ((sp2Kahler L) hA hB bgPG_pos bgGh bgGh_isStd
        (((bgGhostRemainderI L) hA (ghostConjRhoD_proved L) (ghostConjBE_proved L)).pkg hB).sp2)
      ((sp2GUData0 L) hA hB bgPG_pos bgGh bgGh_isStd
        (((bgGhostRemainderI L) hA (ghostConjRhoD_proved L) (ghostConjBE_proved L)).pkg hB).sp2
        (((bgGhostRemainderI L) hA (ghostConjRhoD_proved L) (ghostConjBE_proved L)).pkg
            hB).conj0) :=
  (harmonicWordsReal_of_rep L) _ fun _ w _ => Subtype.ext ((repWordsReal_proved L) w)


end

end VOA.TwoSeries
