/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.HarmonicMetricGeneric
import VOA.Examples.BRSTConjIdentityProved
import VOA.Examples.BRSTGoodnessCreation

/-!
# The three harmonic-metric inputs from statements on the explicit representatives

The harmonic representatives in `HarmonicVacuumNormalized`, `HarmonicCreationAdjoint` and
`HarmonicWordsReal` are replaced by the explicit closed representatives
`x ↦ cosetToComplex (virasoroToCoset x) = (x_C ⊗ |0⟩_U) ⊗ |0⟩_gh`, using the generic layer
`HarmonicMetricGeneric` (`B(harmonic, exact) = 0`, `B(exact, closed) = 0`, and reality of the
harmonic representative of a real closed vector), which needs only the all-ghost-number
intertwining `ρ 𝐐⁻ = μ_g 𝐐⁺ ρ` of the corrected Beem–Garner package.

* `universalHarmonic_sub_mem_range` — the harmonic representative of a universal class differs
  from the explicit representative by a boundary;
* `harmonicVacuumNormalized_of_rep`, `harmonicCreationAdjoint_of_rep`,
  `harmonicWordsReal_of_rep` — for an arbitrary corrected package;
* `RepVacuumNormalized`, `RepCreationAdjoint`, `RepWordsReal` — the three statements on the
  explicit representatives in `BRSTSpace`, for `B = B_M ⊗ B_G` and `ρ = ρ_M ⊗ ρ_G`;
* `leeYang_gradedUnitary_of_affine_reps` — the endpoint with the three harmonic inputs replaced
  by these.

Everything is proved outright from the listed hypotheses.
-/

namespace VOA.ConcreteHodge

open Sl2CosetConcrete Sl2SemiInfinite AffineSl2GeneralRigidity AffineSl2BelowCritical
open VOA.GradedUnitaryCohomology VOA.LeeYangCosetTransfer VOA.VertexOperatorAlgebra
open VOA.LeeYangTransferAssembly LeeYangShortcut VirModule LeeYang VirGradedUnitarity
open scoped TensorProduct

noncomputable section

/-! ### Harmonic and explicit representatives differ by boundaries -/

theorem transportCyclesMap_coe {K E : Type*} [AddCommGroup K] [Module ℂ K]
    [AddCommGroup E] [Module ℂ E] (d d' : K →ₗ[ℂ] K) (hd : d = d')
    (f : E →ₗ[ℂ] LinearMap.ker d) (x : E) :
    ((transportCyclesMap d d' hd f x : LinearMap.ker d') : K) = (f x : K) := by
  subst hd; rfl

theorem universalHarmonic_sub_mem_range (S : ConcreteKahlerGeometry) (n : ℤ)
    (hp : IsPosOn (S.geometry n).P ⊤) (x : UniversalWeight n) :
    ((universalHarmonic S n hp x : (S.model n hp).harm) : relativeWeight n) -
        universalWeightRepresentative n x ∈ LinearMap.range (S.model n hp).D := by
  have h := harmonicClassLift_sub_mem_range (K := relativeWeight n) (U := UniversalWeight n)
    (S.model n hp) (modelUniversalCycles S n hp) x
  have e : ((modelUniversalCycles S n hp x : LinearMap.ker (S.model n hp).D) :
      relativeWeight n) = universalWeightRepresentative n x :=
    transportCyclesMap_coe (K := relativeWeight n) (E := UniversalWeight n) _ _ _ _ x
  rw [← e]
  exact h

/-! ### The bridge for an arbitrary corrected package -/

section Bridge

variable {hA : GradedUnitary affineForm affineRealStructure affineFlag}
  {BB : InvariantForm BVOA} {RB : RealStructure BVOA} {hB : Unitary BB RB}
  {PG : SesqForm Sl2GhostSpace} {hG : IsPosOn PG ⊤} {Gh : GhostRGrading PG} {hs : Gh.IsStd}

/-- The all-ghost datum of the endpoint complex at weight `n`. -/
abbrev pkgAllGhost (Pk : InterpretedBGPackageI Gh hA hB hG (stdZ hs) (stdD hA hB hs)) (n : ℤ)
    (hp : IsPosOn ((sp2Kahler hA hB hG Gh hs Pk.sp2).geometry n).P ⊤) :
    AllGhostConj (concreteGood (interpretedGoodGeometry Gh hA hB hG (stdZ hs) (stdD hA hB hs)
      (interpretedKahlerAnticomm_of_sp2 Gh hA hB hG _ _ Pk.sp2)) n hp) :=
  (Pk n).toAllGhostConj (interpretedHalf_pos Gh hA hB hG _ _ n) _ rfl rfl rfl
    (concreteGood_Dp_eq Gh hA hB hG _ _ Pk.sp2 n hp)

theorem pkg_closed (Pk : InterpretedBGPackageI Gh hA hB hG (stdZ hs) (stdD hA hB hs)) (n : ℤ)
    (hp : IsPosOn ((sp2Kahler hA hB hG Gh hs Pk.sp2).geometry n).P ⊤) (x : UniversalWeight n) :
    (concreteGood (interpretedGoodGeometry Gh hA hB hG (stdZ hs) (stdD hA hB hs)
      (interpretedKahlerAnticomm_of_sp2 Gh hA hB hG _ _ Pk.sp2)) n hp).D
        (universalWeightRepresentative n x) = 0 := by
  have h := (sp2Kahler hA hB hG Gh hs Pk.sp2).model_D n hp
  have e := GoodComplex.toKahler_D (concreteGood (interpretedGoodGeometry Gh hA hB hG (stdZ hs)
    (stdD hA hB hs) (interpretedKahlerAnticomm_of_sp2 Gh hA hB hG _ _ Pk.sp2)) n hp)
  rw [← e]
  change ((sp2Kahler hA hB hG Gh hs Pk.sp2).model n hp).D _ = 0
  rw [h]
  exact universalWeightRepresentative_closed n x

theorem pkg_sub_mem_range (Pk : InterpretedBGPackageI Gh hA hB hG (stdZ hs) (stdD hA hB hs))
    (n : ℤ) (hp : IsPosOn ((sp2Kahler hA hB hG Gh hs Pk.sp2).geometry n).P ⊤)
    (x : UniversalWeight n) :
    ((universalHarmonic (sp2Kahler hA hB hG Gh hs Pk.sp2) n hp x : _) : relativeWeight n) -
        universalWeightRepresentative n x ∈
      LinearMap.range (concreteGood (interpretedGoodGeometry Gh hA hB hG (stdZ hs)
        (stdD hA hB hs) (interpretedKahlerAnticomm_of_sp2 Gh hA hB hG _ _ Pk.sp2)) n hp).D := by
  have h := universalHarmonic_sub_mem_range (sp2Kahler hA hB hG Gh hs Pk.sp2) n hp x
  have e := GoodComplex.toKahler_D (concreteGood (interpretedGoodGeometry Gh hA hB hG (stdZ hs)
    (stdD hA hB hs) (interpretedKahlerAnticomm_of_sp2 Gh hA hB hG _ _ Pk.sp2)) n hp)
  rw [← e]
  exact h

/-- The form on harmonic representatives of universal classes is the form on the explicit
representatives. -/
theorem pkg_B_harmonic (Pk : InterpretedBGPackageI Gh hA hB hG (stdZ hs) (stdD hA hB hs))
    (n : ℤ) (hp : IsPosOn ((sp2Kahler hA hB hG Gh hs Pk.sp2).geometry n).P ⊤)
    (x y : UniversalWeight n) :
    ((sp2GUData0 hA hB hG Gh hs Pk.sp2 Pk.conj0).data n hp).B
        (universalHarmonic (sp2Kahler hA hB hG Gh hs Pk.sp2) n hp x)
        (universalHarmonic (sp2Kahler hA hB hG Gh hs Pk.sp2) n hp y) =
      (Pk n).B (universalWeightRepresentative n x) (universalWeightRepresentative n y) :=
  (pkgAllGhost Pk n hp).B_eq_of_classes
    (universalHarmonic (sp2Kahler hA hB hG Gh hs Pk.sp2) n hp x).2 (pkg_closed Pk n hp y)
    (pkg_sub_mem_range Pk n hp x) (pkg_sub_mem_range Pk n hp y)

/-- **Vacuum normalization from the explicit vacuum representative.** -/
theorem harmonicVacuumNormalized_of_rep
    (Pk : InterpretedBGPackageI Gh hA hB hG (stdZ hs) (stdD hA hB hs))
    (h : (Pk 0).B (universalWeightRepresentative 0 (vacuumWeight leeYangC))
      (universalWeightRepresentative 0 (vacuumWeight leeYangC)) = 1) :
    HarmonicVacuumNormalized (sp2Kahler hA hB hG Gh hs Pk.sp2)
      (sp2GUData0 hA hB hG Gh hs Pk.sp2 Pk.conj0) := fun hp => by
  rw [pkg_B_harmonic]; exact h

/-- **Creation adjointness from the explicit representatives.** -/
theorem harmonicCreationAdjoint_of_rep
    (Pk : InterpretedBGPackageI Gh hA hB hG (stdZ hs) (stdD hA hB hs))
    (h : ∀ (i : ℕ) (n m : ℤ) (x : UniversalWeight n) (y : UniversalWeight m)
      (hx : Lop leeYangC (-(i : ℤ) - 2) x ∈ (virasoroVOA leeYangC).grading m)
      (hy : Lop leeYangC ((i : ℤ) + 2) y ∈ (virasoroVOA leeYangC).grading n),
      (Pk m).B (universalWeightRepresentative m ⟨_, hx⟩) (universalWeightRepresentative m y) =
        (Pk n).B (universalWeightRepresentative n x) (universalWeightRepresentative n ⟨_, hy⟩)) :
    HarmonicCreationAdjoint (sp2Kahler hA hB hG Gh hs Pk.sp2)
      (sp2GUData0 hA hB hG Gh hs Pk.sp2 Pk.conj0) := by
  intro i n m hpn hpm x y hx hy
  rw [pkg_B_harmonic, pkg_B_harmonic]
  exact h i n m x y hx hy

/-- **Reality of the harmonic word representatives from the explicit representatives.** -/
theorem harmonicWordsReal_of_rep
    (Pk : InterpretedBGPackageI Gh hA hB hG (stdZ hs) (stdD hA hB hs))
    (h : ∀ (n : ℤ) (w : List ℕ) (hw : negWordVir leeYangC w ∈ (virasoroVOA leeYangC).grading n),
      (Pk n).ρ (universalWeightRepresentative n ⟨_, hw⟩) =
        universalWeightRepresentative n ⟨_, hw⟩) :
    HarmonicWordsReal (sp2Kahler hA hB hG Gh hs Pk.sp2)
      (sp2GUData0 hA hB hG Gh hs Pk.sp2 Pk.conj0) := by
  intro n hp w hw
  exact (pkgAllGhost Pk n hp).rho_fix_of_class
    (universalHarmonic (sp2Kahler hA hB hG Gh hs Pk.sp2) n hp ⟨_, hw⟩).2
    (pkg_sub_mem_range Pk n hp _) (h n w hw)

end Bridge

/-! ### The statements on the explicit representatives in `BRSTSpace` -/

/-- The explicit representative `(x_C ⊗ |0⟩_U) ⊗ |0⟩_gh` of a universal Virasoro state. -/
def repVec (x : VirUniv leeYangC) : BRSTSpace := cosetToComplex (virasoroToCoset x)

/-- The explicit vacuum representative has `B_M ⊗ B_G`-norm one.
Proved: `repVacuumNormalized_proved` (`HarmonicMetricVacuum.lean`). -/
def RepVacuumNormalized : Prop := ghBBRST (repVec (vacVec leeYangC)) (repVec (vacVec leeYangC)) = 1

/-- On explicit representatives, `L_{-i-2}` is `B_M ⊗ B_G`-adjoint to `L_{i+2}`.
Proved: `repCreationAdjoint_proved` (`HarmonicMetricAdjoint.lean`). -/
def RepCreationAdjoint : Prop :=
  ∀ (i : ℕ) (u v : VirUniv leeYangC),
    ghBBRST (repVec (Lop leeYangC (-(i : ℤ) - 2) u)) (repVec v) =
      ghBBRST (repVec u) (repVec (Lop leeYangC ((i : ℤ) + 2) v))

/-- `ρ_M ⊗ ρ_G` fixes the explicit representative of every creation word.
Proved: `repWordsReal_proved` (`HarmonicMetricReal.lean`). -/
def RepWordsReal : Prop :=
  ∀ w : List ℕ, ghConjBRST (repVec (negWordVir leeYangC w)) = repVec (negWordVir leeYangC w)

/-- **Affine GU ⇒ Lee–Yang GU with the harmonic inputs moved to explicit representatives.**
`#print axioms`-clean, conditional on: `hA` (the hypothesis), `hB` (unitarity of `L_1(sl₂)` for the
canonical pair) and `symbols`, `character`, `hV`, `hC`, `hR`. -/
theorem leeYang_gradedUnitary_of_affine_reps
    (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    (hB : Unitary bForm bRealStructure)
    (symbols : LeadingInvariantSymbolDimension
      (sp2Kahler hA hB bgPG_pos bgGh bgGh_isStd
        ((bgGhostRemainderI hA ghostConjRhoD_proved ghostConjBE_proved).pkg hB).sp2))
    (character : LeeYangPBWCharacter)
    (hV : RepVacuumNormalized) (hC : RepCreationAdjoint) (hR : RepWordsReal) :
    VirGradedUnitary leeYangC leeYangRealStructure :=
  leeYang_gradedUnitary_of_affine_bgConj hA hB symbols character
    (harmonicVacuumNormalized_of_rep _ hV)
    (harmonicCreationAdjoint_of_rep _ fun i _ _ x y _ _ => hC i x y)
    (harmonicWordsReal_of_rep _ fun _ w _ => Subtype.ext (hR w))

end

end VOA.ConcreteHodge
