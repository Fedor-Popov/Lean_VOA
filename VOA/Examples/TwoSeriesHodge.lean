/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.TwoSeriesImage
import VOA.Examples.LeeYangShortcutAssembly

/-!
# Kähler data on the level-`L` relative complexes, and the Virasoro class bridges

The generalization of `ConcreteKahlerGeometry` (`LeeYangTransferAssemblyInputs`), the second half
of `LeeYangShortcutRelative`, `LeeYangShortcutGenerators`, and the metric part of
`LeeYangShortcutAssembly`, from the Lee–Yang complex to the level-`L` complex.  All statements are
about the actual relative complexes `relativeWeight L n` and the actual universal Virasoro
classes `modelUniversalClass`; nothing here is an abstract surrogate.

Definitions only of *named inputs* (`BRSTKahlerGeometry`, `ClassGeneratorFiltration`,
`HarmonicVacuumNormalized`, `HarmonicCreationAdjoint`, `HarmonicWordsReal`); and the proved
reductions between them (`modelUniversalClass_ker_le`, `modelUniversalClass_filtered_of_generators`,
`universalImageMetric_of_invariance`, `harmonicConjugationAgreement_of_words`).
-/

namespace VOA.TwoSeries

open VirModule VirSimple VirGoodFil VirQuotForm VirGradedUnitarity Sl2SemiInfinite
open LeeYangShortcut LeeYangTransferAssembly LeeYangCosetTransfer GradedUnitaryCohomology

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

variable (L : CosetLevels)

/-- The Kähler data of Beem–Garner Lemma 3.16 on the actual level-`L` relative complexes,
before positivity: differential pieces summing to the actual BRST residue, bigrading whose
second coordinate is the actual ghost number. -/
structure BRSTKahlerGeometry where
  geometry : ∀ n : ℤ, KahlerGeometry (relativeWeight L n)
  differential : ∀ n, (geometry n).Qm + (geometry n).Sm = relativeDifferential L n
  ghost : ∀ n a, (geometry n).deg a ≤
    ((brstComplex L).ghost a.2).comap (relativeWeight L n).subtype

namespace BRSTKahlerGeometry

variable {L}
variable (S : BRSTKahlerGeometry L)

def model (n : ℤ) (hp : IsPosOn (S.geometry n).P ⊤) : KahlerComplex (relativeWeight L n) :=
  (S.geometry n).toKahler hp

theorem model_D (n : ℤ) (hp : IsPosOn (S.geometry n).P ⊤) :
    (S.model n hp).D = relativeDifferential L n :=
  S.differential n

def modelUniversalCycles (n : ℤ) (hp : IsPosOn (S.geometry n).P ⊤) :=
  transportCyclesMap (K := relativeWeight L n) (E := UniversalWeight L n)
    (relativeDifferential L n) (S.model n hp).D (S.model_D n hp).symm
    (universalWeightCycles L n)

/-- The actual universal Virasoro class map in the Kähler model. -/
def modelUniversalClass (n : ℤ) (hp : IsPosOn (S.geometry n).P ⊤) :=
  cycleClassOfCycles (K := relativeWeight L n) (M := UniversalWeight L n)
    (S.model n hp).D (S.modelUniversalCycles n hp)

/-- The kernel of the class map is killed by the simple projection (proof-valued `def`, as in
`LeeYangShortcutRelative`, to keep the exact quotient instances). -/
def modelUniversalClass_ker_le (n : ℤ) (hp : IsPosOn (S.geometry n).P ⊤) :=
  transportedCycles_ker_le (K := relativeWeight L n) (E := UniversalWeight L n)
    (T := TargetWeight L n)
    (relativeDifferential L n) (S.model n hp).D (S.model_D n hp).symm
    (universalWeightCycles L n) (simpleWeightProjection L n) (fun x hx => by
      obtain ⟨y, hy⟩ := hx
      exact universalWeightCycles_exact_zero L n x ⟨y, hy⟩)

/-- The harmonic representative of the class of a universal Virasoro state. -/
def universalHarmonic (n : ℤ) (hp : IsPosOn (S.geometry n).P ⊤) :
    UniversalWeight L n →ₗ[ℂ] (S.model n hp).harm :=
  harmonicClassLift (K := relativeWeight L n) (S.model n hp) (S.modelUniversalClass n hp)

/-! ### The filtration bridge -/

/-- Class of each universal PBW prefix lies in the matching cohomology filtration step. -/
def UniversalClassFiltered : Prop :=
  ∀ n (hp : IsPosOn (S.geometry n).P ⊤) p,
    (universalPrefix L p n).map (S.modelUniversalClass n hp) ≤
      (S.model n hp).cohomFilt (KahlerComplex.rowSet (Finset.Icc 0 (2 * (p : ℤ))) 0)

def generatorCohomPrefix (hp : ∀ n, IsPosOn (S.geometry n).P ⊤) (n : ℤ) (p : ℕ) :=
  (S.model n (hp n)).cohomFilt (KahlerComplex.rowSet (Finset.Icc 0 (2 * (p : ℤ))) 0)

theorem generatorCohomPrefix_mono (hp : ∀ n, IsPosOn (S.geometry n).P ⊤) (n : ℤ) :
    Monotone (S.generatorCohomPrefix hp n) := by
  intro p q hpq
  apply Submodule.map_mono
  apply Submodule.comap_mono
  apply KahlerComplex.degOn_mono
  intro a ha
  refine ⟨?_, ha.2⟩
  have h := Finset.mem_Icc.mp ha.1
  apply Finset.mem_Icc.mpr
  exact ⟨h.1, le_trans h.2 (by exact_mod_cast Nat.mul_le_mul_left 2 hpq)⟩

def generatorPullback (hp : ∀ n, IsPosOn (S.geometry n).P ⊤) (n : ℤ) (p : ℕ) :
    Submodule ℂ (UniversalWeight L n) :=
  (S.generatorCohomPrefix hp n p).comap (S.modelUniversalClass n (hp n))

end BRSTKahlerGeometry

def universalVacuum : UniversalWeight L 0 :=
  ⟨vacVec L.c, vacVec_mem_gradingVir_zero L.c⟩

def universalCreation (n : ℤ) (i : ℕ) :
    UniversalWeight L n →ₗ[ℂ] UniversalWeight L (n + i + 2) :=
  ((Lop L.c (-(i : ℤ) - 2)).comp (UniversalWeight L n).subtype).codRestrict _
    (fun x => by
      simpa only [add_assoc] using Lop_neg_maps_grading L.c i x.2)

theorem universalPrefix_le_of_generators
    (F : ∀ n : ℤ, ℕ → Submodule ℂ (UniversalWeight L n))
    (hmono : ∀ n, Monotone (F n))
    (hvac : universalVacuum L ∈ F 0 0)
    (hcreation : ∀ (n : ℤ) (p i : ℕ) (x : UniversalWeight L n),
      x ∈ F n p → universalCreation L n i x ∈ F (n + i + 2) (p + 1))
    (p : ℕ) (n : ℤ) : universalPrefix L p n ≤ F n p := by
  let F' := fun p n => (F n p).map (UniversalWeight L n).subtype
  have hm : ∀ n, Monotone fun p => F' p n :=
    fun n _ _ h => Submodule.map_mono (hmono n h)
  have hv : (LinearMap.id : VirUniv L.c →ₗ[ℂ] VirUniv L.c) (vacVec L.c) ∈ F' 0 0 :=
    Submodule.mem_map.mpr ⟨universalVacuum L, hvac, rfl⟩
  have hs : ∀ (p : ℕ) (n : ℤ) (i : ℕ) (x : VirUniv L.c),
      x ∈ F' p n → Lop L.c (-(i : ℤ) - 2) x ∈ F' (p + 1) (n + i + 2) := by
    intro p n i x hx
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
    exact Submodule.mem_map.mpr ⟨universalCreation L n i y, hcreation n p i y hy, rfl⟩
  have h := virFil_map_le_of_creation LinearMap.id F' hm hv hs p n
  intro x hx
  have hx' : (x : VirUniv L.c) ∈ F' p n :=
    h (Submodule.mem_map.mpr ⟨x, hx, rfl⟩)
  obtain ⟨y, hy, hxy⟩ := Submodule.mem_map.mp hx'
  have he : y = x := Subtype.ext hxy
  exact he ▸ hy

/-- OPEN for general `L`: the vacuum class has filtration degree `0` and each Virasoro
creation mode raises class filtration degree by at most one. -/
structure ClassGeneratorFiltration (S : BRSTKahlerGeometry L)
    (hp : ∀ n, IsPosOn (S.geometry n).P ⊤) : Prop where
  vacuum : universalVacuum L ∈ S.generatorPullback hp 0 0
  creation : ∀ (n : ℤ) (p i : ℕ) (x : UniversalWeight L n),
    x ∈ S.generatorPullback hp n p →
      universalCreation L n i x ∈ S.generatorPullback hp (n + i + 2) (p + 1)

/-- The generator tests imply every universal PBW-prefix inclusion. -/
theorem universalClassFiltered_of_generators (S : BRSTKahlerGeometry L)
    (hp : ∀ n, IsPosOn (S.geometry n).P ⊤) (hgen : ClassGeneratorFiltration L S hp) :
    S.UniversalClassFiltered := by
  intro n hp' p
  rw [Submodule.map_le_iff_le_comap]
  apply universalPrefix_le_of_generators L (S.generatorPullback hp)
  · intro n p q hpq
    exact Submodule.comap_mono (S.generatorCohomPrefix_mono hp n hpq)
  · exact hgen.vacuum
  · exact hgen.creation

/-! ### The metric bridge -/

/-- `GUData` on every positive model. -/
structure BRSTGUData (S : BRSTKahlerGeometry L) where
  data : ∀ n (hp : IsPosOn (S.geometry n).P ⊤), GUData (S.model n hp)

/-- The universal Virasoro conjugation restricted to one weight. -/
def universalConjWeight (n : ℤ) :
    UniversalWeight L n →ₛₗ[starRingEnd ℂ] UniversalWeight L n where
  toFun x := ⟨(VOA.virasoroUniversalRealStructure L.lam_spec
      (VirGradedUnitarity.boundaryBackgroundCharge_fixed L.m)).rho x,
    realStructure_mem_grading _ x.property⟩
  map_add' x y := Subtype.ext ((VOA.virasoroUniversalRealStructure L.lam_spec
      (VirGradedUnitarity.boundaryBackgroundCharge_fixed L.m)).map_add x y)
  map_smul' c x := Subtype.ext ((VOA.virasoroUniversalRealStructure L.lam_spec
      (VirGradedUnitarity.boundaryBackgroundCharge_fixed L.m)).antilinear c x)

/-- On harmonic representatives of universal classes: form = normalized simple form,
conjugation = universal conjugation. -/
structure UniversalImageMetric (S : BRSTKahlerGeometry L) (G : BRSTGUData L S) : Prop where
  form : ∀ n hp (x y : UniversalWeight L n),
    LiRadical.gradedForm (Bsimp L.c) n
        (simpleWeightProjection L n x) (simpleWeightProjection L n y) =
      (G.data n hp).B (S.universalHarmonic n hp x) (S.universalHarmonic n hp y)
  rho : ∀ n hp (x : UniversalWeight L n),
    ((S.universalHarmonic n hp (universalConjWeight L n x) : relativeWeight L n)) =
      (G.data n hp).ρ (S.universalHarmonic n hp x)

/-- OPEN for general `L`: vacuum normalization on the harmonic vacuum class. -/
def HarmonicVacuumNormalized (S : BRSTKahlerGeometry L) (G : BRSTGUData L S) : Prop :=
  ∀ hp : IsPosOn (S.geometry 0).P ⊤,
    (G.data 0 hp).B (S.universalHarmonic 0 hp (vacuumWeight L.c))
      (S.universalHarmonic 0 hp (vacuumWeight L.c)) = 1

/-- OPEN for general `L`: `L_{-i-2}` is adjoint to `L_{i+2}` on harmonic universal classes. -/
def HarmonicCreationAdjoint (S : BRSTKahlerGeometry L) (G : BRSTGUData L S) : Prop :=
  ∀ (i : ℕ) (n m : ℤ) (hpn : IsPosOn (S.geometry n).P ⊤) (hpm : IsPosOn (S.geometry m).P ⊤)
    (x : UniversalWeight L n) (y : UniversalWeight L m)
    (hx : Lop L.c (-(i : ℤ) - 2) x ∈ (virasoroVOA L.c).grading m)
    (hy : Lop L.c ((i : ℤ) + 2) y ∈ (virasoroVOA L.c).grading n),
    (G.data m hpm).B (S.universalHarmonic m hpm ⟨_, hx⟩) (S.universalHarmonic m hpm y) =
      (G.data n hpn).B (S.universalHarmonic n hpn x) (S.universalHarmonic n hpn ⟨_, hy⟩)

/-- OPEN for general `L`: harmonic representatives of creation-word classes are `ρ`-fixed. -/
def HarmonicWordsReal (S : BRSTKahlerGeometry L) (G : BRSTGUData L S) : Prop :=
  ∀ n hp (w : List ℕ) (hw : negWordVir L.c w ∈ (virasoroVOA L.c).grading n),
    (G.data n hp).ρ (S.universalHarmonic n hp ⟨_, hw⟩) = S.universalHarmonic n hp ⟨_, hw⟩

/-- Reality of word classes gives agreement of the conjugations on all universal classes. -/
theorem harmonicConjugation_of_words (S : BRSTKahlerGeometry L) (G : BRSTGUData L S)
    (h : HarmonicWordsReal L S G) (n : ℤ) (hp : IsPosOn (S.geometry n).P ⊤)
    (x : UniversalWeight L n) :
    ((S.universalHarmonic n hp (universalConjWeight L n x) : relativeWeight L n)) =
      (G.data n hp).ρ (S.universalHarmonic n hp x) := by
  let W : Set (VirUniv L.c) :=
    {x | ∃ ws : List ℕ, (energyVir ws : ℤ) = n ∧ negWordVir L.c ws = x}
  have hT : Submodule.span ℂ (((↑) : Submodule.span ℂ W → VirUniv L.c) ⁻¹' W) = ⊤ :=
    Submodule.span_span_coe_preimage
  exact conj_agree_of_span (U := UniversalWeight L n) (X := relativeWeight L n)
    (universalConjWeight L n) (G.data n hp).ρ
    ((S.model n hp).harm.subtype.comp (S.universalHarmonic n hp)) _ hT
    (fun z hz => by
      obtain ⟨ws, -, hws⟩ := hz
      apply Subtype.ext
      change virBasisConj L.c (z : VirUniv L.c) = z
      rw [← hws]
      exact virBasisConj_negWord L.lam_spec
        (VirGradedUnitarity.boundaryBackgroundCharge_fixed L.m) ws)
    (fun z hz => by
      obtain ⟨ws, -, hws⟩ := hz
      obtain ⟨z, hzmem⟩ := z
      change negWordVir L.c ws = z at hws
      subst hws
      exact h n hp ws hzmem) x

/-- Weightwise uniqueness of the normalized Virasoro form turns normalization, adjointness and
word reality into the full metric agreement. -/
theorem universalImageMetric_of_invariance (S : BRSTKahlerGeometry L) (G : BRSTGUData L S)
    (hpAll : ∀ n, IsPosOn (S.geometry n).P ⊤)
    (hnorm : HarmonicVacuumNormalized L S G) (hadj : HarmonicCreationAdjoint L S G)
    (hwords : HarmonicWordsReal L S G) : UniversalImageMetric L S G where
  form n hp x y := by
    have h := weightForm_eq_Bsimp (c := L.c)
      (fun k => ((G.data k (hpAll k)).B.compl₁₂
        ((S.model k (hpAll k)).harm.subtype.comp (S.universalHarmonic k (hpAll k)))
        ((S.model k (hpAll k)).harm.subtype.comp (S.universalHarmonic k (hpAll k)))))
      (hnorm (hpAll 0))
      (fun i n m x y hx hy => hadj i n m (hpAll n) (hpAll m) x y hx hy) n x y
    exact h.symm
  rho n hp x := harmonicConjugation_of_words L S G hwords n hp x

end

end VOA.TwoSeries
