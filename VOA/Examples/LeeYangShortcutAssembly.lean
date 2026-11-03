import VOA.Examples.LeeYangShortcutHodge
import VOA.Examples.LeeYangShortcutGenerators
import VOA.Examples.LeeYangShortcutUniqueness

/-!
# Affine-to-Lee--Yang transfer through the actual Virasoro image

The external coset identification (`CosetIdentification`) of the old assembly is
**absent**. The coset stress tensor gives a VOA map from the universal Virasoro
VOA at `c = -22/5` into the coset, hence into ghost-number-zero cohomology
(`LeeYangShortcutVirasoro`, `LeeYangShortcutImage`). Its kernel is a proper ideal
(the vacuum class survives), so it lies in the maximal ideal and the image
surjects onto `L(-22/5)` prefix by prefix. The dimension squeeze then proves
that this surjection is injective and that the image exhausts every cohomology
prefix (`gradedUnitaryAt_of_class_family`).

Retained unchanged from the old `OpenInputs`: `kahler`, `weakGU`, `gu`,
`symbols`, `character`. The old coset-dependent `filtered` and `metric` fields
are replaced by statements about the *universal Virasoro classes*, which exist
without any identification:

* `ClassGeneratorFiltration` — the vacuum class has filtration degree `0`, and
  each creation mode `L_{-i-2}` raises the class filtration degree by at most
  one. This implies `UniversalClassFiltered` (every universal PBW prefix maps
  into the corresponding cohomology filtration step).
* `HarmonicVacuumNormalized`, `HarmonicCreationAdjoint` — on harmonic
  representatives of universal classes, the complex's form is vacuum-normalized
  and `L_{-i-2}` is adjoint to `L_{i+2}`. Weightwise uniqueness
  (`weightForm_eq_Bsimp`) turns these into agreement with the normalized simple
  Virasoro form.
* `HarmonicWordsReal` — the harmonic representative of each creation-word class
  is fixed by the complex's conjugation. This gives agreement with the
  universal, hence the Lee--Yang, conjugation.

No field asserts positivity, nondegeneracy, injectivity, or a filtered
isomorphism; all of those are proved.
-/

namespace VOA.LeeYangShortcut

open LeeYangTransferAssembly LeeYangCosetTransfer GradedUnitaryCohomology
open VirModule VirSimple VirGoodFil VirQuotForm VirGradedUnitarity LeeYang

noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000

/-! ### The universal Virasoro conjugation at a fixed weight -/

theorem leeYang_lam_spec :
    1 - 12 * VirGradedUnitarity.boundaryBackgroundCharge 2 ^ 2 = leeYangC :=
  (VirGradedUnitarity.boundaryBackgroundCharge_spec 2).trans
    VirGradedUnitarity.boundaryCharge_two_eq_leeYangC

/-- The universal Virasoro real structure at the Lee--Yang charge. -/
abbrev universalRealStructure : RealStructure (virasoroVOA leeYangC) :=
  VOA.virasoroUniversalRealStructure leeYang_lam_spec
    (VirGradedUnitarity.boundaryBackgroundCharge_fixed 2)

/-- The universal conjugation (it fixes every PBW word) restricted to one weight. -/
def universalConjWeight (n : ℤ) :
    UniversalWeight n →ₛₗ[starRingEnd ℂ] UniversalWeight n where
  toFun x := ⟨universalRealStructure.rho x, realStructure_mem_grading _ x.property⟩
  map_add' x y := Subtype.ext (universalRealStructure.map_add x y)
  map_smul' c x := Subtype.ext (universalRealStructure.antilinear c x)

/-- The simple projection intertwines the universal and the Lee--Yang conjugations. -/
theorem simpleWeightProjection_conj (n : ℤ) (x : UniversalWeight n) :
    simpleWeightProjection n (universalConjWeight n x) =
      leeYangRhoWeight n (simpleWeightProjection n x) :=
  Subtype.ext rfl

/-! ### The two residual bridges, stated on universal classes -/

/-- The harmonic representative of the class of a universal Virasoro state. -/
def universalHarmonic (S : ConcreteKahlerGeometry) (n : ℤ)
    (hp : IsPosOn (S.geometry n).P ⊤) : UniversalWeight n →ₗ[ℂ] (S.model n hp).harm :=
  harmonicClassLift (K := relativeWeight n) (S.model n hp) (modelUniversalClass S n hp)

/-- The class of each universal PBW prefix of length `≤ p` lies in the
cohomology filtration step `R ≤ p` at ghost number zero. Inclusion only.
Proved for the main geometry: `ConcreteHodge.endpointKahler_filtered`
(`InvariantSymbolBridge.lean`). -/
def UniversalClassFiltered (S : ConcreteKahlerGeometry) : Prop :=
  ∀ n (hp : IsPosOn (S.geometry n).P ⊤) p,
    (universalPrefix p n).map (modelUniversalClass S n hp) ≤
      (S.model n hp).cohomFilt (KahlerComplex.rowSet (Finset.Icc 0 (2 * (p : ℤ))) 0)

/-- OPEN: on harmonic representatives of the universal Virasoro classes, the
complex's form is the normalized Virasoro form (evaluated on the simple
projections) and its conjugation is the universal Virasoro conjugation.
The `form` clause includes vacuum normalization (`x = y = |0⟩`), so the
simultaneous sign change `B ↦ -B, ρ ↦ -ρ` of `signTwistGUData` does not
satisfy it vacuously. -/
structure UniversalImageMetric (S : ConcreteKahlerGeometry) (G : ConcreteGUData S) :
    Prop where
  form : ∀ n hp (x y : UniversalWeight n),
    LiRadical.gradedForm (Bsimp leeYangC) n
        (simpleWeightProjection n x) (simpleWeightProjection n y) =
      (G.data n hp).B (universalHarmonic S n hp x) (universalHarmonic S n hp y)
  rho : ∀ n hp (x : UniversalWeight n),
    ((universalHarmonic S n hp (universalConjWeight n x) : relativeWeight n)) =
      (G.data n hp).ρ (universalHarmonic S n hp x)

/-- The shortcut inputs other than the metric bridge. There is **no** coset
identification. -/
structure ShortcutCoreInputs where
  kahler : ConcreteKahlerGeometry
  weakGU : WeakGUTensorPositivity kahler
  gu : ConcreteGUData kahler
  symbols : LeadingInvariantSymbolDimension kahler
  character : LeeYangPBWCharacter
  filtered : UniversalClassFiltered kahler

/-- The sesquilinear clause follows from the form and conjugation clauses. -/
theorem universalImage_sesq (S : ConcreteKahlerGeometry) (G : ConcreteGUData S)
    (hm : UniversalImageMetric S G) (n : ℤ) (hp : IsPosOn (S.geometry n).P ⊤)
    (x y : UniversalWeight n) :
    gradedSesq (Bsimp leeYangC) leeYangRealStructure n
        (simpleWeightProjection n x) (simpleWeightProjection n y) =
      (G.data n hp).h (universalHarmonic S n hp x) (universalHarmonic S n hp y) := by
  rw [(G.data n hp).h_eq, ← hm.rho n hp x, ← hm.form n hp]
  change (Bsimp leeYangC).form (leeYangRealStructure.rho _) _ =
    (Bsimp leeYangC).form ((simpleWeightProjection n (universalConjWeight n x) :
      VirUniv leeYangC ⧸ maxIdealVir leeYangC)) _
  rw [simpleWeightProjection_conj]
  rfl

/-- The leading-dimension and character inputs give the squeeze's upper bound. -/
theorem shortcut_character (inputs : ShortcutCoreInputs) (n : ℤ)
    (hp : IsPosOn (inputs.kahler.geometry n).P ⊤) (p : ℕ) :
    (∑ j ∈ Finset.Icc 0 (2 * (p : ℤ)),
        Module.finrank ℂ ((inputs.kahler.model n hp).leadCohom (j, 0))) =
      Module.finrank ℂ ((virGradedFlag leeYangC).pieceIn p n) := by
  rw [inputs.character n p]
  exact Finset.sum_congr rfl fun j _ => inputs.symbols n hp j

/-- Graded unitarity of Lee--Yang from the core inputs and the metric bridge
stated directly on the harmonic representatives of universal classes. -/
theorem leeYang_gradedUnitary_of_affine_of_imageMetric
    (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    (inputs : ShortcutCoreInputs) (hm : UniversalImageMetric inputs.kahler inputs.gu) :
    VirGradedUnitary leeYangC leeYangRealStructure := by
  intro n
  let hp := inputs.weakGU hA auxiliaryGradedUnitary n
  exact gradedUnitaryAt_of_class_family (K := relativeWeight n)
    (inputs.kahler.model n hp) (inputs.gu.data n hp) (virGradedFlag leeYangC) n
    (LiRadical.gradedForm (Bsimp leeYangC) n)
    (gradedSesq (Bsimp leeYangC) leeYangRealStructure n)
    (modelUniversalClass inputs.kahler n hp) (simpleWeightProjection n)
    (simpleWeightProjection_surjective n) (modelUniversalClass_ker_le inputs.kahler n hp)
    (fun p => universalPrefix p n) (fun p => simpleWeightProjection_prefix p n)
    (universalPrefix_exhaustive n) (inputs.filtered n hp)
    (shortcut_character inputs n hp) (hm.form n hp)
    (universalImage_sesq inputs.kahler inputs.gu hm n hp)
    (integralHarmonicSupport_of_symbols inputs.kahler inputs.symbols n hp)

/-! ### The metric bridge reduced to normalization and invariance -/

/-- The form on harmonic representatives of the universal vacuum class
has value `1`. Proved for the concrete endpoint
geometry (given `hA`, `hB`): `ConcreteHodge.harmonicVacuumNormalized_proved`
(`HarmonicMetricEndpoint.lean`). -/
def HarmonicVacuumNormalized (S : ConcreteKahlerGeometry) (G : ConcreteGUData S) : Prop :=
  ∀ hp : IsPosOn (S.geometry 0).P ⊤,
    (G.data 0 hp).B (universalHarmonic S 0 hp (vacuumWeight leeYangC))
      (universalHarmonic S 0 hp (vacuumWeight leeYangC)) = 1

/-- On harmonic representatives of universal classes, each creation mode
`L_{-i-2}` is adjoint to `L_{i+2}` for the complex's forms at the two weights.
Proved for the concrete endpoint
geometry (given `hA`, `hB`): `ConcreteHodge.harmonicCreationAdjoint_proved`
(`HarmonicMetricEndpoint.lean`). -/
def HarmonicCreationAdjoint (S : ConcreteKahlerGeometry) (G : ConcreteGUData S) : Prop :=
  ∀ (i : ℕ) (n m : ℤ) (hpn : IsPosOn (S.geometry n).P ⊤) (hpm : IsPosOn (S.geometry m).P ⊤)
    (x : UniversalWeight n) (y : UniversalWeight m)
    (hx : Lop leeYangC (-(i : ℤ) - 2) x ∈ (virasoroVOA leeYangC).grading m)
    (hy : Lop leeYangC ((i : ℤ) + 2) y ∈ (virasoroVOA leeYangC).grading n),
    (G.data m hpm).B (universalHarmonic S m hpm ⟨_, hx⟩) (universalHarmonic S m hpm y) =
      (G.data n hpn).B (universalHarmonic S n hpn x) (universalHarmonic S n hpn ⟨_, hy⟩)

/-- OPEN: on harmonic representatives of universal classes, the complex's
conjugation acts as the universal Virasoro conjugation (which fixes every PBW word). -/
def HarmonicConjugationAgreement (S : ConcreteKahlerGeometry) (G : ConcreteGUData S) :
    Prop :=
  ∀ n hp (x : UniversalWeight n),
    ((universalHarmonic S n hp (universalConjWeight n x) : relativeWeight n)) =
      (G.data n hp).ρ (universalHarmonic S n hp x)

/-- (Equivalent form of `HarmonicConjugationAgreement`.) The harmonic
representative of the class of every Virasoro creation word is fixed by the
complex's conjugation. Proved for the concrete endpoint
geometry (given `hA`, `hB`): `ConcreteHodge.harmonicWordsReal_proved`
(`HarmonicMetricEndpoint.lean`). -/
def HarmonicWordsReal (S : ConcreteKahlerGeometry) (G : ConcreteGUData S) : Prop :=
  ∀ n hp (w : List ℕ) (hw : negWordVir leeYangC w ∈ (virasoroVOA leeYangC).grading n),
    (G.data n hp).ρ (universalHarmonic S n hp ⟨_, hw⟩) = universalHarmonic S n hp ⟨_, hw⟩

/-- Two semilinear maps that agree on a spanning set of fixed vectors. -/
theorem conj_agree_of_span {U X : Type*} [AddCommGroup U] [Module ℂ U]
    [AddCommGroup X] [Module ℂ X]
    (σ : U →ₛₗ[starRingEnd ℂ] U) (ρ : X →ₛₗ[starRingEnd ℂ] X) (u : U →ₗ[ℂ] X)
    (T : Set U) (hT : Submodule.span ℂ T = ⊤)
    (hσ : ∀ z ∈ T, σ z = z) (hρ : ∀ z ∈ T, ρ (u z) = u z) (x : U) :
    u (σ x) = ρ (u x) := by
  have h : u.comp σ = ρ.comp u := by
    apply LinearMap.ext_on hT
    intro z hz
    change u (σ z) = ρ (u z)
    rw [hσ z hz, hρ z hz]
  exact LinearMap.congr_fun h x

/-- Since the universal conjugation fixes every creation word, reality of the
word classes gives agreement of the conjugations on all universal classes. -/
theorem harmonicConjugationAgreement_of_words (S : ConcreteKahlerGeometry)
    (G : ConcreteGUData S) (h : HarmonicWordsReal S G) :
    HarmonicConjugationAgreement S G := by
  intro n hp x
  let W : Set (VirUniv leeYangC) :=
    {x | ∃ ws : List ℕ, (energyVir ws : ℤ) = n ∧ negWordVir leeYangC ws = x}
  have hT : Submodule.span ℂ (((↑) : Submodule.span ℂ W → VirUniv leeYangC) ⁻¹' W) = ⊤ :=
    Submodule.span_span_coe_preimage
  exact conj_agree_of_span (U := UniversalWeight n) (X := relativeWeight n)
    (universalConjWeight n) (G.data n hp).ρ
    ((S.model n hp).harm.subtype.comp (universalHarmonic S n hp)) _ hT
    (fun z hz => by
      obtain ⟨ws, -, hws⟩ := hz
      apply Subtype.ext
      change virBasisConj leeYangC (z : VirUniv leeYangC) = z
      rw [← hws]
      exact virBasisConj_negWord leeYang_lam_spec
        (VirGradedUnitarity.boundaryBackgroundCharge_fixed 2) ws)
    (fun z hz => by
      obtain ⟨ws, -, hws⟩ := hz
      obtain ⟨z, hzmem⟩ := z
      change negWordVir leeYangC ws = z at hws
      subst hws
      exact h n hp ws hzmem) x

/-- Weightwise uniqueness of the normalized Virasoro form turns vacuum
normalization and creation-mode adjointness into the full form agreement. -/
theorem universalImageMetric_of_invariance (S : ConcreteKahlerGeometry)
    (G : ConcreteGUData S) (hpAll : ∀ n, IsPosOn (S.geometry n).P ⊤)
    (hnorm : HarmonicVacuumNormalized S G) (hadj : HarmonicCreationAdjoint S G)
    (hrho : HarmonicConjugationAgreement S G) : UniversalImageMetric S G where
  form n hp x y := by
    have h := weightForm_eq_Bsimp (c := leeYangC)
      (fun k => ((G.data k (hpAll k)).B.compl₁₂
        ((S.model k (hpAll k)).harm.subtype.comp (universalHarmonic S k (hpAll k)))
        ((S.model k (hpAll k)).harm.subtype.comp (universalHarmonic S k (hpAll k)))))
      (hnorm (hpAll 0))
      (fun i n m x y hx hy => hadj i n m (hpAll n) (hpAll m) x y hx hy) n x y
    exact h.symm
  rho := hrho

/-- The generator tests (vacuum class of degree `0`, creation modes raise degree
by at most one) imply `UniversalClassFiltered`. -/
theorem universalClassFiltered_of_generators (S : ConcreteKahlerGeometry)
    (hp : ∀ n, IsPosOn (S.geometry n).P ⊤) (hgen : ClassGeneratorFiltration S hp) :
    UniversalClassFiltered S := by
  intro n hp' p
  exact modelUniversalClass_filtered_of_generators S hp hgen p n

/-- The shortcut's inputs. There is **no** coset identification. The filtration
bridge is reduced to the vacuum and creation-mode tests, and the metric bridge
to vacuum normalization, creation-mode adjointness, and `ρ`-reality of the
harmonic representatives of creation-word classes. -/
structure ShortcutInputs where
  kahler : ConcreteKahlerGeometry
  weakGU : WeakGUTensorPositivity kahler
  gu : ConcreteGUData kahler
  symbols : LeadingInvariantSymbolDimension kahler
  character : LeeYangPBWCharacter
  generators : ∀ hp : (∀ n, IsPosOn (kahler.geometry n).P ⊤),
    ClassGeneratorFiltration kahler hp
  vacuumNormalized : HarmonicVacuumNormalized kahler gu
  creationAdjoint : HarmonicCreationAdjoint kahler gu
  wordsReal : HarmonicWordsReal kahler gu

/-- **Graded unitarity of the boundary affine algebra implies graded
unitarity of Lee--Yang, without a coset identification.**
`#print axioms`-clean, conditional on the fields of `ShortcutInputs`. -/
theorem leeYang_gradedUnitary_of_affine'
    (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    (inputs : ShortcutInputs) : VirGradedUnitary leeYangC leeYangRealStructure :=
  have hpAll := inputs.weakGU hA auxiliaryGradedUnitary
  leeYang_gradedUnitary_of_affine_of_imageMetric hA
    { kahler := inputs.kahler
      weakGU := inputs.weakGU
      gu := inputs.gu
      symbols := inputs.symbols
      character := inputs.character
      filtered := universalClassFiltered_of_generators inputs.kahler hpAll
        (inputs.generators hpAll) }
    (universalImageMetric_of_invariance inputs.kahler inputs.gu hpAll
      inputs.vacuumNormalized inputs.creationAdjoint
      (harmonicConjugationAgreement_of_words inputs.kahler inputs.gu inputs.wordsReal))

end
end VOA.LeeYangShortcut
