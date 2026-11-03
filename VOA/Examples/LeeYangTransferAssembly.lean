import VOA.Examples.LeeYangTransferAssemblyInputs

/-!
# Affine graded unitarity implies Lee--Yang graded unitarity, conditional assembly

The remaining mathematical inputs are exactly `OpenInputs`. The proof uses
actual coset injectivity, positive finite-dimensional relative Hodge theory,
the leading-cohomology bound, the two explicit character identities, and
filtered isometric transfer. No positivity or nondegeneracy on the target is
assumed. This is a conditional theorem, not a discharge of the open inputs.
-/
namespace VOA.LeeYangTransferAssembly
open GradedUnitaryCohomology LeeYangCosetTransfer
open VirSimple VirQuotForm VirGoodFil VirGradedUnitarity LeeYang
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
noncomputable section

/-- A zero-dimensional harmonic degree vanishes in a finite complex. -/
theorem harmonicDegree_eq_bot {K : Type*} [AddCommGroup K] [Module ℂ K]
    [FiniteDimensional ℂ K] (C : KahlerComplex K) (a : ℤ × ℤ)
    (h : Module.finrank ℂ (C.harmDeg a) = 0) : C.harmDeg a = ⊥ :=
  (Submodule.finrank_eq_zero (R := ℂ) (M := K) (S := C.harmDeg a)).mp h

/-- The leading-character identity forces integral `R` on ghost-zero harmonics;
odd-degree vanishing is not an extra hypothesis of the assembled theorem. -/
theorem integralHarmonicSupport_of_symbols (S : ConcreteKahlerGeometry)
    (hs : LeadingInvariantSymbolDimension S) (n : ℤ)
    (hp : IsPosOn (S.geometry n).P ⊤) : IntegralHarmonicSupport (S.model n hp) := by
  intro p
  have hdim := (S.model n hp).finrank_harmDeg_le_lead (2 * (p : ℤ) + 1, 0)
  rw [hs n hp, leadingCoefficient_odd] at hdim
  exact harmonicDegree_eq_bot (K := relativeWeight n) (S.model n hp)
    (2 * (p : ℤ) + 1, 0) (Nat.eq_zero_of_le_zero hdim)

/-- Harmonic lifting preserves injectivity of a family of cohomology classes. -/
theorem harmonicLiftCyclesVector_injective {K E : Type*}
    [AddCommGroup K] [Module ℂ K] [FiniteDimensional ℂ K]
    [AddCommGroup E] [Module ℂ E] (C : KahlerComplex K)
    (f : E →ₗ[ℂ] LinearMap.ker C.D)
    (hf : Function.Injective (cycleClassOfCycles C.D f)) :
    Function.Injective (C.harm.subtype.comp (harmonicLiftCyclesMap C f)) := by
  intro x y hxy
  have hh : harmonicLiftCyclesMap C f x = harmonicLiftCyclesMap C f y :=
    Subtype.ext hxy
  apply hf
  have hc := congrArg (harmonicToCohomology C.D C.Dadj) hh
  change ((harmonicToCohomology C.D C.Dadj).comp (harmonicLiftCyclesMap C f)) x =
    ((harmonicToCohomology C.D C.Dadj).comp (harmonicLiftCyclesMap C f)) y at hc
  rw [harmonicLiftCyclesMap_class] at hc
  exact hc

/-- Cycle-level form of the leading-dimension squeeze, avoiding any arbitrary
identification of the concrete quotient with a surrogate cohomology space. -/
theorem harmonicLiftCycles_maps_eq_of_finrank_squeeze {K E : Type*}
    [AddCommGroup K] [Module ℂ K] [FiniteDimensional ℂ K]
    [AddCommGroup E] [Module ℂ E] (C : KahlerComplex K)
    (P : ℕ → Submodule ℂ E) (f : E →ₗ[ℂ] LinearMap.ker C.D)
    (hf : Function.Injective (cycleClassOfCycles C.D f))
    (hfiltered : ∀ p : ℕ, (P p).map (cycleClassOfCycles C.D f) ≤
      C.cohomFilt (KahlerComplex.rowSet (Finset.Icc 0 (2 * (p : ℤ))) 0))
    (hcharacter : ∀ p : ℕ,
      (∑ j ∈ Finset.Icc 0 (2 * (p : ℤ)), Module.finrank ℂ (C.leadCohom (j, 0))) =
        Module.finrank ℂ (P p)) :
    ∀ p : ℕ, (P p).map (C.harm.subtype.comp (harmonicLiftCyclesMap C f)) =
      C.flag 0 (2 * (p : ℤ)) := by
  apply harmonic_maps_eq_of_finrank_squeeze C P (harmonicLiftCyclesMap C f)
  · rw [harmonicLiftCyclesMap_class]
    exact hf
  · intro p
    rw [harmonicLiftCyclesMap_class]
    exact hfiltered p
  · exact hcharacter

/-- The canonical harmonic representative map remains injective. -/
theorem harmonicCosetVector_injective (ident : CosetIdentification) (S : ConcreteKahlerGeometry)
    (n : ℤ) (hp : IsPosOn (S.geometry n).P ⊤) :
    Function.Injective (harmonicCosetVector ident S n hp) := by
  exact harmonicLiftCyclesVector_injective (K := relativeWeight n) (E := LeeYangWeight n)
    (S.model n hp) (modelCosetCycles ident S n hp) (modelCosetClass_injective ident S n hp)

/-- The dimension squeeze gives exact filtered images of the canonical harmonic
coset map. Neither strictness nor a filtered isomorphism is an input. -/
theorem harmonicCosetMap_filteredIso (inputs : OpenInputs) (n : ℤ)
    (hp : IsPosOn (inputs.kahler.geometry n).P ⊤) :
    ∀ p : ℕ, ((virGradedFlag leeYangC).pieceIn p n).map
        (harmonicCosetVector inputs.identification inputs.kahler n hp) =
      (inputs.kahler.model n hp).flag 0 (2 * (p : ℤ)) := by
  apply harmonicLiftCycles_maps_eq_of_finrank_squeeze
    (K := relativeWeight n) (E := LeeYangWeight n) (inputs.kahler.model n hp)
    (fun p => (virGradedFlag leeYangC).pieceIn p n)
    (modelCosetCycles inputs.identification inputs.kahler n hp)
  · exact modelCosetClass_injective inputs.identification inputs.kahler n hp
  · intro p
    exact inputs.filtered n hp p
  · intro p
    rw [inputs.character n p]
    exact Finset.sum_congr rfl fun j _ => inputs.symbols n hp j

/-- An injective map with exact piece image is an isomorphism of those pieces. -/
def filteredPieceEquiv {E K : Type*} [AddCommGroup E] [Module ℂ E]
    [AddCommGroup K] [Module ℂ K] (i : E →ₗ[ℂ] K) (hi : Function.Injective i)
    (P : Submodule ℂ E) (F : Submodule ℂ K) (hmap : P.map i = F) : P ≃ₗ[ℂ] F :=
  (Submodule.equivMapOfInjective i hi P).trans (LinearEquiv.ofEq _ _ hmap)

/-- The actual filtered linear isomorphism at every weight and PBW length. -/
def harmonicCosetPieceEquiv (inputs : OpenInputs) (n : ℤ)
    (hp : IsPosOn (inputs.kahler.geometry n).P ⊤) (p : ℕ) :
    ((virGradedFlag leeYangC).pieceIn p n) ≃ₗ[ℂ]
      ((inputs.kahler.model n hp).flag 0 (2 * (p : ℤ))) :=
  filteredPieceEquiv (E := LeeYangWeight n) (K := relativeWeight n)
    (harmonicCosetVector inputs.identification inputs.kahler n hp)
    (harmonicCosetVector_injective inputs.identification inputs.kahler n hp)
    ((virGradedFlag leeYangC).pieceIn p n) ((inputs.kahler.model n hp).flag 0 (2 * (p : ℤ)))
    (harmonicCosetMap_filteredIso inputs n hp p)

/-- Assembled affine-to-Lee--Yang implication on the actual endpoint VOAs.
OPEN: the separately named fields of `OpenInputs`. Auxiliary below-critical GU,
coset simplicity, weight compatibility, harmonic representatives, the squeeze,
odd harmonic vanishing, and transfer are all discharged in the proof chain. -/
theorem leeYang_gradedUnitary_of_affine
    (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    (inputs : OpenInputs) : VirGradedUnitary leeYangC leeYangRealStructure := by
  intro n
  let hp := inputs.weakGU hA auxiliaryGradedUnitary n
  let C := inputs.kahler.model n hp
  let G := inputs.gu.data n hp
  let i := harmonicCosetVector inputs.identification inputs.kahler n hp
  have hi : Function.Injective i :=
    harmonicCosetVector_injective inputs.identification inputs.kahler n hp
  apply gradedUnitaryAt_of_harmonic_filteredIso C G (virGradedFlag leeYangC) n
    (LiRadical.gradedForm (Bsimp leeYangC) n) (gradedSesq (Bsimp leeYangC) leeYangRealStructure n)
    i hi
  · exact inputs.metric.form n hp
  · intro x y
    rw [G.h_eq, ← inputs.metric.rho n hp x, ← inputs.metric.form n hp]
    rfl
  · exact harmonicCosetMap_filteredIso inputs n hp
  · exact integralHarmonicSupport_of_symbols inputs.kahler inputs.symbols n hp

end
end VOA.LeeYangTransferAssembly
