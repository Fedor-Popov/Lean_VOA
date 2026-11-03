import VOA.Examples.LeeYangTransferAssemblyCharacter
import VOA.Examples.LeeYangTransferAssemblyRepresentative
import VOA.Examples.LeeYangTransferAssemblyGeometry
import VOA.Examples.LeeYangTransferAssemblyHodge

/-!
# Precisely named open inputs for affine-to-Lee--Yang transfer

All carriers, differentials, forms on the two endpoint VOAs, real structures,
and endpoint filtrations are fixed. No input assumes Lee--Yang positivity,
prefix nondegeneracy, or a filtered isomorphism. The latter is proved by the
character squeeze in `LeeYangTransferAssembly`.

The leading dimension input combines the leading-Koszul comparison
with the invariant-symbol character identity. It is stated directly for the
leading cohomology of the concrete relative complex; an arbitrary surrogate
invariant space is not used.

Status (later files): for the main geometry `ConcreteHodge.endpointKahler hA` the fields
`kahler`, `weakGU`, `gu`, `symbols` and `character` are constructed or proved (see the
docstrings below). `identification`, and with it `metric` and `filtered`, is not constructed
anywhere; the main theorem `AdamovicSymbol.leeYang_gradedUnitary_of_affine` does not use `OpenInputs`.
-/
namespace VOA.LeeYangTransferAssembly
open Sl2CosetConcrete GradedUnitaryCohomology LeeYangCosetTransfer
open VirSimple VirQuotForm VirGoodFil LeeYang
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
noncomputable section

/-- [H,C] Homogeneous differential pieces, adjoints and Kähler relations
on the actual relative weight spaces, before assuming metric positivity.
Constructed: `ConcreteHodge.sp2Kahler` (`BRSTKahlerGhost.lean`), in the main
`ConcreteHodge.endpointKahler hA` (`InvariantSymbolBridge.lean`). -/
structure ConcreteKahlerGeometry where
  /-- The tensor-derived `R` splitting and modified metric (constructed concretely in
  `ConcreteHodge.sp2Kahler`). -/
  geometry : ∀ n : ℤ, KahlerGeometry (relativeWeight n)
  /-- Their sum is literally the concrete BRST differential. -/
  differential : ∀ n, (geometry n).Qm + (geometry n).Sm = relativeDifferential n
  /-- The second coordinate of the bigrading is the actual BRST ghost number. -/
  ghost : ∀ n a, (geometry n).deg a ≤
    (leeYangBRSTComplex.ghost a.2).comap (relativeWeight n).subtype

/-- [H] Weak graded unitarity of the relative tensor complex, using
corrected GU of the simple A factor and ordinary-current GU of the auxiliary U.
This states positivity of the modified complex metric, not positivity on the
Lee--Yang VOA. The auxiliary premise is discharged in the final assembly.
Proved for the concrete geometries: `ConcreteHodge.concreteKahler_weakGU`
(`ConcreteHodgeAssembly.lean`). -/
def WeakGUTensorPositivity (S : ConcreteKahlerGeometry) : Prop :=
  GradedUnitary affineForm affineRealStructure affineFlag →
  GradedUnitary auxiliaryForm auxiliaryRealStructure auxiliaryFlag →
  ∀ n, IsPosOn (S.geometry n).P ⊤

/-- Supply the positivity proved from the affine input to the verified Hodge theory. -/
def ConcreteKahlerGeometry.model (S : ConcreteKahlerGeometry) (n : ℤ)
    (hp : IsPosOn (S.geometry n).P ⊤) : KahlerComplex (relativeWeight n) :=
  (S.geometry n).toKahler hp

theorem ConcreteKahlerGeometry.model_D (S : ConcreteKahlerGeometry) (n : ℤ)
    (hp : IsPosOn (S.geometry n).P ⊤) : (S.model n hp).D = relativeDifferential n :=
  S.differential n

/-- Rewriting an equal differential gives the same cycle space. -/
def cyclesCongr {K : Type*} [AddCommGroup K] [Module ℂ K]
    (d d' : K →ₗ[ℂ] K) (hd : d = d') : LinearMap.ker d ≃ₗ[ℂ] LinearMap.ker d' := by
  subst d'
  exact LinearEquiv.refl ℂ _

/-- Transport a family of cycles across equality of differentials. -/
def transportCyclesMap {K E : Type*} [AddCommGroup K] [Module ℂ K]
    [AddCommGroup E] [Module ℂ E] (d d' : K →ₗ[ℂ] K) (hd : d = d')
    (f : E →ₗ[ℂ] LinearMap.ker d) : E →ₗ[ℂ] LinearMap.ker d' :=
  (cyclesCongr d d' hd).toLinearMap.comp f

theorem transportedCycles_class_injective {K E : Type*} [AddCommGroup K] [Module ℂ K]
    [AddCommGroup E] [Module ℂ E] (d d' : K →ₗ[ℂ] K) (hd : d = d')
    (f : E →ₗ[ℂ] LinearMap.ker d)
    (hexact : ∀ x, f x ∈ boundariesInCycles d → x = 0) :
    Function.Injective (cycleClassOfCycles d' (transportCyclesMap d d' hd f)) := by
  subst d'
  exact cycleClassOfCycles_injective_of_exact d f hexact

/-- An exact actual coset cycle has zero source vector, by the already verified
absolute cohomology injection. This uses no relative-to-absolute injectivity. -/
theorem cosetCycles_exact_zero (ident : CosetIdentification) (n : ℤ)
    (x : LeeYangWeight n)
    (hb : cosetWeightCycles ident n x ∈
      boundariesInCycles (K := relativeWeight n) (relativeDifferential n)) :
    x = 0 := by
  have ha := weightBoundary_toAbsolute n (cosetWeightCycles ident n x) hb
  rw [cosetWeightCycles_toAbsolute] at ha
  have hz : leeYangCosetToH0 (ident.equiv.symm x) = 0 := Subtype.ext ha
  have hi : ident.equiv.symm x = 0 := ident.cosetToH0_injective (by simpa using hz)
  apply Subtype.ext
  exact ident.equiv.symm.injective (by simpa using hi)

/-- The actual relative cycles in the Kähler model, transported only across
the proved equality of differentials. -/
def modelCosetCycles (ident : CosetIdentification) (S : ConcreteKahlerGeometry)
    (n : ℤ) (hp : IsPosOn (S.geometry n).P ⊤) :=
  transportCyclesMap (K := relativeWeight n) (E := LeeYangWeight n)
    (relativeDifferential n) (S.model n hp).D
    (S.model_D n hp).symm (cosetWeightCycles ident n)

/-- The concrete coset class in the Kähler model, transported only across the
proved equality of differentials. -/
def modelCosetClass (ident : CosetIdentification) (S : ConcreteKahlerGeometry)
    (n : ℤ) (hp : IsPosOn (S.geometry n).P ⊤) :=
  cycleClassOfCycles (K := relativeWeight n) (M := LeeYangWeight n)
    (S.model n hp).D (modelCosetCycles ident S n hp)

/-- The proof-valued specialization keeps the exact concrete quotient instances
selected by the generic injection theorem. -/
def modelCosetClass_injective (ident : CosetIdentification) (S : ConcreteKahlerGeometry)
    (n : ℤ) (hp : IsPosOn (S.geometry n).P ⊤) :=
  transportedCycles_class_injective (K := relativeWeight n) (E := LeeYangWeight n)
    (relativeDifferential n) (S.model n hp).D (S.model_D n hp).symm
    (cosetWeightCycles ident n) (fun x hx => by
      obtain ⟨y, hy⟩ := hx
      exact cosetCycles_exact_zero ident n x ⟨y, hy⟩)

/-- Harmonic lifting of a linear family of cycles, in abstract module instances. -/
def harmonicLiftCyclesMap {K E : Type*} [AddCommGroup K] [Module ℂ K]
    [FiniteDimensional ℂ K] [AddCommGroup E] [Module ℂ E]
    (C : KahlerComplex K) (f : E →ₗ[ℂ] LinearMap.ker C.D) : E →ₗ[ℂ] C.harm :=
  (harmonicEquivCohomology C.P C.pos C.herm C.D C.Dadj C.D_sq C.adj_D).symm.toLinearMap.comp
    (cycleClassOfCycles C.D f)

theorem harmonicLiftCyclesMap_class {K E : Type*} [AddCommGroup K] [Module ℂ K]
    [FiniteDimensional ℂ K] [AddCommGroup E] [Module ℂ E]
    (C : KahlerComplex K) (f : E →ₗ[ℂ] LinearMap.ker C.D) :
    (harmonicToCohomology C.D C.Dadj).comp (harmonicLiftCyclesMap C f) =
      cycleClassOfCycles C.D f := by
  ext x
  exact (harmonicEquivCohomology C.P C.pos C.herm C.D C.Dadj C.D_sq C.adj_D).apply_symm_apply _

/-- The unique harmonic representative of the actual coset class. Existence is
the finite-dimensional Hodge theorem, not an additional open input. -/
def harmonicCosetMap (ident : CosetIdentification) (S : ConcreteKahlerGeometry)
    (n : ℤ) (hp : IsPosOn (S.geometry n).P ⊤) :=
  harmonicLiftCyclesMap (K := relativeWeight n) (E := LeeYangWeight n)
    (S.model n hp) (modelCosetCycles ident S n hp)

/-- The class of the unique harmonic representative is the original class.
The proposition is inferred from the proved abstract identity. -/
def harmonicCosetMap_class (ident : CosetIdentification) (S : ConcreteKahlerGeometry)
    (n : ℤ) (hp : IsPosOn (S.geometry n).P ⊤) :=
  harmonicLiftCyclesMap_class (K := relativeWeight n) (E := LeeYangWeight n)
    (S.model n hp) (modelCosetCycles ident S n hp)

/-- Harmonic representatives as actual vectors in the relative weight complex. -/
def harmonicCosetVector (ident : CosetIdentification) (S : ConcreteKahlerGeometry)
    (n : ℤ) (hp : IsPosOn (S.geometry n).P ⊤) : LeeYangWeight n →ₗ[ℂ] relativeWeight n :=
  (S.model n hp).harm.subtype.comp (harmonicCosetMap ident S n hp)

/-- OPEN [S]: the actual coset map is filtered for the Virasoro PBW flag and
the relative complex's nonnegative `R` filtration at ghost number zero.
This is inclusion only, never surjectivity or strictness. -/
def CosetFiltrationCompatibility (ident : CosetIdentification) (S : ConcreteKahlerGeometry) :
    Prop :=
  ∀ n (hp : IsPosOn (S.geometry n).P ⊤) p,
    ((virGradedFlag leeYangC).pieceIn p n).map (modelCosetClass ident S n hp) ≤
      (S.model n hp).cohomFilt (KahlerComplex.rowSet (Finset.Icc 0 (2 * (p : ℤ))) 0)

/-- [K,I] The leading Koszul computation together with the invariant-symbol
character: the actual leading cohomology has coefficient `G_R(n)` at `(2R,0)`
and vanishes at the other ghost-zero filtration degrees.
Proved for `ConcreteHodge.endpointKahler hA` (every `hA`) by
`ConcreteHodge.leadingInvariantSymbolDimension_of_bound` (`InvariantSymbolBridge.lean`) from
the proved bound `TwoSeries.leeYang_symbolBound hA` (`TwoSeriesLeeYang.lean`). -/
def LeadingInvariantSymbolDimension (S : ConcreteKahlerGeometry) : Prop :=
  ∀ n (hp : IsPosOn (S.geometry n).P ⊤) j,
    Module.finrank ℂ ((S.model n hp).leadCohom (j, 0)) = leadingCoefficient n j

/-- [H] The invariant form and conjugation on the concrete relative
complex satisfy the existing `GUData` identities.
Constructed: `ConcreteHodge.sp2GUData0` (`BRSTKahlerConj.lean`). -/
structure ConcreteGUData (S : ConcreteKahlerGeometry) where
  data : ∀ n (hp : IsPosOn (S.geometry n).P ⊤), GUData (S.model n hp)

/-- OPEN [S]: normalized invariant form and real structure agree on the unique
harmonic representatives of the actual coset classes. -/
structure HarmonicMetricAgreement (ident : CosetIdentification) (S : ConcreteKahlerGeometry)
    (G : ConcreteGUData S) : Prop where
  form : ∀ n hp x y,
    LiRadical.gradedForm (Bsimp leeYangC) n x y =
      (G.data n hp).B (harmonicCosetVector ident S n hp x) (harmonicCosetVector ident S n hp y)
  rho : ∀ n hp x,
    harmonicCosetVector ident S n hp (leeYangRhoWeight n x) =
      (G.data n hp).ρ (harmonicCosetVector ident S n hp x)

/-- Named residual nodes. Every data field is tied to the actual coset, relative
BRST differential, canonical endpoint forms and flags, or the fixed character.
No field asserts the target graded-unitarity statement or a filtered isomorphism. -/
structure OpenInputs where
  identification : CosetIdentification
  kahler : ConcreteKahlerGeometry
  weakGU : WeakGUTensorPositivity kahler
  gu : ConcreteGUData kahler
  metric : HarmonicMetricAgreement identification kahler gu
  filtered : CosetFiltrationCompatibility identification kahler
  symbols : LeadingInvariantSymbolDimension kahler
  character : LeeYangPBWCharacter

end
end VOA.LeeYangTransferAssembly
