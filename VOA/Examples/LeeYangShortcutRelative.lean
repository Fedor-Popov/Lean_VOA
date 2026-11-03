import VOA.Examples.LeeYangShortcutImage
import VOA.Examples.LeeYangTransferAssemblyInputs

/-!
# The Virasoro image in each finite relative weight complex

The representative appends the actual auxiliary and ghost vacua to the
universal conformal evaluation. Relative exactness implies absolute exactness,
so the proper-kernel theorem applies without injectivity of the coset map.
-/

namespace VOA.LeeYangShortcut

open VirModule VirSimple VirGoodFil LeeYang Sl2CosetConcrete
open LeeYangTransferAssembly LeeYangCosetTransfer GradedUnitaryCohomology

set_option Elab.async false

noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

abbrev UniversalWeight (n : ℤ) := (virasoroVOA leeYangC).grading n

/-- Universal PBW prefixes inside a fixed universal weight space. -/
def universalPrefix (p : ℕ) (n : ℤ) : Submodule ℂ (UniversalWeight n) :=
  (virFil leeYangC p n).comap (UniversalWeight n).subtype

/-- The canonical simple projection at a fixed weight. -/
def simpleWeightProjection (n : ℤ) : UniversalWeight n →ₗ[ℂ] LeeYangWeight n :=
  ((maxIdealVir leeYangC).mkQ.comp (UniversalWeight n).subtype).codRestrict _
    (fun x => show (maxIdealVir leeYangC).mkQ (x : VirUniv leeYangC) ∈
      ((virasoroVOA leeYangC).grading n).map (maxIdealVir leeYangC).mkQ from
        Submodule.mem_map.mpr ⟨(x : VirUniv leeYangC), x.2, rfl⟩)

theorem simpleWeightProjection_surjective (n : ℤ) :
    Function.Surjective (simpleWeightProjection n) := by
  intro y
  have hy : (y : LeeYangSpace) ∈
      ((virasoroVOA leeYangC).grading n).map (maxIdealVir leeYangC).mkQ := y.2
  obtain ⟨x, hx, hxy⟩ := Submodule.mem_map.mp hy
  exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

/-- The quotient is already strict on weightwise PBW prefixes. -/
theorem simpleWeightProjection_prefix (p : ℕ) (n : ℤ) :
    (universalPrefix p n).map (simpleWeightProjection n) =
      (virGradedFlag leeYangC).pieceIn p n := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact Submodule.mem_map.mpr ⟨x, hx, rfl⟩
  · intro hy
    obtain ⟨x, hx, hxy⟩ := Submodule.mem_map.mp hy
    refine Submodule.mem_map.mpr ⟨⟨x, virFil_le_grading leeYangC p n hx⟩, hx, ?_⟩
    exact Subtype.ext hxy

theorem universalPrefix_exhaustive (n : ℤ) (x : UniversalWeight n) :
    ∃ p, x ∈ universalPrefix p n := by
  have hx : (x : VirUniv leeYangC) ∈ gradingVir leeYangC n := x.2
  rw [← iSup_virFil leeYangC n] at hx
  obtain ⟨p, hp⟩ := (Submodule.mem_iSup_of_directed (fun p => virFil leeYangC p n)
    (fun p q => ⟨max p q, virFil_mono leeYangC n (le_max_left p q),
      virFil_mono leeYangC n (le_max_right p q)⟩)).mp hx
  exact ⟨p, hp⟩

/-- Closed representative in the actual finite relative complex. -/
def universalWeightRepresentative (n : ℤ) : UniversalWeight n →ₗ[ℂ] relativeWeight n :=
  ((cosetToComplex.comp virasoroToCoset).comp (UniversalWeight n).subtype).codRestrict _
    (fun x => ⟨cosetToComplex_relative _,
      cosetToComplex_mem_weight n _ (conformalEval_grading cosetVOA rfl x.2)⟩)

theorem universalWeightRepresentative_closed (n : ℤ) (x : UniversalWeight n) :
    relativeDifferential n (universalWeightRepresentative n x) = 0 := by
  apply Subtype.ext
  exact cosetToComplex_closed _

def universalWeightCycles (n : ℤ) :
    UniversalWeight n →ₗ[ℂ] LinearMap.ker (relativeDifferential n) :=
  (universalWeightRepresentative n).codRestrict (LinearMap.ker (relativeDifferential n))
    (universalWeightRepresentative_closed n)

def universalWeightClass (n : ℤ) :=
  cycleClassOfCycles (K := relativeWeight n) (M := UniversalWeight n)
    (relativeDifferential n) (universalWeightCycles n)

/-- Relative exactness kills the simple quotient of the universal state. -/
theorem universalWeightCycles_exact_zero (n : ℤ) (x : UniversalWeight n)
    (hb : universalWeightCycles n x ∈
      boundariesInCycles (K := relativeWeight n) (relativeDifferential n)) :
    simpleWeightProjection n x = 0 := by
  have ha := weightBoundary_toAbsolute n (universalWeightCycles n x) hb
  have hz : virasoroToH0 x = 0 := Subtype.ext ha
  apply Subtype.ext
  exact (Submodule.Quotient.mk_eq_zero (maxIdealVir leeYangC)).mpr
    (virasoroToH0_ker_le_maxIdeal hz)

/-- The concrete cycles transported to the equal Kähler differential. -/
def modelUniversalCycles (S : ConcreteKahlerGeometry) (n : ℤ)
    (hp : IsPosOn (S.geometry n).P ⊤) :=
  transportCyclesMap (K := relativeWeight n) (E := UniversalWeight n)
    (relativeDifferential n) (S.model n hp).D (S.model_D n hp).symm
    (universalWeightCycles n)

def modelUniversalClass (S : ConcreteKahlerGeometry) (n : ℤ)
    (hp : IsPosOn (S.geometry n).P ⊤) :=
  cycleClassOfCycles (K := relativeWeight n) (M := UniversalWeight n)
    (S.model n hp).D (modelUniversalCycles S n hp)

/-- Kernel containment is invariant under rewriting the differential. -/
theorem transportedCycles_ker_le {K E T : Type*}
    [AddCommGroup K] [Module ℂ K] [AddCommGroup E] [Module ℂ E]
    [AddCommGroup T] [Module ℂ T]
    (d d' : K →ₗ[ℂ] K) (hd : d = d')
    (f : E →ₗ[ℂ] LinearMap.ker d) (g : E →ₗ[ℂ] T)
    (hexact : ∀ x, f x ∈ boundariesInCycles d → g x = 0) :
    LinearMap.ker (cycleClassOfCycles d' (transportCyclesMap d d' hd f)) ≤
      LinearMap.ker g := by
  subst d'
  intro x hx
  exact hexact x ((Submodule.Quotient.mk_eq_zero (boundariesInCycles d)).mp hx)

def modelUniversalClass_ker_le (S : ConcreteKahlerGeometry) (n : ℤ)
    (hp : IsPosOn (S.geometry n).P ⊤) :=
  transportedCycles_ker_le (K := relativeWeight n) (E := UniversalWeight n)
    (T := LeeYangWeight n)
    (relativeDifferential n) (S.model n hp).D (S.model_D n hp).symm
    (universalWeightCycles n) (simpleWeightProjection n) (fun x hx => by
      obtain ⟨y, hy⟩ := hx
      exact universalWeightCycles_exact_zero n x ⟨y, hy⟩)

/-- A kernel containment factors the target map through the actual range. -/
def rangeFactor {U H T : Type*}
    [AddCommGroup U] [Module ℂ U] [AddCommGroup H] [Module ℂ H]
    [AddCommGroup T] [Module ℂ T]
    (f : U →ₗ[ℂ] H) (g : U →ₗ[ℂ] T) (hk : LinearMap.ker f ≤ LinearMap.ker g) :
    LinearMap.range f →ₗ[ℂ] T :=
  ((LinearMap.ker f).liftQ g hk).comp (LinearMap.quotKerEquivRange f).symm.toLinearMap

@[simp] theorem rangeFactor_apply {U H T : Type*}
    [AddCommGroup U] [Module ℂ U] [AddCommGroup H] [Module ℂ H]
    [AddCommGroup T] [Module ℂ T]
    (f : U →ₗ[ℂ] H) (g : U →ₗ[ℂ] T) (hk : LinearMap.ker f ≤ LinearMap.ker g) (x : U) :
    rangeFactor f g hk (f.rangeRestrict x) = g x := by
  change (LinearMap.ker f).liftQ g hk (f.quotKerEquivRange.symm ⟨f x, _⟩) = _
  rw [LinearMap.quotKerEquivRange_symm_apply_image]
  rfl

/-- A surjective map remains surjective after factoring through an intermediate range. -/
theorem rangeFactor_surjective {U H T : Type*}
    [AddCommGroup U] [Module ℂ U] [AddCommGroup H] [Module ℂ H]
    [AddCommGroup T] [Module ℂ T]
    (f : U →ₗ[ℂ] H) (g : U →ₗ[ℂ] T) (hk : LinearMap.ker f ≤ LinearMap.ker g)
    (hg : Function.Surjective g) : Function.Surjective (rangeFactor f g hk) := by
  intro y
  obtain ⟨x, rfl⟩ := hg y
  exact ⟨f.rangeRestrict x, rangeFactor_apply f g hk x⟩

/-- Passing through a range does not change the image of any source prefix. -/
theorem rangeFactor_prefix {U H T : Type*}
    [AddCommGroup U] [Module ℂ U] [AddCommGroup H] [Module ℂ H]
    [AddCommGroup T] [Module ℂ T]
    (f : U →ₗ[ℂ] H) (g : U →ₗ[ℂ] T) (hk : LinearMap.ker f ≤ LinearMap.ker g)
    (P : Submodule ℂ U) (Q : Submodule ℂ T) (hPQ : P.map g = Q) :
    (P.map f.rangeRestrict).map (rangeFactor f g hk) = Q := by
  rw [← Submodule.map_comp]
  have he : (rangeFactor f g hk).comp f.rangeRestrict = g := by
    ext x
    exact rangeFactor_apply f g hk x
  rw [he]
  exact hPQ

abbrev RelativeImage (S : ConcreteKahlerGeometry) (n : ℤ)
    (hp : IsPosOn (S.geometry n).P ⊤) := LinearMap.range (modelUniversalClass S n hp)

def relativeImageToSimple (S : ConcreteKahlerGeometry) (n : ℤ)
    (hp : IsPosOn (S.geometry n).P ⊤) :=
  rangeFactor (modelUniversalClass S n hp) (simpleWeightProjection n)
    (modelUniversalClass_ker_le S n hp)

def relativeImageToSimple_surjective (S : ConcreteKahlerGeometry) (n : ℤ)
    (hp : IsPosOn (S.geometry n).P ⊤) :=
  rangeFactor_surjective (modelUniversalClass S n hp) (simpleWeightProjection n)
    (modelUniversalClass_ker_le S n hp) (simpleWeightProjection_surjective n)

def relativeImagePrefix (S : ConcreteKahlerGeometry) (n : ℤ)
    (hp : IsPosOn (S.geometry n).P ⊤) (p : ℕ) :=
  (universalPrefix p n).map (modelUniversalClass S n hp).rangeRestrict

def relativeImageToSimple_prefix (S : ConcreteKahlerGeometry) (n : ℤ)
    (hp : IsPosOn (S.geometry n).P ⊤) (p : ℕ) :=
  rangeFactor_prefix (modelUniversalClass S n hp) (simpleWeightProjection n)
    (modelUniversalClass_ker_le S n hp) (universalPrefix p n)
    ((virGradedFlag leeYangC).pieceIn p n) (simpleWeightProjection_prefix p n)

/-- Exhaustion of source prefixes passes to the actual range of any linear map. -/
theorem rangePrefix_exhaustive {U H : Type*}
    [AddCommGroup U] [Module ℂ U] [AddCommGroup H] [Module ℂ H]
    (f : U →ₗ[ℂ] H) (F : ℕ → Submodule ℂ U)
    (hex : ∀ x, ∃ p, x ∈ F p) (x : LinearMap.range f) :
    ∃ p, x ∈ (F p).map f.rangeRestrict := by
  obtain ⟨y, hy⟩ := x.2
  obtain ⟨p, hpy⟩ := hex y
  exact ⟨p, Submodule.mem_map.mpr ⟨y, hpy, Subtype.ext hy⟩⟩

/-- The image PBW prefixes exhaust the actual relative image. -/
def relativeImagePrefix_exhaustive (S : ConcreteKahlerGeometry) (n : ℤ)
    (hp : IsPosOn (S.geometry n).P ⊤) :=
  rangePrefix_exhaustive (modelUniversalClass S n hp) (fun p => universalPrefix p n)
    (universalPrefix_exhaustive n)

end
end VOA.LeeYangShortcut
