import VOA.Examples.LeeYangShortcutSqueeze
import VOA.Examples.LeeYangShortcutRelative
import VOA.Examples.LeeYangTransferAssembly

/-!
# Harmonic transfer from the Virasoro image

The map to the simple VOA is initially only surjective. The image dimension
squeeze proves its injectivity and exact filtering before transferring the
forms. No coset identification or coset simplicity is used here.

OPEN: application to the concrete Virasoro image needs its filtered relative
class map and agreement of its forms with the normalized Virasoro forms.
These are explicit hypotheses below; the existing `GUData` does not provide
Virasoro invariance or vacuum normalization.
-/

namespace VOA.LeeYangShortcut

open LeeYangTransferAssembly LeeYangCosetTransfer GradedUnitaryCohomology
open VertexOperatorAlgebra
open scoped BigOperators

universe u v w
variable {V : Type u} [AddCommGroup V] [Module ℂ V]
variable {W : VertexOperatorAlgebra V}
variable {K : Type v} [AddCommGroup K] [Module ℂ K] [FiniteDimensional ℂ K]
variable {I : Type w} [AddCommGroup I] [Module ℂ I]

set_option maxHeartbeats 1000000

/-- Lift the actual range of a cohomology map to its unique harmonic representatives. -/
noncomputable def harmonicRangeMap (C : KahlerComplex K)
    (f : I →ₗ[ℂ] cycleQuotient C.D) : LinearMap.range f →ₗ[ℂ] C.harm :=
  (harmonicEquivCohomology C.P C.pos C.herm C.D C.Dadj C.D_sq C.adj_D).symm.toLinearMap.comp
    (LinearMap.range f).subtype

theorem harmonicRangeMap_class (C : KahlerComplex K) (f : I →ₗ[ℂ] cycleQuotient C.D) :
    (harmonicToCohomology C.D C.Dadj).comp (harmonicRangeMap C f) =
      (LinearMap.range f).subtype := by
  ext x
  exact (harmonicEquivCohomology C.P C.pos C.herm C.D C.Dadj C.D_sq C.adj_D).apply_symm_apply _

theorem harmonicRangeMap_class_injective (C : KahlerComplex K)
    (f : I →ₗ[ℂ] cycleQuotient C.D) :
    Function.Injective ((harmonicToCohomology C.D C.Dadj).comp (harmonicRangeMap C f)) := by
  rw [harmonicRangeMap_class]
  exact Subtype.val_injective

/-- The leading-cohomology bound supplies the upper half of the image squeeze. -/
theorem cohom_prefix_bound (C : KahlerComplex K)
    {E : Type*} [AddCommGroup E] [Module ℂ E] (Q : ℕ → Submodule ℂ E)
    (hcharacter : ∀ p : ℕ,
      (∑ j ∈ Finset.Icc 0 (2 * (p : ℤ)), Module.finrank ℂ (C.leadCohom (j, 0))) =
        Module.finrank ℂ (Q p)) (p : ℕ) :
    Module.finrank ℂ (C.cohomFilt (KahlerComplex.rowSet (Finset.Icc 0 (2 * (p : ℤ))) 0)) ≤
      Module.finrank ℂ (Q p) := by
  rw [← hcharacter p]
  exact C.finrank_cohomFilt_row_le_lead _ 0

/-- Weightwise graded unitarity from an image surjecting onto the target.
Only the image embeds into cohomology at the start of the proof. -/
theorem gradedUnitaryAt_of_harmonic_image
    (C : KahlerComplex K) (G : GUData C) (F : GradedFlag W) (n : ℤ)
    (β : LinearMap.BilinForm ℂ (W.grading n)) (h : SesqForm (W.grading n))
    (a : I →ₗ[ℂ] C.harm)
    (ha : Function.Injective ((harmonicToCohomology C.D C.Dadj).comp a))
    (q : I →ₗ[ℂ] W.grading n) (hqs : Function.Surjective q)
    (P : ℕ → Submodule ℂ I)
    (hquotient : ∀ p, (P p).map q = F.pieceIn p n)
    (hexhaustive : ∀ x : I, ∃ p, x ∈ P p)
    (hfiltered : ∀ p, (P p).map ((harmonicToCohomology C.D C.Dadj).comp a) ≤
      C.cohomFilt (KahlerComplex.rowSet (Finset.Icc 0 (2 * (p : ℤ))) 0))
    (hcharacter : ∀ p : ℕ,
      (∑ j ∈ Finset.Icc 0 (2 * (p : ℤ)), Module.finrank ℂ (C.leadCohom (j, 0))) =
        Module.finrank ℂ (F.pieceIn p n))
    (hB : ∀ x y, β (q x) (q y) = G.B (a x) (a y))
    (hh : ∀ x y, h (q x) (q y) = G.h (a x) (a y))
    (hintegral : IntegralHarmonicSupport C) : GradedUnitaryAt F n β h := by
  let j := (harmonicToCohomology C.D C.Dadj).comp a
  let Q := fun p => F.pieceIn p n
  let T := fun p : ℕ =>
    C.cohomFilt (KahlerComplex.rowSet (Finset.Icc 0 (2 * (p : ℤ))) 0)
  have hupper : ∀ p, Module.finrank ℂ (T p) ≤ Module.finrank ℂ (Q p) :=
    cohom_prefix_bound C Q hcharacter
  let e := imageEquivSimple j ha q hqs P Q T hquotient hfiltered hupper hexhaustive
  let b := a.comp e.symm.toLinearMap
  let i := C.harm.subtype.comp b
  have he (x : W.grading n) : q (e.symm x) = x := e.apply_symm_apply x
  have hi : Function.Injective i := by
    intro x y hxy
    have hb : b x = b y := Subtype.ext hxy
    have hj : j (e.symm x) = j (e.symm y) := congrArg
      (harmonicToCohomology C.D C.Dadj) hb
    exact e.symm.injective (ha hj)
  apply gradedUnitaryAt_of_harmonic_filteredIso C G F n β h i hi
  · intro x y
    simpa only [he] using hB (e.symm x) (e.symm y)
  · intro x y
    simpa only [he] using hh (e.symm x) (e.symm y)
  · intro p
    apply map_eq_harmonic_flag_of_cohom_map_eq C (F.pieceIn p n) b
    have hmap := simple_map_eq_of_image_squeeze j ha q hqs P Q T
      hquotient hfiltered hupper hexhaustive p
    exact hmap
  · exact hintegral

/-- The unique harmonic representative of the class of a source vector. -/
noncomputable def harmonicClassLift {U : Type*} [AddCommGroup U] [Module ℂ U]
    (C : KahlerComplex K) (f : U →ₗ[ℂ] cycleQuotient C.D) : U →ₗ[ℂ] C.harm :=
  (harmonicEquivCohomology C.P C.pos C.herm C.D C.Dadj C.D_sq C.adj_D).symm.toLinearMap.comp f

/-- Weightwise graded unitarity from a family of cohomology classes `f` on a
source `U` whose kernel is killed by a surjection `g` onto the target weight
space. Injectivity of `f` is not assumed: only the image of `f` embeds in
cohomology, and the squeeze proves that `g` is injective on that image. -/
theorem gradedUnitaryAt_of_class_family {U : Type*} [AddCommGroup U] [Module ℂ U]
    (C : KahlerComplex K) (G : GUData C) (F : GradedFlag W) (n : ℤ)
    (β : LinearMap.BilinForm ℂ (W.grading n)) (h : SesqForm (W.grading n))
    (f : U →ₗ[ℂ] cycleQuotient C.D) (g : U →ₗ[ℂ] W.grading n)
    (hgs : Function.Surjective g) (hker : LinearMap.ker f ≤ LinearMap.ker g)
    (P : ℕ → Submodule ℂ U)
    (hquotient : ∀ p, (P p).map g = F.pieceIn p n)
    (hexhaustive : ∀ x : U, ∃ p, x ∈ P p)
    (hfiltered : ∀ p, (P p).map f ≤
      C.cohomFilt (KahlerComplex.rowSet (Finset.Icc 0 (2 * (p : ℤ))) 0))
    (hcharacter : ∀ p : ℕ,
      (∑ j ∈ Finset.Icc 0 (2 * (p : ℤ)), Module.finrank ℂ (C.leadCohom (j, 0))) =
        Module.finrank ℂ (F.pieceIn p n))
    (hB : ∀ x y, β (g x) (g y) = G.B (harmonicClassLift C f x) (harmonicClassLift C f y))
    (hh : ∀ x y, h (g x) (g y) = G.h (harmonicClassLift C f x) (harmonicClassLift C f y))
    (hintegral : IntegralHarmonicSupport C) : GradedUnitaryAt F n β h := by
  have hcls := harmonicRangeMap_class C f
  have hlift : ∀ u, harmonicRangeMap C f (f.rangeRestrict u) = harmonicClassLift C f u :=
    fun _ => rfl
  apply gradedUnitaryAt_of_harmonic_image C G F n β h (harmonicRangeMap C f)
    (harmonicRangeMap_class_injective C f) (rangeFactor f g hker)
    (rangeFactor_surjective f g hker hgs) (fun p => (P p).map f.rangeRestrict)
    (fun p => rangeFactor_prefix f g hker (P p) _ (hquotient p))
    (rangePrefix_exhaustive f P hexhaustive)
  · intro p
    rw [hcls, ← Submodule.map_comp]
    exact hfiltered p
  · exact hcharacter
  · intro x y
    obtain ⟨u, rfl⟩ := f.surjective_rangeRestrict x
    obtain ⟨v, rfl⟩ := f.surjective_rangeRestrict y
    rw [rangeFactor_apply, rangeFactor_apply, hlift, hlift]
    exact hB u v
  · intro x y
    obtain ⟨u, rfl⟩ := f.surjective_rangeRestrict x
    obtain ⟨v, rfl⟩ := f.surjective_rangeRestrict y
    rw [rangeFactor_apply, rangeFactor_apply, hlift, hlift]
    exact hh u v
  · exact hintegral

end VOA.LeeYangShortcut
