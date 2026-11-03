import VOA.Huang.NgSchauenburgAverageIdempotent

/-! # The killing ring in a nondegenerate braided spherical fusion category

Nondegeneracy is essential for the unit-channel conclusion for monodromy
loops. This theorem does not replace the open-strand averaging theorem for
an arbitrary unbraided base category.
-/
noncomputable section
set_option linter.unusedSectionVars false
universe v u
namespace VOA.Huang.NgSchauenburg
open CategoryTheory MonoidalCategory Limits BraidedCategory
attribute [-instance] hasRightDualUnit hasRightDualLeftDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [BraidedCategory C]

/-- The central lift with inverse opposite braiding. -/
def oppositeBraidedCenter (X : C) : Center C :=
  ⟨X, { β := fun U => (β_ U X).symm }⟩

/-- Comparing the two central lifts of an object produces its monodromy loop. -/
theorem halfBraidingLoop_braided_id (F : SphericalFusion C) (X U : C) :
    halfBraidingLoop F.toPivotal (oppositeBraidedCenter X) (Center.ofBraidedObj X) U
      (𝟙 X) = monodromyLoop F.toPivotal U X := by
  change F.toPivotal.partialTraceLeft U
    ((β_ U X).hom ≫ (𝟙 X) ▷ U ≫ (β_ X U).hom) = _
  simp [monodromyLoop, monodromy]

/-- Closing a loop around the unit gives the dimension of the loop label. -/
theorem monodromyLoop_unit (F : SphericalFusion C) (U : C) :
    monodromyLoop F.toPivotal U (𝟙_ C) = F.dimension U • 𝟙 (𝟙_ C) := by
  have h : monodromy U (𝟙_ C) = U ◁ 𝟙 (𝟙_ C) := by
    simp [monodromy, braiding_tensorUnit_right, braiding_tensorUnit_left]
  rw [monodromyLoop, h, F.partialTraceLeft_whiskerLeft]

/-- The vacuum column of the actual S matrix. -/
theorem categoricalS_unit_right (F : SphericalFusion C) (i : F.Label) :
    categoricalS F i F.unitLabel = F.dimension (F.simple i) := by
  have h := monodromyLoop_naturality F.toPivotal (F.simple i)ᘁ F.unitIso.hom
  rw [monodromyLoop_unit, F.dimension_dual, monodromyLoop_simple,
    F.dimension_unitLabel, div_one] at h
  have h' := congrArg (fun f => f ≫ F.unitIso.inv) h
  have hs := congrArg (F.scalarTrace (F.simple F.unitLabel)) h'
  simpa using hs.symm

/-- A column proportional to the vacuum column must itself be the vacuum
column. The hypothesis is an equality of actual categorical S entries. -/
theorem eq_unitLabel_of_S_dimension_column (F : SphericalFusion C) (M : Modular F)
    (j : F.Label)
    (h : ∀ i, categoricalS F i j = F.dimension (F.simple i) * F.dimension (F.simple j)) :
    j = F.unitLabel := by
  classical
  have hinv := Matrix.nonsing_inv_mul (categoricalS F)
    (isUnit_iff_ne_zero.mpr M.nondegenerate)
  have hj := congrArg (fun A : Matrix F.Label F.Label ℂ => A j j) hinv
  have h0 := congrArg (fun A : Matrix F.Label F.Label ℂ => A j F.unitLabel) hinv
  simp only [Matrix.mul_apply, Matrix.one_apply, ite_true] at hj h0
  by_contra hne
  rw [if_neg hne] at h0
  simp only [h, ← mul_assoc, ← Finset.sum_mul] at hj
  simp only [categoricalS_unit_right] at h0
  rw [h0, zero_mul] at hj
  exact zero_ne_one hj

/-- The weighted monodromy sum vanishes on every non-unit simple. -/
theorem monodromy_killingRing_simple_ne (F : SphericalFusion C) (M : Modular F)
    (j : F.Label) (hj : j ≠ F.unitLabel) :
    (∑ i, F.dimension (F.simple i) •
      monodromyLoop F.toPivotal (F.simple i) (F.simple j)) = 0 := by
  let X := oppositeBraidedCenter (F.simple j)
  let Y := Center.ofBraidedObj (F.simple j)
  let a := halfBraidingAverage F X Y (𝟙 (F.simple j))
  have ha := F.simple_end_eq_trace j a
  let z := F.scalarTrace (F.simple j) a / F.dimension (F.simple j)
  have haz : a = z • 𝟙 (F.simple j) := ha
  have hz : z = 0 := by
    by_contra hn
    apply hj
    apply eq_unitLabel_of_S_dimension_column F M j
    intro i
    have he := congrArg (fun L : Module.End ℂ (X.1 ⟶ Y.1) => L (𝟙 (F.simple j)))
      (halfBraidingLoop_comp_average F X Y (F.simple i)ᘁ)
    change halfBraidingLoop F.toPivotal X Y (F.simple i)ᘁ a =
      F.dimension (F.simple i)ᘁ • a at he
    dsimp only [X, Y] at he
    rw [haz] at he
    erw [LinearMap.map_smul] at he
    change z • halfBraidingLoop F.toPivotal (oppositeBraidedCenter (F.simple j))
      (Center.ofBraidedObj (F.simple j)) (F.simple i)ᘁ (𝟙 (F.simple j)) = _ at he
    rw [halfBraidingLoop_braided_id, monodromyLoop_simple, F.dimension_dual] at he
    have ht := congrArg (F.scalarTrace (F.simple j)) he
    erw [map_smul, map_smul, map_smul, map_smul] at ht
    simp only [F.scalarTrace_id, smul_eq_mul] at ht
    have hd := F.dimension_simple_ne_zero j
    rw [div_mul_cancel₀ _ hd] at ht
    apply mul_left_cancel₀ hn
    calc
      _ = F.dimension (F.simple i) * (z * F.dimension (F.simple j)) := ht
      _ = _ := by ring
  have ha0 : a = 0 := by rw [haz, hz, zero_smul]; rfl
  have hs : a = F.globalDimension⁻¹ • ∑ i, F.dimension (F.simple i) •
      monodromyLoop F.toPivotal (F.simple i) (F.simple j) := by
    simp only [a, halfBraidingAverage, LinearMap.smul_apply, LinearMap.sum_apply]
    simp only [X, Y, halfBraidingLoop_braided_id]
    rfl
  rw [hs] at ha0
  exact (smul_eq_zero.mp ha0).resolve_left (inv_ne_zero F.globalDimension_ne_zero)

/-- On the unit channel the unnormalized ring has value global dimension. -/
theorem monodromy_killingRing_unit (F : SphericalFusion C) :
    (∑ i, F.dimension (F.simple i) •
      monodromyLoop F.toPivotal (F.simple i) (F.simple F.unitLabel)) =
        F.globalDimension • 𝟙 (F.simple F.unitLabel) := by
  have h (U : C) : monodromyLoop F.toPivotal U (F.simple F.unitLabel) =
      F.dimension U • 𝟙 (F.simple F.unitLabel) := by
    apply (cancel_mono F.unitIso.hom).mp
    rw [← monodromyLoop_naturality, monodromyLoop_unit]
    simp
  simp only [h, smul_smul, ← pow_two, ← Finset.sum_smul]
  rfl

open Classical in
/-- The killing-ring scalar on every simple channel. -/
theorem monodromy_killingRing_simple (F : SphericalFusion C) (M : Modular F)
    (j : F.Label) :
    (∑ i, F.dimension (F.simple i) •
      monodromyLoop F.toPivotal (F.simple i) (F.simple j)) =
        if j = F.unitLabel then F.globalDimension • 𝟙 (F.simple j) else 0 := by
  by_cases h : j = F.unitLabel
  · subst j
    simpa using monodromy_killingRing_unit F
  · simpa [h] using monodromy_killingRing_simple_ne F M j h

/-- The genuine dimension-weighted monodromy ring kills every non-unit
isotypic channel of an arbitrary object. No S orthogonality is assumed. -/
theorem monodromy_killingRing (F : SphericalFusion C) (M : Modular F) (X : C) :
    (∑ i, F.dimension (F.simple i) • monodromyLoop F.toPivotal (F.simple i) X) =
      F.globalDimension • F.simpleProjector F.unitLabel X := by
  classical
  apply F.hom_ext_from_simples
  intro j q
  simp only [Preadditive.comp_sum, Linear.comp_smul, monodromyLoop_naturality,
    ← Linear.smul_comp, ← Preadditive.sum_comp, F.comp_simpleProjector]
  rw [monodromy_killingRing_simple F M]
  split_ifs <;> simp

/-- The normalized ring is the already constructed unit isotypic projector. -/
theorem normalized_monodromy_killingRing (F : SphericalFusion C) (M : Modular F)
    (X : C) :
    F.globalDimension⁻¹ •
      (∑ i, F.dimension (F.simple i) • monodromyLoop F.toPivotal (F.simple i) X) =
        F.simpleProjector F.unitLabel X := by
  rw [monodromy_killingRing F M, smul_smul,
    inv_mul_cancel₀ F.globalDimension_ne_zero, one_smul]

end VOA.Huang.NgSchauenburg
