import VOA.Huang.NgSchauenburgLoop

/-! # Fourier inversion of categorical monodromy loops

Simple isotypic projectors are recovered from the actual cup-cap loops using
the inverse categorical S matrix. This is an identity inside a modular category;
it does not assert the different averaging formula on underlying Hom spaces
of two objects of a Drinfeld center.
-/
noncomputable section
set_option linter.unusedSectionVars false
universe v u
namespace VOA.Huang.NgSchauenburg
open CategoryTheory MonoidalCategory Limits
attribute [-instance] hasRightDualUnit hasRightDualLeftDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]

namespace SphericalFusion
variable (F : SphericalFusion C)

/-- The projector onto all copies of a specified simple, constructed from the
composition-dual channel basis. Its action below characterizes it intrinsically. -/
def simpleProjector (i : F.Label) (X : C) : X ⟶ X :=
  ∑ a, F.compositionDual (F.simpleHomBasis X i) a ≫ F.simpleHomBasis X i a

open Classical in
theorem comp_simpleProjector (i j : F.Label) {X : C} (q : F.simple j ⟶ X) :
    q ≫ F.simpleProjector i X = if j = i then q else 0 := by
  by_cases h : j = i
  · subst j
    simp only [simpleProjector, Preadditive.comp_sum, ← Category.assoc,
      F.comp_compositionDual, Linear.smul_comp, Category.id_comp, ite_true]
    exact (F.simpleHomBasis X i).sum_repr q
  · simp only [simpleProjector, Preadditive.comp_sum, ← Category.assoc, if_neg h]
    apply Finset.sum_eq_zero
    intro a _
    rw [F.hom_simple_eq_zero h (q ≫ F.compositionDual (F.simpleHomBasis X i) a),
      zero_comp]

theorem sum_simpleProjector (X : C) : (∑ i, F.simpleProjector i X) = 𝟙 X :=
  F.sum_compositionDual_comp (F.simpleHomBasis X)

theorem simpleProjector_naturality (i : F.Label) {X Y : C} (f : X ⟶ Y) :
    F.simpleProjector i X ≫ f = f ≫ F.simpleProjector i Y := by
  classical
  apply F.hom_ext_from_simples
  intro j q
  rw [← Category.assoc, F.comp_simpleProjector, ← Category.assoc,
    F.comp_simpleProjector]
  split_ifs <;> simp

open Classical in
theorem simpleProjector_comp (i j : F.Label) (X : C) :
    F.simpleProjector i X ≫ F.simpleProjector j X =
      if i = j then F.simpleProjector i X else 0 := by
  apply F.hom_ext_from_simples
  intro k q
  by_cases hki : k = i
  · subst k
    by_cases hij : i = j
    · subst j
      simp [← Category.assoc, F.comp_simpleProjector]
    · simp [← Category.assoc, F.comp_simpleProjector, hij]
  · by_cases hij : i = j
    · subst j
      simp [← Category.assoc, F.comp_simpleProjector, hki]
    · simp [← Category.assoc, F.comp_simpleProjector, hki, hij]

theorem simpleProjector_idempotent (i : F.Label) (X : C) :
    F.simpleProjector i X ≫ F.simpleProjector i X = F.simpleProjector i X := by
  classical
  simp [F.simpleProjector_comp]

end SphericalFusion

variable [BraidedCategory C]

theorem comp_monodromyLoop (F : SphericalFusion C) (i j : F.Label) {X : C}
    (q : F.simple j ⟶ X) :
    q ≫ monodromyLoop F.toPivotal (F.simple i)ᘁ X =
      (categoricalS F i j / F.dimension (F.simple j)) • q := by
  rw [monodromyLoop_naturality, monodromyLoop_simple, Linear.smul_comp, Category.id_comp]

/-- The Fourier expansion of a genuine loop in simple-summand projectors. -/
theorem monodromyLoop_eq_sum_projectors (F : SphericalFusion C) (i : F.Label) (X : C) :
    monodromyLoop F.toPivotal (F.simple i)ᘁ X =
      ∑ j, (categoricalS F i j / F.dimension (F.simple j)) • F.simpleProjector j X := by
  classical
  apply F.hom_ext_from_simples
  intro k q
  simp only [Preadditive.comp_sum, Linear.comp_smul, F.comp_simpleProjector,
    comp_monodromyLoop]
  simp

open Classical in
/-- Invertibility of the actual S matrix recovers each isotypic projector from
cup-cap loops. No orthogonality or normalization identity for S is assumed. -/
theorem simpleProjector_eq_sum_loops (F : SphericalFusion C) (M : Modular F)
    (j : F.Label) (X : C) :
    F.simpleProjector j X =
      ∑ i, (F.dimension (F.simple j) * (categoricalS F)⁻¹ j i) •
        monodromyLoop F.toPivotal (F.simple i)ᘁ X := by
  classical
  apply F.hom_ext_from_simples
  intro k q
  rw [F.comp_simpleProjector]
  simp only [Preadditive.comp_sum, Linear.comp_smul, comp_monodromyLoop, smul_smul]
  have hm : (∑ i, (categoricalS F)⁻¹ j i * categoricalS F i k) = if j = k then 1 else 0 := by
    have h := congrArg (fun A : Matrix F.Label F.Label ℂ => A j k)
      (Matrix.nonsing_inv_mul (categoricalS F) (isUnit_iff_ne_zero.mpr M.nondegenerate))
    simpa only [Matrix.mul_apply, Matrix.one_apply] using h
  have he : (∑ i, (F.dimension (F.simple j) * (categoricalS F)⁻¹ j i) *
      (categoricalS F i k / F.dimension (F.simple k))) =
      (F.dimension (F.simple j) / F.dimension (F.simple k)) *
        (∑ i, (categoricalS F)⁻¹ j i * categoricalS F i k) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [← Finset.sum_smul, he, hm]
  by_cases h : j = k
  · subst k
    simp [F.dimension_simple_ne_zero]
  · simp [h, Ne.symm h]

end VOA.Huang.NgSchauenburg
