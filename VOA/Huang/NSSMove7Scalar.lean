import VOA.Huang.NSSMove7Dual

/-! # The loop transposition for scalar dual monodromies

This generalizes the transparent-color calculation. The remaining general
case has genuinely nonscalar monodromy between the two loop colors.
-/
noncomputable section
set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
namespace VOA.Huang.NSCongruence
open CategoryTheory MonoidalCategory Limits BraidedCategory
open VOA.Huang.NgSchauenburg
universe v u
attribute [-instance] hasRightDualUnit hasRightDualLeftDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [BraidedCategory C]

/-- A scalar interaction with the right spectator factors out of the loop. -/
theorem monodromyLoop_tensor_right_of_scalar (P : Pivotal C) (X A B : C) (z : ℂ)
    (h : monodromy X B = z • 𝟙 _) :
    monodromyLoop P X (A ⊗ B) = z • (monodromyLoop P X A ▷ B) := by
  have hm : monodromy X (A ⊗ B) =
      z • ((α_ X A B).inv ≫ monodromy X A ▷ B ≫ (α_ X A B).hom) := by
    dsimp only [monodromy] at h ⊢
    rw [braiding_tensor_right_hom, braiding_tensor_left_hom]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← whiskerLeft_comp_assoc, h]
    simp
  rw [monodromyLoop, hm]
  change P.partialTraceLeftLinear X _ _ (z • _) = _
  rw [map_smul]
  change z • P.partialTraceLeft X _ = _
  rw [P.partialTraceLeft_whisker]
  rfl

/-- The scalar left-spectator formula follows by braided naturality. -/
theorem monodromyLoop_tensor_left_of_scalar (P : Pivotal C) (X A B : C) (z : ℂ)
    (h : monodromy X A = z • 𝟙 _) :
    monodromyLoop P X (A ⊗ B) = z • (A ◁ monodromyLoop P X B) := by
  apply (cancel_mono (β_ A B).hom).mp
  rw [← monodromyLoop_naturality, monodromyLoop_tensor_right_of_scalar P X B A z h]
  simp only [Linear.comp_smul, Linear.smul_comp, braiding_naturality_right]

/-- An actual open transposition whenever the two dual interactions have the
same scalar. Both exterior objects are unrestricted simple labels. -/
theorem loopTranspose_of_scalar_dual_monodromy (F : SphericalFusion C) (X Y : C)
    (z : ℂ) (hYX : monodromy Y Xᘁ = z • 𝟙 _)
    (hXY : monodromy X Yᘁ = z • 𝟙 _) (i j : F.Label) :
    forwardSewingMap F X i j (monodromyLoop F.toPivotal Y (Xᘁ ⊗ F.simple i)) =
      inverseSewingMap F Y i j (monodromyLoop F.toPivotal X (F.simple j ⊗ Yᘁ)) := by
  rw [monodromyLoop_tensor_left_of_scalar _ _ _ _ z hYX,
    monodromyLoop_tensor_right_of_scalar _ _ _ _ z hXY,
    map_smul, map_smul, forwardSewingMap_whiskerLeft,
    inverseSewingMap_whiskerRight, forwardSewingMap_id, inverseSewingMap_id]
  congr 1
  simp only [Category.assoc]
  rw [whisker_exchange]

/-- Only one scalar dual interaction is needed for the open transposition. -/
theorem loopTranspose_of_scalar_monodromy (F : SphericalFusion C) (X Y : C)
    (z : ℂ) (h : monodromy Y Xᘁ = z • 𝟙 _) (i j : F.Label) :
    forwardSewingMap F X i j (monodromyLoop F.toPivotal Y (Xᘁ ⊗ F.simple i)) =
      inverseSewingMap F Y i j (monodromyLoop F.toPivotal X (F.simple j ⊗ Yᘁ)) :=
  loopTranspose_of_scalar_dual_monodromy F X Y z h
    (scalar_dual_monodromy_transfer F.toPivotal X Y z h) i j

/-- Scalarity of the actual monodromy between a color and the other dual.
The corresponding opposite interaction is automatically its right mate. -/
def ScalarDualMonodromy (F : SphericalFusion C) (r b : F.Label) : Prop :=
  ∃ z : ℂ, monodromy (F.simple b) (F.simple r)ᘁ = z • 𝟙 _

/-- Named proved portion of the exact target. The hypothesis concerns the
actual dual monodromy and does not discard exterior multiplicity entries. -/
def MixedScalarLoopTranspose (F : SphericalFusion C) : Prop :=
  ∀ r b i j : F.Label, ScalarDualMonodromy F r b →
    forwardSewingMap F (F.simple r) i j
      (monodromyLoop F.toPivotal (F.simple b) ((F.simple r)ᘁ ⊗ F.simple i)) =
    inverseSewingMap F (F.simple b) i j
      (monodromyLoop F.toPivotal (F.simple r) (F.simple j ⊗ (F.simple b)ᘁ))

/-- The scalar-interaction portion holds without ribbon or modular hypotheses. -/
theorem mixedScalarLoopTranspose_holds (F : SphericalFusion C) :
    MixedScalarLoopTranspose F := by
  rintro r b i j ⟨z, hz⟩
  exact loopTranspose_of_scalar_monodromy F _ _ z hz i j

/-- The unit-color cases belong to the scalar-interaction portion. -/
theorem scalarDualMonodromy_of_unit (F : SphericalFusion C) (r b : F.Label)
    (h : r = F.unitLabel ∨ b = F.unitLabel) : ScalarDualMonodromy F r b := by
  have hu := transparentDualPair_unitLabel F
  rcases h with h | h
  · subst r
    exact ⟨1, by simpa using hu.2 (F.simple b)⟩
  · subst b
    exact ⟨1, by simpa using hu.1 (F.simple r)ᘁ⟩

/-- Schur's lemma supplies scalar monodromy if the relevant tensor product
is simple. This is a sufficient hypothesis, not a consequence of modularity. -/
theorem scalarDualMonodromy_of_simple (F : SphericalFusion C) (r b : F.Label)
    [Simple (F.simple b ⊗ (F.simple r)ᘁ)] : ScalarDualMonodromy F r b := by
  letI := F.homFinite (F.simple b ⊗ (F.simple r)ᘁ) (F.simple b ⊗ (F.simple r)ᘁ)
  obtain ⟨z, hz⟩ := endomorphism_simple_eq_smul_id ℂ
    (monodromy (F.simple b) (F.simple r)ᘁ)
  exact ⟨z, hz.symm⟩

/-- The complete target holds when all the simple-dual products are simple,
as happens in pointed fusion categories. The displayed hypothesis is explicit. -/
theorem mixedLoopTranspose_of_simple_dual_products (F : SphericalFusion C)
    (h : ∀ r b : F.Label, Simple (F.simple b ⊗ (F.simple r)ᘁ)) :
    MixedLoopTranspose F := by
  intro r b i j
  letI := h r b
  exact mixedScalarLoopTranspose_holds F r b i j (scalarDualMonodromy_of_simple F r b)

end VOA.Huang.NSCongruence
