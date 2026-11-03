import VOA.Huang.NgSchauenburgMixedIndicators
import VOA.Huang.ReconstructionPairing

/-! # Hom spaces between mixed central objects

Duality reduces the mixed Hom space to maps between the two braided embeddings.
The modular killing ring restricts those maps to the unit channel.
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

/-- Maps between the two embeddings are exactly the unit-source channels. -/
def oppositeBraidedHomEquiv (F : SphericalFusion C) (M : Modular F) (X Y : C) :
    (oppositeBraidedCenter X ⟶ Center.ofBraidedObj Y) ≃ₗ[ℂ]
      (Fin (Module.finrank ℂ (F.simple F.unitLabel ⟶ X)) →
        (F.simple F.unitLabel ⟶ Y)) where
  toFun f a := F.simpleHomBasis X F.unitLabel a ≫ f.f
  invFun q := ⟨∑ a, F.compositionDual (F.simpleHomBasis X F.unitLabel) a ≫ q a, by
    intro U
    simp only [sum_whiskerRight, Preadditive.sum_comp, whiskerLeft_sum,
      Preadditive.comp_sum]
    apply Finset.sum_congr rfl
    intro a _
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using
      braided_comm_of_unit_factor
        (F.compositionDual (F.simpleHomBasis X F.unitLabel) a ≫ F.unitIso.hom)
        (F.unitIso.inv ≫ q a) U⟩
  left_inv f := by
    apply Center.ext
    have h := (opposite_braided_comm_iff F M f.f).mp f.comm
    simpa only [SphericalFusion.simpleProjector, Preadditive.sum_comp,
      Category.assoc] using h
  right_inv q := by
    classical
    funext a
    change F.simpleHomBasis X F.unitLabel a ≫
      (∑ b, F.compositionDual (F.simpleHomBasis X F.unitLabel) b ≫ q b) = q a
    simp only [Preadditive.comp_sum, ← Category.assoc, F.basis_comp_compositionDual]
    simp only [ite_comp, Category.id_comp, zero_comp]
    rw [Finset.sum_eq_single a]
    · simp
    · intro b _ hb
      exact if_neg (Ne.symm hb)
    · simp
  map_add' f g := by
    funext a
    change _ ≫ (f.f + g.f) = _ ≫ f.f + _ ≫ g.f
    rw [Preadditive.comp_add]
  map_smul' z f := by
    funext a
    change F.simpleHomBasis X F.unitLabel a ≫ (z • f.f) =
      z • (F.simpleHomBasis X F.unitLabel a ≫ f.f)
    erw [Linear.comp_smul]

/-- The dimension is the product of the two unit multiplicities. -/
theorem finrank_opposite_braided (F : SphericalFusion C) (M : Modular F) (X Y : C) :
    Module.finrank ℂ (oppositeBraidedCenter X ⟶ Center.ofBraidedObj Y) =
      Module.finrank ℂ (𝟙_ C ⟶ X) * Module.finrank ℂ (𝟙_ C ⟶ Y) := by
  letI := F.homFinite
  rw [(oppositeBraidedHomEquiv F M X Y).finrank_eq, Module.finrank_pi_fintype]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [(homCongr F.unitIso (Iso.refl X)).finrank_eq,
    (homCongr F.unitIso (Iso.refl Y)).finrank_eq]

/-- The inverse-braided embedding, as a monoidal functor. -/
def oppositeBraidedFunctor : C ⥤ Center C :=
  @Center.ofBraided C _ _ (reverseBraiding C)

instance oppositeBraidedFunctor_monoidal :
    (oppositeBraidedFunctor (C := C)).Monoidal := by
  unfold oppositeBraidedFunctor
  infer_instance

section Pairing
variable {D : Type*} [Category D] [MonoidalCategory D] [Preadditive D]
  [Linear ℂ D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]

/-- Linear duality for a specified exact pairing, without a global rigid instance. -/
def pairingLeftHomEquiv (X V V' W : D) [ExactPairing V V'] :
    (V' ⊗ X ⟶ W) ≃ₗ[ℂ] (X ⟶ V ⊗ W) :=
  { tensorLeftHomEquiv X V V' W with
    map_add' := by
      intro f g
      simp [tensorLeftHomEquiv, MonoidalPreadditive.whiskerLeft_add,
        Preadditive.comp_add]
    map_smul' := by intro z f; simp [tensorLeftHomEquiv] }

/-- Right linear duality for a specified exact pairing. -/
def pairingRightHomEquiv (X V V' W : D) [ExactPairing V V'] :
    (X ⊗ V ⟶ W) ≃ₗ[ℂ] (X ⟶ W ⊗ V') :=
  { tensorRightHomEquiv X V V' W with
    map_add' := by
      intro f g
      simp [tensorRightHomEquiv, MonoidalPreadditive.add_whiskerRight,
        Preadditive.comp_add]
    map_smul' := by intro z f; simp [tensorRightHomEquiv] }
end Pairing

/-- Bend the two outer factors in the actual center. No rigidity or
semisimplicity of the whole center is assumed. -/
def mixedCenterHomEquiv (F : SphericalFusion C) (X Y K L : C) :
    (mixedCenter X Y ⟶ mixedCenter K L) ≃ₗ[ℂ]
      (oppositeBraidedCenter (Y ⊗ Lᘁ) ⟶ Center.ofBraidedObj (Xᘁ ⊗ K)) := by
  let B := Center.ofBraided C
  let N := oppositeBraidedFunctor (C := C)
  letI : ExactPairing (B.obj Xᘁ) (B.obj (Xᘁ)ᘁ) :=
    TensorCat.Reconstruction.exactPairingMap B Xᘁ (Xᘁ)ᘁ
  letI : ExactPairing (N.obj Lᘁ) (N.obj (Lᘁ)ᘁ) :=
    TensorCat.Reconstruction.exactPairingMap N Lᘁ (Lᘁ)ᘁ
  exact
    (homCongr (whiskerRightIso (B.mapIso (F.j X)) (N.obj Y))
      (Iso.refl (B.obj K ⊗ N.obj L))).trans
    ((pairingLeftHomEquiv (N.obj Y) (B.obj Xᘁ) (B.obj (Xᘁ)ᘁ)
      (B.obj K ⊗ N.obj L)).trans
    ((homCongr (Iso.refl (N.obj Y))
      ((α_ (B.obj Xᘁ) (B.obj K) (N.obj L)).symm ≪≫
        whiskerLeftIso (B.obj Xᘁ ⊗ B.obj K) (N.mapIso (F.j L)))).trans
    ((pairingRightHomEquiv (N.obj Y) (N.obj Lᘁ) (N.obj (Lᘁ)ᘁ)
      (B.obj Xᘁ ⊗ B.obj K)).symm.trans
    (homCongr (Functor.Monoidal.μIso N Y Lᘁ)
      (Functor.Monoidal.μIso B Xᘁ K)))))

/-- The mixed central Hom dimension factors into the two base Hom dimensions. -/
theorem finrank_mixedCenter_hom (F : SphericalFusion C) (M : Modular F)
    (X Y K L : C) :
    Module.finrank ℂ (mixedCenter X Y ⟶ mixedCenter K L) =
      Module.finrank ℂ (X ⟶ K) * Module.finrank ℂ (L ⟶ Y) := by
  rw [(mixedCenterHomEquiv F X Y K L).finrank_eq, finrank_opposite_braided F M]
  rw [← (rightDuality (𝟙_ C) L Y).finrank_eq,
    (homCongr (λ_ L) (Iso.refl Y)).finrank_eq,
    ← (leftDuality (𝟙_ C) Xᘁ K).finrank_eq,
    (homCongr ((ρ_ (Xᘁ)ᘁ) ≪≫ (F.j X).symm) (Iso.refl K)).finrank_eq]
  exact Nat.mul_comm _ _

open Classical in
/-- The full two-label Schur formula for the genuine mixed central Hom spaces. -/
theorem finrank_mixedCenter_simple_hom (F : SphericalFusion C) (M : Modular F)
    (i j k l : F.Label) :
    Module.finrank ℂ (mixedCenter (F.simple i) (F.simple j) ⟶
      mixedCenter (F.simple k) (F.simple l)) = if i = k ∧ j = l then 1 else 0 := by
  rw [finrank_mixedCenter_hom F M, F.finrank_hom_simple, F.finrank_hom_simple]
  split_ifs <;> simp_all

/-- In particular, different second labels have no central morphisms. -/
theorem mixedCenter_hom_eq_zero_of_second_ne (F : SphericalFusion C) (M : Modular F)
    (i j k l : F.Label) (hjl : j ≠ l)
    (f : mixedCenter (F.simple i) (F.simple j) ⟶
      mixedCenter (F.simple k) (F.simple l)) : f = 0 := by
  classical
  letI := F.homFinite
  letI := CenterLinear.hom_finiteDimensional
    (mixedCenter (F.simple i) (F.simple j)) (mixedCenter (F.simple k) (F.simple l))
  have hd : Module.finrank ℂ (mixedCenter (F.simple i) (F.simple j) ⟶
      mixedCenter (F.simple k) (F.simple l)) = 0 := by
    rw [finrank_mixedCenter_simple_hom F M]
    simp [hjl]
  letI := (Module.finrank_zero_iff.mp hd)
  exact Subsingleton.elim f 0

/-- Isomorphisms of mixed simple-labelled objects recover both labels. -/
theorem mixedCenter_iso_labels (F : SphericalFusion C) (M : Modular F)
    (i j k l : F.Label)
    (e : mixedCenter (F.simple i) (F.simple j) ≅
      mixedCenter (F.simple k) (F.simple l)) : i = k ∧ j = l := by
  classical
  have h := (homCongr (Iso.refl (mixedCenter (F.simple i) (F.simple j))) e).finrank_eq
  rw [finrank_mixedCenter_simple_hom F M, finrank_mixedCenter_simple_hom F M] at h
  by_contra hlabels
  simp [hlabels] at h

section CenterFusion
variable [RightRigidCategory (Center C)] [HasKernels (Center C)]
  [HasFiniteBiproducts (Center C)]

/-- In any supplied spherical fusion structure on the center, the mixed
simple-labelled objects are simple. This does not construct that structure. -/
theorem mixedCenter_simple (F : SphericalFusion C) (M : Modular F)
    (Z : SphericalFusion (Center C)) (i j : F.Label) :
    Simple (mixedCenter (F.simple i) (F.simple j)) := by
  classical
  obtain ⟨a, ⟨e⟩⟩ := Z.exists_simple_iso_of_finrank_end
    (mixedCenter (F.simple i) (F.simple j)) (by
      rw [finrank_mixedCenter_simple_hom F M]
      simp)
  letI := Z.simple_isSimple a
  exact Simple.of_iso e

end CenterFusion
end VOA.Huang.NgSchauenburg
