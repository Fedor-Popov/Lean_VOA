import VOA.Huang.NgSchauenburgMixedHom

/-! # The dimension-count criterion for mixed-center exhaustion

The Schur formula supplies an injection into the simple labels of any supplied
spherical fusion center. Exhaustion is equivalent to the expected global
dimension equality. The center-dimension theorem itself is not assumed proved.
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
  [RightRigidCategory (Center C)] [HasKernels (Center C)]
  [HasFiniteBiproducts (Center C)]

/-- Each mixed object has a label in the supplied semisimple center. -/
theorem exists_mixedCenter_label (F : SphericalFusion C) (M : Modular F)
    (Z : SphericalFusion (Center C)) (p : F.Label × F.Label) :
    ∃ a, Nonempty (mixedCenter (F.simple p.1) (F.simple p.2) ≅ Z.simple a) := by
  apply Z.exists_simple_iso_of_finrank_end
  classical
  rw [finrank_mixedCenter_simple_hom F M]
  simp

/-- The label of a mixed object; injectivity is proved below. -/
def mixedCenterLabel (F : SphericalFusion C) (M : Modular F)
    (Z : SphericalFusion (Center C)) (p : F.Label × F.Label) : Z.Label :=
  (exists_mixedCenter_label F M Z p).choose

/-- The label is witnessed by an actual central isomorphism. -/
def mixedCenterLabelIso (F : SphericalFusion C) (M : Modular F)
    (Z : SphericalFusion (Center C)) (p : F.Label × F.Label) :
    mixedCenter (F.simple p.1) (F.simple p.2) ≅ Z.simple (mixedCenterLabel F M Z p) :=
  (exists_mixedCenter_label F M Z p).choose_spec.some

/-- No two pairs have the same central simple label. -/
theorem mixedCenterLabel_injective (F : SphericalFusion C) (M : Modular F)
    (Z : SphericalFusion (Center C)) : Function.Injective (mixedCenterLabel F M Z) := by
  intro p q h
  have e := mixedCenterLabelIso F M Z p ≪≫ eqToIso (congrArg Z.simple h) ≪≫
    (mixedCenterLabelIso F M Z q).symm
  obtain ⟨h₁, h₂⟩ := mixedCenter_iso_labels F M p.1 p.2 q.1 q.2 e
  exact Prod.ext h₁ h₂

/-- Trace compatibility identifies the intrinsic central dimensions of the family. -/
theorem mixedCenterLabel_dimension (F : SphericalFusion C) (M : Modular F)
    (Z : SphericalFusion (Center C)) (hc : CenterTraceCompatible F Z)
    (p : F.Label × F.Label) :
    Z.dimension (Z.simple (mixedCenterLabel F M Z p)) =
      F.dimension (F.simple p.1) * F.dimension (F.simple p.2) := by
  rw [← Z.dimension_iso (mixedCenterLabelIso F M Z p)]
  have h := hc (mixedCenter (F.simple p.1) (F.simple p.2)) (𝟙 _)
  change Z.dimension (mixedCenter (F.simple p.1) (F.simple p.2)) =
    F.dimension (mixedCenter (F.simple p.1) (F.simple p.2)).1 at h
  rw [h, mixedCenter_dimension]

/-- Strict positivity makes a dimension-preserving injection exhaustive. -/
theorem surjective_of_positive_mass {I J : Type*} [Fintype I] [Fintype J]
    (f : I → J) (hf : Function.Injective f) (w : J → ℝ) (hw : ∀ j, 0 < w j)
    (hm : (∑ i, w (f i)) = ∑ j, w j) : Function.Surjective f := by
  classical
  intro j
  by_contra hj
  have hnot : j ∉ Finset.univ.image f := by simpa using hj
  have hlt := Finset.sum_lt_sum_of_subset (Finset.subset_univ (Finset.univ.image f))
    (Finset.mem_univ j) hnot (hw j) (fun k _ _ => (hw k).le)
  rw [Finset.sum_image (fun a _ b _ h => hf h)] at hlt
  exact (ne_of_lt hlt) hm

/-- The missing center-dimension equality suffices for exhaustion. It is an
explicit premise, not a conclusion of the mixed-family dimension sum. -/
theorem mixedCenterLabel_surjective_of_globalDimension (F : SphericalFusion C)
    (M : Modular F) (Z : SphericalFusion (Center C)) (hc : CenterTraceCompatible F Z)
    (hd : Z.globalDimension = F.globalDimension ^ 2) :
    Function.Surjective (mixedCenterLabel F M Z) := by
  classical
  choose w hw he using Z.dimension_simple_sq_pos
  apply surjective_of_positive_mass _ (mixedCenterLabel_injective F M Z) w hw
  apply Complex.ofReal_injective
  push_cast
  simp only [← he]
  rw [← SphericalFusion.globalDimension, hd]
  simp only [mixedCenterLabel_dimension F M Z hc, Fintype.sum_prod_type]
  simpa only [mixedCenter_dimension] using mixedCenter_dimension_mass F

/-- Exhaustion by mixed objects is exactly the remaining dimension equality,
for a supplied trace-compatible spherical fusion center. -/
theorem mixedCenter_exhaustion_iff_globalDimension (F : SphericalFusion C)
    (M : Modular F) (Z : SphericalFusion (Center C)) (hc : CenterTraceCompatible F Z) :
    (∀ a : Z.Label, ∃ i j : F.Label,
      Nonempty (Z.simple a ≅ mixedCenter (F.simple i) (F.simple j))) ↔
        Z.globalDimension = F.globalDimension ^ 2 := by
  classical
  constructor
  · intro hex
    have hs : Function.Surjective (mixedCenterLabel F M Z) := by
      intro a
      obtain ⟨i, j, ⟨e⟩⟩ := hex a
      refine ⟨(i, j), Z.distinct _ _ ?_⟩
      exact ⟨(mixedCenterLabelIso F M Z (i, j)).symm ≪≫ e.symm⟩
    let e := Equiv.ofBijective (mixedCenterLabel F M Z)
      ⟨mixedCenterLabel_injective F M Z, hs⟩
    calc
      Z.globalDimension = ∑ p : F.Label × F.Label,
          Z.dimension (Z.simple (mixedCenterLabel F M Z p)) ^ 2 :=
        (e.sum_comp (fun a => Z.dimension (Z.simple a) ^ 2)).symm
      _ = F.globalDimension ^ 2 := by
        simp only [mixedCenterLabel_dimension F M Z hc, Fintype.sum_prod_type]
        simpa only [mixedCenter_dimension] using mixedCenter_dimension_mass F
  · intro hd a
    obtain ⟨p, hp⟩ := mixedCenterLabel_surjective_of_globalDimension F M Z hc hd a
    exact ⟨p.1, p.2, ⟨eqToIso (congrArg Z.simple hp.symm) ≪≫
      (mixedCenterLabelIso F M Z p).symm⟩⟩

/-- The same dimension count covers every simple object, not only the chosen labels. -/
theorem mixedCenter_exhausts_simples_of_globalDimension (F : SphericalFusion C)
    (M : Modular F) (Z : SphericalFusion (Center C)) (hc : CenterTraceCompatible F Z)
    (hd : Z.globalDimension = F.globalDimension ^ 2) (A : Center C) [Simple A] :
    ∃ i j : F.Label, Nonempty (A ≅ mixedCenter (F.simple i) (F.simple j)) := by
  letI := Z.homFinite
  obtain ⟨a, ⟨e⟩⟩ := Z.exists_simple_iso_of_finrank_end A
    (finrank_endomorphism_simple_eq_one ℂ A)
  obtain ⟨i, j, ⟨f⟩⟩ := (mixedCenter_exhaustion_iff_globalDimension F M Z hc).mpr hd a
  exact ⟨i, j, ⟨e ≪≫ f⟩⟩

end VOA.Huang.NgSchauenburg
