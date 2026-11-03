import VOA.Huang.NgSchauenburgExponent

/-! # Categorical dimensions for the indicator exponent argument

These are identities of the actual pivotal trace, with no numerical dimension
function supplied as an additional hypothesis.
-/
noncomputable section
set_option linter.unusedSectionVars false
universe v u
namespace VOA.Huang.NgSchauenburg
open CategoryTheory MonoidalCategory Limits
attribute [-instance] hasRightDualUnit hasRightDualLeftDual

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]

namespace Pivotal

/-- Forgetting monoidality allows reuse of the established cyclic trace proof. -/
def traceStructure (P : Pivotal C) : TensorCat.PivotalStructure C where
  piv := P.j
  naturality := P.naturality

theorem traceRight_comp_comm (P : Pivotal C) {X Y : C} (f : X ⟶ Y) (g : Y ⟶ X) :
    P.traceRight (f ≫ g) = P.traceRight (g ≫ f) :=
  P.traceStructure.trL_comp_comm f g

theorem traceRight_sum (P : Pivotal C) {X : C} {I : Type*}
    (s : Finset I) (f : I → (X ⟶ X)) :
    P.traceRight (∑ i ∈ s, f i) = ∑ i ∈ s, P.traceRight (f i) :=
  P.traceStructure.trL_sum s f

theorem traceRight_iso (P : Pivotal C) {X Y : C} (e : X ≅ Y) :
    P.traceRight (𝟙 X) = P.traceRight (𝟙 Y) := by
  rw [← e.hom_inv_id, P.traceRight_comp_comm, e.inv_hom_id]

theorem traceLeft_id_eq_cup (P : Pivotal C) (X : C) :
    P.traceLeft (𝟙 X) = P.cup X ≫ ε_ X Xᘁ := by
  simp [traceLeft, cup]

theorem rotation_coevaluation (P : Pivotal C) (X : C) :
    rotation P X Xᘁ (η_ X Xᘁ) = P.cup X := by
  rw [rotation_eq_cup]
  have hb : bend (η_ X Xᘁ) = 𝟙 Xᘁ := by
    dsimp [bend, leftDuality, tensorLeftHomEquiv]
    simp
  rw [hb]
  simp

/-- Rotating both blocks of a cup identifies the left trace of the dual. -/
theorem traceLeft_dual_id (P : Pivotal C) (X : C) :
    P.traceLeft (𝟙 Xᘁ) = P.traceRight (𝟙 X) := by
  have h := rotation_rotation P (η_ X Xᘁ)
  rw [rotation_coevaluation] at h
  change rotation P Xᘁ X (η_ Xᘁ (Xᘁ)ᘁ ≫ Xᘁ ◁ (P.j X).inv) = _ at h
  rw [rotation_naturality_right, rotation_coevaluation] at h
  have hc : P.cup Xᘁ = η_ X Xᘁ ≫ (P.j X).hom ▷ Xᘁ := by
    rw [← h]
    simp
  rw [traceLeft_id_eq_cup, hc]
  simp [traceRight]

theorem traceRight_unit_id (P : Pivotal C) :
    P.traceRight (𝟙 (𝟙_ C)) = 𝟙 (𝟙_ C) := by
  simp only [traceRight, id_whiskerRight, Category.id_comp, P.unit,
    comp_whiskerRight, Category.assoc]
  rw [rightAdjointMate_comp_evaluation, P.unit_coevaluation, P.unit_evaluation]
  rw [Category.assoc, ← whisker_exchange_assoc, leftUnitor_inv_naturality_assoc]
  simp only [id_whiskerLeft, whiskerRight_id, Category.assoc, Iso.inv_hom_id_assoc,
    Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]
  monoidal_coherence

/-- Closing the nested pivotal cups proves tensor multiplicativity. -/
theorem traceLeft_tensor_id (P : Pivotal C) (X Y : C) (z : ℂ)
    (hz : P.traceLeft (𝟙 X) = z • 𝟙 (𝟙_ C)) :
    P.traceLeft (𝟙 (X ⊗ Y)) = z • P.traceLeft (𝟙 Y) := by
  have he : ε_ (X ⊗ Y) (X ⊗ Y)ᘁ =
      (P.dualTensor X Y).inv ▷ (X ⊗ Y) ≫ tensorDualEvaluation C X Y := by
    rw [← P.dualTensor_eval, ← comp_whiskerRight_assoc]
    simp
  rw [traceLeft_id_eq_cup, he, ← Category.assoc, P.cup_tensor]
  calc
    _ = P.cup Y ≫ Yᘁ ◁ (λ_ Y).inv ≫
        Yᘁ ◁ ((P.cup X ≫ ε_ X Xᘁ) ▷ Y) ≫ Yᘁ ◁ (λ_ Y).hom ≫ ε_ Y Yᘁ := by
      dsimp [tensorDualEvaluation]
      monoidal
    _ = _ := by
      rw [← traceLeft_id_eq_cup, hz]
      simp [traceLeft_id_eq_cup]

end Pivotal

variable [HasKernels C] [HasFiniteBiproducts C]
namespace SphericalFusion
variable (F : SphericalFusion C)

theorem dimension_iso {X Y : C} (e : X ≅ Y) : F.dimension X = F.dimension Y :=
  congrArg F.unitScalar.symm (F.toPivotal.traceRight_iso e)

theorem dimension_dual (X : C) : F.dimension Xᘁ = F.dimension X := by
  unfold dimension
  rw [← F.spherical, F.toPivotal.traceLeft_dual_id]

@[simp] theorem dimension_unit : F.dimension (𝟙_ C) = 1 := by
  unfold dimension
  rw [F.toPivotal.traceRight_unit_id]
  have h : F.unitScalar 1 = 𝟙 (𝟙_ C) := by simp [F.unitScalar_apply]
  rw [← h, F.unitScalar.symm_apply_apply]

@[simp] theorem dimension_unitLabel : F.dimension (F.simple F.unitLabel) = 1 := by
  rw [F.dimension_iso F.unitIso, F.dimension_unit]

theorem dimension_dualLabel (i : F.Label) :
    F.dimension (F.simple (F.dualLabel i)) = F.dimension (F.simple i) := by
  rw [← F.dimension_iso (F.dualLabelIso i), F.dimension_dual]

theorem dimension_tensor (X Y : C) :
    F.dimension (X ⊗ Y) = F.dimension X * F.dimension Y := by
  have hx : F.traceLeft (𝟙 X) = F.dimension X • 𝟙 (𝟙_ C) := by
    rw [F.spherical]
    exact (F.unitScalar_apply (F.dimension X)).symm.trans
      (F.unitScalar.apply_symm_apply _)
      |>.symm
  unfold dimension
  rw [← F.spherical, F.toPivotal.traceLeft_tensor_id X Y _ hx, map_smul,
    F.spherical]
  rfl

theorem dimension_decomposition {X : C} {n : ℕ} {a : Fin n → F.Label}
    (e : X ≅ ⨁ fun k => F.simple (a k)) :
    F.dimension X = ∑ k, F.dimension (F.simple (a k)) := by
  unfold dimension
  rw [F.toPivotal.traceRight_iso e]
  change F.unitScalar.symm (F.toPivotal.traceStructure.trL (𝟙 _)) = _
  rw [F.toPivotal.traceStructure.trL_biproduct]
  simp [map_sum, TensorCat.PivotalStructure.trL, Pivotal.traceStructure,
    Pivotal.traceRight]

/-- The categorical dimension is the dimension-weighted multiplicity sum. -/
theorem dimension_eq_sum (X : C) :
    F.dimension X = ∑ i, (Module.finrank ℂ (F.simple i ⟶ X) : ℂ) *
      F.dimension (F.simple i) := by
  classical
  obtain ⟨n, a, ⟨e⟩⟩ := F.decomposition X
  rw [F.dimension_decomposition e]
  simp only [F.multiplicity_eq_card e, Finset.card_eq_sum_ones, Nat.cast_sum,
    Nat.cast_one, Finset.sum_mul, one_mul]
  rw [← Finset.sum_fiberwise_of_maps_to (f := fun k => F.dimension (F.simple (a k)))
    (fun k _ => Finset.mem_univ (a k))]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k hk => by
    rw [(Finset.mem_filter.mp hk).2]

/-- The multiplicative dimension premise is a categorical theorem. -/
theorem fusion_dimension (i j : F.Label) :
    (∑ k, (F.fusionMultiplicity i j (F.simple k) : ℂ) * F.dimension (F.simple k)) =
      F.dimension (F.simple i) * F.dimension (F.simple j) := by
  rw [← F.dimension_tensor, F.dimension_eq_sum (F.simple i ⊗ F.simple j)]
  rfl

/-- The source-variable version of the semisimple Hom decomposition. -/
def homSourceDecomposition {X : C} {n : ℕ} {a : Fin n → F.Label}
    (e : X ≅ ⨁ fun k => F.simple (a k)) (Z : C) :
    (X ⟶ Z) ≃ₗ[ℂ] ((k : Fin n) → (F.simple (a k) ⟶ Z)) where
  toFun f k := biproduct.ι (fun k => F.simple (a k)) k ≫ e.inv ≫ f
  invFun f := e.hom ≫ biproduct.desc f
  left_inv f := by
    have h : biproduct.desc (fun k => biproduct.ι (fun k => F.simple (a k)) k ≫
        e.inv ≫ f) = e.inv ≫ f := by
      ext k; simp
    dsimp only
    rw [h]; simp
  right_inv f := by ext k; simp
  map_add' f g := by ext k; simp [Preadditive.comp_add]
  map_smul' z f := by ext k; simp

include F in
/-- Hom dimensions are symmetric in a finite semisimple category. -/
theorem finrank_hom_symm (X Y : C) :
    Module.finrank ℂ (X ⟶ Y) = Module.finrank ℂ (Y ⟶ X) := by
  classical
  obtain ⟨n, a, ⟨e⟩⟩ := F.decomposition X
  obtain ⟨m, b, ⟨f⟩⟩ := F.decomposition Y
  letI := F.homFinite
  rw [(F.homSourceDecomposition e Y).finrank_eq,
    (F.homDecomposition e Y).finrank_eq]
  simp only [Module.finrank_pi_fintype]
  apply Finset.sum_congr rfl
  intro k _
  rw [(F.homDecomposition f (F.simple (a k))).finrank_eq,
    (F.homSourceDecomposition f (F.simple (a k))).finrank_eq]
  simp [Module.finrank_pi_fintype, F.finrank_hom_simple, eq_comm]

/-- Rigidity, together with semisimplicity, gives fusion reciprocity. -/
theorem fusion_reciprocity (i j k : F.Label) :
    F.fusionMultiplicity i j (F.simple k) =
      F.fusionMultiplicity (F.dualLabel i) k (F.simple j) := by
  unfold fusionMultiplicity
  rw [← (leftDuality (F.simple k) (F.simple i) (F.simple j)).finrank_eq,
    F.finrank_hom_symm]
  exact (homCongr (Iso.refl _) (whiskerRightIso (F.dualLabelIso i) _)).finrank_eq

/-- The weighted sum of one fusion index is a tensor dimension. -/
theorem fusion_dimension_target (i : F.Label) (V : C) :
    (∑ j, (F.fusionMultiplicity i j V : ℂ) * F.dimension (F.simple j)) =
      F.dimension (F.simple i) * F.dimension V := by
  have h (j : F.Label) : F.fusionMultiplicity i j V =
      Module.finrank ℂ (F.simple j ⟶ (F.simple i)ᘁ ⊗ V) := by
    unfold fusionMultiplicity
    rw [← (leftDuality V (F.simple i) (F.simple j)).finrank_eq,
      F.finrank_hom_symm]
  simp only [h]
  rw [← F.dimension_eq_sum, F.dimension_tensor, F.dimension_dual]

/-- The double fusion-dimension sum needed by Bantay's exponent argument. -/
theorem fusion_dimension_mass (V : C) :
    (∑ i, ∑ j, (F.fusionMultiplicity i j V : ℂ) *
      F.dimension (F.simple i) * F.dimension (F.simple j)) =
      F.globalDimension * F.dimension V := by
  calc
    _ = ∑ i, F.dimension (F.simple i) *
        (∑ j, (F.fusionMultiplicity i j V : ℂ) * F.dimension (F.simple j)) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _; ring
    _ = _ := by
      simp only [F.fusion_dimension_target, globalDimension, Finset.sum_mul, pow_two,
        mul_assoc]

include F in
/-- A nonzero map out of a simple splits, by the actual finite decomposition. -/
theorem exists_retraction_of_simple {X Y : C} [Simple X] (f : X ⟶ Y) (hf : f ≠ 0) :
    ∃ g : Y ⟶ X, f ≫ g = 𝟙 X := by
  classical
  obtain ⟨n, a, ⟨e⟩⟩ := F.decomposition Y
  have hex : ∃ k, f ≫ e.hom ≫ biproduct.π _ k ≠ 0 := by
    by_contra! h
    apply hf
    apply (cancel_mono e.hom).mp
    apply biproduct.hom_ext
    intro k
    simpa using h k
  obtain ⟨k, hk⟩ := hex
  letI := F.simple_isSimple (a k)
  letI := (isIso_iff_nonzero (f ≫ e.hom ≫ biproduct.π _ k)).mpr hk
  refine ⟨e.hom ≫ biproduct.π _ k ≫ inv (f ≫ e.hom ≫ biproduct.π _ k), ?_⟩
  simp [← Category.assoc]

/-- A simple pivotal dimension cannot vanish; this uses semisimplicity, not positivity. -/
theorem dimension_simple_ne_zero (i : F.Label) : F.dimension (F.simple i) ≠ 0 := by
  let X := F.simple i
  letI : Simple X := F.simple_isSimple i
  letI := F.simple_unit
  letI := F.homFinite
  have heta : η_ X Xᘁ ≠ 0 := by
    intro h
    have hh := ExactPairing.evaluation_coevaluation X Xᘁ
    rw [h] at hh
    have : 𝟙 X = 0 := by
      have := congrArg (fun f => (λ_ X).inv ≫ f ≫ (ρ_ X).hom) hh
      simpa using this.symm
    exact id_nonzero X this
  have heps : ε_ X Xᘁ ≠ 0 := by
    intro h
    have hh := ExactPairing.evaluation_coevaluation X Xᘁ
    rw [h] at hh
    have : 𝟙 X = 0 := by
      have := congrArg (fun f => (λ_ X).inv ≫ f ≫ (ρ_ X).hom) hh
      simpa using this.symm
    exact id_nonzero X this
  have hcup : F.toPivotal.cup X ≠ 0 := by
    rw [← F.toPivotal.rotation_coevaluation]
    exact fun h => heta ((rotation F.toPivotal X Xᘁ).injective
      (h.trans (map_zero _).symm))
  obtain ⟨g, hg⟩ := F.exists_retraction_of_simple (F.toPivotal.cup X) hcup
  have hr : Module.finrank ℂ (Xᘁ ⊗ X ⟶ 𝟙_ C) = 1 := by
    rw [(leftDuality X X (𝟙_ C)).finrank_eq,
      (homCongr (Iso.refl X) (ρ_ X)).finrank_eq]
    exact finrank_endomorphism_simple_eq_one ℂ X
  obtain ⟨z, hz⟩ := (finrank_eq_one_iff_of_nonzero' (K := ℂ) _ heps).mp hr g
  intro hd
  have ht : F.traceLeft (𝟙 X) = 0 := by
    rw [F.spherical]
    have hh := congrArg F.unitScalar hd
    simpa [dimension, X] using hh
  rw [Pivotal.traceLeft_id_eq_cup] at ht
  rw [← hz, Linear.comp_smul, ht, smul_zero] at hg
  exact id_nonzero (𝟙_ C) hg.symm

/-- Spherical dimensions are real, by transposition of the fusion matrices. -/
theorem dimension_simple_conj (i : F.Label) :
    starRingEnd ℂ (F.dimension (F.simple i)) = F.dimension (F.simple i) := by
  classical
  let d := fun j => F.dimension (F.simple j)
  have ha : (∑ j, d j * starRingEnd ℂ (d j)) ≠ 0 := by
    have hp : 0 < ∑ j, Complex.normSq (d j) := by
      apply Finset.sum_pos' (fun j _ => Complex.normSq_nonneg (d j))
      refine ⟨F.unitLabel, Finset.mem_univ _, ?_⟩
      simp [d]
    have he : (∑ j, d j * starRingEnd ℂ (d j)) =
        ((∑ j, Complex.normSq (d j) : ℝ) : ℂ) := by
      simp [Complex.mul_conj]
    rw [he]
    exact_mod_cast hp.ne'
  apply mul_right_cancel₀ ha
  symm
  calc
    d i * (∑ j, d j * starRingEnd ℂ (d j)) =
        ∑ j, (∑ k, (F.fusionMultiplicity i j (F.simple k) : ℂ) * d k) *
          starRingEnd ℂ (d j) := by
      simp only [F.fusion_dimension, d, Finset.mul_sum, mul_assoc]
    _ = ∑ k, d k * starRingEnd ℂ
        (∑ j, (F.fusionMultiplicity (F.dualLabel i) k (F.simple j) : ℂ) * d j) := by
      simp only [Finset.sum_mul, map_sum, map_mul, map_natCast, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro j _
      rw [F.fusion_reciprocity]
      ring
    _ = starRingEnd ℂ (d i) * (∑ j, d j * starRingEnd ℂ (d j)) := by
      simp only [d, F.fusion_dimension, F.dimension_dualLabel, map_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _; ring

/-- The squared simple dimensions are strictly positive real numbers. -/
theorem dimension_simple_sq_pos (i : F.Label) :
    ∃ w : ℝ, 0 < w ∧ F.dimension (F.simple i) ^ 2 = (w : ℂ) := by
  refine ⟨Complex.normSq (F.dimension (F.simple i)),
    Complex.normSq_pos.mpr (F.dimension_simple_ne_zero i), ?_⟩
  calc
    _ = F.dimension (F.simple i) * starRingEnd ℂ (F.dimension (F.simple i)) := by
      rw [F.dimension_simple_conj, pow_two]
    _ = _ := Complex.mul_conj _

/-- All dimension hypotheses of the exponent argument are discharged. -/
theorem globalDimension_pos : ∃ w : ℝ, 0 < w ∧ F.globalDimension = (w : ℂ) := by
  classical
  choose w hw hd using F.dimension_simple_sq_pos
  refine ⟨∑ i, w i, Finset.sum_pos (fun i _ => hw i)
    ⟨F.unitLabel, Finset.mem_univ _⟩, ?_⟩
  simp [globalDimension, hd]

theorem globalDimension_ne_zero : F.globalDimension ≠ 0 := by
  obtain ⟨w, hw, he⟩ := F.globalDimension_pos
  rw [he]
  exact_mod_cast hw.ne'

end SphericalFusion

variable [BraidedCategory C]

/-- Bantay is the only remaining premise for FS exponent = raw twist order. -/
theorem modularExponentTheorem_of_bantay (F : SphericalFusion C) (M : Modular F)
    (hb : BantayFormula F M) : ModularExponentTheorem F M :=
  modularExponentTheorem_of_bantay_dimensions F M hb F.dimension_simple_sq_pos
    F.fusion_dimension F.fusion_dimension_mass

theorem isFSExponent_iff_twistOrder_dvd (F : SphericalFusion C) (M : Modular F)
    (hb : BantayFormula F M) {n : ℕ} (hn : 0 < n) :
    IsFSExponent F n ↔ M.toRibbon.twistOrder ∣ n :=
  isFSExponent_iff_twistOrder_dvd_of_bantay F M hb F.dimension_simple_sq_pos
    F.fusion_dimension F.fusion_dimension_mass hn

end VOA.Huang.NgSchauenburg
