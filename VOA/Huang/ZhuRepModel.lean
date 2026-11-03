/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Huang.ZhuRepRibbonPivotal
import VOA.Huang.ZhuRepSConj
import VOA.Huang.DLNBridgeGalois
import VOA.Huang.HuangModularityQDim

/-!
# The modular tensor category of a nice VOA in the Ng–Schauenburg formalization

For a nice VOA `W` with modular data `D`, the canonical small model `canonicalModel hW D hD` of
`Rep W` (Huang's braided tensor category, rigid by `huangRigidityInput_holds`) carries:

* `modelSphericalFusion` — a `NgSchauenburg.SphericalFusion` structure whose pivotal structure is
  the ribbon pivotal structure `ZhuRep.ribbonPivotal` of the conformal twist `θ = e^{2πiL(0)}`;
* `modelModular` — a `NgSchauenburg.Modular` structure (`j = θ u`, nondegenerate categorical `S`).

and the comparison with Zhu's modular data:

* `S_eq_S00_mul_categoricalS` — `D.S i j = S₀₀ · S^{NS}_{ij}` (the Ng–Schauenburg (1.6) matrix,
  which carries a dual on the first index), via Huang's `S_ab = S₀₀ conj S̃_ab` and the
  charge-conjugation identity `S_{σa,b} = conj S_{ab}` (`exists_charge_star`);
* `twistScalar_eq` — the categorical twist of `X_i` is `e^{2πi h_i}`.

No reversal of the braiding is needed: the natural choice `C = Rep V` matches Zhu's `ρ(S)`.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace VOA.Huang.ZhuRep

open CategoryTheory MonoidalCategory Limits Module
open VOA VOA.Classification.COne VOA.Huang.TensorCat VOA.Huang.TensorCat.RepPackaging
  VOA.Huang.TensorCat.BraidRibbon VOA.Huang.HuangRigid VOA.Huang.HuangModularity
  VOA.Huang.NgSchauenburg VOA.Huang.FusionProduct VOA.Huang.SPinning

attribute [-instance] hasRightDualUnit hasRightDualLeftDual

universe u

/-! ## The scalar identification of `End 𝟙` -/

section UnitScalar

variable {C : Type*} [Category C] [Preadditive C] [Linear ℂ C] [MonoidalCategory C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C]

/-- `ℂ ≅ End 𝟙` when `End 𝟙` is one-dimensional. -/
def unitScalarOf (h : finrank ℂ (𝟙_ C ⟶ 𝟙_ C) = 1) : ℂ ≃ₗ[ℂ] (𝟙_ C ⟶ 𝟙_ C) :=
  LinearEquiv.ofBijective (LinearMap.toSpanSingleton ℂ _ (𝟙 (𝟙_ C)))
    ⟨by
      have hid : 𝟙 (𝟙_ C) ≠ 0 := by
        intro h0
        have : ∀ g : 𝟙_ C ⟶ 𝟙_ C, g = 0 := fun g => by rw [← Category.id_comp g, h0, zero_comp]
        haveI : Subsingleton (𝟙_ C ⟶ 𝟙_ C) := ⟨fun a b => by rw [this a, this b]⟩
        rw [finrank_zero_of_subsingleton] at h
        exact zero_ne_one h
      intro z w hzw
      simp only [LinearMap.toSpanSingleton_apply] at hzw
      exact smul_left_injective ℂ hid hzw,
    fun f => ⟨toScalar f, toScalar_smul_id h f⟩⟩

theorem unitScalarOf_apply (h : finrank ℂ (𝟙_ C ⟶ 𝟙_ C) = 1) (z : ℂ) :
    unitScalarOf h z = z • 𝟙 (𝟙_ C) := rfl

theorem unitScalarOf_symm_apply (h : finrank ℂ (𝟙_ C ⟶ 𝟙_ C) = 1) (f : 𝟙_ C ⟶ 𝟙_ C) :
    (unitScalarOf h).symm f = toScalar f := by
  rw [LinearEquiv.symm_apply_eq, unitScalarOf_apply, toScalar_smul_id h]


end UnitScalar

/-! ## The canonical model -/

section Model

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
  (hW : Nice W) (D : VOA.Classification.COne.ModularData W) (hD : D.IsModularData)
  [r : RightRigidCategory (canonicalModel hW D hD).C]

local notation "𝕄" => canonicalModel hW D hD

include hD in
/-- The conformal twist is trivial on the tensor unit. -/
theorem modelTwist_unit : (modelTwist (𝕄).E (𝟙_ (𝕄).C)).hom = 𝟙 (𝟙_ (𝕄).C) := by
  letI F := (𝕄).fusion D hD
  have e : F.simple D.vac ≅ 𝟙_ (𝕄).C := F.unitIso
  have hs : (modelTwist (𝕄).E (F.simple D.vac)).hom = 𝟙 _ := by
    have := modelTwist_simple (𝕄).E D hD D.vac
    rw [hD.h_vac] at this
    simpa using this
  have hn := modelTwist_naturality (𝕄).E e.hom
  rw [hs, Category.id_comp] at hn
  calc (modelTwist (𝕄).E (𝟙_ (𝕄).C)).hom = e.inv ≫ e.hom ≫ (modelTwist (𝕄).E (𝟙_ (𝕄).C)).hom := by
        simp
    _ = 𝟙 _ := by rw [hn]; simp

/-- Huang's identification in the orientation `S_ab = S₀₀ conj S̃_ab` (the proof of
`HuangModularity.sMatchInput_of_qDimMatch`, which only records the disjunction). -/
theorem S_eq_S00_star_sTilde (a b : D.ι) :
    letI := (𝕄).fusion D hD
    D.S a b = (D.S00 : ℂ) * star
      (((𝕄).ribbon (modelPivotal 𝕄) (ribbonDualInput_of_nice hW (𝕄) D hD)).sTilde a b) := by
  letI F := (𝕄).fusion D hD
  set R := (𝕄).ribbon (modelPivotal 𝕄) (ribbonDualInput_of_nice hW (𝕄) D hD)
  have hT : ∀ x, R.T x = twistOf (D.h x : ℂ) := fun x =>
    (𝕄).ribbon_T D hD (modelPivotal 𝕄) (ribbonDualInput_of_nice hW (𝕄) D hD) x
  have hq' : ∀ c, R.qdim (F.simple c) = (D.d c : ℂ) := fun c => qdim_eq_d hW D hD c
  have hcat := sTilde_mul_T R a b
  simp_rw [fusionN_eq hW (𝕄) D hD, hT, hq'] at hcat
  have hc := congrArg star hcat
  simp only [star_mul', star_sum, star_natCast, Complex.star_def, Complex.conj_ofReal] at hc
  simp only [← Complex.star_def] at hc
  have hh : ∀ x : D.ι, star (twistOf ((D.h x : ℚ) : ℂ)) = (twistOf ((D.h x : ℚ) : ℂ))⁻¹ := by
    intro x
    have := star_twistOf ((D.h x : ℚ) : ℝ)
    simpa using this
  simp only [hh] at hc
  have hb := balancing_S hW D hD (S_symm hW D hD) a b
  have hc' : star (R.sTilde a b) * ((twistOf ((D.h a : ℚ) : ℂ))⁻¹ * (twistOf ((D.h b : ℚ) : ℂ))⁻¹)
      = ∑ c : D.ι, (fus D a b c : ℂ) * ((twistOf ((D.h c : ℚ) : ℂ))⁻¹ * (D.d c : ℂ)) := hc
  rw [← hc'] at hb
  have hta : twistOf ((D.h a : ℚ) : ℂ) ≠ 0 := Complex.exp_ne_zero _
  have htb : twistOf ((D.h b : ℚ) : ℂ) ≠ 0 := Complex.exp_ne_zero _
  have : (twistOf ((D.h a : ℚ) : ℂ))⁻¹ * (twistOf ((D.h b : ℚ) : ℂ))⁻¹ *
      ((D.S00 : ℂ) * star (R.sTilde a b)) =
      (twistOf ((D.h a : ℚ) : ℂ))⁻¹ * (twistOf ((D.h b : ℚ) : ℂ))⁻¹ * D.S a b := by
    rw [← hb]; ring
  exact (mul_left_cancel₀ (mul_ne_zero (inv_ne_zero hta) (inv_ne_zero htb)) this).symm

/-- The categorical dual of `X_x` is `X_{σx}` (the argument of `HuangModularity.fus_dual`). -/
theorem dual_simple_iso (σ : D.ι → D.ι) (hσ : ∀ x, σ (σ x) = x)
    (hvac : ∀ b x, fus D b x D.vac = if x = σ b then 1 else 0) (x : D.ι) :
    Nonempty ((modelSimple (𝕄).E D x)ᘁ ≅ modelSimple (𝕄).E D (σ x)) := by
  classical
  letI F := (𝕄).fusion D hD
  have hmult : ∀ c : D.ι, mult (F.simple x)ᘁ c = if c = σ x then 1 else 0 := by
    intro c
    let e1 : (F.simple c ⟶ (F.simple x)ᘁ) ≃ₗ[ℂ] (F.simple c ⟶ 𝟙_ (𝕄).C ⊗ (F.simple x)ᘁ) :=
      Linear.homCongr ℂ (Iso.refl _) (λ_ _).symm
    let e2 := (tensorRightHomLinearEquiv (F.simple c) (F.simple x) (F.simple x)ᘁ
      (𝟙_ (𝕄).C)).symm
    let e3 : (F.simple c ⊗ F.simple x ⟶ 𝟙_ (𝕄).C) ≃ₗ[ℂ]
        (F.simple c ⊗ F.simple x ⟶ F.simple D.vac) :=
      Linear.homCongr ℂ (Iso.refl _) F.unitIso.symm
    have h1 : mult (F.simple x)ᘁ c = finrank ℂ (F.simple c ⊗ F.simple x ⟶ F.simple D.vac) := by
      rw [mult, e1.finrank_eq, e2.finrank_eq, e3.finrank_eq]
    rw [h1, ← mult_eq_finrank_hom_to]
    have h2 := fusionN_eq hW (𝕄) D hD c x D.vac
    change mult (F.simple c ⊗ F.simple x) D.vac = _ at h2
    rw [h2, hvac]
    by_cases h : c = σ x
    · rw [if_pos h, if_pos (by rw [h, hσ])]
    · rw [if_neg h, if_neg (fun h' => h (by rw [h', hσ]))]
  obtain ⟨n, f, ⟨e⟩⟩ := F.semisimple (F.simple x)ᘁ
  have hcard : ∀ c, (Finset.univ.filter fun k => f k = c).card = if c = σ x then 1 else 0 :=
    fun c => by rw [← mult_eq_card f e c, hmult]
  have hn : n = 1 := by
    have := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin n)))
      (t := (Finset.univ : Finset F.ι)) (f := f) (fun _ _ => Finset.mem_univ _)
    rw [Finset.card_univ, Fintype.card_fin] at this
    rw [this]
    simp_rw [hcard]
    simp
  subst hn
  have hf0 : f 0 = σ x := by
    have h1 := hcard (σ x)
    rw [if_pos rfl] at h1
    obtain ⟨k, hk⟩ := Finset.card_pos.mp (by rw [h1]; exact Nat.one_pos)
    have hk0 : k = 0 := Subsingleton.elim _ _
    rw [← hk0]
    exact (Finset.mem_filter.mp hk).2
  exact ⟨e ≪≫ HuangModularity.biproductFinOneIso (fun k => F.simple (f k)) ≪≫ eqToIso (congrArg F.simple hf0)⟩

/-- **The Ng–Schauenburg spherical fusion category of `Rep W`.** -/
def modelSphericalFusion : SphericalFusion (𝕄).C :=
  letI F := (𝕄).fusion D hD
  { toPivotal := ribbonPivotal (modelTwist (𝕄).E) (modelTwist_naturality (𝕄).E) (𝕄).balance
      (modelTwist_unit hW D hD)
    Label := D.ι
    simple := modelSimple (𝕄).E D
    simple_isSimple := modelSimple_isSimple (𝕄).E D hD
    unitLabel := D.vac
    unitIso := F.unitIso
    distinct := F.inequivalent
    decomposition := F.semisimple
    homFinite := F.finiteDimensional
    unitScalar := unitScalarOf (FusionCategory.finrank_end_unit (F := F))
    unitScalar_apply := unitScalarOf_apply _
    spherical := ribbonPivotal_spherical _ _ _ _ (ribbonDualInput_of_nice hW (𝕄) D hD) }

theorem modelSphericalFusion_unitScalar_symm (g : 𝟙_ (𝕄).C ⟶ 𝟙_ (𝕄).C) :
    (modelSphericalFusion hW D hD).unitScalar.symm g = toScalar g :=
  unitScalarOf_symm_apply (FusionCategory.finrank_end_unit (F := (𝕄).fusion D hD)) g

theorem modelSphericalFusion_traceRight {X : (𝕄).C} (g : X ⟶ X) :
    (modelSphericalFusion hW D hD).traceRight g = (modelPivotal 𝕄).trL g := rfl

/-- **Zhu's `S` is `S₀₀` times the Ng–Schauenburg categorical `S`** of `Rep W`, given a charge
conjugation `σ` with `S_{σa,b} = conj S_{ab}` (supplied by `exists_charge_star`). -/
theorem S_eq_S00_mul_categoricalS (σ : D.ι → D.ι) (hσ : ∀ x, σ (σ x) = x)
    (hvac : ∀ b x, fus D b x D.vac = if x = σ b then 1 else 0)
    (hstar : ∀ a b, D.S (σ a) b = star (D.S a b)) (i j : D.ι) :
    D.S i j = (D.S00 : ℂ) * categoricalS (modelSphericalFusion hW D hD) i j := by
  letI F := (𝕄).fusion D hD
  obtain ⟨e⟩ := dual_simple_iso hW D hD σ hσ hvac i
  have hmono : (β_ (modelSimple (𝕄).E D i)ᘁ (modelSimple (𝕄).E D j)).hom ≫
      (β_ (modelSimple (𝕄).E D j) (modelSimple (𝕄).E D i)ᘁ).hom =
      (whiskerRightIso e (modelSimple (𝕄).E D j)).hom ≫
        ((β_ (modelSimple (𝕄).E D (σ i)) (modelSimple (𝕄).E D j)).hom ≫
          (β_ (modelSimple (𝕄).E D j) (modelSimple (𝕄).E D (σ i))).hom) ≫
        (whiskerRightIso e (modelSimple (𝕄).E D j)).inv := by
    simp only [whiskerRightIso_hom, whiskerRightIso_inv, Category.assoc]
    rw [BraidedCategory.braiding_naturality_left_assoc,
      BraidedCategory.braiding_naturality_right_assoc, ← comp_whiskerRight, Iso.hom_inv_id,
      id_whiskerRight, Category.comp_id]
  have hcat : categoricalS (modelSphericalFusion hW D hD) i j =
      ((𝕄).ribbon (modelPivotal 𝕄) (ribbonDualInput_of_nice hW (𝕄) D hD)).sTilde (σ i) j := by
    unfold categoricalS
    rw [modelSphericalFusion_unitScalar_symm, modelSphericalFusion_traceRight]
    change toScalar ((modelPivotal 𝕄).trL ((β_ (modelSimple (𝕄).E D i)ᘁ
      (modelSimple (𝕄).E D j)).hom ≫ (β_ (modelSimple (𝕄).E D j)
        (modelSimple (𝕄).E D i)ᘁ).hom)) = _
    rw [hmono, HuangModularity.trL_conj]
    rfl
  have h := S_eq_S00_star_sTilde hW D hD (σ i) j
  rw [hstar, ← hcat] at h
  calc D.S i j = star (star (D.S i j)) := (star_star _).symm
    _ = star ((D.S00 : ℂ) * star (categoricalS (modelSphericalFusion hW D hD) i j)) := by rw [h]
    _ = _ := by rw [star_mul', star_star, Complex.star_def, Complex.conj_ofReal]

include hW hD in
/-- Zhu's `S`-matrix of a nice VOA is invertible (`S² = C`, `C² = 1`). -/
theorem det_S_ne_zero : (Matrix.of D.S).det ≠ 0 := by
  obtain ⟨σ, hσ, -, hSC, -⟩ := exists_charge_star hW D hD
  have hC2 : (Matrix.of fun x y => if y = σ x then (1 : ℂ) else 0) *
      (Matrix.of fun x y => if y = σ x then (1 : ℂ) else 0) = 1 := by
    ext x y
    rw [Matrix.mul_apply, Finset.sum_eq_single (σ x)]
    · simp only [Matrix.of_apply, if_true, one_mul, Matrix.one_apply, hσ]
      by_cases h : x = y
      · subst h; simp
      · rw [if_neg (fun h' => h h'.symm), if_neg h]
    · intro k _ hk
      rw [Matrix.of_apply, Matrix.of_apply, if_neg hk, zero_mul]
    · simp
  refine Matrix.det_ne_zero_of_right_inverse (B := Matrix.of D.S *
    Matrix.of fun x y => if y = σ x then (1 : ℂ) else 0) ?_
  rw [← Matrix.mul_assoc, hSC, hC2]

/-- The categorical `S` of the model is `S₀₀⁻¹ · D.S`. -/
theorem categoricalS_model_eq :
    categoricalS (modelSphericalFusion hW D hD) = ((D.S00 : ℂ)⁻¹) • Matrix.of D.S := by
  obtain ⟨σ, hσ, hvac, -, hstar⟩ := exists_charge_star hW D hD
  have hS0 : (D.S00 : ℂ) ≠ 0 := by exact_mod_cast hD.S00_pos.ne'
  ext i j
  rw [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul,
    S_eq_S00_mul_categoricalS hW D hD σ hσ hvac hstar i j, ← mul_assoc, inv_mul_cancel₀ hS0,
    one_mul]

/-- **The modular structure of `Rep W`** in the Ng–Schauenburg formalization: ribbon twist
`θ = e^{2πiL(0)}` with `j = θ u`, and nondegenerate categorical `S`. -/
def modelModular : Modular (modelSphericalFusion hW D hD) where
  toRibbon := ribbonOfTwist (modelTwist (𝕄).E) (modelTwist_naturality (𝕄).E) (𝕄).balance
    (modelTwist_unit hW D hD) (ribbonDualInput_of_nice hW (𝕄) D hD)
  nondegenerate := by
    have hS0 : (D.S00 : ℂ) ≠ 0 := by exact_mod_cast hD.S00_pos.ne'
    have hdet : (((D.S00 : ℂ)⁻¹) • Matrix.of D.S).det ≠ 0 := by
      rw [Matrix.det_smul]
      exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hS0)) (det_S_ne_zero hW D hD)
    unfold NondegenerateS
    rw [categoricalS_model_eq]
    convert hdet

/-- The categorical twist eigenvalue of `X_i` is `e^{2πi h_i}`. -/
theorem twistScalar_model (i : D.ι) :
    (modelModular hW D hD).twistScalar i = Complex.exp (2 * Real.pi * Complex.I * (D.h i : ℂ)) := by
  letI := modelSimple_isSimple (𝕄).E D hD i
  have h1 := (modelModular hW D hD).toRibbon.twistScalar_smul_id i
  have h2 := modelTwist_simple (𝕄).E D hD i
  change _ • 𝟙 (modelSimple (𝕄).E D i) = (modelTwist (𝕄).E (modelSimple (𝕄).E D i)).hom at h1
  rw [h2] at h1
  exact smul_left_injective ℂ (id_nonzero (modelSimple (𝕄).E D i)) h1

end Model

end VOA.Huang.ZhuRep
