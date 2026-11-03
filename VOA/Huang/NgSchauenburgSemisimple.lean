import VOA.Huang.NgSchauenburgVafaChannels

/-! # Semisimple channel decompositions

The equivalences below split actual Hom spaces, including after tensoring a
chosen decomposition. Multiplicities are computed by Schur's lemma.
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

open Classical in
/-- Schur multiplicities for the specified irredundant simple family. -/
theorem finrank_hom_simple (i j : F.Label) :
    Module.finrank ℂ (F.simple i ⟶ F.simple j) = if i = j then 1 else 0 := by
  classical
  letI := F.simple_isSimple i
  letI := F.simple_isSimple j
  letI := F.homFinite (F.simple i) (F.simple i)
  letI := F.homFinite (F.simple i) (F.simple j)
  split_ifs with h
  · subst j
    exact finrank_endomorphism_simple_eq_one ℂ _
  · exact finrank_hom_simple_simple_eq_zero_of_not_iso ℂ (fun e => h (F.distinct i j ⟨e⟩))

/-- The linear Hom decomposition associated to any finite biproduct decomposition. -/
def homDecomposition {X : C} {n : ℕ} {a : Fin n → F.Label}
    (e : X ≅ ⨁ fun k => F.simple (a k)) (Z : C) :
    (Z ⟶ X) ≃ₗ[ℂ] ((k : Fin n) → (Z ⟶ F.simple (a k))) where
  toFun f k := f ≫ e.hom ≫ biproduct.π _ k
  invFun f := biproduct.lift f ≫ e.inv
  left_inv f := by
    have h : biproduct.lift (fun k => f ≫ e.hom ≫ biproduct.π _ k) = f ≫ e.hom := by
      ext k; simp
    dsimp only
    rw [h]; simp
  right_inv f := by ext k; simp
  map_add' f g := by ext k; simp [Preadditive.add_comp]
  map_smul' z f := by ext k; simp

open Classical in
/-- A chosen simple appears exactly `dim Hom(simple,X)` times. -/
theorem multiplicity_eq_card {X : C} {n : ℕ} {a : Fin n → F.Label}
    (e : X ≅ ⨁ fun k => F.simple (a k)) (i : F.Label) :
    Module.finrank ℂ (F.simple i ⟶ X) = (Finset.univ.filter (a · = i)).card := by
  classical
  letI := fun k => F.homFinite (F.simple i) (F.simple (a k))
  rw [(F.homDecomposition e (F.simple i)).finrank_eq, Module.finrank_pi_fintype]
  simp only [F.finrank_hom_simple, Finset.card_filter]
  exact Finset.sum_congr rfl fun k _ => by simp [eq_comm]

/-- Tensoring a decomposition on the right, expressed directly on Hom spaces. -/
def homTensorDecomposition {X : C} {n : ℕ} {a : Fin n → F.Label}
    (e : X ≅ ⨁ fun k => F.simple (a k)) (Y Z : C) :
    (Z ⟶ X ⊗ Y) ≃ₗ[ℂ] ((k : Fin n) → (Z ⟶ F.simple (a k) ⊗ Y)) where
  toFun f k := f ≫ (e.hom ≫ biproduct.π _ k) ▷ Y
  invFun f := ∑ k, f k ≫ (biproduct.ι (fun k => F.simple (a k)) k ≫ e.inv) ▷ Y
  left_inv f := by
    simp only [← comp_whiskerRight, Category.assoc,
      ← Preadditive.comp_sum, ← sum_whiskerRight,
      ← Preadditive.comp_sum]
    simp [← Category.assoc, ← Preadditive.sum_comp, biproduct.total]
  right_inv f := by
    classical
    funext k
    simp only [Preadditive.sum_comp, Category.assoc, ← comp_whiskerRight,
      Iso.inv_hom_id_assoc]
    rw [Finset.sum_eq_single k]
    · simp
    · intro j _ hj; simp [hj]
    · simp
  map_add' f g := by ext k; simp [Preadditive.add_comp]
  map_smul' z f := by ext k; simp

/-- The same channel decomposition, with the tensor factor on the left. -/
def homLeftTensorDecomposition {X : C} {n : ℕ} {a : Fin n → F.Label}
    (e : X ≅ ⨁ fun k => F.simple (a k)) (Y Z : C) :
    (Z ⟶ Y ⊗ X) ≃ₗ[ℂ] ((k : Fin n) → (Z ⟶ Y ⊗ F.simple (a k))) where
  toFun f k := f ≫ Y ◁ (e.hom ≫ biproduct.π _ k)
  invFun f := ∑ k, f k ≫ Y ◁ (biproduct.ι (fun k => F.simple (a k)) k ≫ e.inv)
  left_inv f := by
    simp only [← whiskerLeft_comp, Category.assoc,
      ← Preadditive.comp_sum, ← whiskerLeft_sum,
      ← Preadditive.comp_sum]
    simp [← Category.assoc, ← Preadditive.sum_comp, biproduct.total]
  right_inv f := by
    classical
    funext k
    simp only [Preadditive.sum_comp, Category.assoc, ← whiskerLeft_comp,
      Iso.inv_hom_id_assoc]
    rw [Finset.sum_eq_single k]
    · simp
    · intro j _ hj; simp [hj]
    · simp
  map_add' f g := by ext k; simp [Preadditive.add_comp]
  map_smul' z f := by ext k; simp

/-- Regroup a sum over chosen summands by its intrinsic simple multiplicities. -/
theorem sum_decomposition {X : C} {n : ℕ} {a : Fin n → F.Label}
    (e : X ≅ ⨁ fun k => F.simple (a k)) (b : F.Label → ℕ) :
    (∑ k, b (a k)) = ∑ i, Module.finrank ℂ (F.simple i ⟶ X) * b i := by
  classical
  simp only [F.multiplicity_eq_card e, Finset.card_eq_sum_ones, Finset.sum_mul,
    one_mul]
  rw [← Finset.sum_fiberwise_of_maps_to (f := fun k => b (a k))
    (fun k _ => Finset.mem_univ (a k))]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k hk => by
    rw [(Finset.mem_filter.mp hk).2]

/-- Dimension of a three-point Hom space, splitting the first tensor block. -/
theorem finrank_tensor (X Y Z : C) :
    Module.finrank ℂ (Z ⟶ X ⊗ Y) =
      ∑ i, Module.finrank ℂ (F.simple i ⟶ X) *
        Module.finrank ℂ (Z ⟶ F.simple i ⊗ Y) := by
  classical
  obtain ⟨n, a, ⟨e⟩⟩ := F.decomposition X
  letI := fun k => F.homFinite Z (F.simple (a k) ⊗ Y)
  rw [(F.homTensorDecomposition e Y Z).finrank_eq, Module.finrank_pi_fintype]
  exact F.sum_decomposition e (fun i => Module.finrank ℂ (Z ⟶ F.simple i ⊗ Y))

/-- Dimension of a three-point Hom space, splitting the second tensor block. -/
theorem finrank_leftTensor (X Y Z : C) :
    Module.finrank ℂ (Z ⟶ Y ⊗ X) =
      ∑ i, Module.finrank ℂ (F.simple i ⟶ X) *
        Module.finrank ℂ (Z ⟶ Y ⊗ F.simple i) := by
  classical
  obtain ⟨n, a, ⟨e⟩⟩ := F.decomposition X
  letI := fun k => F.homFinite Z (Y ⊗ F.simple (a k))
  rw [(F.homLeftTensorDecomposition e Y Z).finrank_eq, Module.finrank_pi_fintype]
  exact F.sum_decomposition e (fun i => Module.finrank ℂ (Z ⟶ Y ⊗ F.simple i))

/-- Associativity of the actual natural-number fusion multiplicities. -/
theorem fusion_assoc (i j k r : F.Label) :
    (∑ p, F.fusionMultiplicity i j (F.simple p) * F.fusionMultiplicity p k (F.simple r)) =
      ∑ p, F.fusionMultiplicity j k (F.simple p) * F.fusionMultiplicity i p (F.simple r) := by
  classical
  unfold fusionMultiplicity
  rw [← F.finrank_tensor, ← F.finrank_leftTensor]
  exact (homCongr (Iso.refl (F.simple r)) (α_ (F.simple i) (F.simple j) (F.simple k))).finrank_eq

end SphericalFusion
end VOA.Huang.NgSchauenburg
