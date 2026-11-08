import VOA.Core.TensorFieldLift
import VOA.Core.LocalSystemBare
import VOA.Core.VertexOperatorAlgebra

/-! Tensor state fields without finite-dimensionality or boundedness assumptions. -/

namespace VOA.Moonshine.ConwayNorton

open scoped TensorProduct
open Module (End)
open TensorFieldLift

variable {A B : Type*} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]

theorem nearField_isField (V : NearVOA A) (a : A) : IsField (V.Y a) := by
  intro x
  obtain ⟨N, hN⟩ := V.regularity a x
  refine ⟨-N, fun s hs => ?_⟩
  have h := hN (-s - 1) (by omega)
  simpa only [mode_apply, show -(-s - 1) - 1 = s from by omega] using h

noncomputable def nearFirstField (V : NearVOA A) :
    A →ₗ[ℂ] FormalDist (End ℂ (A ⊗[ℂ] B)) where
  toFun a := firstField (V.Y a)
  map_add' a b := by
    funext s
    exact congrArg (fun f : FormalDist (End ℂ A) => LinearMap.rTensor B (f s))
      (V.Y.map_add a b) |>.trans (LinearMap.rTensor_add _ _ _)
  map_smul' c a := by
    funext s
    exact congrArg (fun f : FormalDist (End ℂ A) => LinearMap.rTensor B (f s))
      (V.Y.map_smul c a) |>.trans (LinearMap.rTensor_smul _ _ _)

noncomputable def nearSecondField (W : NearVOA B) :
    B →ₗ[ℂ] FormalDist (End ℂ (A ⊗[ℂ] B)) where
  toFun b := secondField (W.Y b)
  map_add' a b := by
    funext s
    exact congrArg (fun f : FormalDist (End ℂ B) => LinearMap.lTensor A (f s))
      (W.Y.map_add a b) |>.trans (LinearMap.lTensor_add _ _ _)
  map_smul' c a := by
    funext s
    exact congrArg (fun f : FormalDist (End ℂ B) => LinearMap.lTensor A (f s))
      (W.Y.map_smul c a) |>.trans (LinearMap.lTensor_smul _ _ _)

theorem nearNormalProduct_congr {M : Type*} [AddCommGroup M] [Module ℂ M]
    {a b a' b' : FormalDist (End ℂ M)} (ha : IsField a) (hb : IsField b)
    (ha' : IsField a') (hb' : IsField b') (h : a = a') (h' : b = b') :
    nprod ha hb = nprod ha' hb' := by
  subst h; subst h'; rfl

/-- Bilinearity of the normal product packages the tensor field with no infinite sums of maps. -/
noncomputable def nearTensorFieldBilinear (V : NearVOA A) (W : NearVOA B) :
    A →ₗ[ℂ] B →ₗ[ℂ] FormalDist (End ℂ (A ⊗[ℂ] B)) where
  toFun a :=
    { toFun b := nprod (isField_firstField (nearField_isField V a))
        (isField_secondField (nearField_isField W b))
      map_add' b c := by
        exact (nearNormalProduct_congr _ _ _ _ rfl
          ((nearSecondField (A := A) W).map_add b c)).trans
            (Fld.nprod_add_right (isField_firstField (nearField_isField V a))
              (isField_secondField (nearField_isField W b))
              (isField_secondField (nearField_isField W c)))
      map_smul' c b := by
        exact (nearNormalProduct_congr _ _ _ _ rfl
          ((nearSecondField (A := A) W).map_smul c b)).trans
            (Fld.nprod_smul_right c (isField_firstField (nearField_isField V a))
              (isField_secondField (nearField_isField W b))) }
  map_add' a b := by
    apply LinearMap.ext
    intro c
    exact (nearNormalProduct_congr
      (isField_firstField (nearField_isField V (a + b)))
      (isField_secondField (nearField_isField W c)) _ _
      ((nearFirstField (B := B) V).map_add a b) rfl).trans
        (Fld.nprod_add_left (isField_firstField (nearField_isField V a))
          (isField_firstField (nearField_isField V b))
          (isField_secondField (nearField_isField W c)))
  map_smul' c a := by
    apply LinearMap.ext
    intro b
    exact (nearNormalProduct_congr
      (isField_firstField (nearField_isField V (c • a)))
      (isField_secondField (nearField_isField W b)) _ _
      ((nearFirstField (B := B) V).map_smul c a) rfl).trans
        (Fld.nprod_smul_left c (isField_firstField (nearField_isField V a))
          (isField_secondField (nearField_isField W b)))

/-- The state–field map on the algebraic tensor product. -/
noncomputable def nearTensorField (V : NearVOA A) (W : NearVOA B) :
    A ⊗[ℂ] B →ₗ[ℂ] FormalDist (End ℂ (A ⊗[ℂ] B)) :=
  TensorProduct.lift (nearTensorFieldBilinear V W)

theorem nearTensorField_tmul (V : NearVOA A) (W : NearVOA B) (a : A) (b : B) :
    nearTensorField V W (a ⊗ₜ b) = nprod (isField_firstField (nearField_isField V a))
      (isField_secondField (nearField_isField W b)) := rfl

theorem nearTensorField_tmul_apply (V : NearVOA A) (W : NearVOA B)
    (a x : A) (b y : B) (s : ℤ) :
    nearTensorField V W (a ⊗ₜ b) s (x ⊗ₜ y) =
      ∑ᶠ m : ℤ, (V.Y a m x) ⊗ₜ[ℂ] (W.Y b (s - m) y) := by
  rw [nearTensorField_tmul,
    nprod_firstField_secondField_apply (nearField_isField V a) (nearField_isField W b)]
  apply finsum_congr
  intro m
  simp only [Module.End.mul_apply, secondField_tmul, firstField_tmul]

theorem nearTensorField_isField (V : NearVOA A) (W : NearVOA B) (u : A ⊗[ℂ] B) :
    IsField (nearTensorField V W u) := by
  induction u using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact Fld.isField_zero
  | tmul a b =>
      exact (isField_firstField (B := B) (nearField_isField V a)).nprod
        (isField_secondField (A := A) (nearField_isField W b))
  | add u v hu hv => rw [map_add]; exact Fld.isField_add hu hv

theorem nearTensorField_local_tmul (V : NearVOA A) (W : NearVOA B)
    (a a' : A) (b b' : B) :
    Local (nearTensorField V W (a ⊗ₜ b)) (nearTensorField V W (a' ⊗ₜ b')) := by
  rw [nearTensorField_tmul, nearTensorField_tmul]
  apply dong_neg
  · exact local_firstField_secondField _ _
  · exact (dong_neg _ _ (local_firstField_secondField _ _)
      (local_firstField (V.locality a' a)) (Local.symm (local_firstField_secondField _ _))).symm
  · exact (dong_neg _ _ (local_firstField_secondField _ _)
      (local_firstField_secondField _ _) (local_secondField (W.locality b' b))).symm

theorem nearTensorField_local (V : NearVOA A) (W : NearVOA B) (u v : A ⊗[ℂ] B) :
    Local (nearTensorField V W u) (nearTensorField V W v) := by
  induction u using TensorProduct.induction_on with
  | zero =>
      rw [map_zero]
      exact local_of_bracketDist_eq_zero
        (by funext m n; change (0 : End ℂ (A ⊗[ℂ] B)) * _ - _ * 0 = 0; simp)
  | add u u' hu hu' => rw [map_add]; exact Reconstruction.Local.add_left hu hu'
  | tmul a b =>
      induction v using TensorProduct.induction_on with
      | zero =>
          rw [map_zero]
          exact local_of_bracketDist_eq_zero
            (by funext m n; change _ * (0 : End ℂ (A ⊗[ℂ] B)) - 0 * _ = 0; simp)
      | add v v' hv hv' => rw [map_add]; exact (Reconstruction.Local.add_left hv.symm hv'.symm).symm
      | tmul a' b' => exact nearTensorField_local_tmul V W a a' b b'

theorem nearField_vacuum_neg (V : NearVOA A) (a : A) (s : ℤ) (hs : s < 0) :
    V.Y a s V.vacuum = 0 := by
  have h := (V.creation a).2 (-s - 1) (by omega)
  simpa only [mode_apply, show -(-s - 1) - 1 = s from by omega] using h

theorem nearField_vacuum_zero (V : NearVOA A) (a : A) : V.Y a 0 V.vacuum = a := by
  simpa only [mode_apply, neg_neg, sub_self] using (V.creation a).1

theorem nearTensorField_creation (V : NearVOA A) (W : NearVOA B) (u : A ⊗[ℂ] B) :
    nearTensorField V W u 0 (V.vacuum ⊗ₜ W.vacuum) = u ∧
      ∀ s : ℤ, s < 0 → nearTensorField V W u s (V.vacuum ⊗ₜ W.vacuum) = 0 := by
  induction u using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact ⟨rfl, fun _ _ => rfl⟩
  | add u v hu hv =>
      constructor
      · rw [map_add]
        change nearTensorField V W u 0 _ + nearTensorField V W v 0 _ = _
        rw [hu.1, hv.1]
      · intro s hs
        rw [map_add]
        change nearTensorField V W u s _ + nearTensorField V W v s _ = _
        rw [hu.2 s hs, hv.2 s hs, add_zero]
  | tmul a b =>
      have hf : ∀ s : ℤ, s < 0 →
          firstField (B := B) (V.Y a) s (V.vacuum ⊗ₜ W.vacuum) = 0 := by
        intro s hs; rw [firstField_tmul, nearField_vacuum_neg V a s hs, TensorProduct.zero_tmul]
      have hg : ∀ s : ℤ, s < 0 →
          secondField (A := A) (W.Y b) s (V.vacuum ⊗ₜ W.vacuum) = 0 := by
        intro s hs; rw [secondField_tmul, nearField_vacuum_neg W b s hs, TensorProduct.tmul_zero]
      rw [nearTensorField_tmul]
      constructor
      · rw [nprod_vacuum_base_gen _ _ _ hf hg, secondField_tmul, firstField_tmul,
          nearField_vacuum_zero, nearField_vacuum_zero]
      · exact fun s hs => nprod_vacuum_neg_gen _ _ _ hf hg hs

end VOA.Moonshine.ConwayNorton
