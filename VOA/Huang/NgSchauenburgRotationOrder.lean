import VOA.Huang.NgSchauenburgBlockRotation

/-! # Iteration of pivotal tensor-block rotation -/
noncomputable section
set_option linter.unusedSectionVars false
universe v u
namespace VOA.Huang.NgSchauenburg
open CategoryTheory MonoidalCategory
attribute [-instance] hasRightDualUnit hasRightDualLeftDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- Concatenation of two positive right-associated tensor powers. -/
def joinPower (V : C) : (a b : ℕ) →
    tensorPower V (a + 1) ⊗ tensorPower V (b + 1) ≅ tensorPower V (a + b + 2)
  | a, 0 => appendPower V a
  | a, b + 1 => whiskerLeftIso (tensorPower V (a + 1)) (appendPower V b).symm ≪≫
      (α_ (tensorPower V (a + 1)) (tensorPower V (b + 1)) V).symm ≪≫
      whiskerRightIso (joinPower V a b) V ≪≫ appendPower V (a + b + 1)

@[simp] theorem joinPower_right_zero (V : C) (a : ℕ) :
    joinPower V a 0 = appendPower V a := rfl

@[simp] theorem joinPower_zero (V : C) (b : ℕ) :
    (joinPower V 0 b).hom = eqToHom (by simp only [Nat.zero_add]; rfl) := by
  induction b with
  | zero => rfl
  | succ b ih =>
    simp only [joinPower, Iso.trans_hom, whiskerLeftIso_hom, Iso.symm_hom,
      whiskerRightIso_hom, ih]
    dsimp only [tensorPower]
    simp only [eqToHom_whiskerRight]
    erw [← eqToHom_iso_hom_naturality (appendPower V) (show b + 1 = 0 + b + 1 by omega)]
    simp only [appendPower, Iso.trans_hom, whiskerLeftIso_hom]
    dsimp only [tensorPower]
    simp

/-- Concatenation commutes with appending the last factor. -/
theorem joinPower_append (V : C) (a b : ℕ) :
    (joinPower V a b).hom ▷ V ≫ (appendPower V (a + b + 1)).hom =
      (α_ (tensorPower V (a + 1)) (tensorPower V (b + 1)) V).hom ≫
        tensorPower V (a + 1) ◁ (appendPower V b).hom ≫ (joinPower V a (b + 1)).hom := by
  simp [joinPower]

/-- Concatenation also respects the first factor. -/
theorem joinPower_succ (V : C) (a b : ℕ) :
    (joinPower V (a + 1) b).hom =
      (α_ V (tensorPower V (a + 1)) (tensorPower V (b + 1))).hom ≫
        V ◁ (joinPower V a b).hom ≫ eqToHom (by
          change tensorPower V (a + b + 3) = tensorPower V (a + 1 + b + 2)
          congr 1; omega) := by
  induction b with
  | zero => simp [joinPower, appendPower, tensorPower]
  | succ b ih =>
    simp only [joinPower, Iso.trans_hom, whiskerLeftIso_hom, Iso.symm_hom,
      whiskerRightIso_hom, whiskerLeft_comp, Category.assoc, ih]
    dsimp only [tensorPower]
    simp only [comp_whiskerRight, Category.assoc, eqToHom_whiskerRight]
    erw [← eqToHom_iso_hom_naturality (appendPower V)
      (show a + b + 2 = a + 1 + b + 1 by omega)]
    simp only [appendPower, Iso.trans_hom, whiskerLeftIso_hom, whiskerLeft_comp,
      Category.assoc]
    monoidal

/-- Associativity of concatenation when the middle block is one factor. -/
theorem joinPower_middle (V : C) (a b : ℕ) :
    (appendPower V a).hom ▷ tensorPower V (b + 1) ≫ (joinPower V (a + 1) b).hom =
      (α_ (tensorPower V (a + 1)) V (tensorPower V (b + 1))).hom ≫
        (joinPower V a (b + 1)).hom ≫ eqToHom (by congr 1; omega) := by
  induction b with
  | zero =>
    simp only [joinPower, appendPower, Iso.trans_hom, Iso.symm_hom,
      whiskerLeftIso_hom, whiskerRightIso_hom, Iso.refl_inv]
    dsimp only [tensorPower]
    simp
  | succ b ih =>
    simp only [joinPower, Iso.trans_hom, Iso.symm_hom, whiskerLeftIso_hom,
      whiskerRightIso_hom]
    dsimp only [tensorPower]
    calc
      _ = (tensorPower V (a + 1) ⊗ V) ◁ (appendPower V b).inv ≫
          (α_ (tensorPower V (a + 1) ⊗ V) (tensorPower V (b + 1)) V).inv ≫
          ((appendPower V a).hom ▷ tensorPower V (b + 1) ≫
            (joinPower V (a + 1) b).hom) ▷ V ≫
          (appendPower V (a + 1 + b + 1)).hom := by
        simp only [comp_whiskerRight, Category.assoc]
        rw [← whisker_exchange_assoc, associator_inv_naturality_left_assoc]
        rfl
      _ = _ := by
        rw [ih]
        simp only [comp_whiskerRight, Category.assoc, eqToHom_whiskerRight]
        erw [← eqToHom_iso_hom_naturality (appendPower V)
          (show a + b + 2 = a + 1 + b + 1 by omega)]
        simp only [joinPower, appendPower, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
          whiskerLeftIso_hom, whiskerLeftIso_inv, whiskerRightIso_hom,
          whiskerLeft_comp, Category.assoc]
        dsimp only [tensorPower]
        monoidal

variable [RightRigidCategory C] [Preadditive C] [Linear ℂ C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C]

/-- Iteration is unchanged by transport of the tensor-power index. -/
theorem fsRotation_iterate_cast (P : Pivotal C) (V : C) {n m : ℕ} (h : n = m)
    (k : ℕ) (f : 𝟙_ C ⟶ tensorPower V n) :
    (fsRotation P V m)^[k] (f ≫ eqToHom (congrArg (tensorPower V) h)) =
      (fsRotation P V n)^[k] f ≫ eqToHom (congrArg (tensorPower V) h) := by
  subst m
  simp

/-- A single rotation commutes with index transport. -/
theorem fsRotation_cast (P : Pivotal C) (V : C) {n m : ℕ} (h : n = m)
    (f : 𝟙_ C ⟶ tensorPower V n) :
    fsRotation P V m (f ≫ eqToHom (congrArg (tensorPower V) h)) =
      fsRotation P V n f ≫ eqToHom (congrArg (tensorPower V) h) := by
  subst m
  simp

/-- The explicit action in degree at least two. -/
theorem fsRotation_apply (P : Pivotal C) (V : C) (n : ℕ)
    (f : 𝟙_ C ⟶ tensorPower V (n + 2)) :
    fsRotation P V (n + 2) f =
      rotation P V (tensorPower V (n + 1)) f ≫ (appendPower V n).hom := by
  change (𝟙 _ ≫ rotation P V (tensorPower V (n + 1)) f ≫ _) = _
  simp

/-- A single rotation enlarges the moved block by one factor. -/
theorem rotation_join_step (P : Pivotal C) (V : C) (a b : ℕ)
    (f : 𝟙_ C ⟶ tensorPower V (a + 1) ⊗ (V ⊗ tensorPower V (b + 1))) :
    fsRotation P V (b + a + 3)
      ((rotation P (tensorPower V (a + 1)) (V ⊗ tensorPower V (b + 1)) f ≫
          (α_ V (tensorPower V (b + 1)) (tensorPower V (a + 1))).hom) ≫
        V ◁ (joinPower V b a).hom) =
      rotation P (tensorPower V (a + 1) ⊗ V) (tensorPower V (b + 1))
        (f ≫ (α_ (tensorPower V (a + 1)) V (tensorPower V (b + 1))).inv) ≫
      tensorPower V (b + 1) ◁ (appendPower V a).hom ≫ (joinPower V b (a + 1)).hom := by
  rw [fsRotation_apply]
  erw [rotation_naturality_right]
  simp only [Category.assoc]
  rw [joinPower_append, ← Category.assoc, ← Category.assoc]
  rw [rotation_tensor]
  simp

/-- Iterated single rotations are the canonical tensor-block rotation. -/
theorem fsRotation_iterate_join (P : Pivotal C) (V : C) (a b : ℕ)
    (f : 𝟙_ C ⟶ tensorPower V (a + 1) ⊗ tensorPower V (b + 1)) :
    (fsRotation P V (a + b + 2))^[a + 1] (f ≫ (joinPower V a b).hom) =
      rotation P (tensorPower V (a + 1)) (tensorPower V (b + 1)) f ≫
        (joinPower V b a).hom ≫ eqToHom (by congr 1; omega) := by
  induction a generalizing b with
  | zero =>
    rw [joinPower_zero]
    erw [fsRotation_iterate_cast P V (show b + 2 = 0 + b + 2 by omega) 1 f]
    simp only [Function.iterate_one, fsRotation_apply, joinPower_right_zero, Category.assoc]
    rfl
  | succ a ih =>
    let g := f ≫ (appendPower V a).inv ▷ tensorPower V (b + 1) ≫
      (α_ (tensorPower V (a + 1)) V (tensorPower V (b + 1))).hom
    have hf : f ≫ (joinPower V (a + 1) b).hom =
        (g ≫ (joinPower V a (b + 1)).hom) ≫
          eqToHom (by congr 1; omega) := by
      dsimp [g]
      simp only [Category.assoc]
      erw [← joinPower_middle]
      simp
    rw [Function.iterate_succ_apply', hf]
    erw [fsRotation_iterate_cast P V (show a + (b + 1) + 2 = a + 1 + b + 2 by omega)]
    erw [ih]
    simp only [Category.assoc, eqToHom_trans, joinPower_succ]
    dsimp only [tensorPower]
    simp only [Category.assoc, eqToHom_trans]
    simp only [← Category.assoc]
    erw [fsRotation_cast P V (show b + a + 3 = a + 1 + b + 2 by omega)]
    erw [rotation_join_step]
    simp only [← Category.assoc]
    rw [← rotation_naturality_left]
    simp [g]
    rfl

/-- The rotation returns to its starting morphism after the number of factors. -/
theorem fsRotation_iterate_self (P : Pivotal C) (V : C) (n : ℕ)
    (f : 𝟙_ C ⟶ tensorPower V n) : (fsRotation P V n)^[n] f = f := by
  rcases n with _ | _ | n
  · rfl
  · rfl
  · have hi := fsRotation_iterate_join P V n 0 (f ≫ (appendPower V n).inv)
    simp only [joinPower_right_zero, Category.assoc, Iso.inv_hom_id, Category.comp_id,
      joinPower_zero, eqToHom_trans] at hi
    dsimp only [tensorPower] at hi
    simp only [eqToHom_refl, Category.comp_id] at hi
    rw [Function.iterate_succ_apply']
    erw [hi]
    rw [fsRotation_apply]
    erw [rotation_rotation]
    simp only [Category.assoc]
    erw [Iso.inv_hom_id, Category.comp_id]

/-- Ng–Schauenburg's rotation-order theorem, for every pivotal category. -/
theorem fsRotation_pow (P : Pivotal C) (V : C) (n : ℕ) :
    (fsRotation P V n).toLinearMap ^ n = 1 := by
  ext f
  rw [Module.End.pow_apply]
  exact fsRotation_iterate_self P V n f

variable [Limits.HasKernels C] [Limits.HasFiniteBiproducts C]

/-- The cyclic-order contract is discharged. -/
theorem rotationOrder_holds (F : SphericalFusion C) : RotationOrder F := by
  intro V n _
  exact fsRotation_pow F.toPivotal V n

/-- Every ordinary positive-degree indicator is an integral cyclotomic number. -/
theorem indicator_cyclotomic (F : SphericalFusion C) (V : C) {n : ℕ} (hn : 0 < n) :
    indicator F.toPivotal V n ∈
      Algebra.adjoin ℤ ({Complex.exp (2 * Real.pi * Complex.I / n)} : Set ℂ) :=
  indicator_mem_cyclotomicIntegers F (rotationOrder_holds F) V hn

end VOA.Huang.NgSchauenburg
