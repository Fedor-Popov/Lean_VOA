import VOA.Huang.NgSchauenburgCentralRotation

/-! # A full central rotation and its twist scalar -/
noncomputable section
set_option linter.unusedSectionVars false
universe v u
namespace VOA.Huang.NgSchauenburg
open CategoryTheory MonoidalCategory Limits
attribute [-instance] hasRightDualUnit hasRightDualLeftDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]

/-- Iteration commutes with transport of the positive degree. -/
theorem generalizedRotation_iterate_cast (P : Pivotal C) (A : Center C) (V : C)
    {n m : ℕ} (h : n = m) (k : ℕ) (f : A.1 ⟶ tensorPower V (n + 1)) :
    (generalizedRotation P A V m)^[k]
        (f ≫ eqToHom (by subst m; rfl)) =
      (generalizedRotation P A V n)^[k] f ≫ eqToHom (by subst m; rfl) := by
  subst m
  simp

/-- A single rotation commutes with transport of the positive degree. -/
theorem generalizedRotation_cast (P : Pivotal C) (A : Center C) (V : C)
    {n m : ℕ} (h : n = m) (f : A.1 ⟶ tensorPower V (n + 1)) :
    generalizedRotation P A V m (f ≫ eqToHom (by subst m; rfl)) =
      generalizedRotation P A V n f ≫ eqToHom (by subst m; rfl) := by
  subst m
  simp

/-- The explicit action in degree at least two. -/
theorem generalizedRotation_apply (P : Pivotal C) (A : Center C) (V : C) (n : ℕ)
    (f : A.1 ⟶ tensorPower V (n + 2)) :
    generalizedRotation P A V (n + 1) f =
      centerRotation P A V (tensorPower V (n + 1)) f ≫ (appendPower V n).hom := by
  change (𝟙 _ ≫ centerRotation P A V (tensorPower V (n + 1)) f ≫ _) = _
  simp

/-- A single central rotation enlarges the moved block by one factor. -/
theorem centerRotation_join_step (P : Pivotal C) (A : Center C) (V : C) (a b : ℕ)
    (f : A.1 ⟶ tensorPower V (a + 1) ⊗ (V ⊗ tensorPower V (b + 1))) :
    generalizedRotation P A V (b + a + 2)
      ((centerRotation P A (tensorPower V (a + 1)) (V ⊗ tensorPower V (b + 1)) f ≫
          (α_ V (tensorPower V (b + 1)) (tensorPower V (a + 1))).hom) ≫
        V ◁ (joinPower V b a).hom) =
      centerRotation P A (tensorPower V (a + 1) ⊗ V) (tensorPower V (b + 1))
        (f ≫ (α_ (tensorPower V (a + 1)) V (tensorPower V (b + 1))).inv) ≫
      tensorPower V (b + 1) ◁ (appendPower V a).hom ≫ (joinPower V b (a + 1)).hom := by
  rw [generalizedRotation_apply]
  erw [centerRotation_naturality_right]
  simp only [Category.assoc]
  rw [joinPower_append, ← Category.assoc, ← Category.assoc]
  rw [centerRotation_tensor]
  simp

/-- Iterated single central rotations equal the tensor-block rotation. -/
theorem generalizedRotation_iterate_join (P : Pivotal C) (A : Center C) (V : C) (a b : ℕ)
    (f : A.1 ⟶ tensorPower V (a + 1) ⊗ tensorPower V (b + 1)) :
    (generalizedRotation P A V (a + b + 1))^[a + 1] (f ≫ (joinPower V a b).hom) =
      centerRotation P A (tensorPower V (a + 1)) (tensorPower V (b + 1)) f ≫
        (joinPower V b a).hom ≫ eqToHom (by congr 1; omega) := by
  induction a generalizing b with
  | zero =>
    rw [joinPower_zero]
    erw [generalizedRotation_iterate_cast P A V (show b + 1 = 0 + b + 1 by omega) 1 f]
    simp only [Function.iterate_one, generalizedRotation_apply,
      joinPower_right_zero, Category.assoc]
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
    erw [generalizedRotation_iterate_cast P A V
      (show a + (b + 1) + 1 = a + 1 + b + 1 by omega)]
    erw [ih]
    simp only [Category.assoc, eqToHom_trans, joinPower_succ]
    dsimp only [tensorPower]
    simp only [Category.assoc, eqToHom_trans]
    simp only [← Category.assoc]
    erw [generalizedRotation_cast P A V (show b + a + 2 = a + 1 + b + 1 by omega)]
    erw [centerRotation_join_step]
    simp only [← Category.assoc]
    rw [← centerRotation_naturality_left]
    simp [g]
    rfl

/-- One full turn acts by the central Drinfeld morphism followed by the pivotal inverse. -/
theorem generalizedRotation_iterate_full (P : Pivotal C) (A : Center C) (V : C) (n : ℕ)
    (f : A.1 ⟶ tensorPower V (n + 1)) :
    (generalizedRotation P A V n)^[n + 1] f =
      centralDrinfeldMorphism A ≫ (P.j A.1).inv ≫ f := by
  cases n with
  | zero => exact generalizedRotation_one_centralDrinfeld P A V f
  | succ n =>
    have hi := generalizedRotation_iterate_join P A V n 0 (f ≫ (appendPower V n).inv)
    simp only [joinPower_right_zero, Category.assoc, Iso.inv_hom_id, Category.comp_id,
      joinPower_zero, eqToHom_trans] at hi
    dsimp only [tensorPower] at hi
    simp only [eqToHom_refl, Category.comp_id] at hi
    rw [Function.iterate_succ_apply']
    erw [hi]
    rw [generalizedRotation_apply]
    erw [centerRotation_rotation, generalizedRotation_one_centralDrinfeld]
    simp only [Category.assoc]
    erw [Iso.inv_hom_id, Category.comp_id]

/-- The power identity for a central source with a specified twist eigenvalue. -/
theorem generalizedRotation_pow_scalar (P : Pivotal C) (A : Center C) (V : C) (n : ℕ)
    {t : ℂ} (ht : t ≠ 0)
    (hj : (P.j A.1).hom = t • centralDrinfeldMorphism A) :
    (generalizedRotation P A V n).toLinearMap ^ (n + 1) =
      t⁻¹ • (1 : Module.End ℂ (A.1 ⟶ tensorPower V (n + 1))) := by
  ext f
  rw [Module.End.pow_apply]
  change (generalizedRotation P A V n)^[n + 1] f = t⁻¹ • f
  rw [generalizedRotation_iterate_full]
  rw [← generalizedRotation_one_centralDrinfeld P A (tensorPower V (n + 1)),
    generalizedRotation_one_scalar P A _ ht hj]

/-- A twist period gives a finite order for the actual central rotation. -/
theorem generalizedRotation_pow_mul_eq_one (P : Pivotal C) (A : Center C) (V : C)
    (n N : ℕ) {t : ℂ} (ht : t ≠ 0)
    (hj : (P.j A.1).hom = t • centralDrinfeldMorphism A) (hN : t ^ N = 1) :
    (generalizedRotation P A V n).toLinearMap ^ ((n + 1) * N) = 1 := by
  rw [pow_mul, generalizedRotation_pow_scalar P A V n ht hj, smul_pow,
    inv_pow, hN, inv_one, one_pow, one_smul]

/-- Shifting the second index by the positive degree multiplies the indicator
by the inverse twist. The second index can be any integer. -/
theorem generalizedIndicatorInt_add_degree (F : SphericalFusion C) (A : Center C)
    (V : C) (n : ℕ) {t : ℂ} (ht : t ≠ 0)
    (hj : (F.j A.1).hom = t • centralDrinfeldMorphism A) (l : ℤ) :
    generalizedIndicatorInt F.toPivotal A V n (l + (n + 1 : ℕ)) =
      t⁻¹ * generalizedIndicatorInt F.toPivotal A V n l := by
  have hp : ((generalizedRotation F.toPivotal A V n) ^ (l + (n + 1 : ℕ))).toLinearMap =
      t⁻¹ • ((generalizedRotation F.toPivotal A V n) ^ l).toLinearMap := by
    ext f
    rw [LinearEquiv.coe_coe, zpow_add, zpow_natCast, LinearEquiv.mul_apply,
      LinearEquiv.pow_apply, generalizedRotation_iterate_full,
      ← generalizedRotation_one_centralDrinfeld F.toPivotal A (tensorPower V (n + 1)),
      generalizedRotation_one_scalar F.toPivotal A _ ht hj]
    simp
  unfold generalizedIndicatorInt
  rw [hp, map_smul]
  rfl

end VOA.Huang.NgSchauenburg
