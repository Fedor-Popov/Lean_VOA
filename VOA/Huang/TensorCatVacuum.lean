import VOA.Huang.TensorCatNatural

/-! # Vacuum creation reduces the triangle to one inner mode

Both inverse unitors are exactly the universal coefficient at mode `-1`
and the vacuum vector. Consequently, the whole triangle is determined by
that single inner coefficient; general vacuum-module vectors and arbitrary
inner modes are not an obligation.
-/

noncomputable section
namespace VOA.Huang.TensorCat
open VOA VOA.Huang.FusionUnit VOA.Huang.FusionProduct CategoryTheory
open VOA.Huang.BraidingSkew
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}

theorem moduleIntertwiner_vacuum_neg_one (X : Ordinary W) (x : X.carrier) :
    (moduleIntertwiner X.isMod).val (-1) W.vacuum x = x := by
  change moduleModes X.isMod (-1) W.vacuum x = x
  rw [show (-1 : ℂ) = ((-1 : ℤ) : ℂ) by simp, moduleModes_apply_intCast]
  exact X.isMod.toWeakModule.act_vacuum (-1) x

/-- Creation for the actual upper-half-plane skew unit, with its phase retained. -/
theorem skew_moduleIntertwiner_vacuum_neg_one (X : Ordinary W) (x : X.carrier) :
    (skew vacuumObject X X (moduleIntertwiner X.isMod)).val (-1) x W.vacuum = x := by
  change skewModes X.isMod.Lm1 omegaPhase (moduleIntertwiner X.isMod).val
    (-1) x W.vacuum = x
  rw [skewModes_apply (trunc_of_isIntertwining (moduleIntertwiner X.isMod).property)]
  have ht (j : ℕ) (hj : 1 ≤ j) :
      (moduleIntertwiner X.isMod).val (-1 + j) W.vacuum x = 0 := by
    change moduleModes X.isMod (-1 + j) W.vacuum x = 0
    rw [show (-1 + (j : ℂ)) = (((j : ℤ) - 1 : ℤ) : ℂ) by push_cast; ring,
      moduleModes_apply_intCast, ← WeakModule.act_def, WeakModule.act_vacuum]
    rw [if_neg (by omega)]
  rw [sSum_eq_sum 1 ht]
  simp [sTerm, sc, omegaPhase, moduleIntertwiner_vacuum_neg_one]

variable (F : FusionChoice W)

@[simp] theorem leftUnitor_inv_apply (X : Ordinary W) (x : X.carrier) :
    (leftUnitor F X).inv.val x = (F vacuumObject X).intertwiner.val (-1) W.vacuum x := by
  have he := leftUnitor_intertwiner F X (-1) W.vacuum x
  rw [moduleIntertwiner_vacuum_neg_one] at he
  have hi := congrArg (fun f : tensorObj F vacuumObject X ⟶ tensorObj F vacuumObject X =>
    f.val ((F vacuumObject X).intertwiner.val (-1) W.vacuum x)) (leftUnitor F X).hom_inv_id
  simpa only [Ordinary.comp_apply, he, Ordinary.id_apply] using hi

@[simp] theorem rightUnitor_inv_apply (X : Ordinary W) (x : X.carrier) :
    (rightUnitor F X).inv.val x = (F X vacuumObject).intertwiner.val (-1) x W.vacuum := by
  have he := rightUnitor_intertwiner F X (-1) x W.vacuum
  rw [skew_moduleIntertwiner_vacuum_neg_one] at he
  have hi := congrArg (fun f : tensorObj F X vacuumObject ⟶ tensorObj F X vacuumObject =>
    f.val ((F X vacuumObject).intertwiner.val (-1) x W.vacuum)) (rightUnitor F X).hom_inv_id
  simpa only [Ordinary.comp_apply, he, Ordinary.id_apply] using hi

/-- The vacuum coefficient alone parametrizes the entire right-unit tensor carrier. -/
theorem right_vacuum_coefficient_surjective (X : Ordinary W) :
    Function.Surjective (fun x => (F X vacuumObject).intertwiner.val (-1) x W.vacuum) := by
  intro w
  refine ⟨(rightUnitor F X).hom.val w, ?_⟩
  change (F X vacuumObject).intertwiner.val (-1) ((rightUnitor F X).hom.val w) W.vacuum = w
  rw [← rightUnitor_inv_apply F X]
  exact congrArg (fun f : tensorObj F X vacuumObject ⟶ tensorObj F X vacuumObject => f.val w)
    (rightUnitor F X).hom_inv_id

/-- Linear maps on `(X fusion V) fusion Y` are determined by the creation slice. -/
theorem vacuum_triple_linear_ext (X Y : Ordinary W)
    {N : Type*} [AddCommGroup N] [Module ℂ N]
    (f g : (tensorObj F (tensorObj F X vacuumObject) Y).carrier →ₗ[ℂ] N)
    (heq : ∀ q x y, f (tripleMode F X vacuumObject Y (-1) q x W.vacuum y) =
      g (tripleMode F X vacuumObject Y (-1) q x W.vacuum y)) : f = g := by
  apply tensor_linear_ext (F (tensorObj F X vacuumObject) Y)
  intro q w y
  obtain ⟨x, rfl⟩ := right_vacuum_coefficient_surjective F X w
  exact heq q x y

/-- The only vacuum normalization still needed for a supplied associator.
This is a genuine restriction to the vacuum vector and inner mode `-1`. -/
def VacuumCreationCompatibility (a : AssociatorFamily F) : Prop :=
  ∀ (X Y : Ordinary W) (q : ℂ) (x : X.carrier) (y : Y.carrier),
    ((a X vacuumObject Y).hom ≫ tensorHom F (𝟙 X) (leftUnitor F Y).hom).val
      (tripleMode F X vacuumObject Y (-1) q x W.vacuum y) =
        (F X Y).intertwiner.val q x y

/-- Vacuum normalization on the creation slice implies the full triangle. -/
theorem triangleOnModes_of_vacuumCreation (a : AssociatorFamily F)
    (hv : VacuumCreationCompatibility F a) : TriangleOnModes F a := by
  have he (X Y : Ordinary W) :
      (a X vacuumObject Y).hom ≫ tensorHom F (𝟙 X) (leftUnitor F Y).hom =
        tensorHom F (rightUnitor F X).hom (𝟙 Y) := by
    apply Subtype.ext
    apply vacuum_triple_linear_ext F X Y
    intro q x y
    rw [hv]
    simp only [tripleMode, tensorHom_intertwiner, Ordinary.id_apply,
      rightUnitor_intertwiner, skew_moduleIntertwiner_vacuum_neg_one]
  intro X Y p q x v y
  rw [he]

/-- The reduced vacuum condition loses no information. -/
theorem triangleOnModes_iff_vacuumCreation (a : AssociatorFamily F) :
    TriangleOnModes F a ↔ VacuumCreationCompatibility F a := by
  refine ⟨?_, triangleOnModes_of_vacuumCreation F a⟩
  intro ht X Y q x y
  have hh := ht X Y (-1) q x W.vacuum y
  simpa only [tripleMode, tensorHom_intertwiner, Ordinary.id_apply,
    rightUnitor_intertwiner, skew_moduleIntertwiner_vacuum_neg_one] using hh

/-- The canonical comparison in a vacuum middle slot, built only from the
proved unitors. Equality with a global analytic associator remains to be shown. -/
def vacuumAssociator (X Y : Ordinary W) :
    tensorObj F (tensorObj F X vacuumObject) Y ≅
      tensorObj F X (tensorObj F vacuumObject Y) :=
  (tensorIso F (rightUnitor F X) (Iso.refl Y)).trans
    (tensorIso F (Iso.refl X) (leftUnitor F Y).symm)

theorem vacuumAssociator_triangle (X Y : Ordinary W) :
    (vacuumAssociator F X Y).hom ≫ tensorHom F (𝟙 X) (leftUnitor F Y).hom =
      tensorHom F (rightUnitor F X).hom (𝟙 Y) := by
  change (tensorHom F (rightUnitor F X).hom (𝟙 Y) ≫
    tensorHom F (𝟙 X) (leftUnitor F Y).inv) ≫ _ = _
  rw [Category.assoc, ← tensorHom_comp]
  simp

end VOA.Huang.TensorCat
