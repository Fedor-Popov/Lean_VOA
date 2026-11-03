import VOA.Classification.COne.OrbPos9Induction
import VOA.Huang.TensorCatVacuum

/-! # The canonical multiplication morphism of an orbifold extension

The ambient vertex operator restricts to an intertwining operator, and hence
to an actual fusion-product morphism. Both unit laws are proved here. This
file does not assert the categorical associativity or commutativity laws.
-/
noncomputable section
namespace VOA.Classification.COne.OrbPos9
open VOA VOA.Huang.FusionUnit VOA.Huang.TensorCat VOA.Huang.FusionProduct CategoryTheory
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}

/-- The ambient vertex operator is an intertwiner over the fixed-point algebra. -/
def ambientIntertwiner (G : Subgroup (Aut W)) :
    IntertwiningOperator (ambient G).isMod (ambient G).isMod (ambient G).isMod :=
  ⟨moduleModes (adjointModule W), by
    have h := isIntertwiningOperator_moduleModes (adjointModule W)
    exact ⟨h.truncation, h.L_neg_one, fun u a x ℓ k n => h.jacobi u.1 a x ℓ k n⟩⟩

/-- The canonical multiplication; no arbitrary algebra structure is substituted. -/
def ambientMultiplication (G : Subgroup (Aut W)) (F : FusionChoice (orbifoldVOA G)) :
    tensorObj F (ambient G) (ambient G) ⟶ ambient G :=
  (F (ambient G) (ambient G)).lift (ambient G).isMod (ambientIntertwiner G)

@[simp] theorem ambientMultiplication_intertwiner (G : Subgroup (Aut W))
    (F : FusionChoice (orbifoldVOA G)) (n : ℂ) (a b : V) :
    (ambientMultiplication G F).val ((F (ambient G) (ambient G)).intertwiner.val n a b) =
      moduleModes (adjointModule W) n a b :=
  congrArg (fun I : IntertwiningOperator (ambient G).isMod (ambient G).isMod
    (ambient G).isMod => I.val n a b) ((F (ambient G) (ambient G)).lift_spec _ _)

/-- The categorical left unit is exactly the sub-VOA inclusion. -/
theorem ambientMultiplication_left_unit (G : Subgroup (Aut W))
    (F : FusionChoice (orbifoldVOA G)) :
    tensorHom F (unitInclusion G) (𝟙 (ambient G)) ≫ ambientMultiplication G F =
      (leftUnitor F (ambient G)).hom := by
  apply tensor_hom_ext F
  intro n v x
  rw [Ordinary.comp_apply, tensorHom_intertwiner, Ordinary.id_apply,
    ambientMultiplication_intertwiner, leftUnitor_intertwiner]
  change moduleModes (adjointModule W) n v.1 x = moduleModes (ambient G).isMod n v x
  unfold moduleModes
  split_ifs <;> rfl

/-- The right unit law follows from the actual VOA creation axiom. -/
theorem ambientMultiplication_right_unit (G : Subgroup (Aut W))
    (F : FusionChoice (orbifoldVOA G)) :
    tensorHom F (𝟙 (ambient G)) (unitInclusion G) ≫ ambientMultiplication G F =
      (rightUnitor F (ambient G)).hom := by
  apply Ordinary.hom_ext
  intro y
  obtain ⟨x, rfl⟩ := right_vacuum_coefficient_surjective F (ambient G) y
  rw [Ordinary.comp_apply, tensorHom_intertwiner, Ordinary.id_apply,
    ambientMultiplication_intertwiner, rightUnitor_intertwiner,
    skew_moduleIntertwiner_vacuum_neg_one]
  change moduleModes (adjointModule W) (-1) x W.vacuum = x
  rw [show (-1 : ℂ) = ((-1 : ℤ) : ℂ) by simp, moduleModes_apply_intCast]
  exact (W.creation x).1

end VOA.Classification.COne.OrbPos9
