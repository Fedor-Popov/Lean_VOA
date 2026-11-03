import VOA.Classification.COne.OrbPos9Reduction

/-! # Quotients of algebra actions in a split abelian category

No separability or rigidity is assumed. Splittings belong to the underlying
category; the quotient action, rather than the splitting, is algebra-linear.
-/
noncomputable section
namespace VOA.Classification.COne.OrbPos10
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open VOA.Huang.HKLRational OrbPos9
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [Abelian C] [MonoidalPreadditive C]
  {A : C} [MonObj A]

omit [Abelian C] [MonoidalPreadditive C] in
/-- A split underlying quotient inherits an action whenever the projection
intertwines it. The action laws can be checked after the split epimorphism. -/
theorem quotient_action_laws {X Z : C} (aX : A ⊗ X ⟶ X) (hX : IsLeftAct aX)
    (p : X ⟶ Z) (s : Z ⟶ X) (hs : s ≫ p = 𝟙 Z)
    (aZ : A ⊗ Z ⟶ Z) (hp : IsLinear aX aZ p) : IsLeftAct aZ := by
  have ep : Epi p := ⟨fun g h he => by
    have := congrArg (fun k => s ≫ k) he
    simpa only [← Category.assoc, hs, Category.id_comp] using this⟩
  have epA : Epi (A ◁ p) := ⟨fun g h he => by
    have := congrArg (fun k => (A ◁ s) ≫ k) he
    simpa only [← Category.assoc, ← whiskerLeft_comp, hs, whiskerLeft_id,
      Category.id_comp] using this⟩
  have epAA : Epi ((A ⊗ A) ◁ p) := ⟨fun g h he => by
    have := congrArg (fun k => ((A ⊗ A) ◁ s) ≫ k) he
    simpa only [← Category.assoc, ← whiskerLeft_comp, hs, whiskerLeft_id,
      Category.id_comp] using this⟩
  have epI : Epi ((𝟙_ C) ◁ p) := ⟨fun g h he => by
    have := congrArg (fun k => ((𝟙_ C) ◁ s) ≫ k) he
    simpa only [← Category.assoc, ← whiskerLeft_comp, hs, whiskerLeft_id,
      Category.id_comp] using this⟩
  constructor
  · apply (cancel_epi ((𝟙_ C) ◁ p)).mp
    rw [leftUnitor_naturality, ← hX.one_act]
    dsimp [IsLinear] at hp
    rw [← Category.assoc, whisker_exchange, Category.assoc, hp]
    simp only [Category.assoc]
  · apply (cancel_epi ((A ⊗ A) ◁ p)).mp
    dsimp [IsLinear] at hp
    rw [← Category.assoc, whisker_exchange, Category.assoc, hp,
      ← Category.assoc, hX.mul_act]
    rw [associator_naturality_right_assoc, Category.assoc,
      ← whiskerLeft_comp_assoc, hp, whiskerLeft_comp]
    simp only [Category.assoc, hp]

/-- Descend an action through the cokernel of an algebra-linear split mono. -/
theorem cokernel_action {Y X : C} (aY : A ⊗ Y ⟶ Y) (aX : A ⊗ X ⟶ X)
    (hX : IsLeftAct aX) (f : Y ⟶ X) (hf : IsLinear aY aX f)
    (r : X ⟶ Y) (hr : f ≫ r = 𝟙 Y) :
    ∃ aZ : A ⊗ cokernel f ⟶ cokernel f,
      IsLeftAct aZ ∧ IsLinear aX aZ (cokernel.π f) ∧
      ∃ s : cokernel f ⟶ X, s ≫ cokernel.π f = 𝟙 _ := by
  let p := cokernel.π f
  let s : cokernel f ⟶ X := cokernel.desc f (𝟙 X - r ≫ f) (by
    simp [Preadditive.comp_sub, ← Category.assoc, hr])
  have hps : p ≫ s = 𝟙 X - r ≫ f := cokernel.π_desc _ _ _
  have hsp : s ≫ p = 𝟙 _ := by
    apply (cancel_epi p).mp
    rw [← Category.assoc, hps]
    simp [p, Preadditive.sub_comp, Category.assoc]
  let aZ : A ⊗ cokernel f ⟶ cokernel f := (A ◁ s) ≫ aX ≫ p
  have hp : IsLinear aX aZ p := by
    change (A ◁ p) ≫ (A ◁ s) ≫ aX ≫ p = aX ≫ p
    have hsub : A ◁ (𝟙 X - r ≫ f) = A ◁ 𝟙 X - A ◁ (r ≫ f) := by
      let L : (X ⟶ X) →+ (A ⊗ X ⟶ A ⊗ X) :=
        ⟨⟨fun t => A ◁ t, MonoidalPreadditive.whiskerLeft_zero⟩,
          fun t u => MonoidalPreadditive.whiskerLeft_add t u⟩
      exact L.map_sub _ _
    rw [← Category.assoc, ← whiskerLeft_comp, hps,
      hsub, whiskerLeft_id,
      Preadditive.sub_comp, Category.id_comp, whiskerLeft_comp]
    dsimp [IsLinear] at hf
    simp [Category.assoc, reassoc_of% hf, p]
  exact ⟨aZ, quotient_action_laws aX hX p s hsp aZ hp, hp, s, hsp⟩

end VOA.Classification.COne.OrbPos10
