import VOA.Huang.NSSMove8Assembly

/-! # Sliding a central coupon around the nested cup

The nested cup creates `X ⊗ Yᘁ ⊗ Y ⊗ Xᘁ`. A coupon on the right pair
`Y ⊗ Xᘁ` slides around the cup to the left pair `X ⊗ Yᘁ`, where it becomes
the transported right mate `interactionMate`. The comparison between the
nested cup and the pivotal cup of `Y ⊗ Xᘁ` involves the automorphism
`dualPivotalDefect X` of `Xᘁ`; centrality of the coupon makes it irrelevant.
-/
noncomputable section
set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
namespace VOA.Huang.NSCongruence
open CategoryTheory MonoidalCategory Limits BraidedCategory
open VOA.Huang.NgSchauenburg
universe v u
attribute [-instance] hasRightDualUnit hasRightDualLeftDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [BraidedCategory C]

/-- The comparison of the pivotal structure on `Xᘁ` with the mate of the
pivotal structure on `X`. (For a monoidal pivotal structure it is the identity,
but that is not needed here.) -/
def dualPivotalDefect (P : Pivotal C) (X : C) : Xᘁ ⟶ Xᘁ :=
  (P.j Xᘁ).hom ≫ ((P.j X).hom)ᘁ

/-- The nested cup: the cup of `Y` placed inside the coevaluation of `X`. -/
def nestedCup (P : Pivotal C) (X Y : C) : 𝟙_ C ⟶ (X ⊗ Yᘁ) ⊗ (Y ⊗ Xᘁ) :=
  η_ X Xᘁ ⊗≫ X ◁ P.cup Y ▷ Xᘁ ⊗≫ 𝟙 _

/-- The coevaluation of `X`, transported by `j`, is the pivotal cup of `Xᘁ`
corrected by `dualPivotalDefect`. -/
theorem coevaluation_j_eq_cup (P : Pivotal C) (X : C) :
    η_ X Xᘁ ≫ (P.j X).hom ▷ Xᘁ = P.cup Xᘁ ≫ (Xᘁ)ᘁ ◁ dualPivotalDefect P X := by
  rw [← coevaluation_comp_rightAdjointMate]
  simp [Pivotal.cup, dualPivotalDefect]

/-- The nested cup is the pivotal cup of `Y ⊗ Xᘁ` followed by an explicit map. -/
theorem nestedCup_eq_cup (P : Pivotal C) (X Y : C) :
    nestedCup P X Y = P.cup (Y ⊗ Xᘁ) ≫
      ((Y ◁ dualPivotalDefect P X)ᘁ ≫ (dualMonodromyPairIso P X Y).inv) ▷ (Y ⊗ Xᘁ) := by
  have hn := P.cup_naturality (Y ◁ dualPivotalDefect P X)
  have ht := P.cup_tensor Y Xᘁ
  have hc := coevaluation_j_eq_cup P X
  have hη : η_ X Xᘁ = (P.cup Xᘁ ≫ (Xᘁ)ᘁ ◁ dualPivotalDefect P X) ≫ (P.j X).inv ▷ Xᘁ := by
    rw [← hc]; simp
  dsimp only [dualMonodromyPairIso, Iso.trans_inv, whiskerRightIso_inv]
  simp only [comp_whiskerRight]
  rw [reassoc_of% hn, whisker_exchange_assoc, reassoc_of% ht]
  dsimp only [nestedCup]
  rw [hη]
  calc
    _ = P.cup Xᘁ ≫ (Xᘁ)ᘁ ◁ dualPivotalDefect P X ⊗≫
        ((P.j X).inv ▷ (𝟙_ C ⊗ Xᘁ) ≫ X ◁ (P.cup Y ▷ Xᘁ)) ⊗≫ 𝟙 _ := by monoidal
    _ = P.cup Xᘁ ⊗≫ (Xᘁ)ᘁ ◁ (𝟙_ C ◁ dualPivotalDefect P X ≫ P.cup Y ▷ Xᘁ) ⊗≫
        (P.j X).inv ▷ ((Yᘁ ⊗ Y) ⊗ Xᘁ) ⊗≫ 𝟙 _ := by
      rw [← whisker_exchange]; monoidal
    _ = _ := by
      rw [whisker_exchange]; monoidal

/-- A coupon commuting with every endomorphism of `Y ⊗ Xᘁ` slides from the
right pair of the nested cup to its transported right mate on the left pair. -/
theorem nestedCup_slide (P : Pivotal C) (X Y : C) (g : Y ⊗ Xᘁ ⟶ Y ⊗ Xᘁ)
    (hg : ∀ e : Y ⊗ Xᘁ ⟶ Y ⊗ Xᘁ, e ≫ g = g ≫ e) :
    nestedCup P X Y ≫ (X ⊗ Yᘁ) ◁ g =
      nestedCup P X Y ≫ interactionMate P X Y g ▷ (Y ⊗ Xᘁ) := by
  have hm : (Y ◁ dualPivotalDefect P X)ᘁ ≫ (dualMonodromyPairIso P X Y).inv ≫
      interactionMate P X Y g =
      gᘁ ≫ (Y ◁ dualPivotalDefect P X)ᘁ ≫ (dualMonodromyPairIso P X Y).inv := by
    change _ ≫ _ ≫ (dualMonodromyPairIso P X Y).hom ≫ gᘁ ≫ _ = _
    rw [Iso.inv_hom_id_assoc, ← comp_rightAdjointMate_assoc, ← comp_rightAdjointMate_assoc,
      hg]
  rw [nestedCup_eq_cup]
  simp only [Category.assoc]
  rw [← whisker_exchange, ← reassoc_of% (P.cup_naturality g), ← comp_whiskerRight,
    ← comp_whiskerRight, Category.assoc, hm]

end VOA.Huang.NSCongruence
