import VOA.Huang.PentagonCloseMain
import VOA.Huang.BraidRibbonTwist

/-! # The hexagons, reduced to an associator-free four-point statement

For a strongly rational `W` the monoidal category `monoidalCategoryOfStronglyRational_pbw F hV`
is proved (`PentagonCloseMain`).  Its associator is characterized by the four-point identity
`evalAssoc_fourPoint`, and iterate evaluations are faithful (`ordinaryFourPointInput_pbw`).  The
braiding `braidingP p F` is purely algebraic (`BraidRibbonBraiding`).

**What remains for the hexagons** is the following associator-free statement about real
four-point matrix coefficients (`AnalyticHexagon F p`): for every `K ∈ I((Y⊠Z) X; T)`,
`M ∈ I((Y⊠X) Z; T)`, `G ∈ I(Y (Z⊠X); T)` with
`It(K) = Pr(G)` and `It(M) = Pr(G ∘ (1 × c_{X,Z}))`,

`Pr(Ω_p K) = It(M ∘ (c_{X,Y} × 1))`

on all real four-point tests.  It is the analytic content of Huang's hexagon theorem (the
four-point function continued along the two homotopic paths that move `x` past the pair `(y, z)`
at once or one point at a time; Huang–Lepowsky's tensor product theory, and Huang–Lepowsky–Zhang,
*Logarithmic tensor category theory* VIII, arXiv:1110.1931 — theorem numbers were not
re-checked here).

Proved here:
* `hexagonForward_of_analytic`: `AnalyticHexagon F p → ` the forward hexagon for `braidingP p`;
* `analytic_of_hexagonForward`: the converse, so `AnalyticHexagon F p` is **exactly** as strong
  as the forward hexagon for `braidingP p` (`analyticHexagon_iff`) — it is true iff Huang's
  hexagon holds for that phase, and is not vacuous;
* `hexagonReverse_of_forward_inv`: the reverse hexagon for phase `p` is the forward hexagon for
  `p⁻¹` (inverted, `braidingP_inv`), so only the forward statement is needed, for the two phases
  `Phase.upper` (`e^{-πi(n+1)}`, FHL `Ω₀`) and `Phase.upper.inv` (`e^{πi(n+1)}`, FHL `Ω₋₁`);
* `braidedCategoryOfStronglyRational_pbw (F) (hV) (h : HexagonInput F) :
  BraidedCategory (Ordinary W)` on top of `monoidalCategoryOfStronglyRational_pbw F hV`, with the
  braiding `braiding F` (naturality proved; hexagons from `h`).

`AnalyticHexagon F p` must NOT be stated for an arbitrary admissible phase: a phase `k · Ω₀` with
constant `k ≠ 1` is admissible and gives a natural isomorphism, but the hexagon fails for it (one
braiding on the left, two on the right).
-/

noncomputable section
namespace VOA.Huang.TensorCat
open VOA VOA.Huang.FusionUnit VOA.Huang.FusionProduct CategoryTheory MonoidalCategory
open VOA.Huang.MatrixCoeff
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}

namespace BraidRibbon

variable (F : FusionChoice W)

/-! ## Universal coefficients of composites -/

theorem postcompose_tensorHom_comp {X X' Y Y' T : Ordinary W} (f : X ⟶ X') (g : Y ⟶ Y')
    (m : tensorObj F X' Y' ⟶ T) :
    postcompose (F X Y).intertwiner T.isMod (tensorHom F f g ≫ m) =
      restrictInputs f g (postcompose (F X' Y').intertwiner T.isMod m) := by
  apply Subtype.ext
  funext n
  ext x y
  change m.val ((tensorHom F f g).val ((F X Y).intertwiner.val n x y)) = _
  rw [tensorHom_intertwiner]
  rfl

/-! ## The associator-free hexagon statement -/

/-- **The analytic hexagon** for phase `p` (associator-free).  See the module docstring. TRUE for
`p = Phase.upper` and `p = Phase.upper.inv` when `W` is strongly rational (Huang's hexagon
theorem); equivalent to the forward hexagon for `braidingP p` (`analyticHexagon_iff`). -/
def AnalyticHexagon (p : Phase) : Prop :=
  ∀ (X Y Z T : Ordinary W) (K : IterateSpace F Y Z X T) (M : IterateSpace F Y X Z T)
    (G : ProductSpace F Y Z X T),
    iterateEvaluation F K = productEvaluation F G →
    iterateEvaluation F M =
      productEvaluation F (restrictInputs (𝟙 Y) (braidingP p F X Z).hom G) →
    productEvaluation F (skewP p (tensorObj F Y Z) X T K) =
      iterateEvaluation F (restrictInputs (braidingP p F X Y).hom (𝟙 Z) M)

variable (H : OrdinaryFourPointInput F)

/-- The forward hexagon for `braidingP p` and the evaluation associator, stated with the
library's own tensor morphisms. -/
def HexagonForward (p : Phase) : Prop :=
  ∀ X Y Z : Ordinary W,
    (evalAssoc F H X Y Z).hom ≫ (braidingP p F X (tensorObj F Y Z)).hom ≫
        (evalAssoc F H Y Z X).hom =
      tensorHom F (braidingP p F X Y).hom (𝟙 Z) ≫ (evalAssoc F H Y X Z).hom ≫
        tensorHom F (𝟙 Y) (braidingP p F X Z).hom

/-- The reverse hexagon for `braidingP p` and the evaluation associator. -/
def HexagonReverse (p : Phase) : Prop :=
  ∀ X Y Z : Ordinary W,
    (evalAssoc F H X Y Z).inv ≫ (braidingP p F (tensorObj F X Y) Z).hom ≫
        (evalAssoc F H Z X Y).inv =
      tensorHom F (𝟙 X) (braidingP p F Y Z).hom ≫ (evalAssoc F H X Z Y).inv ≫
        tensorHom F (braidingP p F X Z).hom (𝟙 Y)

include H in
/-- Morphisms out of `(X ⊠ Y) ⊠ Z` are determined by their iterate evaluations. -/
theorem eq_of_iterateEvaluation {X Y Z U : Ordinary W}
    (φ ψ : tensorObj F (tensorObj F X Y) Z ⟶ U)
    (h : iterateEvaluation F (postcompose (F (tensorObj F X Y) Z).intertwiner U.isMod φ) =
      iterateEvaluation F (postcompose (F (tensorObj F X Y) Z).intertwiner U.isMod ψ)) :
    φ = ψ :=
  ((F (tensorObj F X Y) Z).universal U.carrier U.isMod).1 ((H.faithfulness X Y Z U).1 h)

/-- **The analytic hexagon gives the forward hexagon.** -/
theorem hexagonForward_of_analytic (p : Phase) (hA : AnalyticHexagon F p) :
    HexagonForward F H p := by
  intro X Y Z
  set U := tensorObj F Y (tensorObj F Z X)
  set K : IterateSpace F Y Z X U :=
    postcompose (F (tensorObj F Y Z) X).intertwiner U.isMod (evalAssoc F H Y Z X).hom
  set G : ProductSpace F Y Z X U := postcompose (F Y (tensorObj F Z X)).intertwiner U.isMod (𝟙 U)
  set M : IterateSpace F Y X Z U :=
    postcompose (F (tensorObj F Y X) Z).intertwiner U.isMod
      ((evalAssoc F H Y X Z).hom ≫ tensorHom F (𝟙 Y) (braidingP p F X Z).hom)
  have hK : iterateEvaluation F K = productEvaluation F G := by
    have := evalAssoc_fourPoint F H Y Z X U (𝟙 U)
    rwa [Category.comp_id] at this
  have hM : iterateEvaluation F M =
      productEvaluation F (restrictInputs (𝟙 Y) (braidingP p F X Z).hom G) := by
    have := evalAssoc_fourPoint F H Y X Z U (tensorHom F (𝟙 Y) (braidingP p F X Z).hom)
    rw [this]
    congr 1
    have h2 := postcompose_tensorHom_comp F (𝟙 Y) (braidingP p F X Z).hom (𝟙 U)
    rwa [Category.comp_id] at h2
  have key := hA X Y Z U K M G hK hM
  apply eq_of_iterateEvaluation F H
  rw [evalAssoc_fourPoint, postcompose_braidingP_comp, postcompose_tensorHom_comp]
  exact key

/-- **Converse**: the forward hexagon gives the analytic hexagon, so the two are equivalent
(given the proved four-point input). -/
theorem analytic_of_hexagonForward (p : Phase) (hF : HexagonForward F H p) :
    AnalyticHexagon F p := by
  intro X Y Z T K M G hK hM
  set g : tensorObj F Y (tensorObj F Z X) ⟶ T := (F Y (tensorObj F Z X)).lift T.isMod G
  have hG : postcompose (F Y (tensorObj F Z X)).intertwiner T.isMod g = G :=
    (F Y (tensorObj F Z X)).lift_spec T.isMod G
  -- identify `K`
  have hK' : K = postcompose (F (tensorObj F Y Z) X).intertwiner T.isMod
      ((evalAssoc F H Y Z X).hom ≫ g) := by
    apply (H.faithfulness Y Z X T).1
    rw [hK, evalAssoc_fourPoint, hG]
  -- identify `M`
  have hM' : M = postcompose (F (tensorObj F Y X) Z).intertwiner T.isMod
      ((evalAssoc F H Y X Z).hom ≫ tensorHom F (𝟙 Y) (braidingP p F X Z).hom ≫ g) := by
    apply (H.faithfulness Y X Z T).1
    rw [hM, evalAssoc_fourPoint, postcompose_tensorHom_comp, hG]
  have hx := congrArg (fun φ => iterateEvaluation F
    (postcompose (F (tensorObj F X Y) Z).intertwiner T.isMod (φ ≫ g))) (hF X Y Z)
  simp only [Category.assoc] at hx
  rw [evalAssoc_fourPoint, postcompose_braidingP_comp, postcompose_tensorHom_comp] at hx
  rw [hK', hM']
  exact hx

theorem analyticHexagon_iff (p : Phase) : AnalyticHexagon F p ↔ HexagonForward F H p :=
  ⟨hexagonForward_of_analytic F H p, analytic_of_hexagonForward F H p⟩

/-- The reverse hexagon for `p` is the inverted forward hexagon for `p⁻¹`. -/
theorem hexagonReverse_of_forward_inv (p : Phase) (hF : HexagonForward F H p.inv) :
    HexagonReverse F H p := by
  intro X Y Z
  have hinv : ∀ A B : Ordinary W, (braidingP p.inv F A B).inv = (braidingP p F B A).hom := by
    intro A B
    have := braidingP_inv p.inv F A B
    rw [Phase.inv_inv] at this
    exact this.symm
  have hiso : (evalAssoc F H Z X Y ≪≫ braidingP p.inv F Z (tensorObj F X Y) ≪≫
      evalAssoc F H X Y Z) =
      (tensorIso F (braidingP p.inv F Z X) (Iso.refl Y) ≪≫ evalAssoc F H X Z Y ≪≫
        tensorIso F (Iso.refl X) (braidingP p.inv F Z Y)) :=
    Iso.ext (hF Z X Y)
  have h := congrArg Iso.inv hiso
  have ti : ∀ {A A' B B' : Ordinary W} (e : A ≅ A') (d : B ≅ B'),
      (tensorIso F e d).inv = tensorHom F e.inv d.inv := fun _ _ => rfl
  simp only [Iso.trans_inv, Category.assoc, ti, Iso.refl_inv, hinv] at h
  exact h

/-- **The hexagon input**: the analytic hexagon for FHL's two phases `Ω₀` and `Ω₋₁`. -/
def HexagonInput : Prop :=
  AnalyticHexagon F Phase.upper ∧ AnalyticHexagon F Phase.upper.inv

variable (hV : StronglyRational W)

/-- **The braided monoidal category of ordinary modules** of a strongly rational VOA, on top
of `monoidalCategoryOfStronglyRational_pbw F hV`, with braiding `braiding F` (FHL's `Ω₀`),
conditional on the analytic hexagon `HexagonInput F`. -/
abbrev braidedCategoryOfStronglyRational_pbw (hH : HexagonInput F) :
    @BraidedCategory (Ordinary W) _ (monoidalCategoryOfStronglyRational_pbw F hV) :=
  letI := monoidalCategoryOfStronglyRational_pbw F hV
  { braiding := braiding F
    braiding_naturality_right := fun X _ _ f => braidingP_naturality Phase.upper F (𝟙 X) f
    braiding_naturality_left := fun f Z => braidingP_naturality Phase.upper F f (𝟙 Z)
    hexagon_forward := hexagonForward_of_analytic F (ordinaryFourPointInput_pbw F hV)
      Phase.upper hH.1
    hexagon_reverse := hexagonReverse_of_forward_inv F (ordinaryFourPointInput_pbw F hV)
      Phase.upper (hexagonForward_of_analytic F (ordinaryFourPointInput_pbw F hV)
        Phase.upper.inv hH.2) }

theorem braidedCategoryOfStronglyRational_pbw_braiding (hH : HexagonInput F) (X Y : Ordinary W) :
    @BraidedCategory.braiding (Ordinary W) _ (monoidalCategoryOfStronglyRational_pbw F hV)
      (braidedCategoryOfStronglyRational_pbw F hV hH) X Y = braiding F X Y := rfl

end BraidRibbon
end VOA.Huang.TensorCat
