import VOA.Classification.COne.OrbPos11Dictionary
import VOA.Huang.HKLLocSetup

/-! Product/iterate associativity and scalar branch change for the actual action
fields. These are analytic prerequisites, not a proof of twisted Jacobi. -/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbPos12
open VOA CategoryTheory MonoidalCategory VOA.Huang.TensorCat VOA.Huang.FusionUnit
open VOA.Huang.FusionProduct VOA.Huang.HKLRational
open VOA.Huang.TensorCat.BraidRibbon VOA.Huang.TensorCat.HexagonClose
open OrbPos9 OrbPos10 OrbPos11

variable (G : Subgroup (Aut (V2m 1 le_rfl)))
  (hSR : StronglyRational (orbifoldVOA G)) (X : Ordinary (orbifoldVOA G))
  (a : tensorObj (fusionChoice_pbw hSR) (ambient G) X ⟶ X)

/-- The product of the given action fields, represented on a fusion product. -/
def actionProduct : ProductSpace (fusionChoice_pbw hSR) (ambient G) (ambient G) X X :=
  postcompose ((fusionChoice_pbw hSR) (ambient G)
    (tensorObj (fusionChoice_pbw hSR) (ambient G) X)).intertwiner X.isMod
    (tensorHom (fusionChoice_pbw hSR) (𝟙 (ambient G)) a ≫ a)

/-- The iterate uses the pinned ambient VOA multiplication. -/
def actionIterate : IterateSpace (fusionChoice_pbw hSR) (ambient G) (ambient G) X X :=
  postcompose ((fusionChoice_pbw hSR)
    (tensorObj (fusionChoice_pbw hSR) (ambient G) (ambient G)) X).intertwiner X.isMod
    (tensorHom (fusionChoice_pbw hSR) (ambientMultiplication G (fusionChoice_pbw hSR))
      (𝟙 X) ≫ a)

theorem actionProduct_val (n : ℂ) (v : (ambient G).carrier)
    (z : (tensorObj (fusionChoice_pbw hSR) (ambient G) X).carrier) :
    (actionProduct G hSR X a).val n v z =
      (actionIntertwiner G hSR X a).val n v (a.val z) := by
  change (tensorHom (fusionChoice_pbw hSR) (𝟙 (ambient G)) a ≫ a).val
    (((fusionChoice_pbw hSR) (ambient G) _).intertwiner.val n v z) = _
  rw [Ordinary.comp_apply, tensorHom_intertwiner, Ordinary.id_apply]
  rfl

/-- Action associativity gives equality of the convergent product and iterate
evaluations on the real four-point segment, with no Jacobi assumption. -/
theorem action_iterate_eq_product (E : CanonicalExtensionAlgebra G hSR)
    (ha : ActionLaws G hSR E X a) :
    iterateEvaluation (fusionChoice_pbw hSR) (actionIterate G hSR X a) =
      productEvaluation (fusionChoice_pbw hSR) (actionProduct G hSR X a) := by
  letI := monoidalCategoryOfStronglyRational_pbw (fusionChoice_pbw hSR) hSR
  letI := E.monoid
  change IsLeftAct a at ha
  have hassoc : tensorHom (fusionChoice_pbw hSR)
      (ambientMultiplication G (fusionChoice_pbw hSR)) (𝟙 X) ≫ a =
      (evalAssoc (fusionChoice_pbw hSR) (ordinaryFourPointInput_pbw _ hSR)
        (ambient G) (ambient G) X).hom ≫
        tensorHom (fusionChoice_pbw hSR) (𝟙 (ambient G)) a ≫ a := by
    simpa only [E.mul_eq] using ha.mul_act
  rw [actionIterate, hassoc]
  exact evalAssoc_fourPoint (fusionChoice_pbw hSR) (ordinaryFourPointInput_pbw _ hSR)
    (ambient G) (ambient G) X X _

/-- Both open half-plane continuations exist for these actual action products. -/
theorem actionProduct_halfPlane (d : FourPointTest (ambient G) (ambient G) X X)
    (s : ℝ) (hs : s = 1 ∨ s = -1) :
    ∃ Φ : ℂ → ℂ, AnalyticOnNhd ℂ Φ {ζ | 0 < s * ζ.im} ∧
      ∀ ζ : ℂ, 0 < s * ζ.im → 1 < ‖ζ‖ →
        Φ ζ = prodL (fusionChoice_pbw hSR) (actionProduct G hSR X a) d (Complex.log ζ) :=
  productHalfPlaneContinuation_pbw (fusionChoice_pbw hSR) hSR _ _ _ _
    (actionProduct G hSR X a) d s hs

/-- The nonzero product coefficients have exactly the scalar monodromy
prescribed by the eigenvalue of the outer insertion. -/
theorem actionProduct_coefficient_phase (g : G)
    (hm : ActionMonodromyThrough G hSR X a g)
    (d : FourPointTest (ambient G) (ambient G) X X) (c : ℂ)
    (hx : g.1 d.x = c • d.x) (w : ℂ)
    (hw : prodCoef (fusionChoice_pbw hSR) (actionProduct G hSR X a) d w ≠ 0) :
    Complex.exp ((d.δ - d.α - w) * (2 * Real.pi * Complex.I)) * c = 1 := by
  have hn : (actionIntertwiner G hSR X a).val (d.α + w - d.δ - 1) d.x
      (a.val (((fusionChoice_pbw hSR) (ambient G) X).intertwiner.val
        (d.β + d.γ - w - 1) d.y d.z)) ≠ 0 := by
    intro h
    apply hw
    rw [prodCoef, actionProduct_val, h, map_zero]
  have hp := action_coefficient_phase G hSR X a g hm _ c d.x hx _ hn
  rw [monodromy_phase] at hp
  convert hp using 2
  congr 1
  ring

/-- A complete positive circuit of the outer coordinate multiplies the action
product by the inverse eigenvalue. This is a statement on the actual `prodL`. -/
theorem actionProduct_log_monodromy (g : G)
    (hm : ActionMonodromyThrough G hSR X a g)
    (d : FourPointTest (ambient G) (ambient G) X X) (c : ℂ) (hc : c ≠ 0)
    (hx : g.1 d.x = c • d.x) (L : ℂ) :
    prodL (fusionChoice_pbw hSR) (actionProduct G hSR X a) d
        (L + 2 * Real.pi * Complex.I) =
      c⁻¹ * prodL (fusionChoice_pbw hSR) (actionProduct G hSR X a) d L := by
  unfold prodL
  rw [← tsum_mul_left]
  apply tsum_congr
  intro w
  by_cases hw : prodCoef (fusionChoice_pbw hSR) (actionProduct G hSR X a) d w = 0
  · simp only [hw, zero_mul, mul_zero]
  · have he := actionProduct_coefficient_phase G hSR X a g hm d c hx w hw
    have he' : Complex.exp ((d.δ - d.α - w) * (2 * Real.pi * Complex.I)) = c⁻¹ :=
      (mul_right_cancel₀ hc) (he.trans (inv_mul_cancel₀ hc).symm)
    rw [mul_add, Complex.exp_add, he']
    ring

end VOA.Classification.COne.OrbPos12
