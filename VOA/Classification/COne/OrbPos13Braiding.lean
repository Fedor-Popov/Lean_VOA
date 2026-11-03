import VOA.Classification.COne.OrbPos12Analytic
import VOA.Classification.COne.OrbPos13Descent
import VOA.Core.SkewSymmetry

/-! Braided commutativity of the actual ambient multiplication, and the
resulting symmetry of the action iterate. These do not assert twisted Jacobi. -/
noncomputable section
namespace VOA.Classification.COne.OrbPos13
open VOA CategoryTheory MonoidalCategory VOA.Huang.TensorCat VOA.Huang.FusionUnit
open VOA.Huang.FusionProduct VOA.Huang.TensorCat.BraidRibbon VOA.Huang.BraidingSkew
open OrbPos9 OrbPos10 OrbPos11 OrbPos12

universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}

/-- Applying G cannot turn a nonfixed insertion into a fixed insertion.
Consequently equivariance alone cannot reduce the missing Jacobi cases to U. -/
theorem ambientSymmetry_mem_fixed_iff (G : Subgroup (Aut W)) (g : G) (v : V) :
    g.1 v ∈ (orbifold G).carrier ↔ v ∈ (orbifold G).carrier := by
  constructor
  · intro h
    have he : g.1 v = v := g.1.toLinearEquiv.injective (h g.1 g.2)
    rwa [he] at h
  · intro h
    rwa [h g.1 g.2]

theorem omegaPhase_int_sc (k : ℤ) (j : ℕ) :
    omegaPhase (k : ℂ) * sc j = (j.factorial : ℂ)⁻¹ * sgn (-k - 1 - j) := by
  have hp := phase_int omegaPhase_succ (-1) (k + 1)
  have hn : (-1 : ℂ) + ((k + 1 : ℤ) : ℂ) = k := by push_cast; ring
  rw [hn] at hp
  have hz : omegaPhase (-1) = 1 := by simp [omegaPhase]
  rw [hz, mul_one] at hp
  change _ = _ * negOnePow (-k - 1 - j)
  rw [show -k - 1 - (j : ℤ) = -(k + 1 + j) by ring,
    VertexOperatorAlgebra.negOnePow_neg', VertexOperatorAlgebra.negOnePow_add',
    negOnePow_natCast, hp, sc]
  ring

/-- Ambient VOA skew symmetry agrees with the actual Huang braiding phase. -/
theorem ambientIntertwiner_skew (G : Subgroup (Aut W)) :
    skewP Phase.upper (ambient G) (ambient G) (ambient G) (ambientIntertwiner G) =
      ambientIntertwiner G := by
  apply Subtype.ext
  funext n
  ext a b
  change skewModes (ambient G).isMod.Lm1 omegaPhase (ambientIntertwiner G).val n a b = _
  rw [skewModes_apply (ambientIntertwiner G).property.truncation, sSum, smul_finsum]
  by_cases hn : ∃ k : ℤ, (k : ℂ) = n
  · obtain ⟨k, rfl⟩ := hn
    rw [OrbPos9.Assoc.ambientIntertwiner_int, W.skew_mode]
    apply finsum_congr
    intro j
    have hi : (k : ℂ) + j = ((k + (j : ℤ) : ℤ) : ℂ) := by push_cast; rfl
    have hL : (ambient G).isMod.Lm1 = W.toPreVertexAlgebra.T := by
      rw [W.T_eq_Lneg1]
      rfl
    simp only [sTerm, hi, OrbPos9.Assoc.ambientIntertwiner_int, hL, smul_smul,
      omegaPhase_int_sc]
    congr 2
    change (W.Y b) (-(k + (j : ℤ)) - 1) a = _
    congr 2
    ring
  · have hz : (ambientIntertwiner G).val n a b = 0 := by
      change moduleModes (adjointModule W) n a b = 0
      rw [moduleModes_of_not_int (adjointModule W) (fun k hk => hn ⟨k, hk⟩)]
      rfl
    rw [hz]
    apply finsum_eq_zero_of_forall_eq_zero
    intro j
    have hj : ∀ k : ℤ, (k : ℂ) ≠ n + j := by
      intro k hk
      apply hn
      refine ⟨k - j, ?_⟩
      push_cast
      linear_combination hk
    have hzj : (ambientIntertwiner G).val (n + j) b a = 0 := by
      change moduleModes (adjointModule W) (n + j) b a = 0
      rw [moduleModes_of_not_int (adjointModule W) hj]
      rfl
    simp only [sTerm, hzj, map_zero, smul_zero]

/-- The canonical multiplication is braided commutative for any orbifold
fusion choice. This uses the ambient VOA's skew symmetry. -/
theorem ambientMultiplication_braiding (G : Subgroup (Aut W))
    (F : FusionChoice (orbifoldVOA G)) :
    (braiding F (ambient G) (ambient G)).hom ≫ ambientMultiplication G F =
      ambientMultiplication G F := by
  have hm : postcompose (F (ambient G) (ambient G)).intertwiner
      (ambient G).isMod (ambientMultiplication G F) = ambientIntertwiner G :=
    (F (ambient G) (ambient G)).lift_spec _ _
  have he := postcompose_braidingP_comp Phase.upper F (ambientMultiplication G F)
  rw [hm, ambientIntertwiner_skew] at he
  apply tensor_hom_ext F
  intro n a b
  exact (congrArg (fun I => I.val n a b) he).trans
    (ambientMultiplication_intertwiner G F n a b).symm

/-- Exchanging the two ambient inputs of an iterate does not change its
action morphism. This is a categorical prerequisite for reversed products. -/
theorem actionIterate_braiding (G : Subgroup (Aut W))
    (F : FusionChoice (orbifoldVOA G)) (X : Ordinary (orbifoldVOA G))
    (a : tensorObj F (ambient G) X ⟶ X) :
    tensorHom F (braiding F (ambient G) (ambient G)).hom (𝟙 X) ≫
      tensorHom F (ambientMultiplication G F) (𝟙 X) ≫ a =
        tensorHom F (ambientMultiplication G F) (𝟙 X) ≫ a := by
  rw [← Category.assoc, ← tensorHom_comp, ambientMultiplication_braiding,
    Category.id_comp]

/-- Associativity transports ambient braided commutativity to the two-action
product, with the associator retained. No local-module assumption is used. -/
theorem actionProduct_braided_exchange
    (G : Subgroup (Aut (V2m 1 le_rfl))) (hSR : StronglyRational (orbifoldVOA G))
    (E : CanonicalExtensionAlgebra G hSR) (X : Ordinary (orbifoldVOA G))
    (a : tensorObj (fusionChoice_pbw hSR) (ambient G) X ⟶ X)
    (ha : ActionLaws G hSR E X a) :
    letI := monoidalCategoryOfStronglyRational_pbw (fusionChoice_pbw hSR) hSR
    letI := HexagonClose.braidedCategory_stronglyRational_pbw (fusionChoice_pbw hSR) hSR
    ((β_ (ambient G) (ambient G)).hom ▷ X) ≫
        (α_ (ambient G) (ambient G) X).hom ≫ (ambient G ◁ a) ≫ a =
      (α_ (ambient G) (ambient G) X).hom ≫ (ambient G ◁ a) ≫ a := by
  letI := monoidalCategoryOfStronglyRational_pbw (fusionChoice_pbw hSR) hSR
  letI := HexagonClose.braidedCategory_stronglyRational_pbw (fusionChoice_pbw hSR) hSR
  letI := E.monoid
  have hm := ha.mul_act
  rw [E.mul_eq] at hm
  change (ambientMultiplication G (fusionChoice_pbw hSR) ▷ X) ≫ a =
    (α_ (ambient G) (ambient G) X).hom ≫ (ambient G ◁ a) ≫ a at hm
  rw [← hm]
  exact actionIterate_braiding G (fusionChoice_pbw hSR) X a

end VOA.Classification.COne.OrbPos13
