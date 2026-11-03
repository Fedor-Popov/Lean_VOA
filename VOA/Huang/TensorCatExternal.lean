import VOA.Huang.TensorCatIrreducible

/-! # Finite decomposition in all four external variables

The presentation needs only a finite sum of inclusion/projection composites
which is the identity. Orthogonality of distinct summands is unnecessary.
All test transports preserve the supported weight and the real coordinate.
-/

noncomputable section
namespace VOA.Huang.TensorCat
open VOA VOA.Huang.FusionUnit VOA.Huang.FusionProduct CategoryTheory
open VOA.Huang.AssocConverse
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}

/-- A finite split presentation by irreducible lowest-weight modules. -/
structure SimplePresentation (X : Ordinary W) where
  size : ℕ
  part : Fin size → LWModule W
  irreducible : ∀ j, (part j).IsIrreducibleLW
  inc : ∀ j, Ordinary.of (part j).isMod ⟶ X
  proj : ∀ j, X ⟶ Ordinary.of (part j).isMod
  total : ∀ x, ∑ j, (inc j).val ((proj j).val x) = x

/-- Complete reducibility and ordinary weight-space finiteness supply the presentation. -/
theorem simplePresentation_nonempty (hV : StronglyRational W) (hΦ : Finite (Φ W))
    (X : Ordinary W) : Nonempty (SimplePresentation X) := by
  obtain ⟨n, R, iR, hc, _⟩ := exists_completeIrredundantFamily hΦ
  let S : ULift.{u} (Fin n) → LWModule W := fun j => R j.down
  have hcS : ∀ Q : LWModule W, Q.IsIrreducibleLW → ∃ j, LWModule.Iso W Q (S j) := by
    intro Q iQ
    obtain ⟨j, hj⟩ := hc Q iQ
    exact ⟨⟨j⟩, hj⟩
  obtain ⟨r, lab, inc, proj, ht⟩ :=
    finiteTargets_of_stronglyRational hV hΦ S hcS X.carrier X.isMod
  exact ⟨⟨r, fun j => S (lab j), fun j => iR (lab j).down, inc, proj, ht⟩⟩

variable (F : FusionChoice W) {X Y Z T X' Y' Z' T' : Ordinary W}

/-- Restrict all inputs and postcompose the output of a represented iterate. -/
def iterateMap (f : X' ⟶ X) (g : Y' ⟶ Y) (h : Z' ⟶ Z) (k : T ⟶ T')
    (I : IterateSpace F X Y Z T) : IterateSpace F X' Y' Z' T' :=
  postcompose (restrictInputs (tensorHom F f g) h I) T'.isMod k

/-- Restrict all inputs and postcompose the output of a represented product. -/
def productMap (f : X' ⟶ X) (g : Y' ⟶ Y) (h : Z' ⟶ Z) (k : T ⟶ T')
    (I : ProductSpace F X Y Z T) : ProductSpace F X' Y' Z' T' :=
  postcompose (restrictInputs f (tensorHom F g h) I) T'.isMod k

theorem iterateWeightTerm_map (f : X' ⟶ X) (g : Y' ⟶ Y) (h : Z' ⟶ Z) (k : T ⟶ T')
    (I : IterateSpace F X Y Z T) (d : FourPointTest X' Y' Z' T') (w : ℂ) :
    iterateWeightTerm F (iterateMap F f g h k I) d w =
      iterateWeightTerm F I ((d.inputs f g h).output k) w := by
  change d.functional (k.val (I.val _ ((tensorHom F f g).val _) (h.val d.z))) * _ = _
  rw [tensorHom_intertwiner]
  rfl

theorem productWeightTerm_map (f : X' ⟶ X) (g : Y' ⟶ Y) (h : Z' ⟶ Z) (k : T ⟶ T')
    (I : ProductSpace F X Y Z T) (d : FourPointTest X' Y' Z' T') (w : ℂ) :
    productWeightTerm F (productMap F f g h k I) d w =
      productWeightTerm F I ((d.inputs f g h).output k) w := by
  change d.functional (k.val (I.val _ (f.val d.x) ((tensorHom F g h).val _))) * _ = _
  rw [tensorHom_intertwiner]
  rfl

theorem iterateEvaluation_map (f : X' ⟶ X) (g : Y' ⟶ Y) (h : Z' ⟶ Z) (k : T ⟶ T')
    (I : IterateSpace F X Y Z T) (d : FourPointTest X' Y' Z' T') :
    iterateEvaluation F (iterateMap F f g h k I) d =
      iterateEvaluation F I ((d.inputs f g h).output k) := by
  exact tsum_congr (iterateWeightTerm_map F f g h k I d)

theorem productEvaluation_map (f : X' ⟶ X) (g : Y' ⟶ Y) (h : Z' ⟶ Z) (k : T ⟶ T')
    (I : ProductSpace F X Y Z T) (d : FourPointTest X' Y' Z' T') :
    productEvaluation F (productMap F f g h k I) d =
      productEvaluation F I ((d.inputs f g h).output k) := by
  exact tsum_congr (productWeightTerm_map F f g h k I d)

variable (A : SimplePresentation X) (B : SimplePresentation Y)
  (C : SimplePresentation Z) (D : SimplePresentation T)

/-- One finite index for the four independent external summands. -/
abbrev ExternalIndex := Fin A.size × Fin B.size × Fin C.size × Fin D.size

/-- Restriction to four simple external summands. -/
def iterateComponent (I : IterateSpace F X Y Z T) (j : ExternalIndex A B C D) :=
  iterateMap F (A.inc j.1) (B.inc j.2.1) (C.inc j.2.2.1) (D.proj j.2.2.2) I

def productComponent (I : ProductSpace F X Y Z T) (j : ExternalIndex A B C D) :=
  productMap F (A.inc j.1) (B.inc j.2.1) (C.inc j.2.2.1) (D.proj j.2.2.2) I

/-- A finite external decomposition reconstructs the actual represented iterate. -/
theorem iterate_reassemble (I : IterateSpace F X Y Z T) :
    (∑ j : ExternalIndex A B C D,
      iterateMap F (A.proj j.1) (B.proj j.2.1) (C.proj j.2.2.1) (D.inc j.2.2.2)
        (iterateComponent F A B C D I j)) = I := by
  classical
  apply Subtype.ext
  funext q
  apply LinearMap.ext
  intro v
  apply LinearMap.ext
  intro z
  let J := ∑ j : ExternalIndex A B C D,
      iterateMap F (A.proj j.1) (B.proj j.2.1) (C.proj j.2.2.1) (D.inc j.2.2.2)
        (iterateComponent F A B C D I j)
  have he : (J.val q).flip z = (I.val q).flip z := by
    apply tensor_linear_ext (F X Y)
    intro p x y
    change J.val q ((F X Y).intertwiner.val p x y) z = _
    dsimp only [J]
    simp only [Submodule.coe_sum, Finset.sum_apply, LinearMap.sum_apply]
    change (∑ j : ExternalIndex A B C D, (D.inc j.2.2.2).val ((D.proj j.2.2.2).val
      (I.val q ((tensorHom F (A.inc j.1) (B.inc j.2.1)).val
        ((tensorHom F (A.proj j.1) (B.proj j.2.1)).val
          ((F X Y).intertwiner.val p x y)))
        ((C.inc j.2.2.1).val ((C.proj j.2.2.1).val z))))) = _
    simp only [tensorHom_intertwiner, Fintype.sum_prod_type]
    conv_lhs =>
      arg 2; ext a
      arg 2; ext b
      arg 2; ext c
      tactic => exact D.total (I.val q
        ((F X Y).intertwiner.val p ((A.inc a).val ((A.proj a).val x))
          ((B.inc b).val ((B.proj b).val y))) ((C.inc c).val ((C.proj c).val z)))
    simp only [← map_sum, ← LinearMap.sum_apply]
    simp_rw [C.total, B.total, A.total]
    rfl
  exact congrArg (fun k : (F X Y).carrier →ₗ[ℂ] T.carrier => k v) he

/-- The same reconstruction for the represented product. -/
theorem product_reassemble (I : ProductSpace F X Y Z T) :
    (∑ j : ExternalIndex A B C D,
      productMap F (A.proj j.1) (B.proj j.2.1) (C.proj j.2.2.1) (D.inc j.2.2.2)
        (productComponent F A B C D I j)) = I := by
  classical
  apply Subtype.ext
  funext q
  apply LinearMap.ext
  intro x
  apply tensor_linear_ext (F Y Z)
  intro p y z
  simp only [Submodule.coe_sum, Finset.sum_apply, LinearMap.sum_apply]
  change (∑ j : ExternalIndex A B C D, (D.inc j.2.2.2).val ((D.proj j.2.2.2).val
    (I.val q ((A.inc j.1).val ((A.proj j.1).val x))
      ((tensorHom F (B.inc j.2.1) (C.inc j.2.2.1)).val
        ((tensorHom F (B.proj j.2.1) (C.proj j.2.2.1)).val
          ((F Y Z).intertwiner.val p y z)))))) = _
  simp only [tensorHom_intertwiner, Fintype.sum_prod_type]
  conv_lhs =>
    arg 2; ext a
    arg 2; ext b
    arg 2; ext c
    tactic => exact D.total (I.val q ((A.inc a).val ((A.proj a).val x))
      ((F Y Z).intertwiner.val p ((B.inc b).val ((B.proj b).val y))
        ((C.inc c).val ((C.proj c).val z))))
  simp only [← map_sum, ← LinearMap.sum_apply]
  simp_rw [C.total, B.total, A.total]

end VOA.Huang.TensorCat
