import VOA.Huang.TensorCatUnit
import VOA.Huang.BraidingSkewJacobi

/-! # Skew-symmetry transports universality and supplies the right unit

Only the algebraic skew equivalence is used. No braiding or hexagon is asserted.
-/

noncomputable section
namespace VOA.Huang.TensorCat
open VOA VOA.Huang.FusionUnit VOA.Huang.FusionProduct CategoryTheory
open VOA.Huang.BraidingSkew
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}

/-- Skew-symmetry with the library's upper-half-plane phase. -/
def skew (X Y Z : Ordinary W) :
    IntertwiningOperator X.isMod Y.isMod Z.isMod ≃ₗ[ℂ]
      IntertwiningOperator Y.isMod X.isMod Z.isMod :=
  skewEquiv X.isMod Y.isMod Z.isMod omegaPhase_succ omegaPhase_ne_zero

private theorem hom_Lm1_pow {X Y : Ordinary W} (f : X ⟶ Y) (j : ℕ) (x : X.carrier) :
    f.val ((X.isMod.Lm1 ^ j) x) = (Y.isMod.Lm1 ^ j) (f.val x) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [pow_succ', Module.End.mul_apply]
    rw [show f.val (X.isMod.Lm1 ((X.isMod.Lm1 ^ j) x)) =
      Y.isMod.Lm1 (f.val ((X.isMod.Lm1 ^ j) x)) from
        f.property W.conformalVector 0 _, ih]

/-- Skew-symmetry is natural in the output module. -/
theorem skew_postcompose {X Y Z T : Ordinary W}
    (I : IntertwiningOperator X.isMod Y.isMod Z.isMod) (f : Z ⟶ T) :
    skew X Y T (postcompose I T.isMod f) =
      postcompose (skew X Y Z I) T.isMod f := by
  apply Subtype.ext
  funext n
  ext y x
  change skewModes T.isMod.Lm1 omegaPhase (postcompose I T.isMod f).val n y x =
    f.val (skewModes Z.isMod.Lm1 omegaPhase I.val n y x)
  rw [skewModes_apply (trunc_of_isIntertwining (postcompose I T.isMod f).property),
    skewModes_apply (trunc_of_isIntertwining I.property), map_smul]
  obtain ⟨K, hK⟩ := (trunc_of_isIntertwining I.property).bound x y n
  have hK' : ∀ j : ℕ, K ≤ j → (postcompose I T.isMod f).val (n + j) x y = 0 := by
    intro j hj
    simp only [postcompose_apply, hK j hj, map_zero]
  rw [sSum_eq_sum K hK', sSum_eq_sum K hK, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  simp only [sTerm, postcompose_apply, map_smul, hom_Lm1_pow]

/-- Skew-symmetry exchanges the two input maps. -/
theorem skew_restrictInputs {X X' Y Y' Z : Ordinary W}
    (I : IntertwiningOperator X'.isMod Y'.isMod Z.isMod)
    (f : X ⟶ X') (g : Y ⟶ Y') :
    skew X Y Z (restrictInputs f g I) = restrictInputs g f (skew X' Y' Z I) := by
  apply Subtype.ext
  funext n
  ext y x
  change skewModes Z.isMod.Lm1 omegaPhase (restrictInputs f g I).val n y x =
    skewModes Z.isMod.Lm1 omegaPhase I.val n (g.val y) (f.val x)
  rw [skewModes_apply (trunc_of_isIntertwining (restrictInputs f g I).property),
    skewModes_apply (trunc_of_isIntertwining I.property)]
  rfl

/-- Swapping the inputs of a universal intertwiner preserves its full universality. -/
theorem skew_isUniversal {X Y Z : Ordinary W}
    (I : IntertwiningOperator X.isMod Y.isMod Z.isMod) (hI : IsUniversal I) :
    IsUniversal (skew X Y Z I) := by
  intro N _ _ AN
  have he : postcompose (skew X Y Z I) AN =
      (skew X Y (Ordinary.of AN)).toLinearMap.comp (postcompose I AN) := by
    ext f n x y
    exact congrArg (fun J : IntertwiningOperator Y.isMod X.isMod AN => J.val n x y)
      (skew_postcompose (X := X) (Y := Y) (Z := Z) (T := Ordinary.of AN) I f).symm
  unfold UniversalFor
  rw [he]
  exact (skew X Y (Ordinary.of AN)).bijective.comp (hI N AN)

/-- A representing product with the inputs swapped by skew-symmetry. -/
def swappedProduct {X Y : Ordinary W} (P : Product X.isMod Y.isMod) :
    Product Y.isMod X.isMod where
  carrier := P.carrier
  isMod := P.isMod
  intertwiner := skew X Y (Ordinary.ofProduct P) P.intertwiner
  universal := skew_isUniversal (X := X) (Y := Y) (Z := Ordinary.ofProduct P)
    P.intertwiner P.universal

/-- The right-unit universal intertwiner is the skew module vertex operator. -/
def rightUnitProduct (X : Ordinary W) : Product X.isMod (adjointModule W) :=
  swappedProduct (X := vacuumObject) (Y := X) (unitProduct X.isMod)

variable (F : FusionChoice W)

/-- The actual vacuum right unitor, with no associativity or rationality assumption on F. -/
def rightUnitor (X : Ordinary W) : tensorObj F X vacuumObject ≅ X :=
  Ordinary.isoOfModuleEquiv (productIso (F X vacuumObject) (rightUnitProduct X))

@[simp] theorem rightUnitor_intertwiner (X : Ordinary W)
    (n : ℂ) (x : X.carrier) (v : V) :
    (rightUnitor F X).hom.val ((F X vacuumObject).intertwiner.val n x v) =
      (skew vacuumObject X X (moduleIntertwiner X.isMod)).val n x v :=
  productIso_intertwiner (F X vacuumObject) (rightUnitProduct X) n x v

theorem rightUnitor_naturality {X Y : Ordinary W} (f : X ⟶ Y) :
    tensorHom F f (𝟙 vacuumObject) ≫ (rightUnitor F Y).hom =
      (rightUnitor F X).hom ≫ f := by
  have he : restrictInputs (𝟙 vacuumObject) f (moduleIntertwiner Y.isMod) =
      postcompose (moduleIntertwiner X.isMod) Y.isMod f := by
    apply Subtype.ext
    funext n
    ext v x
    classical
    change moduleModes Y.isMod n v (f.val x) = f.val (moduleModes X.isMod n v x)
    unfold moduleModes
    split_ifs with h
    · exact (f.property v h.choose x).symm
    · simp
  have hs := (skew_restrictInputs (moduleIntertwiner Y.isMod) (𝟙 vacuumObject) f).symm
  rw [he] at hs
  have hs' := hs.trans (skew_postcompose (X := vacuumObject) (Y := X) (Z := X)
    (T := Y) (moduleIntertwiner X.isMod) f)
  apply tensor_hom_ext F
  intro n x v
  simp only [Ordinary.comp_apply, tensorHom_intertwiner, Ordinary.id_apply,
    rightUnitor_intertwiner]
  exact congrArg (fun J : IntertwiningOperator X.isMod (adjointModule W) Y.isMod =>
    J.val n x v) hs'

end VOA.Huang.TensorCat
