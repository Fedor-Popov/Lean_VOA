import VOA.Huang.NgSchauenburgCategory
import VOA.Huang.NgSchauenburgCyclotomic

/-!
# Frobenius–Schur rotation and indicators

Tensor powers are right associated, with `V^0 = 1` and `V^1 = V`.
For degree one the ordinary rotation is in its reduced form, the identity.
For higher degrees it is constructed from evaluation, coevaluation and `j⁻¹`.
The indicator is the **ordinary linear trace on the Hom space**. It is not
the categorical trace of an endomorphism of `V`.

The cyclic-order and additivity statements below are named, unproved Props;
they are not fields of `SphericalFusion`. Cyclotomicity is proved conditional
on the cyclic-order identity. Generalized indicators here cover positive
first index and nonnegative second index; the full integer-index convention
and the equivariance target are not treated here.
-/

noncomputable section
set_option linter.unusedSectionVars false
universe v u

namespace VOA.Huang.NgSchauenburg

open CategoryTheory MonoidalCategory Limits

attribute [-instance] hasRightDualUnit hasRightDualLeftDual

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]

/-- Rebracketing-free degree one convention for right-associated powers. -/
def tensorPower (V : C) : ℕ → C
  | 0 => 𝟙_ C
  | 1 => V
  | n + 2 => V ⊗ tensorPower V (n + 1)

/-- Move the final factor into a right-associated power, using associators only. -/
def appendPower (V : C) : (n : ℕ) → tensorPower V (n + 1) ⊗ V ≅ tensorPower V (n + 2)
  | 0 => Iso.refl _
  | n + 1 => (α_ V (tensorPower V (n + 1)) V) ≪≫ whiskerLeftIso V (appendPower V n)

/-- Linear transport of Hom spaces along object isomorphisms. -/
def homCongr {X X' Y Y' : C} (e : X ≅ X') (f : Y ≅ Y') :
    (X ⟶ Y) ≃ₗ[ℂ] (X' ⟶ Y') where
  toFun g := e.inv ≫ g ≫ f.hom
  invFun g := e.hom ≫ g ≫ f.inv
  left_inv g := by simp
  right_inv g := by simp
  map_add' g h := by simp [Preadditive.comp_add, Preadditive.add_comp]
  map_smul' z g := by simp

/-- Linear version of Mathlib's left duality adjunction. -/
def leftDuality (X V W : C) : (Vᘁ ⊗ X ⟶ W) ≃ₗ[ℂ] (X ⟶ V ⊗ W) :=
  { tensorLeftHomEquiv X V Vᘁ W with
    map_add' := by
      intro f g
      simp [tensorLeftHomEquiv, MonoidalPreadditive.whiskerLeft_add,
        Preadditive.comp_add]
    map_smul' := by intro z f; simp [tensorLeftHomEquiv] }

/-- Linear version of Mathlib's right duality adjunction. -/
def rightDuality (X V W : C) : (X ⊗ V ⟶ W) ≃ₗ[ℂ] (X ⟶ W ⊗ Vᘁ) :=
  { tensorRightHomEquiv X V Vᘁ W with
    map_add' := by
      intro f g
      simp [tensorRightHomEquiv, MonoidalPreadditive.add_whiskerRight,
        Preadditive.comp_add]
    map_smul' := by intro z f; simp [tensorRightHomEquiv] }

/-- The Ng–Schauenburg cyclic transposition `Hom(1,V⊗W) → Hom(1,W⊗V)`.
The three steps are bending down `V`, bending up `V*`, and applying `j_V⁻¹`. -/
def rotation (P : Pivotal C) (V W : C) :
    (𝟙_ C ⟶ V ⊗ W) ≃ₗ[ℂ] (𝟙_ C ⟶ W ⊗ V) :=
  (leftDuality (𝟙_ C) V W).symm |>.trans
    (homCongr ((ρ_ Vᘁ) ≪≫ (λ_ Vᘁ).symm) (Iso.refl W)) |>.trans
    (rightDuality (𝟙_ C) Vᘁ W) |>.trans
    (homCongr (Iso.refl _) (whiskerLeftIso W (P.j V).symm))

/-- Rotation on `Hom(1,V^n)`; the zero-degree identity is only a convention.
All substantive indicator claims below are restricted to positive degree. -/
def fsRotation (P : Pivotal C) (V : C) :
    (n : ℕ) → (𝟙_ C ⟶ tensorPower V n) ≃ₗ[ℂ] (𝟙_ C ⟶ tensorPower V n)
  | 0 => LinearEquiv.refl ℂ _
  | 1 => LinearEquiv.refl ℂ _
  | n + 2 => (rotation P V (tensorPower V (n + 1))).trans
      (homCongr (Iso.refl _) (appendPower V n))

/-- The `n`-th Frobenius–Schur indicator, the linear trace of the rotation. -/
def indicator (P : Pivotal C) (V : C) (n : ℕ) : ℂ :=
  LinearMap.trace ℂ (𝟙_ C ⟶ tensorPower V n) (fsRotation P V n).toLinearMap

theorem fsRotation_one (P : Pivotal C) (V : C) :
    fsRotation P V 1 = LinearEquiv.refl ℂ (𝟙_ C ⟶ V) := rfl

variable [HasKernels C] [HasFiniteBiproducts C]

attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

theorem indicator_one (F : SphericalFusion C) (V : C) :
    indicator F.toPivotal V 1 = (Module.finrank ℂ (𝟙_ C ⟶ V) : ℂ) := by
  letI := F.homFinite (𝟙_ C) V
  change LinearMap.trace ℂ (𝟙_ C ⟶ V) LinearMap.id = _
  exact LinearMap.trace_id ℂ _

open Classical in
/-- The Kronecker delta formula requires a simple object. -/
theorem indicator_one_simple (F : SphericalFusion C) (V : C) [Simple V] :
    indicator F.toPivotal V 1 = if Nonempty (V ≅ 𝟙_ C) then 1 else 0 := by
  classical
  letI := F.homFinite (𝟙_ C) (𝟙_ C)
  letI := F.homFinite (𝟙_ C) V
  letI := F.simple_unit
  rw [indicator_one]
  split_ifs with h
  · obtain ⟨e⟩ := h
    rw [(finrank_hom_simple_simple_eq_one_iff ℂ (𝟙_ C) V).mpr ⟨e.symm⟩]
    simp
  · rw [finrank_hom_simple_simple_eq_zero_of_not_iso ℂ
      (fun e => h ⟨e.symm⟩)]
    simp

theorem indicator_one_unit (F : SphericalFusion C) :
    indicator F.toPivotal (𝟙_ C) 1 = 1 := by
  rw [indicator_one, F.finrank_end_unit]
  simp

/-- Degree-one indicators are invariant under object isomorphism. -/
theorem indicator_one_iso (F : SphericalFusion C) {V W : C} (e : V ≅ W) :
    indicator F.toPivotal V 1 = indicator F.toPivotal W 1 := by
  rw [indicator_one, indicator_one,
    (homCongr (Iso.refl (𝟙_ C)) e).finrank_eq]

/-- The standard Hom-space decomposition of a binary biproduct, linearly. -/
def homBiprod (X V W : C) : (X ⟶ V ⊞ W) ≃ₗ[ℂ] ((X ⟶ V) × (X ⟶ W)) where
  toFun f := (f ≫ biprod.fst, f ≫ biprod.snd)
  invFun f := biprod.lift f.1 f.2
  left_inv f := by aesop_cat
  right_inv f := by simp
  map_add' f g := by simp [Preadditive.add_comp]
  map_smul' z f := by simp

/-- Additivity of the first indicator, with no simplicity restriction. -/
theorem indicator_one_add (F : SphericalFusion C) (V W : C) :
    indicator F.toPivotal (V ⊞ W) 1 =
      indicator F.toPivotal V 1 + indicator F.toPivotal W 1 := by
  letI := F.homFinite (𝟙_ C) V
  letI := F.homFinite (𝟙_ C) W
  rw [indicator_one, indicator_one, indicator_one,
    (homBiprod (𝟙_ C) V W).finrank_eq, Module.finrank_prod]
  simp

/-- Computing in any basis gives the same indicator. -/
theorem indicator_eq_matrix_trace (F : SphericalFusion C) (V : C) (n : ℕ)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℂ (𝟙_ C ⟶ tensorPower V n)) :
    indicator F.toPivotal V n =
      Matrix.trace (LinearMap.toMatrix b b (fsRotation F.toPivotal V n).toLinearMap) := by
  exact LinearMap.trace_eq_matrix_trace ℂ b _

/-- When the invariant Hom space vanishes, so does the indicator. -/
theorem indicator_eq_zero_of_subsingleton (P : Pivotal C) (V : C) (n : ℕ)
    [Subsingleton (𝟙_ C ⟶ tensorPower V n)] : indicator P V n = 0 := by
  have h : (fsRotation P V n).toLinearMap = 0 := Subsingleton.elim _ _
  simp [indicator, h]

/-- Cyclic coherence theorem to be proved from pivotal monoidality. -/
def RotationOrder (F : SphericalFusion C) : Prop :=
  ∀ (V : C) (n : ℕ), 0 < n → (fsRotation F.toPivotal V n).toLinearMap ^ n = 1

/-- Positive-degree unit normalization theorem, not assumed by the category. -/
def IndicatorUnit (F : SphericalFusion C) : Prop :=
  ∀ n : ℕ, 0 < n → indicator F.toPivotal (𝟙_ C) n = 1

/-- Additivity in the object for the ordinary higher indicators. -/
def IndicatorAdditive (F : SphericalFusion C) : Prop :=
  ∀ (V W : C) (n : ℕ), 0 < n →
    indicator F.toPivotal (V ⊞ W) n = indicator F.toPivotal V n + indicator F.toPivotal W n

theorem indicator_mem_cyclotomicIntegers (F : SphericalFusion C)
    (horder : RotationOrder F) (V : C) {n : ℕ} (hn : 0 < n) :
    indicator F.toPivotal V n ∈
      Algebra.adjoin ℤ ({Complex.exp (2 * Real.pi * Complex.I / n)} : Set ℂ) := by
  letI := F.homFinite (𝟙_ C) (tensorPower V n)
  exact trace_mem_standardCyclotomicIntegers _ hn (horder V n hn)

/-- The actual condition defining the FS exponent; quantifies over all objects. -/
def IsFSExponent (F : SphericalFusion C) (n : ℕ) : Prop :=
  0 < n ∧ ∀ V : C, indicator F.toPivotal V n = F.dimension V

open Classical in
/-- FS exponent with the conventional value `0` when no finite exponent exists.
Finiteness is a separate theorem, not baked into the definition. -/
def fsExponent (F : SphericalFusion C) : ℕ :=
  if h : ∃ n, IsFSExponent F n then Nat.find h else 0

theorem fsExponent_spec (F : SphericalFusion C) (h : ∃ n, IsFSExponent F n) :
    IsFSExponent F (fsExponent F) := by
  classical
  unfold fsExponent
  rw [dif_pos h]
  exact Nat.find_spec h

theorem fsExponent_le (F : SphericalFusion C) {n : ℕ} (h : IsFSExponent F n) :
    fsExponent F ≤ n := by
  classical
  unfold fsExponent
  rw [dif_pos ⟨n, h⟩]
  exact Nat.find_min' _ h

/-- Generalized single rotation using a genuine object of Mathlib's Drinfeld center. -/
def centerRotation (P : Pivotal C) (X : Center C) (V W : C) :
    (X.1 ⟶ V ⊗ W) ≃ₗ[ℂ] (X.1 ⟶ W ⊗ V) :=
  (leftDuality X.1 V W).symm |>.trans
    (homCongr (X.2.β Vᘁ).symm (Iso.refl W)) |>.trans
    (rightDuality X.1 Vᘁ W) |>.trans
    (homCongr (Iso.refl _) (whiskerLeftIso W (P.j V).symm))

/-- The generalized rotation with positive first index `n+1`. -/
def generalizedRotation (P : Pivotal C) (X : Center C) (V : C) :
    (n : ℕ) → (X.1 ⟶ tensorPower V (n + 1)) ≃ₗ[ℂ] (X.1 ⟶ tensorPower V (n + 1))
  | 0 => (homCongr (Iso.refl _) (ρ_ V).symm).trans
      ((centerRotation P X V (𝟙_ C)).trans (homCongr (Iso.refl _) (λ_ V)))
  | n + 1 => (centerRotation P X V (tensorPower V (n + 1))).trans
      (homCongr (Iso.refl _) (appendPower V n))

/-- `ν^X_{n+1,l}(V)` for `l ≥ 0`, by powers of the canonical single rotation.
Agreement with the block-evaluation definition is a further diagram identity. -/
def generalizedIndicator (P : Pivotal C) (X : Center C) (V : C) (n l : ℕ) : ℂ :=
  LinearMap.trace ℂ (X.1 ⟶ tensorPower V (n + 1))
    ((generalizedRotation P X V n).toLinearMap ^ l)

theorem generalizedIndicator_zero (F : SphericalFusion C) (X : Center C) (V : C) (n : ℕ) :
    generalizedIndicator F.toPivotal X V n 0 =
      (Module.finrank ℂ (X.1 ⟶ tensorPower V (n + 1)) : ℂ) := by
  letI := F.homFinite X.1 (tensorPower V (n + 1))
  simp [generalizedIndicator, LinearMap.trace_one]

end VOA.Huang.NgSchauenburg
