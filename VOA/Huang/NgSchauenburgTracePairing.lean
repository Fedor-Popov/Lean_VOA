import VOA.Huang.NgSchauenburgEquivarianceReduction

/-! # The categorical trace pairing on Hom spaces

The ordinary linear trace defining an indicator is converted into a sum of
categorical traces using the actual spherical trace pairing. Its perfection
is proved from semisimplicity and nonzero simple dimensions, not assumed.
This supplies the dual-basis step in NS 0806.2493, Proposition 3.1 and the
proof of Theorem 5.4. It does not supply Müger's half-braiding Fourier identity.
-/
noncomputable section
set_option linter.unusedSectionVars false
universe v u
namespace VOA.Huang.NgSchauenburg
open CategoryTheory MonoidalCategory Limits
attribute [-instance] hasRightDualUnit hasRightDualLeftDual

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]

namespace SphericalFusion
variable (F : SphericalFusion C)

/-- The numerical pivotal trace, as a linear map. -/
def scalarTrace (X : C) : (X ⟶ X) →ₗ[ℂ] ℂ where
  toFun f := F.unitScalar.symm (F.traceRight f)
  map_add' f g := by simp [Pivotal.traceRight, map_add,
    MonoidalPreadditive.add_whiskerRight, Preadditive.add_comp, Preadditive.comp_add]
  map_smul' z f := by simp [Pivotal.traceRight]

@[simp] theorem scalarTrace_id (X : C) : F.scalarTrace X (𝟙 X) = F.dimension X := rfl

theorem scalarTrace_comp_comm {X Y : C} (f : X ⟶ Y) (g : Y ⟶ X) :
    F.scalarTrace X (f ≫ g) = F.scalarTrace Y (g ≫ f) :=
  congrArg F.unitScalar.symm (F.toPivotal.traceRight_comp_comm f g)

/-- A nonzero morphism has a reverse morphism with nonzero categorical pairing.
The proof extracts one simple source summand and splits its nonzero image. -/
theorem exists_trace_pair_ne_zero {X Y : C} (f : X ⟶ Y) (hf : f ≠ 0) :
    ∃ g : Y ⟶ X, F.scalarTrace X (f ≫ g) ≠ 0 := by
  classical
  obtain ⟨n, a, ⟨e⟩⟩ := F.decomposition X
  have hex : ∃ k, (biproduct.ι (fun k => F.simple (a k)) k ≫ e.inv) ≫ f ≠ 0 := by
    by_contra! h
    apply hf
    have he : e.inv ≫ f = 0 := by
      apply biproduct.hom_ext'
      intro k
      simpa only [Category.assoc, comp_zero] using h k
    have := congrArg (fun g => e.hom ≫ g) he
    simpa using this
  obtain ⟨k, hk⟩ := hex
  letI := F.simple_isSimple (a k)
  obtain ⟨q, hq⟩ := F.exists_retraction_of_simple _ hk
  refine ⟨q ≫ biproduct.ι (fun k => F.simple (a k)) k ≫ e.inv, ?_⟩
  have he : F.scalarTrace X (f ≫ q ≫ biproduct.ι (fun k => F.simple (a k)) k ≫ e.inv) =
      F.dimension (F.simple (a k)) := by
    calc
      _ = F.scalarTrace (F.simple (a k))
          ((biproduct.ι (fun k => F.simple (a k)) k ≫ e.inv) ≫ (f ≫ q)) := by
        simpa only [Category.assoc] using F.scalarTrace_comp_comm
          (f ≫ q) (biproduct.ι (fun k => F.simple (a k)) k ≫ e.inv)
      _ = _ := by
        simpa only [Category.assoc] using congrArg (F.scalarTrace (F.simple (a k))) hq
  rw [he]
  exact F.dimension_simple_ne_zero (a k)

/-- The pairing `Hom(Y,X) × Hom(X,Y) → ℂ` given by categorical trace. -/
def tracePairing (X Y : C) : (Y ⟶ X) →ₗ[ℂ] Module.Dual ℂ (X ⟶ Y) where
  toFun g :=
    { toFun := fun f => F.scalarTrace X (f ≫ g)
      map_add' := by intros; simp [Preadditive.add_comp]
      map_smul' := by intros; simp }
  map_add' := by intros; ext f; simp [Preadditive.comp_add]
  map_smul' := by intros; ext f; simp

@[simp] theorem tracePairing_apply {X Y : C} (g : Y ⟶ X) (f : X ⟶ Y) :
    F.tracePairing X Y g f = F.scalarTrace X (f ≫ g) := rfl

/-- The pivotal trace pairing has zero left radical. -/
theorem tracePairing_injective (X Y : C) : Function.Injective (F.tracePairing X Y) := by
  apply (LinearMap.ker_eq_bot).mp
  apply LinearMap.ker_eq_bot'.mpr
  intro g hg
  by_contra hne
  obtain ⟨f, hf⟩ := F.exists_trace_pair_ne_zero g hne
  apply hf
  rw [F.scalarTrace_comp_comm]
  exact congrArg (fun l : Module.Dual ℂ (X ⟶ Y) => l f) hg

/-- Perfection uses the proved equality of the two Hom dimensions. -/
def tracePairingEquiv (X Y : C) : (Y ⟶ X) ≃ₗ[ℂ] Module.Dual ℂ (X ⟶ Y) := by
  letI := F.homFinite
  apply LinearEquiv.ofInjectiveOfFinrankEq (F.tracePairing X Y)
    (F.tracePairing_injective X Y)
  rw [Subspace.dual_finrank_eq, F.finrank_hom_symm]

@[simp] theorem tracePairingEquiv_apply {X Y : C} (g : Y ⟶ X) (f : X ⟶ Y) :
    F.tracePairingEquiv X Y g f = F.scalarTrace X (f ≫ g) := rfl

open Classical in
/-- The basis of reverse morphisms dual to a given Hom basis under pivotal trace. -/
def traceDualBasis {X Y : C} {ι : Type*} [Finite ι]
    (b : Module.Basis ι ℂ (X ⟶ Y)) : Module.Basis ι ℂ (Y ⟶ X) :=
  b.dualBasis.map (F.tracePairingEquiv X Y).symm

@[simp] theorem traceDualBasis_pair {X Y : C} {ι : Type*} [Finite ι]
    (b : Module.Basis ι ℂ (X ⟶ Y)) (i : ι) (f : X ⟶ Y) :
    F.scalarTrace X (f ≫ F.traceDualBasis b i) = b.repr f i := by
  classical
  change F.tracePairingEquiv X Y ((F.tracePairingEquiv X Y).symm (b.dualBasis i)) f = _
  rw [LinearEquiv.apply_symm_apply, Module.Basis.dualBasis_apply]

/-- Ordinary linear trace on a Hom space is the contraction of categorical
trace-dual bases. No diagram evaluation is hidden in the statement. -/
theorem linearTrace_eq_sum_scalarTrace {X Y : C} {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℂ (X ⟶ Y)) (E : Module.End ℂ (X ⟶ Y)) :
    LinearMap.trace ℂ (X ⟶ Y) E =
      ∑ i, F.scalarTrace X (E (b i) ≫ F.traceDualBasis b i) := by
  classical
  rw [LinearMap.trace_eq_matrix_trace ℂ b]
  simp [Matrix.trace, LinearMap.toMatrix_apply]

end SphericalFusion

/-- Categorical trace expansion of the actual integer power of central rotation. -/
theorem generalizedIndicatorInt_eq_sum_scalarTrace (F : SphericalFusion C)
    (A : Center C) (V : C) (n : ℕ) (l : ℤ) {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℂ (A.1 ⟶ tensorPower V (n + 1))) :
    generalizedIndicatorInt F.toPivotal A V n l =
      ∑ i, F.scalarTrace A.1
        (((generalizedRotation F.toPivotal A V n) ^ l) (b i) ≫ F.traceDualBasis b i) :=
  F.linearTrace_eq_sum_scalarTrace b _

end VOA.Huang.NgSchauenburg
