import VOA.Huang.LiFusionReconstruction
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Scalar coefficient reconstruction for Li's converse

We use the full algebraic dual as a testing space. The support equation below
forces each homogeneous coefficient to factor through the dual of one finite
weight space; thus it yields a vector of the module, not merely a vector of its
completion. This supplies algebraic coefficient recovery for a scalar-pairing
approach to Li's converse; it does not formalize Li's induced-module
construction.

The existence of scalar coefficients extending an arbitrary Frenkel–Zhu datum
is not proved here. In particular no induced-module surjection is used as a
substitute for such an extension.
-/
namespace VOA.Huang.LiFusion
open VOA FusionTop
open scoped BigOperators
universe u
variable {V M₁ M₂ M₃ : Type u}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup M₁] [Module ℂ M₁]
  [AddCommGroup M₂] [Module ℂ M₂] [AddCommGroup M₃] [Module ℂ M₃]
  {W : VertexOperatorAlgebra V}
  {A₁ : OrdVModule W M₁} {A₂ : OrdVModule W M₂} {A₃ : OrdVModule W M₃}

/-- A scalar mode coefficient, trilinear in the two input vectors and a test
functional on the target. -/
abbrev ScalarModes (M₁ M₂ M₃ : Type u)
    [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
    [AddCommGroup M₃] [Module ℂ M₃] :=
  ℂ → M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] Module.Dual ℂ (Module.Dual ℂ M₃)

/-- Projection onto a single ordinary weight space, with codomain the module. -/
noncomputable def weightProjection (A₃ : OrdVModule W M₃) (γ : ℂ) : Module.End ℂ M₃ :=
  (A₃.weight γ).subtype.comp (internalProjTo A₃.isInternal γ)

theorem weightProjection_of_mem (A₃ : OrdVModule W M₃) {γ : ℂ} {v : M₃}
    (hv : v ∈ A₃.weight γ) : weightProjection A₃ γ v = v :=
  congrArg Subtype.val (internalProjTo_coe A₃.isInternal γ ⟨v, hv⟩)

/-- Scalar grading: only the restriction of the test functional to the
predicted output weight is relevant. -/
def ScalarWeightCompatible (A₁ : OrdVModule W M₁) (A₂ : OrdVModule W M₂)
    (A₃ : OrdVModule W M₃) (C : ScalarModes M₁ M₂ M₃) : Prop :=
  ∀ (α β : ℂ) (x : M₁) (y : M₂), x ∈ A₁.weight α → y ∈ A₂.weight β →
    ∀ (n : ℂ) (f : Module.Dual ℂ M₃),
      C n x y f = C n x y (f.comp (weightProjection A₃ (α + β - n - 1)))

/-- Recovery in a finite weight space uses algebraic double-dual reflexivity. -/
theorem exists_vector_of_supported_functional (A₃ : OrdVModule W M₃) (γ : ℂ)
    (F : Module.Dual ℂ (Module.Dual ℂ M₃))
    (hF : ∀ f, F f = F (f.comp (weightProjection A₃ γ))) :
    ∃ v ∈ A₃.weight γ, ∀ f : Module.Dual ℂ M₃, f v = F f := by
  letI := A₃.finrank γ
  let p := internalProjTo A₃.isInternal γ
  let G : Module.Dual ℂ (Module.Dual ℂ (A₃.weight γ)) := F.comp p.dualMap
  let v := (Module.evalEquiv ℂ (A₃.weight γ)).symm G
  refine ⟨v, v.property, fun f => ?_⟩
  have hv := Module.apply_evalEquiv_symm_apply ℂ (A₃.weight γ)
    (f.comp (A₃.weight γ).subtype) G
  change f (v : M₃) = F f
  rw [show f (v : M₃) = F (f.comp (weightProjection A₃ γ)) from hv]
  exact (hF f).symm

/-- Every scalar coefficient has a representing vector. The proof extends
finite-weight recovery by the two internal direct-sum decompositions. -/
theorem scalarModes_representable {C : ScalarModes M₁ M₂ M₃}
    (hw : ScalarWeightCompatible A₁ A₂ A₃ C) (n : ℂ) (x : M₁) (y : M₂) :
    ∃ v : M₃, ∀ f : Module.Dual ℂ M₃, f v = C n x y f := by
  induction x using induction_weight A₁ with
  | h0 => exact ⟨0, fun _ => by simp⟩
  | hadd x x' hx hx' =>
    obtain ⟨v, hv⟩ := hx
    obtain ⟨v', hv'⟩ := hx'
    exact ⟨v + v', fun f => by simp [hv, hv']⟩
  | hhom α x hx =>
    induction y using induction_weight A₂ with
    | h0 => exact ⟨0, fun _ => by simp⟩
    | hadd y y' hy hy' =>
      obtain ⟨v, hv⟩ := hy
      obtain ⟨v', hv'⟩ := hy'
      exact ⟨v + v', fun f => by simp [hv, hv']⟩
    | hhom β y hy =>
      obtain ⟨v, _, hv⟩ := exists_vector_of_supported_functional A₃
        (α + β - n - 1) (C n x y) (hw α β x y hx hy n)
      exact ⟨v, hv⟩

theorem dual_ext {v w : M₃} (h : ∀ f : Module.Dual ℂ M₃, f v = f w) : v = w :=
  Module.eval_apply_injective ℂ (LinearMap.ext h)

noncomputable def recoveredVector {C : ScalarModes M₁ M₂ M₃}
    (hw : ScalarWeightCompatible A₁ A₂ A₃ C) (n : ℂ) (x : M₁) (y : M₂) : M₃ :=
  (scalarModes_representable hw n x y).choose

theorem recoveredVector_pairing {C : ScalarModes M₁ M₂ M₃}
    (hw : ScalarWeightCompatible A₁ A₂ A₃ C) (n : ℂ) (x : M₁) (y : M₂)
    (f : Module.Dual ℂ M₃) : f (recoveredVector hw n x y) = C n x y f :=
  (scalarModes_representable hw n x y).choose_spec f

/-- Actual bilinear mode data recovered from scalar coefficients. -/
noncomputable def recoveredModes {C : ScalarModes M₁ M₂ M₃}
    (hw : ScalarWeightCompatible A₁ A₂ A₃ C) : IntertwiningModes M₁ M₂ M₃ :=
  fun n => LinearMap.mk₂ ℂ (recoveredVector hw n)
    (fun x x' y => dual_ext fun f => by simp [recoveredVector_pairing])
    (fun c x y => dual_ext fun f => by simp [recoveredVector_pairing])
    (fun x y y' => dual_ext fun f => by simp [recoveredVector_pairing])
    (fun c x y => dual_ext fun f => by simp [recoveredVector_pairing])

@[simp] theorem recoveredModes_pairing {C : ScalarModes M₁ M₂ M₃}
    (hw : ScalarWeightCompatible A₁ A₂ A₃ C) (n : ℂ) (x : M₁) (y : M₂)
    (f : Module.Dual ℂ M₃) : f (recoveredModes hw n x y) = C n x y f :=
  recoveredVector_pairing hw n x y f

theorem recoveredModes_weightCompatible {C : ScalarModes M₁ M₂ M₃}
    (hw : ScalarWeightCompatible A₁ A₂ A₃ C) :
    WeightCompatible A₁ A₂ A₃ (recoveredModes hw) := by
  intro α β x y hx hy n
  obtain ⟨v, hv, he⟩ := exists_vector_of_supported_functional A₃
    (α + β - n - 1) (C n x y) (hw α β x y hx hy n)
  have eq : recoveredModes hw n x y = v :=
    dual_ext fun f => (recoveredModes_pairing hw n x y f).trans (he f).symm
  rwa [eq]

/-- Jacobi tested against scalar functionals. On the first term the target
mode is transferred to the test functional by ordinary precomposition.
This is a coefficient identity, with all integers and complex indices explicit. -/
def ScalarJacobi (A₁ : OrdVModule W M₁) (A₂ : OrdVModule W M₂)
    (A₃ : OrdVModule W M₃) (C : ScalarModes M₁ M₂ M₃) : Prop :=
  ∀ (a : V) (x : M₁) (y : M₂) (l m : ℤ) (n : ℂ) (f : Module.Dual ℂ M₃),
    (∑ᶠ i : ℤ, (negOnePow i * cbz l i) *
      (C (n + i) x y (f.comp (mode (A₃.YM a) (l + m - i))) -
        negOnePow l * C ((l : ℂ) + n - i) x (mode (A₂.YM a) (m + i) y) f)) =
      ∑ᶠ i : ℤ, cbz m i * C ((m : ℂ) + n - i) (mode (A₁.YM a) (l + i) x) y f

theorem recoveredModes_jacobi {C : ScalarModes M₁ M₂ M₃}
    (hw : ScalarWeightCompatible A₁ A₂ A₃ C) (hj : ScalarJacobi A₁ A₂ A₃ C) :
    ModeJacobi A₁ A₂ A₃ (recoveredModes hw) := by
  intro a x y l m n
  apply dual_ext
  intro f
  have htr := truncation_of_weightCompatible (recoveredModes_weightCompatible hw)
  rw [map_finsum f (IsIntertwiningOperator.jacL_support_finite htr a x y l m n),
    map_finsum f (IsIntertwiningOperator.jacR_support_finite
      (A₁ := A₁) (recoveredModes hw) a x y l m n)]
  have ht (k : ℤ) (q : ℂ) :
      f (mode (A₃.YM a) k (recoveredModes hw q x y)) =
        C q x y (f.comp (mode (A₃.YM a) k)) :=
    recoveredModes_pairing hw q x y (f.comp (mode (A₃.YM a) k))
  simpa only [IsIntertwiningOperator.jacL, IsIntertwiningOperator.jacR,
    map_smul, map_sub, smul_eq_mul, ht, recoveredModes_pairing] using hj a x y l m n f

/-- Scalar Jacobi plus weight support reconstructs a genuine FHL intertwiner,
including truncation and the derivative identity. -/
theorem isIntertwiningOperator_recoveredModes {C : ScalarModes M₁ M₂ M₃}
    (hw : ScalarWeightCompatible A₁ A₂ A₃ C) (hj : ScalarJacobi A₁ A₂ A₃ C) :
    IsIntertwiningOperator A₁ A₂ A₃ (recoveredModes hw) :=
  isIntertwiningOperator_of_weightCompatible_jacobi
    (recoveredModes_weightCompatible hw) (recoveredModes_jacobi hw hj)

/-- Pair the vector coefficients with arbitrary algebraic test functionals. -/
noncomputable def scalarize (Y : IntertwiningModes M₁ M₂ M₃) : ScalarModes M₁ M₂ M₃ :=
  fun n => (Y n).compr₂ (Module.Dual.eval ℂ M₃)

@[simp] theorem scalarize_apply (Y : IntertwiningModes M₁ M₂ M₃) (n : ℂ)
    (x : M₁) (y : M₂) (f : Module.Dual ℂ M₃) : scalarize Y n x y f = f (Y n x y) := rfl

theorem scalarize_weightCompatible {Y : IntertwiningModes M₁ M₂ M₃}
    (hY : IsIntertwiningOperator A₁ A₂ A₃ Y) :
    ScalarWeightCompatible A₁ A₂ A₃ (scalarize Y) := by
  intro α β x y hx hy n f
  simp only [scalarize_apply, LinearMap.comp_apply,
    weightProjection_of_mem A₃ (FusionTop.mem_weight hY hx hy n)]

theorem scalarize_jacobi {Y : IntertwiningModes M₁ M₂ M₃}
    (hY : IsIntertwiningOperator A₁ A₂ A₃ Y) : ScalarJacobi A₁ A₂ A₃ (scalarize Y) := by
  intro a x y l m n f
  have h := congrArg f (hY.jacobi a x y l m n)
  change f (∑ᶠ i : ℤ, IsIntertwiningOperator.jacL A₂ A₃ Y a x y l m n i) =
    f (∑ᶠ i : ℤ, IsIntertwiningOperator.jacR A₁ Y a x y l m n i) at h
  rw [map_finsum f (IsIntertwiningOperator.jacL_support_finite hY.truncation a x y l m n),
    map_finsum f (IsIntertwiningOperator.jacR_support_finite (A₁ := A₁) Y a x y l m n)] at h
  simpa only [scalarize_apply, LinearMap.comp_apply, IsIntertwiningOperator.jacL,
    IsIntertwiningOperator.jacR, map_smul, map_sub, smul_eq_mul] using h

/-- Coefficient reconstruction loses no information. -/
theorem recoveredModes_scalarize {Y : IntertwiningModes M₁ M₂ M₃}
    (hY : IsIntertwiningOperator A₁ A₂ A₃ Y) :
    recoveredModes (scalarize_weightCompatible hY) = Y := by
  funext n
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  exact dual_ext fun f => recoveredModes_pairing (scalarize_weightCompatible hY) n x y f

end VOA.Huang.LiFusion
