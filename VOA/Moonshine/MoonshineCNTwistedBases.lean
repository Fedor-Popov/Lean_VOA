import VOA.Moonshine.MoonshineCNTwistedPBW
import VOA.Moonshine.MoonshineCNBorcherdsStringSum
import VOA.Moonshine.MoonshineCNBorcherdsGeneratorWeights
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.LinearAlgebra.Semisimple
import Mathlib.LinearAlgebra.Trace
import Mathlib.FieldTheory.Separable
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Eigenbases and homogeneous bases for the positive part

* A finite-order endomorphism of a finite-dimensional complex space has a basis of eigenvectors
  (`exists_eigenbasis_of_pow_eq_one`), and the trace of its powers is the corresponding power sum
  of eigenvalues (`trace_pow_eq_sum_of_eigenbasis`).
* For Borcherds data with bases `b γ` of the root spaces, the positive part `𝔲⁺` has the basis
  `positiveBasis` (the `b γ` for `γ` in the positive cone) and the generating space `U` has the
  basis `generatorBasis` (the real-root strings `(ad e)^k (b (1, j))`, `k < j`).  Both consist of
  homogeneous vectors, and of eigenvectors of every symmetry for which the `b γ` are eigenbases.
* `weightTorus χ` multiplies the root space `γ` by `χ γ`; for multiplicative `χ` it is a Lie algebra
  endomorphism, restricting to `positiveTorus χ` on `𝔲⁺`.  These record the bidegree.
-/

noncomputable section

namespace VOA.Moonshine.ConwayNorton

open Module

/-! ### Eigenbases of finite-order endomorphisms -/

universe u

theorem exists_eigenbasis_of_pow_eq_one {V : Type u} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (T : Module.End ℂ V) {N : ℕ} (hN : 0 < N) (hT : T ^ N = 1) :
    ∃ (ι : Type u) (_ : Fintype ι) (b : Basis ι ℂ V) (μ : ι → ℂ), ∀ i, T (b i) = μ i • b i := by
  classical
  have hsq : Squarefree (Polynomial.X ^ N - Polynomial.C (1 : ℂ)) :=
    (Polynomial.separable_X_pow_sub_C 1 (by exact_mod_cast hN.ne') one_ne_zero).squarefree
  have hzero : Polynomial.aeval T (Polynomial.X ^ N - Polynomial.C (1 : ℂ)) = 0 := by
    simp [hT]
  have hss : T.IsSemisimple := Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsq hzero
  have hint : DirectSum.IsInternal (fun μ : ℂ => T.eigenspace μ) :=
    (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mpr
      ⟨T.eigenspaces_iSupIndep, hss.iSup_eigenspace_eq_top⟩
  let b := hint.collectedBasis fun μ => Basis.ofVectorSpace ℂ (T.eigenspace μ)
  haveI : Finite (Σ μ : ℂ, Basis.ofVectorSpaceIndex ℂ (T.eigenspace μ)) :=
    Module.Finite.finite_basis b
  refine ⟨_, Fintype.ofFinite _, b, fun x => x.1, fun x => ?_⟩
  exact Module.End.mem_eigenspace_iff.mp (hint.collectedBasis_mem _ x)

theorem trace_pow_eq_sum_of_eigenbasis {V : Type*} [AddCommGroup V] [Module ℂ V]
    {ι : Type*} [Fintype ι] (b : Basis ι ℂ V) (T : Module.End ℂ V) (μ : ι → ℂ)
    (h : ∀ i, T (b i) = μ i • b i) (k : ℕ) :
    LinearMap.trace ℂ V (T ^ k) = ∑ i, μ i ^ k := by
  classical
  have hk : ∀ i, (T ^ k) (b i) = μ i ^ k • b i := by
    intro i
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', Module.End.mul_apply, ih, map_smul, h, smul_smul, pow_succ]
  rw [LinearMap.trace_eq_matrix_trace ℂ b, Matrix.trace]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply, hk, map_smul, Basis.repr_self,
    Finsupp.smul_single, Finsupp.single_eq_same, smul_eq_mul, mul_one]

/-! ### Internal sums of subspaces of a subspace -/

theorem isInternal_comap_subtype {M : Type*} [AddCommGroup M] [Module ℂ M] {κ : Type*}
    [DecidableEq κ] (V : Submodule ℂ M) (p : κ → Submodule ℂ M) (hind : iSupIndep p)
    (hle : ∀ s, p s ≤ V) (hsup : ⨆ s, p s = V) :
    DirectSum.IsInternal (fun s => (p s).comap V.subtype) := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  constructor
  · rw [iSupIndep_def] at hind ⊢
    intro s
    have hs := hind s
    rw [Submodule.disjoint_def] at hs ⊢
    intro x hx hx'
    have h1 : (x : M) ∈ ⨆ (j) (_ : j ≠ s), p j := by
      have h2 := Submodule.mem_map_of_mem (f := V.subtype) hx'
      have hle2 : Submodule.map V.subtype (⨆ (j) (_ : j ≠ s), (p j).comap V.subtype) ≤
          ⨆ (j) (_ : j ≠ s), p j := by
        rw [Submodule.map_iSup]
        refine iSup_mono fun j => ?_
        rw [Submodule.map_iSup]
        exact iSup_mono fun _ => Submodule.map_comap_le _ _
      exact hle2 h2
    exact Subtype.ext (hs x hx h1)
  · apply Submodule.map_injective_of_injective V.injective_subtype
    rw [Submodule.map_iSup, Submodule.map_top, Submodule.range_subtype]
    simp only [Submodule.map_comap_subtype]
    rw [iSup_congr fun s => inf_eq_right.mpr (hle s)]
    exact hsup

/-- Decidable equality of the real-root string positions. -/
noncomputable instance borcherdsStringIndex_decidableEq : DecidableEq borcherdsStringIndex :=
  Classical.decEq _

namespace BorcherdsData

variable {g : Type*} [LieRing g] [LieAlgebra ℂ g] (D : BorcherdsData g)

/-! ### The torus -/

/-- Decomposition of `g` into its root spaces. -/
def weightDecompose : g ≃ₗ[ℂ] DirectSum (ℤ × ℤ) fun γ => D.weightSpace γ :=
  (LinearEquiv.ofBijective (DirectSum.coeLinearMap D.weightSpace) D.weight_internal).symm

theorem weightDecompose_of_mem {γ : ℤ × ℤ} {x : g} (hx : x ∈ D.weightSpace γ) :
    D.weightDecompose x = DFinsupp.single γ (⟨x, hx⟩ : D.weightSpace γ) := by
  rw [weightDecompose, LinearEquiv.symm_apply_eq, LinearEquiv.ofBijective_apply]
  exact (DirectSum.coeLinearMap_of (fun γ => D.weightSpace γ) γ ⟨x, hx⟩).symm

/-- Multiplication by `χ γ` on the root space `γ`. -/
def weightTorus (χ : ℤ × ℤ → ℂ) : g →ₗ[ℂ] g :=
  DirectSum.coeLinearMap D.weightSpace ∘ₗ
    DFinsupp.mapRange.linearMap (fun γ => χ γ • LinearMap.id) ∘ₗ D.weightDecompose.toLinearMap

theorem weightTorus_of_mem (χ : ℤ × ℤ → ℂ) {γ : ℤ × ℤ} {x : g} (hx : x ∈ D.weightSpace γ) :
    D.weightTorus χ x = χ γ • x := by
  change DirectSum.coeLinearMap D.weightSpace
    (DFinsupp.mapRange.linearMap (fun γ => χ γ • LinearMap.id) (D.weightDecompose x)) = χ γ • x
  rw [D.weightDecompose_of_mem hx, DFinsupp.mapRange.linearMap_apply, DFinsupp.mapRange_single]
  exact (DirectSum.coeLinearMap_of (fun γ => D.weightSpace γ) γ _).trans rfl

theorem mem_weightSpace_iSup (x : g) : x ∈ ⨆ γ, D.weightSpace γ := by
  rw [D.weight_internal.submodule_iSup_eq_top]
  trivial

/-- For multiplicative `χ` the torus is a Lie algebra endomorphism. -/
theorem weightTorus_lie (χ : ℤ × ℤ → ℂ) (hχ : ∀ γ δ, χ (γ + δ) = χ γ * χ δ) (x y : g) :
    D.weightTorus χ ⁅x, y⁆ = ⁅D.weightTorus χ x, D.weightTorus χ y⁆ := by
  have hx := D.mem_weightSpace_iSup x
  have hy := D.mem_weightSpace_iSup y
  induction hx using Submodule.iSup_induction' with
  | mem γ x hx =>
      induction hy using Submodule.iSup_induction' with
      | mem δ y hy =>
          rw [D.weightTorus_of_mem χ (D.bracket_weight hx hy), D.weightTorus_of_mem χ hx,
            D.weightTorus_of_mem χ hy, hχ, smul_lie, lie_smul, smul_smul]
      | zero => simp
      | add y z _ _ h1 h2 => simp only [lie_add, map_add, h1, h2]
  | zero => simp
  | add x z _ _ h1 h2 => simp only [add_lie, map_add, h1, h2]

theorem weightTorus_mem_weightSpan (χ : ℤ × ℤ → ℂ) (P : ℤ × ℤ → Prop) {x : g}
    (hx : x ∈ D.weightSpan P) : D.weightTorus χ x ∈ D.weightSpan P := by
  induction hx using Submodule.iSup_induction' with
  | mem γ x hx =>
      induction hx using Submodule.iSup_induction' with
      | mem hγ x hx =>
          rw [D.weightTorus_of_mem χ hx]
          exact D.weightSpace_le_weightSpan hγ (Submodule.smul_mem _ _ hx)
      | zero => simp
      | add x y _ _ hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
  | zero => simp
  | add x y _ _ hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy

/-- The torus restricted to the positive part. -/
def positiveTorus (χ : ℤ × ℤ → ℂ) (hχ : ∀ γ δ, χ (γ + δ) = χ γ * χ δ) :
    D.positivePart →ₗ⁅ℂ⁆ D.positivePart where
  toLinearMap := (D.weightTorus χ).restrict (p := D.positivePart.toSubmodule)
    (q := D.positivePart.toSubmodule) fun _ hx => D.weightTorus_mem_weightSpan χ _ hx
  map_lie' {x y} := Subtype.ext (D.weightTorus_lie χ hχ x y)

theorem positiveTorus_coe (χ : ℤ × ℤ → ℂ) (hχ : ∀ γ δ, χ (γ + δ) = χ γ * χ δ)
    (x : D.positivePart) : ((D.positiveTorus χ hχ x : D.positivePart) : g) = D.weightTorus χ x :=
  rfl

theorem weightTorus_genSpace (χ : ℤ × ℤ → ℂ) (e : g) (he : e ∈ D.weightSpace borcherdsRealRoot)
    {u : g} (hu : u ∈ D.genSpace e) : D.weightTorus χ u ∈ D.genSpace e := by
  rw [D.genSpace_eq_iSup_strings] at hu ⊢
  induction hu using Submodule.iSup_induction' with
  | mem s u hu =>
      rw [D.weightTorus_of_mem χ (D.generatorString_le_weight e he _ _ hu)]
      exact Submodule.mem_iSup_of_mem s (Submodule.smul_mem _ _ hu)
  | zero => simp
  | add x y _ _ hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy

/-! ### Homogeneous bases -/

variable (ι : ℤ × ℤ → Type*) (b : ∀ γ, Basis (ι γ) ℂ (D.weightSpace γ))

theorem positiveWeight_isInternal :
    DirectSum.IsInternal (fun γ : {γ : ℤ × ℤ // borcherdsPositiveCone γ} =>
      (D.weightSpace γ.1).comap D.positivePart.toSubmodule.subtype) :=
  isInternal_comap_subtype D.positivePart.toSubmodule
    (fun γ : {γ : ℤ × ℤ // borcherdsPositiveCone γ} => D.weightSpace γ.1)
    (D.weight_internal.submodule_iSupIndep.comp Subtype.val_injective)
    (fun γ => D.weightSpace_le_weightSpan γ.2) (by
      change _ = D.weightSpan borcherdsPositiveCone
      rw [weightSpan, iSup_subtype'])

/-- The basis of `𝔲⁺` formed by the bases of the positive root spaces. -/
def positiveBasis :
    Basis (Σ γ : {γ : ℤ × ℤ // borcherdsPositiveCone γ}, ι γ.1) ℂ D.positivePart :=
  (D.positiveWeight_isInternal).collectedBasis fun γ =>
    (b γ.1).map (Submodule.comapSubtypeEquivOfLe (D.weightSpace_le_weightSpan γ.2)).symm

theorem positiveBasis_coe (x : Σ γ : {γ : ℤ × ℤ // borcherdsPositiveCone γ}, ι γ.1) :
    ((D.positiveBasis ι b x : D.positivePart) : g) = (b x.1.1 x.2 : g) := by
  simp [positiveBasis]
  rfl

theorem positiveBasis_mem (x : Σ γ : {γ : ℤ × ℤ // borcherdsPositiveCone γ}, ι γ.1) :
    ((D.positiveBasis ι b x : D.positivePart) : g) ∈ D.weightSpace x.1.1 := by
  rw [positiveBasis_coe]
  exact (b x.1.1 x.2).2

variable (e : g) (he : e ∈ D.weightSpace borcherdsRealRoot)

include he in
theorem generatorStrings_isInternal :
    DirectSum.IsInternal (fun s : borcherdsStringIndex =>
      (D.generatorString e s.val.1 s.val.2).comap (D.genSpace e).subtype) :=
  isInternal_comap_subtype (κ := borcherdsStringIndex) (D.genSpace e)
    (fun s => D.generatorString e s.val.1 s.val.2)
    (D.generatorStrings_independent e he)
    (fun s => D.generatorString_le_genSpace e _ s.2.1 _ s.2.2)
    (D.genSpace_eq_iSup_strings e).symm

variable (f : g) (hf : f ∈ D.weightSpace (-borcherdsRealRoot)) (hef : D.form e f = 1)

/-- The basis of `U` formed by the real-root strings `(ad e)^k (b (1, j) i)`, `k < j`. -/
def generatorBasis :
    Basis (Σ s : borcherdsStringIndex, ι (borcherdsImaginaryRoot s.val.1)) ℂ
      (D.positiveGeneratorSpace e) :=
  ((D.generatorStrings_isInternal e he).collectedBasis fun s =>
    ((b _).map (D.generatorStringEquiv e f he hf hef s.val.1 s.2.1 s.val.2 s.2.2)).map
      (Submodule.comapSubtypeEquivOfLe
        (D.generatorString_le_genSpace e _ s.2.1 _ s.2.2)).symm).map
    (Submodule.comapSubtypeEquivOfLe (q := D.positivePart.toSubmodule)
      (D.genSpace_le_positive e he)).symm

theorem generatorBasis_coe (x : Σ s : borcherdsStringIndex, ι (borcherdsImaginaryRoot s.val.1)) :
    (((D.generatorBasis ι b e he f hf hef x : D.positiveGeneratorSpace e) : D.positivePart) : g) =
      (LieModule.toEnd ℂ g g e ^ x.1.val.2) (b _ x.2 : g) := by
  simp [generatorBasis]
  rfl

theorem generatorBasis_mem (x : Σ s : borcherdsStringIndex, ι (borcherdsImaginaryRoot s.val.1)) :
    (((D.generatorBasis ι b e he f hf hef x : D.positiveGeneratorSpace e) : D.positivePart) : g) ∈
      D.weightSpace (borcherdsStringDegree x.1) := by
  rw [generatorBasis_coe]
  exact D.adReal_pow_mem e he _ _ (b _ x.2).2 _

/-! ### Symmetries diagonal in the bases -/

theorem positiveTorus_positiveBasis (χ : ℤ × ℤ → ℂ) (hχ : ∀ γ δ, χ (γ + δ) = χ γ * χ δ)
    (x : Σ γ : {γ : ℤ × ℤ // borcherdsPositiveCone γ}, ι γ.1) :
    D.positiveTorus χ hχ (D.positiveBasis ι b x) = χ x.1.1 • D.positiveBasis ι b x :=
  Subtype.ext (D.weightTorus_of_mem χ (D.positiveBasis_mem ι b x))

theorem positiveTorus_generatorBasis (χ : ℤ × ℤ → ℂ) (hχ : ∀ γ δ, χ (γ + δ) = χ γ * χ δ)
    (x : Σ s : borcherdsStringIndex, ι (borcherdsImaginaryRoot s.val.1)) :
    D.positiveTorus χ hχ (D.generatorBasis ι b e he f hf hef x : D.positivePart) =
      χ (borcherdsStringDegree x.1) • (D.generatorBasis ι b e he f hf hef x : D.positivePart) :=
  Subtype.ext (D.weightTorus_of_mem χ (D.generatorBasis_mem ι b e he f hf hef x))

include he in
theorem positiveTorus_generator_mem (χ : ℤ × ℤ → ℂ) (hχ : ∀ γ δ, χ (γ + δ) = χ γ * χ δ) :
    ∀ u ∈ D.positiveGeneratorSpace e, D.positiveTorus χ hχ u ∈ D.positiveGeneratorSpace e :=
  fun _ hu => D.weightTorus_genSpace χ e he hu

section Action

variable {G : Type*} [Group G] (A : D.GAction G)

/-- A symmetry on one root space. -/
def weightAction (σ : G) (γ : ℤ × ℤ) : Module.End ℂ (D.weightSpace γ) :=
  (A.action σ).toLinearMap.restrict fun x hx => A.graded σ γ x hx

theorem weightAction_pow (σ : G) (γ : ℤ × ℤ) (k : ℕ) :
    D.weightAction A (σ ^ k) γ = D.weightAction A σ γ ^ k := by
  induction k with
  | zero =>
      ext x
      simp [weightAction]
  | succ k ih =>
      rw [pow_succ, pow_succ, ← ih]
      ext x
      simp [weightAction, map_mul]

variable (μ : ∀ γ, ι γ → ℂ)

/-- The positive part of a symmetry is diagonal in `positiveBasis` when the `b γ` are
eigenbases. -/
theorem positivePartAction_positiveBasis (σ : G)
    (hb : ∀ γ i, D.weightAction A σ γ (b γ i) = μ γ i • b γ i)
    (x : Σ γ : {γ : ℤ × ℤ // borcherdsPositiveCone γ}, ι γ.1) :
    D.positivePartAction A σ (D.positiveBasis ι b x) = μ x.1.1 x.2 • D.positiveBasis ι b x := by
  apply Subtype.ext
  change A.action σ ((D.positiveBasis ι b x : D.positivePart) : g) =
    μ x.1.1 x.2 • ((D.positiveBasis ι b x : D.positivePart) : g)
  rw [D.positiveBasis_coe ι b x]
  exact congrArg Subtype.val (hb x.1.1 x.2)

theorem positivePartAction_generatorBasis (σ : G)
    (hb : ∀ γ i, D.weightAction A σ γ (b γ i) = μ γ i • b γ i)
    (x : Σ s : borcherdsStringIndex, ι (borcherdsImaginaryRoot s.val.1)) :
    D.positivePartAction A σ (D.generatorBasis ι b e he f hf hef x : D.positivePart) =
      μ _ x.2 • (D.generatorBasis ι b e he f hf hef x : D.positivePart) := by
  apply Subtype.ext
  change A.action σ (((D.generatorBasis ι b e he f hf hef x : D.positiveGeneratorSpace e) :
    D.positivePart) : g) = μ _ x.2 • (((D.generatorBasis ι b e he f hf hef x :
      D.positiveGeneratorSpace e) : D.positivePart) : g)
  rw [D.generatorBasis_coe ι b e he f hf hef x, D.generatorStringMap_equivariant A σ e he,
    show A.action σ (b _ x.2 : g) = μ _ x.2 • (b _ x.2 : g) from
      congrArg Subtype.val (hb _ x.2), map_smul]

end Action

end BorcherdsData

end VOA.Moonshine.ConwayNorton
