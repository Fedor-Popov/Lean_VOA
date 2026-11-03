/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.TannakianSymmetric
import Mathlib.CategoryTheory.Limits.FullSubcategory

/-!
# The trivial-twist part is a fusion category

For a ribbon fusion category `C` (T1) with ribbon structure `R`, write `TT R` for the full
subcategory of objects with `θ_X = 𝟙` (`Rep(V)_{h∈ℤ}` when `C = Rep V`).

* `trivialTwist_isClosedUnderLimitsOfShape` — closed under all limits (naturality of `θ`), hence
  `HasKernels (TT R)` and `HasFiniteBiproducts (TT R)`;
* given `[(trivialTwist R).IsMonoidal]`: right duals (`trivialTwist_dual`), `RightRigidCategory`,
  the simples `ttSimple i` (`T_i = 1`) are simple in `TT R` (`mono_hom_of_mono`), and
  `ttFusion : FusionCategory (TT R)`;
* `toScalar_tt`, `symDim_ttSimple` — scalars and braided dimensions agree with those of `C`;
* `tannakian_of_factorized` — **GR Prop. 2.17, conditional on `DeligneTannakian`**: from
  `S̃_ij = d_i d_j` on trivial-twist simples (plus `PseudoUnitaryData`, `SymDimAgrees`), the
  trivial-twist part is braided-equivalent, by a `ℂ`-linear functor, to `Rep(G)`, `G` finite.

No `sorry`, no new axioms.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace VOA.Huang.TensorCat

open CategoryTheory MonoidalCategory Limits Module

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C] [MonoidalCategory C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C] [RightRigidCategory C] [BraidedCategory C]
  [HasKernels C] [HasFiniteBiproducts C] [F : FusionCategory C] (R : RibbonStructure C)

instance trivialTwist_isClosedUnderLimitsOfShape (J : Type*) [Category J] :
    (trivialTwist R).IsClosedUnderLimitsOfShape J where
  limitsOfShape_le := by
    rintro X ⟨h⟩
    change (R.twist X).hom = 𝟙 X
    apply h.isLimit.hom_ext
    intro j
    have hn := R.twist_naturality (h.π.app j)
    have hj : (R.twist (h.diag.obj j)).hom = 𝟙 _ := h.prop_diag_obj j
    simp only [Category.id_comp]
    exact hn.symm.trans (by rw [hj, Category.comp_id])

/-- The trivial-twist part as a category. -/
abbrev TT := (trivialTwist R).FullSubcategory

instance : HasKernels (TT R) := by
  haveI : HasEqualizers C := Preadditive.hasEqualizers_of_hasKernels
  infer_instance

instance : HasFiniteBiproducts (TT R) := by
  haveI : HasFiniteProducts (TT R) := ⟨fun n => inferInstance⟩
  exact HasFiniteBiproducts.of_hasFiniteProducts

section Monoidal

variable [(trivialTwist R).IsMonoidal]

/-- Right duals in the trivial-twist part (closed under `ᘁ` by `trivialTwist_dual`). -/
instance (X : TT R) : HasRightDual X where
  rightDual := ⟨X.obj ᘁ, trivialTwist_dual R X.2⟩
  exact :=
    { coevaluation' := ObjectProperty.homMk (η_ X.obj X.objᘁ)
      evaluation' := ObjectProperty.homMk (ε_ X.obj X.objᘁ)
      coevaluation_evaluation' := by
        ext
        simp
      evaluation_coevaluation' := by
        ext
        simp }

instance : RightRigidCategory (TT R) where

/-- The simple objects of the trivial-twist part: the simples of `C` with `T_i = 1`. -/
def ttSimple (i : {i : F.ι // R.T i = 1}) : TT R :=
  ⟨F.simple i.1, (trivialTwist_simple_iff R i.1).mpr i.2⟩

theorem mono_hom_of_mono {X Y : TT R} (f : X ⟶ Y) [Mono f] : Mono f.hom := by
  haveI : HasEqualizers C := Preadditive.hasEqualizers_of_hasKernels
  have hK : trivialTwist R (kernel f.hom) :=
    (trivialTwist R).prop_limit (parallelPair f.hom 0) (by
      rintro (_ | _)
      · exact X.2
      · exact Y.2)
  let k : (⟨kernel f.hom, hK⟩ : TT R) ⟶ X := ObjectProperty.homMk (kernel.ι f.hom)
  have hk : k ≫ f = 0 := by
    ext
    simp [k]
  have hk0 : k = 0 := (cancel_mono f).mp (by rw [hk, zero_comp])
  have hι : kernel.ι f.hom = 0 := by
    have := congrArg (fun g => g.hom) hk0
    simpa [k] using this
  refine Preadditive.mono_of_cancel_zero _ fun g hg => ?_
  rw [← kernel.lift_ι f.hom g hg, hι, comp_zero]

instance (i : {i : F.ι // R.T i = 1}) : Simple (ttSimple R i) where
  mono_isIso_iff_nonzero {Y} f _ := by
    haveI : Mono f.hom := mono_hom_of_mono R f
    haveI : Simple (ttSimple R i).obj := F.isSimple i.1
    rw [← ObjectProperty.isIso_hom_iff]
    refine (Simple.mono_isIso_iff_nonzero f.hom).trans ?_
    constructor
    · intro h h0; apply h; rw [h0]; rfl
    · intro h h0; apply h; ext; exact h0

/-- `Hom` in the trivial-twist part embeds `ℂ`-linearly into `Hom` in `C`. -/
def ttHomLinear (X Y : TT R) : (X ⟶ Y) →ₗ[ℂ] (X.obj ⟶ Y.obj) where
  toFun f := f.hom
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

open Classical in
/-- **The trivial-twist part is a fusion category**, with simples the `X_i`, `T_i = 1`. -/
instance ttFusion : FusionCategory (TT R) where
  ι := {i : F.ι // R.T i = 1}
  simple := ttSimple R
  isSimple i := inferInstance
  unitLabel := ⟨F.unitLabel, R.T_unitLabel⟩
  unitIso := (trivialTwist R).isoMk F.unitIso
  inequivalent i j h := by
    obtain ⟨e⟩ := h
    exact Subtype.ext (F.inequivalent _ _ ⟨(trivialTwist R).ι.mapIso e⟩)
  semisimple X := by
    obtain ⟨n, f, ⟨e⟩⟩ := F.semisimple X.obj
    have hf : ∀ k, R.T (f k) = 1 := fun k =>
      (trivialTwist_iff R X.obj).mp X.2 _ _ (iota_comp_inv_ne_zero e k)
    let f' : Fin n → {i : F.ι // R.T i = 1} := fun k => ⟨f k, hf k⟩
    refine ⟨n, f', ⟨(trivialTwist R).isoMk (e ≪≫ ?_)⟩⟩
    exact ((trivialTwist R).ι.mapBiproduct fun k => ttSimple R (f' k)).symm
  finiteDimensional X Y := by
    haveI := F.finiteDimensional X.obj Y.obj
    exact FiniteDimensional.of_injective (ttHomLinear R X Y) fun f g h => ObjectProperty.hom_ext _ h

/-- Scalars of `End 𝟙` are the same in `C` and in the trivial-twist part. -/
theorem toScalar_tt (f : 𝟙_ (TT R) ⟶ 𝟙_ (TT R)) : toScalar f = toScalar f.hom := by
  have hC := F.finrank_end_unit
  have hT := (ttFusion R).finrank_end_unit
  have h1 : toScalar f.hom • 𝟙 (𝟙_ (TT R)) = f := by
    ext
    exact toScalar_smul_id hC f.hom
  conv_lhs => rw [← h1]
  rw [toScalar_smul hT]

/-- The braided dimension of a simple of the trivial-twist part is computed in `C`. -/
theorem symDim_ttSimple (i : {i : F.ι // R.T i = 1}) :
    symDim (ttSimple R i) = symDim (F.simple i.1) := by
  rw [symDim, toScalar_tt]
  rfl

end Monoidal

/-! ## GR Proposition 2.17, conditional on Deligne -/

variable {R}

/-- **GR Proposition 2.17 (pure tensor-category form), conditional on Deligne's theorem.**
Let `C` be a pseudo-unitary ribbon fusion category (`PseudoUnitaryData`) in which Turaev's
dimension formula holds at trivial twist (`SymDimAgrees`).  If `S̃_ij = d_i d_j` for all simples
with `T_i = T_j = 1`, then the trivial-twist part `C_{θ=1}` (`Rep(V)_{h∈ℤ}`) is a symmetric fusion
category (proved: `isMonoidal_trivialTwist_of_factorized`, `symmetricTrivialTwist_of_factorized`,
`ttFusion`) and, by Deligne, it is braided-equivalent to `Rep(G)` for a finite group `G`. -/
theorem tannakian_of_factorized (hDel : DeligneTannakian.{v, u}) (U : PseudoUnitaryData R)
    (hS : ∀ i j, R.T i = 1 → R.T j = 1 → R.sTilde i j = (U.d i : ℂ) * (U.d j : ℂ))
    (hsym : R.SymDimAgrees) :
    letI := isMonoidal_trivialTwist_of_factorized U hS
    letI := symmetricTrivialTwist_of_factorized U hS
    ∃ (G : Type) (_ : Group G) (_ : Fintype G) (Φ : TT R ⥤ FDRep ℂ G),
      Nonempty Φ.Braided ∧ Φ.Linear ℂ ∧ Φ.IsEquivalence := by
  letI := isMonoidal_trivialTwist_of_factorized U hS
  letI := symmetricTrivialTwist_of_factorized U hS
  refine hDel (TT R) fun i => ?_
  have h := symDim_ttSimple R i
  have h2 : symDim (F.simple i.1) = (U.d i.1 : ℂ) := by rw [hsym i.1 i.2, U.qdim_eq]
  change 0 < (symDim (ttSimple R i)).re
  rw [h, h2, Complex.ofReal_re]
  exact U.d_pos i.1

end VOA.Huang.TensorCat
