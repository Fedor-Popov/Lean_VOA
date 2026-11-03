/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.TannakianCategory
import Mathlib.CategoryTheory.Monoidal.Subcategory
import Mathlib.RepresentationTheory.FDRep

/-!
# The trivial-twist part is symmetric (GR Prop. 2.17, categorical half)

Let `C` be a ribbon fusion category (T1 sense) and `R` its ribbon structure.  The objects with
**trivial twist**, `θ_X = 𝟙` (for `C = Rep V`: the modules with integer conformal weights,
`Rep(V)_{h∈ℤ}`), form the property `trivialTwist R`.

* `RibbonStructure.twist_unit`, `T_unitLabel` — `θ_𝟙 = 𝟙`.
* `trivialTwist_iff` — `θ_X = 𝟙` **iff** every simple constituent of `X` has `T = 1`.
* `trivialTwist_dual` — closed under right duals (`θ_{Xᘁ} = (θ_X)ᘁ`).
* `doubleBraiding_eq_id_of_trivialTwist` — if every pair of trivial-twist *simples* has trivial
  double braiding, then so does every pair of trivial-twist *objects* (biproduct expansion).
* `isMonoidal_trivialTwist` — then `trivialTwist R` is closed under `⊗` (balancing).
* `symmetricTrivialTwist` — and the full subcategory is a **symmetric** monoidal category.
* `isMonoidal_trivialTwist_of_factorized`, `symmetricTrivialTwist_of_factorized` — **GR
  Proposition 2.17**, categorical form: in a pseudo-unitary ribbon fusion category with
  multiplicative dimensions, if `S̃_ij = d_i d_j` for all simples with `T_i = T_j = 1`, then the
  trivial-twist part is a symmetric monoidal subcategory (via `muger_simple`).

## Deligne's theorem, as a named `Prop`

* `symDim X = ε_X ∘ c_{X,Xᘁ} ∘ η_X` — the dimension of `X` computed with the braiding (the
  categorical dimension for the canonical pivotal structure of a symmetric category; in
  `Rep(G)` it is `dim V > 0`, in `sVec` the odd line has `symDim = -1`).
* `DeligneTannakian` — **Deligne (1990, 2002)**: a symmetric fusion category over `ℂ` in which
  every simple has positive `symDim` is braided-equivalent to `Rep(G)` for a finite group `G`.
  The positivity hypothesis is what excludes the super-Tannakian `Rep(G, z)` (`sVec`).
* `RibbonStructure.SymDimAgrees` — `symDim X_i = qdim X_i` whenever `T_i = 1`: true in every
  genuine ribbon category by Turaev's formula `dim X = ε c_{X,Xᘁ} (θ_X ⊗ 1) η` (convention
  independent at `θ_X = 1`); recorded as a hypothesis because the T1 `RibbonStructure` does not
  tie the pivotal structure to the braiding.

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

/-! ## §1  The twist of the unit -/

namespace RibbonStructure

variable (R : RibbonStructure C)

/-- `θ_𝟙 = 𝟙` (from the balancing axiom at `X = Y = 𝟙`). -/
theorem twist_unit : (R.twist (𝟙_ C)).hom = 𝟙 (𝟙_ C) := by
  have hb := R.balance (𝟙_ C) (𝟙_ C)
  rw [isTransparent_unit C (𝟙_ C), Category.comp_id] at hb
  have hn := R.twist_naturality (λ_ (𝟙_ C)).hom
  rw [hb] at hn
  -- `(θ ⊗ θ) ≫ λ = λ ≫ θ ≫ θ`
  have hlam : ((R.twist (𝟙_ C)).hom ⊗ₘ (R.twist (𝟙_ C)).hom) ≫ (λ_ (𝟙_ C)).hom =
      (λ_ (𝟙_ C)).hom ≫ (R.twist (𝟙_ C)).hom ≫ (R.twist (𝟙_ C)).hom := by
    rw [tensorHom_def, Category.assoc, leftUnitor_naturality, ← Category.assoc,
      unitors_equal, rightUnitor_naturality, Category.assoc]
  rw [hlam] at hn
  -- `λ ≫ θ = λ ≫ θ ≫ θ`, cancel `λ` and then `θ`
  have h1 := (cancel_epi (λ_ (𝟙_ C)).hom).mp hn
  have h2 : 𝟙 (𝟙_ C) ≫ (R.twist (𝟙_ C)).hom = (R.twist (𝟙_ C)).hom ≫ (R.twist (𝟙_ C)).hom := by
    rw [Category.id_comp]; exact h1
  exact ((cancel_mono (R.twist (𝟙_ C)).hom).mp h2).symm

variable [HasKernels C] [HasFiniteBiproducts C] [F : FusionCategory C]

/-- The twist of the unit label is `1`. -/
theorem T_unitLabel : R.T F.unitLabel = 1 := by
  have hn := R.twist_naturality F.unitIso.hom
  rw [twist_unit, Category.comp_id, ← R.T_spec, Linear.smul_comp, Category.id_comp] at hn
  have hne : F.unitIso.hom ≠ 0 := by
    intro h0
    haveI := F.isSimple F.unitLabel
    apply id_nonzero (F.simple F.unitLabel)
    rw [← F.unitIso.hom_inv_id, h0, zero_comp]
  have : (1 : ℂ) • F.unitIso.hom = R.T F.unitLabel • F.unitIso.hom := by rw [one_smul]; exact hn
  exact (smul_left_injective ℂ hne this).symm

end RibbonStructure

/-! ## §2  The trivial-twist part -/

variable [HasKernels C] [HasFiniteBiproducts C] [F : FusionCategory C] (R : RibbonStructure C)

/-- The objects with trivial twist (`Rep(V)_{h∈ℤ}` for `C = Rep V`). -/
def trivialTwist : ObjectProperty C := fun X => (R.twist X).hom = 𝟙 X

/-- `θ_X = 𝟙` iff every simple constituent `X_c ⟶ X` (nonzero) has `T_c = 1`. -/
theorem trivialTwist_iff (X : C) :
    trivialTwist R X ↔ ∀ c (φ : F.simple c ⟶ X), φ ≠ 0 → R.T c = 1 := by
  constructor
  · intro hX c φ hφ
    have hn := R.twist_naturality φ
    rw [show (R.twist X).hom = 𝟙 X from hX, Category.comp_id, ← R.T_spec, Linear.smul_comp,
      Category.id_comp] at hn
    have : (1 : ℂ) • φ = R.T c • φ := by rw [one_smul]; exact hn
    exact (smul_left_injective ℂ hφ this).symm
  · intro h
    obtain ⟨n, f, ⟨e⟩⟩ := F.semisimple X
    have := R.twist_eq_smul_of_iso e 1 fun k => h _ _ (iota_comp_inv_ne_zero e k)
    rw [one_smul] at this
    exact this

theorem trivialTwist_simple_iff (i : F.ι) : trivialTwist R (F.simple i) ↔ R.T i = 1 := by
  rw [trivialTwist, ← R.T_spec]
  constructor
  · intro h
    haveI := F.isSimple i
    have hid := id_nonzero (F.simple i)
    exact smul_left_injective ℂ hid (show R.T i • 𝟙 _ = (1 : ℂ) • 𝟙 _ by rw [one_smul]; exact h)
  · intro h; rw [h, one_smul]

theorem trivialTwist_unit : trivialTwist R (𝟙_ C) := R.twist_unit

/-- Closed under right duals. -/
theorem trivialTwist_dual {X : C} (hX : trivialTwist R X) : trivialTwist R Xᘁ := by
  change (R.twist Xᘁ).hom = 𝟙 Xᘁ
  rw [R.twist_dual, show (R.twist X).hom = 𝟙 X from hX, rightAdjointMate_id]

/-- The expansion `𝟙_{X ⊗ Y} = ∑_{k,l} (a_k ⊗ b_l) ≫ (a'_k ⊗ b'_l)` along decompositions of
`X` and `Y`. -/
theorem id_tensor_eq_sum {X Y : C} {J K : Type} [Fintype J] [Fintype K] {f : J → C} {g : K → C}
    (eX : X ≅ ⨁ f) (eY : Y ≅ ⨁ g) :
    𝟙 (X ⊗ Y) = ∑ k, ∑ l, ((eX.hom ≫ biproduct.π f k) ⊗ₘ (eY.hom ≫ biproduct.π g l)) ≫
      ((biproduct.ι f k ≫ eX.inv) ⊗ₘ (biproduct.ι g l ≫ eY.inv)) := by
  have hX : ∑ k, (eX.hom ≫ biproduct.π f k) ≫ (biproduct.ι f k ≫ eX.inv) = 𝟙 X := by
    simp only [Category.assoc, ← Preadditive.comp_sum]
    simp only [← Category.assoc, ← Preadditive.sum_comp, biproduct.total, Category.id_comp,
      Iso.hom_inv_id]
  have hY : ∑ l, (eY.hom ≫ biproduct.π g l) ≫ (biproduct.ι g l ≫ eY.inv) = 𝟙 Y := by
    simp only [Category.assoc, ← Preadditive.comp_sum]
    simp only [← Category.assoc, ← Preadditive.sum_comp, biproduct.total, Category.id_comp,
      Iso.hom_inv_id]
  rw [← id_tensorHom_id, ← hX, ← hY, sum_tensor]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [tensor_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [tensorHom_comp_tensorHom]

/-- Naturality of the double braiding. -/
theorem tensorHom_comp_doubleBraiding {X X' Y Y' : C} (f : X ⟶ X') (g : Y ⟶ Y') :
    (f ⊗ₘ g) ≫ (β_ X' Y').hom ≫ (β_ Y' X').hom = (β_ X Y).hom ≫ (β_ Y X).hom ≫ (f ⊗ₘ g) := by
  rw [BraidedCategory.braiding_naturality_assoc, BraidedCategory.braiding_naturality]

/-- If every pair of trivial-twist simples has trivial double braiding, so does every pair of
trivial-twist objects. -/
theorem doubleBraiding_eq_id_of_trivialTwist
    (H : ∀ i j, R.T i = 1 → R.T j = 1 →
      (β_ (F.simple i) (F.simple j)).hom ≫ (β_ (F.simple j) (F.simple i)).hom = 𝟙 _)
    {X Y : C} (hX : trivialTwist R X) (hY : trivialTwist R Y) :
    (β_ X Y).hom ≫ (β_ Y X).hom = 𝟙 (X ⊗ Y) := by
  obtain ⟨n, f, ⟨eX⟩⟩ := F.semisimple X
  obtain ⟨m, g, ⟨eY⟩⟩ := F.semisimple Y
  have hf : ∀ k, R.T (f k) = 1 := fun k =>
    (trivialTwist_iff R X).mp hX _ _ (iota_comp_inv_ne_zero eX k)
  have hg : ∀ l, R.T (g l) = 1 := fun l =>
    (trivialTwist_iff R Y).mp hY _ _ (iota_comp_inv_ne_zero eY l)
  conv_lhs => rw [← Category.id_comp ((β_ X Y).hom ≫ (β_ Y X).hom), id_tensor_eq_sum eX eY]
  conv_rhs => rw [id_tensor_eq_sum eX eY]
  simp only [Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  rw [Category.assoc, tensorHom_comp_doubleBraiding]
  erw [reassoc_of% (H _ _ (hf k) (hg l))]

/-- Under the same hypothesis, `trivialTwist R` is a monoidal property (closed under `⊗`,
contains `𝟙`). -/
theorem isMonoidal_trivialTwist
    (H : ∀ i j, R.T i = 1 → R.T j = 1 →
      (β_ (F.simple i) (F.simple j)).hom ≫ (β_ (F.simple j) (F.simple i)).hom = 𝟙 _) :
    (trivialTwist R).IsMonoidal where
  prop_unit := trivialTwist_unit R
  prop_tensor X Y hX hY := by
    change (R.twist (X ⊗ Y)).hom = 𝟙 (X ⊗ Y)
    rw [R.balance, show (R.twist X).hom = 𝟙 X from hX, show (R.twist Y).hom = 𝟙 Y from hY,
      id_tensorHom_id, Category.id_comp, doubleBraiding_eq_id_of_trivialTwist R H hX hY]

/-- The trivial-twist part is a **symmetric** monoidal category (braiding inherited from
`C`). -/
@[reducible] def symmetricTrivialTwist
    (H : ∀ i j, R.T i = 1 → R.T j = 1 →
      (β_ (F.simple i) (F.simple j)).hom ≫ (β_ (F.simple j) (F.simple i)).hom = 𝟙 _) :
    letI := isMonoidal_trivialTwist R H
    SymmetricCategory (trivialTwist R).FullSubcategory :=
  letI := isMonoidal_trivialTwist R H
  { toBraidedCategory := ObjectProperty.fullBraidedSubcategory (trivialTwist R)
    symmetry := fun X Y => ObjectProperty.hom_ext _
      (doubleBraiding_eq_id_of_trivialTwist R H X.2 Y.2) }

/-! ## §3  GR Proposition 2.17 (categorical half) -/

/-- **Pseudo-unitary data** for a ribbon fusion category: positive real quantum dimensions,
unimodular twists, and multiplicative dimensions on pairs of simples. -/
structure PseudoUnitaryData where
  d : F.ι → ℝ
  d_pos : ∀ c, 0 < d c
  qdim_eq : ∀ c, R.qdim (F.simple c) = d c
  norm_T : ∀ c, ‖R.T c‖ = 1
  qdim_tensor : ∀ i j, R.qdim (F.simple i ⊗ F.simple j) = (d i : ℂ) * (d j : ℂ)

variable {R}

/-- The factorization hypothesis on trivial-twist simples gives trivial double braiding. -/
theorem doubleBraiding_eq_id_of_factorized (U : PseudoUnitaryData R)
    (hS : ∀ i j, R.T i = 1 → R.T j = 1 → R.sTilde i j = (U.d i : ℂ) * (U.d j : ℂ)) :
    ∀ i j, R.T i = 1 → R.T j = 1 →
      (β_ (F.simple i) (F.simple j)).hom ≫ (β_ (F.simple j) (F.simple i)).hom = 𝟙 _ :=
  fun i j hi hj => (R.muger_simple U.d U.d_pos U.qdim_eq U.norm_T i j (U.qdim_tensor i j)).mp
    (hS i j hi hj)

/-- **GR Proposition 2.17 (categorical half).**  If `S̃_ij = d_i d_j` for all simples of
trivial twist, the trivial-twist part is closed under `⊗`. -/
theorem isMonoidal_trivialTwist_of_factorized (U : PseudoUnitaryData R)
    (hS : ∀ i j, R.T i = 1 → R.T j = 1 → R.sTilde i j = (U.d i : ℂ) * (U.d j : ℂ)) :
    (trivialTwist R).IsMonoidal :=
  isMonoidal_trivialTwist R (doubleBraiding_eq_id_of_factorized U hS)

/-- … and is a symmetric monoidal category. -/
@[reducible] def symmetricTrivialTwist_of_factorized (U : PseudoUnitaryData R)
    (hS : ∀ i j, R.T i = 1 → R.T j = 1 → R.sTilde i j = (U.d i : ℂ) * (U.d j : ℂ)) :
    letI := isMonoidal_trivialTwist_of_factorized U hS
    SymmetricCategory (trivialTwist R).FullSubcategory :=
  symmetricTrivialTwist R (doubleBraiding_eq_id_of_factorized U hS)

/-! ## §4  Deligne's theorem, as a named `Prop` -/

section Deligne

variable {C₀ : Type u} [Category.{v} C₀] [MonoidalCategory C₀] [BraidedCategory C₀]
  [Preadditive C₀] [Linear ℂ C₀] [RightRigidCategory C₀]

/-- The **braided dimension** `symDim X = ε_X ∘ c_{X,Xᘁ} ∘ η_X ∈ End 𝟙 = ℂ`.  In a symmetric
category it is the categorical dimension for the canonical (Drinfeld) pivotal structure: in
`Rep(G)` it is `dim V`, in `sVec` the odd line has `symDim = -1`. -/
def symDim (X : C₀) : ℂ := toScalar (η_ X Xᘁ ≫ (β_ X Xᘁ).hom ≫ ε_ X Xᘁ)

end Deligne

/-- **Deligne's theorem** (P. Deligne, *Catégories tannakiennes* (1990) and *Catégories
tensorielles* (2002); in the fusion case, EGNO *Tensor categories* §9.9), in the form used by
GR Prop. 2.17 / 2.11: a symmetric fusion category over `ℂ` all of whose simple objects have
positive braided dimension is braided-equivalent, by a `ℂ`-linear functor, to `Rep(G)` for a finite
group `G`.

*True and faithful.*  Deligne: every symmetric fusion category over `ℂ` is braided-equivalent to
`Rep(G, z)` for a finite group `G` and a central `z` with `z² = 1`; in `Rep(G, z)` a simple `V` has
`symDim V = ±dim V`, the sign being the scalar by which `z` acts.  Positivity forces `z = 1`, and
`Rep(G, 1) = Rep(G)` with its standard symmetric structure (`FDRep ℂ G`).  The positivity
hypothesis is necessary (`sVec`).  `FusionCategory` (T1) is semisimple with finitely many simples
and `End 𝟙 = ℂ`, hence abelian; right duals plus the braiding give two-sided rigidity.

*Not proved here.*  This is the deepest pure-category input of the Tannakian
argument. -/
def DeligneTannakian : Prop :=
  ∀ (D : Type u) [Category.{v} D] [Preadditive D] [Linear ℂ D] [MonoidalCategory D]
    [MonoidalPreadditive D] [MonoidalLinear ℂ D] [HasKernels D] [HasFiniteBiproducts D]
    [RightRigidCategory D] [SymmetricCategory D] [F : FusionCategory D],
    (∀ i, 0 < (symDim (F.simple i)).re) →
    ∃ (G : Type) (_ : Group G) (_ : Fintype G) (Φ : D ⥤ FDRep ℂ G),
      Nonempty Φ.Braided ∧ Φ.Linear ℂ ∧ Φ.IsEquivalence

namespace RibbonStructure

/-- **Turaev's dimension formula at trivial twist**: `symDim X_i = qdim X_i` whenever `T_i = 1`.
In a genuine ribbon category `qdim X = ε_X c_{X,Xᘁ} (θ_X ⊗ 1) η_X` (Turaev, *Quantum invariants*,
I.1); at `θ_X = 1` the formula does not depend on the orientation conventions (the double braiding
acts trivially on the image of `η_X` there).  Recorded as a hypothesis because the T1
`RibbonStructure` does not tie the pivotal structure to the braiding and twist. -/
def SymDimAgrees (R : RibbonStructure C) : Prop :=
  ∀ i, R.T i = 1 → symDim (F.simple i) = R.qdim (F.simple i)

end RibbonStructure

end VOA.Huang.TensorCat
