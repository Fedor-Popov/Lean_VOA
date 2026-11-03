/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Monoidal.Linear
import Mathlib.CategoryTheory.Preadditive.Schur
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.Algebra.Group.AddChar
import VOA.Huang.LatticeFusion
import VOA.Classification.COne.RankOneTheta

/-!
# Tensor-category foundations for Huang's theorem

## §1  Abstract definitions, on Mathlib's monoidal-category library

Mathlib v4.30 has `MonoidalCategory`, `BraidedCategory`, `SymmetricCategory`,
`MonoidalPreadditive`, `MonoidalLinear`, right/left duals (`HasRightDual`, `ExactPairing`,
`RightRigidCategory`, `RigidCategory`), simple objects and Schur's lemma.  It has **no** pivotal,
spherical, ribbon, fusion or modular notion, and no dual-of-a-tensor-product isomorphism
`(X ⊗ Y)ᘁ ≅ Yᘁ ⊗ Xᘁ`.  We add, over a `ℂ`-linear monoidal category with right duals:

* `FusionCategory` — finitely many pairwise non-isomorphic simples `simple i`, one of them `≅ 𝟙`,
  every object a finite biproduct of simples, finite-dimensional `Hom`s;
  `FusionCategory.finrank_end_unit : finrank ℂ (𝟙 ⟶ 𝟙) = 1` (`End 𝟙 = ℂ`) is **derived** (Schur).
* `toScalar : (𝟙 ⟶ 𝟙) → ℂ`, with `toScalar_smul_id`, `toScalar_smul`.
* `PivotalStructure` — a natural isomorphism `X ≅ Xᘁᘁ`; `PivotalStructure.trL/trR` (left/right
  pivotal traces), `qdim`, `IsSpherical`.  **Deferred:** the monoidality axiom
  `piv_{X⊗Y} = piv_X ⊗ piv_Y` (modulo `(X⊗Y)ᘁᘁ ≅ Xᘁᘁ ⊗ Yᘁᘁ`) is *not* imposed, because Mathlib
  lacks the canonical iso `(X ⊗ Y)ᘁ ≅ Yᘁ ⊗ Xᘁ`; the traces below do not need it.
* `RibbonStructure` — pivotal + a natural twist `θ` with the balancing axiom
  `θ_{X⊗Y} = (θ_X ⊗ θ_Y) ≫ c_{X,Y} ≫ c_{Y,X}` and `θ_{Xᘁ} = (θ_X)ᘁ`.
* `RibbonStructure.sTilde i j = tr(c_{j,i} ∘ c_{i,j})`, `RibbonStructure.T i` (`θ_{X_i} = T_i • 𝟙`),
  `FusionCategory.N i j k = dim Hom(X_k, X_i ⊗ X_j)`, `RibbonStructure.IsModular` (`det S̃ ≠ 0`).
* `IsTransparent X` (`c_{Y,X} ∘ c_{X,Y} = 𝟙` for all `Y`) and `mugerCentralizer`; the unit is
  transparent (`isTransparent_unit`) and transparency is closed under `⊗`
  (`IsTransparent.tensor`, from the hexagon axioms).

## §2  Modular data as finite data: `ModularDatum`

Labels, vacuum, `N`, `S`, `T`, `d`, `S₀₀`, with the predicates `Verlinde`, `IsUnitary`,
`IsSymmetric` and `Factorized a` (`S_ab = S₀₀ d_a d_b ∀ b` — exactly the hypothesis shape of
`ITannakian`).

## §3  The pointed braided fusion category `C(A, q)`

For a finite abelian group `A` with a quadratic form `q : A → U(1)` (`PreMetricGroup`; bicharacter
`b(a,c) = q(a+c)/(q(a)q(c))`), `pointedDatum` is its modular data: `N_{ab}^c = [c = a + b]`,
`S_ab = |A|^{-1/2} conj b(a,b)`, `T_a = q(a)`, `d_a = 1`.  Proved:
* `PreMetricGroup.sum_bil` — the character sum `∑_x b(y,x) = |A| [b(y,·) ≡ 1]`;
* `pointedDatum_verlinde` — the Verlinde formula, for nondegenerate `b`;
* `pointedDatum_isUnitary_iff` — `S` is unitary **iff** `b` is nondegenerate (modularity);
* `pointedDatum_factorized_iff` — **Müger's criterion**: `b(a,·) ≡ 1 ⟺ S_ab = S₀₀ d_a d_b ∀ b`;
* `bil_self` (`b(a,a) = q(a)²`), `pointedDatum_isSymmetric`, `pointedDatum_T_vac`.
The braided monoidal category `C(A, q)` itself (`A`-graded vector spaces with the abelian 3-cocycle
`(ω, c)` attached to `q`) is **not** constructed here; only its modular data are.

## §4  `A = ℤ/2m`, `q(j) = e^{πi j²/2m}`: the modular data of `V_{2m}`

`latticePMG m`, with `latticePMG_bil : b(j,k) = e^{2πi jk/2m}`, `latticePMG_nondegenerate`, and
* `latticeDatum_N_eq_fusionRule` — `N_{jk}^l = fusionRule (V_{L+λ_j}) (V_{L+λ_k}) (V_{L+λ_l})`
  (via `fusionRule_latticeModule`);
* `latticeTheta_T` — `θ_j(τ+1) = T_j θ_j(τ)`, `T_j = q(j) = e^{2πi h_j}`, `h_j = j²/4m`;
* `latticeTheta_S` — `θ_j(−1/τ) = (−iτ)^{1/2} ∑_k S_{jk} θ_k(τ)`, where
  `θ_j = θ_{j,2m,1/4m} = ∑_{n ≡ j (2m)} q^{n²/4m}` is the numerator of the character
  `ch_j = θ_j/η` of `V_{L+λ_j}`, so (with `η(−1/τ) = (−iτ)^{1/2} η(τ)`) `S` is the character
  `S`-matrix.

No `sorry`, no new axioms.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace VOA.Huang.TensorCat

open CategoryTheory MonoidalCategory Limits Module

universe v u

/-! ## §1  Abstract definitions -/

section Abstract

variable (C : Type u) [Category.{v} C] [Preadditive C] [Linear ℂ C] [MonoidalCategory C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C]

/-- The scalar of an endomorphism of the unit, when `End 𝟙` is one-dimensional: the `c` with
`f = c • 𝟙`. (Junk value `0` if no such `c` exists.) -/
def toScalar {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C] [MonoidalCategory C]
    (f : 𝟙_ C ⟶ 𝟙_ C) : ℂ :=
  open Classical in if h : ∃ c : ℂ, c • 𝟙 (𝟙_ C) = f then h.choose else 0

variable {C}

theorem toScalar_smul_id (h : finrank ℂ (𝟙_ C ⟶ 𝟙_ C) = 1) (f : 𝟙_ C ⟶ 𝟙_ C) :
    toScalar f • 𝟙 (𝟙_ C) = f := by
  have hid : 𝟙 (𝟙_ C) ≠ 0 := by
    intro h0
    have : ∀ g : 𝟙_ C ⟶ 𝟙_ C, g = 0 := fun g => by rw [← Category.id_comp g, h0, zero_comp]
    haveI : Subsingleton (𝟙_ C ⟶ 𝟙_ C) := ⟨fun a b => by rw [this a, this b]⟩
    rw [finrank_zero_of_subsingleton] at h
    exact zero_ne_one h
  have hex : ∃ c : ℂ, c • 𝟙 (𝟙_ C) = f := (finrank_eq_one_iff_of_nonzero' _ hid).mp h f
  rw [toScalar, dif_pos hex]
  exact hex.choose_spec

theorem toScalar_smul (h : finrank ℂ (𝟙_ C ⟶ 𝟙_ C) = 1) (c : ℂ) :
    toScalar (c • 𝟙 (𝟙_ C)) = c := by
  have hid : 𝟙 (𝟙_ C) ≠ 0 := by
    intro h0
    have : ∀ g : 𝟙_ C ⟶ 𝟙_ C, g = 0 := fun g => by rw [← Category.id_comp g, h0, zero_comp]
    haveI : Subsingleton (𝟙_ C ⟶ 𝟙_ C) := ⟨fun a b => by rw [this a, this b]⟩
    rw [finrank_zero_of_subsingleton] at h
    exact zero_ne_one h
  have h1 := toScalar_smul_id h (c • 𝟙 (𝟙_ C))
  exact smul_left_injective ℂ hid h1

variable (C)

/-- **Fusion category** structure on a `ℂ`-linear monoidal category with right duals, kernels and
finite biproducts: finitely many pairwise non-isomorphic simple objects `simple i`, one of which
is the unit, such that every object is a finite biproduct of them, and all `Hom`-spaces are
finite-dimensional. `End 𝟙 = ℂ` is then a theorem (`finrank_end_unit`). -/
class FusionCategory [HasKernels C] [HasFiniteBiproducts C] [RightRigidCategory C] where
  ι : Type
  [fintype : Fintype ι]
  [decEq : DecidableEq ι]
  simple : ι → C
  isSimple : ∀ i, Simple (simple i)
  unitLabel : ι
  unitIso : simple unitLabel ≅ 𝟙_ C
  inequivalent : ∀ i j, Nonempty (simple i ≅ simple j) → i = j
  semisimple : ∀ X : C, ∃ (n : ℕ) (f : Fin n → ι), Nonempty (X ≅ ⨁ fun k => simple (f k))
  finiteDimensional : ∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)

namespace FusionCategory

variable {C} [HasKernels C] [HasFiniteBiproducts C] [RightRigidCategory C] [F : FusionCategory C]

attribute [instance_reducible, instance] FusionCategory.fintype FusionCategory.decEq

/-- `End 𝟙 = ℂ`, from Schur's lemma for the simple unit. -/
theorem finrank_end_unit : finrank ℂ (𝟙_ C ⟶ 𝟙_ C) = 1 := by
  haveI := F.isSimple F.unitLabel
  haveI : Simple (𝟙_ C) := Simple.of_iso F.unitIso.symm
  haveI := F.finiteDimensional (𝟙_ C) (𝟙_ C)
  exact finrank_endomorphism_simple_eq_one ℂ (𝟙_ C)

/-- Fusion multiplicities `N_{ij}^k = dim Hom(X_k, X_i ⊗ X_j)`. -/
def N (i j k : F.ι) : ℕ := finrank ℂ (F.simple k ⟶ F.simple i ⊗ F.simple j)

end FusionCategory

/-- A **pivotal structure**: a natural isomorphism `X ≅ Xᘁᘁ`.  (The monoidality axiom is deferred:
Mathlib has no canonical `(X ⊗ Y)ᘁ ≅ Yᘁ ⊗ Xᘁ`; see the module docstring.) -/
structure PivotalStructure [RightRigidCategory C] where
  piv : ∀ X : C, X ≅ (Xᘁ)ᘁ
  naturality : ∀ {X Y : C} (f : X ⟶ Y), f ≫ (piv Y).hom = (piv X).hom ≫ (fᘁ)ᘁ

namespace PivotalStructure

variable {C} [RightRigidCategory C] (P : PivotalStructure C)

/-- The **left pivotal trace** `𝟙 → X ⊗ Xᘁ → X ⊗ Xᘁ → Xᘁᘁ ⊗ Xᘁ → 𝟙`. -/
def trL {X : C} (f : X ⟶ X) : 𝟙_ C ⟶ 𝟙_ C :=
  η_ X Xᘁ ≫ (f ▷ Xᘁ) ≫ ((P.piv X).hom ▷ Xᘁ) ≫ ε_ Xᘁ (Xᘁ)ᘁ

/-- The **right pivotal trace** `𝟙 → Xᘁ ⊗ Xᘁᘁ → Xᘁ ⊗ X → 𝟙`. -/
def trR {X : C} (f : X ⟶ X) : 𝟙_ C ⟶ 𝟙_ C :=
  η_ Xᘁ (Xᘁ)ᘁ ≫ (Xᘁ ◁ ((P.piv X).inv ≫ f)) ≫ ε_ X Xᘁ

theorem trL_add {X : C} (f g : X ⟶ X) : P.trL (f + g) = P.trL f + P.trL g := by
  simp [trL, MonoidalPreadditive.add_whiskerRight, Preadditive.add_comp, Preadditive.comp_add]

theorem trL_smul {X : C} (c : ℂ) (f : X ⟶ X) : P.trL (c • f) = c • P.trL f := by
  simp [trL]

/-- The **quantum (categorical) dimension** `dim X = tr_L(𝟙_X)`, as a scalar. -/
def qdim (X : C) : ℂ := toScalar (P.trL (𝟙 X))

/-- **Spherical**: left and right traces agree. -/
def IsSpherical : Prop := ∀ (X : C) (f : X ⟶ X), P.trL f = P.trR f

end PivotalStructure

/-- A **ribbon structure** on a braided category with right duals: a pivotal structure and a
natural twist `θ` satisfying the balancing axiom and `θ_{Xᘁ} = (θ_X)ᘁ`. -/
structure RibbonStructure [RightRigidCategory C] [BraidedCategory C] extends PivotalStructure C where
  twist : ∀ X : C, X ≅ X
  twist_naturality : ∀ {X Y : C} (f : X ⟶ Y), f ≫ (twist Y).hom = (twist X).hom ≫ f
  balance : ∀ X Y : C,
    (twist (X ⊗ Y)).hom = ((twist X).hom ⊗ₘ (twist Y).hom) ≫ (β_ X Y).hom ≫ (β_ Y X).hom
  twist_dual : ∀ X : C, (twist Xᘁ).hom = ((twist X).hom)ᘁ

/-- `X` is **transparent** (lies in the Müger centralizer): its double braiding with every `Y`
is trivial. -/
def IsTransparent [BraidedCategory C] (X : C) : Prop :=
  ∀ Y : C, (β_ X Y).hom ≫ (β_ Y X).hom = 𝟙 (X ⊗ Y)

/-- The **Müger centralizer** (Müger center) of a braided category. -/
def mugerCentralizer [BraidedCategory C] : Set C := {X | IsTransparent C X}

theorem isTransparent_unit [BraidedCategory C] : IsTransparent C (𝟙_ C) := by
  intro Y
  simp [braiding_tensorUnit_left, braiding_tensorUnit_right]

/-- The Müger centralizer is closed under `⊗` (hexagon axioms). -/
theorem IsTransparent.tensor [BraidedCategory C] {X X' : C} (hX : IsTransparent C X)
    (hX' : IsTransparent C X') : IsTransparent C (X ⊗ X') := by
  intro Y
  rw [BraidedCategory.braiding_tensor_left_hom, BraidedCategory.braiding_tensor_right_hom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← comp_whiskerRight_assoc, hX Y, id_whiskerRight, Category.id_comp, Iso.inv_hom_id_assoc,
    ← whiskerLeft_comp_assoc, hX' Y, whiskerLeft_id, Category.id_comp, Iso.hom_inv_id]

namespace RibbonStructure

variable {C} [RightRigidCategory C] [BraidedCategory C] [HasKernels C] [HasFiniteBiproducts C]
  [F : FusionCategory C] (R : RibbonStructure C)

/-- The unnormalized **`S`-matrix** `S̃_ij = tr(c_{j,i} ∘ c_{i,j})`. -/
def sTilde (i j : F.ι) : ℂ :=
  toScalar (R.trL ((β_ (F.simple i) (F.simple j)).hom ≫ (β_ (F.simple j) (F.simple i)).hom))

/-- The **`T`-matrix** (diagonal): `θ_{X_i} = T_i • 𝟙` (Schur). -/
def T (i : F.ι) : ℂ :=
  open Classical in
  if h : ∃ c : ℂ, c • 𝟙 (F.simple i) = (R.twist (F.simple i)).hom then h.choose else 0

theorem T_spec (i : F.ι) : R.T i • 𝟙 (F.simple i) = (R.twist (F.simple i)).hom := by
  haveI := F.isSimple i
  haveI := F.finiteDimensional (F.simple i) (F.simple i)
  have hex := endomorphism_simple_eq_smul_id ℂ (R.twist (F.simple i)).hom
  rw [T, dif_pos hex]
  exact hex.choose_spec

/-- **Modular**: the `S̃`-matrix is nondegenerate. -/
def IsModular : Prop := (Matrix.of R.sTilde).det ≠ 0

end RibbonStructure

end Abstract

/-! ## §2  Modular data as finite data -/

/-- **Modular data** as finite data: labels `ι` with a vacuum, fusion multiplicities
`N a b c = N_{ab}^c`, the `S`- and `T`-matrices, dimensions `d`, and `S₀₀`. -/
structure ModularDatum where
  ι : Type
  [fintype : Fintype ι]
  [decEq : DecidableEq ι]
  vac : ι
  N : ι → ι → ι → ℕ
  S : ι → ι → ℂ
  T : ι → ℂ
  d : ι → ℝ
  S00 : ℝ

attribute [instance] ModularDatum.fintype ModularDatum.decEq

namespace ModularDatum

variable (D : ModularDatum)

/-- The **Verlinde formula** `N_{ab}^c = ∑_x S_{ax} S_{bx} conj(S_{cx}) / S_{0x}`. -/
def Verlinde : Prop :=
  ∀ a b c, (D.N a b c : ℂ) = ∑ x, D.S a x * D.S b x * star (D.S c x) / D.S D.vac x

/-- `S` is **unitary**. -/
def IsUnitary : Prop := Matrix.of D.S * Matrix.conjTranspose (Matrix.of D.S) = 1

/-- `S` is symmetric. -/
def IsSymmetric : Prop := ∀ a b, D.S a b = D.S b a

/-- The row of `a` **factorizes**: `S_ab = S₀₀ d_a d_b` for all `b` (the `ITannakian` shape). -/
def Factorized (a : D.ι) : Prop := ∀ b, D.S a b = (D.S00 : ℂ) * (D.d a : ℂ) * (D.d b : ℂ)

end ModularDatum

/-! ## §3  The pointed braided fusion category `C(A, q)` -/

/-- A **pre-metric group** `(A, q)`: a finite abelian group with a `U(1)`-valued quadratic form,
i.e. `q(-a) = q(a)` and `b(a,c) = q(a+c)/(q(a) q(c))` is a bicharacter. -/
structure PreMetricGroup (A : Type) [AddCommGroup A] [Fintype A] where
  q : A → ℂ
  norm_q : ∀ a, ‖q a‖ = 1
  q_neg : ∀ a, q (-a) = q a
  bil_add_left : ∀ a a' c,
    q (a + a' + c) / (q (a + a') * q c) = q (a + c) / (q a * q c) * (q (a' + c) / (q a' * q c))

namespace PreMetricGroup

variable {A : Type} [AddCommGroup A] [Fintype A] (Q : PreMetricGroup A)

/-- The associated bicharacter `b(a,c) = q(a+c)/(q(a) q(c))` (= the double braiding
`c_{c,a} c_{a,c}` of `C(A,q)`). -/
def bil (a c : A) : ℂ := Q.q (a + c) / (Q.q a * Q.q c)

theorem q_ne_zero (a : A) : Q.q a ≠ 0 := by
  intro h; have := Q.norm_q a; rw [h, norm_zero] at this; exact zero_ne_one this

theorem bil_comm (a c : A) : Q.bil a c = Q.bil c a := by
  simp only [bil, add_comm a c, mul_comm (Q.q a)]

theorem bil_add_left' (a a' c : A) : Q.bil (a + a') c = Q.bil a c * Q.bil a' c :=
  Q.bil_add_left a a' c

theorem bil_add_right (a c c' : A) : Q.bil a (c + c') = Q.bil a c * Q.bil a c' := by
  rw [bil_comm, bil_add_left', Q.bil_comm c a, Q.bil_comm c' a]

theorem norm_bil (a c : A) : ‖Q.bil a c‖ = 1 := by
  simp [bil, Q.norm_q]

theorem bil_ne_zero (a c : A) : Q.bil a c ≠ 0 := by
  intro h; have := Q.norm_bil a c; rw [h, norm_zero] at this; exact zero_ne_one this

theorem bil_zero_left (c : A) : Q.bil 0 c = 1 := by
  have h := Q.bil_add_left' 0 0 c
  rw [add_zero] at h
  have hne := Q.bil_ne_zero 0 c
  have : Q.bil 0 c * (Q.bil 0 c - 1) = 0 := by rw [mul_sub, mul_one, ← h, sub_self]
  rcases mul_eq_zero.mp this with h1 | h1
  · exact absurd h1 hne
  · exact sub_eq_zero.mp h1

theorem bil_zero_right (a : A) : Q.bil a 0 = 1 := by rw [bil_comm, bil_zero_left]

theorem q_zero : Q.q 0 = 1 := by
  have h := Q.bil_zero_left 0
  simp only [bil, add_zero] at h
  have hq := Q.q_ne_zero 0
  field_simp at h
  exact h.symm

theorem star_bil (a c : A) : star (Q.bil a c) = Q.bil (-a) c := by
  have h1 : Q.bil a c * Q.bil (-a) c = 1 := by rw [← bil_add_left', add_neg_cancel, bil_zero_left]
  have h2 : Q.bil a c * star (Q.bil a c) = 1 := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_bil]; simp
  have hne := Q.bil_ne_zero a c
  exact mul_left_cancel₀ hne (h2.trans h1.symm)

/-- `b(a, a) = q(a)²` (the self-monodromy is the square of the twist). -/
theorem bil_self (a : A) : Q.bil a a = Q.q a ^ 2 := by
  have h1 : Q.bil a a * Q.bil a (-a) = 1 := by rw [← bil_add_right, add_neg_cancel, bil_zero_right]
  have h2 : Q.bil a (-a) = (Q.q a ^ 2)⁻¹ := by
    rw [bil, add_neg_cancel, q_zero, Q.q_neg]; ring
  rw [h2] at h1
  have hq := pow_ne_zero 2 (Q.q_ne_zero a)
  field_simp at h1
  rwa [div_eq_one_iff_eq hq] at h1

/-- The additive character `x ↦ b(y, x)`. -/
def bilChar (y : A) : AddChar A ℂ where
  toFun := Q.bil y
  map_zero_eq_one' := Q.bil_zero_right y
  map_add_eq_mul' := Q.bil_add_right y

/-- `y` is **transparent** in `C(A, q)`: `b(y, ·) ≡ 1`. -/
def IsTransparent (y : A) : Prop := ∀ x, Q.bil y x = 1

/-- `b` is **nondegenerate** (the Müger center of `C(A, q)` is trivial). -/
def Nondegenerate : Prop := ∀ y, Q.IsTransparent y → y = 0

/-- The **character sum** `∑_x b(y, x) = |A|` if `y` is transparent, `0` otherwise. -/
theorem sum_bil (y : A) [Decidable (Q.IsTransparent y)] :
    ∑ x, Q.bil y x = if Q.IsTransparent y then (Fintype.card A : ℂ) else 0 := by
  classical
  have h := AddChar.sum_eq_ite (Q.bilChar y)
  have hiff : Q.bilChar y = 0 ↔ Q.IsTransparent y := by
    constructor
    · intro h0 x
      have := congrArg (fun ψ : AddChar A ℂ => ψ x) h0
      simpa [bilChar] using this
    · intro ht; ext x; simpa [bilChar] using ht x
  have hs : ∑ x, Q.bilChar y x = ∑ x, Q.bil y x := rfl
  rw [hs] at h
  rw [h]
  by_cases ht : Q.IsTransparent y
  · rw [if_pos (hiff.mpr ht), if_pos ht]
  · rw [if_neg (fun h0 => ht (hiff.mp h0)), if_neg ht]

/-- The normalization `|A|^{-1/2}`. -/
def s0 : ℝ := (Real.sqrt (Fintype.card A))⁻¹

theorem s0_sq : (s0 (A := A) : ℂ) * (s0 (A := A) : ℂ) = (Fintype.card A : ℂ)⁻¹ := by
  have hpos : (0 : ℝ) < Fintype.card A := by
    have : Nonempty A := ⟨0⟩
    exact_mod_cast Fintype.card_pos
  rw [← Complex.ofReal_mul, s0, ← mul_inv, Real.mul_self_sqrt hpos.le]
  push_cast; rfl

/-- **The modular data of `C(A, q)`**: `N_{ab}^c = [c = a + b]`, `S_ab = |A|^{-1/2} conj b(a,b)`,
`T_a = q(a)`, `d_a = 1`, `S₀₀ = |A|^{-1/2}`. -/
abbrev pointedDatum [DecidableEq A] : ModularDatum where
  ι := A
  vac := 0
  N a b c := if c = a + b then 1 else 0
  S a x := (s0 (A := A) : ℂ) * star (Q.bil a x)
  T := Q.q
  d _ := 1
  S00 := s0 (A := A)

variable [DecidableEq A]

theorem pointedDatum_S (a x : A) :
    Q.pointedDatum.S a x = (s0 (A := A) : ℂ) * Q.bil (-a) x := by
  rw [← star_bil]

theorem pointedDatum_isSymmetric : Q.pointedDatum.IsSymmetric := by
  intro a b
  change (s0 (A := A) : ℂ) * star (Q.bil a b) = (s0 (A := A) : ℂ) * star (Q.bil b a)
  rw [bil_comm]

/-- The key orthogonality: `∑_x S_{ax} conj(S_{cx}) = |A|^{-1} ∑_x b(c - a, x)`. -/
theorem sum_S_mul_star (a c : A) :
    ∑ x, Q.pointedDatum.S a x * star (Q.pointedDatum.S c x) =
      (Fintype.card A : ℂ)⁻¹ * ∑ x, Q.bil (c - a) x := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [pointedDatum_S, pointedDatum_S, star_mul', Complex.star_def, Complex.conj_ofReal,
    ← Complex.star_def, star_bil, neg_neg, ← s0_sq, sub_eq_add_neg, add_comm c,
    bil_add_left']
  ring

/-- **Modularity**: the `S`-matrix of `C(A, q)` is unitary **iff** `b` is nondegenerate. -/
theorem pointedDatum_isUnitary_iff : Q.pointedDatum.IsUnitary ↔ Q.Nondegenerate := by
  classical
  have hcard : (Fintype.card A : ℂ) ≠ 0 := by
    have : Nonempty A := ⟨0⟩
    exact_mod_cast Fintype.card_ne_zero
  have hentry : ∀ a c : A, (Matrix.of Q.pointedDatum.S * Matrix.conjTranspose (Matrix.of Q.pointedDatum.S)) a c =
      if Q.IsTransparent (c - a) then 1 else 0 := by
    intro a c
    rw [Matrix.mul_apply]
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply]
    rw [sum_S_mul_star, sum_bil]
    split_ifs <;> simp [hcard]
  constructor
  · intro hU y hy
    have h := congrFun (congrFun hU 0) y
    rw [hentry, sub_zero, if_pos hy, Matrix.one_apply] at h
    by_contra hne
    rw [if_neg (Ne.symm hne)] at h
    exact one_ne_zero h
  · intro hnd
    ext a c
    rw [hentry, Matrix.one_apply]
    by_cases hac : a = c
    · subst hac
      rw [sub_self, if_pos (show Q.IsTransparent 0 from fun x => Q.bil_zero_left x), if_pos rfl]
    · rw [if_neg hac, if_neg]
      intro ht
      exact hac (sub_eq_zero.mp (hnd _ ht)).symm

/-- **The Verlinde formula** for `C(A, q)`, `b` nondegenerate. -/
theorem pointedDatum_verlinde (hnd : Q.Nondegenerate) : Q.pointedDatum.Verlinde := by
  classical
  intro a b c
  have hcard : (Fintype.card A : ℂ) ≠ 0 := by
    have : Nonempty A := ⟨0⟩
    exact_mod_cast Fintype.card_ne_zero
  have hs : (s0 (A := A) : ℂ) ≠ 0 := by
    intro h; have := s0_sq (A := A); rw [h, zero_mul] at this
    exact (inv_ne_zero hcard) this.symm
  have hterm : ∀ x, Q.pointedDatum.S a x * Q.pointedDatum.S b x *
      star (Q.pointedDatum.S c x) / Q.pointedDatum.S Q.pointedDatum.vac x =
      (Fintype.card A : ℂ)⁻¹ * Q.bil (c - (a + b)) x := by
    intro x
    have hv : Q.pointedDatum.S Q.pointedDatum.vac x = (s0 (A := A) : ℂ) := by
      change (s0 (A := A) : ℂ) * star (Q.bil 0 x) = _
      rw [bil_zero_left, star_one, mul_one]
    rw [hv, pointedDatum_S, pointedDatum_S, pointedDatum_S, star_mul', Complex.star_def,
      Complex.conj_ofReal, ← Complex.star_def, star_bil, neg_neg, ← s0_sq,
      sub_eq_add_neg, neg_add, add_comm c, add_assoc, bil_add_left', bil_add_left']
    field_simp
  rw [Finset.sum_congr rfl fun x _ => hterm x, ← Finset.mul_sum, sum_bil]
  change ((if c = a + b then 1 else 0 : ℕ) : ℂ) = _
  by_cases h : c = a + b
  · rw [if_pos h, if_pos, Nat.cast_one, inv_mul_cancel₀ hcard]
    rw [h, sub_self]; exact (show Q.IsTransparent 0 from fun x => Q.bil_zero_left x)
  · rw [if_neg h, if_neg, Nat.cast_zero, mul_zero]
    intro ht; exact h (sub_eq_zero.mp (hnd _ ht))

/-- **Müger's criterion, pointed case**: `a` is transparent (`b(a,·) ≡ 1`) iff its `S`-row
factorizes, `S_ab = S₀₀ d_a d_b` for all `b` — the hypothesis shape of `ITannakian`. -/
theorem pointedDatum_factorized_iff (a : A) :
    Q.pointedDatum.Factorized a ↔ Q.IsTransparent a := by
  have hs : (s0 (A := A) : ℂ) ≠ 0 := by
    have hcard : (Fintype.card A : ℂ) ≠ 0 := by
      have : Nonempty A := ⟨0⟩
      exact_mod_cast Fintype.card_ne_zero
    intro h; have := s0_sq (A := A); rw [h, zero_mul] at this
    exact (inv_ne_zero hcard) this.symm
  change (∀ x, (s0 (A := A) : ℂ) * star (Q.bil a x) = (s0 (A := A) : ℂ) * ((1 : ℝ) : ℂ) * ((1 : ℝ) : ℂ)) ↔ _
  simp only [Complex.ofReal_one, mul_one]
  constructor
  · intro h x
    have := mul_left_cancel₀ hs ((h x).trans (mul_one _).symm)
    rw [← star_star (Q.bil a x), this, star_one]
  · intro h x; rw [h x, star_one, mul_one]

theorem pointedDatum_T_vac : Q.pointedDatum.T Q.pointedDatum.vac = 1 := Q.q_zero

end PreMetricGroup

/-! ## §4  `A = ℤ/2m`, `q(j) = e^{πi j²/2m}`: the modular data of `V_{2m}` -/

section Lattice

open Complex VOA.Classification.COne

variable (m : ℕ) [NeZero m]

instance instNeZeroTwoMul : NeZero (2 * m) := ⟨by have := NeZero.ne m; omega⟩

/-- The quadratic form `q(j) = e^{πi j²/2m}` on `ℤ/2m` (`j` read through its representative in
`[0, 2m)`; `latQ_intCast` shows any integer lift gives the same value). -/
def latQ (j : ZMod (2 * m)) : ℂ :=
  cexp (((Real.pi * ((j.val : ℕ) : ℝ) ^ 2 / (2 * m) : ℝ) : ℂ) * I)

theorem latQ_intCast (n : ℤ) :
    latQ m (n : ZMod (2 * m)) = cexp (Real.pi * I * (n : ℂ) ^ 2 / (2 * m)) := by
  have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  set r := n % (2 * (m : ℤ)) with hr
  set t := n / (2 * (m : ℤ)) with ht
  have hn : n = r + 2 * m * t := (Int.emod_add_mul_ediv n (2 * m)).symm
  have hv : (((n : ZMod (2 * m)).val : ℕ) : ℤ) = r := by
    rw [ZMod.val_intCast]; push_cast; rfl
  have hvR : (((n : ZMod (2 * m)).val : ℕ) : ℝ) = (r : ℝ) := by exact_mod_cast hv
  rw [latQ, hvR]
  have : Real.pi * I * (n : ℂ) ^ 2 / (2 * m) =
      ((Real.pi * (r : ℝ) ^ 2 / (2 * m) : ℝ) : ℂ) * I + ((r * t + m * t ^ 2 : ℤ) : ℂ) * (2 * Real.pi * I) := by
    rw [hn]; push_cast; field_simp; ring
  rw [this, Complex.exp_add, exp_int_mul_two_pi_mul_I, mul_one]

/-- The bicharacter of `latQ` on integer lifts. -/
theorem latQ_bil_int (j k : ℤ) :
    latQ m ((j + k : ℤ) : ZMod (2 * m)) / (latQ m (j : ZMod (2 * m)) * latQ m (k : ZMod (2 * m))) =
      cexp (2 * Real.pi * I * j * k / (2 * m)) := by
  rw [latQ_intCast, latQ_intCast, latQ_intCast, ← Complex.exp_add, ← Complex.exp_sub]
  congr 1
  have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  push_cast; field_simp; ring

/-- **The pre-metric group `(ℤ/2m, e^{πi j²/2m})`** — the discriminant form of `√(2m) ℤ`. -/
def latticePMG : PreMetricGroup (ZMod (2 * m)) where
  q := latQ m
  norm_q a := by rw [latQ]; exact Complex.norm_exp_ofReal_mul_I _
  q_neg a := by
    obtain ⟨n, rfl⟩ := ZMod.intCast_surjective a
    rw [← Int.cast_neg, latQ_intCast, latQ_intCast]; push_cast; ring_nf
  bil_add_left a a' c := by
    obtain ⟨j, rfl⟩ := ZMod.intCast_surjective a
    obtain ⟨j', rfl⟩ := ZMod.intCast_surjective a'
    obtain ⟨k, rfl⟩ := ZMod.intCast_surjective c
    simp only [← Int.cast_add]
    rw [latQ_bil_int, latQ_bil_int, latQ_bil_int, ← Complex.exp_add]
    congr 1; push_cast; ring

/-- `b(j, k) = e^{2πi jk/2m}`. -/
theorem latticePMG_bil (j k : ℤ) :
    (latticePMG m).bil (j : ZMod (2 * m)) (k : ZMod (2 * m)) = cexp (2 * Real.pi * I * j * k / (2 * m)) := by
  rw [PreMetricGroup.bil, ← Int.cast_add]
  exact latQ_bil_int m j k

/-- `T_j = q(j) = e^{2πi h_j}` with `h_j = j²/4m`, the conformal weight of `V_{L+λ_j}`. -/
theorem latticePMG_q_eq_exp_weight (j : ℤ) :
    (latticePMG m).q (j : ZMod (2 * m)) = cexp (2 * Real.pi * I * ((j : ℂ) ^ 2 / (4 * m))) := by
  change latQ m _ = _
  rw [latQ_intCast]
  congr 1
  have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  field_simp; ring

/-- The bicharacter of `ℤ/2m` is **nondegenerate**: `C(ℤ/2m, q)` is modular. -/
theorem latticePMG_nondegenerate : (latticePMG m).Nondegenerate := by
  intro y hy
  obtain ⟨n, rfl⟩ := ZMod.intCast_surjective y
  have h := hy ((1 : ℤ) : ZMod (2 * m))
  rw [latticePMG_bil, Complex.exp_eq_one_iff] at h
  obtain ⟨k, hk⟩ := h
  have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hnC : (n : ℂ) = ((2 * m * k : ℤ) : ℂ) := by
    push_cast
    field_simp at hk
    simpa using hk
  have hn : n = 2 * m * k := by exact_mod_cast hnC
  rw [hn, ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  exact Dvd.intro k rfl

/-- **Fusion match**: the fusion rules of `C(ℤ/2m, q)` are those of `V_{2m}`,
`N_{jk}^l = fusionRule (V_{L+λ_j}) (V_{L+λ_k}) (V_{L+λ_l})` (H2a, `fusionRule_latticeModule`). -/
theorem latticeDatum_N_eq_fusionRule (hm : 1 ≤ m) (j k l : ℤ) :
    (latticePMG m).pointedDatum.N (j : ZMod (2 * m)) (k : ZMod (2 * m)) (l : ZMod (2 * m)) =
      VOA.fusionRule (LatMod.latticeModule m hm j) (LatMod.latticeModule m hm k)
        (LatMod.latticeModule m hm l) := by
  rw [VOA.Huang.LatFus.fusionRule_latticeModule]
  change (if (l : ZMod (2 * m)) = (j : ZMod (2 * m)) + (k : ZMod (2 * m)) then 1 else 0) = _
  have hiff : (l : ZMod (2 * m)) = (j : ZMod (2 * m)) + (k : ZMod (2 * m)) ↔
      (l - j - k) % (2 * (m : ℤ)) = 0 := by
    rw [← Int.cast_add, ZMod.intCast_eq_intCast_iff_dvd_sub]
    push_cast
    constructor
    · intro h
      exact Int.emod_eq_zero_of_dvd (by
        have : l - j - k = -(j + k - l) := by ring
        rw [this]; exact (Int.dvd_neg).mpr h)
    · intro h
      have h' := Int.dvd_of_emod_eq_zero h
      have : j + k - l = -(l - j - k) := by ring
      rw [this]; exact (Int.dvd_neg).mpr h'
  by_cases h : (l : ZMod (2 * m)) = (j : ZMod (2 * m)) + (k : ZMod (2 * m))
  · rw [if_pos h, if_pos (hiff.mp h)]
  · rw [if_neg h, if_neg (fun h' => h (hiff.mpr h'))]

/-- The theta numerator `θ_j(τ) = ∑_{n ≡ j (2m)} q^{n²/4m}` of the character of `V_{L+λ_j}`
(GR's `θ_{j,2m,1/4m}`). -/
def latTheta (n : ℤ) (τ : ℂ) : ℂ := rankOneTheta n ((2 * m : ℕ) : ℤ) (1 / (4 * (m : ℝ))) τ

/-- **`T`-law**: `θ_j(τ + 1) = T_j θ_j(τ)`, `T_j = q(j) = e^{2πi j²/4m}`. -/
theorem latticeTheta_T (j : ℤ) (τ : ℂ) :
    latTheta m j (τ + 1) = (latticePMG m).pointedDatum.T (j : ZMod (2 * m)) * latTheta m j τ := by
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  rw [latTheta, latTheta, rankOneTheta_T_twisted j _ _ m j (by push_cast; field_simp; ring)
    (by push_cast; field_simp; ring)]
  congr 1
  change _ = latQ m _
  rw [latQ_intCast]
  congr 1
  push_cast
  field_simp
  ring

theorem rankOneTheta_add_mul (n₀ r d : ℤ) (t : ℝ) (τ : ℂ) :
    rankOneTheta (n₀ + r * d) r t τ = rankOneTheta n₀ r t τ := by
  conv_lhs => rw [rankOneTheta, ← (Equiv.addRight (-d)).tsum_eq]
  refine tsum_congr fun k => ?_
  simp only [rankOneThetaTerm, Equiv.coe_addRight]
  congr 3; push_cast; ring

theorem rankOneTheta_neg (n₀ r : ℤ) (t : ℝ) (τ : ℂ) :
    rankOneTheta (-n₀) r t τ = rankOneTheta n₀ r t τ := by
  conv_lhs => rw [rankOneTheta, ← (Equiv.neg ℤ).tsum_eq]
  refine tsum_congr fun k => ?_
  simp only [rankOneThetaTerm, Equiv.neg_apply]
  congr 3; push_cast; ring

/-- `θ_j` depends only on `j mod 2m`. -/
theorem latTheta_congr {a b : ℤ} (h : (a : ZMod (2 * m)) = b) (τ : ℂ) :
    latTheta m a τ = latTheta m b τ := by
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h
  obtain ⟨d, hd⟩ := h
  have : b = a + ((2 * m : ℕ) : ℤ) * d := by omega
  rw [this, latTheta, latTheta, rankOneTheta_add_mul]

theorem latTheta_neg (a : ℤ) (τ : ℂ) : latTheta m (-a) τ = latTheta m a τ :=
  rankOneTheta_neg _ _ _ _

/-- `(x z)^{1/2} = √x · z^{1/2}` for `x > 0` real. -/
theorem ofReal_mul_cpow_half {x : ℝ} (hx : 0 < x) {z : ℂ} (hz : z ≠ 0) :
    ((x : ℂ) * z) ^ (1 / 2 : ℂ) = ((Real.sqrt x : ℝ) : ℂ) * z ^ (1 / 2 : ℂ) := by
  have hx' : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  rw [cpow_def_of_ne_zero (mul_ne_zero hx' hz), log_ofReal_mul hx hz, cpow_def_of_ne_zero hz,
    add_mul, Complex.exp_add, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx, Complex.ofReal_exp]
  push_cast
  ring_nf

/-- **`S`-law**: `θ_j(−1/τ) = (−iτ)^{1/2} ∑_{k ∈ ℤ/2m} S_{jk} θ_k(τ)` with
`S_{jk} = (2m)^{-1/2} conj b(j,k)` the `S`-matrix of `C(ℤ/2m, q)`.  Since
`η(−1/τ) = (−iτ)^{1/2} η(τ)`, this is `ch_j(−1/τ) = ∑_k S_{jk} ch_k(τ)` for `ch_j = θ_j/η`. -/
theorem latticeTheta_S (j : ℤ) {τ : ℂ} (hτ : 0 < τ.im) :
    latTheta m j (-1 / τ) = (-I * τ) ^ (1 / 2 : ℂ) *
      ∑ k : ZMod (2 * m), (latticePMG m).pointedDatum.S (j : ZMod (2 * m)) k *
        latTheta m (k.val : ℤ) τ := by
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne m))
  have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  have hτ0 : τ ≠ 0 := fun h => by simp [h] at hτ
  have ht : (0 : ℝ) < 1 / (4 * (m : ℝ)) := by positivity
  have h := rankOneTheta_S_residues j (2 * m) ht hτ
  -- the dual theta parameter is again `1/4m`
  have ht' : (1 / (4 * (1 / (4 * (m : ℝ))) * ((2 * m : ℕ) : ℝ) ^ 2)) = 1 / (4 * (m : ℝ)) := by
    push_cast; field_simp; ring
  rw [ht'] at h
  -- the prefactor
  have hpre : (-I * (τ / (2 * ((1 / (4 * (m : ℝ)) : ℝ) : ℂ) * (((2 * m : ℕ) : ℤ) : ℂ) ^ 2))) ^ (1 / 2 : ℂ) =
      ((Real.sqrt ((2 * m : ℝ)⁻¹) : ℝ) : ℂ) * (-I * τ) ^ (1 / 2 : ℂ) := by
    rw [← ofReal_mul_cpow_half (by positivity) (mul_ne_zero (neg_ne_zero.mpr I_ne_zero) hτ0)]
    congr 1
    push_cast; field_simp; ring
  rw [hpre] at h
  -- the sums
  have hs0 : (PreMetricGroup.s0 (A := ZMod (2 * m)) : ℂ) = ((Real.sqrt ((2 * m : ℝ)⁻¹) : ℝ) : ℂ) := by
    rw [PreMetricGroup.s0, ZMod.card, Real.sqrt_inv]; push_cast; rfl
  have hstar : ∀ k : ZMod (2 * m), (latticePMG m).pointedDatum.S (j : ZMod (2 * m)) k *
      latTheta m (k.val : ℤ) τ =
      (PreMetricGroup.s0 (A := ZMod (2 * m)) : ℂ) *
        ((latticePMG m).bil (j : ZMod (2 * m)) (-k) * latTheta m ((-k).val : ℤ) τ) := by
    intro k
    have hb : star ((latticePMG m).bil (j : ZMod (2 * m)) k) =
        (latticePMG m).bil (j : ZMod (2 * m)) (-k) := by
      rw [PreMetricGroup.bil_comm, PreMetricGroup.star_bil, PreMetricGroup.bil_comm]
    have hθ : latTheta m ((-k).val : ℤ) τ = latTheta m (k.val : ℤ) τ := by
      rw [← latTheta_neg m (k.val : ℤ)]
      apply latTheta_congr
      push_cast
      rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    change (PreMetricGroup.s0 (A := ZMod (2 * m)) : ℂ) * star ((latticePMG m).bil (j : ZMod (2 * m)) k) *
      latTheta m (k.val : ℤ) τ = _
    rw [hb, hθ, mul_assoc]
  have hneg : ∑ k : ZMod (2 * m), (latticePMG m).bil (j : ZMod (2 * m)) (-k) * latTheta m ((-k).val : ℤ) τ =
      ∑ k : ZMod (2 * m), (latticePMG m).bil (j : ZMod (2 * m)) k * latTheta m (k.val : ℤ) τ :=
    Fintype.sum_equiv (Equiv.neg (ZMod (2 * m)))
    (fun k => (latticePMG m).bil (j : ZMod (2 * m)) (-k) * latTheta m ((-k).val : ℤ) τ)
    (fun k => (latticePMG m).bil (j : ZMod (2 * m)) k * latTheta m (k.val : ℤ) τ)
    (fun k => rfl)
  -- `Fin (2m) → ZMod (2m)`, `k ↦ k`
  have hbij : Function.Bijective (fun k : Fin (2 * m) => ((k : ℕ) : ZMod (2 * m))) := by
    constructor
    · intro a b hab
      have := congrArg ZMod.val hab
      simp only [ZMod.val_natCast_of_lt a.isLt, ZMod.val_natCast_of_lt b.isLt] at this
      exact Fin.ext this
    · intro z
      exact ⟨⟨z.val, ZMod.val_lt z⟩, ZMod.natCast_zmod_val z⟩
  have hfin : ∑ k : Fin (2 * m), cexp (2 * Real.pi * I * ((k : ℕ) : ℂ) * j / ((2 * m : ℕ) : ℂ)) *
      rankOneTheta ((k : ℕ) : ℤ) ((2 * m : ℕ) : ℤ) (1 / (4 * (m : ℝ))) τ =
      ∑ k : ZMod (2 * m), (latticePMG m).bil (j : ZMod (2 * m)) k * latTheta m (k.val : ℤ) τ := by
    refine Fintype.sum_bijective _ hbij _ _ fun k => ?_
    have hc : ((k : ℕ) : ZMod (2 * m)) = (((k : ℕ) : ℤ) : ZMod (2 * m)) := (Int.cast_natCast _).symm
    rw [hc, latticePMG_bil, ← hc, ZMod.val_natCast_of_lt k.isLt, latTheta]
    congr 2
    push_cast
    ring
  rw [Finset.sum_congr rfl fun k _ => hstar k, ← Finset.mul_sum, hneg, ← hfin, hs0, latTheta, h]
  ring

end Lattice

end VOA.Huang.TensorCat
