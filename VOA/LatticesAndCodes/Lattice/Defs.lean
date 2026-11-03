/-
Copyright (c) 2026 Leonardo Rastelli and Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Integral lattices

This file is the keystone of the library: it fixes what a *lattice* is for the rest of the
project, following decision **D1** of `BLUEPRINT.md`.

Ebeling (§1.1) works with a lattice as a subgroup `Γ = ℤe₁ ⊕ ⋯ ⊕ ℤeₙ` of a Euclidean space.
Here a lattice is instead an *abstract* finitely generated free `ℤ`-module carrying a symmetric
`ℤ`-valued bilinear form. The two notions agree for positive definite forms — the bridge is
`LatticesAndCodes/Lattice/Euclidean.lean` — but the abstract form is what almost every argument
in the book actually uses, and it costs no basis bookkeeping.

Definiteness is deliberately **not** part of the definition, so that indefinite lattices such as
the hyperbolic plane share this API.

## Main definitions

* `IntegralLattice` — the bundled structure.
* `IntegralLattice.normSq` — the value `⟪x, x⟫`, written `x²` in the book.
* `IntegralLattice.rank`, `IntegralLattice.chooseBasis` — the rank and a chosen `ℤ`-basis.
* `IntegralLattice.gram` — the Gram matrix in a basis.
* `IntegralLattice.det` — the discriminant; basis independent by `IntegralLattice.det_eq_gram_det`.
* `IntegralLattice.IsEven`, `IntegralLattice.IsUnimodular`, `IntegralLattice.IsPosDef`.
* `IntegralLattice.orthSum` — the orthogonal direct sum, notation `Γ ⊞ Λ`.
* `IntegralLattice.Isom` — isometry of lattices, notation `Γ ≃ₗᵢ Λ`.
* `IntegralLattice.ofGram` — the lattice `ℤⁿ` with a prescribed symmetric Gram matrix; the
  standard way to write down an explicit lattice.

## Implementation notes

The structure bundles its carrier as a field of type `Type` (universe `0`, not polymorphic):
every lattice occurring in the book is countable, and universe polymorphism would only cost
elaboration pain. The instance fields are re-exposed with `attribute [instance]`, the same
pattern Mathlib uses for concrete categories.

## References

Ebeling, *Lattices and Codes*, 3rd ed., §1.1.
-/

open scoped Matrix
open Module (Basis finrank finBasis)

/-- An **integral lattice**: a finitely generated free `ℤ`-module together with a symmetric
`ℤ`-valued bilinear form. No definiteness is assumed, so indefinite lattices such as the
hyperbolic plane are covered. See `BLUEPRINT.md` D1. -/
structure IntegralLattice : Type 1 where
  /-- The underlying `ℤ`-module. -/
  carrier : Type
  [addCommGroup : AddCommGroup carrier]
  [free : Module.Free ℤ carrier]
  [finite : Module.Finite ℤ carrier]
  /-- The bilinear form. -/
  bilin : carrier →ₗ[ℤ] carrier →ₗ[ℤ] ℤ
  /-- The form is symmetric. -/
  bilin_symm : ∀ x y, bilin x y = bilin y x

namespace IntegralLattice

attribute [instance] IntegralLattice.addCommGroup IntegralLattice.free IntegralLattice.finite

instance : CoeSort IntegralLattice Type := ⟨carrier⟩

/-- The form of a lattice is symmetric, in Mathlib's `LinearMap.IsSymm` packaging. -/
theorem isSymm_bilin (Γ : IntegralLattice) : Γ.bilin.IsSymm :=
  LinearMap.isSymm_def.mpr fun x y => Γ.bilin_symm x y

/-! ### Elementary bilinearity lemmas -/

section Elementary

variable {Γ : IntegralLattice} (x y z : Γ) (n : ℤ)

@[simp] theorem bilin_zero_left : Γ.bilin 0 y = 0 := LinearMap.map_zero₂ _ _
@[simp] theorem bilin_zero_right : Γ.bilin x 0 = 0 := map_zero _
@[simp] theorem bilin_add_left : Γ.bilin (x + y) z = Γ.bilin x z + Γ.bilin y z :=
  LinearMap.map_add₂ _ _ _ _
@[simp] theorem bilin_add_right : Γ.bilin x (y + z) = Γ.bilin x y + Γ.bilin x z := map_add _ _ _
@[simp] theorem bilin_neg_left : Γ.bilin (-x) y = -Γ.bilin x y := LinearMap.map_neg₂ _ _ _
@[simp] theorem bilin_neg_right : Γ.bilin x (-y) = -Γ.bilin x y := map_neg _ _
@[simp] theorem bilin_sub_left : Γ.bilin (x - y) z = Γ.bilin x z - Γ.bilin y z :=
  LinearMap.map_sub₂ _ _ _ _
@[simp] theorem bilin_sub_right : Γ.bilin x (y - z) = Γ.bilin x y - Γ.bilin x z := map_sub _ _ _
@[simp] theorem bilin_smul_left : Γ.bilin (n • x) y = n * Γ.bilin x y := by
  rw [LinearMap.map_smul₂, smul_eq_mul]
@[simp] theorem bilin_smul_right : Γ.bilin x (n • y) = n * Γ.bilin x y := by
  rw [map_smul, smul_eq_mul]

end Elementary

/-! ### The norm (`x²` in the book) -/

/-- `normSq x = ⟪x, x⟫`. Ebeling writes this `x²`. -/
def normSq {Γ : IntegralLattice} (x : Γ) : ℤ := Γ.bilin x x

@[simp] theorem normSq_def {Γ : IntegralLattice} (x : Γ) : normSq x = Γ.bilin x x := rfl

@[simp] theorem normSq_zero (Γ : IntegralLattice) : normSq (0 : Γ) = 0 := by simp [normSq]

@[simp] theorem normSq_neg {Γ : IntegralLattice} (x : Γ) : normSq (-x) = normSq x := by
  simp [normSq]

/-- Polarisation: `(x + y)² = x² + 2⟪x,y⟫ + y²`. -/
theorem normSq_add {Γ : IntegralLattice} (x y : Γ) :
    normSq (x + y) = normSq x + 2 * Γ.bilin x y + normSq y := by
  simp only [normSq, bilin_add_left, bilin_add_right, Γ.bilin_symm y x]
  ring

theorem normSq_sub {Γ : IntegralLattice} (x y : Γ) :
    normSq (x - y) = normSq x - 2 * Γ.bilin x y + normSq y := by
  simp only [normSq, bilin_sub_left, bilin_sub_right, Γ.bilin_symm y x]
  ring

theorem normSq_zsmul {Γ : IntegralLattice} (n : ℤ) (x : Γ) :
    normSq (n • x) = n ^ 2 * normSq x := by
  simp only [normSq, bilin_smul_left, bilin_smul_right]
  ring

/-! ### Rank and Gram matrices -/

variable (Γ Λ : IntegralLattice)

/-- The rank of a lattice: the rank of its underlying free `ℤ`-module. -/
noncomputable def rank : ℕ := finrank ℤ Γ

/-- A chosen `ℤ`-basis, indexed by `Fin Γ.rank`. -/
noncomputable def chooseBasis : Basis (Fin Γ.rank) ℤ Γ := finBasis ℤ Γ

theorem rank_eq_card {ι : Type*} [Fintype ι] (b : Basis ι ℤ Γ) : Γ.rank = Fintype.card ι :=
  Module.finrank_eq_card_basis b

/-- The **Gram matrix** of `Γ` in the basis `b`: the matrix of inner products of basis vectors. -/
noncomputable def gram {ι : Type*} (b : Basis ι ℤ Γ) : Matrix ι ι ℤ :=
  Matrix.of fun i j => Γ.bilin (b i) (b j)

@[simp] theorem gram_apply {ι : Type*} (b : Basis ι ℤ Γ) (i j : ι) :
    Γ.gram b i j = Γ.bilin (b i) (b j) := rfl

theorem gram_transpose {ι : Type*} (b : Basis ι ℤ Γ) : (Γ.gram b)ᵀ = Γ.gram b := by
  ext i j; simpa using (Γ.bilin_symm (b j) (b i))

theorem isSymm_gram {ι : Type*} (b : Basis ι ℤ Γ) : (Γ.gram b).IsSymm := Γ.gram_transpose b

theorem gram_eq_toMatrix {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℤ Γ) :
    Γ.gram b = LinearMap.BilinForm.toMatrix b Γ.bilin := by
  ext i j
  rw [gram_apply, LinearMap.BilinForm.toMatrix_apply]

/-- Row `i` of `G *ᵥ (coordinates of x)` is the inner product of the `i`-th basis vector with
`x`. This is the workhorse for translating between the form and its Gram matrix. -/
theorem gram_mulVec_repr {ι : Type*} [Fintype ι] (b : Basis ι ℤ Γ) (x : Γ) (i : ι) :
    (Γ.gram b *ᵥ (fun j => b.repr x j)) i = Γ.bilin (b i) x := by
  conv_rhs => rw [← b.sum_repr x]
  rw [map_sum]
  simp only [Matrix.mulVec, dotProduct, gram_apply, map_smul, smul_eq_mul]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-! ### The determinant -/

/-- The **discriminant** of a lattice: the determinant of any Gram matrix. It is independent of
the basis by `IntegralLattice.det_eq_gram_det`, because a change of basis over `ℤ` has
determinant `±1`. -/
noncomputable def det : ℤ := (Γ.gram Γ.chooseBasis).det

theorem det_eq_det_gram_chooseBasis : Γ.det = (Γ.gram Γ.chooseBasis).det := rfl

/-- Gram determinants in two bases with the *same* index type agree. -/
theorem gram_det_eq_gram_det {ι : Type*} [Fintype ι] [DecidableEq ι] (b c : Basis ι ℤ Γ) :
    (Γ.gram b).det = (Γ.gram c).det := by
  have key := LinearMap.BilinForm.toMatrix_mul_basis_toMatrix (b := b) c Γ.bilin
  have hflip : (b.toMatrix c) * (c.toMatrix b) = 1 := Basis.toMatrix_mul_toMatrix_flip b c
  have hmul : (b.toMatrix c).det * (c.toMatrix b).det = 1 := by
    rw [← Matrix.det_mul, hflip, Matrix.det_one]
  have hsq : (b.toMatrix c).det * (b.toMatrix c).det = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hmul with h | h <;> rw [h] <;> ring
  have hdet := congrArg Matrix.det key
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, ← gram_eq_toMatrix,
    ← gram_eq_toMatrix] at hdet
  calc (Γ.gram b).det
      = ((b.toMatrix c).det * (b.toMatrix c).det) * (Γ.gram b).det := by rw [hsq, one_mul]
    _ = (Γ.gram c).det := by rw [← hdet]; ring

/-- **The determinant is basis independent.** -/
@[simp] theorem det_eq_gram_det {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℤ Γ) :
    (Γ.gram b).det = Γ.det := by
  classical
  let e : Fin Γ.rank ≃ ι := Basis.indexEquiv Γ.chooseBasis b
  have hre : Γ.gram (b.reindex e.symm) = (Γ.gram b).submatrix e e := by
    ext i j; simp [gram, Basis.reindex_apply]
  have h1 : (Γ.gram (b.reindex e.symm)).det = (Γ.gram b).det := by
    rw [hre, Matrix.det_submatrix_equiv_self]
  rw [← h1, det, gram_det_eq_gram_det Γ Γ.chooseBasis (b.reindex e.symm)]

/-! ### Nondegeneracy -/

/-- A vector is orthogonal to the whole lattice exactly when the Gram matrix kills its
coordinate vector. -/
theorem bilin_eq_zero_iff_gram_mulVec {ι : Type*} [Fintype ι] (b : Basis ι ℤ Γ) (x : Γ) :
    (∀ y, Γ.bilin x y = 0) ↔ Γ.gram b *ᵥ (fun j => b.repr x j) = 0 := by
  constructor
  · intro h
    funext i
    rw [Γ.gram_mulVec_repr b x i, Γ.bilin_symm, h]
    rfl
  · intro h y
    have hflip : Γ.bilin.flip x = 0 := by
      refine b.ext fun j => ?_
      have := congrFun h j
      rw [Γ.gram_mulVec_repr b x j] at this
      simpa using this
    have := LinearMap.congr_fun hflip y
    rw [LinearMap.flip_apply, LinearMap.zero_apply] at this
    rw [Γ.bilin_symm]
    exact this

/-- Left-separation of the form is exactly nonvanishing of the discriminant. -/
theorem separatingLeft_iff_det_ne_zero : Γ.bilin.SeparatingLeft ↔ Γ.det ≠ 0 := by
  classical
  set b := Γ.chooseBasis with hb
  have hcoord : ∀ v : Fin Γ.rank → ℤ, (fun j => b.repr (b.equivFun.symm v) j) = v := by
    intro v
    funext j
    have hv : b.equivFun (b.equivFun.symm v) = v := b.equivFun.apply_symm_apply v
    rw [Basis.equivFun_apply] at hv
    exact congrFun hv j
  constructor
  · intro hsep hdet
    obtain ⟨v, hv, hMv⟩ := (Matrix.exists_mulVec_eq_zero_iff (M := Γ.gram b)).mpr
      (by rw [det_eq_gram_det]; exact hdet)
    refine hv ?_
    have hx0 : b.equivFun.symm v = 0 :=
      hsep _ ((Γ.bilin_eq_zero_iff_gram_mulVec b _).mpr (by rw [hcoord v]; exact hMv))
    have := hcoord v
    rw [hx0] at this
    rw [← this]
    funext j
    simp
  · intro hdet x hx
    by_contra hne
    have hMv := (Γ.bilin_eq_zero_iff_gram_mulVec b x).mp hx
    have hv : (fun j => b.repr x j) ≠ 0 := by
      intro h
      apply hne
      have hr : b.repr x = 0 := by ext j; exact congrFun h j
      have := congrArg b.repr.symm hr
      simpa using this
    exact hdet (by
      rw [← det_eq_gram_det Γ b]
      exact (Matrix.exists_mulVec_eq_zero_iff (M := Γ.gram b)).mp ⟨_, hv, hMv⟩)

/-- The form of a lattice is nondegenerate exactly when the discriminant is nonzero. -/
theorem nondegenerate_iff_det_ne_zero : Γ.bilin.Nondegenerate ↔ Γ.det ≠ 0 := by
  constructor
  · intro h
    exact (Γ.separatingLeft_iff_det_ne_zero).mp h.1
  · intro h
    refine ⟨(Γ.separatingLeft_iff_det_ne_zero).mpr h, ?_⟩
    intro y hy
    refine (Γ.separatingLeft_iff_det_ne_zero).mpr h y ?_
    intro z
    rw [Γ.bilin_symm]
    exact hy z

/-! ### Even, unimodular, positive definite -/

/-- A lattice is **even** when every vector has even norm. Ebeling §1.1. -/
def IsEven : Prop := ∀ x : Γ, (2 : ℤ) ∣ normSq x

/-- A lattice is **unimodular** when its discriminant is a unit of `ℤ`, i.e. `±1`. -/
def IsUnimodular : Prop := IsUnit Γ.det

/-- A lattice is **positive definite** when every nonzero vector has positive norm. -/
def IsPosDef : Prop := ∀ x : Γ, x ≠ 0 → 0 < normSq x

variable {Γ Λ}

theorem isUnimodular_iff : Γ.IsUnimodular ↔ Γ.det = 1 ∨ Γ.det = -1 := Int.isUnit_iff

theorem IsUnimodular.det_ne_zero (h : Γ.IsUnimodular) : Γ.det ≠ 0 := h.ne_zero

theorem IsEven.two_dvd (h : Γ.IsEven) (x : Γ) : (2 : ℤ) ∣ Γ.bilin x x := h x

theorem IsPosDef.normSq_eq_zero_iff (h : Γ.IsPosDef) {x : Γ} : normSq x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    by_contra hne
    exact absurd hx (ne_of_gt (h x hne))
  · rintro rfl; simp

theorem IsPosDef.normSq_nonneg (h : Γ.IsPosDef) (x : Γ) : 0 ≤ normSq x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · exact (h x hx).le

/-- **Cauchy–Schwarz** for a positive definite lattice, proved entirely inside `ℤ`: no real or
rational scalars are needed. This is what makes `finite_normSq_le` an algebraic statement. -/
theorem IsPosDef.bilin_sq_le (h : Γ.IsPosDef) (x y : Γ) :
    (Γ.bilin x y) ^ 2 ≤ normSq x * normSq y := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have hxx : 0 < normSq x := h x hx
    have key : normSq (normSq x • y - Γ.bilin x y • x)
        = normSq x * (normSq x * normSq y - (Γ.bilin x y) ^ 2) := by
      rw [normSq_sub, normSq_zsmul, normSq_zsmul, bilin_smul_left, bilin_smul_right,
        Γ.bilin_symm y x]
      simp only [normSq_def]
      ring
    have hnn : 0 ≤ normSq (normSq x • y - Γ.bilin x y • x) :=
      h.normSq_nonneg _
    rw [key] at hnn
    nlinarith [hxx, hnn]

theorem IsPosDef.separatingLeft (h : Γ.IsPosDef) : Γ.bilin.SeparatingLeft := fun x hx =>
  h.normSq_eq_zero_iff.mp (hx x)

theorem IsPosDef.nondegenerate (h : Γ.IsPosDef) : Γ.bilin.Nondegenerate :=
  (nondegenerate_iff_det_ne_zero Γ).mpr
    ((separatingLeft_iff_det_ne_zero Γ).mp h.separatingLeft)

theorem IsPosDef.det_ne_zero (h : Γ.IsPosDef) : Γ.det ≠ 0 :=
  (separatingLeft_iff_det_ne_zero Γ).mp h.separatingLeft

/-! ### Isometries -/

/-- An **isometry** of integral lattices: a `ℤ`-linear isomorphism preserving the forms. -/
structure Isom (Γ Λ : IntegralLattice) extends Γ ≃ₗ[ℤ] Λ where
  /-- The underlying linear equivalence preserves the bilinear forms. -/
  map_bilin' : ∀ x y : Γ, Λ.bilin (toLinearEquiv x) (toLinearEquiv y) = Γ.bilin x y

@[inherit_doc] infixl:25 " ≃ₗᵢ " => Isom

namespace Isom

instance : CoeFun (Γ ≃ₗᵢ Λ) fun _ => Γ → Λ := ⟨fun f => f.toLinearEquiv⟩

@[simp] theorem coe_toLinearEquiv (f : Γ ≃ₗᵢ Λ) (x : Γ) : f.toLinearEquiv x = f x := rfl

@[simp] theorem map_bilin (f : Γ ≃ₗᵢ Λ) (x y : Γ) : Λ.bilin (f x) (f y) = Γ.bilin x y :=
  f.map_bilin' x y

@[simp] theorem map_normSq (f : Γ ≃ₗᵢ Λ) (x : Γ) : normSq (f x) = normSq x := f.map_bilin' x x

/-- The identity isometry. -/
def refl (Γ : IntegralLattice) : Γ ≃ₗᵢ Γ where
  toLinearEquiv := LinearEquiv.refl ℤ Γ
  map_bilin' _ _ := rfl

/-- The inverse of an isometry. -/
def symm (f : Γ ≃ₗᵢ Λ) : Λ ≃ₗᵢ Γ where
  toLinearEquiv := f.toLinearEquiv.symm
  map_bilin' x y := by
    have h := f.map_bilin' (f.toLinearEquiv.symm x) (f.toLinearEquiv.symm y)
    rw [f.toLinearEquiv.apply_symm_apply, f.toLinearEquiv.apply_symm_apply] at h
    exact h.symm

@[simp] theorem symm_apply (f : Γ ≃ₗᵢ Λ) (x : Λ) : f.symm x = f.toLinearEquiv.symm x := rfl

@[simp] theorem apply_symm_apply (f : Γ ≃ₗᵢ Λ) (x : Λ) : f (f.symm x) = x :=
  f.toLinearEquiv.apply_symm_apply x

@[simp] theorem symm_apply_apply (f : Γ ≃ₗᵢ Λ) (x : Γ) : f.symm (f x) = x :=
  f.toLinearEquiv.symm_apply_apply x

/-- Composition of isometries. -/
def trans {Ξ : IntegralLattice} (f : Γ ≃ₗᵢ Λ) (g : Λ ≃ₗᵢ Ξ) : Γ ≃ₗᵢ Ξ where
  toLinearEquiv := f.toLinearEquiv.trans g.toLinearEquiv
  map_bilin' x y := by
    show Ξ.bilin (g (f x)) (g (f y)) = Γ.bilin x y
    rw [g.map_bilin, f.map_bilin]

/-- An isometry carries a basis to a basis with the same Gram matrix. -/
theorem gram_map {ι : Type*} (f : Γ ≃ₗᵢ Λ) (b : Basis ι ℤ Γ) :
    Λ.gram (b.map f.toLinearEquiv) = Γ.gram b := by
  ext i j; simp [gram]

theorem rank_eq (f : Γ ≃ₗᵢ Λ) : Γ.rank = Λ.rank := by
  simpa [rank] using f.toLinearEquiv.finrank_eq

theorem det_eq (f : Γ ≃ₗᵢ Λ) : Γ.det = Λ.det := by
  classical
  rw [← det_eq_gram_det Γ Γ.chooseBasis,
    ← det_eq_gram_det Λ (Γ.chooseBasis.map f.toLinearEquiv), f.gram_map]

theorem isEven (f : Γ ≃ₗᵢ Λ) (h : Γ.IsEven) : Λ.IsEven := fun x => by
  have := h (f.symm x)
  rwa [← f.map_normSq (f.symm x), f.apply_symm_apply] at this

theorem isPosDef (f : Γ ≃ₗᵢ Λ) (h : Γ.IsPosDef) : Λ.IsPosDef := fun x hx => by
  have hne : f.symm x ≠ 0 := by
    intro hc
    apply hx
    rw [← f.apply_symm_apply x, hc]
    exact map_zero f.toLinearEquiv
  have := h (f.symm x) hne
  rwa [← f.map_normSq (f.symm x), f.apply_symm_apply] at this

theorem isUnimodular (f : Γ ≃ₗᵢ Λ) (h : Γ.IsUnimodular) : Λ.IsUnimodular := by
  unfold IsUnimodular at h ⊢
  rwa [← f.det_eq]

end Isom

/-! ### The orthogonal direct sum -/

variable (Γ Λ)

/-- The **orthogonal direct sum** `Γ ⊞ Λ`: the module `Γ × Λ` with the sum of the two forms.
Ebeling writes this `Γ ⊥ Λ`. -/
def orthSum : IntegralLattice where
  carrier := Γ × Λ
  bilin :=
    Γ.bilin.compl₁₂ (LinearMap.fst ℤ Γ Λ) (LinearMap.fst ℤ Γ Λ) +
      Λ.bilin.compl₁₂ (LinearMap.snd ℤ Γ Λ) (LinearMap.snd ℤ Γ Λ)
  bilin_symm x y := by
    simp only [LinearMap.add_apply, LinearMap.compl₁₂_apply, LinearMap.fst_apply,
      LinearMap.snd_apply]
    rw [Γ.bilin_symm x.1 y.1, Λ.bilin_symm x.2 y.2]

@[inherit_doc] infixl:65 " ⊞ " => orthSum

@[simp] theorem orthSum_bilin (x y : Γ × Λ) :
    (Γ ⊞ Λ).bilin x y = Γ.bilin x.1 y.1 + Λ.bilin x.2 y.2 := rfl

@[simp] theorem orthSum_normSq (x : Γ × Λ) :
    normSq (Γ := Γ ⊞ Λ) x = normSq x.1 + normSq x.2 := rfl

/-- Value of the product basis of `Γ ⊞ Λ` on a left index. -/
theorem prod_basis_inl {ι κ : Type*} (b : Basis ι ℤ Γ) (c : Basis κ ℤ Λ) (i : ι) :
    (b.prod c) (Sum.inl i) = (b i, 0) := by
  have h1 : ((b.prod c) (Sum.inl i)).1 = b i := Basis.prod_apply_inl_fst b c i
  have h2 : ((b.prod c) (Sum.inl i)).2 = 0 := Basis.prod_apply_inl_snd b c i
  calc (b.prod c) (Sum.inl i)
      = (((b.prod c) (Sum.inl i)).1, ((b.prod c) (Sum.inl i)).2) := rfl
    _ = (b i, 0) := by rw [h1, h2]

/-- Value of the product basis of `Γ ⊞ Λ` on a right index. -/
theorem prod_basis_inr {ι κ : Type*} (b : Basis ι ℤ Γ) (c : Basis κ ℤ Λ) (i : κ) :
    (b.prod c) (Sum.inr i) = (0, c i) := by
  have h1 : ((b.prod c) (Sum.inr i)).1 = 0 := Basis.prod_apply_inr_fst b c i
  have h2 : ((b.prod c) (Sum.inr i)).2 = c i := Basis.prod_apply_inr_snd b c i
  calc (b.prod c) (Sum.inr i)
      = (((b.prod c) (Sum.inr i)).1, ((b.prod c) (Sum.inr i)).2) := rfl
    _ = (0, c i) := by rw [h1, h2]

/-- The Gram matrix of an orthogonal sum in a product basis is block diagonal. -/
theorem gram_orthSum {ι κ : Type*} (b : Basis ι ℤ Γ) (c : Basis κ ℤ Λ) :
    (Γ ⊞ Λ).gram (b.prod c) = Matrix.fromBlocks (Γ.gram b) 0 0 (Λ.gram c) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · show Γ.bilin ((b.prod c) (Sum.inl i)).1 ((b.prod c) (Sum.inl j)).1
        + Λ.bilin ((b.prod c) (Sum.inl i)).2 ((b.prod c) (Sum.inl j)).2 = _
    rw [prod_basis_inl, prod_basis_inl]
    simp
  · show Γ.bilin ((b.prod c) (Sum.inl i)).1 ((b.prod c) (Sum.inr j)).1
        + Λ.bilin ((b.prod c) (Sum.inl i)).2 ((b.prod c) (Sum.inr j)).2 = _
    rw [prod_basis_inl, prod_basis_inr]
    simp
  · show Γ.bilin ((b.prod c) (Sum.inr i)).1 ((b.prod c) (Sum.inl j)).1
        + Λ.bilin ((b.prod c) (Sum.inr i)).2 ((b.prod c) (Sum.inl j)).2 = _
    rw [prod_basis_inr, prod_basis_inl]
    simp
  · show Γ.bilin ((b.prod c) (Sum.inr i)).1 ((b.prod c) (Sum.inr j)).1
        + Λ.bilin ((b.prod c) (Sum.inr i)).2 ((b.prod c) (Sum.inr j)).2 = _
    rw [prod_basis_inr, prod_basis_inr]
    simp

theorem rank_orthSum : (Γ ⊞ Λ).rank = Γ.rank + Λ.rank := by
  show finrank ℤ (Γ.carrier × Λ.carrier) = finrank ℤ Γ.carrier + finrank ℤ Λ.carrier
  exact Module.finrank_prod

theorem det_orthSum : (Γ ⊞ Λ).det = Γ.det * Λ.det := by
  classical
  rw [← det_eq_gram_det (Γ ⊞ Λ) (Γ.chooseBasis.prod Λ.chooseBasis), gram_orthSum,
    Matrix.det_fromBlocks_zero₂₁, det_eq_det_gram_chooseBasis, det_eq_det_gram_chooseBasis]

variable {Γ Λ}

theorem isEven_orthSum (hΓ : Γ.IsEven) (hΛ : Λ.IsEven) : (Γ ⊞ Λ).IsEven := fun x =>
  dvd_add (hΓ x.1) (hΛ x.2)

theorem isPosDef_orthSum (hΓ : Γ.IsPosDef) (hΛ : Λ.IsPosDef) : (Γ ⊞ Λ).IsPosDef := by
  intro x hx
  rw [show normSq (Γ := Γ ⊞ Λ) x = normSq x.1 + normSq x.2 from rfl]
  rcases eq_or_ne x.1 0 with h1 | h1
  · have h2 : x.2 ≠ 0 := fun h2 => hx (Prod.ext h1 h2)
    have := hΛ x.2 h2
    rw [h1]
    simpa using this
  · exact add_pos_of_pos_of_nonneg (hΓ x.1 h1) (hΛ.normSq_nonneg x.2)

theorem isUnimodular_orthSum (hΓ : Γ.IsUnimodular) (hΛ : Λ.IsUnimodular) :
    (Γ ⊞ Λ).IsUnimodular := by
  unfold IsUnimodular at hΓ hΛ ⊢
  rw [det_orthSum]
  exact hΓ.mul hΛ

/-! ### Explicit lattices from Gram matrices -/

/-- The lattice `ℤⁿ` equipped with the form whose Gram matrix in the standard basis is `G`.
This is the standard way to write down an explicit lattice (the `ADE` models of §1.4, the
hyperbolic plane, …). -/
def ofGram {n : ℕ} (G : Matrix (Fin n) (Fin n) ℤ) (hG : G.IsSymm) : IntegralLattice where
  carrier := Fin n → ℤ
  bilin := Matrix.toBilin' G
  bilin_symm x y := by
    rw [Matrix.toBilin'_apply', Matrix.toBilin'_apply']
    calc
      x ⬝ᵥ G *ᵥ y = x ⬝ᵥ Gᵀ *ᵥ y := by rw [hG.eq]
      _ = y ⬝ᵥ G *ᵥ x := Matrix.dotProduct_transpose_mulVec G x y

@[simp] theorem ofGram_bilin {n : ℕ} (G : Matrix (Fin n) (Fin n) ℤ) (hG : G.IsSymm)
    (x y : Fin n → ℤ) : (ofGram G hG).bilin x y = x ⬝ᵥ G *ᵥ y :=
  Matrix.toBilin'_apply' G x y

@[simp] theorem gram_ofGram {n : ℕ} (G : Matrix (Fin n) (Fin n) ℤ) (hG : G.IsSymm) :
    (ofGram G hG).gram (Pi.basisFun ℤ (Fin n)) = G := by
  ext i j
  show Matrix.toBilin' G (Pi.basisFun ℤ (Fin n) i) (Pi.basisFun ℤ (Fin n) j) = G i j
  rw [Pi.basisFun_apply, Pi.basisFun_apply, Matrix.toBilin'_single]

@[simp] theorem det_ofGram {n : ℕ} (G : Matrix (Fin n) (Fin n) ℤ) (hG : G.IsSymm) :
    (ofGram G hG).det = G.det := by
  rw [← det_eq_gram_det _ (Pi.basisFun ℤ (Fin n)), gram_ofGram]

@[simp] theorem rank_ofGram {n : ℕ} (G : Matrix (Fin n) (Fin n) ℤ) (hG : G.IsSymm) :
    (ofGram G hG).rank = n := by
  rw [rank_eq_card _ (Pi.basisFun ℤ (Fin n))]
  simp

/-- The form of `ofGram G hG`, written out. Stated with the arguments typed as elements of the
lattice (rather than of `Fin n → ℤ`) so that it applies directly in goals produced by `IsEven`,
`IsPosDef` and friends. -/
theorem ofGram_bilin_sum {n : ℕ} (G : Matrix (Fin n) (Fin n) ℤ) (hG : G.IsSymm)
    (x y : ofGram G hG) : (ofGram G hG).bilin x y = ∑ i, ∑ j, x i * G i j * y j :=
  Matrix.toBilin'_apply G x y

theorem ofGram_normSq {n : ℕ} (G : Matrix (Fin n) (Fin n) ℤ) (hG : G.IsSymm)
    (x : ofGram G hG) : normSq x = ∑ i, ∑ j, x i * G i j * x j :=
  ofGram_bilin_sum G hG x x

theorem ofGram_eq_zero_iff {n : ℕ} (G : Matrix (Fin n) (Fin n) ℤ) (hG : G.IsSymm)
    (x : ofGram G hG) : x = 0 ↔ ∀ i, x i = 0 :=
  ⟨fun h i => by rw [h]; rfl, fun h => funext fun i => h i⟩

/-! ### Usage sketches

`BLUEPRINT.md` §9 asks M1 to carry downstream *usage sketches* as a smoke test of the API before
Tier 2 opens. These are `example`s, not public definitions: the explicit `Aₙ, Dₙ, E₆₋₈` models are
M9's to name, and the hyperbolic plane is M32's. What is tested here is that a lattice can
actually be written down, that `det`, `rank`, `IsEven`, `IsPosDef` and `IsUnimodular` can be
decided by hand on such a presentation, and that `orthSum` and `Isom` compose with them.
-/

section UsageSketches

private theorem isSymm_fin_one (a : ℤ) : (!![a] : Matrix (Fin 1) (Fin 1) ℤ).IsSymm := by
  ext i j
  fin_cases i
  fin_cases j
  rfl

private theorem isSymm_fin_two (a b : ℤ) : (!![a, b; b, a] : Matrix (Fin 2) (Fin 2) ℤ).IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The `A₁` lattice: `ℤ` with the form `2xy`. -/
private noncomputable def sketchA1 : IntegralLattice := ofGram !![2] (isSymm_fin_one 2)

/-- The hyperbolic plane `U`: `ℤ²` with the form `x₁y₂ + x₂y₁`. -/
private noncomputable def sketchU : IntegralLattice := ofGram !![0, 1; 1, 0] (isSymm_fin_two 0 1)

/-- The odd unimodular lattice `ℤ` with the standard form `xy`. -/
private noncomputable def sketchZ : IntegralLattice := ofGram !![1] (isSymm_fin_one 1)

private theorem sketchA1_normSq (x : sketchA1) : normSq x = 2 * (x 0 * x 0) := by
  have h := ofGram_normSq !![2] (isSymm_fin_one 2) x
  rw [show normSq x = ∑ i, ∑ j, x i * (!![2] : Matrix (Fin 1) (Fin 1) ℤ) i j * x j from h]
  simp
  ring

private theorem sketchU_normSq (x : sketchU) : normSq x = 2 * (x 0 * x 1) := by
  have h := ofGram_normSq !![0, 1; 1, 0] (isSymm_fin_two 0 1) x
  rw [show normSq x = ∑ i, ∑ j, x i * (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ) i j * x j from h]
  simp [Fin.sum_univ_two]
  ring

private theorem sketchZ_normSq (x : sketchZ) : normSq x = x 0 * x 0 := by
  have h := ofGram_normSq !![1] (isSymm_fin_one 1) x
  rw [show normSq x = ∑ i, ∑ j, x i * (!![1] : Matrix (Fin 1) (Fin 1) ℤ) i j * x j from h]
  simp

-- Sketch 1: rank and determinant of an explicitly presented lattice.
example : sketchA1.rank = 1 := rank_ofGram _ _
example : sketchA1.det = 2 := (det_ofGram _ _).trans (Matrix.det_fin_one_of 2)

-- Sketch 2: evenness and positive definiteness are checkable on the presentation.
example : sketchA1.IsEven := fun x => ⟨x 0 * x 0, sketchA1_normSq x⟩

example : sketchA1.IsPosDef := by
  intro x hx
  rw [sketchA1_normSq]
  have hx0 : x 0 ≠ 0 := by
    intro h
    exact hx ((ofGram_eq_zero_iff _ _ x).mpr fun i => by fin_cases i; exact h)
  have : 0 < x 0 * x 0 := mul_self_pos.mpr hx0
  omega

-- Sketch 3: an indefinite unimodular even lattice; `IsPosDef` genuinely fails for it.
example : sketchU.det = -1 := by
  rw [show sketchU.det = (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ).det from det_ofGram _ _,
    Matrix.det_fin_two_of]
  ring

example : sketchU.IsUnimodular := by
  rw [IsUnimodular,
    show sketchU.det = (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ).det from det_ofGram _ _,
    Matrix.det_fin_two_of]
  norm_num

example : sketchU.IsEven := fun x => ⟨x 0 * x 1, sketchU_normSq x⟩

example : ¬ sketchU.IsPosDef := by
  intro h
  have hne : (![1, 0] : sketchU) ≠ 0 := by
    intro hc
    have h0 := (ofGram_eq_zero_iff !![0, 1; 1, 0] (isSymm_fin_two 0 1) ![1, 0]).mp hc 0
    simp at h0
  have hpos := h ![1, 0] hne
  rw [sketchU_normSq ![1, 0]] at hpos
  simp at hpos

-- Sketch 4: `ofGram !![1]` is unimodular but *not* even — the two conditions are independent.
example : sketchZ.IsUnimodular := by
  rw [IsUnimodular, show sketchZ.det = (!![1] : Matrix (Fin 1) (Fin 1) ℤ).det from det_ofGram _ _,
    Matrix.det_fin_one_of]
  exact isUnit_one

example : ¬ sketchZ.IsEven := by
  intro h
  obtain ⟨k, hk⟩ := h ![1]
  rw [sketchZ_normSq ![1]] at hk
  simp at hk
  omega

-- Sketch 5: orthogonal sums multiply determinants and add ranks, and preserve evenness.
example : (sketchA1 ⊞ sketchA1).det = 4 := by
  rw [det_orthSum, show sketchA1.det = (!![2] : Matrix (Fin 1) (Fin 1) ℤ).det from det_ofGram _ _,
    Matrix.det_fin_one_of]
  ring

example : (sketchA1 ⊞ sketchU).rank = 3 := by
  rw [rank_orthSum, show sketchA1.rank = 1 from rank_ofGram _ _,
    show sketchU.rank = 2 from rank_ofGram _ _]

example : (sketchA1 ⊞ sketchA1).IsEven :=
  isEven_orthSum (fun x => ⟨x 0 * x 0, sketchA1_normSq x⟩)
    (fun x => ⟨x 0 * x 0, sketchA1_normSq x⟩)

-- Sketch 6: isometry invariants transport, so classification statements are expressible.
example (Γ' Λ' : IntegralLattice) (f : Γ' ≃ₗᵢ Λ') (h : Γ'.det = 2) : Λ'.det = 2 := by
  rw [← f.det_eq]; exact h

example (Λ' : IntegralLattice) (f : sketchA1 ≃ₗᵢ Λ') : Λ'.IsEven ∧ Λ'.det = 2 := by
  refine ⟨f.isEven fun x => ⟨x 0 * x 0, sketchA1_normSq x⟩, ?_⟩
  rw [← f.det_eq, show sketchA1.det = (!![2] : Matrix (Fin 1) (Fin 1) ℤ).det from det_ofGram _ _,
    Matrix.det_fin_one_of]

-- Sketch 7: the determinant may be computed in *any* basis, not just the chosen one.
example (Γ' : IntegralLattice) {ι : Type} [Fintype ι] [DecidableEq ι] (b : Basis ι ℤ Γ')
    (h : (Γ'.gram b).det = 1) : Γ'.IsUnimodular := by
  rw [IsUnimodular, ← det_eq_gram_det Γ' b, h]
  exact isUnit_one

-- Sketch 8: nondegeneracy is available from the determinant, as Layer B (M4) will need.
example (Γ' : IntegralLattice) (h : Γ'.IsPosDef) : Γ'.bilin.Nondegenerate := h.nondegenerate

end UsageSketches

end IntegralLattice
