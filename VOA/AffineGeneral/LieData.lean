/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Foundations.AffineLie
import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
# Finite Lie data for the general affine VOA

The general affine construction needs, for a Lie algebra `𝔤` with invariant form `κ`, a finite basis
`generator : ι → 𝔤` and a `κ`-dual family `dualGenerator`.  This file packages them in `LieData`
and proves the finite identities used by the Sugawara construction.  The names match the sl₃ files
(`VOA/Examples/AffineSl3Structure.lean`, `AffineSl3SugawaraTensor.lean`) so that the downstream
ports change only the index type:

* `structureConstant a b c` and `generator_bracket`;
* `formTable`, `kappaInv` (the inverse Gram matrix), `kappaInv_symm`, `kappa_symm`, `kappaInv_kappa`,
  `dualGenerator_expand`;
* `graised`, `graised_eq_form`, `graised_antisymm`, `kappaInv_fabc_antisymm_zero`;
* `structureConstant_diag_sum` (`tr ad x = 0`, from invariance alone);
* `trace_kappaInv_formTable` (`= card ι = dim 𝔤`);
* `struct_casimir_contract` from the **Casimir hypothesis** `casimir : ∑ i, ⁅gᵢ, ⁅gᵢ∨, x⁆⁆ = (2h) • x`.

The only Lie-theoretic input that is not automatic is `casimir`; for the sl₃ trace form it is
`AffineSl3.adjoint_casimir` with `h = 3`.
-/

namespace VOA.AffineGeneral

open VOA.AffineLie

noncomputable section

/-- Finite Lie data for the affine construction: a basis, a `κ`-dual family, and the adjoint
Casimir eigenvalue `2h` (`h` = the dual Coxeter number in the normalization of `κ`). -/
structure LieData {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (κ : LinearMap.BilinForm ℂ 𝔤) (ι : Type*) [Fintype ι] [DecidableEq ι] where
  /-- `κ` is symmetric and ad-invariant. -/
  invariant : κ.IsInvariant
  /-- A basis of `𝔤`. -/
  basis : Module.Basis ι ℂ 𝔤
  /-- The `κ`-dual family. -/
  dual : ι → 𝔤
  /-- Duality: `κ(gᵢ, gⱼ∨) = δᵢⱼ`. -/
  pair : ∀ i j, κ (basis i) (dual j) = if i = j then 1 else 0
  /-- The dual Coxeter number (in the normalization of `κ`). -/
  h : ℂ
  /-- The adjoint Casimir acts by `2h`. -/
  casimir : ∀ x : 𝔤, ∑ i, ⁅basis i, ⁅dual i, x⁆⁆ = (2 * h) • x

variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
variable {κ : LinearMap.BilinForm ℂ 𝔤}
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (D : LieData κ ι)

namespace LieData

/-- The basis generators. -/
abbrev generator (i : ι) : 𝔤 := D.basis i

/-- The dual generators. -/
abbrev dualGenerator (i : ι) : 𝔤 := D.dual i

/-- Coordinates in the basis. -/
abbrev coordinates (x : 𝔤) (i : ι) : ℂ := D.basis.repr x i

theorem reconstruct (x : 𝔤) : ∑ i, D.coordinates x i • D.generator i = x := by
  simpa [coordinates, generator] using D.basis.sum_repr x

theorem coordinates_generator (i j : ι) : D.coordinates (D.generator i) j = if i = j then 1 else 0 := by
  simp [coordinates, generator, Finsupp.single_apply]

/-- Pairing with a dual generator extracts the coordinate. -/
theorem form_dual_coordinates (x : 𝔤) (j : ι) : κ x (D.dualGenerator j) = D.coordinates x j := by
  conv_lhs => rw [← D.reconstruct x]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    generator, dualGenerator, D.pair, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

/-- Structure constants `⁅gₐ, g_b⁆ = ∑_c f^{ab}_c g_c`. -/
def structureConstant (a b c : ι) : ℂ := D.coordinates ⁅D.generator a, D.generator b⁆ c

theorem generator_bracket (a b : ι) :
    ⁅D.generator a, D.generator b⁆ = ∑ c, D.structureConstant a b c • D.generator c :=
  (D.reconstruct _).symm

theorem structureConstant_antisymm (a b c : ι) :
    D.structureConstant a b c = -D.structureConstant b a c := by
  simp only [structureConstant, coordinates, ← lie_skew (D.generator a) (D.generator b), map_neg,
    Finsupp.neg_apply]

/-- The Gram matrix. -/
def formTable (a b : ι) : ℂ := κ (D.generator a) (D.generator b)

theorem form_generator_eq_table (a b : ι) : κ (D.generator a) (D.generator b) = D.formTable a b := rfl

theorem kappa_symm (a b : ι) : D.formTable a b = D.formTable b a := D.invariant.symm _ _

/-- The inverse Gram matrix: coordinates of the dual generators. -/
def kappaInv (a c : ι) : ℂ := D.coordinates (D.dualGenerator a) c

theorem dualGenerator_expand (a : ι) :
    D.dualGenerator a = ∑ b, D.kappaInv a b • D.generator b :=
  (D.reconstruct _).symm

theorem kappaInv_eq_form (a c : ι) : D.kappaInv a c = κ (D.dualGenerator a) (D.dualGenerator c) :=
  (D.form_dual_coordinates _ c).symm

theorem kappaInv_symm (a b : ι) : D.kappaInv a b = D.kappaInv b a := by
  rw [kappaInv_eq_form, kappaInv_eq_form, D.invariant.symm]

/-- `formTable · kappaInv = 1`. -/
theorem kappaInv_kappa (a c : ι) :
    (∑ b, D.formTable a b * D.kappaInv b c) = if a = c then 1 else 0 := by
  have h : κ (D.generator a) (D.dualGenerator c) = if a = c then 1 else 0 := D.pair a c
  rw [D.dualGenerator_expand c] at h
  simp only [map_sum, map_smul, smul_eq_mul] at h
  rw [← h]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [D.kappaInv_symm b c, formTable]
  ring

/-- Structure constants with the first index raised by `κ⁻¹`. -/
def graised (a c d : ι) : ℂ := ∑ b, D.kappaInv a b * D.structureConstant b c d

theorem graised_eq_form (a c d : ι) :
    D.graised a c d = κ ⁅D.dualGenerator a, D.generator c⁆ (D.dualGenerator d) := by
  rw [D.dualGenerator_expand a, sum_lie]
  simp only [smul_lie, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    D.form_dual_coordinates, smul_eq_mul]
  rfl

theorem graised_antisymm (a c d : ι) : D.graised a c d = -D.graised d c a := by
  rw [D.graised_eq_form, D.graised_eq_form, D.invariant.invariant]
  rw [← lie_skew (D.generator c) (D.dualGenerator d), map_neg]
  rw [D.invariant.symm (D.dualGenerator a) ⁅D.dualGenerator d, D.generator c⁆]

theorem kappaInv_fabc_antisymm_zero (d : ι) :
    (∑ a, ∑ b, D.kappaInv a b * D.structureConstant a b d) = 0 := by
  have h : (∑ a, ∑ b, D.kappaInv a b * D.structureConstant a b d) =
      -(∑ a, ∑ b, D.kappaInv a b * D.structureConstant a b d) := by
    conv_lhs => rw [Finset.sum_comm]
    simp only [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [D.kappaInv_symm b a, D.structureConstant_antisymm b a d]
    ring
  have h2 : (2 : ℂ) * (∑ a, ∑ b, D.kappaInv a b * D.structureConstant a b d) = 0 := by
    linear_combination h
  exact (mul_eq_zero.mp h2).resolve_left two_ne_zero

/-- The coordinate form of the adjoint Casimir: the structure contraction equals `2h · δ`. -/
theorem struct_casimir_contract (c e : ι) :
    (∑ a, ∑ d, (∑ b, D.kappaInv a b * D.structureConstant b c d) * D.structureConstant a d e) =
      if c = e then 2 * D.h else 0 := by
  have h := congrArg (fun x : 𝔤 => D.coordinates x e) (D.casimir (D.generator c))
  simp only [D.dualGenerator_expand, sum_lie, smul_lie, lie_sum, lie_smul, D.generator_bracket,
    map_sum, map_smul, Finsupp.coe_finset_sum, Finsupp.coe_smul, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, coordinates] at h
  simp only [generator, Module.Basis.repr_self, Finsupp.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.mul_sum] at h
  convert h using 1
  · apply Finset.sum_congr rfl
    intro a _
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro d _
    simp only [structureConstant, coordinates, generator]
    ring

/-- `tr (ad x) = 0` for every `x`, from invariance and symmetry of `κ`.  In coordinates:
`∑ₐ f^{a c}_a = 0`. -/
theorem structureConstant_diag_sum (c : ι) : (∑ a, D.structureConstant a c a) = 0 := by
  -- S = ∑ₐ κ(⁅x, gₐ⁆, gₐ∨) with x = g_c
  set x := D.generator c
  have hS : (∑ a, D.structureConstant a c a) = -∑ a, κ ⁅x, D.generator a⁆ (D.dualGenerator a) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [D.form_dual_coordinates, structureConstant, ← lie_skew, coordinates, coordinates,
      map_neg, Finsupp.neg_apply]
  -- invariance: κ(⁅x,gₐ⁆, gₐ∨) = -κ(gₐ, ⁅x, gₐ∨⁆)
  have hinv : ∀ a, κ ⁅x, D.generator a⁆ (D.dualGenerator a) =
      -κ (D.generator a) ⁅x, D.dualGenerator a⁆ := by
    intro a
    rw [← lie_skew x (D.generator a), map_neg, LinearMap.neg_apply, D.invariant.invariant]
  -- and ∑ₐ κ(gₐ, ⁅x, gₐ∨⁆) = ∑ₐ κ(⁅x,gₐ⁆, gₐ∨)
  have hswap : (∑ a, κ (D.generator a) ⁅x, D.dualGenerator a⁆) =
      ∑ a, κ ⁅x, D.generator a⁆ (D.dualGenerator a) := by
    simp only [D.dualGenerator_expand, lie_sum, lie_smul, map_sum, map_smul, smul_eq_mul]
    -- κ(gₐ, ⁅x, g_b⁆) = κ(⁅x,g_b⁆, gₐ), and ∑ₐ kappaInv a b κ(y, gₐ) = κ(y, g_b∨)
    have hy : ∀ b, (∑ a, D.kappaInv a b * κ (D.generator a) ⁅x, D.generator b⁆) =
        ∑ a, D.kappaInv b a * κ ⁅x, D.generator b⁆ (D.generator a) := by
      intro b
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [D.kappaInv_symm a b, D.invariant.symm]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => hy b
  have h2 : (∑ a, κ ⁅x, D.generator a⁆ (D.dualGenerator a)) =
      -(∑ a, κ ⁅x, D.generator a⁆ (D.dualGenerator a)) := by
    conv_lhs => rw [← hswap]
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun a _ => by rw [hinv a, neg_neg]
  have h3 : (∑ a, κ ⁅x, D.generator a⁆ (D.dualGenerator a)) = 0 := by
    have : (2 : ℂ) * (∑ a, κ ⁅x, D.generator a⁆ (D.dualGenerator a)) = 0 := by
      linear_combination h2
    exact (mul_eq_zero.mp this).resolve_left two_ne_zero
  rw [hS, h3, neg_zero]

/-- The full trace `∑ kappaInv · formTable = card ι = dim 𝔤` (central charge numerator). -/
theorem trace_kappaInv_formTable :
    (∑ a, ∑ b, D.kappaInv a b * D.formTable a b) = Fintype.card ι := by
  have hrow (a : ι) : (∑ b, D.kappaInv a b * D.formTable a b) = 1 := by
    have h := D.kappaInv_kappa a a
    simpa only [if_pos rfl, D.kappaInv_symm, mul_comm] using h
  simp only [hrow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

end LieData

end

end VOA.AffineGeneral

namespace VOA.AffineGeneral.LieData

noncomputable section

variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
variable {κ : LinearMap.BilinForm ℂ 𝔤} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Lie data from a nondegenerate invariant form.**  The `κ`-dual family is Mathlib's
`LinearMap.BilinForm.dualBasis`; the only remaining Lie-theoretic hypothesis is the adjoint Casimir
eigenvalue `2h` for that dual pair. -/
def ofNondegenerate (hinv : κ.IsInvariant) (hnd : LinearMap.BilinForm.Nondegenerate κ) (b : Module.Basis ι ℂ 𝔤)
    (h : ℂ) (hcas : ∀ x : 𝔤, ∑ i, ⁅b i, ⁅LinearMap.BilinForm.dualBasis κ hnd b i, x⁆⁆ = (2 * h) • x) :
    LieData κ ι where
  invariant := hinv
  basis := b
  dual := LinearMap.BilinForm.dualBasis κ hnd b
  pair i j := by
    rw [hinv.symm, LinearMap.BilinForm.apply_dualBasis_left]
  h := h
  casimir := hcas

end

end VOA.AffineGeneral.LieData

namespace VOA.AffineGeneral.LieData

noncomputable section

variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
variable {κ : LinearMap.BilinForm ℂ 𝔤} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Rescaling the form.**  For `c ≠ 0`, the Lie data of `κ` give Lie data of `c • κ`: same basis,
dual family divided by `c`, dual Coxeter number `h / c`. -/
def smulForm (D : LieData κ ι) (c : ℂ) (hc : c ≠ 0) : LieData (c • κ) ι where
  invariant :=
    { symm := fun x y => by simp [D.invariant.symm x y]
      invariant := fun x y z => by simp [D.invariant.invariant x y z] }
  basis := D.basis
  dual i := c⁻¹ • D.dual i
  pair i j := by
    simp only [LinearMap.smul_apply, map_smul, smul_eq_mul, D.pair]
    rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  h := D.h / c
  casimir x := by
    simp only [smul_lie, lie_smul, ← Finset.smul_sum, D.casimir, smul_smul]
    congr 1
    field_simp

theorem smulForm_h (D : LieData κ ι) (c : ℂ) (hc : c ≠ 0) : (D.smulForm c hc).h = D.h / c := rfl

end

end VOA.AffineGeneral.LieData

namespace VOA.AffineGeneral.LieData

variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
variable {κ : LinearMap.BilinForm ℂ 𝔤} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The form separates points in its right argument (a consequence of the dual pairing). -/
theorem form_right_nondegenerate (D : LieData κ ι) (x : 𝔤) (hx : ∀ y, κ y x = 0) : x = 0 := by
  rw [← D.reconstruct x]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [← D.form_dual_coordinates, D.invariant.symm, hx, zero_smul]

section Reindex


/-- Transport Lie data along a reindexing `ι ≃ ι'`. -/
noncomputable def reindex {ι' : Type*} [Fintype ι'] [DecidableEq ι'] (D : LieData κ ι) (e : ι ≃ ι') :
    LieData κ ι' where
  invariant := D.invariant
  basis := D.basis.reindex e
  dual i := D.dual (e.symm i)
  pair i j := by
    rw [Module.Basis.reindex_apply, D.pair]
    simp only [e.symm.injective.eq_iff]
  h := D.h
  casimir x := by
    rw [← D.casimir x]
    simp only [Module.Basis.reindex_apply]
    exact e.symm.sum_comp (fun i => ⁅D.basis i, ⁅D.dual i, x⁆⁆)

@[simp] theorem reindex_h {ι' : Type*} [Fintype ι'] [DecidableEq ι'] (D : LieData κ ι)
    (e : ι ≃ ι') : (D.reindex e).h = D.h := rfl

end Reindex

end VOA.AffineGeneral.LieData
