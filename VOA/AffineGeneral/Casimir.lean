/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.AffineGeneral.LieData
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.Algebra.Lie.Semisimple.Defs
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# The adjoint Casimir of a simple Lie algebra is a scalar

Let `𝔤` be a finite-dimensional complex Lie algebra with an invariant symmetric form `κ`, a basis
`b` and a `κ`-dual family `d` (`κ(bᵢ, dⱼ) = δᵢⱼ`).  The adjoint Casimir `C x = ∑ᵢ ⁅bᵢ, ⁅dᵢ, x⁆⁆`

* commutes with every `ad y` (`casimir_commute`), by invariance of `κ`;
* is therefore a scalar when `𝔤` is simple (`casimir_scalar`): an eigenspace of `C` is an ideal.

Consequently `LieData.ofSimple` builds the full Lie data — and hence `affineVOA` — for **every**
finite-dimensional simple complex Lie algebra with a nondegenerate invariant form, the dual Coxeter
number being half the Casimir eigenvalue in the normalization of `κ`.  No explicit value of the
eigenvalue is needed for the construction (only `k + h ≠ 0`).
-/

namespace VOA.AffineGeneral

noncomputable section

variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
variable {κ : LinearMap.BilinForm ℂ 𝔤} {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (hinv : κ.IsInvariant) (b : Module.Basis ι ℂ 𝔤) (d : ι → 𝔤)
variable (pair : ∀ i j, κ (b i) (d j) = if i = j then 1 else 0)

include pair in
/-- Pairing with a dual vector extracts the coordinate. -/
theorem coord_eq_pair (z : 𝔤) (j : ι) : κ z (d j) = b.repr z j := by
  conv_lhs => rw [← b.sum_repr z]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, pair,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

include hinv pair in
/-- Expansion in the dual family: `z = ∑ⱼ κ(z, bⱼ) dⱼ`. -/
theorem dual_expand (z : 𝔤) : z = ∑ j, κ z (b j) • d j := by
  apply b.repr.injective
  ext m
  rw [map_sum, Finsupp.coe_finset_sum, Finset.sum_apply]
  simp only [map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
  rw [← coord_eq_pair b d pair z m]
  -- κ z (d m) = ∑ⱼ (repr (d m) j) κ z (b j), and repr (d m) j = κ (d m) (d j) = κ (d j) (d m)
  conv_lhs => rw [← b.sum_repr (d m)]
  simp only [map_sum, map_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← coord_eq_pair b d pair (d m) j, ← coord_eq_pair b d pair (d j) m, hinv.symm (d m) (d j)]
  ring

/-- The adjoint Casimir operator `x ↦ ∑ᵢ ⁅bᵢ, ⁅dᵢ, x⁆⁆`. -/
def casimirOp : Module.End ℂ 𝔤 :=
  ∑ i, (LieModule.toEnd ℂ 𝔤 𝔤 (b i)) * (LieModule.toEnd ℂ 𝔤 𝔤 (d i))

theorem casimirOp_apply (x : 𝔤) : casimirOp b d x = ∑ i, ⁅b i, ⁅d i, x⁆⁆ := by
  simp [casimirOp]

include hinv pair in
/-- **The Casimir commutes with the adjoint action.** -/
theorem casimir_commute (y x : 𝔤) : casimirOp b d ⁅y, x⁆ = ⁅y, casimirOp b d x⁆ := by
  rw [casimirOp_apply, casimirOp_apply, lie_sum]
  -- ⁅y, ⁅bᵢ, ⁅dᵢ, x⁆⁆⁆ = ⁅⁅y,bᵢ⁆,⁅dᵢ,x⁆⁆ + ⁅bᵢ,⁅⁅y,dᵢ⁆,x⁆⁆ + ⁅bᵢ,⁅dᵢ,⁅y,x⁆⁆⁆
  have hl : ∀ i, ⁅y, ⁅b i, ⁅d i, x⁆⁆⁆ =
      ⁅⁅y, b i⁆, ⁅d i, x⁆⁆ + ⁅b i, ⁅⁅y, d i⁆, x⁆⁆ + ⁅b i, ⁅d i, ⁅y, x⁆⁆⁆ := by
    intro i
    rw [leibniz_lie y (b i), leibniz_lie y (d i), lie_add]
    abel
  simp only [hl, Finset.sum_add_distrib]
  -- the cross terms cancel
  suffices hcross : (∑ i, ⁅⁅y, b i⁆, ⁅d i, x⁆⁆) + (∑ i, ⁅b i, ⁅⁅y, d i⁆, x⁆⁆) = 0 by
    rw [hcross, zero_add]
  have e1 : ∀ i, ⁅y, b i⁆ = ∑ j, κ ⁅y, b i⁆ (d j) • b j := by
    intro i
    conv_lhs => rw [← b.sum_repr ⁅y, b i⁆]
    exact Finset.sum_congr rfl fun j _ => by rw [coord_eq_pair b d pair]
  have e2 : ∀ i, ⁅y, d i⁆ = ∑ j, κ ⁅y, d i⁆ (b j) • d j := fun i => dual_expand hinv b d pair _
  have t1 : (∑ i, ⁅⁅y, b i⁆, ⁅d i, x⁆⁆) = ∑ i, ∑ j, κ ⁅y, b i⁆ (d j) • ⁅b j, ⁅d i, x⁆⁆ := by
    refine Finset.sum_congr rfl fun i _ => ?_
    conv_lhs => rw [e1 i, sum_lie]
    simp only [smul_lie]
  have t2 : (∑ i, ⁅b i, ⁅⁅y, d i⁆, x⁆⁆) = ∑ i, ∑ j, κ ⁅y, d i⁆ (b j) • ⁅b i, ⁅d j, x⁆⁆ := by
    refine Finset.sum_congr rfl fun i _ => ?_
    conv_lhs => rw [e2 i, sum_lie, lie_sum]
    simp only [smul_lie, lie_smul]
  rw [t1, t2, Finset.sum_comm (f := fun i j => κ ⁅y, d i⁆ (b j) • ⁅b i, ⁅d j, x⁆⁆),
    ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [← add_smul]
  have hc : κ ⁅y, b i⁆ (d j) + κ ⁅y, d j⁆ (b i) = 0 := by
    rw [hinv.symm ⁅y, d j⁆ (b i), ← lie_skew y (b i), map_neg, LinearMap.neg_apply,
      hinv.invariant]
    ring
  rw [hc, zero_smul]

/-- The eigenspace of the Casimir for `μ` is an ideal. -/
def casimirEigenIdeal (μ : ℂ) : LieIdeal ℂ 𝔤 :=
  { Module.End.eigenspace (casimirOp b d) μ with
    lie_mem := by
      intro y x hx
      simp only [Submodule.mem_carrier, SetLike.mem_coe, Module.End.mem_eigenspace_iff] at hx ⊢
      rw [casimir_commute hinv b d pair, hx, lie_smul] }

include hinv pair in
/-- **For a simple Lie algebra the adjoint Casimir is a scalar.** -/
theorem casimir_scalar [FiniteDimensional ℂ 𝔤] [LieAlgebra.IsSimple ℂ 𝔤] :
    ∃ c : ℂ, ∀ x : 𝔤, ∑ i, ⁅b i, ⁅d i, x⁆⁆ = c • x := by
  haveI : Nontrivial 𝔤 := by
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    exact LieAlgebra.IsSimple.non_abelian (R := ℂ) (L := 𝔤)
      ⟨fun x y => Subsingleton.elim _ _⟩
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (casimirOp b d)
  refine ⟨μ, fun x => ?_⟩
  have htop : casimirEigenIdeal hinv b d pair μ = ⊤ := by
    rcases LieAlgebra.IsSimple.eq_bot_or_eq_top (casimirEigenIdeal hinv b d pair μ) with h | h
    · exfalso
      obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
      have hmem : v ∈ casimirEigenIdeal hinv b d pair μ := hv.1
      rw [h] at hmem
      exact hv.2 ((LieSubmodule.mem_bot v).mp hmem)
    · exact h
  have hx : x ∈ casimirEigenIdeal hinv b d pair μ := by rw [htop]; exact LieSubmodule.mem_top x
  have := Module.End.mem_eigenspace_iff.mp hx
  rw [← casimirOp_apply]
  exact this

namespace LieData

/-- **Lie data for every finite-dimensional simple Lie algebra** with a nondegenerate invariant form:
the dual family is Mathlib's `dualBasis`, and `h` is half the (existing, by `casimir_scalar`)
adjoint Casimir eigenvalue. -/
def ofSimple [FiniteDimensional ℂ 𝔤] [LieAlgebra.IsSimple ℂ 𝔤] (hinv : κ.IsInvariant)
    (hnd : LinearMap.BilinForm.Nondegenerate κ) (b : Module.Basis ι ℂ 𝔤) : LieData κ ι :=
  have hpair : ∀ i j, κ (b i) (LinearMap.BilinForm.dualBasis κ hnd b j) = if i = j then 1 else 0 := by
    intro i j
    rw [hinv.symm, LinearMap.BilinForm.apply_dualBasis_left]
  ofNondegenerate hinv hnd b
    ((Classical.choose (casimir_scalar hinv b (LinearMap.BilinForm.dualBasis κ hnd b) hpair)) / 2)
    (fun x => by
      rw [mul_div_cancel₀ _ two_ne_zero]
      exact Classical.choose_spec (casimir_scalar hinv b _ hpair) x)

end LieData

end

end VOA.AffineGeneral
