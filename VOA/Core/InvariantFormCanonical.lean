/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Core.InvariantFormFHLClosure
import Mathlib.Algebra.DirectSum.Decomposition

/-!
# The canonical (Li) invariant bilinear form — constructed so invariance is built in

A **concrete** Gannon-normalised invariant form, constructed via the Li route (the vacuum-coordinate
functional of the `e^{zL₁}(−z⁻²)^{L₀}` adjoint at the creation mode), sidestepping the arbitrary-`B`
transpose obstruction (`Core.InvariantFormTranspose`) — a *fixed concrete* form, not an arbitrary
`InvariantForm`, so the transpose argument does not apply.

* **`vacCoord`** — the linear vacuum-coordinate `V →ₗ ℂ` (Li's functional on `V₀`).
* **`canBilin`** — the concrete form, glued across the `a`-grading, a genuine bilinear `V →ₗ V →ₗ ℂ`.
* Proved axiom-free: bilinearity, **`canBilin_vacuum`** `(𝟙|𝟙) = −1`, **`canBilin_offdiag`** grading
  orthogonality, **`canBilin_L0_adj`** the `n = 0` Virasoro-adjointness slice.
* **`CanVirasoroAdj`** / **`canForm`** — the construction-specific Virasoro-adjointness residual.

## Status
**The residual is discharged in `Core.InvariantFormFHL2`.**  The residual named below is discharged, under the
standing hypotheses `hne : 𝟙 ≠ 0` and `hqp : L₁𝒱₁ = 0`, by `canDiagonal_unconditional : CanDiagonal hne`
and `canVirasoroAdj_of_diagonal`; the resulting form is `canonicalInvariantForm`.  The text below
describes this file's own reduction, an intermediate step.
Axiom-free reduction; bottoms out at the residual `CanVirasoroAdj` (→ Li 1994; discharged, see above).
Axiom-clean for the construction and its proved properties. The remaining content of this file (a
hypothesis, **not** an axiom) is `CanVirasoroAdj` — the *full* Virasoro-adjointness of the fixed
concrete `canBilin` (its `n = 0` case proved), provable from the construction via the VOA duality
(`assoc_neg`/`assoc_nonneg`) — the genuine remaining Li argument, distinct from the conditionally
obstructed arbitrary-`B` `DiagonalFHL` route. Closing it makes the raw Gannon-normalised invariant
form unconditional.

## References
* Gannon §5.1.3, eqs. (5.1.11)–(5.1.12); Frenkel–Huang–Lepowsky [199]; Li [380].
-/

namespace VOA
open VOA.VertexOperatorAlgebra
open scoped BigOperators

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}

/-- The grade-0 component (chosen via the internal direct-sum decomposition). -/
noncomputable def grade0 (W : VertexOperatorAlgebra V) : V →ₗ[ℂ] (W.grading 0) :=
  letI : DirectSum.Decomposition W.grading := W.isInternal.chooseDecomposition
  (DirectSum.component ℂ ℤ (fun i => W.grading i) 0).comp
    (DirectSum.decomposeLinearEquiv W.grading).toLinearMap

/-- The linear iso `W.grading 0 ≃ₗ ℂ ∙ vacuum` (rewriting along `vacuum_grade`). -/
noncomputable def grade0ToSpan (W : VertexOperatorAlgebra V) :
    (W.grading 0) ≃ₗ[ℂ] (ℂ ∙ W.vacuum) :=
  LinearEquiv.ofEq _ _ W.vacuum_grade

/-- The underlying vector of `grade0 W x` is the grade-0 piece in the decomposition. -/
theorem grade0_coe (W : VertexOperatorAlgebra V) (x : V) :
    letI : DirectSum.Decomposition W.grading := W.isInternal.chooseDecomposition
    ((grade0 W x : V)) = (DirectSum.decompose W.grading x 0 : V) := by
  rfl

/-- For a homogeneous `x ∈ W.grading 0`, the grade-0 projection returns `x` itself. -/
theorem grade0_of_mem_zero (W : VertexOperatorAlgebra V) {x : V} (hx : x ∈ W.grading 0) :
    (grade0 W x : V) = x := by
  letI : DirectSum.Decomposition W.grading := W.isInternal.chooseDecomposition
  rw [grade0_coe]
  exact DirectSum.decompose_of_mem_same W.grading hx

/-- For `x ∈ W.grading n` with `n ≠ 0`, the grade-0 projection vanishes. -/
theorem grade0_of_mem_ne (W : VertexOperatorAlgebra V) {n : ℤ} (hn : n ≠ 0) {x : V}
    (hx : x ∈ W.grading n) : (grade0 W x : V) = 0 := by
  letI : DirectSum.Decomposition W.grading := W.isInternal.chooseDecomposition
  rw [grade0_coe]
  exact DirectSum.decompose_of_mem_ne W.grading hx hn

/-- The **vacuum coordinate** functional `V →ₗ[ℂ] ℂ`: project to grade 0, then read off the
`ℂ`-coefficient on `vacuum` (using `vacuum ≠ 0`). -/
noncomputable def vacCoord (W : VertexOperatorAlgebra V) (hne : W.vacuum ≠ 0) : V →ₗ[ℂ] ℂ :=
  ((LinearEquiv.toSpanNonzeroSingleton ℂ V W.vacuum hne).symm.toLinearMap).comp
    ((grade0ToSpan W).toLinearMap.comp (grade0 W))

/-- **The defining property of `vacCoord`:** the grade-0 part of `x` is `(vacCoord x) • vacuum`. -/
theorem grade0_eq_vacCoord_smul (W : VertexOperatorAlgebra V) (hne : W.vacuum ≠ 0) (x : V) :
    (grade0 W x : V) = vacCoord W hne x • W.vacuum := by
  -- `grade0ToSpan W (grade0 W x)` is the same vector, viewed inside `ℂ ∙ vacuum`.
  have hcoe : ((grade0ToSpan W) (grade0 W x) : V) = (grade0 W x : V) := rfl
  have hkey := LinearEquiv.toSpanNonzeroSingleton_symm_apply_smul ℂ V W.vacuum hne
    ((grade0ToSpan W) (grade0 W x))
  -- hkey : (toSpanNonzeroSingleton …).symm (grade0ToSpan W (grade0 W x)) • vacuum
  --        = ↑(grade0ToSpan W (grade0 W x))
  rw [hcoe] at hkey
  rw [← hkey]
  rfl

/-- `vacCoord (c • vacuum) = c`. -/
theorem vacCoord_smul_vacuum (W : VertexOperatorAlgebra V) (hne : W.vacuum ≠ 0) (c : ℂ) :
    vacCoord W hne (c • W.vacuum) = c := by
  have h := grade0_eq_vacCoord_smul W hne (c • W.vacuum)
  have hmem : c • W.vacuum ∈ W.grading 0 := Submodule.smul_mem _ _ W.vacuum_mem
  rw [grade0_of_mem_zero W hmem] at h
  -- h : c • vacuum = vacCoord (c • vacuum) • vacuum, cancel vacuum (≠ 0)
  have := sub_eq_zero.mpr h
  rw [← sub_smul] at this
  rcases smul_eq_zero.mp this with hc | hv
  · exact (sub_eq_zero.mp hc).symm
  · exact absurd hv hne

/-- `vacCoord vacuum = 1`. -/
theorem vacCoord_vacuum (W : VertexOperatorAlgebra V) (hne : W.vacuum ≠ 0) :
    vacCoord W hne W.vacuum = 1 := by
  have h := vacCoord_smul_vacuum W hne 1
  rwa [one_smul] at h

/-- `vacCoord` vanishes on homogeneous vectors of nonzero grade. -/
theorem vacCoord_of_mem_ne (W : VertexOperatorAlgebra V) (hne : W.vacuum ≠ 0) {n : ℤ}
    (hn : n ≠ 0) {x : V} (hx : x ∈ W.grading n) : vacCoord W hne x = 0 := by
  have h := grade0_eq_vacCoord_smul W hne x
  rw [grade0_of_mem_ne W hn hx] at h
  -- 0 = vacCoord x • vacuum
  rcases smul_eq_zero.mp h.symm with hc | hv
  · exact hc
  · exact absurd hv hne

/-- If `x ∈ W.grading 0`, then `x = vacCoord x • vacuum`. -/
theorem eq_vacCoord_smul_of_mem_zero (W : VertexOperatorAlgebra V) (hne : W.vacuum ≠ 0) {x : V}
    (hx : x ∈ W.grading 0) : x = vacCoord W hne x • W.vacuum := by
  have h := grade0_eq_vacCoord_smul W hne x
  rwa [grade0_of_mem_zero W hx] at h

/-! ## The canonical adjoint pairing on a fixed weight

For homogeneous `a ∈ V_wt`, the **adjoint creation product** is the FHL `e^{zL₁}(−z⁻²)^{L₀}`
adjoint at the creation mode `n = −1`, extracted to the vacuum line:
`adjPair wt a b = (−1)^wt ∑_{j≤wt} (1/j!) vacCoord( (L₁ʲa)₍2wt−1−j₎ b )`.
The mode index `2wt − (−1) − 2 − j = 2wt − 1 − j` is the unique one landing the product in grade 0
when `b ∈ V_wt` (creation/diagonal); `vacCoord` reads off the vacuum coefficient.  This is
manifestly bilinear in `(a, b)` and finite (`L₁ʲa = 0` for `j > wt`). -/

/-- The per-weight adjoint creation pairing (`b`-side, before summing weights of `a`). -/
noncomputable def adjPair (W : VertexOperatorAlgebra V) (hne : W.vacuum ≠ 0) (wt : ℤ)
    (a b : V) : ℂ :=
  (-1 : ℂ) ^ wt • ∑ j ∈ Finset.range (wt.toNat + 1), ((j.factorial : ℂ)⁻¹) •
    vacCoord W hne (W.smul (((W.L 1) ^ j) a) (2 * wt - 1 - (j : ℤ)) b)

/-- `adjPair` is additive in the `a`-slot. -/
theorem adjPair_add_left (hne : W.vacuum ≠ 0) (wt : ℤ) (a₁ a₂ b : V) :
    adjPair W hne wt (a₁ + a₂) b = adjPair W hne wt a₁ b + adjPair W hne wt a₂ b := by
  simp only [adjPair, ← smul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [map_add, PreVertexAlgebra.smul_add_left, map_add]

/-- `adjPair` is `ℂ`-homogeneous in the `a`-slot. -/
theorem adjPair_smul_left (hne : W.vacuum ≠ 0) (wt : ℤ) (c : ℂ) (a b : V) :
    adjPair W hne wt (c • a) b = c • adjPair W hne wt a b := by
  rw [adjPair, adjPair]
  rw [show (∑ j ∈ Finset.range (wt.toNat + 1), ((j.factorial : ℂ)⁻¹) •
        vacCoord W hne (W.smul (((W.L 1) ^ j) (c • a)) (2 * wt - 1 - (j : ℤ)) b))
      = c • ∑ j ∈ Finset.range (wt.toNat + 1), ((j.factorial : ℂ)⁻¹) •
        vacCoord W hne (W.smul (((W.L 1) ^ j) a) (2 * wt - 1 - (j : ℤ)) b) from ?_]
  · rw [smul_comm]
  · rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [map_smul, PreVertexAlgebra.smul_smul_left, map_smul, smul_comm ((j.factorial : ℂ)⁻¹) c]

/-- `adjPair` is additive in the `b`-slot. -/
theorem adjPair_add_right (hne : W.vacuum ≠ 0) (wt : ℤ) (a b₁ b₂ : V) :
    adjPair W hne wt a (b₁ + b₂) = adjPair W hne wt a b₁ + adjPair W hne wt a b₂ := by
  simp only [adjPair, ← smul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [PreVertexAlgebra.smul_add_right, map_add]

/-- `adjPair` is `ℂ`-homogeneous in the `b`-slot. -/
theorem adjPair_smul_right (hne : W.vacuum ≠ 0) (wt : ℤ) (c : ℂ) (a b : V) :
    adjPair W hne wt a (c • b) = c • adjPair W hne wt a b := by
  rw [adjPair, adjPair]
  rw [show (∑ j ∈ Finset.range (wt.toNat + 1), ((j.factorial : ℂ)⁻¹) •
        vacCoord W hne (W.smul (((W.L 1) ^ j) a) (2 * wt - 1 - (j : ℤ)) (c • b)))
      = c • ∑ j ∈ Finset.range (wt.toNat + 1), ((j.factorial : ℂ)⁻¹) •
        vacCoord W hne (W.smul (((W.L 1) ^ j) a) (2 * wt - 1 - (j : ℤ)) b) from ?_]
  · rw [smul_comm]
  · rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [PreVertexAlgebra.smul_smul_right, map_smul, smul_comm ((j.factorial : ℂ)⁻¹) c]

/-- `adjPair` vanishes when `a = 0`. -/
@[simp] theorem adjPair_zero_left (hne : W.vacuum ≠ 0) (wt : ℤ) (b : V) :
    adjPair W hne wt 0 b = 0 := by
  simp only [adjPair]
  rw [Finset.sum_eq_zero (fun j _ => ?_), smul_zero]
  rw [map_zero, PreVertexAlgebra.smul_zero_left, map_zero, smul_zero]

/-- `adjPair` vanishes when `b = 0`. -/
@[simp] theorem adjPair_zero_right (hne : W.vacuum ≠ 0) (wt : ℤ) (a : V) :
    adjPair W hne wt a 0 = 0 := by
  simp only [adjPair]
  rw [Finset.sum_eq_zero (fun j _ => ?_), smul_zero]
  rw [PreVertexAlgebra.smul_zero_right, map_zero, smul_zero]

/-! ## The canonical form: summing the per-weight adjoint pairings over the grading of `a`

`canFormFun a b = − ∑_{wt} adjPair wt (component_wt a) b`, the (Gannon-normalised, so the leading
`−`) FHL adjoint pairing summed over the homogeneous decomposition of `a`.  For homogeneous
`a ∈ V_p` only the `wt = p` term survives (`canForm_homog`). -/

variable (W) in
/-- The grade-`wt` component of `x`, as a plain vector. -/
noncomputable def comp (wt : ℤ) (x : V) : V :=
  letI : DirectSum.Decomposition W.grading := W.isInternal.chooseDecomposition
  (DirectSum.decompose W.grading x wt : V)

theorem comp_mem (W : VertexOperatorAlgebra V) (wt : ℤ) (x : V) :
    comp W wt x ∈ W.grading wt := by
  letI : DirectSum.Decomposition W.grading := W.isInternal.chooseDecomposition
  exact (DirectSum.decompose W.grading x wt).2

theorem comp_of_mem_same (W : VertexOperatorAlgebra V) {wt : ℤ} {x : V} (hx : x ∈ W.grading wt) :
    comp W wt x = x := by
  letI : DirectSum.Decomposition W.grading := W.isInternal.chooseDecomposition
  exact DirectSum.decompose_of_mem_same W.grading hx

theorem comp_of_mem_ne (W : VertexOperatorAlgebra V) {wt n : ℤ} (hn : wt ≠ n) {x : V}
    (hx : x ∈ W.grading n) : comp W wt x = 0 := by
  letI : DirectSum.Decomposition W.grading := W.isInternal.chooseDecomposition
  exact DirectSum.decompose_of_mem_ne W.grading hx (Ne.symm hn)

/-- The `b`-slot functional `b ↦ −adjPair wt a b`, as a `ℂ`-linear map (for fixed weight `wt`,
homogeneous `a`).  The leading `−` gives Gannon's normalisation `(𝟙|𝟙) = −1`. -/
noncomputable def bSlotLin (W : VertexOperatorAlgebra V) (hne : W.vacuum ≠ 0) (wt : ℤ)
    (a : V) : V →ₗ[ℂ] ℂ where
  toFun b := - adjPair W hne wt a b
  map_add' b₁ b₂ := by rw [adjPair_add_right]; ring
  map_smul' c b := by rw [adjPair_smul_right]; simp

/-- `bSlotLin` is `ℂ`-linear in the homogeneous `a`-slot — packaged as a map out of `W.grading wt`. -/
noncomputable def bSlotOfGrade (W : VertexOperatorAlgebra V) (hne : W.vacuum ≠ 0) (wt : ℤ) :
    (W.grading wt) →ₗ[ℂ] (V →ₗ[ℂ] ℂ) where
  toFun a := bSlotLin W hne wt (a : V)
  map_add' a₁ a₂ := by
    ext b
    simp only [bSlotLin, LinearMap.coe_mk, AddHom.coe_mk, Submodule.coe_add, LinearMap.add_apply]
    rw [adjPair_add_left]; ring
  map_smul' c a := by
    ext b
    simp only [bSlotLin, LinearMap.coe_mk, AddHom.coe_mk, SetLike.val_smul, RingHom.id_apply,
      LinearMap.smul_apply, smul_eq_mul]
    rw [adjPair_smul_left]; ring

/-- The canonical bilinear form as a `ℂ`-linear map `V →ₗ[ℂ] (V →ₗ[ℂ] ℂ)`: glue the per-weight
`bSlotOfGrade` family across the internal direct-sum decomposition of the `a`-slot. -/
noncomputable def canBilin (W : VertexOperatorAlgebra V) (hne : W.vacuum ≠ 0) :
    V →ₗ[ℂ] (V →ₗ[ℂ] ℂ) :=
  letI : DirectSum.Decomposition W.grading := W.isInternal.chooseDecomposition
  (DirectSum.toModule ℂ ℤ (V →ₗ[ℂ] ℂ) (bSlotOfGrade W hne)).comp
    (DirectSum.decomposeLinearEquiv W.grading).toLinearMap

/-- **Homogeneous evaluation:** on `a ∈ W.grading p`, the canonical form collapses to the single
weight-`p` adjoint pairing `−adjPair p a b`. -/
theorem canBilin_homog (W : VertexOperatorAlgebra V) (hne : W.vacuum ≠ 0) {p : ℤ} {a : V}
    (ha : a ∈ W.grading p) (b : V) :
    canBilin W hne a b = - adjPair W hne p a b := by
  letI : DirectSum.Decomposition W.grading := W.isInternal.chooseDecomposition
  rw [canBilin]
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    DirectSum.decomposeLinearEquiv_apply]
  rw [DirectSum.decompose_of_mem W.grading ha, ← DirectSum.lof_eq_of ℂ, DirectSum.toModule_lof]
  show bSlotLin W hne p a b = - adjPair W hne p a b
  rfl

/-- `adjPair 0 vacuum vacuum = 1`: the single `j = 0` term is `vacCoord(𝟙₍₋₁₎𝟙) = vacCoord 𝟙 = 1`. -/
theorem adjPair_vacuum (hne : W.vacuum ≠ 0) :
    adjPair W hne 0 W.vacuum W.vacuum = 1 := by
  rw [adjPair, show ((0 : ℤ).toNat + 1) = 1 from rfl, Finset.sum_range_one]
  rw [pow_zero, Module.End.one_apply, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul,
    Nat.cast_zero, show (2 * (0 : ℤ) - 1 - 0) = -1 by ring]
  rw [PreVertexAlgebra.smul_vacuum_left, if_pos rfl, vacCoord_vacuum, zpow_zero, one_smul]

/-- **Normalisation** (Gannon 5.1.12a): `B(𝟙,𝟙) = −1`. -/
theorem canBilin_vacuum (hne : W.vacuum ≠ 0) :
    canBilin W hne W.vacuum W.vacuum = -1 := by
  rw [canBilin_homog W hne W.vacuum_mem, adjPair_vacuum]

/-- **Off-diagonal vanishing** (grading): for homogeneous `a ∈ V_p`, `b ∈ V_q` with `p ≠ q`,
`adjPair p a b = 0` — each summand `(L₁ʲa)₍2p−1−j₎b ∈ V_{q−p}` has `vacCoord = 0`. -/
theorem adjPair_offdiag (hne : W.vacuum ≠ 0) {p q : ℤ} {a b : V}
    (ha : a ∈ W.grading p) (hb : b ∈ W.grading q) (hpq : p ≠ q) :
    adjPair W hne p a b = 0 := by
  rw [adjPair, Finset.sum_eq_zero, smul_zero]
  intro j _
  have hLa : ((W.L 1) ^ j) a ∈ W.grading (p - (j : ℤ)) := L_one_pow_mem W ha j
  have hmem : W.smul (((W.L 1) ^ j) a) (2 * p - 1 - (j : ℤ)) b ∈ W.grading (q - p) := by
    have h := W.smul_mem_grading hLa hb (2 * p - 1 - (j : ℤ))
    rwa [show (p - (j : ℤ) + q - (2 * p - 1 - (j : ℤ)) - 1 : ℤ) = q - p by ring] at h
  rw [vacCoord_of_mem_ne W hne (by omega : (q - p : ℤ) ≠ 0) hmem, smul_zero]

/-- **Off-diagonal vanishing for `canBilin`**: `B a b = 0` for homogeneous `a ∈ V_p`, `b ∈ V_q`,
`p ≠ q`. -/
theorem canBilin_offdiag (hne : W.vacuum ≠ 0) {p q : ℤ} {a b : V}
    (ha : a ∈ W.grading p) (hb : b ∈ W.grading q) (hpq : p ≠ q) :
    canBilin W hne a b = 0 := by
  rw [canBilin_homog W hne ha, adjPair_offdiag hne ha hb hpq, neg_zero]

/-! ## `vacCoord` annihilates the image of `L₋₁` and of any nonzero `Lₙ` on a homogeneous vector

`L₋₁` raises the grading by 1 (`L_neg_one_raise`); since `𝒱_{<0} = 0` and `vacCoord` only sees the
grade-0 part, `vacCoord (L₋₁ x) = 0` whenever the grade-0 part of `x` is its only contribution to
grade 1 under `L₋₁` — more simply, for homogeneous `x ∈ 𝒱_k`, `L₋₁ x ∈ 𝒱_{k+1}`, which meets grade 0
only when `k = −1`, impossible (`𝒱_{−1} = 0`). -/

/-- `vacCoord (L₋₁ x) = 0` for homogeneous `x` (the image lands in grade `k+1 ≥ 1 ≠ 0`,
or `x = 0`). -/
theorem vacCoord_Lneg1_homog (hne : W.vacuum ≠ 0) {k : ℤ} {x : V} (hx : x ∈ W.grading k) :
    vacCoord W hne (W.L (-1) x) = 0 := by
  have hmem : W.L (-1) x ∈ W.grading (k + 1) := L_neg_one_raise W hx
  rcases eq_or_ne (k + 1) 0 with hk | hk
  · -- k = -1 ⟹ x ∈ 𝒱_{-1} = 0
    have hx0 : x = 0 := eq_zero_of_mem_neg_grading W (by omega : k < 0) hx
    rw [hx0, map_zero, map_zero]
  · exact vacCoord_of_mem_ne W hne hk hmem

/-! ## `L₀`-adjointness — the `n = 0` case of `virasoro_adj`, proved outright

`(L₀a|b) = (a|L₀b)`: by bilinearity + off-diagonal vanishing reduce to homogeneous `a ∈ V_p`,
`b ∈ V_q`; both sides are `0` unless `p = q`, where `L₀a = p•a`, `L₀b = q•b = p•b` agree. -/

/-- `canBilin` is additive/linear, so it suffices to check identities on homogeneous inputs.  This
records the linearity in the second slot already available from `LinearMap`. -/
theorem canBilin_L0_adj (hne : W.vacuum ≠ 0) (a b : V) :
    canBilin W hne (W.L 0 a) b = canBilin W hne a (W.L 0 b) := by
  -- Reduce to homogeneous `a` and `b` via the internal direct sum.
  have hatop : a ∈ ⨆ i, W.grading i := by
    rw [W.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
  refine Submodule.iSup_induction W.grading (motive := fun a =>
      canBilin W hne (W.L 0 a) b = canBilin W hne a (W.L 0 b)) hatop ?_ ?_ ?_
  · intro p a ha
    have hbtop : b ∈ ⨆ i, W.grading i := by
      rw [W.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
    refine Submodule.iSup_induction W.grading (motive := fun b =>
        canBilin W hne (W.L 0 a) b = canBilin W hne a (W.L 0 b)) hbtop ?_ ?_ ?_
    · intro q b hb
      rw [W.L_zero_grading a ha, W.L_zero_grading b hb, map_smul, LinearMap.smul_apply,
        map_smul, smul_eq_mul, smul_eq_mul]
      rcases eq_or_ne p q with hpq | hpq
      · rw [hpq]
      · rw [canBilin_offdiag hne ha hb hpq, mul_zero, mul_zero]
    · simp
    · intro b₁ b₂ hb₁ hb₂; rw [map_add, map_add, map_add, hb₁, hb₂]
  · simp
  · intro a₁ a₂ ha₁ ha₂
    rw [map_add, map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, ha₁, ha₂]

/-! ## Packaging into an `InvariantForm`, and the FHL reduction for the construction

`canBilin` is a concrete, bilinear, **Gannon-normalised** (`canBilin_vacuum`) form respecting the grading
(`canBilin_offdiag`), with `L₀`-adjointness proved (`canBilin_L0_adj`).  The remaining structural
field of `InvariantForm` is the *full* Virasoro-adjointness `(Lₙa|b) = (a|L₋ₙb)` for every `n` — the
genuine VOA-duality content of the construction (its `n = 0` case is `canBilin_L0_adj`).  We isolate
it as the precise residual `CanVirasoroAdj`, package the `InvariantForm` from it, and chain the
project's `isFullyInvariant_of_diagonal` to obtain `IsFullyInvariant` for the constructed form
reduced to `DiagonalFHL`. -/

variable (W) in
/-- The **construction-specific Virasoro-adjointness residual** (the remaining content of making
`canBilin` an `InvariantForm`): `(Lₙa|b) = (a|L₋ₙb)` for the concrete `canBilin`.  Its `n = 0` case
is `canBilin_L0_adj`; the full statement is the FHL-strength VOA duality for the adjoint operator
`Y*(u,z) = Y(e^{zL₁}(−z⁻²)^{L₀}u, z⁻¹)` that `canBilin` is the vacuum-coefficient of. -/
def CanVirasoroAdj (hne : W.vacuum ≠ 0) : Prop :=
  ∀ (n : ℤ) (a b : V), canBilin W hne (W.L n a) b = canBilin W hne a (W.L (-n) b)

/-- The canonical form as an `InvariantForm`, given the Virasoro-adjointness residual. -/
noncomputable def canForm (hne : W.vacuum ≠ 0) (hv : CanVirasoroAdj W hne) :
    InvariantForm W where
  form := canBilin W hne
  virasoro_adj := hv

@[simp] theorem canForm_form (hne : W.vacuum ≠ 0) (hv : CanVirasoroAdj W hne) :
    (canForm hne hv).form = canBilin W hne := rfl

/-- **The raw constructed form is Gannon-normalised** (Gannon 5.1.12a): `(𝟙|𝟙) = −1`. -/
theorem canForm_gannonNormalized (hne : W.vacuum ≠ 0) (hv : CanVirasoroAdj W hne) :
    (canForm hne hv).GannonNormalized := by
  show canBilin W hne W.vacuum W.vacuum = -1
  exact canBilin_vacuum hne

/-- **Full FHL invariance for the constructed Gannon-normalised form, reduced to `DiagonalFHL`.**
Given the Virasoro-adjointness residual, `canForm` is a genuine `InvariantForm`, so the project's
`isFullyInvariant_of_diagonal` applies: full `IsFullyInvariant` of the *constructed* form follows
from the single matching-mode identity `DiagonalFHL (canForm …)`. Unlike the conditionally
obstructed arbitrary-`B` route (`InvariantFormTranspose` and `InvariantFormDelimitation`), here the
form is a fixed concrete object whose creation-mode structure is built in. -/
theorem canForm_isFullyInvariant_of_diagonal (hne : W.vacuum ≠ 0) (hv : CanVirasoroAdj W hne)
    (hdiag : DiagonalFHL (canForm hne hv)) :
    (canForm hne hv).IsFullyInvariant :=
  isFullyInvariant_of_diagonal (canForm hne hv) hdiag
end VOA
