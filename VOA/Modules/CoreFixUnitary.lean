/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.Contragredient
import VOA.Core.CoreFixCommutative
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Unitary vertex operator algebras and modules (Dong–Lin)

A corrected unitarity predicate, as a leaf file alongside `Modules/Contragredient.lean`.

The predicate `VOA.Unitary N` (`Modules/Contragredient.lean`) asks for a `ℂ`-**bilinear** form with
`form x x ≠ 0` for `x ≠ 0` and invariance `(u₍ₙ₎x | y) = (x | u₍ₙ₎y)`, with a stray
`[StarRing ℂ]` argument that is never used.  Over `ℂ` no bilinear form on a space of dimension
`≥ 2` is anisotropic, so it is empty on every module of dimension `≥ 2`
(`old_unitary_isEmpty`, moved here from `Notes/Textbook/certificates/L12_UnitaryEmpty.lean`);
and the invariance condition omits the twist `e^{zL₁}(-z⁻²)^{L₀}` and the involution.

## The Dong–Lin definition
C. Dong, X. Lin, *Unitary vertex operator algebras*, J. Algebra 397 (2014) 252–277, §2:
* an **anti-linear involution** `φ` of `V`: anti-linear, `φ² = id`, `φ(𝟙) = 𝟙`, `φ(ω) = ω`,
  `φ(u₍ₙ₎v) = φ(u)₍ₙ₎φ(v)` (`AntiLinearInvolution`);
* `(V, φ)` is **unitary** if there is a positive-definite Hermitian form `(·,·)` on `V`, linear in
  the first and anti-linear in the second variable, with
  `(Y(e^{zL(1)}(-z⁻²)^{L(0)} a, z⁻¹) u, v) = (u, Y(φ(a), z) v)` for all `a, u, v`;
* a `V`-module `M` is **unitary** if it carries a positive-definite Hermitian form with
  `(Y_M(e^{zL(1)}(-z⁻²)^{L(0)} a, z⁻¹) w₁, w₂) = (w₁, Y_M(φ(a), z) w₂)`.
  (Dong–Lin state this for a unitary `(V, φ)`; the predicate below does not itself require it.)

**Mode form.**  For `a ∈ V_wt`, `e^{zL₁}(-z⁻²)^{L₀}a = (-1)^wt ∑ⱼ zʲ⁻²ʷᵗ L₁ʲa / j!`, so the
coefficient of `z^{-n-1}` of `Y(e^{zL₁}(-z⁻²)^{L₀}a, z⁻¹)u` is
`(-1)^wt ∑_{j ≤ wt} (1/j!) (L₁ʲa)₍₂wt−n−2−j₎ u`.  The range `j ≤ wt` is complete because
`L₁ʲa = 0` for `j > wt` (`L_one_pow_eq_zero`).  This is the same expansion as the library's full
invariance of a bilinear form, `InvariantForm.IsFullyInvariant` (`Core/BilinearForm.lean`).
Invariance for homogeneous `a` gives it for all `a` by linearity (`V = ⊕ V_wt`).

## Main declarations
* `AntiLinearInvolution W`, `UnitaryDL φ N` (modules), `UnitaryVOADL φ` (= `UnitaryDL φ` of the
  adjoint module).
* Sanity: `trivialVOAℂ` (the VOA `ℂ`, `c = 0`), `conjInvolution` (complex conjugation),
  `unitaryVOADL_trivial : Nonempty (UnitaryVOADL conjInvolution)`.
* Defect certificate: `old_unitary_isEmpty`.

Not attempted: a unitary example of dimension `≥ 2` (no small module of dimension `≥ 2` is
available in the library without proving a module Jacobi identity).
-/

namespace VOA

open Module (End)
open scoped ComplexConjugate

universe u v

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- An **anti-linear involution** of a VOA (Dong–Lin §2): an anti-linear map `φ` with `φ² = id`,
`φ(𝟙) = 𝟙`, `φ(ω) = ω` and `φ(u₍ₙ₎v) = φ(u)₍ₙ₎φ(v)`. -/
structure AntiLinearInvolution (W : VertexOperatorAlgebra 𝒱) where
  /-- The anti-linear map. -/
  toFun : 𝒱 →ₗ⋆[ℂ] 𝒱
  involutive : ∀ a, toFun (toFun a) = a
  map_vacuum : toFun W.vacuum = W.vacuum
  map_conformal : toFun W.conformalVector = W.conformalVector
  map_smul : ∀ (a : 𝒱) (n : ℤ) (b : 𝒱), toFun (W.smul a n b) = W.smul (toFun a) n (toFun b)

/-- The coefficient of `z^{-n-1}` in `Y_M(e^{zL₁}(-z⁻²)^{L₀} a, z⁻¹) x`, for `a ∈ V_wt`:
`(-1)^wt ∑_{j ≤ wt} (1/j!) (L₁ʲa)₍₂wt−n−2−j₎ x`. -/
noncomputable def oppositeMode {W : VertexOperatorAlgebra 𝒱} {M : Type v} [AddCommGroup M]
    [Module ℂ M] (N : OrdVModule W M) (wt : ℤ) (a : 𝒱) (n : ℤ) (x : M) : M :=
  (-1 : ℂ) ^ wt • ∑ j ∈ Finset.range (wt.toNat + 1), ((j.factorial : ℂ)⁻¹) •
    mode (N.YM (((W.L 1) ^ j) a)) (2 * wt - n - 2 - (j : ℤ)) x

/-- A **unitary module** in the sense of Dong–Lin (§2): a positive-definite Hermitian form on `M`
(linear in the first, anti-linear in the second variable) with
`(Y_M(e^{zL₁}(-z⁻²)^{L₀} a, z⁻¹) x, y) = (x, Y_M(φ(a), z) y)`, in mode form for homogeneous `a`. -/
structure UnitaryDL {W : VertexOperatorAlgebra 𝒱} (φ : AntiLinearInvolution W) {M : Type v}
    [AddCommGroup M] [Module ℂ M] (N : OrdVModule W M) where
  /-- The form, linear in the first and anti-linear in the second variable. -/
  form : M →ₗ[ℂ] M →ₗ⋆[ℂ] ℂ
  /-- Hermitian symmetry `(y, x) = conj (x, y)`. -/
  hermitian : ∀ x y : M, form y x = conj (form x y)
  /-- Positive-definiteness. -/
  posDef : ∀ x : M, x ≠ 0 → 0 < (form x x).re
  /-- Dong–Lin invariance, coefficient of `z^{-n-1}`, for `a ∈ V_wt`. -/
  invariant : ∀ (wt : ℤ) (a : 𝒱), a ∈ W.grading wt → ∀ (n : ℤ) (x y : M),
    form (oppositeMode N wt a n x) y = form x (mode (N.YM (φ.toFun a)) n y)

/-- A **unitary VOA** `(V, φ)` (Dong–Lin Def. 2.1): `V` is a unitary module over itself. -/
abbrev UnitaryVOADL {W : VertexOperatorAlgebra 𝒱} (φ : AntiLinearInvolution W) : Type u :=
  UnitaryDL φ (adjointModule W)

/-! ## The old `Unitary` is empty in dimension `≥ 2` (S1 entry 47, certified) -/

/-- Pure linear algebra: a bilinear form over `ℂ` on a space with two linearly independent
vectors has a nonzero isotropic vector. -/
theorem exists_isotropic_of_bilinear {M : Type*} [AddCommGroup M] [Module ℂ M]
    (B : M →ₗ[ℂ] M →ₗ[ℂ] ℂ) {e₁ e₂ : M} (h : LinearIndependent ℂ ![e₁, e₂]) :
    ∃ x : M, x ≠ 0 ∧ B x x = 0 := by
  rw [LinearIndependent.pair_iff] at h
  have he₁ : e₁ ≠ 0 := by
    intro h0
    have := (h 1 0 (by simp [h0])).1
    exact one_ne_zero this
  by_cases h11 : B e₁ e₁ = 0
  · exact ⟨e₁, he₁, h11⟩
  · obtain ⟨s, hs⟩ := IsAlgClosed.exists_eq_mul_self
      (discrim (B e₁ e₁) (B e₁ e₂ + B e₂ e₁) (B e₂ e₂))
    obtain ⟨a, ha⟩ := exists_quadratic_eq_zero h11 ⟨s, hs⟩
    refine ⟨a • e₁ + e₂, ?_, ?_⟩
    · intro h0
      have := (h a 1 (by simpa using h0)).2
      exact one_ne_zero this
    · simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
      linear_combination ha

/-- **The S1 entry 47 defect, certified**: the old `Unitary N` is empty whenever `M` has two
linearly independent vectors. -/
theorem old_unitary_isEmpty {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M]
    [Module ℂ M] (N : OrdVModule W M) {e₁ e₂ : M} (h : LinearIndependent ℂ ![e₁, e₂]) :
    IsEmpty (Unitary N) := by
  constructor
  intro U
  obtain ⟨x, hx, hxx⟩ := exists_isotropic_of_bilinear U.form h
  exact U.posDef x hx hxx

/-! ## Sanity: the trivial VOA `ℂ` is unitary -/

/-- **The trivial VOA on `ℂ`**: the commutative vertex algebra `ofCommAlgebra ℂ` (`Y(a,z) = a·`,
`𝟙 = 1`, all of `ℂ` in weight `0`) with `ω = 0` and `c = 0`. -/
noncomputable def trivialVOAℂ : VertexOperatorAlgebra ℂ where
  toPreVertexAlgebra := PreVertexAlgebra.ofCommAlgebra ℂ
  conformalVector := 0
  conformal_mem := Submodule.zero_mem _
  centralCharge := 0
  virasoro := by
    intro m n
    have hz : ∀ k : ℤ, (0 : FormalDist (End ℂ ℂ)) k = 0 := fun _ => rfl
    simp [hz]
  L0_grading := by
    intro n v hv
    change mode (PreVertexAlgebra.constMulField ℂ 0) 1 v = (n : ℂ) • v
    rw [map_zero, mode_zero, LinearMap.zero_apply]
    by_cases hn : n = 0
    · rw [hn]; simp
    · rw [PreVertexAlgebra.eq_zero_of_mem_gradingZero ℂ hn hv, smul_zero]
  translation := by
    intro v
    change PreVertexAlgebra.constMulField ℂ (mode (PreVertexAlgebra.constMulField ℂ 0) 0 v)
      = deriv (PreVertexAlgebra.constMulField ℂ v)
    rw [map_zero, mode_zero, LinearMap.zero_apply, map_zero]
    refine FormalDist.ext fun k => ?_
    rw [deriv_apply, PreVertexAlgebra.constMulField_apply]
    by_cases hk : k + 1 = 0
    · rw [if_pos hk, hk, zero_smul]; rfl
    · rw [if_neg hk, smul_zero]; rfl
  vacuum_grade := by
    change PreVertexAlgebra.gradingZero ℂ 0 = Submodule.span ℂ {(1 : ℂ)}
    rw [PreVertexAlgebra.gradingZero_zero]
    exact Ideal.span_singleton_one.symm
  positivity := fun n hn => PreVertexAlgebra.gradingZero_of_ne ℂ (by omega)

theorem trivialVOAℂ_mode (a : ℂ) (k : ℤ) (x : ℂ) :
    mode ((adjointModule trivialVOAℂ).YM a) k x = if k = -1 then a * x else 0 :=
  PreVertexAlgebra.mode_constMulField ℂ a k x

theorem trivialVOAℂ_smul (a : ℂ) (k : ℤ) (x : ℂ) :
    trivialVOAℂ.smul a k x = if k = -1 then a * x else 0 :=
  PreVertexAlgebra.mode_constMulField ℂ a k x

/-- Complex conjugation as an anti-linear map `ℂ → ℂ`. -/
noncomputable def conjSL : ℂ →ₗ⋆[ℂ] ℂ where
  toFun := conj
  map_add' := map_add _
  map_smul' c x := by simp

/-- **Complex conjugation** is an anti-linear involution of `trivialVOAℂ`. -/
noncomputable def conjInvolution : AntiLinearInvolution trivialVOAℂ where
  toFun := conjSL
  involutive a := by simp [conjSL]
  map_vacuum := by
    change conj (1 : ℂ) = 1
    simp
  map_conformal := by
    change conj (0 : ℂ) = 0
    simp
  map_smul a n b := by
    change conj (trivialVOAℂ.smul a n b) = trivialVOAℂ.smul (conj a) n (conj b)
    rw [trivialVOAℂ_smul, trivialVOAℂ_smul]
    split_ifs <;> simp

/-- The standard Hermitian form `(x, y) = x · conj y` on `ℂ`. -/
noncomputable def stdHermitian : ℂ →ₗ[ℂ] ℂ →ₗ⋆[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun x y => x * conj y)
    (fun _ _ _ => add_mul _ _ _) (fun _ _ _ => by simp [mul_assoc])
    (fun _ _ _ => by simp [mul_add]) (fun _ _ _ => by simp; ring)

/-- **Sanity (non-vacuity of `UnitaryVOADL`)**: the trivial VOA `ℂ` with complex conjugation is a
unitary VOA in the sense of Dong–Lin, with the form `(x, y) = x · conj y`. -/
theorem unitaryVOADL_trivial : Nonempty (UnitaryVOADL conjInvolution) := by
  refine ⟨{ form := stdHermitian, hermitian := ?_, posDef := ?_, invariant := ?_ }⟩
  · intro x y
    simp only [stdHermitian, LinearMap.mk₂'ₛₗ_apply, map_mul, Complex.conj_conj]
    ring
  · intro x hx
    simp only [stdHermitian, LinearMap.mk₂'ₛₗ_apply, Complex.mul_conj]
    exact_mod_cast Complex.normSq_pos.mpr hx
  · intro wt a ha n x y
    by_cases hwt : wt = 0
    · subst hwt
      simp only [oppositeMode, stdHermitian, LinearMap.mk₂'ₛₗ_apply, zpow_zero, one_smul,
        Int.toNat_zero, zero_add, Finset.sum_range_one, Nat.factorial_zero, Nat.cast_one,
        inv_one, pow_zero, Module.End.one_apply, Nat.cast_zero, mul_zero, zero_sub]
      rw [trivialVOAℂ_mode, trivialVOAℂ_mode]
      change _ = x * conj (if n = -1 then conj a * y else 0)
      by_cases hn : n = -1
      · rw [if_pos (by omega), if_pos hn]; simp; ring
      · rw [if_neg (by omega), if_neg hn]; simp
    · have ha0 : a = 0 := PreVertexAlgebra.eq_zero_of_mem_gradingZero ℂ hwt ha
      subst ha0
      have hz : ∀ k : ℤ, (0 : FormalDist (End ℂ ℂ)) k = 0 := fun _ => rfl
      simp [oppositeMode, map_zero, hz]

end VOA
