/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.ExtraspecialModule
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Anti-involutions of `ℂ^c[(ZMod 2)^n]` and invariant forms on `T`  (Moonshine step M8c)

Abstract half of the invariant form on the extraspecial module.  Fix
`M : Matrix (Fin n) (Fin n) (ZMod 2)` with `M + Mᵀ` invertible, the twisted group algebra
`A = alg M` (basis `e_x`, `e_x e_y = c(x,y) e_{x+y}`) and its simple module `T = Rep M hN`, with
`φ = repEquiv : A ≃ End(T)`.

* `algBasis` — the basis `x ↦ e_x` of `A`.
* `iotaA s` — for a sign function `s` with `s 0 = 1` and
  `s(x+y) = s(x) s(y) c(x,y) c(y,x)` (`IsQuadSign`), the linear map `e_x ↦ s(x) e_x`;
  it is an **anti-automorphism** (`iotaA_mul`) and an involution (`iotaA_iotaA`).
* `iotaT s = φ ∘ iotaA s ∘ φ⁻¹` on `End(T)`: `iotaT_mul`, `iotaT_iotaT`, `iotaT_one`,
  `iotaT_op`, and `trace_iotaT` (`tr ∘ ι = tr`, because `tr(φ e_x) = 0` for `x ≠ 0`,
  `trace_op_eq_zero`).
* `formOf s u` — for `u ∈ T*`, `B_u(t,t') = tr(ι(t ⊗ u) ∘ (t' ⊗ u))`.  It is **symmetric**
  (`formOf_symm`, from `tr ∘ ι = tr` and `ι² = 1`) and **ι-invariant**
  (`formOf_invariant : B(X t, t') = B(t, ι(X) t')`); it is **nondegenerate** as soon as it is
  nonzero (`formOf_nondegenerate`: its radical is `End(T)`-stable).
* `exists_form_of_idempotent` — if `P ∈ End(T)` is an idempotent with `ι(P) = P` and
  `tr P = 1` (so `P = v ⊗ u` has rank one), then `B_u(v,v) = tr(P) = 1`, so there is a
  nondegenerate symmetric ι-invariant form.

## Why this route
Every anti-automorphism of `End(T)` is `X ↦ B⁻¹XᵀB` with `B` symmetric or alternating; which one
is decided by the sign function `s`, *not* by the algebra.  Rather than prove Skolem–Noether and a
Frobenius–Schur count over `2^{24}` classes, we produce the form directly from one ι-fixed
rank-one idempotent; such an idempotent exists exactly when `s` has Arf invariant `0`, and for a
lattice it is built from a Lagrangian (see `TForm.lean`).  Symmetry is then free.

## Status
All declarations proved, no `sorry`; see `TForm.lean` for the axiom audit.  Reached from the
umbrella `VOA/Moonshine.lean`.
-/

namespace VOA.Moonshine.Extraspecial

open Matrix Module LinearMap

variable {n : ℕ} (M : Matrix (Fin n) (Fin n) (ZMod 2))

/-- The basis `x ↦ e_x` of the twisted group algebra. -/
noncomputable def algBasis : Basis (Fin n → ZMod 2) ℂ (alg M) :=
  Basis.mk (v := fun x => (⟨op M x, op_mem M x⟩ : alg M))
    (LinearIndependent.of_comp (alg M).val.toLinearMap (linearIndependent_op M))
    (by
      rintro ⟨f, hf⟩ -
      have hx : (⟨f, hf⟩ : alg M)
          = ∑ v, f (Pi.single 0 1) v • (⟨op M v, op_mem _ _⟩ : alg M) := by
        apply Subtype.ext
        rw [AddSubmonoidClass.coe_finsetSum]
        simp only [Subalgebra.coe_smul]
        exact eq_sum_coeff _ hf
      rw [hx]
      exact Submodule.sum_mem _ fun v _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨v, rfl⟩))

theorem algBasis_apply (x : Fin n → ZMod 2) : algBasis M x = ⟨op M x, op_mem M x⟩ := by
  simp [algBasis]

theorem coe_algBasis (x : Fin n → ZMod 2) : (algBasis M x : Module.End ℂ _) = op M x := by
  rw [algBasis_apply]

theorem algBasis_mul (x y : Fin n → ZMod 2) :
    algBasis M x * algBasis M y = coc M x y • algBasis M (x + y) := by
  apply Subtype.ext
  simp only [Subalgebra.coe_mul, Subalgebra.coe_smul, coe_algBasis, op_mul]

theorem algBasis_zero : algBasis M 0 = 1 := by
  apply Subtype.ext; rw [coe_algBasis, op_zero]; rfl

/-- A sign function compatible with the commutator: `s 0 = 1` and
`s(x+y) = s(x) s(y) c(x,y) c(y,x)`. -/
structure IsQuadSign (s : (Fin n → ZMod 2) → ℂ) : Prop where
  zero : s 0 = 1
  add : ∀ x y, s (x + y) = s x * s y * (coc M x y * coc M y x)

variable {M}

theorem IsQuadSign.mul_self {s : (Fin n → ZMod 2) → ℂ} (hs : IsQuadSign M s) (x) :
    s x * s x = 1 := by
  have h := hs.add x x
  rw [add_self_vec, hs.zero, coc_sq, mul_one] at h
  exact h.symm

variable (M)

/-- The anti-involution `e_x ↦ s(x) e_x` of `A`. -/
noncomputable def iotaA (s : (Fin n → ZMod 2) → ℂ) : alg M →ₗ[ℂ] alg M :=
  (algBasis M).constr ℂ fun x => s x • algBasis M x

theorem iotaA_basis (s : (Fin n → ZMod 2) → ℂ) (x) :
    iotaA M s (algBasis M x) = s x • algBasis M x := by
  rw [iotaA, Basis.constr_basis]

variable {M}

theorem iotaA_mul {s : (Fin n → ZMod 2) → ℂ} (hs : IsQuadSign M s) (a b : alg M) :
    iotaA M s (a * b) = iotaA M s b * iotaA M s a := by
  let f : alg M →ₗ[ℂ] alg M →ₗ[ℂ] alg M := (LinearMap.mul ℂ (alg M)).compr₂ (iotaA M s)
  let g : alg M →ₗ[ℂ] alg M →ₗ[ℂ] alg M :=
    (LinearMap.mul ℂ (alg M)).flip.compl₁₂ (iotaA M s) (iotaA M s)
  have hfg : f = g := by
    refine (algBasis M).ext fun x => (algBasis M).ext fun y => ?_
    simp only [f, g, LinearMap.compr₂_apply, LinearMap.mul_apply',
      LinearMap.compl₁₂_apply, LinearMap.flip_apply]
    rw [algBasis_mul, map_smul, iotaA_basis, iotaA_basis, iotaA_basis, smul_mul_smul_comm,
      algBasis_mul, smul_smul, smul_smul, add_comm y x, hs.add]
    congr 1
    linear_combination (s x * s y * coc M y x) * coc_sq M x y
  exact congrArg (fun F : alg M →ₗ[ℂ] alg M →ₗ[ℂ] alg M => F a b) hfg

theorem iotaA_iotaA {s : (Fin n → ZMod 2) → ℂ} (hs : IsQuadSign M s) (a : alg M) :
    iotaA M s (iotaA M s a) = a := by
  have : (iotaA M s).comp (iotaA M s) = LinearMap.id :=
    (algBasis M).ext fun x => by
      rw [LinearMap.comp_apply, iotaA_basis, map_smul, iotaA_basis, smul_smul,
        hs.mul_self, one_smul, LinearMap.id_apply]
  exact congrArg (fun F : alg M →ₗ[ℂ] alg M => F a) this

theorem iotaA_one {s : (Fin n → ZMod 2) → ℂ} (hs : IsQuadSign M s) : iotaA M s 1 = 1 := by
  rw [← algBasis_zero, iotaA_basis, hs.zero, one_smul]

/-! ### Transport to `End(T)` -/

variable (M) (hN : IsUnit (M + Mᵀ).det)

/-- The anti-involution on `End(T)`, transported along `repEquiv`. -/
noncomputable def iotaT (s : (Fin n → ZMod 2) → ℂ) :
    Module.End ℂ (Rep M hN) →ₗ[ℂ] Module.End ℂ (Rep M hN) :=
  (repEquiv M hN).toLinearMap ∘ₗ iotaA M s ∘ₗ (repEquiv M hN).symm.toLinearMap

theorem iotaT_apply (s : (Fin n → ZMod 2) → ℂ) (X : Module.End ℂ (Rep M hN)) :
    iotaT M hN s X = repEquiv M hN (iotaA M s ((repEquiv M hN).symm X)) := rfl

theorem iotaT_repEquiv (s : (Fin n → ZMod 2) → ℂ) (a : alg M) :
    iotaT M hN s (repEquiv M hN a) = repEquiv M hN (iotaA M s a) := by
  rw [iotaT_apply, AlgEquiv.symm_apply_apply]

theorem iotaT_op (s : (Fin n → ZMod 2) → ℂ) (x : Fin n → ZMod 2) :
    iotaT M hN s (repEquiv M hN (algBasis M x)) = s x • repEquiv M hN (algBasis M x) := by
  rw [iotaT_repEquiv, iotaA_basis, map_smul]

variable {M}

theorem iotaT_mul {s : (Fin n → ZMod 2) → ℂ} (hs : IsQuadSign M s)
    (X Y : Module.End ℂ (Rep M hN)) : iotaT M hN s (X * Y) = iotaT M hN s Y * iotaT M hN s X := by
  rw [iotaT_apply, map_mul, iotaA_mul hs, map_mul]; rfl

theorem iotaT_iotaT {s : (Fin n → ZMod 2) → ℂ} (hs : IsQuadSign M s)
    (X : Module.End ℂ (Rep M hN)) : iotaT M hN s (iotaT M hN s X) = X := by
  rw [iotaT_apply, iotaT_apply, AlgEquiv.symm_apply_apply, iotaA_iotaA hs,
    AlgEquiv.apply_symm_apply]

theorem iotaT_one {s : (Fin n → ZMod 2) → ℂ} (hs : IsQuadSign M s) :
    iotaT M hN s 1 = 1 := by
  rw [iotaT_apply, map_one, iotaA_one hs, map_one]

/-! ### The trace -/

variable (M)

/-- `tr(φ e_x) = 0` for `x ≠ 0` (conjugate by an anticommuting `e_w`). -/
theorem trace_op_eq_zero {x : Fin n → ZMod 2} (hx : x ≠ 0) :
    trace ℂ (Rep M hN) (repEquiv M hN (algBasis M x)) = 0 := by
  have hv : (M + Mᵀ) *ᵥ x ≠ 0 := fun h => hx ((mulVec_eq_zero_iff M hN x).mp h)
  obtain ⟨i, hi⟩ : ∃ i, ((M + Mᵀ) *ᵥ x) i ≠ 0 := by
    by_contra h; push Not at h; exact hv (funext h)
  have hi1 : ((M + Mᵀ) *ᵥ x) i = 1 := by
    have : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
    exact this _ hi
  set w : Fin n → ZMod 2 := Pi.single i 1
  have hsg : sgn (w ⬝ᵥ ((M + Mᵀ) *ᵥ x)) = -1 := by
    rw [single_dotProduct, one_mul, hi1, sgn_one]
  -- `c(w,w) e_w e_x e_w = - e_x` in `A`
  have hconj : coc M w w • (algBasis M w * algBasis M x * algBasis M w) = -algBasis M x := by
    apply Subtype.ext
    simp only [Subalgebra.coe_smul, Subalgebra.coe_mul, coe_algBasis, NegMemClass.coe_neg]
    rw [op_conj, hsg, neg_one_smul]
  have hww : algBasis M w * algBasis M w = coc M w w • (1 : alg M) := by
    rw [algBasis_mul, add_self_vec, algBasis_zero]
  set E := fun y => repEquiv M hN (algBasis M y)
  have h1 := congrArg (fun a => trace ℂ (Rep M hN) (repEquiv M hN a)) hconj
  simp only [map_smul, map_mul, map_neg] at h1
  rw [trace_mul_cycle, ← map_mul, hww, map_smul, map_one, smul_mul_assoc, one_mul, map_smul,
    smul_smul, coc_sq, one_smul] at h1
  linear_combination h1 / 2

variable {M}

/-- `tr ∘ ι = tr` on `End(T)`. -/
theorem trace_iotaT {s : (Fin n → ZMod 2) → ℂ} (hs : IsQuadSign M s)
    (X : Module.End ℂ (Rep M hN)) : trace ℂ (Rep M hN) (iotaT M hN s X) = trace ℂ (Rep M hN) X := by
  have key : (trace ℂ (Rep M hN)) ∘ₗ (repEquiv M hN).toLinearMap ∘ₗ iotaA M s
      = (trace ℂ (Rep M hN)) ∘ₗ (repEquiv M hN).toLinearMap :=
    (algBasis M).ext fun x => by
      simp only [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, iotaA_basis,
        map_smul, smul_eq_mul]
      by_cases hx : x = 0
      · rw [hx, hs.zero, one_mul]
      · rw [trace_op_eq_zero M hN hx, mul_zero]
  have := congrArg (fun F : alg M →ₗ[ℂ] ℂ => F ((repEquiv M hN).symm X)) key
  simpa [iotaT_apply] using this

/-! ### The forms `B_u` -/

variable (M)

/-- `B_u(t,t') = tr(ι(t ⊗ u) ∘ (t' ⊗ u))`. -/
noncomputable def formOf (s : (Fin n → ZMod 2) → ℂ) (u : Module.Dual ℂ (Rep M hN)) :
    LinearMap.BilinForm ℂ (Rep M hN) :=
  LinearMap.mk₂ ℂ
    (fun t t' => trace ℂ (Rep M hN) (iotaT M hN s (u.smulRight t) * u.smulRight t'))
    (fun t₁ t₂ t' => by
      beta_reduce
      rw [show u.smulRight (t₁ + t₂) = u.smulRight t₁ + u.smulRight t₂ by ext; simp [smul_add],
        map_add, add_mul, map_add])
    (fun c t t' => by
      beta_reduce
      rw [show u.smulRight (c • t) = c • u.smulRight t by
        ext x; simp only [LinearMap.smulRight_apply, LinearMap.smul_apply]; exact smul_comm _ _ _,
        map_smul, smul_mul_assoc, map_smul, smul_eq_mul])
    (fun t t₁ t₂ => by
      beta_reduce
      rw [show u.smulRight (t₁ + t₂) = u.smulRight t₁ + u.smulRight t₂ by ext; simp [smul_add],
        mul_add, map_add])
    (fun c t t' => by
      beta_reduce
      rw [show u.smulRight (c • t') = c • u.smulRight t' by
        ext x; simp only [LinearMap.smulRight_apply, LinearMap.smul_apply]; exact smul_comm _ _ _,
        mul_smul_comm, map_smul, smul_eq_mul])

theorem formOf_apply (s : (Fin n → ZMod 2) → ℂ) (u : Module.Dual ℂ (Rep M hN)) (t t') :
    formOf M hN s u t t'
      = trace ℂ (Rep M hN) (iotaT M hN s (u.smulRight t) * u.smulRight t') := rfl

theorem mul_smulRight (u : Module.Dual ℂ (Rep M hN)) (X : Module.End ℂ (Rep M hN)) (t) :
    X * u.smulRight t = u.smulRight (X t) := by
  ext c; simp

variable {M}

theorem formOf_symm {s : (Fin n → ZMod 2) → ℂ} (hs : IsQuadSign M s)
    (u : Module.Dual ℂ (Rep M hN)) (t t' : Rep M hN) :
    formOf M hN s u t t' = formOf M hN s u t' t := by
  rw [formOf_apply, formOf_apply, ← trace_iotaT hN hs (iotaT M hN s _ * _), iotaT_mul hN hs,
    iotaT_iotaT hN hs]

/-- **Invariance**: `B_u(X t, t') = B_u(t, ι(X) t')`. -/
theorem formOf_invariant {s : (Fin n → ZMod 2) → ℂ} (hs : IsQuadSign M s)
    (u : Module.Dual ℂ (Rep M hN)) (X : Module.End ℂ (Rep M hN)) (t t' : Rep M hN) :
    formOf M hN s u (X t) t' = formOf M hN s u t (iotaT M hN s X t') := by
  rw [formOf_apply, formOf_apply, ← mul_smulRight, ← mul_smulRight, iotaT_mul hN hs, mul_assoc]

/-- A nonzero `B_u` is **nondegenerate** (its radical is `End(T)`-stable). -/
theorem formOf_nondegenerate {s : (Fin n → ZMod 2) → ℂ} (hs : IsQuadSign M s)
    (u : Module.Dual ℂ (Rep M hN)) {v w : Rep M hN} (hvw : formOf M hN s u v w ≠ 0) :
    (formOf M hN s u).Nondegenerate := by
  have hL : (formOf M hN s u).SeparatingLeft := by
    intro t ht
    by_contra h0
    obtain ⟨f, hf⟩ : ∃ f : Module.Dual ℂ (Rep M hN), f t ≠ 0 := by
      by_contra h; push Not at h
      exact h0 ((forall_dual_apply_eq_zero_iff ℂ t).mp h)
    set X : Module.End ℂ (Rep M hN) := ((f t)⁻¹ • f).smulRight v
    have hX : X t = v := by
      simp [X, inv_mul_cancel₀ hf]
    apply hvw
    rw [← hX, formOf_invariant hN hs]
    exact ht _
  refine ⟨hL, fun y hy => hL y fun x => ?_⟩
  rw [formOf_symm hN hs]
  exact hy x

/-- **Existence**: an idempotent `P` with `ι(P) = P` and `tr P = 1` yields a nondegenerate
symmetric ι-invariant form. -/
theorem exists_form_of_idempotent {s : (Fin n → ZMod 2) → ℂ} (hs : IsQuadSign M s)
    {P : Module.End ℂ (Rep M hN)} (hP : IsIdempotentElem P) (hιP : iotaT M hN s P = P)
    (htr : trace ℂ (Rep M hN) P = 1) :
    ∃ B : LinearMap.BilinForm ℂ (Rep M hN), (∀ t t', B t t' = B t' t) ∧ B.Nondegenerate ∧
      ∀ X t t', B (X t) t' = B t (iotaT M hN s X t') := by
  have hproj := hP.isProj_range
  have hrk : finrank ℂ (LinearMap.range P) = 1 := by
    have := hproj.trace
    rw [htr] at this
    exact_mod_cast this.symm
  let b := finBasisOfFinrankEq ℂ (LinearMap.range P) hrk
  set v : Rep M hN := (b 0 : Rep M hN)
  set u : Module.Dual ℂ (Rep M hN) := b.coord 0 ∘ₗ P.rangeRestrict
  have hPu : u.smulRight v = P := by
    ext c
    simp only [smulRight_apply, u, v]
    have h := b.sum_repr (P.rangeRestrict c)
    rw [Fin.sum_univ_one] at h
    have h' := congrArg Subtype.val h
    simp only [SetLike.val_smul] at h'
    rw [LinearMap.comp_apply, Basis.coord_apply]
    exact h'
  refine ⟨formOf M hN s u, formOf_symm hN hs u, formOf_nondegenerate hN hs u (v := v) (w := v) ?_,
    formOf_invariant hN hs u⟩
  rw [formOf_apply, hPu, hιP, hP.eq, htr]
  exact one_ne_zero

end VOA.Moonshine.Extraspecial
