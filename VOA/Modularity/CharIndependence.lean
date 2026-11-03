/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.SimpleAModFinite
import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Jacobson separation — a ring element that is `1` on one simple module and `0` on the others

This is the algebraic engine of residual **(d)**, `FibreIndependent`: the trace functions of
pairwise non-isomorphic irreducible modules are linearly independent because the *characters of
their bottoms* are, and character separation over a ring is the **Jacobson density theorem**.

Note what is **not** needed: no `C₂`-cofiniteness, no Artin–Wedderburn, no semisimplicity of the
ring, and no finite-dimensionality of the ring.  Only: the modules are simple, pairwise
non-isomorphic, and (for the trace statement) finite-dimensional over `ℂ`.

## The argument

For pairwise non-isomorphic simples `U₀, …, U_{r−1}` put `M = ∏ U_l`.  Schur's lemma
(`LinearMap.bijective_or_eq_zero`) makes every `R`-endomorphism of `M` **block diagonal**, so the
coordinate projection `piProj k` commutes with `End R M` — i.e. it is an element of
`End (End R M) M`.  Jacobson density
(`Module.Finite.toModuleEnd_moduleEnd_surjective`) then realises it as the action of a single
`a : R`, which is therefore the identity on `U k` and zero on every other factor.

## Main results

* `piProj`, `piProj_apply_single`;
* `piProj_comm` — Schur block-diagonality;
* `exists_smul_eq_one_and_zero` — the separating ring element;
* `exists_trace_separating` — the separating **character**.

## Status
Proved, axiom-clean, `pbw`-free, no `sorry`.
-/

namespace VOA

open Module (End)

section Jacobson

universe uR uU

variable {R : Type uR} [Ring R] {r : ℕ} (U : Fin r → Type uU)
  [∀ k, AddCommGroup (U k)] [∀ k, Module R (U k)]

/-- The `k`-th coordinate projection of `∏ U l`, viewed as an endomorphism. -/
def piProj (k : Fin r) : (∀ l, U l) →ₗ[R] (∀ l, U l) :=
  (LinearMap.single R U k).comp (LinearMap.proj (R := R) (φ := U) k)

@[simp] theorem piProj_apply (k : Fin r) (x : ∀ l, U l) :
    piProj (R := R) U k x = Pi.single k (x k) := rfl

/-- Schur: an `R`-endomorphism of `∏ U l` has no off-diagonal blocks. -/
theorem offDiag_eq_zero (hsimp : ∀ k, IsSimpleModule R (U k))
    (hne : ∀ k l : Fin r, k ≠ l → IsEmpty (U k ≃ₗ[R] U l))
    (f : Module.End R (∀ l, U l)) (k l : Fin r) (hkl : l ≠ k) (y : U k) :
    f (Pi.single k y) l = 0 := by
  haveI := hsimp k
  haveI := hsimp l
  set g : U k →ₗ[R] U l :=
    (LinearMap.proj (R := R) (φ := U) l).comp (f.comp (LinearMap.single R U k)) with hg
  rcases LinearMap.bijective_or_eq_zero g with hbij | h0
  · exact ((hne k l (Ne.symm hkl)).false (LinearEquiv.ofBijective g hbij)).elim
  · have := congrArg (fun (t : U k →ₗ[R] U l) => t y) h0
    simpa [hg] using this

/-- **The projection is `End R M`-linear** — the content of Schur's lemma here. -/
theorem piProj_comm (hsimp : ∀ k, IsSimpleModule R (U k))
    (hne : ∀ k l : Fin r, k ≠ l → IsEmpty (U k ≃ₗ[R] U l)) (k : Fin r)
    (f : Module.End R (∀ l, U l)) (x : ∀ l, U l) :
    piProj (R := R) U k (f x) = f (piProj (R := R) U k x) := by
  classical
  have hsplit : ∀ y : ∀ l, U l, y = ∑ l : Fin r, Pi.single l (y l) := by
    intro y; rw [Finset.univ_sum_single]
  have hk : (f x) k = (f (Pi.single k (x k))) k := by
    conv_lhs => rw [hsplit x]
    rw [map_sum]
    have : ∀ l ∈ Finset.univ, l ≠ k → (f (Pi.single l (x l))) k = 0 := by
      intro l _ hlk
      exact offDiag_eq_zero (R := R) U hsimp hne f l k (Ne.symm hlk) (x l)
    rw [Finset.sum_apply]
    rw [Finset.sum_eq_single k (fun l hl hlk => this l hl hlk) (by simp)]
  have hsupp : f (Pi.single k (x k)) = Pi.single k ((f (Pi.single k (x k))) k) := by
    funext l
    by_cases hlk : l = k
    · subst hlk; simp
    · rw [Pi.single_eq_of_ne hlk]
      exact offDiag_eq_zero (R := R) U hsimp hne f k l hlk (x k)
  rw [piProj_apply, piProj_apply, hk, ← hsupp]

variable [IsSemisimpleModule R (∀ l, U l)]
  [Module.Finite (Module.End R (∀ l, U l)) (∀ l, U l)]

/-- **The separating ring element.**  Jacobson density realises the `k`-th projection. -/
theorem exists_smul_eq_one_and_zero (hsimp : ∀ k, IsSimpleModule R (U k))
    (hne : ∀ k l : Fin r, k ≠ l → IsEmpty (U k ≃ₗ[R] U l)) (k : Fin r) :
    ∃ a : R, (∀ y : U k, a • y = y) ∧ ∀ (l : Fin r), l ≠ k → ∀ y : U l, a • y = 0 := by
  classical
  set P : Module.End (Module.End R (∀ l, U l)) (∀ l, U l) :=
    { toFun := piProj (R := R) U k
      map_add' := fun x y => map_add _ x y
      map_smul' := fun f x => piProj_comm (R := R) U hsimp hne k f x } with hP
  obtain ⟨a, ha⟩ := Module.Finite.toModuleEnd_moduleEnd_surjective (R := R)
    (M := (∀ l, U l)) P
  have hact : ∀ x : ∀ l, U l, a • x = piProj (R := R) U k x := by
    intro x
    exact congrArg (fun (t : Module.End (Module.End R (∀ l, U l)) (∀ l, U l)) => t x) ha
  refine ⟨a, ?_, ?_⟩
  · intro y
    have h := hact (Pi.single k y)
    have hsm : a • (Pi.single k y : ∀ l, U l) = Pi.single k (a • y) := by
      funext l
      by_cases hlk : l = k
      · subst hlk; simp
      · simp [Pi.single_eq_of_ne hlk]
    rw [hsm, piProj_apply] at h
    have := congrFun h k
    simpa using this
  · intro l hlk y
    have h := hact (Pi.single l y)
    have hsm : a • (Pi.single l y : ∀ m, U m) = Pi.single l (a • y) := by
      funext m
      by_cases hml : m = l
      · subst hml; simp
      · simp [Pi.single_eq_of_ne hml]
    rw [hsm, piProj_apply] at h
    have h2 := congrFun h l
    rw [Pi.single_eq_same, Pi.single_eq_of_ne hlk] at h2
    exact h2

end Jacobson

section Trace

universe uR' uU'

variable {R : Type uR'} [Ring R] {r : ℕ} (U : Fin r → Type uU')
  [∀ k, AddCommGroup (U k)] [∀ k, Module R (U k)] [∀ k, Module ℂ (U k)]
  [∀ k, SMulCommClass R ℂ (U k)] [∀ k, FiniteDimensional ℂ (U k)]

/-- The action of `a : R` on the `l`-th factor, as a `ℂ`-endomorphism. -/
def actC (a : R) (l : Fin r) : U l →ₗ[ℂ] U l where
  toFun x := a • x
  map_add' x y := smul_add a x y
  map_smul' c x := smul_comm a c x

@[simp] theorem actC_apply (a : R) (l : Fin r) (x : U l) : actC U a l x = a • x := rfl

/-- **The separating character.**  For pairwise non-isomorphic simple modules there is a ring
element whose trace is nonzero on the `k`-th and zero on all the others.  This is the linear
independence of characters that residual **(d)** consumes. -/
theorem exists_trace_separating [IsSemisimpleModule R (∀ l, U l)]
    [Module.Finite (Module.End R (∀ l, U l)) (∀ l, U l)]
    (hsimp : ∀ k, IsSimpleModule R (U k))
    (hne : ∀ k l : Fin r, k ≠ l → IsEmpty (U k ≃ₗ[R] U l)) (k : Fin r) :
    ∃ a : R, LinearMap.trace ℂ (U k) (actC U a k) ≠ 0 ∧
      ∀ l : Fin r, l ≠ k → LinearMap.trace ℂ (U l) (actC U a l) = 0 := by
  obtain ⟨a, hone, hzero⟩ := exists_smul_eq_one_and_zero (R := R) U hsimp hne k
  refine ⟨a, ?_, ?_⟩
  · have hid : actC U a k = LinearMap.id := by
      refine LinearMap.ext fun y => ?_
      rw [actC_apply, hone y]; rfl
    rw [hid, LinearMap.trace_id]
    haveI := (hsimp k).nontrivial
    have hpos : 0 < Module.finrank ℂ (U k) := Module.finrank_pos
    exact_mod_cast Nat.cast_ne_zero.mpr hpos.ne'
  · intro l hlk
    have h0 : actC U a l = 0 := by
      refine LinearMap.ext fun y => ?_
      rw [actC_apply, hzero l hlk y]; rfl
    rw [h0, map_zero]

end Trace

end VOA
