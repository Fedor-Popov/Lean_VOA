/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import Mathlib.Data.Matrix.Action
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.Data.Matrix.Basis

/-!
# A product of `n` matrix algebras has `n` pairwise non-isomorphic simple modules

This is the module-theoretic half of DLM Lemma 10.7's bookkeeping (link **L1**): together with
`Modularity.SemisimpleTrace.finrank_quot_commSpan_pi_eq` (`dim (A/[A,A]) = n`) it says the
Wedderburn factor count is bounded above by the number of isomorphism classes of simple modules —
the direction Zhu's count actually consumes.

For `A = ∏_{i<n} Mat_{dᵢ}(K)` the `j`-th simple module is `Kᵈʲ` with `A` acting through the
projection `Pi.evalRingHom`.  Simplicity is the usual "one nonzero vector generates" argument;
pairwise non-isomorphism is the central idempotent `Pi.single j 1`, which acts as `1` on the `j`-th
module and as `0` on the others.

## Main results

* `piSimple K d j` — the `j`-th simple module, with its `A`-module structure;
* `piSimple_isSimpleModule`;
* `piSimple_isEmpty_linearEquiv` — pairwise non-isomorphic.

## Status
Proved, axiom-clean, `pbw`-free, no `sorry`.
-/

namespace VOA

open scoped BigOperators

section

variable (K : Type*) [Field K] {n : ℕ} (d : Fin n → ℕ)

/-- The product of matrix algebras. -/
abbrev PiMat : Type _ := ∀ i : Fin n, Matrix (Fin (d i)) (Fin (d i)) K

/-- The `j`-th candidate simple module of `∏ᵢ Mat_{dᵢ}(K)` — a type synonym for `K^{dⱼ}` so that
the `j`-dependent module structure is an instance. -/
def piSimple (j : Fin n) : Type _ := Fin (d j) → K

namespace piSimple

variable {K d}

instance (j : Fin n) : AddCommGroup (piSimple K d j) :=
  inferInstanceAs (AddCommGroup (Fin (d j) → K))

instance (j : Fin n) : Module (Matrix (Fin (d j)) (Fin (d j)) K) (piSimple K d j) :=
  inferInstanceAs (Module (Matrix (Fin (d j)) (Fin (d j)) K) (Fin (d j) → K))

/-- `∏ᵢ Mat_{dᵢ}(K)` acts on the `j`-th factor's vectors through the `j`-th projection. -/
instance instModulePiMat (j : Fin n) : Module (PiMat K d) (piSimple K d j) :=
  Module.compHom _ (Pi.evalRingHom (fun i => Matrix (Fin (d i)) (Fin (d i)) K) j)

theorem smul_def (j : Fin n) (a : PiMat K d) (v : piSimple K d j) :
    a • v = (a j : Matrix (Fin (d j)) (Fin (d j)) K) • (v : Fin (d j) → K) := rfl

end piSimple

variable {K d}

/-- Any nonzero vector generates: for `v ≠ 0` and any `w` there is a matrix carrying `v` to `w`. -/
theorem exists_matrix_mulVec_eq {m : ℕ} {v : Fin m → K} (hv : v ≠ 0)
    (w : Fin m → K) : ∃ A : Matrix (Fin m) (Fin m) K, Matrix.mulVec A v = w := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hv (funext hc)
  refine ⟨Matrix.of fun a b => if b = i then w a / v i else 0, ?_⟩
  funext a
  show ∑ b, (if b = i then w a / v i else 0) * v b = w a
  rw [Finset.sum_eq_single i (fun b _ hb => by rw [if_neg hb, zero_mul])
    (fun hc => absurd (Finset.mem_univ i) hc), if_pos rfl]
  exact div_mul_cancel₀ _ hi

/-- **Each `piSimple K d j` is a simple `∏ᵢ Mat_{dᵢ}(K)`-module.** -/
theorem piSimple_isSimpleModule (hd : ∀ i, NeZero (d i)) (j : Fin n) :
    IsSimpleModule (PiMat K d) (piSimple K d j) := by
  classical
  haveI : NeZero (d j) := hd j
  haveI : Nontrivial (piSimple K d j) := by
    refine ⟨0, Pi.single ⟨0, Nat.pos_of_ne_zero (hd j).out⟩ 1, ?_⟩
    intro hc
    have := congrFun hc ⟨0, Nat.pos_of_ne_zero (hd j).out⟩
    rw [Pi.single_eq_same] at this
    exact one_ne_zero this.symm
  rw [isSimpleModule_iff]
  refine { eq_bot_or_eq_top := fun N => ?_ }
  by_cases hN : N = ⊥
  · exact Or.inl hN
  · right
    obtain ⟨v, hvN, hv0⟩ : ∃ v ∈ N, v ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hN (Submodule.eq_bot_iff N |>.mpr hc)
    rw [eq_top_iff]
    intro w _
    obtain ⟨A, hA⟩ := exists_matrix_mulVec_eq (v := (v : Fin (d j) → K)) hv0 (w : Fin (d j) → K)
    have hmem : (Pi.single j A : PiMat K d) • v ∈ N := N.smul_mem _ hvN
    have hEq : (Pi.single j A : PiMat K d) • v = w := by
      rw [piSimple.smul_def, Pi.single_eq_same]
      exact hA
    rwa [hEq] at hmem

/-- **Distinct factors give non-isomorphic simple modules.**  The central idempotent
`Pi.single i 1` acts as the identity on `piSimple … i` and as zero on `piSimple … j`. -/
theorem piSimple_isEmpty_linearEquiv (hd : ∀ i, NeZero (d i)) {i j : Fin n} (hij : i ≠ j) :
    IsEmpty (piSimple K d i ≃ₗ[PiMat K d] piSimple K d j) := by
  classical
  haveI : NeZero (d i) := hd i
  refine ⟨fun φ => ?_⟩
  set e : PiMat K d := Pi.single i 1 with he
  have hone : ∀ x : piSimple K d i, e • x = x := by
    intro x
    rw [piSimple.smul_def, he, Pi.single_eq_same, one_smul]
  have hzero : ∀ y : piSimple K d j, e • y = 0 := by
    intro y
    rw [piSimple.smul_def, he, Pi.single_eq_of_ne (Ne.symm hij), zero_smul]
  have hx : ∀ x : piSimple K d i, φ x = 0 := by
    intro x
    rw [← hone x, map_smul, hzero]
  have hinj := φ.injective
  have h0 : (0 : piSimple K d i) ≠ Pi.single ⟨0, Nat.pos_of_ne_zero (hd i).out⟩ 1 := by
    intro hc
    have := congrFun hc ⟨0, Nat.pos_of_ne_zero (hd i).out⟩
    rw [Pi.single_eq_same] at this
    exact one_ne_zero this.symm
  exact h0 (hinj (by rw [hx, hx]))

end

end VOA
