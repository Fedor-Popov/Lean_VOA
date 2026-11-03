/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.DSMorphismSl2

/-!
# Affine sl2 actions on abstract matter super vertex algebras

`AffineSl2Action V k` specifies three actual states of `V`, of weight one and even
parity, whose modes satisfy the complete affine commutator at level `k`.
`AffineSl2Action.current_ope` recovers the formal-distribution OPE, including the
double pole with the repository's normalized form `κ(e,f)=1`, `κ(h,h)=2`.
The structure is inhabited by the existing universal affine algebra (`affineAction`).

This is the matter input for the diagonal semi-infinite construction. It imposes
no simplicity or unitarity condition, and makes no nilpotency assertion.
-/

namespace VOA.Sl2SemiInfinite

open Module (End)
open AffineVOA
open scoped BigOperators

universe u

variable {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- An even affine sl2 current action on a matter super vertex algebra.
The commutator specifies all modes, not just a truncation of the OPE. -/
structure AffineSl2Action (V : SuperVertexAlgebra M) (k : ℂ) where
  current : Fin 3 → M
  current_weight : ∀ a, current a ∈ V.grading 1
  current_even : ∀ a, current a ∈ V.parity 0
  current_comm : ∀ (a b : Fin 3) (m n : ℤ),
    mode (V.Y (current a)) m * mode (V.Y (current b)) n
      - mode (V.Y (current b)) n * mode (V.Y (current a)) m
      = (∑ c, fabc a b c • mode (V.Y (current c)) (m + n))
        + if m + n = 0 then ((m : ℂ) * k * kappa a b) • LinearMap.id else 0

namespace AffineSl2Action

variable {V : SuperVertexAlgebra M} {k : ℂ} (A : AffineSl2Action V k)

/-- The simple-pole coefficient field. -/
noncomputable def simplePole (a b : Fin 3) : FormalDist (End ℂ M) :=
  fun j => ∑ c, fabc a b c • V.Y (A.current c) j

/-- The double-pole coefficient, as a constant identity-valued field. -/
noncomputable def doublePole (_A : AffineSl2Action V k) (a b : Fin 3) :
    FormalDist (End ℂ M) :=
  fun j => if j = 0 then (k * kappa a b) • LinearMap.id else 0

/-- The full affine OPE, with exactly a simple and a double pole. -/
theorem current_ope (a b : Fin 3) :
    bracketDist (V.Y (A.current a)) (V.Y (A.current b))
      = deltaDeriv 0 (A.simplePole a b) + deltaDeriv 1 (A.doublePole a b) := by
  refine FormalDist₂.ext fun m n => ?_
  have hc := A.current_comm a b (-m - 1) (-n - 1)
  simp only [mode_apply, show -(-m - 1) - 1 = m by omega,
    show -(-n - 1) - 1 = n by omega] at hc
  rw [bracketDist_apply, hc]
  change (∑ c, fabc a b c • V.Y (A.current c) (-(-m - 1 + (-n - 1)) - 1))
      + (if -m - 1 + (-n - 1) = 0 then
          (((-m - 1 : ℤ) : ℂ) * k * kappa a b) • LinearMap.id else 0)
    = deltaDeriv 0 (A.simplePole a b) m n + deltaDeriv 1 (A.doublePole a b) m n
  rw [deltaDeriv_apply, deltaDeriv_apply]
  simp only [simplePole, doublePole]
  rw [Finset.range_zero, Finset.prod_empty, one_smul,
    Finset.range_one, Finset.prod_singleton, Nat.cast_zero, sub_zero, Nat.cast_one]
  congr 1
  · refine Finset.sum_congr rfl fun c _ => ?_
    rw [show -(-m - 1 + (-n - 1)) - 1 = m + n + 1 + 0 by ring]
  · by_cases hmn : (-m - 1) + (-n - 1) = 0
    · rw [if_pos hmn, if_pos (by omega : m + n + 1 + 1 = 0),
        ← Int.cast_smul_eq_zsmul ℂ (-m - 1 : ℤ)
          ((k * kappa a b) • LinearMap.id : End ℂ M), smul_smul, mul_assoc]
    · rw [if_neg hmn, if_neg (by omega : ¬ m + n + 1 + 1 = 0)]
      exact (smul_zero _).symm

/-- The affine currents have uniform locality bound two. -/
theorem current_local (a b : Fin 3) : Local (V.Y (A.current a)) (V.Y (A.current b)) := by
  refine ⟨2, ?_⟩
  rw [A.current_ope, map_add, mulBySubPow_deltaDeriv_eq_zero (by norm_num),
    mulBySubPow_deltaDeriv_eq_zero (by norm_num), add_zero]

/-- Nonnegative current products on current states, before specializing the mode.
This follows by applying the affine commutator to the vacuum. -/
theorem current_product (a b : Fin 3) (n : ℤ) (hn : 0 ≤ n) :
    mode (V.Y (A.current a)) n (A.current b)
      = (∑ c, fabc a b c • mode (V.Y (A.current c)) (n - 1) V.vacuum)
        + if n = 1 then (k * kappa a b) • V.vacuum else 0 := by
  have hc := congrArg (fun f : End ℂ M => f V.vacuum) (A.current_comm a b n (-1))
  simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.add_apply,
    LinearMap.sum_apply, LinearMap.smul_apply] at hc
  rw [(V.creation (A.current b)).1, (V.creation (A.current a)).2 n hn,
    map_zero, sub_zero] at hc
  rw [hc]
  simp only [sub_eq_add_neg]
  congr 1
  by_cases h : n = 1
  · subst n
    simp
  · rw [if_neg h, if_neg (by omega)]
    rfl

/-- The simple-pole state is the sl2 bracket. -/
theorem current_product_zero (a b : Fin 3) :
    mode (V.Y (A.current a)) 0 (A.current b) = ∑ c, fabc a b c • A.current c := by
  rw [A.current_product a b 0 (by omega)]
  simp only [zero_sub, (V.creation _).1, zero_ne_one, if_false, add_zero]

/-- The double-pole state records the level with the normalized Killing form. -/
theorem current_product_one (a b : Fin 3) :
    mode (V.Y (A.current a)) 1 (A.current b) = (k * kappa a b) • V.vacuum := by
  rw [A.current_product a b 1 (by omega)]
  simp only [sub_self, (V.creation _).2 0 (by omega), smul_zero,
    Finset.sum_const_zero, ite_true, zero_add]

/-- There are no poles of order three or higher. -/
theorem current_product_high (a b : Fin 3) (n : ℤ) (hn : 2 ≤ n) :
    mode (V.Y (A.current a)) n (A.current b) = 0 := by
  rw [A.current_product a b n (by omega)]
  simp only [(V.creation _).2 (n - 1) (by omega), smul_zero,
    Finset.sum_const_zero, if_neg (by omega : n ≠ 1), add_zero]

end AffineSl2Action

/-- The existing universal affine algebra supplies the abstract matter input. -/
noncomputable def affineAction (k : ℂ) (hk : k + 2 ≠ 0) :
    AffineSl2Action (DSsl2.affSVA k hk) k where
  current a := J k a (-1) (vacuumA k)
  current_weight a := by
    have h := J_mem_gradingZA k a (-1) 0 (vacuumA_mem_gradingZA_zero k)
    have hg : (DSsl2.affSVA k hk).grading 1 = gradingZA k 1 := by
      change (Vir.affineVA k hk).gradingC 1 = _
      rw [← show ((1 : ℤ) : ℂ) = 1 by norm_num, (Vir.affineVA k hk).gradingC_intCast]
      rfl
    rw [hg]
    simpa using h
  current_even a := DSMor.mem_parity_zero_toSuper (Vir.affineVA k hk) _
  current_comm a b m n := by
    change mode (YA k hk (J k a (-1) (vacuumA k))) m *
        mode (YA k hk (J k b (-1) (vacuumA k))) n -
        mode (YA k hk (J k b (-1) (vacuumA k))) n *
        mode (YA k hk (J k a (-1) (vacuumA k))) m =
      (∑ c, fabc a b c • mode (YA k hk (J k c (-1) (vacuumA k))) (m + n)) + _
    simp only [Vir.YA_current_state, Jfield_mode]
    exact current_comm k a b m n

end VOA.Sl2SemiInfinite
