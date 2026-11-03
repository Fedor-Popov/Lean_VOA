/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Core.Dong
import VOA.Foundations.Parity
import Mathlib.Tactic.Module
import Mathlib.Tactic.LinearCombination

/-!
# Dong's lemma, `ε`-generically  (Axis B of the super generalization)

The `n ≥ 0` case of Dong's lemma for the **sign-twisted** commutator `bracketDistε`, so
that the bosonic and super theories are two instances of one proof rather than two
parallel developments.

## What is and is not `ε`-dependent

The point of this file is that almost nothing is.  Reused **verbatim** from `Core.Dong`,
because they never mention the bracket:

`mulBySub₂₃Pow_eq_sum`, `mulBySub₂₁Pow_sign`, `comm₂₃₁₂`, `comm₁₃₁₂`, `comm₂₃₁₃`,
`comm₂₁₁₃`, `reorder₂₃₁₂`, `reorder₁₃₁₂`, `reorder₂₃₁₃`, `reorder₂₁₁₃`,
`mulBySub₂₃Pow_add`, `mulBySub₁₂Pow_add`, `mulBySubPow_mono₂`, `res₁`, `res₁_mulBySubPow`,
`res₁_zero`, `cCoeff`.

In particular `mulBySub₂₁Pow_sign`'s `(-1)ⁱ` is the *variable* sign from
`z₂ - z₁ = -(z₁ - z₂)`; it has nothing to do with parity and is untouched.

Genuinely `ε`-dependent, and re-proved here: the three outer brackets, their pass-through
lemmas, the Jacobi identity, the core vanishing lemma, and Dong's lemma itself.

## The one piece of real mathematics

`jacobi₃ε` is the **super-Jacobi identity**

  `⁅⁅a,b⁆,c⁆ = ⁅a,⁅b,c⁆⁆ - ε_ab ⁅b,⁅a,c⁆⁆`,

with the outer signs distributed as `ε_{⁅a,b⁆,c} = ε_ac ε_bc` (the bracket has parity
`|a| + |b|`; see `VOA.koszul_add_left`).  Its proof needs, and only needs,
`ε_ab² = 1` — supplied in the super case by `VOA.koszul_mul_self`.  Everything
downstream inherits its signs from this one identity.

## Status
`sorry`-free / axiom-free.  `dong_nonnegε` specializes to the existing `dong_nonneg`
at `ε = 1` (`dong_nonneg_of_dong_nonnegε`), so this is a generalization, not a fork.

## References
* Gannon §5.1.2; Kac, *Vertex Algebras for Beginners*, §3.2 and §4.1 (super case);
  Lepowsky–Li §3.2.
-/

namespace VOA

open Module (End)

universe v

variable {V : Type v} [AddCommGroup V] [Module ℂ V]

/-! ## The `ε`-twisted outer brackets -/

/-- `outerAε ε a X := ⁅a(z₁), X(z₂,z₃)⁆_ε`. -/
def outerAε (ε : ℂ) (a : FormalDist (End ℂ V)) (X : FormalDist₂ (End ℂ V)) :
    FormalDist₃ (End ℂ V) :=
  fun m n p => a m * X n p - ε • (X n p * a m)

/-- `outerBε ε b X := ⁅b(z₂), X(z₁,z₃)⁆_ε`. -/
def outerBε (ε : ℂ) (b : FormalDist (End ℂ V)) (X : FormalDist₂ (End ℂ V)) :
    FormalDist₃ (End ℂ V) :=
  fun m n p => b n * X m p - ε • (X m p * b n)

/-- `outerC₁₂ε ε X c := ⁅X(z₁,z₂), c(z₃)⁆_ε`. -/
def outerC₁₂ε (ε : ℂ) (X : FormalDist₂ (End ℂ V)) (c : FormalDist (End ℂ V)) :
    FormalDist₃ (End ℂ V) :=
  fun m n p => X m n * c p - ε • (c p * X m n)

@[simp] theorem outerAε_apply (ε : ℂ) (a : FormalDist (End ℂ V)) (X : FormalDist₂ (End ℂ V))
    (m n p : ℤ) : outerAε ε a X m n p = a m * X n p - ε • (X n p * a m) := rfl

@[simp] theorem outerBε_apply (ε : ℂ) (b : FormalDist (End ℂ V)) (X : FormalDist₂ (End ℂ V))
    (m n p : ℤ) : outerBε ε b X m n p = b n * X m p - ε • (X m p * b n) := rfl

@[simp] theorem outerC₁₂ε_apply (ε : ℂ) (X : FormalDist₂ (End ℂ V)) (c : FormalDist (End ℂ V))
    (m n p : ℤ) : outerC₁₂ε ε X c m n p = X m n * c p - ε • (c p * X m n) := rfl

/-- At `ε = 1` the twisted outer bracket is the ordinary one. -/
theorem outerAε_one (a : FormalDist (End ℂ V)) (X : FormalDist₂ (End ℂ V)) :
    outerAε 1 a X = outerA a X := by
  apply FormalDist₃.ext; intro m n p; simp

/-- At `ε = 1` the twisted outer bracket is the ordinary one. -/
theorem outerBε_one (b : FormalDist (End ℂ V)) (X : FormalDist₂ (End ℂ V)) :
    outerBε 1 b X = outerB b X := by
  apply FormalDist₃.ext; intro m n p; simp

/-- At `ε = 1` the twisted outer bracket is the ordinary one. -/
theorem outerC₁₂ε_one (X : FormalDist₂ (End ℂ V)) (c : FormalDist (End ℂ V)) :
    outerC₁₂ε 1 X c = outerC₁₂ X c := by
  apply FormalDist₃.ext; intro m n p; simp

@[simp] theorem outerAε_zero (ε : ℂ) (a : FormalDist (End ℂ V)) :
    outerAε ε a (0 : FormalDist₂ (End ℂ V)) = 0 := by
  apply FormalDist₃.ext; intro m n p
  show a m * (0 : End ℂ V) - ε • ((0 : End ℂ V) * a m) = 0; simp

@[simp] theorem outerBε_zero (ε : ℂ) (b : FormalDist (End ℂ V)) :
    outerBε ε b (0 : FormalDist₂ (End ℂ V)) = 0 := by
  apply FormalDist₃.ext; intro m n p
  show b n * (0 : End ℂ V) - ε • ((0 : End ℂ V) * b n) = 0; simp

@[simp] theorem outerC₁₂ε_zero (ε : ℂ) (c : FormalDist (End ℂ V)) :
    outerC₁₂ε ε (0 : FormalDist₂ (End ℂ V)) c = 0 := by
  apply FormalDist₃.ext; intro m n p
  show (0 : End ℂ V) * c p - ε • (c p * (0 : End ℂ V)) = 0; simp

/-! ## The difference operators pass through the outer field (unchanged by `ε`) -/

/-- `(z₂-z₃)` on `outerAε ε a X` passes to `X`. -/
theorem mulBySub₂₃_outerAε (ε : ℂ) (a : FormalDist (End ℂ V)) (X : FormalDist₂ (End ℂ V)) :
    mulBySub₂₃ (outerAε ε a X) = outerAε ε a (mulBySub X) := by
  apply FormalDist₃.ext; intro m n p
  simp only [mulBySub₂₃_apply, outerAε_apply, mulBySub_apply, mul_sub, sub_mul, smul_sub]
  abel

/-- `(z₁-z₃)` on `outerBε ε b X` passes to `X`. -/
theorem mulBySub₁₃_outerBε (ε : ℂ) (b : FormalDist (End ℂ V)) (X : FormalDist₂ (End ℂ V)) :
    mulBySub₁₃ (outerBε ε b X) = outerBε ε b (mulBySub X) := by
  apply FormalDist₃.ext; intro m n p
  simp only [mulBySub₁₃_apply, outerBε_apply, mulBySub_apply, mul_sub, sub_mul, smul_sub]
  abel

/-- `(z₁-z₂)` on `outerC₁₂ε ε X c` passes to `X`. -/
theorem mulBySub₁₂_outerC₁₂ε (ε : ℂ) (X : FormalDist₂ (End ℂ V)) (c : FormalDist (End ℂ V)) :
    mulBySub₁₂ (outerC₁₂ε ε X c) = outerC₁₂ε ε (mulBySub X) c := by
  apply FormalDist₃.ext; intro m n p
  simp only [mulBySub₁₂_apply, outerC₁₂ε_apply, mulBySub_apply, mul_sub, sub_mul, smul_sub]
  abel

/-- Iterated: `(z₂-z₃)ᵏ` on `outerAε ε a X` passes to `X`. -/
theorem mulBySub₂₃Pow_outerAε (k : ℕ) (ε : ℂ) (a : FormalDist (End ℂ V))
    (X : FormalDist₂ (End ℂ V)) :
    mulBySub₂₃Pow k (outerAε ε a X) = outerAε ε a (mulBySubPow k X) := by
  induction k generalizing X with
  | zero => rfl
  | succ j ih => rw [mulBySub₂₃Pow_succ, LinearMap.comp_apply, ih, mulBySub₂₃_outerAε,
      ← LinearMap.comp_apply, ← mulBySubPow_succ]

/-- Iterated: `(z₁-z₃)ᵏ` on `outerBε ε b X` passes to `X`. -/
theorem mulBySub₁₃Pow_outerBε (k : ℕ) (ε : ℂ) (b : FormalDist (End ℂ V))
    (X : FormalDist₂ (End ℂ V)) :
    mulBySub₁₃Pow k (outerBε ε b X) = outerBε ε b (mulBySubPow k X) := by
  induction k generalizing X with
  | zero => rfl
  | succ j ih => rw [mulBySub₁₃Pow_succ, LinearMap.comp_apply, ih, mulBySub₁₃_outerBε,
      ← LinearMap.comp_apply, ← mulBySubPow_succ]

/-- Iterated: `(z₁-z₂)ᵏ` on `outerC₁₂ε ε X c` passes to `X`. -/
theorem mulBySub₁₂Pow_outerC₁₂ε (k : ℕ) (ε : ℂ) (X : FormalDist₂ (End ℂ V))
    (c : FormalDist (End ℂ V)) :
    mulBySub₁₂Pow k (outerC₁₂ε ε X c) = outerC₁₂ε ε (mulBySubPow k X) c := by
  induction k generalizing X with
  | zero => rfl
  | succ j ih => rw [mulBySub₁₂Pow_succ, LinearMap.comp_apply, ih, mulBySub₁₂_outerC₁₂ε,
      ← LinearMap.comp_apply, ← mulBySubPow_succ]

/-! ## The super-Jacobi identity -/

/-- **The super-Jacobi identity**, lifted to three variables:

  `⁅⁅a,b⁆_{ε_ab}, c⁆_{ε_ac ε_bc} = ⁅a, ⁅b,c⁆_{ε_bc}⁆_{ε_ab ε_ac}
       - ε_ab • ⁅b, ⁅a,c⁆_{ε_ac}⁆_{ε_ab ε_bc}`.

The outer sign on the left is `ε_ac ε_bc` because `⁅a,b⁆` has parity `|a| + |b|`
(`VOA.koszul_add_left`).  The proof needs exactly one fact about the signs,
`ε_ab² = 1`; in the super case that is `VOA.koszul_mul_self`.

At `εab = εac = εbc = 1` this is the ordinary `jacobi₃`. -/
theorem jacobi₃ε (εab εac εbc : ℂ) (hab : εab * εab = 1) (a b c : FormalDist (End ℂ V)) :
    outerC₁₂ε (εac * εbc) (bracketDistε εab a b) c
      = outerAε (εab * εac) a (bracketDistε εbc b c)
        - εab • outerBε (εab * εbc) b (bracketDistε εac a c) := by
  apply FormalDist₃.ext; intro m n p
  show (a m * b n - εab • (b n * a m)) * c p
      - (εac * εbc) • (c p * (a m * b n - εab • (b n * a m)))
    = (a m * (b n * c p - εbc • (c p * b n))
        - (εab * εac) • ((b n * c p - εbc • (c p * b n)) * a m))
      - εab • (b n * (a m * c p - εac • (c p * a m))
        - (εab * εbc) • ((a m * c p - εac • (c p * a m)) * b n))
  simp only [sub_mul, mul_sub, smul_sub, smul_mul_assoc, mul_smul_comm, smul_smul, mul_assoc]
  -- the single place `ε² = 1` is used; everything else is `ring` on the scalars
  rw [show εab * (εab * (εbc * εac)) = εbc * εac by rw [← mul_assoc, hab, one_mul]]
  -- NB `ring1`, not `ring`: inside `first`, `ring` falls back to `ring_nf` and *succeeds*
  -- without closing the goal, so the alternatives below would never be tried.
  match_scalars <;>
    first
      | ring1
      | linear_combination (εbc : ℂ) * hab
      | linear_combination (-εbc : ℂ) * hab
      | linear_combination (εbc * εac : ℂ) * hab
      | linear_combination (-(εbc * εac) : ℂ) * hab

/-! ## The core vanishing lemma and Dong's lemma, `ε`-generically -/

/-- **The three-variable core of Dong's lemma, `ε`-generically.**  Identical in shape and
proof to `dong_core`; the only new input is the super-Jacobi identity and the hypothesis
`ε_ab² = 1` it rests on. -/
theorem dong_coreε (εab εac εbc : ℂ) (hab2 : εab * εab = 1)
    (a b c : FormalDist (End ℂ V)) {r : ℕ}
    (hab : mulBySubPow r (bracketDistε εab a b) = 0)
    (hac : mulBySubPow r (bracketDistε εac a c) = 0)
    (hbc : mulBySubPow r (bracketDistε εbc b c) = 0)
    (k M : ℕ) (hM : 2 * r ≤ M) :
    mulBySub₂₃Pow (M + r)
      (mulBySub₁₂Pow k (outerC₁₂ε (εac * εbc) (bracketDistε εab a b) c)) = 0 := by
  have killA : ∀ s, r ≤ s →
      mulBySub₂₃Pow s (outerAε (εab * εac) a (bracketDistε εbc b c)) = 0 := fun s hs => by
    rw [mulBySub₂₃Pow_outerAε, mulBySubPow_mono₂ hs hbc, outerAε_zero]
  have killB : ∀ s, r ≤ s →
      mulBySub₁₃Pow s (outerBε (εab * εbc) b (bracketDistε εac a c)) = 0 := fun s hs => by
    rw [mulBySub₁₃Pow_outerBε, mulBySubPow_mono₂ hs hac, outerBε_zero]
  have killC : ∀ s, r ≤ s →
      mulBySub₁₂Pow s (outerC₁₂ε (εac * εbc) (bracketDistε εab a b) c) = 0 := fun s hs => by
    rw [mulBySub₁₂Pow_outerC₁₂ε, mulBySubPow_mono₂ hs hab, outerC₁₂ε_zero]
  -- Jacobi rearranged.  `jac''` is the only place the `εab` factor appears, and `ε² = 1`
  -- is exactly what lets it be moved to the other side.
  have jac' : εab • outerBε (εab * εbc) b (bracketDistε εac a c)
      = outerAε (εab * εac) a (bracketDistε εbc b c)
        - outerC₁₂ε (εac * εbc) (bracketDistε εab a b) c := by
    rw [jacobi₃ε εab εac εbc hab2 a b c]; abel
  have jac'' : outerBε (εab * εbc) b (bracketDistε εac a c)
      = εab • (outerAε (εab * εac) a (bracketDistε εbc b c)
        - outerC₁₂ε (εac * εbc) (bracketDistε εab a b) c) := by
    rw [← jac', smul_smul, hab2, one_smul]
  rw [jacobi₃ε εab εac εbc hab2 a b c, map_sub, map_sub, reorder₂₃₁₂,
    killA (M + r) (by omega), map_zero, zero_sub, neg_eq_zero]
  -- Factor the `εab` out of Part II; what remains is the bosonic argument verbatim.
  rw [map_smul, map_smul]
  refine smul_eq_zero_of_right _ ?_
  rw [show M + r = r + M from Nat.add_comm M r, mulBySub₂₃Pow_add,
    mulBySub₂₃Pow_eq_sum M
      (mulBySub₁₂Pow k (outerBε (εab * εbc) b (bracketDistε εac a c))), map_sum]
  apply Finset.sum_eq_zero
  intro i hi
  rw [map_nsmul]
  have hiM : i ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  suffices h : mulBySub₂₃Pow r (mulBySub₂₁Pow i (mulBySub₁₃Pow (M - i)
      (mulBySub₁₂Pow k (outerBε (εab * εbc) b (bracketDistε εac a c))))) = 0 by
    rw [h, smul_zero]
  by_cases hle : i ≤ M - r
  · rw [reorder₁₃₁₂, killB (M - i) (by omega), map_zero, map_zero, map_zero]
  · rw [reorder₂₁₁₃, reorder₂₃₁₃, mulBySub₂₁Pow_sign, map_smul, ← mulBySub₁₂Pow_add, jac'',
      map_smul, map_smul, map_sub, killC (i + k) (by omega), sub_zero, map_smul,
      reorder₂₃₁₂, killA r le_rfl]
    simp

/-- The `ε`-bracket of the field `k`-th product with `c` is the `Res_{z₁}` of the
three-variable double bracket. -/
theorem bracketDistε_cCoeff (ε : ℂ) (g : FormalDist₂ (End ℂ V)) (c : FormalDist (End ℂ V))
    (k : ℕ) :
    bracketDistε ε (cCoeff k g) c = res₁ (mulBySub₁₂Pow k (outerC₁₂ε ε g c)) := by
  apply FormalDist₂.ext; intro n p
  simp only [bracketDistε_apply, cCoeff_apply, res₁_apply, mulBySub₁₂Pow_outerC₁₂ε,
    outerC₁₂ε_apply]

/-- **Dong's lemma (`n ≥ 0` case), `ε`-generically.**  For pairwise `ε`-locally-commuting
`a, b, c`, the field `k`-th product `a₍ₖ₎b = cCoeff k ⁅a,b⁆_{ε_ab}` is `ε_ac ε_bc`-local
with `c`.  The signs compose exactly as parities add. -/
theorem dong_nonnegε {εab εac εbc : ℂ} (hab2 : εab * εab = 1)
    {a b c : FormalDist (End ℂ V)}
    (hab : Localε εab a b) (hac : Localε εac a c) (hbc : Localε εbc b c) (k : ℕ) :
    Localε (εac * εbc) (cCoeff k (bracketDistε εab a b)) c := by
  obtain ⟨Nab, hNab⟩ := hab
  obtain ⟨Nac, hNac⟩ := hac
  obtain ⟨Nbc, hNbc⟩ := hbc
  set r := max Nab (max Nac Nbc) with hr
  have hab' : mulBySubPow r (bracketDistε εab a b) = 0 :=
    mulBySubPow_mono₂ (le_max_left _ _) hNab
  have hac' : mulBySubPow r (bracketDistε εac a c) = 0 :=
    mulBySubPow_mono₂ (le_trans (le_max_left _ _) (le_max_right _ _)) hNac
  have hbc' : mulBySubPow r (bracketDistε εbc b c) = 0 :=
    mulBySubPow_mono₂ (le_trans (le_max_right _ _) (le_max_right _ _)) hNbc
  refine ⟨2 * r + r, ?_⟩
  rw [bracketDistε_cCoeff, res₁_mulBySubPow,
    dong_coreε εab εac εbc hab2 a b c hab' hac' hbc' k (2 * r) le_rfl, res₁_zero]

/-! ## The bosonic theory is the instance `ε = 1` -/

/-- The existing bosonic Dong lemma is the `ε = 1` case of `dong_nonnegε`: this is a
generalization of `Core.Dong`, not a parallel development. -/
theorem dong_nonneg_of_dong_nonnegε {a b c : FormalDist (End ℂ V)}
    (hab : Local a b) (hac : Local a c) (hbc : Local b c) (k : ℕ) :
    Local (cCoeff k (bracketDist a b)) c := by
  have h := dong_nonnegε (εab := 1) (εac := 1) (εbc := 1) (by norm_num)
    ((localε_one_iff a b).2 hab) ((localε_one_iff a c).2 hac) ((localε_one_iff b c).2 hbc) k
  rw [bracketDistε_one] at h
  rw [← localε_one_iff]
  simpa using h

end VOA
