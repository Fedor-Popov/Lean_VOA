/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Foundations.FormalDist3
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NoncommRing
import Mathlib.Data.Int.Interval

/-!
# Dong's lemma  (Gannon §5.1.2; Kac §3.2; Lepowsky–Li §3.2; FLM §8)

**Dong's lemma** is the structural input of the reconstruction theorems: the field
`n`-th product of two mutually-local fields is local with any third local field.  Combined
with `Core.Goddard.goddard_uniqueness` it discharges the unmet locality hypothesis and
unblocks the duality/Borcherds cascade.

This file proves the **`n ≥ 0` (singular / commutator) case**: for pairwise-local
`End ℂ V`-valued distributions `a, b, c`, the field `k`-th product
`a₍ₖ₎b := Res_{z₁}((z₁-z₂)ᵏ[a(z₁),b(z₂)]) = cCoeff k (bracketDist a b)`
is mutually local with `c`.

## The proof (three variables)

Writing `[[a(z₁),b(z₂)],c(z₃)]` as a three-variable distribution, the heart is the
identity
  `(z₂-z₃)ᴺ (z₁-z₂)ᵏ [[a(z₁),b(z₂)],c(z₃)] = 0`   (for `N` large).
By the operator Jacobi identity `[[a,b],c] = [a,[b,c]] - [b,[a,c]]`:
* `[a,[b,c]]` is killed by `(z₂-z₃)ʳ` (locality of `b,c`), since `(z₂-z₃)` passes through
  the outer `a(z₁)` to the inner `[b(z₂),c(z₃)]`;
* `[b,[a,c]]` is handled by binomially expanding `(z₂-z₃) = (z₂-z₁)+(z₁-z₃)`
  (`mulBySub₂₃Pow_eq_sum`): terms with a high `(z₁-z₃)`-power die by locality of `a,c`;
  the remaining terms have a high `(z₂-z₁) = -(z₁-z₂)`-power which, combined with the
  ambient `(z₁-z₂)ᵏ`, kills the `[[b,a],c]` part (locality of `a,b`) while a *reserve*
  factor `(z₂-z₃)ʳ` kills the `[a,[b,c]]` part.
All difference operators commute, which lets us reorder freely.

Taking `Res_{z₁}` then gives `(z₂-z₃)ᴺ [a₍ₖ₎b(z₂), c(z₃)] = 0`, i.e. mutual locality.

## Dependencies
* `VOA.Foundations.FormalDist3`, `VOA.Foundations.Locality`.

## Status
**Complete** & `sorry`-free / axiom-free.  Dong's lemma holds for **all `n`**:

* **`n ≥ 0`** (`dong_nonneg`): the commutator product `a₍ₖ₎b = cCoeff k (bracketDist a b)` is
  local with any third local field, via the three-variable `dong_core` vanishing identity.
* **`n < 0`** (`dong_neg`): the **same-variable normal-ordered product** `:a(z)b(z): = a₍₋₁₎b`
  (`nprod`, built via the algebraically-summable `finsum` discipline so the infinite operator
  sum converges on the lower-truncated fields `IsField`) is local with any third local field —
  Li's normal-product locality.  The proof lifts `[:a(z₁)b(z₂):, c(z₃)]` to three variables,
  annihilates it with the pairwise-locality powers (`mulBySub_normalOrderedBracket_eq_zero`,
  reusing `dong_core` for the gated triple commutator), and collapses the diagonal `z₁ = z₂`
  (`diag3`).  The `n < 0` fieldMul `negProd` `a₍₋ₘ₋₁₎b = (1/m!):(∂_z^m a)b:` and `IsField.deriv`
  are built on top; the vertex operators are fields (`Core.Reconstruction.isField_Y`).

## References
* Gannon §5.1.2; Kac, *VA for Beginners*, §3.2 (Lemma on `n`-th products / Dong's lemma);
  Lepowsky–Li, §3.2; Frenkel–Lepowsky–Meurman, §8.
-/

namespace VOA

open Module (End)

universe v

variable {V : Type v} [AddCommGroup V] [Module ℂ V]

/-! ## Monotonicity of the two-variable locality power (local helpers) -/

/-- `(z₁-z₂)^{a+b} = (z₁-z₂)ᵃ·(z₁-z₂)ᵇ` on `FormalDist₂`. -/
theorem mulBySubPow_add₂ (a b : ℕ) (f : FormalDist₂ (End ℂ V)) :
    mulBySubPow (a + b) f = mulBySubPow a (mulBySubPow b f) := by
  induction a with
  | zero => simp
  | succ k ih =>
      rw [Nat.succ_add, mulBySubPow_succ, LinearMap.comp_apply, ih, ← LinearMap.comp_apply,
        ← mulBySubPow_succ]

/-- If `(z₁-z₂)ᴺ f = 0` then `(z₁-z₂)ᴹ f = 0` for `M ≥ N` (`FormalDist₂`). -/
theorem mulBySubPow_mono₂ {N M : ℕ} (h : N ≤ M) {f : FormalDist₂ (End ℂ V)}
    (hf : mulBySubPow N f = 0) : mulBySubPow M f = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_comm, mulBySubPow_add₂, hf, map_zero]

/-! ## The three "outer commutator" lifts

Each lifts a one-variable field bracketed with a two-variable distribution into
`FormalDist₃`.  The pattern: multiplication by `(zᵢ-zⱼ)` in the two *inner* variables
passes through the outer field to the inner two-variable distribution. -/

/-- `outerA a X := [a(z₁), X(z₂,z₃)]`. -/
def outerA (a : FormalDist (End ℂ V)) (X : FormalDist₂ (End ℂ V)) : FormalDist₃ (End ℂ V) :=
  fun m n p => a m * X n p - X n p * a m

/-- `outerB b X := [b(z₂), X(z₁,z₃)]`. -/
def outerB (b : FormalDist (End ℂ V)) (X : FormalDist₂ (End ℂ V)) : FormalDist₃ (End ℂ V) :=
  fun m n p => b n * X m p - X m p * b n

/-- `outerC₁₂ X c := [X(z₁,z₂), c(z₃)]`. -/
def outerC₁₂ (X : FormalDist₂ (End ℂ V)) (c : FormalDist (End ℂ V)) : FormalDist₃ (End ℂ V) :=
  fun m n p => X m n * c p - c p * X m n

@[simp] theorem outerA_apply (a : FormalDist (End ℂ V)) (X : FormalDist₂ (End ℂ V)) (m n p : ℤ) :
    outerA a X m n p = a m * X n p - X n p * a m := rfl
@[simp] theorem outerB_apply (b : FormalDist (End ℂ V)) (X : FormalDist₂ (End ℂ V)) (m n p : ℤ) :
    outerB b X m n p = b n * X m p - X m p * b n := rfl
@[simp] theorem outerC₁₂_apply (X : FormalDist₂ (End ℂ V)) (c : FormalDist (End ℂ V)) (m n p : ℤ) :
    outerC₁₂ X c m n p = X m n * c p - c p * X m n := rfl

@[simp] theorem outerA_zero (a : FormalDist (End ℂ V)) :
    outerA a (0 : FormalDist₂ (End ℂ V)) = 0 := by
  apply FormalDist₃.ext; intro m n p
  show a m * (0 : End ℂ V) - (0 : End ℂ V) * a m = 0; simp
@[simp] theorem outerB_zero (b : FormalDist (End ℂ V)) :
    outerB b (0 : FormalDist₂ (End ℂ V)) = 0 := by
  apply FormalDist₃.ext; intro m n p
  show b n * (0 : End ℂ V) - (0 : End ℂ V) * b n = 0; simp
@[simp] theorem outerC₁₂_zero (c : FormalDist (End ℂ V)) :
    outerC₁₂ (0 : FormalDist₂ (End ℂ V)) c = 0 := by
  apply FormalDist₃.ext; intro m n p
  show (0 : End ℂ V) * c p - c p * (0 : End ℂ V) = 0; simp

/-! ## The difference operators pass through the outer field -/

/-- `(z₂-z₃)` on `outerA a X` passes to `X`. -/
theorem mulBySub₂₃_outerA (a : FormalDist (End ℂ V)) (X : FormalDist₂ (End ℂ V)) :
    mulBySub₂₃ (outerA a X) = outerA a (mulBySub X) := by
  apply FormalDist₃.ext; intro m n p
  simp only [mulBySub₂₃_apply, outerA_apply, mulBySub_apply, mul_sub, sub_mul]; abel

/-- `(z₁-z₃)` on `outerB b X` passes to `X`. -/
theorem mulBySub₁₃_outerB (b : FormalDist (End ℂ V)) (X : FormalDist₂ (End ℂ V)) :
    mulBySub₁₃ (outerB b X) = outerB b (mulBySub X) := by
  apply FormalDist₃.ext; intro m n p
  simp only [mulBySub₁₃_apply, outerB_apply, mulBySub_apply, mul_sub, sub_mul]; abel

/-- `(z₁-z₂)` on `outerC₁₂ X c` passes to `X`. -/
theorem mulBySub₁₂_outerC₁₂ (X : FormalDist₂ (End ℂ V)) (c : FormalDist (End ℂ V)) :
    mulBySub₁₂ (outerC₁₂ X c) = outerC₁₂ (mulBySub X) c := by
  apply FormalDist₃.ext; intro m n p
  simp only [mulBySub₁₂_apply, outerC₁₂_apply, mulBySub_apply, mul_sub, sub_mul]; abel

/-- Iterated: `(z₂-z₃)ᵏ` on `outerA a X` passes to `X`. -/
theorem mulBySub₂₃Pow_outerA (k : ℕ) (a : FormalDist (End ℂ V)) (X : FormalDist₂ (End ℂ V)) :
    mulBySub₂₃Pow k (outerA a X) = outerA a (mulBySubPow k X) := by
  induction k generalizing X with
  | zero => rfl
  | succ j ih => rw [mulBySub₂₃Pow_succ, LinearMap.comp_apply, ih, mulBySub₂₃_outerA,
      ← LinearMap.comp_apply, ← mulBySubPow_succ]

/-- Iterated: `(z₁-z₃)ᵏ` on `outerB b X` passes to `X`. -/
theorem mulBySub₁₃Pow_outerB (k : ℕ) (b : FormalDist (End ℂ V)) (X : FormalDist₂ (End ℂ V)) :
    mulBySub₁₃Pow k (outerB b X) = outerB b (mulBySubPow k X) := by
  induction k generalizing X with
  | zero => rfl
  | succ j ih => rw [mulBySub₁₃Pow_succ, LinearMap.comp_apply, ih, mulBySub₁₃_outerB,
      ← LinearMap.comp_apply, ← mulBySubPow_succ]

/-- Iterated: `(z₁-z₂)ᵏ` on `outerC₁₂ X c` passes to `X`. -/
theorem mulBySub₁₂Pow_outerC₁₂ (k : ℕ) (X : FormalDist₂ (End ℂ V)) (c : FormalDist (End ℂ V)) :
    mulBySub₁₂Pow k (outerC₁₂ X c) = outerC₁₂ (mulBySubPow k X) c := by
  induction k generalizing X with
  | zero => rfl
  | succ j ih => rw [mulBySub₁₂Pow_succ, LinearMap.comp_apply, ih, mulBySub₁₂_outerC₁₂,
      ← LinearMap.comp_apply, ← mulBySubPow_succ]

/-! ## Reordering the (commuting) difference operators -/

/-- `mulBySub₁₂Pow N = mulBySub₁₂ ^ N`. -/
theorem mulBySub₁₂Pow_eq_npow (N : ℕ) :
    (mulBySub₁₂Pow N : FormalDist₃ V →ₗ[ℂ] _) = mulBySub₁₂ ^ N := by
  induction N with
  | zero => rfl
  | succ k ih => rw [mulBySub₁₂Pow_succ, ih, pow_succ']; rfl

/-- Commuting powers, applied to a distribution. -/
theorem comm_pow_apply {f g : Module.End ℂ (FormalDist₃ V)} (h : Commute f g) (m n : ℕ)
    (X : FormalDist₃ V) : (f ^ m) ((g ^ n) X) = (g ^ n) ((f ^ m) X) := by
  have hp : f ^ m * g ^ n = g ^ n * f ^ m := h.pow_pow m n
  calc (f ^ m) ((g ^ n) X) = (f ^ m * g ^ n) X := (Module.End.mul_apply _ _ _).symm
    _ = (g ^ n * f ^ m) X := by rw [hp]
    _ = (g ^ n) ((f ^ m) X) := Module.End.mul_apply _ _ _

/-- A one-step commutation of two difference operators, given they commute coefficient-wise. -/
private theorem comm_of_apply
    {F G : FormalDist₃ V →ₗ[ℂ] FormalDist₃ V}
    (h : ∀ (f : FormalDist₃ V) (m n p : ℤ), F (G f) m n p = G (F f) m n p) :
    Commute F G := by
  show F * G = G * F
  ext f m n p
  exact h f m n p

theorem comm₂₃₁₂ : Commute (mulBySub₂₃ : FormalDist₃ V →ₗ[ℂ] _) mulBySub₁₂ :=
  comm_of_apply fun f m n p => by
    simp only [mulBySub₂₃_apply, mulBySub₁₂_apply]; abel
theorem comm₁₃₁₂ : Commute (mulBySub₁₃ : FormalDist₃ V →ₗ[ℂ] _) mulBySub₁₂ :=
  comm_of_apply fun f m n p => by
    simp only [mulBySub₁₃_apply, mulBySub₁₂_apply]; abel
theorem comm₂₃₁₃ : Commute (mulBySub₂₃ : FormalDist₃ V →ₗ[ℂ] _) mulBySub₁₃ :=
  comm_of_apply fun f m n p => by
    simp only [mulBySub₂₃_apply, mulBySub₁₃_apply]; abel
theorem comm₂₁₁₃ : Commute (mulBySub₂₁ : FormalDist₃ V →ₗ[ℂ] _) mulBySub₁₃ :=
  comm_of_apply fun f m n p => by
    simp only [mulBySub₂₁_apply, mulBySub₁₃_apply]; abel

/-- Reorder `(z₂-z₃)ᴺ` past `(z₁-z₂)ᵏ`. -/
theorem reorder₂₃₁₂ (N k : ℕ) (X : FormalDist₃ V) :
    mulBySub₂₃Pow N (mulBySub₁₂Pow k X) = mulBySub₁₂Pow k (mulBySub₂₃Pow N X) := by
  rw [mulBySub₂₃Pow_eq_npow, mulBySub₁₂Pow_eq_npow]; exact comm_pow_apply comm₂₃₁₂ N k X

/-- Reorder `(z₁-z₃)ᴺ` past `(z₁-z₂)ᵏ`. -/
theorem reorder₁₃₁₂ (N k : ℕ) (X : FormalDist₃ V) :
    mulBySub₁₃Pow N (mulBySub₁₂Pow k X) = mulBySub₁₂Pow k (mulBySub₁₃Pow N X) := by
  rw [mulBySub₁₃Pow_eq_npow, mulBySub₁₂Pow_eq_npow]; exact comm_pow_apply comm₁₃₁₂ N k X

/-- Reorder `(z₂-z₃)ᴺ` past `(z₁-z₃)ᵏ`. -/
theorem reorder₂₃₁₃ (N k : ℕ) (X : FormalDist₃ V) :
    mulBySub₂₃Pow N (mulBySub₁₃Pow k X) = mulBySub₁₃Pow k (mulBySub₂₃Pow N X) := by
  rw [mulBySub₂₃Pow_eq_npow, mulBySub₁₃Pow_eq_npow]; exact comm_pow_apply comm₂₃₁₃ N k X

/-- Reorder `(z₂-z₁)ᴺ` past `(z₁-z₃)ᵏ`. -/
theorem reorder₂₁₁₃ (N k : ℕ) (X : FormalDist₃ V) :
    mulBySub₂₁Pow N (mulBySub₁₃Pow k X) = mulBySub₁₃Pow k (mulBySub₂₁Pow N X) := by
  rw [mulBySub₂₁Pow_eq_npow, mulBySub₁₃Pow_eq_npow]; exact comm_pow_apply comm₂₁₁₃ N k X

/-! ## `Pow_add`, the `(z₂-z₁) = -(z₁-z₂)` sign, and the Jacobi identity -/

/-- `(z₂-z₃)^{s+t} = (z₂-z₃)ˢ·(z₂-z₃)ᵗ`. -/
theorem mulBySub₂₃Pow_add (s t : ℕ) (X : FormalDist₃ V) :
    mulBySub₂₃Pow (s + t) X = mulBySub₂₃Pow s (mulBySub₂₃Pow t X) := by
  rw [mulBySub₂₃Pow_eq_npow, mulBySub₂₃Pow_eq_npow, mulBySub₂₃Pow_eq_npow, pow_add,
    Module.End.mul_apply]

/-- `(z₁-z₂)^{s+t} = (z₁-z₂)ˢ·(z₁-z₂)ᵗ`. -/
theorem mulBySub₁₂Pow_add (s t : ℕ) (X : FormalDist₃ V) :
    mulBySub₁₂Pow (s + t) X = mulBySub₁₂Pow s (mulBySub₁₂Pow t X) := by
  rw [mulBySub₁₂Pow_eq_npow, mulBySub₁₂Pow_eq_npow, mulBySub₁₂Pow_eq_npow, pow_add,
    Module.End.mul_apply]

/-- `(z₂-z₁)ⁱ = (-1)ⁱ·(z₁-z₂)ⁱ`, applied to a distribution. -/
theorem mulBySub₂₁Pow_sign (i : ℕ) (X : FormalDist₃ V) :
    mulBySub₂₁Pow i X = ((-1 : ℂ) ^ i) • mulBySub₁₂Pow i X := by
  induction i with
  | zero => simp
  | succ j ih =>
      have h21 : mulBySub₂₁Pow (j + 1) X = mulBySub₂₁ (mulBySub₂₁Pow j X) := rfl
      have h12 : mulBySub₁₂Pow (j + 1) X = mulBySub₁₂ (mulBySub₁₂Pow j X) := rfl
      rw [h21, ih, map_smul, mulBySub₂₁_eq_neg, LinearMap.neg_apply, h12, pow_succ,
        mul_smul, neg_one_smul]

/-- **The operator Jacobi identity** `[[a,b],c] = [a,[b,c]] - [b,[a,c]]`, lifted to three
variables. -/
theorem jacobi₃ (a b c : FormalDist (End ℂ V)) :
    outerC₁₂ (bracketDist a b) c
      = outerA a (bracketDist b c) - outerB b (bracketDist a c) := by
  apply FormalDist₃.ext; intro m n p
  show outerC₁₂ (bracketDist a b) c m n p
    = outerA a (bracketDist b c) m n p - outerB b (bracketDist a c) m n p
  simp only [outerC₁₂_apply, outerA_apply, outerB_apply, bracketDist_apply]
  noncomm_ring

/-! ## The core vanishing lemma and Dong's lemma -/

/-- **The three-variable core of Dong's lemma**: for pairwise-local `a, b, c` (common order
`r`), the distribution `(z₂-z₃)^{M+r} (z₁-z₂)ᵏ [[a(z₁),b(z₂)],c(z₃)]` vanishes (any `k`, and
`M ≥ 2r`).  This is the identity sketched in the file header. -/
theorem dong_core (a b c : FormalDist (End ℂ V)) {r : ℕ}
    (hab : mulBySubPow r (bracketDist a b) = 0)
    (hac : mulBySubPow r (bracketDist a c) = 0)
    (hbc : mulBySubPow r (bracketDist b c) = 0)
    (k M : ℕ) (hM : 2 * r ≤ M) :
    mulBySub₂₃Pow (M + r) (mulBySub₁₂Pow k (outerC₁₂ (bracketDist a b) c)) = 0 := by
  -- annihilation lemmas (each difference power passes through its outer field, then locality)
  have killA : ∀ s, r ≤ s → mulBySub₂₃Pow s (outerA a (bracketDist b c)) = 0 := fun s hs => by
    rw [mulBySub₂₃Pow_outerA, mulBySubPow_mono₂ hs hbc, outerA_zero]
  have killB : ∀ s, r ≤ s → mulBySub₁₃Pow s (outerB b (bracketDist a c)) = 0 := fun s hs => by
    rw [mulBySub₁₃Pow_outerB, mulBySubPow_mono₂ hs hac, outerB_zero]
  have killC : ∀ s, r ≤ s → mulBySub₁₂Pow s (outerC₁₂ (bracketDist a b) c) = 0 := fun s hs => by
    rw [mulBySub₁₂Pow_outerC₁₂, mulBySubPow_mono₂ hs hab, outerC₁₂_zero]
  -- Jacobi rearranged: outerB b AC = outerA a BC - outerC₁₂ AB c
  have jac' : outerB b (bracketDist a c)
      = outerA a (bracketDist b c) - outerC₁₂ (bracketDist a b) c := by
    rw [jacobi₃ a b c]; abel
  -- split D = outerA a BC - outerB b AC; the outerA part dies by (z₂-z₃)ʳ
  rw [jacobi₃ a b c, map_sub, map_sub, reorder₂₃₁₂, killA (M + r) (by omega), map_zero,
    zero_sub, neg_eq_zero]
  -- remaining (Part II): mulBySub₂₃Pow (M+r) (mulBySub₁₂Pow k (outerB b AC)) = 0
  rw [show M + r = r + M from Nat.add_comm M r, mulBySub₂₃Pow_add,
    mulBySub₂₃Pow_eq_sum M (mulBySub₁₂Pow k (outerB b (bracketDist a c))), map_sum]
  apply Finset.sum_eq_zero
  intro i hi
  rw [map_nsmul]
  have hiM : i ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  suffices h : mulBySub₂₃Pow r (mulBySub₂₁Pow i
      (mulBySub₁₃Pow (M - i) (mulBySub₁₂Pow k (outerB b (bracketDist a c))))) = 0 by
    rw [h, smul_zero]
  by_cases hle : i ≤ M - r
  · -- i ≤ M-r ⟹ M-i ≥ r ⟹ the (z₁-z₃)^{M-i} factor kills outerB
    rw [reorder₁₃₁₂, killB (M - i) (by omega), map_zero, map_zero, map_zero]
  · -- i > M-r ⟹ i+k ≥ r; reorder, use the (z₁-z₂)^{i+k} and reserve (z₂-z₃)ʳ
    rw [reorder₂₁₁₃, reorder₂₃₁₃, mulBySub₂₁Pow_sign, map_smul, ← mulBySub₁₂Pow_add, jac',
      map_sub, killC (i + k) (by omega), sub_zero, reorder₂₃₁₂, killA r le_rfl, map_zero,
      smul_zero, map_zero]

/-! ## From the core identity to mutual locality (`Res_{z₁}`) -/

/-- The `z₁`-residue (coefficient of `z₁⁻¹`) of a three-variable distribution, a
two-variable distribution in `z₂, z₃`. -/
def res₁ (G : FormalDist₃ (End ℂ V)) : FormalDist₂ (End ℂ V) := fun n p => G (-1) n p

@[simp] theorem res₁_apply (G : FormalDist₃ (End ℂ V)) (n p : ℤ) : res₁ G n p = G (-1) n p := rfl

@[simp] theorem res₁_zero : res₁ (0 : FormalDist₃ (End ℂ V)) = 0 := by
  apply FormalDist₂.ext; intro n p; show (0 : End ℂ V) = (0 : FormalDist₂ (End ℂ V)) n p; rfl

/-- `Res_{z₁}` intertwines the two-variable `(z₂-z₃)` with the three-variable `(z₂-z₃)`. -/
theorem res₁_mulBySub (G : FormalDist₃ (End ℂ V)) :
    mulBySub (res₁ G) = res₁ (mulBySub₂₃ G) := by
  apply FormalDist₂.ext; intro n p
  simp only [mulBySub_apply, res₁_apply, mulBySub₂₃_apply]

/-- Iterated: `Res_{z₁}` intertwines `(z₂-z₃)ᴺ`. -/
theorem res₁_mulBySubPow (N : ℕ) (G : FormalDist₃ (End ℂ V)) :
    mulBySubPow N (res₁ G) = res₁ (mulBySub₂₃Pow N G) := by
  induction N generalizing G with
  | zero => rfl
  | succ k ih => rw [mulBySubPow_succ, LinearMap.comp_apply, ih, res₁_mulBySub,
      ← LinearMap.comp_apply, ← mulBySub₂₃Pow_succ]

/-- The bracket of the field `k`-th product with `c` is the `Res_{z₁}` of the three-variable
double bracket: `[a₍ₖ₎b(z₂), c(z₃)] = Res_{z₁}((z₁-z₂)ᵏ[[a,b],c])`. -/
theorem bracketDist_cCoeff (g : FormalDist₂ (End ℂ V)) (c : FormalDist (End ℂ V)) (k : ℕ) :
    bracketDist (cCoeff k g) c = res₁ (mulBySub₁₂Pow k (outerC₁₂ g c)) := by
  apply FormalDist₂.ext; intro n p
  simp only [bracketDist_apply, cCoeff_apply, res₁_apply, mulBySub₁₂Pow_outerC₁₂, outerC₁₂_apply]

/-- **Dong's lemma (`n ≥ 0` case)** (Gannon §5.1.2; Kac §3.2): for pairwise mutually-local
`a, b, c`, the field `k`-th product `a₍ₖ₎b = cCoeff k (bracketDist a b)` is mutually local
with `c`. -/
theorem dong_nonneg {a b c : FormalDist (End ℂ V)}
    (hab : Local a b) (hac : Local a c) (hbc : Local b c) (k : ℕ) :
    Local (cCoeff k (bracketDist a b)) c := by
  obtain ⟨Nab, hNab⟩ := hab
  obtain ⟨Nac, hNac⟩ := hac
  obtain ⟨Nbc, hNbc⟩ := hbc
  set r := max Nab (max Nac Nbc) with hr
  have hab' : mulBySubPow r (bracketDist a b) = 0 := mulBySubPow_mono₂ (le_max_left _ _) hNab
  have hac' : mulBySubPow r (bracketDist a c) = 0 :=
    mulBySubPow_mono₂ (le_trans (le_max_left _ _) (le_max_right _ _)) hNac
  have hbc' : mulBySubPow r (bracketDist b c) = 0 :=
    mulBySubPow_mono₂ (le_trans (le_max_right _ _) (le_max_right _ _)) hNbc
  refine ⟨2 * r + r, ?_⟩
  rw [bracketDist_cCoeff, res₁_mulBySubPow,
    dong_core a b c hab' hac' hbc' k (2 * r) le_rfl, res₁_zero]

/-! ## The normal-ordered same-variable field product `:a(z)b(z):` (M1(c))

For two **fields** `a, b` (lower-truncated on every vector) the same-variable normal-ordered
product `:a(z)b(z):` is itself a field.  This is the `n = -1` field product `a₍₋₁₎b`; together
with its `z`-derivatives it supplies the `n < 0` branch of the reconstruction (the
normal-ordered duality 5.1.9a).  Unlike the purely algebraic two-variable `normalOrdered`, the
*same-variable* product is an infinite operator sum that converges only on the lower-truncated
fields, so it is built via the algebraically-summable (`finsum`) discipline (Gannon p. 315). -/

/-- An `End ℂ V`-valued distribution is a **field** when it is lower-truncated on every
vector: `aₙ x = 0` for `n ≪ 0` (Gannon §5.1.2).  The vertex operators `Y(u,z)` are fields by
VA5 regularity. -/
def IsField (a : FormalDist (End ℂ V)) : Prop :=
  ∀ x : V, ∃ B : ℤ, ∀ n : ℤ, n < B → a n x = 0

/-- The diagonal summand of `:a(z)b(z):` has finite support in `m` (for fixed `s, x`): the
`m ≥ 0` part is bounded above by `b`'s lower truncation, the `m < 0` part below by `a`'s.
This is what makes the same-variable normal product algebraically defined. -/
theorem normalOrdered_diag_support_finite {a b : FormalDist (End ℂ V)}
    (ha : IsField a) (hb : IsField b) (s : ℤ) (x : V) :
    (Function.support (fun m : ℤ => normalOrdered a b m (s - m) x)).Finite := by
  obtain ⟨Ba, hBa⟩ := ha x
  obtain ⟨Bb, hBb⟩ := hb x
  apply Set.Finite.subset (Set.finite_Icc (min Ba 0) (max (s - Bb) 0))
  intro m hm
  rw [Function.mem_support, normalOrdered_apply] at hm
  rw [Set.mem_Icc]
  by_cases h0 : 0 ≤ m
  · rw [if_pos h0] at hm
    have hb' : b (s - m) x ≠ 0 := fun hbz => hm (by rw [Module.End.mul_apply, hbz, map_zero])
    have : ¬ (s - m < Bb) := fun hlt => hb' (hBb (s - m) hlt)
    omega
  · rw [if_neg h0] at hm
    have ha' : a m x ≠ 0 := fun haz => hm (by rw [Module.End.mul_apply, haz, map_zero])
    have : ¬ (m < Ba) := fun hlt => ha' (hBa m hlt)
    omega

/-- The `z^s`-coefficient operator of `:a(z)b(z):`, defined by its (finite, by
`normalOrdered_diag_support_finite`) action on each vector:
`(:ab:)ₛ x = ∑_{m} (:ab:)_{m,s-m} x` (Gannon 5.1.6b, same-variable). -/
noncomputable def nprodCoeff {a b : FormalDist (End ℂ V)}
    (ha : IsField a) (hb : IsField b) (s : ℤ) : V →ₗ[ℂ] V where
  toFun x := ∑ᶠ m : ℤ, normalOrdered a b m (s - m) x
  map_add' x y := by
    rw [← finsum_add_distrib (normalOrdered_diag_support_finite ha hb s x)
        (normalOrdered_diag_support_finite ha hb s y)]
    exact finsum_congr fun m => map_add _ x y
  map_smul' c x := by
    rw [RingHom.id_apply, smul_finsum' c (normalOrdered_diag_support_finite ha hb s x)]
    exact finsum_congr fun m => map_smul _ c x

/-- The **same-variable normal-ordered product** `:a(z)b(z):` of two fields (Gannon 5.1.6b):
the `n = -1` field product `a₍₋₁₎b`, a field again. -/
noncomputable def nprod {a b : FormalDist (End ℂ V)}
    (ha : IsField a) (hb : IsField b) : FormalDist (End ℂ V) :=
  fun s => nprodCoeff ha hb s

@[simp] theorem nprod_apply {a b : FormalDist (End ℂ V)} (ha : IsField a) (hb : IsField b)
    (s : ℤ) (x : V) :
    nprod ha hb s x = ∑ᶠ m : ℤ, normalOrdered a b m (s - m) x := rfl

/-- The formal derivative of a field is a field (the lower-truncation bound shifts by `1`):
`∂_z a(z)` is again lower-truncated on every vector.  This makes the `z`-derivatives of a
field available for the `n < -1` normal-ordered products `a₍₋ₘ₋₁₎b = (1/m!):(∂_z^m a)b:`. -/
theorem IsField.deriv {a : FormalDist (End ℂ V)} (ha : IsField a) :
    IsField (VOA.deriv a) := by
  intro x
  obtain ⟨B, hB⟩ := ha x
  refine ⟨B - 1, fun n hn => ?_⟩
  have h0 : a (n + 1) x = 0 := hB (n + 1) (by omega)
  show (VOA.deriv a) n x = 0
  rw [deriv_apply]
  show ((n + 1 : ℤ) • a (n + 1)) x = 0
  rw [LinearMap.smul_apply, h0, smul_zero]

/-- Iterated: the `m`-th derivative of a field is a field. -/
theorem IsField.deriv_iterate {a : FormalDist (End ℂ V)} (ha : IsField a) (m : ℕ) :
    IsField ((VOA.deriv^[m]) a) := by
  induction m with
  | zero => simpa using ha
  | succ k ih => rw [Function.iterate_succ', Function.comp_apply]; exact ih.deriv

/-- The **negative (normal-ordered) field product** `a₍₋ₘ₋₁₎b = (1/m!) :(∂_z^m a(z)) b(z):`
(Gannon 5.1.9a, the `n < 0` branch of the field `n`-th product) for fields `a, b`.  Together
with the `n ≥ 0` commutator product `cCoeff k (bracketDist a b)` this realizes the field
`n`-th product at every integer index `n = -m-1 < 0`. -/
noncomputable def negProd {a b : FormalDist (End ℂ V)} (ha : IsField a) (hb : IsField b)
    (m : ℕ) : FormalDist (End ℂ V) :=
  (m.factorial : ℂ)⁻¹ • nprod (ha.deriv_iterate m) hb

/-- The `n = -1` negative product is the bare normal-ordered product `:a(z)b(z):`. -/
theorem negProd_zero {a b : FormalDist (End ℂ V)} (ha : IsField a) (hb : IsField b) :
    negProd ha hb 0 = nprod (ha.deriv_iterate 0) hb := by
  rw [negProd]; simp

@[simp] theorem negProd_apply {a b : FormalDist (End ℂ V)} (ha : IsField a) (hb : IsField b)
    (m : ℕ) (s : ℤ) (x : V) :
    negProd ha hb m s x
      = (m.factorial : ℂ)⁻¹ • (nprod (ha.deriv_iterate m) hb s x) := by
  change ((m.factorial : ℂ)⁻¹ • (nprod (ha.deriv_iterate m) hb s)) x = _
  rw [LinearMap.smul_apply]

/-! ## Full Dong's lemma: locality of the `n<0` normal-ordered product (M1(c))

`Local (nprod a b) c` for pairwise-local fields — Li's normal-product locality.  The bracket
`[:a(z₂)b(z₂):, c(z₃)]` is lifted to a three-variable distribution (separating the two copies
of `z₂` into `z₁, z₂`), killed by the pairwise-locality powers, then collapsed along the
diagonal `z₁ = z₂`.  The normal-ordering splits as `:ab:(m,n) = b(n)a(m) + [0≤m]·[a(m),b(n)]`,
isolating the order-dependence onto the triple commutator `[[a,b],c]` (which `dong_core` kills
with `(z₂-z₃)` powers alone — the `m`-gate is untouched by `z₂₃`), while the ungated `b(n)a(m)`
part splits into clean `[a,c]` and `[b,c]` pieces. -/

/-- Lift `b(z₂)·X(z₁,z₃)`: left-multiply the two-variable `X` (in `z₁,z₃`) by `b(z₂)`. -/
def lmulB (b : FormalDist (End ℂ V)) (X : FormalDist₂ (End ℂ V)) : FormalDist₃ (End ℂ V) :=
  fun m n p => b n * X m p

/-- Lift `Y(z₂,z₃)·a(z₁)`: right-multiply the two-variable `Y` (in `z₂,z₃`) by `a(z₁)`. -/
def rmulA (Y : FormalDist₂ (End ℂ V)) (a : FormalDist (End ℂ V)) : FormalDist₃ (End ℂ V) :=
  fun m n p => Y n p * a m

/-- The `z₁`-causal gate `[0 ≤ m]`: keep only the nonnegative `z₁`-modes (the normal-ordering
gate, depending only on the first variable). -/
def gateM (G : FormalDist₃ (End ℂ V)) : FormalDist₃ (End ℂ V) :=
  fun m n p => if 0 ≤ m then G m n p else 0

@[simp] theorem lmulB_apply (b : FormalDist (End ℂ V)) (X : FormalDist₂ (End ℂ V)) (m n p : ℤ) :
    lmulB b X m n p = b n * X m p := rfl
@[simp] theorem rmulA_apply (Y : FormalDist₂ (End ℂ V)) (a : FormalDist (End ℂ V)) (m n p : ℤ) :
    rmulA Y a m n p = Y n p * a m := rfl
@[simp] theorem gateM_apply (G : FormalDist₃ (End ℂ V)) (m n p : ℤ) :
    gateM G m n p = if 0 ≤ m then G m n p else 0 := rfl

@[simp] theorem lmulB_zero (b : FormalDist (End ℂ V)) :
    lmulB b (0 : FormalDist₂ (End ℂ V)) = 0 := by
  apply FormalDist₃.ext; intro m n p; show b n * (0 : End ℂ V) = 0; simp
@[simp] theorem rmulA_zero (a : FormalDist (End ℂ V)) :
    rmulA (0 : FormalDist₂ (End ℂ V)) a = 0 := by
  apply FormalDist₃.ext; intro m n p; show (0 : End ℂ V) * a m = 0; simp
@[simp] theorem gateM_zero : gateM (0 : FormalDist₃ (End ℂ V)) = 0 := by
  apply FormalDist₃.ext; intro m n p; show (if 0 ≤ m then (0 : End ℂ V) else 0) = 0; simp

/-- `(z₁-z₃)` on `lmulB b X` passes to `X` (the `b(z₂)`-factor is in the inert variable). -/
theorem mulBySub₁₃_lmulB (b : FormalDist (End ℂ V)) (X : FormalDist₂ (End ℂ V)) :
    mulBySub₁₃ (lmulB b X) = lmulB b (mulBySub X) := by
  apply FormalDist₃.ext; intro m n p
  simp only [mulBySub₁₃_apply, lmulB_apply, mulBySub_apply, mul_sub]

/-- `(z₂-z₃)` on `rmulA Y a` passes to `Y` (the `a(z₁)`-factor is in the inert variable). -/
theorem mulBySub₂₃_rmulA (Y : FormalDist₂ (End ℂ V)) (a : FormalDist (End ℂ V)) :
    mulBySub₂₃ (rmulA Y a) = rmulA (mulBySub Y) a := by
  apply FormalDist₃.ext; intro m n p
  simp only [mulBySub₂₃_apply, rmulA_apply, mulBySub_apply, sub_mul]

/-- `(z₂-z₃)` on `gateM G` passes through the `z₁`-gate to `G`. -/
theorem mulBySub₂₃_gateM (G : FormalDist₃ (End ℂ V)) :
    mulBySub₂₃ (gateM G) = gateM (mulBySub₂₃ G) := by
  apply FormalDist₃.ext; intro m n p
  simp only [mulBySub₂₃_apply, gateM_apply]
  split_ifs <;> simp

/-- Iterated `(z₁-z₃)ᵏ` on `lmulB b X` passes to `X`. -/
theorem mulBySub₁₃Pow_lmulB (k : ℕ) (b : FormalDist (End ℂ V)) (X : FormalDist₂ (End ℂ V)) :
    mulBySub₁₃Pow k (lmulB b X) = lmulB b (mulBySubPow k X) := by
  induction k generalizing X with
  | zero => rfl
  | succ j ih => rw [mulBySub₁₃Pow_succ, LinearMap.comp_apply, ih, mulBySub₁₃_lmulB,
      ← LinearMap.comp_apply, ← mulBySubPow_succ]

/-- Iterated `(z₂-z₃)ᵏ` on `rmulA Y a` passes to `Y`. -/
theorem mulBySub₂₃Pow_rmulA (k : ℕ) (Y : FormalDist₂ (End ℂ V)) (a : FormalDist (End ℂ V)) :
    mulBySub₂₃Pow k (rmulA Y a) = rmulA (mulBySubPow k Y) a := by
  induction k generalizing Y with
  | zero => rfl
  | succ j ih => rw [mulBySub₂₃Pow_succ, LinearMap.comp_apply, ih, mulBySub₂₃_rmulA,
      ← LinearMap.comp_apply, ← mulBySubPow_succ]

/-- Iterated `(z₂-z₃)ᵏ` on `gateM G` passes through the gate to `G`. -/
theorem mulBySub₂₃Pow_gateM (k : ℕ) (G : FormalDist₃ (End ℂ V)) :
    mulBySub₂₃Pow k (gateM G) = gateM (mulBySub₂₃Pow k G) := by
  induction k generalizing G with
  | zero => rfl
  | succ j ih => rw [mulBySub₂₃Pow_succ, LinearMap.comp_apply, ih, mulBySub₂₃_gateM,
      ← LinearMap.comp_apply, ← mulBySub₂₃Pow_succ]

/-- The three-variable bracket `[:a(z₁)b(z₂):, c(z₃)]` of the two-variable normal-ordered
product with `c`.  Its diagonal `z₁ = z₂` is `[:a(z)b(z):, c]`. -/
def normalOrderedBracket (a b c : FormalDist (End ℂ V)) : FormalDist₃ (End ℂ V) :=
  fun m n p => normalOrdered a b m n * c p - c p * normalOrdered a b m n

@[simp] theorem normalOrderedBracket_apply (a b c : FormalDist (End ℂ V)) (m n p : ℤ) :
    normalOrderedBracket a b c m n p
      = normalOrdered a b m n * c p - c p * normalOrdered a b m n := rfl

/-- **The normal-ordering split** `:ab:(m,n) = b(n)a(m) + [0≤m]·[a(m),b(n)]`, applied to the
bracket with `c`: the three-variable `[:ab:,c]` decomposes into an ungated `[b·a, c]` (split
into `[a,c]` and `[b,c]` pieces) plus the `z₁`-gated triple commutator `[[a,b],c]`. -/
theorem normalOrderedBracket_decomp (a b c : FormalDist (End ℂ V)) :
    normalOrderedBracket a b c
      = lmulB b (bracketDist a c) + rmulA (bracketDist b c) a
        + gateM (outerC₁₂ (bracketDist a b) c) := by
  apply FormalDist₃.ext; intro m n p
  show normalOrdered a b m n * c p - c p * normalOrdered a b m n
    = b n * bracketDist a c m p + bracketDist b c n p * a m
      + (if 0 ≤ m then outerC₁₂ (bracketDist a b) c m n p else 0)
  simp only [bracketDist_apply, outerC₁₂_apply, normalOrdered_apply]
  split_ifs with h <;> noncomm_ring

/-- **The three-variable locality of the normal-ordered bracket.**  For pairwise-local `a, b, c`
with common order `r`, `(z₁-z₃)ʳ (z₂-z₃)³ʳ [:a(z₁)b(z₂):, c(z₃)] = 0`. -/
theorem mulBySub_normalOrderedBracket_eq_zero (a b c : FormalDist (End ℂ V)) {r : ℕ}
    (hab : mulBySubPow r (bracketDist a b) = 0)
    (hac : mulBySubPow r (bracketDist a c) = 0)
    (hbc : mulBySubPow r (bracketDist b c) = 0) :
    mulBySub₁₃Pow r (mulBySub₂₃Pow (3 * r) (normalOrderedBracket a b c)) = 0 := by
  -- piece 1: lmulB b (bracketDist a c), killed by (z₁-z₃)ʳ (reorder past (z₂-z₃))
  have h1 : mulBySub₁₃Pow r (mulBySub₂₃Pow (3 * r) (lmulB b (bracketDist a c))) = 0 := by
    rw [← reorder₂₃₁₃, mulBySub₁₃Pow_lmulB, hac, lmulB_zero, map_zero]
  -- piece 2: rmulA (bracketDist b c) a, killed by (z₂-z₃)³ʳ ≥ (z₂-z₃)ʳ
  have h2 : mulBySub₁₃Pow r (mulBySub₂₃Pow (3 * r) (rmulA (bracketDist b c) a)) = 0 := by
    rw [mulBySub₂₃Pow_rmulA, mulBySubPow_mono₂ (show r ≤ 3 * r by omega) hbc, rmulA_zero,
      map_zero]
  -- piece 3: gateM [[a,b],c], killed by (z₂-z₃)³ʳ via dong_core (the m-gate is inert)
  have h3 : mulBySub₁₃Pow r (mulBySub₂₃Pow (3 * r) (gateM (outerC₁₂ (bracketDist a b) c))) = 0 := by
    have hdc : mulBySub₂₃Pow (3 * r) (outerC₁₂ (bracketDist a b) c) = 0 := by
      have h := dong_core a b c hab hac hbc 0 (2 * r) le_rfl
      rw [show mulBySub₁₂Pow 0 (outerC₁₂ (bracketDist a b) c)
            = outerC₁₂ (bracketDist a b) c from rfl] at h
      rwa [show (2 * r + r : ℕ) = 3 * r from by ring] at h
    rw [mulBySub₂₃Pow_gateM, hdc, gateM_zero, map_zero]
  rw [normalOrderedBracket_decomp]
  simp only [map_add, h1, h2, h3, add_zero]

/-! ### Collapsing the diagonal `z₁ = z₂` -/

/-- Apply a three-variable operator distribution to a vector, coefficient-wise. -/
def appVec3 (x : V) (G : FormalDist₃ (End ℂ V)) : FormalDist₃ V := fun m n p => G m n p x

/-- Apply a two-variable operator distribution to a vector, coefficient-wise. -/
def appVec2 (x : V) (F : FormalDist₂ (End ℂ V)) : FormalDist₂ V := fun s p => F s p x

@[simp] theorem appVec3_apply (x : V) (G : FormalDist₃ (End ℂ V)) (m n p : ℤ) :
    appVec3 x G m n p = G m n p x := rfl
@[simp] theorem appVec2_apply (x : V) (F : FormalDist₂ (End ℂ V)) (s p : ℤ) :
    appVec2 x F s p = F s p x := rfl

@[simp] theorem appVec3_zero (x : V) : appVec3 x (0 : FormalDist₃ (End ℂ V)) = 0 := by
  apply FormalDist₃.ext; intro m n p; show (0 : End ℂ V) x = (0 : FormalDist₃ V) m n p; simp; rfl

/-- Evaluation on `x` commutes with `(z₂-z₃)`. -/
theorem appVec3_mulBySub₂₃ (x : V) (G : FormalDist₃ (End ℂ V)) :
    appVec3 x (mulBySub₂₃ G) = mulBySub₂₃ (appVec3 x G) := by
  apply FormalDist₃.ext; intro m n p
  simp only [appVec3_apply, mulBySub₂₃_apply, LinearMap.sub_apply]
/-- Evaluation on `x` commutes with `(z₁-z₃)`. -/
theorem appVec3_mulBySub₁₃ (x : V) (G : FormalDist₃ (End ℂ V)) :
    appVec3 x (mulBySub₁₃ G) = mulBySub₁₃ (appVec3 x G) := by
  apply FormalDist₃.ext; intro m n p
  simp only [appVec3_apply, mulBySub₁₃_apply, LinearMap.sub_apply]

theorem appVec3_mulBySub₂₃Pow (k : ℕ) (x : V) (G : FormalDist₃ (End ℂ V)) :
    appVec3 x (mulBySub₂₃Pow k G) = mulBySub₂₃Pow k (appVec3 x G) := by
  induction k generalizing G with
  | zero => rfl
  | succ j ih => rw [mulBySub₂₃Pow_succ, LinearMap.comp_apply, appVec3_mulBySub₂₃, ih,
      ← LinearMap.comp_apply, ← mulBySub₂₃Pow_succ]
theorem appVec3_mulBySub₁₃Pow (k : ℕ) (x : V) (G : FormalDist₃ (End ℂ V)) :
    appVec3 x (mulBySub₁₃Pow k G) = mulBySub₁₃Pow k (appVec3 x G) := by
  induction k generalizing G with
  | zero => rfl
  | succ j ih => rw [mulBySub₁₃Pow_succ, LinearMap.comp_apply, appVec3_mulBySub₁₃, ih,
      ← LinearMap.comp_apply, ← mulBySub₁₃Pow_succ]

theorem appVec2_mulBySub (x : V) (F : FormalDist₂ (End ℂ V)) :
    appVec2 x (mulBySub F) = mulBySub (appVec2 x F) := by
  apply FormalDist₂.ext; intro s p
  simp only [appVec2_apply, mulBySub_apply, LinearMap.sub_apply]
theorem appVec2_mulBySubPow (k : ℕ) (x : V) (F : FormalDist₂ (End ℂ V)) :
    appVec2 x (mulBySubPow k F) = mulBySubPow k (appVec2 x F) := by
  induction k generalizing F with
  | zero => rfl
  | succ j ih => rw [mulBySubPow_succ, LinearMap.comp_apply, appVec2_mulBySub, ih,
      ← LinearMap.comp_apply, ← mulBySubPow_succ]

/-- The diagonal `z₁ = z₂` of a (vector-valued) three-variable distribution:
`(diag3 G)(z, z₃) = ∑_{m+n=z} G(m,n,z₃)` — the `z^s`-coefficient sums the antidiagonal. -/
noncomputable def diag3 (G : FormalDist₃ V) : FormalDist₂ V := fun s p => ∑ᶠ m : ℤ, G m (s - m) p

@[simp] theorem diag3_apply (G : FormalDist₃ V) (s p : ℤ) :
    diag3 G s p = ∑ᶠ m : ℤ, G m (s - m) p := rfl

@[simp] theorem diag3_zero : diag3 (0 : FormalDist₃ V) = 0 := by
  apply FormalDist₂.ext; intro s p
  show (∑ᶠ _ : ℤ, (0 : V)) = (0 : FormalDist₂ V) s p
  rw [finsum_zero]; rfl

/-- A three-variable distribution is **diagonally summable** when each antidiagonal sum is
finite — exactly what makes `diag3` algebraically defined. -/
def DiagSummable (G : FormalDist₃ V) : Prop :=
  ∀ s p : ℤ, (Function.support (fun m : ℤ => G m (s - m) p)).Finite

/-- The `z₁`-shifted antidiagonal of a diagonally-summable distribution still has finite
support (the shift `m ↦ m-1` is a bijection). -/
theorem DiagSummable.shift_finite {G : FormalDist₃ V} (hG : DiagSummable G) (s p : ℤ) :
    (Function.support (fun m : ℤ => G (m - 1) (s - m) p)).Finite := by
  apply Set.Finite.subset ((hG (s - 1) p).image (· + 1))
  intro m hm
  rw [Function.mem_support] at hm
  rw [Set.mem_image]
  refine ⟨m - 1, ?_, by ring⟩
  rw [Function.mem_support, show s - 1 - (m - 1) = s - m from by ring]
  exact hm

theorem DiagSummable.mulBySub₂₃ {G : FormalDist₃ V} (hG : DiagSummable G) :
    DiagSummable (mulBySub₂₃ G) := by
  intro s p
  apply Set.Finite.subset ((hG (s - 1) p).union (hG s (p - 1)))
  intro m hm
  rw [Function.mem_support, mulBySub₂₃_apply] at hm
  rw [Set.mem_union, Function.mem_support, Function.mem_support]
  by_contra hcon
  push_neg at hcon
  refine hm ?_
  rw [show s - m - 1 = s - 1 - m from by ring, hcon.1, hcon.2, sub_zero]

theorem DiagSummable.mulBySub₁₃ {G : FormalDist₃ V} (hG : DiagSummable G) :
    DiagSummable (mulBySub₁₃ G) := by
  intro s p
  apply Set.Finite.subset ((hG.shift_finite s p).union (hG s (p - 1)))
  intro m hm
  rw [Function.mem_support, mulBySub₁₃_apply] at hm
  rw [Set.mem_union, Function.mem_support, Function.mem_support]
  by_contra hcon
  push Not at hcon
  exact hm (by rw [hcon.1, hcon.2, sub_zero])

/-- `DiagSummable` is preserved by iterating `(z₂-z₃)`. -/
theorem DiagSummable.mulBySub₂₃pow (j : ℕ) {G : FormalDist₃ V} (hG : DiagSummable G) :
    DiagSummable (mulBySub₂₃Pow j G) := by
  induction j generalizing G with
  | zero => exact hG
  | succ k ih => rw [mulBySub₂₃Pow_succ, LinearMap.comp_apply]; exact (ih hG).mulBySub₂₃

/-- `DiagSummable` is preserved by iterating `(z₁-z₃)`. -/
theorem DiagSummable.mulBySub₁₃pow (j : ℕ) {G : FormalDist₃ V} (hG : DiagSummable G) :
    DiagSummable (mulBySub₁₃Pow j G) := by
  induction j generalizing G with
  | zero => exact hG
  | succ k ih => rw [mulBySub₁₃Pow_succ, LinearMap.comp_apply]; exact (ih hG).mulBySub₁₃

/-- `diag3` intertwines `(z₂-z₃)` (on the 3-var side) with `(z₁-z₂)` (on the diagonal). -/
theorem diag3_mulBySub₂₃ {G : FormalDist₃ V} (hG : DiagSummable G) :
    diag3 (mulBySub₂₃ G) = mulBySub (diag3 G) := by
  apply FormalDist₂.ext; intro s p
  rw [mulBySub_apply]
  change (∑ᶠ m : ℤ, mulBySub₂₃ G m (s - m) p) = diag3 G (s - 1) p - diag3 G s (p - 1)
  rw [show (∑ᶠ m : ℤ, mulBySub₂₃ G m (s - m) p)
        = ∑ᶠ m : ℤ, (G m (s - 1 - m) p - G m (s - m) (p - 1)) from
      finsum_congr fun m => by rw [mulBySub₂₃_apply, show s - m - 1 = s - 1 - m from by ring]]
  rw [finsum_sub_distrib (hG (s - 1) p) (hG s (p - 1))]
  rfl

/-- `diag3` intertwines `(z₁-z₃)` (on the 3-var side) with `(z₁-z₂)` (on the diagonal). -/
theorem diag3_mulBySub₁₃ {G : FormalDist₃ V} (hG : DiagSummable G) :
    diag3 (mulBySub₁₃ G) = mulBySub (diag3 G) := by
  apply FormalDist₂.ext; intro s p
  rw [mulBySub_apply]
  change (∑ᶠ m : ℤ, mulBySub₁₃ G m (s - m) p) = diag3 G (s - 1) p - diag3 G s (p - 1)
  rw [show (∑ᶠ m : ℤ, mulBySub₁₃ G m (s - m) p)
        = ∑ᶠ m : ℤ, (G (m - 1) (s - m) p - G m (s - m) (p - 1)) from
      finsum_congr fun m => by rw [mulBySub₁₃_apply]]
  rw [finsum_sub_distrib (hG.shift_finite s p) (hG s (p - 1))]
  congr 1
  change (∑ᶠ m : ℤ, G (m - 1) (s - m) p) = ∑ᶠ m : ℤ, G m (s - 1 - m) p
  rw [← finsum_int_succ_shift (fun m : ℤ => G (m - 1) (s - m) p)]
  exact finsum_congr fun m => by rw [show (m + 1) - 1 = m from by ring,
    show s - (m + 1) = s - 1 - m from by ring]

theorem diag3_mulBySub₂₃Pow (k : ℕ) {G : FormalDist₃ V} (hG : DiagSummable G) :
    mulBySubPow k (diag3 G) = diag3 (mulBySub₂₃Pow k G) := by
  induction k generalizing G with
  | zero => rfl
  | succ j ih =>
      rw [mulBySubPow_succ, LinearMap.comp_apply, ih hG, ← diag3_mulBySub₂₃ (hG.mulBySub₂₃pow j),
        ← LinearMap.comp_apply, ← mulBySub₂₃Pow_succ]

theorem diag3_mulBySub₁₃Pow (k : ℕ) {G : FormalDist₃ V} (hG : DiagSummable G) :
    mulBySubPow k (diag3 G) = diag3 (mulBySub₁₃Pow k G) := by
  induction k generalizing G with
  | zero => rfl
  | succ j ih =>
      rw [mulBySubPow_succ, LinearMap.comp_apply, ih hG,
        ← diag3_mulBySub₁₃ (hG.mulBySub₁₃pow j), ← LinearMap.comp_apply, ← mulBySub₁₃Pow_succ]

/-! ### Assembling Dong's lemma for `n < 0` -/

/-- `(z₁-z₂)^{a+b} = (z₁-z₂)ᵃ·(z₁-z₂)ᵇ` on a `FormalDist₂` over any `ℂ`-module. -/
theorem mulBySubPow_add_gen {𝒲 : Type*} [AddCommGroup 𝒲] [Module ℂ 𝒲] (a b : ℕ)
    (f : FormalDist₂ 𝒲) : mulBySubPow (a + b) f = mulBySubPow a (mulBySubPow b f) := by
  induction a with
  | zero => simp
  | succ k ih =>
      rw [Nat.succ_add, mulBySubPow_succ, LinearMap.comp_apply, ih, ← LinearMap.comp_apply,
        ← mulBySubPow_succ]

/-- The bracket `[:a(z)b(z):, c(z₃)]`, evaluated on `x`, is the diagonal `z₁ = z₂` of the
three-variable `[:a(z₁)b(z₂):, c(z₃)]` evaluated on `x`. -/
theorem appVec2_bracketDist_nprod {a b : FormalDist (End ℂ V)} (ha : IsField a) (hb : IsField b)
    (c : FormalDist (End ℂ V)) (x : V) :
    appVec2 x (bracketDist (nprod ha hb) c)
      = diag3 (appVec3 x (normalOrderedBracket a b c)) := by
  apply FormalDist₂.ext; intro s p
  rw [appVec2_apply, bracketDist_apply, LinearMap.sub_apply, Module.End.mul_apply,
    Module.End.mul_apply, nprod_apply, nprod_apply,
    map_finsum (c p) (normalOrdered_diag_support_finite ha hb s x),
    ← finsum_sub_distrib (normalOrdered_diag_support_finite ha hb s (c p x))
      ((normalOrdered_diag_support_finite ha hb s x).subset (fun m hm => by
        rw [Function.mem_support] at hm ⊢; exact fun h => hm (by rw [h, map_zero]))),
    diag3_apply]
  exact finsum_congr fun m => by
    rw [appVec3_apply, normalOrderedBracket_apply, LinearMap.sub_apply, Module.End.mul_apply,
      Module.End.mul_apply]

/-- The diagonal antidiagonals of `[:a(z₁)b(z₂):, c]` evaluated on `x` are finite sums. -/
theorem diagSummable_appVec3_normalOrderedBracket {a b : FormalDist (End ℂ V)}
    (ha : IsField a) (hb : IsField b) (c : FormalDist (End ℂ V)) (x : V) :
    DiagSummable (appVec3 x (normalOrderedBracket a b c)) := by
  intro s p
  apply Set.Finite.subset ((normalOrdered_diag_support_finite ha hb s (c p x)).union
    (normalOrdered_diag_support_finite ha hb s x))
  intro m hm
  rw [Function.mem_support, appVec3_apply, normalOrderedBracket_apply, LinearMap.sub_apply,
    Module.End.mul_apply, Module.End.mul_apply] at hm
  rw [Set.mem_union, Function.mem_support, Function.mem_support]
  by_contra hcon
  push Not at hcon
  exact hm (by rw [hcon.1, hcon.2, map_zero, sub_zero])

/-- **Dong's lemma, `n < 0` case** (Gannon §5.1.2; Kac §3.2; Li): for pairwise mutually-local
fields `a, b, c`, the normal-ordered product `:a(z)b(z): = a₍₋₁₎b` (`nprod`) is mutually local
with `c`.  Lifting to three variables (separating the two copies of `z`), the pairwise-locality
powers `(z₁-z₃)ʳ (z₂-z₃)³ʳ` annihilate `[:a(z₁)b(z₂):, c(z₃)]`
(`mulBySub_normalOrderedBracket_eq_zero`), and collapsing the diagonal `z₁ = z₂` (where both
powers become `(z-z₃)`) gives `(z-z₃)⁴ʳ [:ab:(z), c] = 0`. -/
theorem dong_neg {a b c : FormalDist (End ℂ V)} (ha : IsField a) (hb : IsField b)
    (hab : Local a b) (hac : Local a c) (hbc : Local b c) :
    Local (nprod ha hb) c := by
  obtain ⟨Nab, hNab⟩ := hab
  obtain ⟨Nac, hNac⟩ := hac
  obtain ⟨Nbc, hNbc⟩ := hbc
  set r := max Nab (max Nac Nbc) with hr
  have hab' : mulBySubPow r (bracketDist a b) = 0 := mulBySubPow_mono₂ (le_max_left _ _) hNab
  have hac' : mulBySubPow r (bracketDist a c) = 0 :=
    mulBySubPow_mono₂ (le_trans (le_max_left _ _) (le_max_right _ _)) hNac
  have hbc' : mulBySubPow r (bracketDist b c) = 0 :=
    mulBySubPow_mono₂ (le_trans (le_max_right _ _) (le_max_right _ _)) hNbc
  refine ⟨r + 3 * r, ?_⟩
  apply FormalDist₂.ext; intro s p
  apply LinearMap.ext; intro x
  have hDS : DiagSummable (appVec3 x (normalOrderedBracket a b c)) :=
    diagSummable_appVec3_normalOrderedBracket ha hb c x
  have key : appVec2 x (mulBySubPow (r + 3 * r) (bracketDist (nprod ha hb) c)) = 0 := by
    rw [appVec2_mulBySubPow, appVec2_bracketDist_nprod, mulBySubPow_add_gen,
      diag3_mulBySub₂₃Pow (3 * r) hDS, diag3_mulBySub₁₃Pow r (hDS.mulBySub₂₃pow (3 * r)),
      ← appVec3_mulBySub₂₃Pow, ← appVec3_mulBySub₁₃Pow,
      mulBySub_normalOrderedBracket_eq_zero a b c hab' hac' hbc', appVec3_zero, diag3_zero]
  have h := congrFun (congrFun key s) p
  rw [appVec2_apply] at h
  exact h

/-! ## The normal-ordered product on the vacuum (generic; module-polymorphic)

The vacuum action of `:g(z)h(z):` for two **fields** that each create a power series on a vector
`vac` (`g q vac = 0` for `q < 0`, same for `h`).  These are the basis-free / `PreVertexAlgebra`-free
companions of the VOA-specific `Core.Reconstruction.nprod_vacuum_{neg,base}` — the engine the
existence reconstruction (affine `WakModule`, Virasoro `L(c,0)`) uses to compute the creation tower
of its iterated word fields. -/

/-- `:g(z)h(z):` annihilates `vac` below degree `0`, for fields creating power series on `vac`. -/
theorem nprod_vacuum_neg_gen {g h : FormalDist (End ℂ V)} (hg : IsField g) (hh : IsField h)
    (vac : V) (hgvac : ∀ q : ℤ, q < 0 → g q vac = 0) (hhvac : ∀ q : ℤ, q < 0 → h q vac = 0)
    {s : ℤ} (hs : s < 0) : nprod hg hh s vac = 0 := by
  rw [nprod_apply]
  refine finsum_eq_zero_of_forall_eq_zero fun m => ?_
  rw [normalOrdered_apply]
  by_cases hm : 0 ≤ m
  · rw [if_pos hm, Module.End.mul_apply, hhvac (s - m) (by omega), map_zero]
  · rw [if_neg hm, Module.End.mul_apply, hgvac m (by omega), map_zero]

/-- The base vacuum value `:g(z)h(z):₀ vac = g₀ (h₀ vac)`. -/
theorem nprod_vacuum_base_gen {g h : FormalDist (End ℂ V)} (hg : IsField g) (hh : IsField h)
    (vac : V) (hgvac : ∀ q : ℤ, q < 0 → g q vac = 0) (hhvac : ∀ q : ℤ, q < 0 → h q vac = 0) :
    nprod hg hh 0 vac = g 0 (h 0 vac) := by
  rw [nprod_apply, finsum_eq_single _ 0]
  · rw [normalOrdered_apply, if_pos le_rfl, Module.End.mul_apply, show (0 : ℤ) - 0 = 0 from by ring]
  · intro m hm
    rw [normalOrdered_apply]
    by_cases h0 : 0 ≤ m
    · rw [if_pos h0, Module.End.mul_apply, hhvac (0 - m) (by omega), map_zero]
    · rw [if_neg h0, Module.End.mul_apply, hgvac m (by omega), map_zero]

end VOA
