/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Foundations.Locality
import Mathlib.Tactic.Abel
import Mathlib.Data.Nat.Choose.Sum

/-!
# Three-variable formal distributions  (Gannon §5.1.2; Kac §3.2; FLM §8)

The three-variable companion to `FormalDist₂`, built as the minimal substrate for **Dong's
lemma** (`Core.Dong`): the `n`-th product of two mutually-local fields is local with any
third local field.  Dong's lemma is a genuinely three-variable statement — its proof tracks
the three pairwise locality powers `(z₁-z₂)`, `(z₁-z₃)`, `(z₂-z₃)` simultaneously, moving
them around with the polynomial identity `(z₂-z₃) = (z₂-z₁) + (z₁-z₃)`.

* `FormalDist₃ 𝒲 := ℤ → ℤ → ℤ → 𝒲`, with the `AddCommGroup`/`Module ℂ` structure.
* the three coordinate shifts `shift₁/₂/₃` (multiplication by `z₁/z₂/z₃`) and the three
  pairwise difference operators `mulBySub₁₂/₁₃/₂₃` (multiplication by `zᵢ-zⱼ`), with their
  iterated powers.
* the key linear identity `mulBySub₂₃ = mulBySub₂₁ + mulBySub₁₃` and the resulting binomial
  expansion of `mulBySub₂₃Pow`.

## Dependencies
* `VOA.Foundations.Locality` (and transitively `FormalSeries`/`FormalCalculus`).

## Status
Complete & `sorry`-free / axiom-free (the substrate of Dong's lemma).  The three-variable
distributions `FormalDist₃`, the coordinate shifts and pairwise difference operators
`mulBySub₁₂/₁₃/₂₃` with their iterated powers, the linear identity
`mulBySub₂₃ = mulBySub₂₁ + mulBySub₁₃`, and the binomial expansion `mulBySub₂₃Pow_eq_sum` — every
listed target — are proved (`#print axioms = [propext, Classical.choice, Quot.sound]`).  Consumed
by `Core.Dong`.

## References
* Gannon §5.1.2; Kac, *VA for Beginners*, §3.2 (Dong's lemma); Lepowsky–Li §3.2; FLM §8.
-/

namespace VOA

open scoped BigOperators

universe u

variable {𝒲 : Type u}

/-! ## The space of three-variable distributions -/

/-- A three-variable formal distribution: `f m n p` is the coefficient of `z₁ᵐ z₂ⁿ z₃ᵖ`. -/
def FormalDist₃ (𝒲 : Type*) : Type _ := ℤ → ℤ → ℤ → 𝒲

namespace FormalDist₃

instance instAddCommGroup [AddCommGroup 𝒲] : AddCommGroup (FormalDist₃ 𝒲) :=
  inferInstanceAs (AddCommGroup (ℤ → ℤ → ℤ → 𝒲))

instance instModule {R : Type*} [Semiring R] [AddCommGroup 𝒲] [Module R 𝒲] :
    Module R (FormalDist₃ 𝒲) := inferInstanceAs (Module R (ℤ → ℤ → ℤ → 𝒲))

@[ext]
theorem ext {f g : FormalDist₃ 𝒲} (h : ∀ m n p, f m n p = g m n p) : f = g :=
  funext fun m => funext fun n => funext (h m n)

end FormalDist₃

/-! ## Coordinate shifts (multiplication by `z₁`, `z₂`, `z₃`) -/

section ComplexModule

variable [AddCommGroup 𝒲] [Module ℂ 𝒲]

/-- Multiplication by `z₁`: `(z₁·f) m n p = f (m-1) n p`. -/
def shift₁ : FormalDist₃ 𝒲 →ₗ[ℂ] FormalDist₃ 𝒲 where
  toFun f := fun m n p => f (m - 1) n p
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Multiplication by `z₂`: `(z₂·f) m n p = f m (n-1) p`. -/
def shift₂ : FormalDist₃ 𝒲 →ₗ[ℂ] FormalDist₃ 𝒲 where
  toFun f := fun m n p => f m (n - 1) p
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Multiplication by `z₃`: `(z₃·f) m n p = f m n (p-1)`. -/
def shift₃ : FormalDist₃ 𝒲 →ₗ[ℂ] FormalDist₃ 𝒲 where
  toFun f := fun m n p => f m n (p - 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem shift₁_apply (f : FormalDist₃ 𝒲) (m n p : ℤ) : shift₁ f m n p = f (m - 1) n p :=
  rfl
@[simp] theorem shift₂_apply (f : FormalDist₃ 𝒲) (m n p : ℤ) : shift₂ f m n p = f m (n - 1) p :=
  rfl
@[simp] theorem shift₃_apply (f : FormalDist₃ 𝒲) (m n p : ℤ) : shift₃ f m n p = f m n (p - 1) :=
  rfl

/-! ## The three pairwise difference operators (multiplication by `zᵢ - zⱼ`) -/

/-- Multiplication by `(z₁ - z₂)`. -/
def mulBySub₁₂ : FormalDist₃ 𝒲 →ₗ[ℂ] FormalDist₃ 𝒲 := shift₁ - shift₂
/-- Multiplication by `(z₁ - z₃)`. -/
def mulBySub₁₃ : FormalDist₃ 𝒲 →ₗ[ℂ] FormalDist₃ 𝒲 := shift₁ - shift₃
/-- Multiplication by `(z₂ - z₃)`. -/
def mulBySub₂₃ : FormalDist₃ 𝒲 →ₗ[ℂ] FormalDist₃ 𝒲 := shift₂ - shift₃
/-- Multiplication by `(z₂ - z₁) = -(z₁ - z₂)`. -/
def mulBySub₂₁ : FormalDist₃ 𝒲 →ₗ[ℂ] FormalDist₃ 𝒲 := shift₂ - shift₁

@[simp] theorem mulBySub₁₂_apply (f : FormalDist₃ 𝒲) (m n p : ℤ) :
    mulBySub₁₂ f m n p = f (m - 1) n p - f m (n - 1) p := rfl
@[simp] theorem mulBySub₁₃_apply (f : FormalDist₃ 𝒲) (m n p : ℤ) :
    mulBySub₁₃ f m n p = f (m - 1) n p - f m n (p - 1) := rfl
@[simp] theorem mulBySub₂₃_apply (f : FormalDist₃ 𝒲) (m n p : ℤ) :
    mulBySub₂₃ f m n p = f m (n - 1) p - f m n (p - 1) := rfl
@[simp] theorem mulBySub₂₁_apply (f : FormalDist₃ 𝒲) (m n p : ℤ) :
    mulBySub₂₁ f m n p = f m (n - 1) p - f (m - 1) n p := rfl

/-- The defining decomposition `(z₂ - z₃) = (z₂ - z₁) + (z₁ - z₃)`. -/
theorem mulBySub₂₃_eq : (mulBySub₂₃ : FormalDist₃ 𝒲 →ₗ[ℂ] _) = mulBySub₂₁ + mulBySub₁₃ := by
  ext f m n p
  show mulBySub₂₃ f m n p = mulBySub₂₁ f m n p + mulBySub₁₃ f m n p
  simp only [mulBySub₂₃_apply, mulBySub₂₁_apply, mulBySub₁₃_apply]
  abel

/-- `(z₂ - z₁) = -(z₁ - z₂)`. -/
theorem mulBySub₂₁_eq_neg : (mulBySub₂₁ : FormalDist₃ 𝒲 →ₗ[ℂ] _) = -mulBySub₁₂ := by
  ext f m n p
  show mulBySub₂₁ f m n p = -(mulBySub₁₂ f m n p)
  simp only [mulBySub₂₁_apply, mulBySub₁₂_apply]
  abel

/-! ## Iterated powers -/

/-- `(z₁ - z₂)ᴺ`. -/
def mulBySub₁₂Pow : ℕ → (FormalDist₃ 𝒲 →ₗ[ℂ] FormalDist₃ 𝒲)
  | 0 => LinearMap.id
  | (N + 1) => mulBySub₁₂.comp (mulBySub₁₂Pow N)

/-- `(z₁ - z₃)ᴺ`. -/
def mulBySub₁₃Pow : ℕ → (FormalDist₃ 𝒲 →ₗ[ℂ] FormalDist₃ 𝒲)
  | 0 => LinearMap.id
  | (N + 1) => mulBySub₁₃.comp (mulBySub₁₃Pow N)

/-- `(z₂ - z₃)ᴺ`. -/
def mulBySub₂₃Pow : ℕ → (FormalDist₃ 𝒲 →ₗ[ℂ] FormalDist₃ 𝒲)
  | 0 => LinearMap.id
  | (N + 1) => mulBySub₂₃.comp (mulBySub₂₃Pow N)

/-- `(z₂ - z₁)ᴺ`. -/
def mulBySub₂₁Pow : ℕ → (FormalDist₃ 𝒲 →ₗ[ℂ] FormalDist₃ 𝒲)
  | 0 => LinearMap.id
  | (N + 1) => mulBySub₂₁.comp (mulBySub₂₁Pow N)

@[simp] theorem mulBySub₁₂Pow_zero :
    (mulBySub₁₂Pow 0 : FormalDist₃ 𝒲 →ₗ[ℂ] FormalDist₃ 𝒲) = LinearMap.id := rfl
@[simp] theorem mulBySub₁₃Pow_zero :
    (mulBySub₁₃Pow 0 : FormalDist₃ 𝒲 →ₗ[ℂ] FormalDist₃ 𝒲) = LinearMap.id := rfl
@[simp] theorem mulBySub₂₃Pow_zero :
    (mulBySub₂₃Pow 0 : FormalDist₃ 𝒲 →ₗ[ℂ] FormalDist₃ 𝒲) = LinearMap.id := rfl
@[simp] theorem mulBySub₂₁Pow_zero :
    (mulBySub₂₁Pow 0 : FormalDist₃ 𝒲 →ₗ[ℂ] FormalDist₃ 𝒲) = LinearMap.id := rfl

theorem mulBySub₁₂Pow_succ (N : ℕ) :
    (mulBySub₁₂Pow (N + 1) : FormalDist₃ 𝒲 →ₗ[ℂ] _) = mulBySub₁₂.comp (mulBySub₁₂Pow N) := rfl
theorem mulBySub₁₃Pow_succ (N : ℕ) :
    (mulBySub₁₃Pow (N + 1) : FormalDist₃ 𝒲 →ₗ[ℂ] _) = mulBySub₁₃.comp (mulBySub₁₃Pow N) := rfl
theorem mulBySub₂₃Pow_succ (N : ℕ) :
    (mulBySub₂₃Pow (N + 1) : FormalDist₃ 𝒲 →ₗ[ℂ] _) = mulBySub₂₃.comp (mulBySub₂₃Pow N) := rfl

/-! ## Commutativity and the binomial expansion of `(z₂-z₃)ᴺ`

All three coordinate shifts commute, hence so do all the difference operators.  In the
endomorphism ring this lets us expand `(z₂-z₃)ᴺ = ((z₂-z₁)+(z₁-z₃))ᴺ` binomially — the key
move in Dong's lemma. -/

theorem mulBySub₂₁_comm_mulBySub₁₃ :
    Commute (mulBySub₂₁ : FormalDist₃ 𝒲 →ₗ[ℂ] _) mulBySub₁₃ := by
  show mulBySub₂₁ * mulBySub₁₃ = mulBySub₁₃ * mulBySub₂₁
  ext f m n p
  show mulBySub₂₁ (mulBySub₁₃ f) m n p = mulBySub₁₃ (mulBySub₂₁ f) m n p
  simp only [mulBySub₂₁_apply, mulBySub₁₃_apply]
  abel

/-- `mulBySub₂₃Pow N = mulBySub₂₃ ^ N` (relating the iterated-comp definition to the
monoid power). -/
theorem mulBySub₂₃Pow_eq_npow (N : ℕ) :
    (mulBySub₂₃Pow N : FormalDist₃ 𝒲 →ₗ[ℂ] _) = mulBySub₂₃ ^ N := by
  induction N with
  | zero => rfl
  | succ k ih => rw [mulBySub₂₃Pow_succ, ih, pow_succ']; rfl

/-- `mulBySub₂₁Pow N = mulBySub₂₁ ^ N`. -/
theorem mulBySub₂₁Pow_eq_npow (N : ℕ) :
    (mulBySub₂₁Pow N : FormalDist₃ 𝒲 →ₗ[ℂ] _) = mulBySub₂₁ ^ N := by
  induction N with
  | zero => rfl
  | succ k ih => rw [mulBySub₂₁Pow, ih, pow_succ']; rfl

/-- `mulBySub₁₃Pow N = mulBySub₁₃ ^ N`. -/
theorem mulBySub₁₃Pow_eq_npow (N : ℕ) :
    (mulBySub₁₃Pow N : FormalDist₃ 𝒲 →ₗ[ℂ] _) = mulBySub₁₃ ^ N := by
  induction N with
  | zero => rfl
  | succ k ih => rw [mulBySub₁₃Pow_succ, ih, pow_succ']; rfl

/-- **The binomial expansion** `(z₂-z₃)ᴺ = ∑_{i} \binom{N}{i} (z₂-z₁)ⁱ (z₁-z₃)^{N-i}`,
applied to a distribution (Gannon §5.1.2; the engine of Dong's lemma). -/
theorem mulBySub₂₃Pow_eq_sum (N : ℕ) (f : FormalDist₃ 𝒲) :
    mulBySub₂₃Pow N f
      = ∑ i ∈ Finset.range (N + 1),
          (N.choose i) • mulBySub₂₁Pow i (mulBySub₁₃Pow (N - i) f) := by
  have hbin := Commute.add_pow (mulBySub₂₁_comm_mulBySub₁₃ (𝒲 := 𝒲)) N
  rw [mulBySub₂₃Pow_eq_npow, mulBySub₂₃_eq, hbin, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Module.End.mul_apply, Module.End.mul_apply, Module.End.natCast_apply, map_nsmul, map_nsmul,
    ← mulBySub₂₁Pow_eq_npow, ← mulBySub₁₃Pow_eq_npow]

end ComplexModule

end VOA
