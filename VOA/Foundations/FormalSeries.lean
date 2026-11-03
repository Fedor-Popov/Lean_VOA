/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Group.Support
import Mathlib.Data.Complex.Basic

/-!
# Formal distributions `𝒲⟦z^±⟧`  (Gannon §5.1.2, pp. 312–316)

The basic object underlying a vertex algebra is **not** a power series ring. For a
vector space `𝒲`, Gannon writes `𝒲⟦z^±⟧` for the space of all *doubly-infinite*
formal series
`∑_{n ∈ ℤ} wₙ zⁿ`  with `wₙ ∈ 𝒲`, with no convergence asked of the coefficients —
`z` is a formal place-keeper. These are the **formal distributions**. The Laurent
polynomials `𝒲[z^±] = ∑_{n=-M}^{N} wₙ zⁿ` are the "test functions".

The key subtlety (Gannon p. 313, items (i)–(iii); Paradoxes 5.1 and 5.2):

* `𝒲⟦z^±⟧` is **not** a ring — there is no associative product in general (you cannot
  multiply two two-sided series, e.g. `δ(z)²` is undefined: Paradox 5.1). Accordingly we
  give `FormalDist` only `AddCommGroup`/`Module` instances, *never* a global `Mul`. This
  is the reason `FormalDist` is a `def` (an opaque type synonym) and not a `reducible`
  abbreviation: it stops the pointwise `Mul`/`Ring` of `ℤ → 𝒲` from leaking in.
* It **is** a module over the Laurent polynomials `ℂ[z^±]`, and a `ℂ`-vector space.
* Multiplication exists only for *algebraically summable* families (p. 315): a sum
  `∑ᵢ w⁽ⁱ⁾(z)` is *algebraically defined* iff, for each fixed `n`, the coefficient is a
  finite sum. All other sums/products are forbidden.

This file sets up `𝒲⟦z^±⟧`, its module structure, the subspace of Laurent
polynomials, multiplication by a monomial, the notions of algebraically summable family
and algebraically defined sum, and the two-variable distributions `𝒲⟦z₁^±,z₂^±⟧`
together with multiplication by `(z₁ - z₂)ᴺ` (the operator behind locality).

## Dependencies
Mathlib only (modules, big operators, finsupp).

## Status
Complete & `sorry`-free. This is the analytic foundation; the
"algebraically summable" bookkeeping (`AlgSummable`/`algSum`) is the crux that lets the
doubly-infinite products `Y(u,z)v` make sense (cf. `FormalCalculus`, `Locality`).

## References
* Gannon, *Moonshine beyond the Monster*, §5.1.2.
* Frenkel–Lepowsky–Meurman, *Vertex Operator Algebras and the Monster*, Ch. 2.
* Lepowsky–Li, *Introduction to Vertex Operator Algebras and Their Representations*,
  Ch. 2 (formal calculus).
-/

namespace VOA

universe u

variable {𝒲 : Type u}

/-! ## The space of formal distributions -/

/-- A formal distribution with coefficients in `𝒲`: a bi-infinite family `ℤ → 𝒲`,
thought of as `∑_{n ∈ ℤ} (f n) zⁿ` (so `f n` is the coefficient of `zⁿ`).
Gannon §5.1.2, the space `𝒲⟦z^±⟧`. It is **not** a ring (Paradox 5.1), so it is kept as
an opaque `def` carrying only additive/module structure. -/
def FormalDist (𝒲 : Type*) : Type _ := ℤ → 𝒲

@[inherit_doc] notation:max 𝒲 "⟦z^±⟧" => FormalDist 𝒲

namespace FormalDist

/-- Pointwise addition makes `𝒲⟦z^±⟧` an additive group (Gannon §5.1.2). -/
instance instAddCommGroup [AddCommGroup 𝒲] : AddCommGroup (FormalDist 𝒲) :=
  inferInstanceAs (AddCommGroup (ℤ → 𝒲))

/-- Pointwise scaling makes `𝒲⟦z^±⟧` a module — but note there is deliberately **no**
ring structure (Gannon Paradox 5.1). -/
instance instModule {R : Type*} [Semiring R] [AddCommGroup 𝒲] [Module R 𝒲] :
    Module R (FormalDist 𝒲) := inferInstanceAs (Module R (ℤ → 𝒲))

/-- Two formal distributions are equal when all their coefficients agree. -/
@[ext]
theorem ext {f g : FormalDist 𝒲} (h : ∀ n, f n = g n) : f = g := funext h

end FormalDist

/-! ## Two-variable distributions `𝒲⟦z₁^±,z₂^±⟧` (Gannon p. 314) -/

/-- A two-variable formal distribution: `f m n` is the coefficient of `z₁ᵐ z₂ⁿ`
(Gannon p. 314). Used to express locality. -/
def FormalDist₂ (𝒲 : Type*) : Type _ := ℤ → ℤ → 𝒲

@[inherit_doc] notation:max 𝒲 "⟦z₁^±,z₂^±⟧" => FormalDist₂ 𝒲

namespace FormalDist₂

/-- Pointwise addition makes `𝒲⟦z₁^±,z₂^±⟧` an additive group. -/
instance instAddCommGroup [AddCommGroup 𝒲] : AddCommGroup (FormalDist₂ 𝒲) :=
  inferInstanceAs (AddCommGroup (ℤ → ℤ → 𝒲))

/-- Pointwise scaling makes `𝒲⟦z₁^±,z₂^±⟧` a module (again with no global ring). -/
instance instModule {R : Type*} [Semiring R] [AddCommGroup 𝒲] [Module R 𝒲] :
    Module R (FormalDist₂ 𝒲) := inferInstanceAs (Module R (ℤ → ℤ → 𝒲))

/-- Two two-variable distributions are equal when all coefficients agree. -/
@[ext]
theorem ext {f g : FormalDist₂ 𝒲} (h : ∀ m n, f m n = g m n) : f = g :=
  funext fun m => funext (h m)

end FormalDist₂

/-! ## Laurent polynomials (the test functions) -/

/-- The Laurent-polynomial "test functions" `𝒲[z^±] ⊆ 𝒲⟦z^±⟧`: the formal
distributions with only finitely many nonzero coefficients (Gannon §5.1.2). -/
def LaurentPoly (𝒲 : Type*) [AddCommGroup 𝒲] [Module ℂ 𝒲] : Submodule ℂ (FormalDist 𝒲) where
  carrier := {f | (Function.support f).Finite}
  add_mem' {f g} hf hg := by
    refine (hf.union hg).subset ?_
    intro n hn
    rw [Function.mem_support] at hn
    rw [Set.mem_union, Function.mem_support, Function.mem_support]
    by_contra hcon
    simp only [not_or, not_ne_iff] at hcon
    exact hn (by rw [show (f + g) n = f n + g n from rfl, hcon.1, hcon.2, add_zero])
  zero_mem' := by
    refine Set.finite_empty.subset ?_
    intro n hn
    rw [Function.mem_support] at hn
    exact absurd rfl hn
  smul_mem' c f hf := by
    refine hf.subset ?_
    intro n hn
    rw [Function.mem_support] at hn ⊢
    intro h
    exact hn (by rw [show (c • f) n = c • f n from rfl, h, smul_zero])

/-- Membership in `LaurentPoly` unfolds to having finite support. -/
theorem mem_laurentPoly [AddCommGroup 𝒲] [Module ℂ 𝒲] {f : FormalDist 𝒲} :
    f ∈ LaurentPoly 𝒲 ↔ (Function.support f).Finite := Iff.rfl

/-! ## Algebraically summable families and the algebraic sum (Gannon p. 315) -/

section AlgebraicSum

variable [AddCommGroup 𝒲]

/-- A family `f : ι → 𝒲⟦z^±⟧` of formal distributions is **algebraically summable** when,
for every fixed power `n`, only finitely many members contribute to the `zⁿ`-coefficient.
This is the discipline (Gannon p. 315) that makes infinite sums of distributions
meaningful: a sum is *algebraically defined* iff each coefficient is a finite sum. -/
def AlgSummable {ι : Type*} (f : ι → FormalDist 𝒲) : Prop := ∀ n, {i | f i n ≠ 0}.Finite

/-- The **algebraically-defined sum** of an algebraically summable family: take each
coefficient to be the (finite) sum `∑ᶠ i, f i n` (Gannon p. 315). -/
noncomputable def algSum {ι : Type*} (f : ι → FormalDist 𝒲) (_h : AlgSummable f) :
    FormalDist 𝒲 := fun n => ∑ᶠ i, f i n

@[simp]
theorem algSum_apply {ι : Type*} (f : ι → FormalDist 𝒲) (h : AlgSummable f) (n : ℤ) :
    algSum f h n = ∑ᶠ i, f i n := rfl

/-- Every family indexed by a finite type is algebraically summable. -/
theorem algSummable_of_finite {ι : Type*} [Finite ι] (f : ι → FormalDist 𝒲) :
    AlgSummable f := fun _ => Set.toFinite _

/-- On a finite index type the algebraic sum is just the ordinary `Finset.sum`. -/
theorem algSum_apply_fintype {ι : Type*} [Fintype ι] (f : ι → FormalDist 𝒲)
    (h : AlgSummable f) (n : ℤ) : algSum f h n = ∑ i, f i n := by
  rw [algSum_apply, finsum_eq_sum_of_fintype]

/-- The sum of two algebraically summable families is algebraically summable. -/
theorem AlgSummable.add {ι : Type*} {f g : ι → FormalDist 𝒲}
    (hf : AlgSummable f) (hg : AlgSummable g) : AlgSummable (fun i => f i + g i) := by
  intro n
  refine ((hf n).union (hg n)).subset ?_
  intro i hi
  simp only [Set.mem_union, Set.mem_setOf_eq] at hi ⊢
  by_contra hcon
  simp only [not_or, not_ne_iff] at hcon
  exact hi (by rw [show (f i + g i) n = f i n + g i n from rfl, hcon.1, hcon.2, add_zero])

/-- The algebraic sum is additive: `algSum (f + g) = algSum f + algSum g`. -/
theorem algSum_add {ι : Type*} {f g : ι → FormalDist 𝒲}
    (hf : AlgSummable f) (hg : AlgSummable g) :
    algSum (fun i => f i + g i) (hf.add hg) = algSum f hf + algSum g hg := by
  funext n
  simp only [algSum_apply]
  exact finsum_add_distrib (hf n) (hg n)

end AlgebraicSum

/-! ## Multiplication by a monomial, scalar smul, and the locality operator -/

section ComplexModule

variable [AddCommGroup 𝒲] [Module ℂ 𝒲]

/-- Multiplication by the monomial `zᵏ`: it shifts coefficients, `(zᵏ · f) n = f (n-k)`.
A `ℂ`-linear endomorphism of `𝒲⟦z^±⟧`. -/
def mulByMonomial (k : ℤ) : FormalDist 𝒲 →ₗ[ℂ] FormalDist 𝒲 where
  toFun f := fun n => f (n - k)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem mulByMonomial_apply (k : ℤ) (f : FormalDist 𝒲) (n : ℤ) :
    mulByMonomial k f n = f (n - k) := rfl

/-- A scalar multiple of an algebraically summable family is algebraically summable. -/
theorem AlgSummable.smul {ι : Type*} (c : ℂ) {f : ι → FormalDist 𝒲} (hf : AlgSummable f) :
    AlgSummable (fun i => c • f i) := by
  intro n
  refine (hf n).subset ?_
  intro i hi
  simp only [Set.mem_setOf_eq] at hi ⊢
  intro h
  exact hi (by rw [show (c • f i) n = c • f i n from rfl, h, smul_zero])

/-- The algebraic sum is `ℂ`-homogeneous: `algSum (c • f) = c • algSum f`. -/
theorem algSum_smul {ι : Type*} (c : ℂ) {f : ι → FormalDist 𝒲} (hf : AlgSummable f) :
    algSum (fun i => c • f i) (hf.smul c) = c • algSum f hf := by
  funext n
  simp only [algSum_apply]
  exact (smul_finsum' c (hf n)).symm

/-- Multiplication by `z₁` on two-variable distributions: `(z₁ · f) m n = f (m-1) n`. -/
def shiftZ₁ : FormalDist₂ 𝒲 →ₗ[ℂ] FormalDist₂ 𝒲 where
  toFun f := fun m n => f (m - 1) n
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Multiplication by `z₂` on two-variable distributions: `(z₂ · f) m n = f m (n-1)`. -/
def shiftZ₂ : FormalDist₂ 𝒲 →ₗ[ℂ] FormalDist₂ 𝒲 where
  toFun f := fun m n => f m (n - 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem shiftZ₁_apply (f : FormalDist₂ 𝒲) (m n : ℤ) : shiftZ₁ f m n = f (m - 1) n := rfl

@[simp]
theorem shiftZ₂_apply (f : FormalDist₂ 𝒲) (m n : ℤ) : shiftZ₂ f m n = f m (n - 1) := rfl

/-- Multiplication by `(z₁ - z₂)` on two-variable distributions: it sends `f` to the
distribution with `((z₁ - z₂) · f) m n = f (m-1) n - f m (n-1)` (Gannon p. 314). -/
def mulBySub : FormalDist₂ 𝒲 →ₗ[ℂ] FormalDist₂ 𝒲 := shiftZ₁ - shiftZ₂

@[simp]
theorem mulBySub_apply (f : FormalDist₂ 𝒲) (m n : ℤ) :
    mulBySub f m n = f (m - 1) n - f m (n - 1) := rfl

/-- Multiplication by `(z₁ - z₂)ᴺ` on two-variable distributions, the operator at the
heart of locality / Proposition 5.1.2 (Gannon p. 314). Defined by iterating `mulBySub`. -/
def mulBySubPow : ℕ → (FormalDist₂ 𝒲 →ₗ[ℂ] FormalDist₂ 𝒲)
  | 0 => LinearMap.id
  | (N + 1) => mulBySub.comp (mulBySubPow N)

@[simp]
theorem mulBySubPow_zero :
    (mulBySubPow 0 : FormalDist₂ 𝒲 →ₗ[ℂ] FormalDist₂ 𝒲) = LinearMap.id := rfl

theorem mulBySubPow_succ (N : ℕ) :
    (mulBySubPow (N + 1) : FormalDist₂ 𝒲 →ₗ[ℂ] FormalDist₂ 𝒲)
      = mulBySub.comp (mulBySubPow N) := rfl

/-- `(z₁ - z₂)¹ = (z₁ - z₂)`. -/
theorem mulBySubPow_one :
    (mulBySubPow 1 : FormalDist₂ 𝒲 →ₗ[ℂ] FormalDist₂ 𝒲) = mulBySub :=
  LinearMap.comp_id mulBySub

end ComplexModule

end VOA
