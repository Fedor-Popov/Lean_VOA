/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.SemisimpleTrace

/-!
# Symmetric functionals are exactly the dual of the commutator quotient

Dong–Li–Mason's **Lemma 10.7** — the linear-algebra step at the end of Zhu's genus-one dimension
count — is usually stated for a finite-dimensional **semisimple** algebra: a symmetric functional
`φ(ab) = φ(ba)` on `A` is a combination of the traces of the finitely many simple modules, because
Artin–Wedderburn turns `A` into `⊕ᵢ Mat_{nᵢ}(K)` and `[A,A] = ⊕ᵢ 𝔰𝔩_{nᵢ}` has codimension exactly
the number of simple factors.

Miyamoto's theorem (*Modular invariance of vertex operator algebras satisfying `C₂`-cofiniteness*,
Duke Math. J. **122** (2004) 51–91) drops rationality, hence drops semisimplicity of `A(𝒱)`, and
replaces "traces of simple modules" by **pseudo-traces**.  This file isolates the part of DLM
Lemma 10.7 that survives that removal, namely *all of the linear algebra*: the identification

  `{symmetric functionals on A}  ≃  (A/[A,A])*`

holds for a **completely general** `K`-algebra `A` — no finite-dimensionality, no semisimplicity,
no algebraically closed `K`.  Semisimplicity is only ever used to *compute* the right-hand side.

`VOA/Modularity/SemisimpleTrace.lean` already defines `commSpan`, `symmetricFunctionals`
and the injection `symmetricLift`, and already factors the semisimplicity out of them; this file
imports all of that verbatim and supplies the missing half.

## Main results

* `mem_symmetricFunctionals_comp_mkQ` — pulling a functional back along `A ↠ A/[A,A]` lands in the
  symmetric functionals;
* `symmetricOfDualQuot` — that pullback, as a linear map, the inverse-to-be of `symmetricLift`;
* `symmetricLift_surjective`, `symmetricLift_bijective` — `symmetricLift` is onto;
* `symmetricFunctionalsEquivDualQuot` — **the central theorem**:
  `symmetricFunctionals K A ≃ₗ[K] Module.Dual K (A ⧸ commSpan K A)` for an arbitrary `K`-algebra
  `A`;
* `finrank_symmetricFunctionals_eq_finrank_quot_commSpan` —
  `finrank K (symmetricFunctionals K A) = finrank K (A ⧸ commSpan K A)`, **with no hypotheses at
  all** (`Subspace.dual_finrank_eq` is itself unconditional);
* `finiteDimensional_symmetricFunctionals` — **the main result**: for `[FiniteDimensional K A]`
  the symmetric functionals form a finite-dimensional space, *without any semisimplicity
  assumption*.  This is the finiteness Miyamoto's argument consumes.  It is deduced from the
  sharper `finiteDimensional_symmetricFunctionals_of_quot`, which only needs the **quotient**
  `A/[A,A]` to be finite-dimensional;
* `finrank_symmetricFunctionals_eq_of_algEquiv_pi_matrix`,
  `finrank_symmetricFunctionals_le_wedderburn`, `exists_finrank_symmetricFunctionals_eq` — the
  semisimple statements of `SemisimpleTrace.lean` recovered as special cases, showing the
  generalization is faithful.

## Relation to `SemisimpleTrace.lean`

Nothing there is modified.  `finrank_symmetricFunctionals_le_wedderburn` reproves the conclusion
of `finrank_symmetricFunctionals_le_of_algEquiv_pi_matrix` through the equality proved here
together with `finrank_quot_commSpan_le_of_algEquiv_pi_matrix`.  On this route the
`[FiniteDimensional K A]` hypothesis of the original is not needed — it is in any case redundant,
since the algebra equivalence `e` already forces `A` to be finite-dimensional — so **no hypothesis
has been weakened and no conclusion strengthened**; the two statements are the same mathematical
fact, reached by different routes.

## Status
Proved, axiom-clean, `pbw`-free, no `sorry`.
-/

namespace VOA

open Module (finrank)

variable {K : Type*} [Field K] {A : Type*} [Ring A] [Algebra K A]

/-! ## Surjectivity of `symmetricLift`

`symmetricLift` sends a symmetric functional to the functional it induces on `A/[A,A]`.  It is
already known to be injective (`symmetricLift_injective`).  Surjectivity is the easy direction:
*every* functional on the quotient pulls back to a symmetric functional, because `a*b - b*a` lies
in `commSpan K A` and is therefore killed by the quotient map. -/

section Surjectivity

/-- Pulling a functional on the commutator quotient back along `A ↠ A ⧸ [A,A]` always produces a
**symmetric** functional: `φ(ab) - φ(ba) = ψ(⟦ab - ba⟧) = ψ 0 = 0`. -/
theorem mem_symmetricFunctionals_comp_mkQ (ψ : Module.Dual K (A ⧸ commSpan K A)) :
    (ψ ∘ₗ (commSpan K A).mkQ) ∈ symmetricFunctionals K A := by
  rw [mem_symmetricFunctionals]
  intro a b
  have h : (commSpan K A).mkQ (a * b) = (commSpan K A).mkQ (b * a) := by
    rw [← sub_eq_zero, ← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact mul_sub_mul_mem_commSpan a b
  change ψ ((commSpan K A).mkQ (a * b)) = ψ ((commSpan K A).mkQ (b * a))
  rw [h]

/-- The pullback along `A ↠ A ⧸ [A,A]`, as a `K`-linear map into the symmetric functionals.  This
is the inverse of `symmetricLift`. -/
noncomputable def symmetricOfDualQuot :
    Module.Dual K (A ⧸ commSpan K A) →ₗ[K] symmetricFunctionals K A where
  toFun ψ := ⟨ψ ∘ₗ (commSpan K A).mkQ, mem_symmetricFunctionals_comp_mkQ ψ⟩
  map_add' _ _ := Subtype.ext (LinearMap.ext fun _ => rfl)
  map_smul' _ _ := Subtype.ext (LinearMap.ext fun _ => rfl)

@[simp] theorem symmetricOfDualQuot_apply_apply (ψ : Module.Dual K (A ⧸ commSpan K A)) (a : A) :
    ((symmetricOfDualQuot ψ : symmetricFunctionals K A) : A →ₗ[K] K) a
      = ψ ((commSpan K A).mkQ a) := rfl

@[simp] theorem symmetricLift_apply_mk (φ : symmetricFunctionals K A) (a : A) :
    symmetricLift φ ((commSpan K A).mkQ a) = (φ : A →ₗ[K] K) a := rfl

/-- `symmetricOfDualQuot` is a right inverse of `symmetricLift`. -/
theorem symmetricLift_symmetricOfDualQuot (ψ : Module.Dual K (A ⧸ commSpan K A)) :
    symmetricLift (symmetricOfDualQuot ψ) = ψ := by
  refine LinearMap.ext fun q => ?_
  obtain ⟨x, rfl⟩ := (commSpan K A).mkQ_surjective q
  rfl

/-- **`symmetricLift` is surjective** — for an arbitrary `K`-algebra `A`.  No
finite-dimensionality, no semisimplicity, no algebraically closed `K`. -/
theorem symmetricLift_surjective :
    Function.Surjective (symmetricLift : symmetricFunctionals K A →ₗ[K] _) :=
  fun ψ => ⟨symmetricOfDualQuot ψ, symmetricLift_symmetricOfDualQuot ψ⟩

/-- `symmetricLift` is bijective. -/
theorem symmetricLift_bijective :
    Function.Bijective (symmetricLift : symmetricFunctionals K A →ₗ[K] _) :=
  ⟨symmetricLift_injective, symmetricLift_surjective⟩

end Surjectivity

/-! ## The central equivalence -/

section Equiv

/-- **The central theorem of this layer.**  For a *completely general* `K`-algebra `A` the
symmetric linear functionals on `A` are canonically the full linear dual of the commutator
quotient:

`symmetricFunctionals K A ≃ₗ[K] Module.Dual K (A ⧸ commSpan K A)`.

This is the semisimplicity-free core of Dong–Li–Mason Lemma 10.7 and the foundation on which
Miyamoto's pseudo-trace argument is built.  Semisimplicity of `A`, finite-dimensionality of `A`,
and algebraic closedness of `K` are all irrelevant here; they enter only when one wants to
*compute* `finrank K (A ⧸ commSpan K A)`. -/
noncomputable def symmetricFunctionalsEquivDualQuot :
    symmetricFunctionals K A ≃ₗ[K] Module.Dual K (A ⧸ commSpan K A) :=
  LinearEquiv.ofBijective symmetricLift symmetricLift_bijective

@[simp] theorem symmetricFunctionalsEquivDualQuot_apply (φ : symmetricFunctionals K A) :
    symmetricFunctionalsEquivDualQuot φ = symmetricLift φ := rfl

@[simp] theorem symmetricFunctionalsEquivDualQuot_apply_mk
    (φ : symmetricFunctionals K A) (a : A) :
    symmetricFunctionalsEquivDualQuot φ ((commSpan K A).mkQ a) = (φ : A →ₗ[K] K) a := rfl

theorem symmetricFunctionalsEquivDualQuot_symm_apply
    (ψ : Module.Dual K (A ⧸ commSpan K A)) :
    symmetricFunctionalsEquivDualQuot.symm ψ = symmetricOfDualQuot ψ :=
  symmetricFunctionalsEquivDualQuot.symm_apply_eq.2
    (symmetricLift_symmetricOfDualQuot ψ).symm

end Equiv

/-! ## Dimension and finite-dimensionality — with no semisimplicity -/

section Dimension

/-- **The dimension count without semisimplicity.**
`dim {symmetric functionals on A} = dim (A/[A,A])`, for an arbitrary `K`-algebra `A`.

There are literally no hypotheses: `Subspace.dual_finrank_eq` is unconditional (both sides are
`0` in the infinite-dimensional case), so the equality holds verbatim in general.  In particular
it holds for `[FiniteDimensional K A]`, which is the form Miyamoto's argument uses, and it holds
whether or not `A` is semisimple — **that is the whole point of this file**. -/
theorem finrank_symmetricFunctionals_eq_finrank_quot_commSpan :
    finrank K (symmetricFunctionals K A) = finrank K (A ⧸ commSpan K A) := by
  rw [symmetricFunctionalsEquivDualQuot.finrank_eq, Subspace.dual_finrank_eq]

/-- The sharp finiteness statement: the symmetric functionals are finite-dimensional as soon as
the **commutator quotient** `A/[A,A]` is, even if `A` itself is infinite-dimensional. -/
theorem finiteDimensional_symmetricFunctionals_of_quot
    [FiniteDimensional K (A ⧸ commSpan K A)] :
    FiniteDimensional K (symmetricFunctionals K A) :=
  symmetricFunctionalsEquivDualQuot.symm.finiteDimensional

/-- **The main result of this file.**  For a finite-dimensional `K`-algebra `A` the space of
symmetric linear functionals `φ(ab) = φ(ba)` is finite-dimensional — **with no semisimplicity
hypothesis whatsoever**.

Dong–Li–Mason obtain this finiteness from Artin–Wedderburn, which is unavailable once rationality
of the vertex operator algebra is dropped.  Here it is a formal consequence of
`symmetricFunctionalsEquivDualQuot`: the space is the dual of a quotient of `A`.  This is exactly
the finiteness that Miyamoto's pseudo-trace argument needs for `A = A(𝒱)` with `𝒱` merely
`C₂`-cofinite.

Honest caveat: *in this exact form* the statement is also immediate from typeclass inference,
since `symmetricFunctionals K A` is a submodule of the finite-dimensional space `A →ₗ[K] K`.  The
point being recorded is that **no semisimplicity is used anywhere**, in contrast with DLM's route;
the genuinely sharper statement is `finiteDimensional_symmetricFunctionals_of_quot` above, which
allows `A` itself to be infinite-dimensional. -/
theorem finiteDimensional_symmetricFunctionals [FiniteDimensional K A] :
    FiniteDimensional K (symmetricFunctionals K A) :=
  finiteDimensional_symmetricFunctionals_of_quot

end Dimension

/-! ## The semisimple statements recovered as special cases

Nothing below is new mathematics; it exists to certify that the generalization above is
*faithful*, i.e. that the semisimple bounds of `SemisimpleTrace.lean` factor through it. -/

section Wedderburn

/-- The Wedderburn count in dual form, **as an equality**: if `A ≃ₐ[K] ∏_{i<n} Mat_{dᵢ}(K)` then
the symmetric functionals form an `n`-dimensional space.  (Combines
`finrank_symmetricFunctionals_eq_finrank_quot_commSpan` with
`finrank_quot_commSpan_eq_of_algEquiv_pi_matrix`.) -/
theorem finrank_symmetricFunctionals_eq_of_algEquiv_pi_matrix {n : ℕ} {d : Fin n → ℕ}
    (hd : ∀ i, NeZero (d i))
    (e : A ≃ₐ[K] ∀ i : Fin n, Matrix (Fin (d i)) (Fin (d i)) K) :
    finrank K (symmetricFunctionals K A) = n := by
  rw [finrank_symmetricFunctionals_eq_finrank_quot_commSpan]
  exact finrank_quot_commSpan_eq_of_algEquiv_pi_matrix hd e

/-- **The DLM bound, reproved through the general equivalence.**  This has the same conclusion as
`finrank_symmetricFunctionals_le_of_algEquiv_pi_matrix` in `SemisimpleTrace.lean`, but is deduced
from `finrank_symmetricFunctionals_eq_finrank_quot_commSpan` together with
`finrank_quot_commSpan_le_of_algEquiv_pi_matrix`.

The hypothesis `[FiniteDimensional K A]` of the original is not needed on this route (it is in any
case redundant: `e` already forces `A` to be finite-dimensional), so nothing has been weakened.
The name differs from the original only to avoid a namespace collision. -/
theorem finrank_symmetricFunctionals_le_wedderburn {n : ℕ} {d : Fin n → ℕ}
    (hd : ∀ i, NeZero (d i))
    (e : A ≃ₐ[K] ∀ i : Fin n, Matrix (Fin (d i)) (Fin (d i)) K) :
    finrank K (symmetricFunctionals K A) ≤ n := by
  rw [finrank_symmetricFunctionals_eq_finrank_quot_commSpan]
  exact finrank_quot_commSpan_le_of_algEquiv_pi_matrix hd e

/-- The Artin–Wedderburn packaging, upgraded from `≤ n` to `= n`: for a finite-dimensional
semisimple algebra over an algebraically closed field, the symmetric functionals form a space of
dimension **exactly** the number of Wedderburn factors. -/
theorem exists_finrank_symmetricFunctionals_eq [IsAlgClosed K] [IsSemisimpleRing A]
    [FiniteDimensional K A] :
    ∃ n : ℕ, (∃ d : Fin n → ℕ, (∀ i, NeZero (d i)) ∧
      Nonempty (A ≃ₐ[K] ∀ i : Fin n, Matrix (Fin (d i)) (Fin (d i)) K)) ∧
      finrank K (symmetricFunctionals K A) = n := by
  obtain ⟨n, d, hd, ⟨e⟩⟩ := IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed K A
  exact ⟨n, ⟨d, hd, ⟨e⟩⟩, finrank_symmetricFunctionals_eq_of_algEquiv_pi_matrix hd e⟩

end Wedderburn

end VOA
