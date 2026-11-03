/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Examples.VirasoroGoodFiltration

/-!
# F3 — the refined character, as a **cited hypothesis** and nothing else

⚠⚠ **Caveat: nothing in this file is proved, and nothing in this file may be proved here.**  The file
exists so that the one imported combinatorial input of the graded-unitarity programme is a named
`Prop` that appears in the signature of every statement that uses it, instead of leaking into a
definition where it would be invisible.

## The input

For the boundary Virasoro minimal models `L(c_{2,2n+1}, 0)` the refined generating function

  `p^{s,i}(t,q) = Σ_λ t^{len λ} q^{Δ(λ)}`

of Salazar, arXiv:2405.07126v3 (Theorem 0.1 and §5), gives numbers `a_{N,r}` — the count of
**admissible partitions of `N` of length `r`** — uniformly in `n` via Andrews–Gordon.  The claim
that these are the dimensions of the associated graded of the length filtration **on the simple
quotient**,

  `dim gr_r L(c_{2,2n+1},0)_N = a_{N,r}`,

is the Andrews–Gordon/Salazar refined character.  It is **not** proved in this repository, it is
**not** provable from anything here, and it is recorded below as `AdmissibleBasisHyp`.

Salazar proves more than a dimension formula: Theorem 0.2 states that the admissible PBW
monomials form a basis, and Proposition 2.2 supplies the filtered-basis bridge.  None of this gives
positivity input.  Thus it settles the basis/counting half in the literature, but is not close by
itself to graded unitarity.  The theorem has not yet been formalized in this repository.

## ⚠ Why `a` is still a **parameter** rather than a definition

The source (Salazar, arXiv:2405.07126v3) states the condition explicitly: for a partition `λ` with parts at
least two, `λᵢ - λᵢ₊ₙ₋₁ ≥ 2` whenever both parts occur.  This file does not yet replace the opaque
count parameter by the resulting computable finite set.
That replacement is the first step of a formalization of Salazar's basis theorem; until it is done, keeping
`a` explicit prevents downstream theorems from silently depending on unfinished combinatorics.

So `a : ℕ → ℕ → ℕ` is carried as an **explicit argument**.  Whoever supplies it also supplies the
citation.  This is deliberate and must not be "tidied up" into a concrete definition until the
sources are in `refs/` and have been read.

## What the flag gives unconditionally, for contrast

The *universal* module `V(c,0)` has an honest formalized partition basis (`VirModule.gradedBasis`),
so the length filtration there has completely elementary layer dimensions.  Salazar's basis of
`L(c,0) = V(c,0)/J` at the degenerate central charges is not yet formalized, which is exactly what
`AdmissibleBasisHyp` temporarily abstracts.  `VirGoodFil.goodFil` is therefore defined as an
*image*, never as a span of an unformalized basis; see that file's docstring.

## Status
* Not proved: `AdmissibleBasisHyp` — **cited and unproved in Lean.**  Salazar arXiv:2405.07126v3,
  Theorems 0.1--0.2.
* Not proved: `FlagBasisHyp` — **cited and unproved in Lean.**  The abstract form of the filtered basis that
  Theorem 0.2 and Proposition 2.2 provide and that the minor/pivot criterion
  (`Core.FlagMinors`) consumes.
* Proved: `altSum` and `flagBasisHyp_imp` — the only two things below with proofs; both are trivial
  bookkeeping, and neither asserts anything about `L(c,0)`.

## References
* D. Salazar, arXiv:2405.07126v3, Proposition 2.2, Theorems 0.1--0.2, §5.
* Arabi Ardehali, Beem, Lemos, Rastelli, arXiv:2507.23781v2, §3.
* R. M. Kaufmann, hep-th/9405041, §4.2.
-/

namespace VOA

namespace AdmissiblePartitions

open VOA.VirModule VOA.VirSimple VOA.VirGoodFil
open VOA.VertexOperatorAlgebra
open Module (finrank)

/-! ## §1  ⚠ The cited hypothesis -/

/-- ⚠⚠ **Cited hypothesis: not proved, and not provable here.**

`AdmissibleBasisHyp c a` says that the length flag on `L(c,0)` has the layer dimensions predicted
by the refined Andrews–Gordon/Salazar character `a`: the step `G_p L(c,0)_N` has dimension
`a_{N,0} + ⋯ + a_{N,p}`.

Stated cumulatively rather than as `dim gr_p = a_{N,p}` purely to avoid quotient modules; the two
are equivalent, and the cumulative form is what the reduction consumes directly.

⚠ `a` is temporarily a **parameter**.  See the file docstring: the explicit admissibility
predicate and finite count should replace it in the first Salazar-formalization stage.

Source: D. Salazar, arXiv:2405.07126v3, Theorem 0.1 and §5. -/
def AdmissibleBasisHyp (c : ℂ) (a : ℕ → ℕ → ℕ) : Prop :=
  ∀ N p : ℕ, finrank ℂ (goodFil c p (N : ℤ)) = ∑ r ∈ Finset.range (p + 1), a N r

/-- ⚠⚠ **Cited hypothesis: not proved.**

The abstract basis-level interface: `L(c,0)_N` has a basis indexed by `Fin m`, ordered so that the
**initial segments are exactly the steps of the length flag**.  Equivalently: the admissible
monomials descend to a basis of the simple quotient, listed in nondecreasing order of length.

This is what the leading-principal-minor form of the criterion (`Core.FlagMinors`) needs, and the
`Core.FlagMinors.RefinesBasis` structure is precisely the abstract shape of the conclusion.  For
the boundary minimal models, it follows mathematically from Salazar's Theorem 0.2 together with
the filtered-basis bridge in Proposition 2.2; that implication remains to be formalized here.

⚠ The ordering matters and is not decoration.  Checked numerically at `c = -22/5`, `N = 6`: in the
order `([4], [2,0])` the textbook Gram pivots are `(-77, +682/35)` — signs `(-,+)`, the
alternation the conjecture demands; in the **reversed** order they are `(66/5, -341/3)` — signs
`(+,-)`.  Same subspace, same form, opposite conclusion.  A pivot statement without an explicit
"the flag refines the length" hypothesis is simply **false**. -/
def FlagBasisHyp (c : ℂ) (N : ℕ) : Prop :=
  ∃ (m : ℕ) (e : Module.Basis (Fin m) ℂ ((virasoroSimple c).grading (N : ℤ)))
    (d : ℕ → ℕ) (hd : ∀ p, d p ≤ m),
    ∀ p : ℕ, (virGradedFlag c).pieceIn p (N : ℤ)
      = Submodule.span ℂ (Set.range fun i : Fin (d p) => e (Fin.castLE (hd p) i))

/-! ## §2  The alternating sum — the Step-0 quantity -/

/-- The alternating sum `Σ_{r ≤ p} (-1)^r a_{N,r}`.

At `p` large enough to exhaust `L(c,0)_N` this is the quantity that graded unitarity predicts for
the **signature** of the level-`N` Shapovalov form on the simple quotient — ABLR eq. (3.16) /
Kaufmann eq. (4.4), `sign⟨O|O⟩ = (-1)^{R_O}`.

⚠ It is defined here only as a number attached to `a`. This repository proves **no** relation
between it and any form. Mathlib has real quadratic-form invariants `sigPos` and `sigNeg`; the
missing project interface is the convenient bridge from Hermitian Gram matrices and filtration
pivots to those invariants. See `Core.GradedUnitarity` §"Status". -/
def altSum (a : ℕ → ℕ → ℕ) (N p : ℕ) : ℤ :=
  ∑ r ∈ Finset.range (p + 1), (-1 : ℤ) ^ r * (a N r : ℤ)

@[simp] theorem altSum_zero (a : ℕ → ℕ → ℕ) (N : ℕ) : altSum a N 0 = (a N 0 : ℤ) := by
  simp [altSum]

theorem altSum_succ (a : ℕ → ℕ → ℕ) (N p : ℕ) :
    altSum a N (p + 1) = altSum a N p + (-1 : ℤ) ^ (p + 1) * (a N (p + 1) : ℤ) := by
  simp [altSum, Finset.sum_range_succ]

/-! ## §3  The one implication worth recording -/

/-- A flag basis pins the step dimensions, so `FlagBasisHyp` is the stronger of the two cited
hypotheses: it determines `a` rather than merely matching it.

Recorded as the statement that the step dimension is the size of the initial segment.  This is
bookkeeping about `FlagBasisHyp`; it says nothing about `L(c,0)`. -/
theorem finrank_pieceIn_of_flagBasisHyp {c : ℂ} {N : ℕ}
    {m : ℕ} (e : Module.Basis (Fin m) ℂ ((virasoroSimple c).grading (N : ℤ)))
    {d : ℕ → ℕ} (hd : ∀ p, d p ≤ m) (p : ℕ)
    (hp : (virGradedFlag c).pieceIn p (N : ℤ)
      = Submodule.span ℂ (Set.range fun i : Fin (d p) => e (Fin.castLE (hd p) i))) :
    finrank ℂ ((virGradedFlag c).pieceIn p (N : ℤ)) = d p := by
  rw [hp]
  have hli : LinearIndependent ℂ (fun i : Fin (d p) => e (Fin.castLE (hd p) i)) :=
    e.linearIndependent.comp _ (Fin.castLE_injective (hd p))
  simpa using finrank_span_eq_card hli

end AdmissiblePartitions

end VOA
