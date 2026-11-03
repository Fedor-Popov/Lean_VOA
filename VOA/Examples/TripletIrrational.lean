/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modularity.BlockBoundC2
import VOA.Examples.TripletW2C2
import VOA.Modules.Rationality
import VOA.Modules.AdmissibleRationality

/-!
# The triplet `W(2)` is not rational — `A(W(2))` is not semisimple

The library's genus-one bound (`Modularity.BlockBoundC2`) is the Arike–Nagatomo bound

  `dim 𝒞₁(𝒱) ≤ dim SLF(A(𝒱))`,   hypotheses `VacuumGradeZero 𝒱` and `C2Cofinite 𝒱` only,

whose whole point is that it does **not** assume rationality.  Instantiated at `trivialVOA`,
which *is* rational, the bound is true but not interesting.  This file supplies a non-rational
witness, by turning the bound into an obstruction.

## The argument

`Modularity.SemisimpleTrace.finrank_quot_commSpan_pi_eq` proves that the Artin–Wedderburn factor
count of a finite-dimensional semisimple algebra over an algebraically closed field is *intrinsic*:
it equals `dim (A ⧸ [A,A])`, hence (by the unconditional
`Modularity.SymmetricFunctionals.finrank_symmetricFunctionals_eq_finrank_quot_commSpan`) equals
`dim SLF(A)`.  So **if** `A(𝒱)` were semisimple, `dim SLF(A(𝒱))` would be exactly the number of
simple `A(𝒱)`-modules, which by Zhu's correspondence is the number of irreducible `𝒱`-modules.
Combining with the genus-one bound:

  `dim 𝒞₁(𝒱)  ≤  dim SLF(A(𝒱))  =  #(irreducible 𝒱-modules)`.

For `𝒱 = W(2)` the left side is `5` and the right side is `4`, so `A(W(2))` is not semisimple.

A second, completely independent route is recorded as a cross-check: a finite-dimensional
semisimple `ℂ`-algebra with `n` Wedderburn blocks has dimension a sum of `n` positive squares,
and `dim A(W(2)) = 11` is **not** a sum of four positive squares.  This route uses no genus-one
input at all — not even `C₂`-cofiniteness.

## Main results

* `finrank_symmetricFunctionals_eq_of_wedderburnBlockCount` — for a finite-dimensional
  semisimple algebra over an algebraically closed field whose Wedderburn block count is `n`,
  `dim SLF(A) = n` exactly.  (Repackaging of results already in the library; see
  "⚠ §1 is a repackaging" below.)
* `not_isSemisimpleRing_of_lt_finrank_symmetricFunctionals` — the general obstruction:
  block count `n` plus `n < dim SLF(A)` forces `A` non-semisimple.
* `finrank_symmetricFunctionals_matrix_two`, `finrank_symmetricFunctionals_pi_four` — concrete
  positive controls: `dim SLF(M₂(ℂ)) = 1` and `dim SLF(∏_{i<4} ℂ) = 4`, so the count really is the
  Wedderburn count and the number `4` in the contradiction is genuinely computed, not stipulated.
* `not_isSemisimpleRing_A_of_blocks_lt_finrank_analyticBlocks` — the same, driven by the
  genus-one bound: `hzero + hC2 +` block count `n +` `n < dim 𝒞₁(𝒱)` gives
  `¬ IsSemisimpleRing (A 𝒱)`.
* `finrank_eq_sum_sq_of_algEquiv_pi_matrix`, `not_eleven_sum_four_pos_sq`,
  `not_isSemisimpleRing_of_finrank_eq_eleven` — the arithmetic cross-check.
* `tripletW2_not_isSemisimpleRing_A` and
  `tripletW2_not_isSemisimpleRing_A_of_finrank_eleven` — `¬ IsSemisimpleRing (A tripletW2)`, by
  the two routes.
* `not_admissiblyRational_tripletW2` and
  `not_admissiblyRational_tripletW2_of_finrank_eleven` (§6) — hence `W(2)` is not rational, in the
  **standard** sense `AdmissiblyRational` (Zhu, JAMS **9** (1996); Dong–Li–Mason, J. Algebra
  **206** (1998)): *every admissible (`ℕ`-gradable weak) module is completely reducible*.  This is
  the statement the literature means by "`W(2)` is not rational".
  ⚠ These are stated over `IsRational := AdmissiblyRational`, not over Gannon's
  Def. 5.3.2 (`GannonRational`); §5 records why the two notions differ.

## ⚠ Everything here is CONDITIONAL.  The named hypotheses, with citations

Nothing below is unconditional, and the honest main statement is
*"`A(W(2))` is not semisimple, conditional on `C2Cofinite tripletW2` and two citations"*.
The imported facts are carried as **explicit named hypotheses**, never as definitions:

1. `hC2 : C2Cofinite tripletW2` — Abe, *A `ℤ₂`-orbifold model of the symplectic fermionic vertex
   operator superalgebra*, Math. Z. **255** (2007) 755–792, Theorem 3.9.  **Not proved in this
   repository**; `Examples.TripletW2C2` and `Examples.TripletW2C2Direct` reduce it to one
   residual step.  (Route 2 does not need it.)

2. `hblocks : WedderburnBlockCount ℂ (A tripletW2) 4` — "any Artin–Wedderburn decomposition of
   `A(W(2))` has exactly four matrix factors".  Justified by
   Abe *op. cit.* **Theorem 4.2** (the complete list of inequivalent simple `SF⁺`-modules is
   `{𝓕⁺, 𝓕⁻, 𝓕ₜ⁺, 𝓕ₜ⁻}`, four of them, for every `d ≥ 1`; and `SF(1)⁺ ≅ W(2)`, Abe Remark 3.9)
   together with Zhu's correspondence (Zhu, *Modular invariance of characters of vertex operator
   algebras*, J. Amer. Math. Soc. **9** (1996) 237–302, Theorem 2.2.3(2): `Ω` is a bijection
   between inequivalent simple `𝒱`-modules and inequivalent simple `A(𝒱)`-modules).  The blocks
   of a Wedderburn decomposition biject with the simple modules.

3. `hfive : 5 ≤ dim 𝒞₁(W(2))` — Arike–Nagatomo, *Some remarks on pseudo-trace functions for
   orbifold models associated with symplectic fermions*, Internat. J. Math. **24** (2013), no. 2,
   1350008 (`arXiv:1104.0068`), **Theorem 6.3.2(4)–(5)**: for the `ℤ₂`-orbifold `𝓕⁺` of `d` pairs
   of symplectic fermions, `dim 𝒞(𝓕⁺) ≥ 2^{2d−1} + 3`, which at `d = 1` — where `𝓕⁺ ≅ W(2)` — is
   `≥ 5`.  This is the **lower** half, and it is *proved* there by explicit construction:
   part (4) proves that the pseudo-trace functions `{S^{c·φ} | c ∈ Z(Ω)}` are nonzero and linearly
   independent, and part (5) adjoins the two ordinary trace functions on `𝓕ₜ^±`.  It does **not**
   use the upper bound, so combining it with the genus-one bound here is **not circular**.
   (Their Theorem **6.3.4**, `dim 𝒞(W(2)) = 5` exactly, *does* use their own upper bound
   Theorem 3.3.6 — which is the genus-one bound imported here — so using **6.3.4** instead of 6.3.2
   *would* be circular.  We deliberately do not.)

4. `hdim : dim A(W(2)) = 11` (route 2 only) — Adamović–Milas, *The structure of Zhu's algebras for
   certain `W`-algebras*, Adv. Math. **227** (2011) 2425–2456 (`arXiv:1006.5134`),
   **Theorem 4.6** (arXiv numbering): `dim A(W(p)) = 6p − 1`, so `11` at `p = 2`.
   Cross-checked by the explicit shape
   `A(W(2)) ≅ ℂ ⊕ M₂(ℂ) ⊕ M₂(ℂ) ⊕ ℂ[ε]/(ε²)` recorded in Arike–Nagatomo `§5.3`
   (their Proposition 5.3.2, after Abe Prop. 4.6 and Nagatomo–Tsuchiya Thm. 4.6), of dimension
   `1 + 4 + 4 + 2 = 11`.

5. `hzhu : ZhuAdmissibleSemisimple 𝒱` (§6) — *if every admissible module is completely reducible
   then `A(𝒱)` is semisimple*.  **Dong–Li–Mason**, *Vertex operator algebras and associative
   algebras*, J. Algebra **206** (1998) 67–96, **Theorem 4.10(a)**; see also *Twisted
   representations of vertex operator algebras*, Math. Ann. **310** (1998) 571–600, Thm. 8.1(a).
   ⚠ **Do not cite Zhu JAMS 9 (1996) Thm. 2.2.3 as the licence**: Zhu's Def. 1.2.4 of "rational"
   carries two extra finiteness clauses that `AdmissiblyRational` drops, so his theorem is about a
   different, stronger predicate.  ⚠ This is a **theorem of the literature, not a definitional
   consequence** of `AdmissiblyRational`, and is therefore carried as a hypothesis, never
   proved and never folded into a definition.

## ⚠ A convention caveat on hypothesis 3, recorded because it is the load-bearing one

`𝒞₁(𝒱)` is modelled here as `Submodule.map restrictImGT (analyticBlocks 𝒱)`, and
`IsAnalyticBlock` (`Modularity.AnalyticBlock`) is Zhu's/Arike–Nagatomo's definition of a one-point
function on the elliptic curve: holomorphic on `ℍ`, linear in `v`, killed by `a[0]v`, satisfying
the `[−2]`-identity, and satisfying the `ω`-recursion.  Two deliberate differences from the
printed definition, neither of which changes the space:

* the `[−2]`-identity is imposed with the sum starting at `G₂` rather than `G₄`; the extra term is
  `G₂(z)·F(a[0]v)(z)`, which vanishes by the `a[0]`-condition, which is imposed simultaneously;
* the `ω`-recursion is imposed for **all** `v`, not only for square-bracket homogeneous `v`; both
  sides are linear in `v`, so this is equivalent, but *the equivalence is not proved in Lean*.

Consequently hypothesis 3 is a statement about the **repository's** block space, and asserting it
from Arike–Nagatomo's theorem takes for granted that their five functions satisfy the repository's
conditions.  Mathematically they do; formally this is part of what the citation buys.  This is
flagged rather than hidden.

## Status
No `sorry`, no `admit`, no `native_decide`, no `unsafe`, no new axioms, and
`VOA.pbw`-free (nothing here consumes a `BottomProjection`).

## ⚠ §1 is a repackaging

`Modularity.SymmetricFunctionals.finrank_symmetricFunctionals_eq_of_algEquiv_pi_matrix` and
`exists_finrank_symmetricFunctionals_eq` already prove "`dim SLF(A) =` number of Wedderburn
blocks", carrying the algebra equivalence explicitly.  §1 below only wraps them in the
`WedderburnBlockCount` predicate that the obstruction consumes; it is not new content.
-/

namespace VOA.Irrationality

open VOA
open VOA.SympFerm
open Module (finrank)

/-! ## §1  The Wedderburn block count and the space of symmetric functionals -/

section GeneralAlgebra

variable (K : Type*) [Field K] (A : Type*) [Ring A] [Algebra K A]

/-- **`A` has Wedderburn block count `n`**: *every* Artin–Wedderburn decomposition of `A` into
matrix algebras over `K` has exactly `n` factors.

Stated this way — quantifying over decompositions rather than asserting one — because that is the
shape `Modularity.SemisimpleTrace` supplies (`exists_wedderburn_finrank_quot_commSpan_le` returns
the equivalence explicitly), and because it is exactly what an *external* count of simple modules
justifies: by Artin–Wedderburn the factors of any decomposition biject with the simple
`A`-modules, so knowing the number of simple modules pins `n` down.

⚠ Note this predicate is **vacuously true** when `A` admits no such decomposition, in particular
when `A` is not semisimple.  It is the implication "*if* `A` is a product of matrix algebras,
there are `n` factors", not an assertion that `A` has `n` simple modules; hypothesis lists that
take it assume less than the prose "four simple modules" suggests (harmless for correctness). -/
def WedderburnBlockCount (n : ℕ) : Prop :=
  ∀ (m : ℕ) (d : Fin m → ℕ), (∀ i, NeZero (d i)) →
    Nonempty (A ≃ₐ[K] ∀ i : Fin m, Matrix (Fin (d i)) (Fin (d i)) K) → m = n

variable {K A}

/-- **The block count is the dimension of the symmetric functionals.**

For a finite-dimensional semisimple algebra over an algebraically closed field with Wedderburn
block count `n`,

  `dim SLF(A) = n`.

This is the general lemma the obstruction needs.  Its two ingredients are already in the library:
Mathlib's Artin–Wedderburn (`IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed`) produces
*some* decomposition, and
`Modularity.SymmetricFunctionals.finrank_symmetricFunctionals_eq_of_algEquiv_pi_matrix` evaluates
`dim SLF(A)` on it as an **equality** (through
`Modularity.SemisimpleTrace.finrank_quot_commSpan_pi_eq`, the exact intrinsic count, and the
unconditional `finrank_symmetricFunctionals_eq_finrank_quot_commSpan`).  The `WedderburnBlockCount`
hypothesis is what transfers the count from *that* decomposition to the externally known `n`. -/
theorem finrank_symmetricFunctionals_eq_of_wedderburnBlockCount [IsAlgClosed K] [IsSemisimpleRing A]
    [FiniteDimensional K A] {n : ℕ} (hcount : WedderburnBlockCount K A n) :
    finrank K (symmetricFunctionals K A) = n := by
  obtain ⟨m, d, hd, ⟨e⟩⟩ := IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed K A
  rw [finrank_symmetricFunctionals_eq_of_algEquiv_pi_matrix hd e]
  exact hcount m d hd ⟨e⟩

/-- **The general obstruction.**  If `A` would have only `n` Wedderburn blocks but its space
of symmetric linear functionals is bigger than `n`-dimensional, then `A` is **not** semisimple.

Contrapositive of `finrank_symmetricFunctionals_eq_of_wedderburnBlockCount`. -/
theorem not_isSemisimpleRing_of_lt_finrank_symmetricFunctionals [IsAlgClosed K]
    [FiniteDimensional K A] {n : ℕ} (hcount : WedderburnBlockCount K A n)
    (hlt : n < finrank K (symmetricFunctionals K A)) :
    ¬ IsSemisimpleRing A := by
  intro hss
  haveI := hss
  have h := finrank_symmetricFunctionals_eq_of_wedderburnBlockCount (K := K) (A := A) hcount
  omega

end GeneralAlgebra

/-! ### Positive controls against vacuity

The whole argument turns on `dim SLF(A)` being *literally* the Wedderburn block count, so it is
worth two concrete evaluations that a degenerate `symmetricFunctionals` would fail. -/

section Controls

/-- **Control 1.**  On `M₂(ℂ)` — simple, one Wedderburn block — the symmetric linear functionals
form a **one**-dimensional space (spanned by the trace).  A `symmetricFunctionals` that were
accidentally `⊥`, or accidentally the whole dual, would give `0` or `4` here. -/
theorem finrank_symmetricFunctionals_matrix_two :
    finrank ℂ (symmetricFunctionals ℂ (Matrix (Fin 2) (Fin 2) ℂ)) = 1 :=
  finrank_symmetricFunctionals_eq_of_algEquiv_pi_matrix (d := fun _ : Fin 1 => 2)
    (fun _ => ⟨two_ne_zero⟩)
    (AlgEquiv.funUnique ℂ (Fin 1) (Matrix (Fin 2) (Fin 2) ℂ)).symm

/-- **Control 2, the number `4` actually being computed.**  A semisimple `ℂ`-algebra with four
Wedderburn blocks has a **four**-dimensional space of symmetric linear functionals — this is the
right-hand side that `5 ≤ dim 𝒞₁(W(2))` contradicts. -/
theorem finrank_symmetricFunctionals_pi_four :
    finrank ℂ (symmetricFunctionals ℂ (∀ _ : Fin 4, Matrix (Fin 1) (Fin 1) ℂ)) = 4 :=
  finrank_symmetricFunctionals_eq_of_algEquiv_pi_matrix (d := fun _ : Fin 4 => 1)
    (fun _ => ⟨one_ne_zero⟩) (AlgEquiv.refl)

end Controls

/-! ## §2  The dimension of a semisimple algebra is a sum of squares

An independent arithmetic obstruction, using no genus-one input whatsoever. -/

section SumOfSquares

variable {K : Type*} [Field K] {A : Type*} [Ring A] [Algebra K A]

/-- The dimension of `∏_{i<m} Mat_{dᵢ}(K)`, transported along an algebra equivalence: a
**sum of `m` positive squares**. -/
theorem finrank_eq_sum_sq_of_algEquiv_pi_matrix {m : ℕ} {d : Fin m → ℕ}
    (e : A ≃ₐ[K] ∀ i : Fin m, Matrix (Fin (d i)) (Fin (d i)) K) :
    finrank K A = ∑ i, d i * d i := by
  rw [e.toLinearEquiv.finrank_eq, Module.finrank_pi_fintype]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Module.finrank_matrix, Module.finrank_self, mul_one, Fintype.card_fin]

/-- **`11` is not a sum of four positive squares.**

With four parts from `{1, 4, 9, …}` the achievable totals below `16` are
`4, 7, 10, 12, 13, 15` — and `11` is missing.  (The naive bound is `dᵢ ≤ 3`, since `4² = 16 > 11`;
`interval_cases` then closes the `3⁴ = 81` remaining cases.)

⚠ This is genuinely special to `p = 2`.  At `p = 3` the triplet has `dim A(W(3)) = 17` with `6`
irreducible modules, and `1+1+1+1+4+9 = 17` **is** achievable, so the arithmetic route gives
nothing there. -/
theorem not_eleven_sum_four_pos_sq {a b c e : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (he : 0 < e) : a * a + b * b + c * c + e * e ≠ 11 := by
  intro h
  have sq_le : ∀ {x : ℕ}, x * x ≤ 11 → x ≤ 3 := by
    intro x hx
    by_contra hcon
    have h4 : 4 ≤ x := by omega
    have : 4 * 4 ≤ x * x := Nat.mul_le_mul h4 h4
    omega
  have hbb : 1 ≤ b * b := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero hb.ne' hb.ne')
  have hcc : 1 ≤ c * c := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero hc.ne' hc.ne')
  have hee : 1 ≤ e * e := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero he.ne' he.ne')
  have haa : 1 ≤ a * a := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero ha.ne' ha.ne')
  have ha3 : a ≤ 3 := sq_le (by omega)
  have hb3 : b ≤ 3 := sq_le (by omega)
  have hc3 : c ≤ 3 := sq_le (by omega)
  have he3 : e ≤ 3 := sq_le (by omega)
  interval_cases a <;> interval_cases b <;> interval_cases c <;> interval_cases e <;> omega

/-- **The arithmetic obstruction.**  A `ℂ`-algebra (more generally: an algebra over an
algebraically closed field) of dimension `11` whose Wedderburn block count would be `4` is not
semisimple, because `11` is not a sum of four positive squares.

Independent of every genus-one statement: no `C₂`-cofiniteness, no block space, no genus-one bound. -/
theorem not_isSemisimpleRing_of_finrank_eq_eleven [IsAlgClosed K] [FiniteDimensional K A]
    (hcount : WedderburnBlockCount K A 4) (hdim : finrank K A = 11) :
    ¬ IsSemisimpleRing A := by
  intro hss
  haveI := hss
  obtain ⟨m, d, hd, ⟨e⟩⟩ := IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed K A
  have hm : m = 4 := hcount m d hd ⟨e⟩
  subst hm
  have hsum : finrank K A = ∑ i, d i * d i := finrank_eq_sum_sq_of_algEquiv_pi_matrix e
  rw [hdim, Fin.sum_univ_four] at hsum
  exact not_eleven_sum_four_pos_sq (Nat.pos_of_ne_zero (hd 0).out)
    (Nat.pos_of_ne_zero (hd 1).out) (Nat.pos_of_ne_zero (hd 2).out)
    (Nat.pos_of_ne_zero (hd 3).out) hsum.symm

end SumOfSquares

/-! ## §3  The obstruction, driven by the genus-one bound

`Modularity.BlockBoundC2.finrank_analyticBlocks_le_finrank_symmetricFunctionals` — Arike–Nagatomo
Theorem 3.3.6, `dim 𝒞₁(𝒱) ≤ dim SLF(A(𝒱))`, with hypotheses `VacuumGradeZero` and `C2Cofinite`
only — meets §1's obstruction here. -/

section Milestone

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] (W : VertexOperatorAlgebra 𝒱)

/-- **The contradiction lemma.**

If `𝒱` is `C₂`-cofinite with one-dimensional grade zero, if `A(𝒱)` would have only `n` Wedderburn
blocks, and if the genus-one block space `𝒞₁(𝒱)` has dimension **greater** than `n`, then `A(𝒱)`
is **not semisimple**.

The chain is

  `n  <  dim 𝒞₁(𝒱)  ≤  dim SLF(A(𝒱))  =  n` ,

the middle step being the genus-one bound
(`Modularity.BlockBoundC2.finrank_analyticBlocks_le_finrank_symmetricFunctionals`) and the last
`finrank_symmetricFunctionals_eq_of_wedderburnBlockCount`, which is where semisimplicity is used
and refuted.

This is the statement that makes the genus-one bound *do work*: an upper bound on `dim 𝒞₁` becomes a
lower bound on the complexity of `A(𝒱)` as soon as one knows `dim 𝒞₁` from below. -/
theorem not_isSemisimpleRing_A_of_blocks_lt_finrank_analyticBlocks
    (hzero : VacuumGradeZero W) (hC2 : C2Cofinite W) {n : ℕ}
    (hcount : letI := instRingA W; letI := instAlgebraA W;
      WedderburnBlockCount ℂ (A W) n)
    (hlow : n < finrank ℂ (Submodule.map restrictImGT (analyticBlocks W))) :
    letI := instRingA W; ¬ IsSemisimpleRing (A W) := by
  letI := instRingA W
  letI := instAlgebraA W
  haveI : FiniteDimensional ℂ (A W) := finiteDimensional_A_of_C2Cofinite W hC2
  refine not_isSemisimpleRing_of_lt_finrank_symmetricFunctionals hcount ?_
  exact lt_of_lt_of_le hlow
    (finrank_analyticBlocks_le_finrank_symmetricFunctionals W hzero hC2)

end Milestone

/-! ## §4  The application: `A(W(2))` is not semisimple

Two routes, on disjoint citations.  Every imported fact is an explicit hypothesis; see the module
docstring for the citation of each. -/

section TripletW2

/-- **`A(W(2))` is not semisimple** — route 1, through the genus-one bound.

Hypotheses, each a citation and none of them proved here:

* `hC2 : C2Cofinite tripletW2` — Abe, Math. Z. **255** (2007) 755–792, Theorem 3.9.
* `hblocks` — `A(W(2))` would have exactly four Wedderburn blocks: Abe *op. cit.* Theorem 4.2
  (four inequivalent simple `SF⁺`-modules `𝓕^±, 𝓕ₜ^±`) plus Zhu's correspondence
  (Zhu, JAMS **9** (1996), Theorem 2.2.3(2)).
* `hfive` — `dim 𝒞₁(W(2)) ≥ 5`: Arike–Nagatomo, Internat. J. Math. **24** (2013) 1350008
  (`arXiv:1104.0068`), Theorem 6.3.2(4)–(5) at `d = 1`, where `𝓕⁺ ≅ W(2)`.  This is their
  *construction* half — five explicitly constructed, provably linearly independent one-point
  functions — and does **not** use their upper bound, so the argument is not circular.

`VacuumGradeZero tripletW2` is free (`tripletW2_vacuumGradeZero`, from the VOA structure field).

The contradiction is `5 ≤ dim 𝒞₁(W(2)) ≤ dim SLF(A(W(2))) = 4`. -/
theorem tripletW2_not_isSemisimpleRing_A
    (hC2 : C2Cofinite tripletW2)
    (hblocks : letI := instRingA tripletW2; letI := instAlgebraA tripletW2;
      WedderburnBlockCount ℂ (A tripletW2) 4)
    (hfive : 5 ≤ finrank ℂ (Submodule.map restrictImGT (analyticBlocks tripletW2))) :
    letI := instRingA tripletW2; ¬ IsSemisimpleRing (A tripletW2) :=
  not_isSemisimpleRing_A_of_blocks_lt_finrank_analyticBlocks tripletW2
    tripletW2_vacuumGradeZero hC2 hblocks (by omega)

/-- **`A(W(2))` is not semisimple** — route 2, purely arithmetic, as an independent
cross-check.

Hypotheses:

* `hblocks` — as above (Abe Theorem 4.2 + Zhu's correspondence);
* `hdim : dim A(W(2)) = 11` — Adamović–Milas, Adv. Math. **227** (2011) 2425–2456
  (`arXiv:1006.5134`), Theorem 4.6 (arXiv numbering): `dim A(W(p)) = 6p − 1`.

⚠ Note what is **not** needed: `C2Cofinite tripletW2`, the block space, the genus-one bound, and indeed
anything at all about `W(2)` as a vertex operator algebra.  The whole content is that `11` is not
a sum of four positive squares.  Finite-dimensionality of `A(W(2))` follows from `hdim`
(`finrank = 11 ≠ 0`), so a separate `FiniteDimensional` hypothesis is redundant.  `hblocks` is
only the implication "if `A(W(2)) ≅ ∏ Mₐᵢ(ℂ)` then there are `4` factors"; it is vacuously true
when `A(W(2))` is not semisimple, so it asserts less than "four simple modules".

⚠ This route does **not** generalize: see `not_eleven_sum_four_pos_sq`. -/
theorem tripletW2_not_isSemisimpleRing_A_of_finrank_eleven
    (hfin : FiniteDimensional ℂ (A tripletW2))
    (hblocks : letI := instRingA tripletW2; letI := instAlgebraA tripletW2;
      WedderburnBlockCount ℂ (A tripletW2) 4)
    (hdim : finrank ℂ (A tripletW2) = 11) :
    letI := instRingA tripletW2; ¬ IsSemisimpleRing (A tripletW2) := by
  letI := instRingA tripletW2
  letI := instAlgebraA tripletW2
  haveI := hfin
  exact not_isSemisimpleRing_of_finrank_eq_eleven hblocks hdim

end TripletW2

/-! ## §5  ⚠ Remark: Gannon's rationality versus the admissible notion

`IsRational` abbreviates `AdmissiblyRational` (`Modules/AdmissibleModule.lean`), the standard
Zhu / Dong–Li–Mason notion, and the irrationality corollaries of this file are stated in §6 for
that notion.  Three points about the alternative, Gannon's Def. 5.3.2:

1. Its faithful transcription is `GannonRational` (`Modules/Rationality.lean`).  Gannon's
   Def. 5.3.1 "weak module" is `ℕ`-**graded**, i.e. Dong–Li–Mason admissible; a transcription over
   the *ungraded* `WeakModule`, with a detached conclusion `Nonempty (OrdVModule W M)` rather than
   a statement about the given module, is not faithful.
2. `GannonRational` and `AdmissiblyRational` are different notions, not two names for one notion:
   `GannonRational ⇏ AdmissiblyRational` (`Modules/RationalityLattice.lean` §8.2).
3. The semisimplicity hypothesis `ZhuAdmissibleSemisimple` (`Modules/AdmissibleRationality.lean`)
   carries the correct licence: Dong–Li–Mason, *Vertex operator algebras and associative
   algebras*, J. Algebra **206** (1998) 67–96, **Thm. 4.10(a)** (the `A_n` generalisation of
   *Twisted representations of vertex operator algebras*, Math. Ann. **310** (1998) 571–600,
   Thm. 8.1(a)), together with the explicit warning **not** to cite Zhu JAMS **9** (1996)
   Thm. 2.2.3 for it (Zhu's own Def. 1.2.4 of "rational" carries two extra finiteness clauses
   that the admissible notion drops).  Attaching Zhu's/DLM's semisimplicity theorem to Gannon's
   predicate would be a **mis-licensed citation**: Gannon clause (1) asks complete reducibility
   only of *ordinary* modules, and Gannon himself flags the gap in his Def. 6.2.3.

The load-bearing content of this file is `tripletW2_not_isSemisimpleRing_A` and
`tripletW2_not_isSemisimpleRing_A_of_finrank_eleven`; the rationality hypothesis enters only in §6,
as `ZhuAdmissibleSemisimple`.

**What is *not* claimed.**  `¬ GannonRational tripletW2` is **not** proved anywhere, and is not a
consequence of §6: `GannonRational ⇏ AdmissiblyRational`
(`Modules/RationalityLattice.lean` §8.2), so §6's negation does not transport to it.  Refuting
Gannon's predicate directly would mean refuting its clause (1) — that every *ordinary* `W(2)`-module
is completely reducible — which is true (Adamović–Milas, Adv. Math. **217** (2008), Prop. 4.2,
exhibits indecomposable non-semisimple ordinary modules) but needs those modules built in Lean, and
this repository has no `W(2)`-modules at all.  It is left undone and stated, not asserted.

⚠ On a citation that is easy to misread: McRae,
*On rationality for `C₂`-cofinite vertex operator algebras* (`arXiv:2108.01898`), **Definition 2.3**
in the current version (numbered **2.4** in earlier versions — the numbering moved), defines the
*grading-restricted generalized `𝒱`-module*; it is **not** a definition of rationality.  McRae uses
the standard meaning, "the category of grading-restricted generalized `𝒱`-modules is semisimple",
which is what `AdmissiblyRational` targets. -/

/-! ## §6  The standard notion — `W(2)` is not rational in the admissible (Zhu / DLM) sense

⚠ **Why this section exists.**  These are the *only* irrationality corollaries in this file,
and they target the notion Zhu's and Dong–Li–Mason's semisimplicity theorem is actually stated for:
`AdmissiblyRational` (`Modules/AdmissibleModule.lean`) — *every admissible (`ℕ`-gradable weak)
module is completely reducible*.

They are not stated over a transcription of Gannon Def. 5.3.2, for two reasons:

* Gannon's clause (1) quantifies only over `OrdVModule`s — *ordinary* modules, a **proper
  subcategory** of the admissible ones — so it is strictly weaker than the Zhu/DLM clause, and
  `GannonRational ⇏ AdmissiblyRational` (`Modules/RationalityLattice.lean` §8.2).  Attaching Zhu's
  semisimplicity theorem to it would be a **mis-licensed citation**.
* A transcription over the ungraded `WeakModule` rather than over Gannon's own
  `ℕ`-graded Def. 5.3.1 notion, concluding a detached `Nonempty (OrdVModule W M)`, is not
  faithful; the faithful transcription is `GannonRational` (`Modules/Rationality.lean`).

The load-bearing content lives upstream in this file:
`tripletW2_not_isSemisimpleRing_A` and `tripletW2_not_isSemisimpleRing_A_of_finrank_eleven`.  The
rationality hypothesis is the correctly licensed `ZhuAdmissibleSemisimple`.

⚠ `AdmissiblyRational` is not vacuous: `Examples/TrivialAdmissiblyRational.lean` proves
`AdmissiblyRational trivialVOA`, so these are not negations of an unsatisfiable predicate. -/

section AdmissibleNotRational

/-- **The triplet `W(2)` is NOT rational**, in the standard admissible sense of Zhu and
Dong–Li–Mason.

Conditional on four named inputs, all cited in the module docstring, the fourth of them stated
over the standard notion:

* `hC2 : C2Cofinite tripletW2` (Abe, Math. Z. **255** (2007), Theorem 3.9);
* `hblocks`: `A(W(2))` would have four Wedderburn blocks (Abe *op. cit.* Theorem 4.2 with Zhu's
  correspondence, JAMS **9** (1996) Theorem 2.2.3(2));
* `hfive`: `dim 𝒞₁(W(2)) ≥ 5` (Arike–Nagatomo, IJM **24** (2013) 1350008, Theorem 6.3.2(4)–(5));
* `hzhu : ZhuAdmissibleSemisimple tripletW2` — **Dong–Li–Mason**, *Vertex operator algebras and
  associative algebras*, J. Algebra **206** (1998) 67–96, **Thm. 4.10(a)**: if every admissible
  module is completely reducible then `A(𝒱)` is semisimple.  ⚠ **Not** Zhu JAMS **9** (1996)
  Thm. 2.2.3 — Zhu's Def. 1.2.4 of "rational" carries two extra finiteness clauses that
  `AdmissiblyRational` drops, so his theorem is about a stronger predicate; see the licence note
  on `ZhuAdmissibleSemisimple` itself.  ⚠ Carried as a hypothesis; not proved here, and **not**
  folded into the definition of `AdmissiblyRational`. -/
theorem not_admissiblyRational_tripletW2
    (hC2 : C2Cofinite tripletW2)
    (hblocks : letI := instRingA tripletW2; letI := instAlgebraA tripletW2;
      WedderburnBlockCount ℂ (A tripletW2) 4)
    (hfive : 5 ≤ finrank ℂ (Submodule.map restrictImGT (analyticBlocks tripletW2)))
    (hzhu : ZhuAdmissibleSemisimple tripletW2) :
    ¬ AdmissiblyRational tripletW2 :=
  fun hrat => tripletW2_not_isSemisimpleRing_A hC2 hblocks hfive (hzhu hrat)

/-- **`W(2)` is not rational (standard notion)** — the arithmetic route.

⚠ Note what is **absent from the hypothesis list**: there is no `C2Cofinite tripletW2`, no block
space, no genus-one bound.  The whole content is that `dim A(W(2)) = 11` is not a sum of four
positive squares, so a four-block semisimple algebra of dimension `11` cannot exist.  This is the
same disjoint-citation cross-check as `not_admissiblyRational_tripletW2`, from an entirely
different literature input.

`hfin : FiniteDimensional ℂ (A tripletW2)` appears because, without `C₂`-cofiniteness, nothing
else in scope supplies it; it also follows from `hdim`, but assuming it is cheaper than deriving
it. -/
theorem not_admissiblyRational_tripletW2_of_finrank_eleven
    (hfin : FiniteDimensional ℂ (A tripletW2))
    (hblocks : letI := instRingA tripletW2; letI := instAlgebraA tripletW2;
      WedderburnBlockCount ℂ (A tripletW2) 4)
    (hdim : finrank ℂ (A tripletW2) = 11)
    (hzhu : ZhuAdmissibleSemisimple tripletW2) :
    ¬ AdmissiblyRational tripletW2 :=
  fun hrat =>
    tripletW2_not_isSemisimpleRing_A_of_finrank_eleven hfin hblocks hdim (hzhu hrat)

end AdmissibleNotRational

end VOA.Irrationality
