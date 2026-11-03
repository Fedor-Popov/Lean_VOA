/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli
-/
import VOA.Modules.WeakModule

/-!
# Admissible (`ℕ`-gradable weak) modules, and `AdmissiblyRational`

The **admissible** module category — Zhu's "`ℕ`-gradable weak modules", Dong–Li–Mason's
"admissible modules" — sits strictly between the ungraded `WeakModule` and the `ℂ`-graded
`OrdVModule` of `Modules/WeakModule.lean`:

  `ordinary  ⊆  admissible  ⊆  weak`.

This file is deliberately a **leaf**: it imports only `Modules/WeakModule.lean`, so that
`Modules/Rationality.lean` can state Gannon's Definition 5.3.2 over the module category Gannon
actually uses (his Def. 5.3.1 "weak" module *is* `ℕ`-graded — see the ⚠ note below) without
dragging in Zhu's algebra.  The Zhu-algebra-facing material — `ZhuAdmissibleSemisimple`, the
`OrdVModule → AdmissibleModule` comparison, the positive witness generator — stays in
`Modules/AdmissibleRationality.lean`, which imports this file.

## ⚠ Naming, stated once and for all

Every rationality predicate in this repository is named for **the module category it quantifies
over**, never by comparison with some other author's stronger notion:

* `AdmissiblyRational` (here) — every **admissible** module is completely reducible.  The standard
  Zhu / Dong–Li–Mason notion; this is what "rational" means in the modern literature.
* `Regular` (`Modules/RationalityLattice.lean`) — every **weak** module is completely reducible.
  Dong–Li–Mason's strongest notion.
* `GannonRational` (`Modules/Rationality.lean`) — Gannon Def. 5.3.2, a three-clause package.

The name `WeaklyRational` is deliberately not used for Gannon's predicate: Gannon's "weakly" is a
comparative against *his own* stronger Def. 6.2.3 "rational",
and says nothing whatever about weak modules — while the predicate's own third field was
transcribed over `WeakModule`, making the natural misreading half-true.  See
`Modules/Rationality.lean`.

## Main declarations

* `AdmissibleModule` — the `ℕ`-gradable weak module (Zhu §1.4, DLM Def. 2.2).
* `AdmissibleModule.IsIrreducible`, `AdmissibleModule.IsCompletelyReducible`.
* `adjointAdmissibleModule` — `𝒱` itself, so the category is never empty.
* `AdmissiblyRational` — every admissible module is completely reducible.
* `IsRational` — a *readability alias* for `AdmissiblyRational`, nothing more.

## References
* Y. Zhu, *Modular invariance of characters of vertex operator algebras*, J. Amer. Math. Soc. **9**
  (1996) 237–302, §1.4.
* Dong–Li–Mason, *Vertex operator algebras and associative algebras*, J. Algebra **206** (1998)
  67–96, Def. 2.2.

## Status
`sorry`-free, with no project axioms.  Every declaration below is `[propext, Classical.choice, Quot.sound]`.
-/

namespace VOA

open Module (End)

universe u v

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## Admissible (`ℕ`-gradable weak) modules -/

/-- An **admissible** (= `ℕ`-gradable weak) `𝒱`-module: Zhu, JAMS **9** (1996), §1.4;
Dong–Li–Mason, J. Algebra **206** (1998) 67–96, Def. 2.2.

The grading is indexed by `ℤ` with the pieces below `0` forced to `⊥` — an `ℕ`-grading in `ℤ`
bookkeeping, so that the mode shift `wt a − p − 1` (which can be negative) needs no truncated
subtraction.  Deliberately **no** finite-dimensionality of the pieces and **no** `L₀`-eigenvalue
condition: that is exactly what separates this from `OrdVModule` (Gannon 5.3.1c), and it is why
this — not `OrdVModule` — is the category that Zhu's and DLM's rationality quantifies over.

⚠ This is *also* the category of Gannon's Def. 5.3.1 "weak `V`-module" (CUP 2006, p. 330), which is
verbatim `ℕ`-graded with this mode shift.  The ungraded `WeakModule` of
`Modules/WeakModule.lean` is Li's / DLM's notion, not Gannon's. -/
structure AdmissibleModule (W : VertexOperatorAlgebra 𝒱) (M : Type v)
    [AddCommGroup M] [Module ℂ M] extends WeakModule W M where
  /-- The level decomposition `M(k)`. -/
  lev : ℤ → Submodule ℂ M
  /-- `ℕ`-gradability: `M(k) = 0` for `k < 0`. -/
  lev_eq_bot_of_neg : ∀ k : ℤ, k < 0 → lev k = ⊥
  /-- `M = ⨁_k M(k)`: a genuine internal direct sum. -/
  isInternal : DirectSum.IsInternal lev
  /-- **The DLM mode-shift axiom** `a₍ₚ₎ M(k) ⊆ M(k + wt a − p − 1)` for `a ∈ 𝒱_w`. -/
  act_lev : ∀ ⦃w p k : ℤ⦄ ⦃a : 𝒱⦄, a ∈ W.grading w → ∀ ⦃x : M⦄, x ∈ lev k →
    mode (YM a) p x ∈ lev (k + (w - p - 1))

namespace AdmissibleModule

variable {W : VertexOperatorAlgebra 𝒱} {M : Type v} [AddCommGroup M] [Module ℂ M]

/-- The mode-shift axiom in the `WeakModule.act` API. -/
theorem act_lev' (N : AdmissibleModule W M) {w p k : ℤ} {a : 𝒱} (ha : a ∈ W.grading w)
    {x : M} (hx : x ∈ N.lev k) :
    N.toWeakModule.act a p x ∈ N.lev (k + (w - p - 1)) := N.act_lev ha hx

/-- The levels span `M` (a free consequence of internality). -/
theorem lev_iSup_eq_top (N : AdmissibleModule W M) : (⨆ k : ℤ, N.lev k) = ⊤ :=
  N.isInternal.submodule_iSup_eq_top

/-- **Irreducible** admissible module: nonzero, with no weak submodule other than `0` and `M`
(same shape as `OrdVModule.IsIrreducible`). -/
def IsIrreducible (N : AdmissibleModule W M) : Prop :=
  Nontrivial M ∧ ∀ P : WeakModule.Submodule' N.toWeakModule, P.carrier = ⊥ ∨ P.carrier = ⊤

/-- **Completely reducible** admissible module: every weak submodule is complemented by a weak
submodule (same shape as `OrdVModule.IsCompletelyReducible`, one category up).  See
`Modules/AdmissibleRationality.lean` for the deliberate choice of *weak* rather than
*level-graded* submodules here. -/
def IsCompletelyReducible (N : AdmissibleModule W M) : Prop :=
  ∀ P : WeakModule.Submodule' N.toWeakModule,
    ∃ Q : WeakModule.Submodule' N.toWeakModule, IsCompl P.carrier Q.carrier

end AdmissibleModule

/-! ## The admissible category is never empty: the adjoint module -/

/-- **The adjoint module `𝒱` is admissible**, for every VOA.  The level family is the VOA's own
`ℤ`-grading: it is `ℕ`-supported by VOA positivity (`W.positivity`), internal by VA0
(`W.isInternal`), and the DLM mode shift is *literally* VA1
(`PreVertexAlgebra.smul_mem_grading`: `u₍ₙ₎ 𝒱_ℓ ⊆ 𝒱_{k+ℓ−n−1}`).

This matters for the reading of `AdmissiblyRational`: the class it quantifies over always has
objects, so the predicate is never vacuously true for lack of admissible modules. -/
def adjointAdmissibleModule (W : VertexOperatorAlgebra 𝒱) : AdmissibleModule W 𝒱 where
  toWeakModule := adjointWeakModule W
  lev := W.grading
  lev_eq_bot_of_neg := fun k hk => W.positivity k hk
  isInternal := W.isInternal
  act_lev := by
    intro w p k a ha x hx
    have hmem := W.smul_mem_grading ha hx p
    have heq : w + k - p - 1 = k + (w - p - 1) := by ring
    rw [heq] at hmem
    exact hmem

/-- The adjoint admissible module has the VOA's own grading as its level family. -/
@[simp] theorem adjointAdmissibleModule_lev (W : VertexOperatorAlgebra 𝒱) :
    (adjointAdmissibleModule W).lev = W.grading := rfl

/-- Its action is the `𝒱`-product, as for `adjointModule`. -/
@[simp] theorem adjointAdmissibleModule_act (W : VertexOperatorAlgebra 𝒱) (u : 𝒱) (n : ℤ)
    (x : 𝒱) : (adjointAdmissibleModule W).toWeakModule.act u n x = W.smul u n x := rfl

/-! ## Rationality in the admissible category -/

/-- **Rational**, in the standard sense of Zhu and Dong–Li–Mason: *every admissible
(`ℕ`-gradable weak) `𝒱`-module is completely reducible*.

This is the predicate the name says it is: it quantifies over the **admissible** category, and
nothing else.  No finiteness of `Φ(𝒱)` is imposed and no "every irreducible weak module is graded"
clause: the first is a *theorem* about rational VOAs (DLM, Math. Ann. **310** (1998), Thm. 8.1(b))
and the second is a regularity-flavoured statement (see `Regular` in
`Modules/RationalityLattice.lean`).

Compare `GannonRational` (`Modules/Rationality.lean`), Gannon's three-clause Def. 5.3.2, which is
**not** comparable to this in either direction: its clause (1) asks complete reducibility only of
*ordinary* modules, which is weaker, while its clause (2) adds a finiteness demand.  Gannon himself
records the gap: his Def. 6.2.3 adds "*every `ℕ`-graded weak module is completely reducible*" —
i.e. this predicate — on top of Def. 5.3.2, with the remark that it "is a little stronger than the
usual complete reducibility requirement". -/
def AdmissiblyRational (W : VertexOperatorAlgebra 𝒱) : Prop :=
  ∀ {M : Type u} [AddCommGroup M] [Module ℂ M] (N : AdmissibleModule W M),
    N.IsCompletelyReducible

/-- **`𝒱` is rational** — a readability alias for `AdmissiblyRational`, so that statements can be
spelled the way the literature spells them.  It adds **no content**.

⚠ **Which notion.**  This alias abbreviates the standard Zhu / Dong–Li–Mason notion.  It is *not*
Gannon Def. 5.3.2 read with clause (3) over ungraded weak modules, and it is *not comparable* to
that reading in either direction; see `Examples/TripletIrrational.lean` §5.

⚠ **Two caveats that must travel with any use of this name.**

1. **Which submodules.** `AdmissibleModule.IsCompletelyReducible` quantifies over *weak*
   submodules with *weak* complements, not level-graded ones. One direction of the relation to
   the graded (DLM-style) reading is proved in Lean:
   `admissiblyRationalGraded_of_admissiblyRational : AdmissiblyRational W →
   AdmissiblyRationalGraded W` (`Modules/AdmissibleGradedComplement.lean`).
   The converse, graded rationality ⟹ `IsRational`, is **not** proved in Lean, so theorems with
   hypothesis `IsRational` do not yet apply to a VOA known to be rational only in the graded sense;
   see the discussion in `Modules/AdmissibleRationality.lean` (on paper, DLM-rational ⟹
   `IsRational` via DLM Thm 8.1; that argument is unchecked).

2. **Which citation.** For "rational ⟹ `A(V)` semisimple", cite **Dong–Li–Mason**, Math. Ann.
   **310** (1998) 571–600, Thm 8.1(a) (arXiv q-alg/9509005v1) — it assumes *only* `g`-rationality,
   with no CFT type, no simplicity, no `C₂`. Do **not** cite Zhu, JAMS **9** (1996), Thm 2.2.3:
   Zhu's own Def. 1.2.4 of "rational" carries **two extra finiteness clauses** that this predicate
   drops, so his theorem is about a different, stronger notion. See `ZhuAdmissibleSemisimple`,
   proved for every VOA as `VOA.zhuAdmissibleSemisimple_holds`
   (`Modularity/ZhuModularityRational.lean`; general form
   `VOA.Huang.ZhuSemisimple.isSemisimpleRing_A_of_admissiblyRational`). The `A_n(V)`
   generalisation is DLM, J. Algebra **206** (1998) 67–96, Thm 4.10(a).

Minor: the quantifier is `∀ {M : Type u}` with `u` the universe of `𝒱`, formally weaker than the
literature's unrestricted one. Benign — every admissible module is a sum of cyclic ones, realizable
in `Type u` — but recorded so it is not mistaken for the general statement.

It lives here, next to the definition it abbreviates, rather than in an `Examples/` file, so that
it cannot drift away from its referent again. -/
abbrev IsRational (W : VertexOperatorAlgebra 𝒱) : Prop := AdmissiblyRational W

end VOA
