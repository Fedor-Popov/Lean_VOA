/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modules.PoissonDescent
import VOA.Modularity.TraceSpace

/-!
# Poisson traces on `A₂(𝒱)` and the Etingof–Schedler finiteness hypothesis

Arakawa–Kawasetsu (*Quasi-lisse vertex algebras and modular linear differential equations*,
arXiv:1610.05865) generalize Zhu's modularity theorem by replacing `C₂`-cofiniteness with
**quasi-lisse**-ness.  Their linear-algebra input is the space of **Poisson traces** on the
Poisson algebra `A₂(𝒱) = 𝒱 ⧸ O₂(𝒱)` — the linear functionals annihilating every bracket — whose
finite-dimensionality they obtain from Etingof–Schedler (*Poisson traces and D-modules on Poisson
varieties*, GAFA **20** (2010) 958–987, arXiv:0908.3868).

This file assembles that side of the story, with **no algebraic geometry**:

* the span of the brackets `{A₂, A₂} ≤ A₂(𝒱)` (`poissonSpan`), an instance of the `bilinSpan`
  construction of `Modularity.TraceSpace` applied to the descended bracket `A₂bracket` of
  `Modules.PoissonDescent`;
* the zeroth Poisson homology `HP₀(A₂ 𝒱) = A₂(𝒱) ⧸ {A₂, A₂}` — a `ℂ`-**vector space**, not a ring
  (the bracket span is not an ideal, and nothing here claims it is);
* the Poisson traces `poissonTraces W = HP₀(A₂ 𝒱)*`, again via `Modularity.TraceSpace`;
* the **Etingof–Schedler hypothesis** `EtingofFinite W : Prop`, i.e. `dim HP₀ < ∞`, taken as a
  hypothesis rather than derived (see the warning below);
* `EtingofFinite_of_C2Cofinite` — the hypothesis is genuinely **weaker** than
  `C₂`-cofiniteness, which is the whole point of Arakawa–Kawasetsu;
* `finiteDimensional_poissonTraces` — `EtingofFinite W` gives a finite-dimensional trace space,
  the input to the modular differential equation.

## Main results

* `poissonSpan W : Submodule ℂ (A₂ W)` — `{A₂, A₂}`, the span of the range of the descended
  Poisson bracket; `poissonSpan_eq_map` identifies it with the image in `A₂(𝒱)` of the span of the
  representative brackets `u₍₀₎v` upstairs in `𝒱`;
* `poissonTraces W : Submodule ℂ (Module.Dual ℂ (A₂ W))` — the Poisson traces, with the membership
  criteria `mem_poissonTraces` (`φ ⁅p, q⁆ = 0`) and `mem_poissonTraces_mk` (on representatives:
  `φ [u₍₀₎v] = 0`);
* `EtingofFinite W : Prop` — the Etingof–Schedler finiteness **hypothesis**;
* `EtingofFinite_of_C2Cofinite : C2Cofinite W → EtingofFinite W`;
* `poissonTracesEquiv : poissonTraces W ≃ₗ[ℂ] Module.Dual ℂ (HP₀ W)` and the unconditional count
  `finrank_poissonTraces`;
* `finiteDimensional_poissonTraces : EtingofFinite W → FiniteDimensional ℂ (poissonTraces W)`,
  and its `C₂`-cofinite corollary `finiteDimensional_poissonTraces_of_C2Cofinite`;
* `EtingofFinite_iff_C2Cofinite_of_poissonSpan_eq_bot` and
  `not_EtingofFinite_of_poissonSpan_eq_bot` — when the descended bracket vanishes the two
  conditions coincide, which is exactly why the free boson is *not* a witness of strictness.

## ⚠ What is *assumed* and what is *proved*

`EtingofFinite` is a **deliberate axiomatization of the conclusion of an external theorem**, not a
proof of it.  Etingof–Schedler prove: a finitely generated Poisson algebra whose variety has
finitely many symplectic leaves has finite-dimensional zeroth Poisson homology
`HP₀(R) = R ⧸ {R, R}`.  Arakawa–Kawasetsu apply this to `R = A₂(𝒱)` under the quasi-lisse
assumption on the associated variety `X_𝒱`.  Formalizing symplectic leaves, associated varieties
and the D-module machinery of Etingof–Schedler is out of scope for this project, so their
*conclusion* — finite-dimensionality of `A₂(𝒱) ⧸ {A₂, A₂}` — is taken directly as the hypothesis
`EtingofFinite W`.  Nothing in this file proves Etingof–Schedler, and no statement below is
weakened and presented as their theorem: every result here is either a proof from `EtingofFinite`
as an explicit hypothesis, or a proof that `C₂`-cofiniteness implies it.

The sanity check that the axiomatization is not vacuous or inverted is
`EtingofFinite_of_C2Cofinite`: every `C₂`-cofinite VOA satisfies it, so the hypothesis is weaker
than the one in Zhu's theorem — exactly the situation Arakawa–Kawasetsu exploit.  (It is *strictly*
weaker mathematically; see the "Strictness" note at the end of the file for what is and is not
established here about that.)

## Dependencies

* `Modules.PoissonDescent` — the descended bracket `A₂bracket W : A₂ W →ₗ[ℂ] A₂ W →ₗ[ℂ] A₂ W`
  and the `LieRing (A₂ W)` instance;
* `Modularity.TraceSpace` — `bilinSpan`, `bilinTraces`, `vanishingEquiv`,
  `finiteDimensional_vanishingFunctionals_of_quot`.  Nothing proved there is restated here.

## References

* T. Arakawa, K. Kawasetsu, *Quasi-lisse vertex algebras and modular linear differential
  equations*, arXiv:1610.05865.
* P. Etingof, T. Schedler, *Poisson traces and D-modules on Poisson varieties*,
  GAFA **20** (2010) 958–987, arXiv:0908.3868.
* Gannon §5.3.2 (the Poisson algebra `A₂(𝒱)`); Zhu [574].

## Status
Proved, axiom-clean (`[propext, Classical.choice, Quot.sound]`), `pbw`-free, no `sorry`.
-/

namespace VOA

open Module (finrank)

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The span of the Poisson brackets `{A₂, A₂}` -/

/-- **The span of the brackets** `{A₂(𝒱), A₂(𝒱)}` — the `ℂ`-submodule of `A₂(𝒱)` spanned by all
values `⁅p, q⁆ = [u₍₀₎v]` of the descended Poisson bracket `A₂bracket` of
`Modules.PoissonDescent`.

This is the `bilinSpan` of `Modularity.TraceSpace` applied to `A₂bracket W`; the whole point of
that file is that the Miyamoto side (`commSpan`, spanned by commutators `ab − ba`) and this
Poisson side are the *same* construction with the bilinear map swapped. -/
noncomputable def poissonSpan (W : VertexOperatorAlgebra 𝒱) : Submodule ℂ (A₂ W) :=
  bilinSpan (A₂bracket W)

/-- `poissonSpan` unfolded: the span of the range of the descended bracket. -/
theorem poissonSpan_def (W : VertexOperatorAlgebra 𝒱) :
    poissonSpan W = Submodule.span ℂ {x : A₂ W | ∃ p q : A₂ W, x = A₂bracket W p q} := rfl

/-- Every bracket lies in `poissonSpan`. -/
theorem A₂bracket_mem_poissonSpan (W : VertexOperatorAlgebra 𝒱) (p q : A₂ W) :
    A₂bracket W p q ∈ poissonSpan W :=
  mem_bilinSpan_of _ p q

/-- Every bracket lies in `poissonSpan`, in Lie-bracket notation. -/
theorem lie_mem_poissonSpan (W : VertexOperatorAlgebra 𝒱) (p q : A₂ W) :
    ⁅p, q⁆ ∈ poissonSpan W :=
  A₂bracket_mem_poissonSpan W p q

/-- Every class of a representative bracket `u₍₀₎v` lies in `poissonSpan`. -/
theorem mk₂_poissonBracket_mem_poissonSpan (W : VertexOperatorAlgebra 𝒱) (u v : 𝒱) :
    mk₂ W (poissonBracket W u v) ∈ poissonSpan W := by
  rw [← A₂bracket_mk]
  exact A₂bracket_mem_poissonSpan W _ _

/-- **`{A₂, A₂}` is the image of the representative brackets.**  The span of the descended
brackets in `A₂(𝒱)` is the image under `mk₂ : 𝒱 ↠ A₂(𝒱)` of the span of the upstairs brackets
`u₍₀₎v` in `𝒱`.  (So the two possible definitions of "the span of the brackets" — downstairs and
downstairs-of-upstairs — agree, and the construction is well defined either way.) -/
theorem poissonSpan_eq_map (W : VertexOperatorAlgebra 𝒱) :
    poissonSpan W
      = Submodule.map (mk₂ W)
          (Submodule.span ℂ {x : 𝒱 | ∃ u v : 𝒱, x = poissonBracket W u v}) := by
  rw [poissonSpan_def, Submodule.map_span]
  congr 1
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨p, q, rfl⟩
    obtain ⟨u, rfl⟩ := mk₂_surjective W p
    obtain ⟨v, rfl⟩ := mk₂_surjective W q
    exact ⟨poissonBracket W u v, ⟨u, v, rfl⟩, (A₂bracket_mk W u v).symm⟩
  · rintro ⟨x, ⟨u, v, rfl⟩, rfl⟩
    exact ⟨mk₂ W u, mk₂ W v, (A₂bracket_mk W u v).symm⟩

/-! ## Zeroth Poisson homology and the Poisson traces -/

/-- **The zeroth Poisson homology** `HP₀(A₂ 𝒱) := A₂(𝒱) ⧸ {A₂, A₂}`.

A `ℂ`-**vector space**, not a ring: in a Poisson algebra the bracket span `{R, R}` is in general
*not* an ideal (`r·{a,b} = {a, rb} − {a,r}·b` does not close), and no ring structure on `HP₀` is
constructed or claimed here.  Finite-dimensionality of this vector space is all that
Etingof–Schedler conclude and all that Arakawa–Kawasetsu consume. -/
noncomputable abbrev HP₀ (W : VertexOperatorAlgebra 𝒱) : Type u := A₂ W ⧸ poissonSpan W

/-- **The Poisson traces** on `A₂(𝒱)`: the linear functionals `φ : A₂(𝒱) → ℂ` annihilating every
Poisson bracket, `φ ⁅p, q⁆ = 0`.  This is the Arakawa–Kawasetsu trace space, and it is the dual
`HP₀(A₂ 𝒱)*` (`poissonTracesEquiv`).

Defined as an instance of `vanishingFunctionals` from `Modularity.TraceSpace`, exactly parallel to
Miyamoto's symmetric functionals `symmetricFunctionals K A = vanishingFunctionals K A
(commSpan K A)`. -/
noncomputable def poissonTraces (W : VertexOperatorAlgebra 𝒱) :
    Submodule ℂ (Module.Dual ℂ (A₂ W)) :=
  vanishingFunctionals ℂ (A₂ W) (poissonSpan W)

/-- `poissonTraces` is the `bilinTraces` of the descended bracket. -/
theorem poissonTraces_eq_bilinTraces (W : VertexOperatorAlgebra 𝒱) :
    poissonTraces W = bilinTraces (A₂bracket W) := rfl

/-- **Membership criterion**: a functional is a Poisson trace iff it kills every bracket. -/
theorem mem_poissonTraces {W : VertexOperatorAlgebra 𝒱} {φ : Module.Dual ℂ (A₂ W)} :
    φ ∈ poissonTraces W ↔ ∀ p q : A₂ W, φ (A₂bracket W p q) = 0 :=
  mem_bilinTraces

/-- Membership criterion in Lie-bracket notation: `φ ⁅p, q⁆ = 0`. -/
theorem mem_poissonTraces_lie {W : VertexOperatorAlgebra 𝒱} {φ : Module.Dual ℂ (A₂ W)} :
    φ ∈ poissonTraces W ↔ ∀ p q : A₂ W, φ ⁅p, q⁆ = 0 :=
  mem_poissonTraces

/-- **Membership criterion on representatives**: it suffices to test against the classes of the
upstairs brackets `u₍₀₎v`, `u, v ∈ 𝒱`. -/
theorem mem_poissonTraces_mk {W : VertexOperatorAlgebra 𝒱} {φ : Module.Dual ℂ (A₂ W)} :
    φ ∈ poissonTraces W ↔ ∀ u v : 𝒱, φ (mk₂ W (poissonBracket W u v)) = 0 := by
  rw [mem_poissonTraces]
  constructor
  · intro h u v
    rw [← A₂bracket_mk]
    exact h _ _
  · intro h p q
    obtain ⟨u, rfl⟩ := mk₂_surjective W p
    obtain ⟨v, rfl⟩ := mk₂_surjective W q
    rw [A₂bracket_mk]
    exact h u v

/-- **The Poisson traces are the dual of `HP₀`.**  Immediate from the single general theorem
`vanishingEquiv` of `Modularity.TraceSpace`, with `S = {A₂, A₂}`. -/
noncomputable def poissonTracesEquiv (W : VertexOperatorAlgebra 𝒱) :
    poissonTraces W ≃ₗ[ℂ] Module.Dual ℂ (HP₀ W) :=
  vanishingEquiv (poissonSpan W)

/-- The dimension count, with **no** hypotheses: `dim (Poisson traces) = dim HP₀`. -/
theorem finrank_poissonTraces (W : VertexOperatorAlgebra 𝒱) :
    finrank ℂ (poissonTraces W) = finrank ℂ (HP₀ W) :=
  finrank_vanishingFunctionals (poissonSpan W)

/-! ## The Etingof–Schedler hypothesis -/

/-- **The Etingof–Schedler finiteness hypothesis**: the zeroth Poisson homology
`HP₀(A₂ 𝒱) = A₂(𝒱) ⧸ {A₂, A₂}` is finite-dimensional over `ℂ`.

⚠ **This is the CONCLUSION of an external theorem, taken here as a HYPOTHESIS — it is not proved
in this development.**  Etingof–Schedler (*Poisson traces and D-modules on Poisson varieties*,
GAFA **20** (2010) 958–987, arXiv:0908.3868) prove that a finitely generated Poisson algebra whose
variety has finitely many symplectic leaves has finite-dimensional `HP₀`.  Arakawa–Kawasetsu
(arXiv:1610.05865) invoke this for `R = A₂(𝒱)` when the associated variety `X_𝒱` is quasi-lisse
(finitely many symplectic leaves).  Formalizing associated varieties, symplectic leaves and the
D-module argument is deliberately out of scope: taking the conclusion as the hypothesis
`EtingofFinite W` removes *all* algebraic geometry from the Arakawa–Kawasetsu route while keeping
every downstream statement honest, since `EtingofFinite W` then appears as an explicit named
hypothesis wherever it is used.

Sanity: `EtingofFinite_of_C2Cofinite` shows this is implied by `C₂`-cofiniteness
(`C2Cofinite W`, i.e. `dim A₂(𝒱) < ∞`), so it is a *weaker* hypothesis than the one in Zhu's
theorem — which is precisely the gain Arakawa–Kawasetsu obtain. -/
def EtingofFinite (W : VertexOperatorAlgebra 𝒱) : Prop := FiniteDimensional ℂ (HP₀ W)

/-- `EtingofFinite` unfolded, for use as a typeclass assumption. -/
theorem EtingofFinite_iff (W : VertexOperatorAlgebra 𝒱) :
    EtingofFinite W ↔ FiniteDimensional ℂ (A₂ W ⧸ poissonSpan W) := Iff.rfl

/-- **`C₂`-cofinite ⟹ Etingof–Schedler finite.**  The essential sanity check: the
Arakawa–Kawasetsu hypothesis is *weaker* than Zhu's, since `HP₀(A₂ 𝒱)` is a quotient of `A₂(𝒱)`
and a quotient of a finite-dimensional space is finite-dimensional.  (Mathematically it is
strictly weaker — quasi-lisse non-`C₂`-cofinite vertex algebras exist, e.g. affine `𝒱_{k}(𝔤)` at
admissible level — but strictness is not established here; see the closing note.) -/
theorem EtingofFinite_of_C2Cofinite (W : VertexOperatorAlgebra 𝒱) (h : C2Cofinite W) :
    EtingofFinite W := by
  haveI : FiniteDimensional ℂ (A₂ W) := h
  exact Module.Finite.of_surjective (poissonSpan W).mkQ (Submodule.mkQ_surjective _)

/-- Dot-notation form of `EtingofFinite_of_C2Cofinite`. -/
theorem C2Cofinite.etingofFinite {W : VertexOperatorAlgebra 𝒱} (h : C2Cofinite W) :
    EtingofFinite W :=
  EtingofFinite_of_C2Cofinite W h

/-! ## Finite-dimensionality of the trace space -/

/-- **The Arakawa–Kawasetsu input.**  Under the Etingof–Schedler hypothesis the space of Poisson
traces on `A₂(𝒱)` is finite-dimensional.

This is where `Modularity.TraceSpace` pays off: the proof is one application of
`finiteDimensional_vanishingFunctionals_of_quot`, the *same* theorem that gives Miyamoto's
symmetric functionals their finite-dimensionality — the only difference is which submodule is
divided out.  Note that `A₂(𝒱)` itself is **not** assumed finite-dimensional. -/
theorem finiteDimensional_poissonTraces (W : VertexOperatorAlgebra 𝒱) (h : EtingofFinite W) :
    FiniteDimensional ℂ (poissonTraces W) := by
  haveI : FiniteDimensional ℂ (A₂ W ⧸ poissonSpan W) := h
  exact finiteDimensional_vanishingFunctionals_of_quot (poissonSpan W)

/-- The trace space is finite-dimensional for a `C₂`-cofinite VOA — the Zhu-theorem case,
recovered through the weaker Arakawa–Kawasetsu hypothesis. -/
theorem finiteDimensional_poissonTraces_of_C2Cofinite (W : VertexOperatorAlgebra 𝒱)
    (h : C2Cofinite W) : FiniteDimensional ℂ (poissonTraces W) :=
  finiteDimensional_poissonTraces W (EtingofFinite_of_C2Cofinite W h)

/-- The dimension of the trace space is the dimension of `HP₀`, and under the Etingof–Schedler
hypothesis both are finite. -/
theorem finrank_poissonTraces_eq (W : VertexOperatorAlgebra 𝒱) :
    finrank ℂ (poissonTraces W) = finrank ℂ (A₂ W ⧸ poissonSpan W) :=
  finrank_poissonTraces W

/-! ## When the bracket is trivial, the hypothesis is *not* weaker -/

/-- **A trivial bracket collapses the hypothesis.**  If `{A₂, A₂} = 0` — the descended Poisson
bracket vanishes identically — then `HP₀(A₂ 𝒱) ≅ A₂(𝒱)` and the Etingof–Schedler hypothesis is
*equivalent* to `C₂`-cofiniteness, so nothing is gained.

This is the honest reason the free boson is **not** a witness that `EtingofFinite` is strictly
weaker than `C2Cofinite`: for `M(1)` the bracket on `A₂(M(1)) ≅ ℂ[x]` vanishes (see the closing
note), so the two conditions coincide there and `M(1)` fails both.  (The hypothesis
`poissonSpan W = ⊥` is stated explicitly and is *not* verified for `M(1)` anywhere in this
development.) -/
theorem EtingofFinite_iff_C2Cofinite_of_poissonSpan_eq_bot (W : VertexOperatorAlgebra 𝒱)
    (h : poissonSpan W = ⊥) : EtingofFinite W ↔ C2Cofinite W := by
  have e : HP₀ W ≃ₗ[ℂ] A₂ W := Submodule.quotEquivOfEqBot (poissonSpan W) h
  constructor
  · intro hf
    haveI : FiniteDimensional ℂ (HP₀ W) := hf
    exact e.finiteDimensional
  · intro hf
    haveI : FiniteDimensional ℂ (A₂ W) := hf
    exact e.symm.finiteDimensional

/-- Corollary, in the shape a would-be counterexample has to avoid: a VOA whose descended Poisson
bracket vanishes and which is not `C₂`-cofinite also fails `EtingofFinite`. -/
theorem not_EtingofFinite_of_poissonSpan_eq_bot (W : VertexOperatorAlgebra 𝒱)
    (h : poissonSpan W = ⊥) (h₂ : ¬ C2Cofinite W) : ¬ EtingofFinite W :=
  fun hf => h₂ ((EtingofFinite_iff_C2Cofinite_of_poissonSpan_eq_bot W h).mp hf)

/-!
## Strictness of the hypothesis — what is and is not established

`EtingofFinite_of_C2Cofinite` proves one implication.  The converse fails mathematically: the
affine vertex algebras `𝒱_k(𝔤)` at admissible level are quasi-lisse (their associated variety is a
nilpotent orbit closure, with finitely many symplectic leaves) but not `C₂`-cofinite, which is the
entire content of Arakawa–Kawasetsu.  **No such witness is formalized here.**

In particular the free boson is *not* one, contrary to what its non-`C₂`-cofiniteness might
suggest.  `Examples.HeisenbergC2.heisenberg_not_C2Cofinite` shows `A₂(M(1))` is
infinite-dimensional — indeed `A₂(M(1)) ≅ ℂ[x]` with `x = [a]`.  But the descended Poisson bracket
there is *zero*: `a₍₀₎a = 0` for the free boson (`Y(a, z)a = k z⁻² 𝟙 + …` has no `z⁻¹` term — in the
repo, `Examples.HeisenbergC2.heis_smul_X0` plus `osc_zero` give `(X₀)₍₀₎u = 0` for *every* `u`), and
a bracket vanishing on the generators of the commutative algebra `A₂` vanishes identically by the
Leibniz rule `A₂_leibniz`.  Hence `{A₂, A₂} = 0`, and by
`EtingofFinite_iff_C2Cofinite_of_poissonSpan_eq_bot` the free boson fails `EtingofFinite` exactly
as it fails `C2Cofinite`: `HP₀(A₂(M(1))) ≅ A₂(M(1)) ≅ ℂ[x]` is infinite-dimensional.  This is
consistent with the geometry — the associated variety of `M(1)` is the affine line with the zero
Poisson structure, whose symplectic leaves are its points, infinitely many — and it is why the free
boson is not a quasi-lisse example.

⚠ The unproved link in that paragraph is `poissonSpan (heisenbergVOA k hk) = ⊥`.  Establishing it
formally needs the identification of `A₂(M(1))` with `ℂ[x]` as a *ring* (that the polynomial
product is the descended `₍₋₁₎`-product mod `O₂`, so that `[X₀]` generates), which is not available
in the repo; only the left-slot vanishing `(X₀)₍₀₎u = 0` is.  It was therefore deliberately not
attempted, and no statement here asserts it.
-/

end VOA
