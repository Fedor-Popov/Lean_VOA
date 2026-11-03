/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.SymmetricFunctionals

/-!
# Trace spaces: functionals that vanish on a submodule

Two different generalizations of Zhu's modularity theorem run through the *same* piece of linear
algebra, with a single operation swapped:

| theorem           | space           | quotient by             | functionals                 |
| ----------------- | --------------- | ----------------------- | --------------------------- |
| Miyamoto          | `A` associative | `[A,A] = span{ab − ba}` | symmetric `φ(ab) = φ(ba)`   |
| Arakawa–Kawasetsu | `R` Poisson     | `{R,R} = span{ {a,b} }` | Poisson trace `φ({a,b})= 0` |

In both cases the object of interest is *the linear functionals killing a designated submodule*,
and in both cases exactly one theorem is needed:

  `{φ ∈ Dual K E | S ≤ ker φ}  ≃ₗ[K]  Dual K (E ⧸ S)`.

This file proves that once, for an **arbitrary** submodule `S` of an arbitrary module `E` over an
arbitrary commutative ring `K` — no algebra structure, no bracket, no finiteness, no
semisimplicity — and then instantiates it.

## Main results

* `vanishingFunctionals K E S` — the submodule `{φ : Dual K E | S ≤ ker φ}` of the dual;
* `mem_vanishingFunctionals`, `mem_vanishingFunctionals_span` — the membership API; the second is
  the workhorse: for `S = span K s` a functional vanishes on `S` iff it kills every element of the
  generating set `s`;
* `vanishingLift` / `vanishingOfDualQuot` — the two maps (`Submodule.liftQ`, precomposition with
  `Submodule.mkQ`) and their round-trip lemmas;
* `vanishingEquiv` — **the one theorem**:
  `vanishingFunctionals K E S ≃ₗ[K] Module.Dual K (E ⧸ S)`;
* `finrank_vanishingFunctionals` — `finrank K (vanishingFunctionals K E S) = finrank K (E ⧸ S)`
  over a field, with **no** hypotheses on `E`; and the finiteness corollaries
  `finiteDimensional_vanishingFunctionals_of_quot` (sharp: only the *quotient* need be finite
  dimensional) and `finiteDimensional_vanishingFunctionals`;
* `bilinSpan b`, `bilinTraces b`, `mem_bilinTraces` — the shape both applications take: `S` is
  the span of the range of a bilinear map `b : E →ₗ[K] E →ₗ[K] E`, and `φ` kills `S` iff
  `φ (b u v) = 0` for all `u v`.  For `b` = commutator this is Miyamoto; for `b` = Poisson bracket
  on `A₂(𝒱)` this is Arakawa–Kawasetsu;
* `symmetricFunctionals_eq_vanishingFunctionals` — **the Miyamoto instance**:
  `symmetricFunctionals K A = vanishingFunctionals K A (commSpan K A)`, on the nose, as submodules
  of `Dual K A`.  With `bilinSpan_commBilin` and `symmetricFunctionals_eq_bilinTraces` this
  exhibits Miyamoto's trace space as a `bilinTraces`.

## Relation to `SemisimpleTrace.lean` and `SymmetricFunctionals.lean`

Nothing in either file is modified, and nothing proved there is restated here.

`SemisimpleTrace.lean` supplies `commSpan`, `symmetricFunctionals`, `commSpan_le_ker_of_symmetric`
and the injection `symmetricLift`; `SymmetricFunctionals.lean` upgrades `symmetricLift` to the
equivalence `symmetricFunctionalsEquivDualQuot` and deduces
`finrank_symmetricFunctionals_eq_finrank_quot_commSpan` and
`finiteDimensional_symmetricFunctionals`.  All of that is *the `S = commSpan K A` case* of the
present file.  That claim is not asserted but **proved**:

* `symmetricLift_eq_vanishingLift` — the two lifts are literally the same map (`rfl`);
* `symmetricEquivVanishing_trans_vanishingEquiv` — the two equivalences agree, i.e.
  `symmetricEquivVanishing ≪≫ₗ vanishingEquiv = symmetricFunctionalsEquivDualQuot`;
* two `example`s at the end re-derive `finrank_symmetricFunctionals_eq_finrank_quot_commSpan` and
  `finiteDimensional_symmetricFunctionals` from the general theorems, confirming agreement without
  duplicating the names.

## Honest attribution

`vanishingFunctionals K E S` is, up to unfolding, Mathlib's `Submodule.dualAnnihilator S`
(`vanishingFunctionals_eq_dualAnnihilator`), and the abstract equivalence is Mathlib's
`Submodule.dualQuotEquivDualAnnihilator` read backwards.  It is reproved here in the `liftQ`/`mkQ`
form because that — and only that — makes the repo's existing `symmetricLift` a *definitional*
special case, which is what `symmetricLift_eq_vanishingLift` records; the value added by this file
is the uniform API, the `bilinSpan` layer, and the verified Miyamoto instantiation, not the bare
existence of the isomorphism.

## Status
Proved, axiom-clean, `pbw`-free, no `sorry`.
-/

namespace VOA

open Module (finrank)

/-! ## The functionals vanishing on a submodule -/

section General

variable (K : Type*) [CommRing K] (E : Type*) [AddCommGroup E] [Module K E]

/-- The **functionals vanishing on `S`**: `{φ : Dual K E | S ≤ ker φ}`, as a submodule of the
dual.  For `S = [A,A]` these are the symmetric (trace) functionals of Miyamoto's theorem; for
`S = {R,R}` they are the Poisson traces of Arakawa–Kawasetsu. -/
def vanishingFunctionals (S : Submodule K E) : Submodule K (Module.Dual K E) where
  carrier := {φ : Module.Dual K E | S ≤ LinearMap.ker φ}
  add_mem' := fun {φ ψ} hφ hψ x hx => by
    have h₁ : φ x = 0 := LinearMap.mem_ker.mp (hφ hx)
    have h₂ : ψ x = 0 := LinearMap.mem_ker.mp (hψ hx)
    exact LinearMap.mem_ker.mpr (by rw [LinearMap.add_apply, h₁, h₂, add_zero])
  zero_mem' := fun x _ => LinearMap.mem_ker.mpr rfl
  smul_mem' := fun c φ hφ x hx => by
    have h : φ x = 0 := LinearMap.mem_ker.mp (hφ hx)
    exact LinearMap.mem_ker.mpr (by rw [LinearMap.smul_apply, h, smul_zero])

variable {K E}

@[simp] theorem mem_vanishingFunctionals {S : Submodule K E} {φ : Module.Dual K E} :
    φ ∈ vanishingFunctionals K E S ↔ S ≤ LinearMap.ker φ := Iff.rfl

/-- `vanishingFunctionals` is Mathlib's `Submodule.dualAnnihilator`, spelled in the `S ≤ ker φ`
form that the applications produce. -/
theorem vanishingFunctionals_eq_dualAnnihilator (S : Submodule K E) :
    vanishingFunctionals K E S = S.dualAnnihilator := by
  ext φ
  rw [mem_vanishingFunctionals, Submodule.mem_dualAnnihilator]
  exact ⟨fun h x hx => LinearMap.mem_ker.mp (h hx),
    fun h x hx => LinearMap.mem_ker.mpr (h x hx)⟩

/-- **The workhorse membership criterion.**  A functional vanishes on `span K s` exactly when it
kills every generator.  Both instantiations enter through this lemma, since both designated
submodules are spans. -/
theorem mem_vanishingFunctionals_span {s : Set E} {φ : Module.Dual K E} :
    φ ∈ vanishingFunctionals K E (Submodule.span K s) ↔ ∀ x ∈ s, φ x = 0 := by
  rw [mem_vanishingFunctionals, Submodule.span_le]
  exact ⟨fun h x hx => LinearMap.mem_ker.mp (h hx),
    fun h x hx => LinearMap.mem_ker.mpr (h x hx)⟩

/-! ## The equivalence with the dual of the quotient -/

/-- The forward map: a functional killing `S` descends to the quotient `E ⧸ S`.  This is
`Submodule.liftQ`, packaged as a linear map in the functional. -/
noncomputable def vanishingLift (S : Submodule K E) :
    vanishingFunctionals K E S →ₗ[K] Module.Dual K (E ⧸ S) where
  toFun φ := S.liftQ (φ : Module.Dual K E) (mem_vanishingFunctionals.mp φ.2)
  map_add' φ ψ := by
    refine LinearMap.ext fun q => ?_
    obtain ⟨x, rfl⟩ := S.mkQ_surjective q
    rfl
  map_smul' c φ := by
    refine LinearMap.ext fun q => ?_
    obtain ⟨x, rfl⟩ := S.mkQ_surjective q
    rfl

@[simp] theorem vanishingLift_apply_mk (S : Submodule K E) (φ : vanishingFunctionals K E S)
    (x : E) : vanishingLift S φ (S.mkQ x) = (φ : Module.Dual K E) x := rfl

/-- Precomposing a functional on `E ⧸ S` with the projection `E ↠ E ⧸ S` produces a functional
that vanishes on `S`. -/
theorem mem_vanishingFunctionals_comp_mkQ (S : Submodule K E)
    (ψ : Module.Dual K (E ⧸ S)) : (ψ ∘ₗ S.mkQ) ∈ vanishingFunctionals K E S := by
  rw [mem_vanishingFunctionals]
  intro x hx
  refine LinearMap.mem_ker.mpr ?_
  rw [LinearMap.comp_apply, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero S).2 hx,
    map_zero]

/-- The inverse map: precomposition with `Submodule.mkQ`. -/
noncomputable def vanishingOfDualQuot (S : Submodule K E) :
    Module.Dual K (E ⧸ S) →ₗ[K] vanishingFunctionals K E S where
  toFun ψ := ⟨ψ ∘ₗ S.mkQ, mem_vanishingFunctionals_comp_mkQ S ψ⟩
  map_add' _ _ := Subtype.ext (LinearMap.ext fun _ => rfl)
  map_smul' _ _ := Subtype.ext (LinearMap.ext fun _ => rfl)

@[simp] theorem vanishingOfDualQuot_apply_apply (S : Submodule K E)
    (ψ : Module.Dual K (E ⧸ S)) (x : E) :
    ((vanishingOfDualQuot S ψ : vanishingFunctionals K E S) : Module.Dual K E) x
      = ψ (S.mkQ x) := rfl

/-- `vanishingOfDualQuot` is a right inverse of `vanishingLift`. -/
theorem vanishingLift_vanishingOfDualQuot (S : Submodule K E) (ψ : Module.Dual K (E ⧸ S)) :
    vanishingLift S (vanishingOfDualQuot S ψ) = ψ := by
  refine LinearMap.ext fun q => ?_
  obtain ⟨x, rfl⟩ := S.mkQ_surjective q
  rfl

/-- `vanishingOfDualQuot` is a left inverse of `vanishingLift`. -/
theorem vanishingOfDualQuot_vanishingLift (S : Submodule K E)
    (φ : vanishingFunctionals K E S) : vanishingOfDualQuot S (vanishingLift S φ) = φ :=
  Subtype.ext (LinearMap.ext fun _ => rfl)

/-- **The one theorem.**  For an arbitrary submodule `S` of an arbitrary `K`-module `E`, the
functionals vanishing on `S` are canonically the full dual of the quotient:

`vanishingFunctionals K E S ≃ₗ[K] Module.Dual K (E ⧸ S)`.

No algebra structure on `E`, no bracket, no finiteness, no semisimplicity, no field.  Miyamoto's
symmetric functionals (`S = commSpan K A`) and Arakawa–Kawasetsu's Poisson traces
(`S = bilinSpan` of the bracket) are the two instances the modularity theorems consume. -/
noncomputable def vanishingEquiv (S : Submodule K E) :
    vanishingFunctionals K E S ≃ₗ[K] Module.Dual K (E ⧸ S) :=
  { vanishingLift S with
    invFun := vanishingOfDualQuot S
    left_inv := vanishingOfDualQuot_vanishingLift S
    right_inv := vanishingLift_vanishingOfDualQuot S }

@[simp] theorem vanishingEquiv_apply (S : Submodule K E) (φ : vanishingFunctionals K E S) :
    vanishingEquiv S φ = vanishingLift S φ := rfl

theorem vanishingEquiv_symm_apply (S : Submodule K E) (ψ : Module.Dual K (E ⧸ S)) :
    (vanishingEquiv S).symm ψ = vanishingOfDualQuot S ψ := rfl

/-! ## Spans of bilinear ranges

Both applications produce `S` as the span of the range of a bilinear map: the commutator
`(a,b) ↦ ab − ba` for Miyamoto, the Poisson bracket `(a,b) ↦ {a,b}` for Arakawa–Kawasetsu.  This
section gives that situation a name and the one lemma it needs. -/

/-- The submodule spanned by the range of a bilinear map `b : E →ₗ[K] E →ₗ[K] E`. -/
def bilinSpan (b : E →ₗ[K] E →ₗ[K] E) : Submodule K E :=
  Submodule.span K {x : E | ∃ u v : E, x = b u v}

theorem mem_bilinSpan_of (b : E →ₗ[K] E →ₗ[K] E) (u v : E) : b u v ∈ bilinSpan b :=
  Submodule.subset_span ⟨u, v, rfl⟩

/-- The **`b`-traces**: functionals killing every value of the bilinear map `b`. -/
noncomputable abbrev bilinTraces (b : E →ₗ[K] E →ₗ[K] E) : Submodule K (Module.Dual K E) :=
  vanishingFunctionals K E (bilinSpan b)

/-- A functional vanishes on `bilinSpan b` **iff** it kills every `b u v`.  This is the lemma
both instantiations go through: with `b` the commutator it says `φ(ab) = φ(ba)`, with `b` the
Poisson bracket it says `φ({u,v}) = 0`. -/
theorem mem_bilinTraces {b : E →ₗ[K] E →ₗ[K] E} {φ : Module.Dual K E} :
    φ ∈ bilinTraces b ↔ ∀ u v : E, φ (b u v) = 0 := by
  rw [bilinTraces, bilinSpan, mem_vanishingFunctionals_span]
  constructor
  · intro h u v; exact h _ ⟨u, v, rfl⟩
  · rintro h _ ⟨u, v, rfl⟩; exact h u v

/-- The equivalence, in the bilinear-span form the two modularity theorems use:
`{φ | ∀ u v, φ (b u v) = 0} ≃ₗ[K] Dual K (E ⧸ bilinSpan b)`. -/
noncomputable def bilinTracesEquiv (b : E →ₗ[K] E →ₗ[K] E) :
    bilinTraces b ≃ₗ[K] Module.Dual K (E ⧸ bilinSpan b) :=
  vanishingEquiv (bilinSpan b)

end General

/-! ## Dimension and finite-dimensionality

Over a field the equivalence turns into a dimension count, and — this is the point of the whole
construction — it needs **no structure on `E` beyond being a module**. -/

section Dimension

variable {K : Type*} [Field K] {E : Type*} [AddCommGroup E] [Module K E]

/-- `dim {φ | S ≤ ker φ} = dim (E ⧸ S)`.

There are no hypotheses: `Subspace.dual_finrank_eq` is unconditional (both sides are `0` in the
infinite-dimensional case).  In particular no algebra structure, no semisimplicity and no
Poisson bracket appear anywhere — *that generality is the deliverable*. -/
theorem finrank_vanishingFunctionals (S : Submodule K E) :
    finrank K (vanishingFunctionals K E S) = finrank K (E ⧸ S) := by
  rw [(vanishingEquiv S).finrank_eq, Subspace.dual_finrank_eq]

/-- The sharp finiteness statement: the vanishing functionals are finite-dimensional as soon as
the **quotient** `E ⧸ S` is, even when `E` itself is infinite-dimensional.

This is the form Arakawa–Kawasetsu needs.  There `E = A₂(𝒱)` is a Poisson algebra, `S = {E,E}`,
and finite-dimensionality of `E ⧸ S = HP₀(E)` is exactly the Etingof–Schedler conclusion
(finitely many symplectic leaves ⟹ `HP₀` finite dimensional) taken as a hypothesis. -/
theorem finiteDimensional_vanishingFunctionals_of_quot (S : Submodule K E)
    [FiniteDimensional K (E ⧸ S)] : FiniteDimensional K (vanishingFunctionals K E S) :=
  (vanishingEquiv S).symm.finiteDimensional

/-- If `E` is finite-dimensional then so is the space of functionals vanishing on `S`, for every
`S`.  (In this form it is also immediate from typeclass inference — `vanishingFunctionals` is a
submodule of the finite-dimensional space `Dual K E`.  The content is the sharper
`finiteDimensional_vanishingFunctionals_of_quot` above.) -/
theorem finiteDimensional_vanishingFunctionals (S : Submodule K E) [FiniteDimensional K E] :
    FiniteDimensional K (vanishingFunctionals K E S) :=
  finiteDimensional_vanishingFunctionals_of_quot S

/-- The bilinear-span form of the dimension count: `dim {φ | ∀ u v, φ (b u v) = 0}
= dim (E ⧸ bilinSpan b)`. -/
theorem finrank_bilinTraces (b : E →ₗ[K] E →ₗ[K] E) :
    finrank K (bilinTraces b) = finrank K (E ⧸ bilinSpan b) :=
  finrank_vanishingFunctionals _

/-- The bilinear-span form of the finiteness statement — the shape in which Arakawa–Kawasetsu
consumes Etingof–Schedler: if the quotient of `E` by the span of the brackets is
finite-dimensional, so is the space of traces. -/
theorem finiteDimensional_bilinTraces_of_quot (b : E →ₗ[K] E →ₗ[K] E)
    [FiniteDimensional K (E ⧸ bilinSpan b)] : FiniteDimensional K (bilinTraces b) :=
  finiteDimensional_vanishingFunctionals_of_quot _

end Dimension

/-! ## The Miyamoto instance

`symmetricFunctionals K A` — defined in `SemisimpleTrace.lean` by the condition
`φ (a * b) = φ (b * a)` — **is** `vanishingFunctionals K A (commSpan K A)`, on the nose. -/

section Miyamoto

variable {K : Type*} [Field K] {A : Type*} [Ring A] [Algebra K A]

/-- The commutator, as a `K`-bilinear map `A →ₗ[K] A →ₗ[K] A`. -/
noncomputable def commBilin (K : Type*) [Field K] (A : Type*) [Ring A] [Algebra K A] :
    A →ₗ[K] A →ₗ[K] A :=
  LinearMap.mul K A - (LinearMap.mul K A).flip

@[simp] theorem commBilin_apply (a b : A) : commBilin K A a b = a * b - b * a := by
  simp [commBilin]

theorem commBilin_range_eq :
    {x : A | ∃ u v : A, x = commBilin K A u v} = {x : A | ∃ a b : A, x = a * b - b * a} := by
  ext x
  simp only [Set.mem_setOf_eq, commBilin_apply]

/-- The commutator subspace `[A,A]` of `SemisimpleTrace.lean` is the `bilinSpan` of the
commutator bilinear map — so Miyamoto's designated submodule really is an instance of the general
construction. -/
theorem bilinSpan_commBilin : bilinSpan (commBilin K A) = commSpan K A :=
  congrArg (Submodule.span K) commBilin_range_eq

/-- **The Miyamoto instance.**  The symmetric functionals `φ(ab) = φ(ba)` are exactly the
functionals vanishing on the commutator subspace:

`symmetricFunctionals K A = vanishingFunctionals K A (commSpan K A)`.

The `⊆` direction is `commSpan_le_ker_of_symmetric` from `SemisimpleTrace.lean`; the `⊇`
direction is `φ (ab − ba) = 0 ⟹ φ(ab) = φ(ba)`. -/
theorem symmetricFunctionals_eq_vanishingFunctionals :
    symmetricFunctionals K A = vanishingFunctionals K A (commSpan K A) := by
  ext φ
  rw [mem_symmetricFunctionals, mem_vanishingFunctionals]
  constructor
  · intro hφ
    exact commSpan_le_ker_of_symmetric (mem_symmetricFunctionals.mpr hφ)
  · intro h a b
    have hz : φ (a * b - b * a) = 0 :=
      LinearMap.mem_ker.mp (h (mul_sub_mul_mem_commSpan a b))
    rw [map_sub, sub_eq_zero] at hz
    exact hz

/-- Miyamoto's trace space displayed as a `bilinTraces`, the same shape the Poisson side takes. -/
theorem symmetricFunctionals_eq_bilinTraces :
    symmetricFunctionals K A = bilinTraces (commBilin K A) := by
  rw [symmetricFunctionals_eq_vanishingFunctionals, bilinTraces, bilinSpan_commBilin]

/-- The identification of the two carriers, as a linear equivalence. -/
noncomputable def symmetricEquivVanishing :
    symmetricFunctionals K A ≃ₗ[K] vanishingFunctionals K A (commSpan K A) :=
  LinearEquiv.ofEq _ _ symmetricFunctionals_eq_vanishingFunctionals

/-! ### Agreement with `SymmetricFunctionals.lean`

Nothing below restates a result of `SymmetricFunctionals.lean`; each item *checks* that the
general construction specializes to it. -/

/-- The general lift **is** the repo's `symmetricLift` — the same `Submodule.liftQ`, so `rfl`. -/
theorem symmetricLift_eq_vanishingLift (φ : symmetricFunctionals K A)
    (hφ : (φ : A →ₗ[K] K) ∈ vanishingFunctionals K A (commSpan K A)) :
    vanishingLift (commSpan K A) ⟨(φ : A →ₗ[K] K), hφ⟩ = symmetricLift φ := rfl

/-- The general equivalence specializes to `symmetricFunctionalsEquivDualQuot`: transporting
along the identification of carriers and then applying `vanishingEquiv` gives exactly the map
proved in `SymmetricFunctionals.lean`. -/
theorem symmetricEquivVanishing_trans_vanishingEquiv :
    (symmetricEquivVanishing (K := K) (A := A)).trans (vanishingEquiv (commSpan K A))
      = symmetricFunctionalsEquivDualQuot := by
  refine LinearEquiv.ext fun φ => LinearMap.ext fun q => ?_
  obtain ⟨x, rfl⟩ := (commSpan K A).mkQ_surjective q
  rfl

/-- Confirmation that the general dimension count reproduces
`finrank_symmetricFunctionals_eq_finrank_quot_commSpan`. -/
example : finrank K (symmetricFunctionals K A) = finrank K (A ⧸ commSpan K A) :=
  (symmetricEquivVanishing (K := K) (A := A)).finrank_eq.trans
    (finrank_vanishingFunctionals (commSpan K A))

/-- Confirmation that the general finiteness result reproduces
`finiteDimensional_symmetricFunctionals`. -/
example [FiniteDimensional K A] : FiniteDimensional K (symmetricFunctionals K A) :=
  (symmetricEquivVanishing (K := K) (A := A)).symm.finiteDimensional

end Miyamoto

end VOA
