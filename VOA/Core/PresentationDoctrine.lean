/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Core.VAPresentation
import VOA.Core.QuotientVOA
import VOA.Core.InvariantFormRadical
import VOA.Core.SimpleImage

/-!
# The presentation doctrine: nullity certificates, THE VOA, uniqueness

The doctrine: **vertex algebras are introduced by generators and
OPEs; THE vertex algebra of a presentation is the simple quotient of the presented
object.**  This file states the doctrine's hooks over the `NPExtension` interface layer, proving
what is honestly provable and leaving the rest as `def : Prop` statements or structures with
named hypotheses.

## What is defined and what is proved

* `evTR` — the **evaluation of `T(R)` in any VOA** along an assignment `g : ι → 𝒱`:
  a letter `(i,k)` goes to `Tᵏ(g i)/k!` (with `T = L₋₁`) and a word to the iterated
  `(−1)`-modes of its letters applied to the vacuum — the direct generalization of
  `psiVir`/`PhiVir` (`Examples.NonlinearVirasoroTransport`), **definition only**: the
  intertwining theorems U1–U3 (`MRfull ≤ ker evTR` etc.) are not formalised, and nothing
  here claims them.
* `NullCertificate` — a listed relation is *null* for an invariant form: its evaluation
  pairs to zero against everything.  The provable hook `mem_maxGradedIdeal_of_null`
  wires it to Li's theorem (`LiRadical.leftRadical_eq_maxGradedIdeal`,
  `Core.InvariantFormRadical`): a null relation's evaluation lies in the maximal proper
  graded ideal.
* `RelIdealNull` — the statement shape "the whole relation ideal evaluates into the
  maximal graded ideal", a `def : Prop` whose discharge (through U1–U3 and the model's
  `hRel`) is not formalised.  Its honestly-provable fragment `relIdealNull_of_isIdeal` — given
  that the image is an ideal avoiding the vacuum — is proved, via
  `QuotVOA.le_maxGradedIdeal` and `QuotVOA.isGradedIdeal_of_isIdeal`.  The equivalence
  `relIdealNull_iff_forms_vanish` restates it through Li's theorem.
* `TheVOA` — **the definitional convention**: THE vertex algebra of a presentation is
  `maxQuotientVOA` of the presented object — the quotient by the maximal proper graded
  ideal, no explicit maximal ideal required.  ⚠ Parametrized over a
  `VertexOperatorAlgebra` structure on `UPres`, which the library does **not** construct
  (it would come from `GenFields` + conformal data).
* `RealizesPresentation` — the data of a realization of a presentation in a VOA:
  homogeneous generator images, the OPE list (`hOPE`), the null relations (`hRel`), and
  spanning.  Closure hypotheses of the `SmulClosedWp`/`AMOmegaIdentity` kind (triplet
  algebras) take this form, exactly and without discount, as finite lists.
* `simple_realization_unique` — ⚠ **an honest `def : Prop`, stated and NOT proved**:
  any two simple realizations of one presentation are isomorphic.  The intended proof
  route is the universal property + `Core.SimpleImage` transfer +
  `InvariantForm.invariantForm_nondegenerate`; nothing in the library depends on it.

## Honesty

Nothing in this file — or anywhere in the presentation layer — consumes Jacobi
certificates: the certificate layer (`Jac`, `JacobiModRel`) is not even well-formed
without an `NPExtension` instance, which the library does not construct, and the theorems above are
independent of it.  No docstring here may be read as claiming otherwise.

No `sorry`, no `admit`, no `native_decide`, no new axiom; `VOA.pbw` is not used.
-/

namespace VOA.NonlinearConformal

open Module (End)
open NPExtension
open VOA.VertexOperatorAlgebra

set_option maxRecDepth 4000

universe u v

variable {ι : Type u}

/-! ## §1  Evaluation of `T(R)` in a vertex operator algebra -/

section Evaluation

variable {𝒱 : Type v} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- The image of the basis letter `(i,k)` under an assignment `g`: the divided power
`Tᵏ(g i)/k!`, with `T = L₋₁` of the target VOA. -/
noncomputable def evLetter (W : VertexOperatorAlgebra 𝒱) (g : ι → 𝒱) (p : GenIdx ι) : 𝒱 :=
  ((p.2.factorial : ℂ))⁻¹ • ((W.L (-1)) ^ p.2) (g p.1)

/-- The image of a word: iterated `(−1)`-modes of the letters, applied to the vacuum. -/
noncomputable def evWord (W : VertexOperatorAlgebra 𝒱) (g : ι → 𝒱) : List (GenIdx ι) → 𝒱
  | [] => W.vacuum
  | p :: l => W.smul (evLetter W g p) (-1) (evWord W g l)

/-- **The evaluation of `T(R)` in a VOA** along `g : ι → 𝒱` — `Module.Basis.constr`
on the word basis.  Definition only: the U1–U3 intertwining theorems are not formalised. -/
noncomputable def evTR (W : VertexOperatorAlgebra 𝒱) (g : ι → 𝒱) : TR ι →ₗ[ℂ] 𝒱 :=
  (wbasis ι).constr ℂ (fun w => evWord W g (FreeMonoid.toList w))

theorem evTR_wbasis (W : VertexOperatorAlgebra 𝒱) (g : ι → 𝒱) (w : FreeMonoid (GenIdx ι)) :
    evTR W g (wbasis ι w) = evWord W g (FreeMonoid.toList w) :=
  Module.Basis.constr_basis (wbasis ι) ℂ _ w

/-- The unit word evaluates to the vacuum. -/
theorem evTR_one (W : VertexOperatorAlgebra 𝒱) (g : ι → 𝒱) :
    evTR W g (1 : TR ι) = W.vacuum := by
  rw [← wbasis_one, evTR_wbasis]
  rfl

/-- A single letter evaluates to its divided power: `u₍₋₁₎𝟙 = u`. -/
theorem evTR_gv (W : VertexOperatorAlgebra 𝒱) (g : ι → 𝒱) (p : GenIdx ι) :
    evTR W g (gv p) = evLetter W g p := by
  rw [gv, evTR_wbasis]
  change W.smul (evLetter W g p) (-1) W.vacuum = evLetter W g p
  exact PreVertexAlgebra.smul_vacuum_neg_one _ _

/-- A bottom letter evaluates to the assigned generator itself. -/
theorem evTR_bot (W : VertexOperatorAlgebra 𝒱) (g : ι → 𝒱) (i : ι) :
    evTR W g (gv (i, 0)) = g i := by
  rw [evTR_gv, evLetter]
  simp

end Evaluation

/-! ## §2  Nullity certificates, wired to Li's theorem -/

section Nullity

variable {𝒱 : Type v} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- **A nullity certificate** for a listed relation `r`: its evaluation pairs to zero
against every state, for a given invariant form.  This is the finite, computable
non-vacuity check of the doctrine: nullity is a statement about pairings computed from
the OPE data. -/
def NullCertificate (P : VAPresentation ι) (W : VertexOperatorAlgebra 𝒱)
    (B : InvariantForm W) (g : ι → 𝒱) (r : P.relIdx) : Prop :=
  ∀ v : 𝒱, B.form (evTR W g (P.relVal r)) v = 0

/-- **The provable hook**: a null relation's evaluation lies in the maximal proper
graded ideal — Li's theorem (`leftRadical_eq_maxGradedIdeal`) applied to the
certificate.  This is the door through which any discharge of `RelIdealNull`
passes. -/
theorem mem_maxGradedIdeal_of_null {P : VAPresentation ι} {W : VertexOperatorAlgebra 𝒱}
    {B : InvariantForm W} {g : ι → 𝒱} {r : P.relIdx}
    (hB : B.IsFullyInvariant) (hn : B.Normalized)
    (hnull : NullCertificate P W B g r) :
    evTR W g (P.relVal r) ∈ QuotVOA.maxGradedIdeal W := by
  rw [← LiRadical.leftRadical_eq_maxGradedIdeal hB hn, InvariantForm.mem_leftRadical]
  exact LinearMap.ext hnull

/-- **The statement shape** "the whole relation ideal is null": its image under the
evaluation lies in the maximal proper graded ideal.  A `def : Prop`; its discharge from
`hRel` plus the U1–U3 intertwining is not formalised, and nothing in the library claims it. -/
def RelIdealNull (P : VAPresentation ι) (NP : NPExtension P.toOPEData)
    (W : VertexOperatorAlgebra 𝒱) (g : ι → 𝒱) : Prop :=
  Submodule.map (evTR W g) (RelIdeal P NP) ≤ QuotVOA.maxGradedIdeal W

/-- The honestly-provable fragment of `RelIdealNull`: **given** that the image of the
relation ideal is a VOA ideal avoiding the vacuum (the `IsIdeal` binder is the unformalised
content), it lies in the maximal proper graded ideal — gradedness is automatic
(`isGradedIdeal_of_isIdeal`). -/
theorem relIdealNull_of_isIdeal {P : VAPresentation ι} {NP : NPExtension P.toOPEData}
    {W : VertexOperatorAlgebra 𝒱} {g : ι → 𝒱}
    (hI : W.IsIdeal (Submodule.map (evTR W g) (RelIdeal P NP)))
    (hv : W.vacuum ∉ Submodule.map (evTR W g) (RelIdeal P NP)) :
    RelIdealNull P NP W g :=
  QuotVOA.le_maxGradedIdeal ⟨hI, QuotVOA.isGradedIdeal_of_isIdeal hI, hv⟩

/-- `RelIdealNull` through Li's theorem: it says exactly that every element of the
relation ideal evaluates to a state that pairs to zero against everything. -/
theorem relIdealNull_iff_forms_vanish {P : VAPresentation ι}
    {NP : NPExtension P.toOPEData} {W : VertexOperatorAlgebra 𝒱} {g : ι → 𝒱}
    {B : InvariantForm W} (hB : B.IsFullyInvariant) (hn : B.Normalized) :
    RelIdealNull P NP W g ↔
      ∀ x : TR ι, InRelIdeal P NP x → ∀ v : 𝒱, B.form (evTR W g x) v = 0 := by
  constructor
  · intro h x hx v
    have hm := h (Submodule.mem_map_of_mem (p := RelIdeal P NP) hx)
    rw [LiRadical.mem_maxGradedIdeal_iff hB hn] at hm
    exact hm v
  · intro h y hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [LiRadical.mem_maxGradedIdeal_iff hB hn]
    exact h x hx

end Nullity

/-! ## §3  THE vertex algebra of a presentation -/

/-- **The definitional convention** (doctrine, 2026-08): THE vertex algebra of a
presentation is the **simple quotient** of the presented object — `maxQuotientVOA`, the
quotient by the maximal proper graded ideal.  No explicit maximal ideal is ever
required: `maxGradedIdeal` is the supremum of all proper graded ideals.

⚠ Parametrized over a `VertexOperatorAlgebra` structure `W` on `UPres P NP`, which
the library does **not** construct — it would come from the `GenFields` contract and
conformal data.  Simplicity of the result is itself conditional
(`QuotVOA.isSimple_maxQuotientVOA`); nothing here claims it unconditionally. -/
noncomputable def TheVOA (P : VAPresentation ι) (NP : NPExtension P.toOPEData)
    (W : VertexOperatorAlgebra (UPres P NP)) :
    VertexOperatorAlgebra (UPres P NP ⧸ QuotVOA.maxGradedIdeal W) :=
  QuotVOA.maxQuotientVOA W

/-! ## §4  Realizations, and the uniqueness statement -/

section Realization

variable {𝒱 : Type v} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- **A realization of a presentation in a VOA** — minimal, data-only: homogeneous
images of the generators, the OPE list satisfied through the evaluation (`hOPE`), the
listed relations null (`hRel`), and the word states spanning.  This is where the
`SmulClosedWp`-style closure hypotheses (triplet algebras) appear as
finite explicit lists; the structure itself proves nothing. -/
structure RealizesPresentation (P : VAPresentation ι) (W : VertexOperatorAlgebra 𝒱) where
  /-- the images of the strong generators -/
  gen : ι → 𝒱
  /-- each image is homogeneous of the declared weight -/
  gen_homog : ∀ i, gen i ∈ W.grading (P.wt i : ℤ)
  /-- the model satisfies the OPE list -/
  hOPE : ∀ i j (n : ℕ), W.smul (gen i) (n : ℤ) (gen j) = evTR W gen (P.ope i j n)
  /-- the listed relations vanish in the model -/
  hRel : ∀ r, evTR W gen (P.relVal r) = 0
  /-- the word states span the model -/
  spanning : Submodule.span ℂ
    (Set.range fun w : FreeMonoid (GenIdx ι) => evTR W gen (wbasis ι w)) = ⊤

end Realization

/-- ⚠⚠ **STATED, NOT PROVED — an honest `def : Prop`.**  Any two simple VOAs realizing
the same presentation (same generators, same OPE list, same null relations, both
spanned by their word states) are isomorphic as VOAs.

Intended proof route (not carried out): the universal property of the
presented object gives mode-intertwining surjections onto both realizations (U1–U3,
not formalised); `Core.SimpleImage` identifies each simple image with the quotient by
`maxGradedIdeal`; and `InvariantForm.invariantForm_nondegenerate` controls the kernel.
Roitman's presentation of lattice vertex algebras (J. Algebra 255 (2002) 297–323) is
the published pattern for exactly this argument.  **Do not cite this statement as a
theorem**; nothing in the library depends on it. -/
def simple_realization_unique : Prop :=
  ∀ {κ : Type u} (P : VAPresentation κ) {𝒱₁ 𝒱₂ : Type v}
    [AddCommGroup 𝒱₁] [Module ℂ 𝒱₁] [AddCommGroup 𝒱₂] [Module ℂ 𝒱₂]
    (W₁ : VertexOperatorAlgebra 𝒱₁) (W₂ : VertexOperatorAlgebra 𝒱₂),
    RealizesPresentation P W₁ → RealizesPresentation P W₂ →
    W₁.IsSimple → W₂.IsSimple →
    ∃ e : 𝒱₁ ≃ₗ[ℂ] 𝒱₂,
      e W₁.vacuum = W₂.vacuum ∧
      ∀ (u v : 𝒱₁) (n : ℤ), e (W₁.smul u n v) = W₂.smul (e u) n (e v)

end VOA.NonlinearConformal
