/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli
-/
import VOA.Modules.RationalityLattice
import VOA.Modules.Contragredient
import VOA.Core.InvariantFormFHL2
import VOA.Core.InvariantFormRadical
import VOA.Core.SimpleImage

/-!
# `StronglyFinite` and `StronglyRational`

The two literature bundles that sit on top of the rationality lattice of
`Modules/RationalityLattice.lean`.  Both are transcribed from primary sources — each conjunct
checked against the paper, section by section — and both are **satisfiable**
(`Examples/TrivialStronglyRational.lean`).

## The literature, verified against the papers

* **"strongly-finite"** originates with **Creutzig–Gannon**, *Logarithmic conformal field theory,
  log-modular tensor categories and modular forms*, J. Phys. A **50** (2017) no. 40, 404004 =
  arXiv:1605.04630v1, **§2.2 "VOA basics"** — an unnumbered in-text convention, not a numbered
  definition.  Their four conjuncts: **simple**, **`C₂`-cofinite**, **of CFT type**, and
  **`V ≅ V∨`**.  Their CFT type, fixed two sentences earlier in the same subsection, is the
  three-part condition `V = ⊕_{n≥0} V(n)`, `V(0) = ℂ1`, `dim V(n) < ∞`.  In the next sentence they
  define **strongly-rational** as strongly-finite plus **regular**.
* **"strongly rational"** originates with **Dong–Mason**, *Rational vertex operator algebras and
  the effective central charge*, arXiv:math/0201318v1, **§3**, where the term is explicitly
  introduced with three conjuncts: **of strong CFT type**, **`C₂`-cofinite**, **rational**.  Their
  "strong CFT type" is defined in **§2**: of CFT type (no negative weights, `dim V₀ = 1`) *plus*
  `L(1)V₁ = 0`.  Their §2 also records the equivalence used throughout this file: for `V` of CFT
  type, strong CFT type holds **precisely when** `V` is self-dual, i.e. `V′ ≅ V`.
* **McRae**, *On rationality for `C₂`-cofinite vertex operator algebras*, arXiv:2108.01898v3,
  **§2.2** (also unnumbered, in-text) gives the modern four-clause form of **strongly rational**:
  (1) positive energy / CFT type — `V(n) = 0` for `n < 0` and `V(0) = ℂ1`; (2) self-contragredient
  — `V ≅ V′` as `V`-modules, *equivalently* the existence of a nondegenerate invariant bilinear
  form `V × V → ℂ`; (3) `C₂`-cofinite; (4) rational.  He then attributes **strongly finite** to
  Creutzig–Gannon (his `[CG]` is the paper above) as "strongly rational minus rationality", and
  adopts for his own use a **weakened** variant — `ℕ`-graded (instead of CFT type), simple,
  self-contragredient, `C₂`-cofinite — because he needs to relax positive energy.

⚠ **Four corrections to the naive recollection, each following the literature:**

1. **Simplicity is a conjunct of "strongly finite", but is *derivable* in McRae's "strongly
   rational".**  McRae §2.2 lists only the four clauses above and then derives simplicity from
   (1)+(2): a proper ideal meets the generating subspace `V(0) = ℂ1` trivially, hence (by the
   classification of invariant bilinear forms, H. Li, J. Pure Appl. Algebra **96** (1994) 279–297,
   Thm. 3.1) lies in the radical of every invariant form — and self-contragredience supplies a
   nondegenerate one, so the ideal is `0`.  His own "strongly finite" keeps simplicity as a
   conjunct precisely because he weakens CFT type to `ℕ`-graded, which breaks that derivation.
   This repository keeps simplicity as an explicit conjunct (Creutzig–Gannon's form), because Li
   Thm. 3.1 is not formalized here — see §3.
2. **Creutzig–Gannon's "strongly-rational" adds `regular`, not `rational`.**  Dong–Mason's and
   McRae's add rationality.  `StronglyRational` below follows Dong–Mason/McRae and is built over
   `AdmissiblyRational` (the library's transcription of the standard Zhu/DLM notion; see the
   ⚠ on the `rational` field); `Regular` is strictly stronger
   (`Modules/RationalityLattice.lean`), so the Creutzig–Gannon variant is *implied* by, not equal
   to, the one defined here.  `stronglyRational_of_regular` records the Creutzig–Gannon route and
   `StronglyRational.regular_of_abd` the converse under the Abe–Buhl–Dong predicate, which is
   a theorem, so the converse is unconditional: `StronglyRational.regular`
   (`Classification/COne/LiteratureInputsProved.lean`).
3. **Dong–Mason's clause 1 is "strong CFT type", not "CFT type".**  It silently *contains* the
   self-duality clause that McRae and Creutzig–Gannon list separately, by the §2 equivalence
   quoted above.  That equivalence is **proved here**, in the invariant-form formulation, as
   `selfDual_iff` — it is not imported as a citation.
4. **McRae's rationality clause is formally stronger than `AdmissiblyRational`.**  His (4) demands
   that the summands be *grading-restricted* (ordinary); Dong–Mason's demands only irreducible
   *admissible* summands, which is what `AdmissiblyRational` says.  The gap is exactly DLM
   Thm. 8.1(c), carried here as the named predicate `DLMSimpleAdmissibleOrdinary`; it is proved
   for every `C₂`-cofinite VOA, hence for every `StronglyRational` one
   (`AdmissibleOrdinary.dlmSimpleAdmissibleOrdinary_of_stronglyRational`).

## §1 ⚠ `SelfContragredient` (`Modules/Contragredient.lean`) is VACUOUS — do not use it

`Modules/Contragredient.lean` defines `SelfContragredient N := Nonempty (M ≃ₗ[ℂ] RestrictedDual N)`,
a bare **linear** equivalence to the graded dual.  Every `OrdVModule` carries `finrank` (each
weight space finite-dimensional) and `isInternal` (`M = ⊕_α M_α`), so this holds of **every**
module and carries no mathematical content whatsoever.  That is not an assertion here, it is
`selfContragredient_of_ordVModule` below: the equivalence is *constructed*, unconditionally, for an
arbitrary `OrdVModule`.  Consequently `SelfContragredient` **must not** be used as the self-duality
conjunct of `StronglyFinite`, and it is not.

## §2 The duplicate `IsSimple`, resolved

`IsSimple` was defined **twice**:

* `VertexOperatorAlgebra.IsSimple` (`Core/BilinearForm.lean:208`) — `⊤ ≠ ⊥` and every VOA ideal is
  `⊥` or `⊤`;
* `VOA.IsSimple` (`Modules/Rationality.lean:147`) — `OrdVModule.IsIrreducible
  (adjointModule W)`.

They are **equivalent**, and that is proved here (`isSimple_iff_adjointModule_isIrreducible`): a
`WeakModule.Submodule'` of the adjoint module is *definitionally* an ideal, and `Nontrivial 𝒱` is
`(⊤ : Submodule ℂ 𝒱) ≠ ⊥`.  `VOA.IsSimple` had **zero** consumers in the repository, so it
is the one deprecated (in place, at `Modules/Rationality.lean`); everything downstream already used
the `Core/BilinearForm.lean` one, which is also the one the literature means when it reasons about
proper ideals (McRae §2.2).

## §3 What replaces the vacuous predicate: `VertexOperatorAlgebra.SelfDual`

McRae §2.2 clause (2) supplies the escape itself: `V ≅ V′` is stated there as *equivalent* to the
existence of a nondegenerate invariant bilinear form on `V`.  That second formulation is entirely
internal to `𝒱`, needs no contragredient action, and is exactly what `Core/BilinearForm.lean` +
`Core/InvariantFormFHL2.lean` already build.  So

  `W.SelfDual := ∃ B : InvariantForm W, B.IsFullyInvariant ∧ leftRadical B = ⊥`.

Both directions of the Dong–Mason equivalence are then **proved**, not cited:

* `SelfDual.L_one_grading_one_eq_zero` — a nondegenerate invariant form forces `L₁𝒱₁ = 0`, i.e.
  strong CFT type.  Elementary: `L₁𝒱₁ ⊆ 𝒱₀ = ℂ𝟙` (`L_one_lower`, VOA4), and if `L₁u = λ𝟙` with
  `λ ≠ 0` then `λ(𝟙|𝟙) = (L₁u|𝟙) = (u|L₋₁𝟙) = 0`, so `(𝟙|𝟙) = 0`; with `𝒱ₘ ⟂ 𝒱ₙ` for `m ≠ n`
  that puts `𝟙` in the radical, contradicting nondegeneracy.
* `selfDual_of_L_one_grading_one_eq_zero` — conversely, for a **simple** `𝒱` with `L₁𝒱₁ = 0` the
  canonical FHL form is fully invariant and nondegenerate (`invariantForm_nondegenerate_FHL`,
  H. Li, *Symmetric invariant bilinear forms on vertex operator algebras*, J. Pure Appl. Algebra
  **96** (1994) 279–297).

## §4 ⚠ CFT type is discharged by the ambient structure — documented, not dropped

`VertexOperatorAlgebra` (`Core/VertexOperatorAlgebra.lean:103`) carries, as **structure fields**:

* `positivity : ∀ n : ℤ, n < 0 → grading n = ⊥`  — "`V(n) = 0` for `n < 0`" (VOA4, part 2);
* `vacuum_grade : grading 0 = ℂ ∙ vacuum`         — "`V(0) = ℂ1`"        (VOA4, part 1);
* `PreVertexAlgebra.finrank : ∀ n, FiniteDimensional ℂ (grading n)` — "`dim V(n) < ∞`".

Those are precisely the three clauses of Creutzig–Gannon's CFT type and of McRae's clause (1), so
the CFT-type conjunct of `StronglyFinite` is **structurally true of every VOA in this repository**
and is not repeated as a field.  It is *not* silently dropped: `StronglyFinite.cftType` states it
and proves it, `StronglyFinite.finrank_grading_zero_eq_one` proves the sharp form `dim 𝒱₀ = 1`, and
`StronglyFinite.grading_neg_eq_bot` proves `𝒱_{n<0} = 0`.

⚠ One genuine gap in the ambient fields, closed by a conjunct rather than assumed away:
`vacuum_grade` gives `𝒱₀ = ℂ𝟙`, which is `dim 𝒱₀ ≤ 1`, and equals `1` only when `𝟙 ≠ 0` — the
zero VOA satisfies `vacuum_grade` with `dim 𝒱₀ = 0`.  `dim 𝒱₀ = 1` is therefore recovered from the
`simple` conjunct (`IsSimple.vacuum_ne_zero`, `Core/SimpleImage.lean`), not from VOA4 alone.

## Status

`sorry`-free, `admit`-free, `native_decide`-free, no project axioms, `VOA.pbw`-free.
Every declaration is `[propext, Classical.choice, Quot.sound]`.

## References
* Creutzig–Gannon, J. Phys. A **50** (2017) no. 40, 404004 = arXiv:1605.04630v1, §2.2 (this is
  McRae's `[CG]`).  Dong–Mason, *Rational vertex operator algebras and the effective central
  charge*, arXiv:math/0201318v1, §2–§3.  McRae, arXiv:2108.01898v3, §1 and §2.2.  H. Li,
  *Symmetric invariant bilinear forms on vertex operator algebras*, J. Pure Appl. Algebra **96**
  (1994) 279–297, Thm. 3.1.  Frenkel–Huang–Lepowsky, Mem. AMS **104** (1993) no. 494, §5.3.
-/

namespace VOA

open Module (End Dual)

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## §1  `SelfContragredient` is vacuous -/

/-- ⚠⚠ **`SelfContragredient` (`Modules/Contragredient.lean`) is VACUOUS.**  It asks only for a
`ℂ`-**linear** equivalence `M ≃ₗ RestrictedDual N`, and every `OrdVModule` has one: `isInternal`
gives `M ≅ ⨁_α M_α`, `finrank` makes each `M_α` finite-dimensional, and a finite-dimensional space
is linearly isomorphic to its dual.  The equivalence is *constructed* below, so this is a theorem,
not an assertion.

Consequence, and the reason this theorem is stated at all: `SelfContragredient` **cannot** serve as
the self-duality conjunct of `StronglyFinite`.  The mathematical content of `V ≅ V′` lives in the
contragredient **action**, not in the underlying graded vector space; see
`VertexOperatorAlgebra.SelfDual` below for the replacement, which is McRae §2.2's own "equivalently"
clause and carries genuine content (`selfDual_iff`). -/
theorem selfContragredient_of_ordVModule {W : VertexOperatorAlgebra 𝒱} {M : Type u}
    [AddCommGroup M] [Module ℂ M] (N : OrdVModule W M) : SelfContragredient N := by
  classical
  haveI : ∀ α : ℂ, FiniteDimensional ℂ (N.weight α) := N.finrank
  exact ⟨(LinearEquiv.ofBijective (DirectSum.coeLinearMap N.weight) N.isInternal).symm.trans
    (DFinsupp.mapRange.linearEquiv fun α : ℂ =>
      LinearEquiv.ofFinrankEq (N.weight α) (Module.Dual ℂ (N.weight α))
        Subspace.dual_finrank_eq.symm)⟩

/-! ## §2  The duplicate `IsSimple`, resolved -/

/-- **The two `IsSimple` predicates agree.**

* `VertexOperatorAlgebra.IsSimple W` (`Core/BilinearForm.lean:208`): `⊤ ≠ ⊥`, and every VOA ideal
  is `⊥` or `⊤`.
* `VOA.IsSimple W` (`Modules/Rationality.lean:147`):
  `OrdVModule.IsIrreducible (adjointModule W)`.

The proof is a repackaging, not an argument: `WeakModule.Submodule' (adjointModule W).toWeakModule`
has exactly the data of an ideal, since `(adjointModule W).act u n x = W.smul u n x` by `rfl`; and
`Nontrivial 𝒱 ↔ (⊤ : Submodule ℂ 𝒱) ≠ ⊥`.

⚠ The literature means this predicate — McRae §2.2 argues simplicity through "any proper ideal
`I ⊊ V`", the ideal-theoretic form.  `VOA.IsSimple` had no consumers and is deprecated. -/
theorem isSimple_iff_adjointModule_isIrreducible (W : VertexOperatorAlgebra 𝒱) :
    W.IsSimple ↔ OrdVModule.IsIrreducible (adjointModule W) := by
  constructor
  · rintro ⟨htb, hid⟩
    refine ⟨?_, fun P => hid P.carrier fun u v n hv => P.act_mem u n hv⟩
    by_contra hns
    rw [not_nontrivial_iff_subsingleton] at hns
    exact htb (le_antisymm (fun x _ => by
      rw [Submodule.mem_bot]; exact Subsingleton.elim x 0) bot_le)
  · rintro ⟨hnt, hsub⟩
    refine ⟨?_, fun I hI => hsub ⟨I, fun u n {x} hx => hI u x n hx⟩⟩
    obtain ⟨x, hx⟩ := exists_ne (0 : 𝒱)
    intro h
    exact hx (by simpa [h] using (Submodule.mem_top : x ∈ (⊤ : Submodule ℂ 𝒱)))

set_option linter.deprecated false in
/-- The deprecated duplicate, spelled out: `VOA.IsSimple` is `W.IsSimple`.

(`linter.deprecated` is switched off for this one declaration — naming the deprecated constant is
the entire point of the statement.) -/
theorem isSimple_iff_isSimple (W : VertexOperatorAlgebra 𝒱) :
    VOA.IsSimple W ↔ W.IsSimple :=
  (isSimple_iff_adjointModule_isIrreducible W).symm

-- ⚠ The `@[deprecated]` attribute on `VOA.IsSimple` itself must live at the declaration
-- site (Lean refuses to attach it from a downstream module), so it is applied in
-- `Modules/Rationality.lean`, in the message form, pointing here for the bridge.

namespace VertexOperatorAlgebra

variable {W : VertexOperatorAlgebra 𝒱}

/-! ## §3  VOA-level self-duality with genuine content -/

/-- **`𝒱` is self-dual** (`V ≅ V′`), in McRae's equivalent invariant-form formulation.

McRae, arXiv:2108.01898v3, §2.2, clause (2), states self-contragredience as `V ≅ V′` (as
`V`-modules) and, in the same breath, as the *equivalent* condition that `V` carry a nondegenerate
invariant bilinear form `V × V → ℂ`.  It is that second formulation that is taken as the
definition here.

"Invariant" is taken in the full Frenkel–Huang–Lepowsky sense
`(Y(u,z)a|b) = (a|Y(e^{zL₁}(−z⁻²)^{L₀}u, z⁻¹)b)`, carried here by
`InvariantForm.IsFullyInvariant` (its explicit mode content); "nondegenerate" is
`leftRadical B = ⊥`.  The side is a convention, not a restriction: for a fully invariant
**normalised** form the two radicals coincide (`leftRadical_eq_rightRadical`,
`Core/InvariantFormRadical.lean`), and `form_vacuum_ne_zero_of_leftRadical_eq_bot` below shows any
nondegenerate invariant form has `(𝟙|𝟙) ≠ 0`, hence is a nonzero rescaling away from normalised.

⚠ **This is the replacement for the vacuous `SelfContragredient`** (see
`selfContragredient_of_ordVModule`).  It is not vacuous: `selfDual_iff` shows it is *equivalent* to
Dong–Mason's strong-CFT-type condition `L₁𝒱₁ = 0`, and Dong–Mason §2 (arXiv:math/0201318v1) record
that CFT type does **not** imply strong CFT type — they note that the level and Virasoro vector of
their §2 example can be modified so that the result is of CFT type but not of strong CFT type. -/
def SelfDual (W : VertexOperatorAlgebra 𝒱) : Prop :=
  ∃ B : InvariantForm W, B.IsFullyInvariant ∧ InvariantForm.leftRadical B = ⊥

/-- **A nondegenerate invariant form does not kill the vacuum**: `(𝟙|𝟙) ≠ 0`.

`𝟙 ∈ 𝒱₀` is orthogonal to every `𝒱ₙ` with `n ≠ 0` (`orthogonal_of_ne`), and `𝒱₀ = ℂ𝟙` (VOA4), so
`(𝟙|𝟙) = 0` would already put `𝟙` in the left radical; nondegeneracy then gives `𝟙 = 0`.

Consequence worth recording: every nondegenerate invariant form is a nonzero rescaling away from
the unit normalisation `(𝟙|𝟙) = 1`, so nothing is lost by not building `Normalized` into
`SelfDual`. -/
theorem form_vacuum_ne_zero_of_leftRadical_eq_bot (hne : W.vacuum ≠ 0) {B : InvariantForm W}
    (hrad : InvariantForm.leftRadical B = ⊥) : B.form W.vacuum W.vacuum ≠ 0 := by
  classical
  intro hvv
  refine hne ?_
  have hmemrad : W.vacuum ∈ InvariantForm.leftRadical B := by
    rw [InvariantForm.mem_leftRadical]
    refine LinearMap.ext fun b => ?_
    simp only [LinearMap.zero_apply]
    have hbtop : b ∈ ⨆ i, W.grading i := by
      rw [W.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
    refine Submodule.iSup_induction W.grading
      (motive := fun b => B.form W.vacuum b = 0) hbtop ?_ ?_ ?_
    · intro i x hx
      rcases eq_or_ne (0 : ℤ) i with rfl | hne0
      · rw [W.vacuum_grade] at hx
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
        rw [map_smul, smul_eq_mul, hvv, mul_zero]
      · exact InvariantForm.orthogonal_of_ne B hne0 W.vacuum_mem_grading_zero hx
    · exact map_zero _
    · intro x y hx hy; rw [map_add, hx, hy, add_zero]
  rw [hrad, Submodule.mem_bot] at hmemrad
  exact hmemrad

/-- **A nondegenerate invariant form forces strong CFT type**: `L₁𝒱₁ = 0`.

This is one half of the Dong–Mason §2 equivalence (arXiv:math/0201318v1): for `V` of CFT type,
strong CFT type holds precisely when `V` is self-dual, `V′ ≅ V`.  In the literature this half is
read off H. Li's classification of invariant forms (J. Pure Appl. Algebra **96** (1994) 279–297,
Thm. 3.1: they are classified by the dual of `V₀/L(1)V₁`); here it is proved directly and needs
neither Li's theorem nor full invariance — only the Virasoro-adjointness `(Lₙa|b) = (a|L₋ₙb)` that
every `InvariantForm` carries.

Proof.  `L₁𝒱₁ ⊆ 𝒱₀ = ℂ𝟙` (`L_one_lower` + VOA4 `vacuum_grade`), so `L₁v = λ𝟙`.  Virasoro
adjointness gives `λ(𝟙|𝟙) = (L₁v|𝟙) = (v|L₋₁𝟙) = (v|0) = 0`, and
`form_vacuum_ne_zero_of_leftRadical_eq_bot` gives `(𝟙|𝟙) ≠ 0`, so `λ = 0`. -/
theorem invariantForm_L_one_grading_one_eq_zero (hne : W.vacuum ≠ 0) {B : InvariantForm W}
    (hrad : InvariantForm.leftRadical B = ⊥) {v : 𝒱} (hv : v ∈ W.grading 1) : W.L 1 v = 0 := by
  classical
  have hmem : W.L 1 v ∈ W.grading 0 := by simpa using L_one_lower W hv
  rw [W.vacuum_grade] at hmem
  obtain ⟨lam, hlam⟩ := Submodule.mem_span_singleton.mp hmem
  have h1 : B.form (W.L 1 v) W.vacuum = B.form v (W.L (-1) W.vacuum) :=
    B.virasoro_adj 1 v W.vacuum
  rw [L_neg_one_vacuum W, map_zero] at h1
  rw [← hlam, map_smul, LinearMap.smul_apply, smul_eq_mul] at h1
  have hlam0 : lam = 0 :=
    (mul_eq_zero.mp h1).resolve_right (form_vacuum_ne_zero_of_leftRadical_eq_bot hne hrad)
  rw [← hlam, hlam0, zero_smul]

/-- **Self-dual ⟹ strong CFT type** (Dong–Mason §2, one direction). -/
theorem SelfDual.L_one_grading_one_eq_zero (hne : W.vacuum ≠ 0) (h : W.SelfDual)
    {v : 𝒱} (hv : v ∈ W.grading 1) : W.L 1 v = 0 :=
  let ⟨_, _, hrad⟩ := h
  invariantForm_L_one_grading_one_eq_zero hne hrad hv

/-- **Strong CFT type + simple ⟹ self-dual** (Dong–Mason §2, the other direction).

The witness is the canonical FHL form `canonicalInvariantForm`
(`Core/InvariantFormFHL2.lean`), which is unconditionally fully invariant and normalised under
`𝟙 ≠ 0` and `L₁𝒱₁ = 0`; simplicity turns "nonzero" into "nondegenerate" via
`leftRadical_eq_maxGradedIdeal` (H. Li, J. Pure Appl. Algebra **96** (1994) 279–297). -/
theorem selfDual_of_L_one_grading_one_eq_zero (hne : W.vacuum ≠ 0)
    (hqp : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0) (hsimple : W.IsSimple) : W.SelfDual :=
  ⟨canonicalInvariantForm hne hqp, canonicalInvariantForm_isFullyInvariant hne hqp,
    invariantForm_nondegenerate_FHL hne hqp hsimple⟩

/-- **Dong–Mason's equivalence, machine-checked.**  For a **simple** VOA (of CFT type, which is
structural here — see the file docstring §4),

  `V` is self-dual  ⟺  `V` is of strong CFT type, i.e. `L₁𝒱₁ = 0`.

This is the equivalence stated (without proof, as a reading of Frenkel–Huang–Lepowsky §5.3) in
Dong–Mason, arXiv:math/0201318v1, §2.  Their self-duality is `V′ ≅ V`; ours is the equivalent
nondegenerate-invariant-form formulation of McRae §2.2 clause (2).

⚠ Simplicity is used only in the `←` direction. -/
theorem selfDual_iff (hsimple : W.IsSimple) :
    W.SelfDual ↔ ∀ v, v ∈ W.grading 1 → W.L 1 v = 0 :=
  ⟨fun h _ hv => h.L_one_grading_one_eq_zero hsimple.vacuum_ne_zero hv,
    fun hqp => selfDual_of_L_one_grading_one_eq_zero hsimple.vacuum_ne_zero hqp hsimple⟩

/-! ## §4  CFT type, discharged by the ambient structure -/

/-- **`dim 𝒱₀ = 1`** — the sharp form of "`V(0) = ℂ1`".  VOA4's `vacuum_grade` alone gives only
`𝒱₀ = ℂ𝟙`, i.e. `dim 𝒱₀ ≤ 1`; the zero VOA satisfies it with `dim 𝒱₀ = 0`.  The upgrade needs
`𝟙 ≠ 0`, which simplicity supplies. -/
theorem finrank_grading_zero_eq_one (hne : W.vacuum ≠ 0) :
    Module.finrank ℂ (W.grading 0) = 1 := by
  rw [W.vacuum_grade]
  exact finrank_span_singleton hne

end VertexOperatorAlgebra

/-! ## §5  `StronglyFinite` -/

/-- **`StronglyFinite`** — Creutzig–Gannon, arXiv:1605.04630v1, **§2.2** (an unnumbered in-text
convention).  Their four conjuncts, in their order: **simple**, **`C₂`-cofinite**, **of CFT type**,
**`V ≅ V∨`**.

McRae, arXiv:2108.01898v3, §2.2 attributes the term to them, describing it as "strongly rational
with rationality dropped"; his own use of the name additionally relaxes CFT type to `ℕ`-graded, a
weakening this file does **not** adopt (the `ℕ`-graded variant would lose the `dim 𝒱₀ = 1` clause,
which is structural here).

**The four conjuncts, and where each lives:**

| Creutzig–Gannon clause | here |
| --- | --- |
| simple | `simple : W.IsSimple` |
| `V ≅ V∨` | `selfDual : W.SelfDual` |
| `C₂`-cofinite | `c2Cofinite : C2Cofinite W` |
| of CFT type | ⚠ **structural** — see below |

⚠ **The CFT-type conjunct is discharged by the ambient `VertexOperatorAlgebra` structure and is
therefore not a field.**  Creutzig–Gannon's CFT type has three parts — `V = ⊕_{n≥0} V(n)`,
`V(0) = ℂ1`, `dim V(n) < ∞` — and each is a structure field:
`VertexOperatorAlgebra.positivity`, `VertexOperatorAlgebra.vacuum_grade` and
`PreVertexAlgebra.finrank`.  This is recorded, not slid past: `StronglyFinite.cftType` states and
proves all three, and `StronglyFinite.finrank_grading_zero_eq_one` proves the sharp `dim 𝒱₀ = 1`
(which needs `𝟙 ≠ 0`, supplied by `simple`, since `vacuum_grade` alone permits `dim 𝒱₀ = 0`).

⚠ **Simplicity is kept as a conjunct, deliberately.**  McRae §2.2 *derives* simplicity from CFT
type + self-contragredience via H. Li, J. Pure Appl. Algebra **96** (1994) 279–297, Thm. 3.1.  That
theorem is not formalized in this repository (only the *other* direction, "simple + nondegenerate
form", is — `invariantForm_nondegenerate_FHL`), so the conjunct is carried rather than borrowed.
This matches Creutzig–Gannon's and McRae's own `strongly finite`, both of which list it. -/
structure StronglyFinite (W : VertexOperatorAlgebra 𝒱) : Prop where
  /-- `𝒱` is simple: `⊤ ≠ ⊥` and its only ideals are `⊥` and `⊤`. -/
  simple : W.IsSimple
  /-- `𝒱 ≅ 𝒱∨`, in McRae §2.2's equivalent form: a nondegenerate invariant bilinear form. -/
  selfDual : W.SelfDual
  /-- `dim 𝒱/C₂(𝒱) < ∞` (Zhu). -/
  c2Cofinite : C2Cofinite W

namespace StronglyFinite

variable {W : VertexOperatorAlgebra 𝒱}

/-- `𝟙 ≠ 0`, from simplicity (`Core/SimpleImage.lean`). -/
theorem vacuum_ne_zero (h : StronglyFinite W) : W.vacuum ≠ 0 := h.simple.vacuum_ne_zero

/-- **CFT type, discharged.**  All three Creutzig–Gannon clauses at once: `𝒱ₙ = 0` for `n < 0`,
`𝒱₀ = ℂ𝟙` with `dim 𝒱₀ = 1`, and `dim 𝒱ₙ < ∞`.  The first, second and fourth are the structure
fields `positivity`, `vacuum_grade`, `PreVertexAlgebra.finrank`; the third needs `𝟙 ≠ 0`. -/
theorem cftType (h : StronglyFinite W) :
    (∀ n : ℤ, n < 0 → W.grading n = ⊥) ∧ W.grading 0 = ℂ ∙ W.vacuum ∧
      Module.finrank ℂ (W.grading 0) = 1 ∧ ∀ n : ℤ, FiniteDimensional ℂ (W.grading n) :=
  ⟨W.positivity, W.vacuum_grade,
    VertexOperatorAlgebra.finrank_grading_zero_eq_one h.vacuum_ne_zero, W.finrank⟩

/-- `𝒱ₙ = 0` for `n < 0` — VOA4, part 2. -/
theorem grading_neg_eq_bot (_h : StronglyFinite W) {n : ℤ} (hn : n < 0) : W.grading n = ⊥ :=
  W.positivity n hn

/-- `dim 𝒱₀ = 1` — the sharp CFT-type clause. -/
theorem finrank_grading_zero_eq_one (h : StronglyFinite W) :
    Module.finrank ℂ (W.grading 0) = 1 :=
  VertexOperatorAlgebra.finrank_grading_zero_eq_one h.vacuum_ne_zero

/-- **`StronglyFinite ⟹ strong CFT type`** (`L₁𝒱₁ = 0`), Dong–Mason §2.  So Dong–Mason's
clause 1 is *implied* by the Creutzig–Gannon package, not an extra demand. -/
theorem L_one_grading_one_eq_zero (h : StronglyFinite W) {v : 𝒱} (hv : v ∈ W.grading 1) :
    W.L 1 v = 0 :=
  h.selfDual.L_one_grading_one_eq_zero h.vacuum_ne_zero hv

end StronglyFinite

/-- **Recognition principle for `StronglyFinite`**: simple + `C₂`-cofinite + strong CFT type.
By `selfDual_iff` this is not a weakening — the three hypotheses are *equivalent* to
`StronglyFinite`, which `stronglyFinite_iff` records. -/
theorem stronglyFinite_of_L_one_grading_one_eq_zero {W : VertexOperatorAlgebra 𝒱}
    (hsimple : W.IsSimple) (hqp : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0) (hc2 : C2Cofinite W) :
    StronglyFinite W where
  simple := hsimple
  selfDual := VertexOperatorAlgebra.selfDual_of_L_one_grading_one_eq_zero
    hsimple.vacuum_ne_zero hqp hsimple
  c2Cofinite := hc2

/-- **`StronglyFinite` in Dong–Mason's vocabulary.**  Given simplicity and `C₂`-cofiniteness,
being strongly finite is exactly being of **strong CFT type** — the self-duality clause of
Creutzig–Gannon and the `L₁V₁ = 0` clause of Dong–Mason are the same condition here. -/
theorem stronglyFinite_iff {W : VertexOperatorAlgebra 𝒱} (hsimple : W.IsSimple)
    (hc2 : C2Cofinite W) :
    StronglyFinite W ↔ ∀ v, v ∈ W.grading 1 → W.L 1 v = 0 :=
  ⟨fun h _ hv => h.L_one_grading_one_eq_zero hv,
    fun hqp => stronglyFinite_of_L_one_grading_one_eq_zero hsimple hqp hc2⟩

/-! ## §6  `StronglyRational` -/

/-- **`StronglyRational`** — Dong–Mason, arXiv:math/0201318v1, **§3**, where the term is
introduced with three conjuncts: of strong CFT type, `C₂`-cofinite, rational.  Equivalently, McRae,
arXiv:2108.01898v3, **§2.2**, in four: (1) positive energy / CFT type, (2) self-contragredient,
(3) `C₂`-cofinite, (4) rational — i.e. `StronglyFinite` + rationality, which is how it is packaged
here.

**Rationality here is `AdmissiblyRational`** — the standard Zhu / Dong–Li–Mason notion, "every
admissible (`ℕ`-gradable weak) module is completely reducible" — deliberately, *not*
`GannonRational`.  Dong–Mason's §3 spells rationality out as "every admissible module is a direct
sum of irreducible **admissible** modules", and that is the clause matched here.
`GannonRational` (Gannon Def. 5.3.2) is a three-clause package over three different module
categories and is not comparable to `AdmissiblyRational` in either direction
(`Modules/RationalityLattice.lean` §8); using it here would misquote both sources.

⚠ **Two places where this definition is formally *stronger* than a literal reading of a source,
recorded rather than hidden.**

* **Simplicity.**  Dong–Mason's three clauses do **not** list it, and McRae's §2.2 four clauses do
  not either — he *derives* it from clauses (1)+(2) through H. Li, J. Pure Appl. Algebra **96**
  (1994) 279–297, Thm. 3.1, which is not formalized in this repository.  `StronglyFinite.simple`
  therefore carries it as a hypothesis.  Extensionally the literature says the two agree; formally,
  `StronglyRational` here implies but is not *known here* to be implied by the Dong–Mason
  three-clause form.
* **The shape of clause (4).**  McRae's (4) requires every `½ℕ`-gradable weak module to decompose
  into irreducible **grading-restricted** modules — i.e. the summands must be *ordinary*.
  `AdmissiblyRational` asks only complete reducibility inside the
  admissible category, matching Dong–Mason's phrasing; upgrading the summands to ordinary is DLM
  Thm. 8.1(c), carried as the named predicate `DLMSimpleAdmissibleOrdinary`
  (`Modules/RationalityLattice.lean` §5) and used in `StronglyRational.gannonRational`.  For a
  strongly rational VOA it is a theorem
  (`AdmissibleOrdinary.dlmSimpleAdmissibleOrdinary_of_stronglyRational`).

⚠ **Creutzig–Gannon's `strongly-rational` is a *different, stronger* predicate.**  Their §2.2
defines it as strongly-finite plus **regular** — `Regular`, not `AdmissiblyRational`.  Since
`Regular ⟹ AdmissiblyRational` (`Regular.admissiblyRational`, DLM
Remark 3.2) and the converse needs `C₂`-cofiniteness (Abe–Buhl–Dong Thm. 4.5, carried as the
named predicate `ABDRegularOfC2AndRational`), the Creutzig–Gannon notion implies this one;
`stronglyRational_of_regular` records that direction, and `StronglyRational.regular_of_abd` the
converse under the ABD predicate.  That predicate is proved for every VOA
(`LiteratureInputs.abdRegularOfC2AndRational_holds`), so the converse holds outright:
`StronglyRational.regular` (`Classification/COne/LiteratureInputsProved.lean`). -/
structure StronglyRational (W : VertexOperatorAlgebra 𝒱) : Prop extends StronglyFinite W where
  /-- Rational in the admissible sense, `AdmissiblyRational`: every **admissible** module is
  completely reducible.  ⚠ This is the library's transcription of the Zhu / Dong–Li–Mason notion,
  with complements taken among *weak* submodules; `Modules/AdmissibleRationality.lean`
  (§ *⚠ One deliberate convention*) records that its relation to DLM's graded reading is **not
  settled** (only "DLM-rational ⟹ `AdmissiblyRational`" is known on paper). -/
  rational : AdmissiblyRational W

namespace StronglyRational

variable {W : VertexOperatorAlgebra 𝒱}

/-- **`StronglyRational ⟹ StronglyFinite`** — McRae §2.2 describes strongly finite as exactly
strongly rational with the rationality clause dropped, so this must be, and is, a projection. -/
theorem stronglyFinite (h : StronglyRational W) : StronglyFinite W := h.toStronglyFinite

/-- **`StronglyRational ⟹` strong CFT type** (`L₁𝒱₁ = 0`), Dong–Mason §3 clause 1 recovered
from the McRae/Creutzig–Gannon presentation. -/
theorem L_one_grading_one_eq_zero (h : StronglyRational W) {v : 𝒱} (hv : v ∈ W.grading 1) :
    W.L 1 v = 0 :=
  h.toStronglyFinite.L_one_grading_one_eq_zero hv

/-- **`StronglyRational ⟹ GannonRational`**, given Dong–Li–Mason Thm. 8.1(b) and 8.1(c) as
named hypotheses (`Modules/RationalityLattice.lean` §5).  Both are theorems for strongly
rational VOAs; the hypothesis-free form is `StronglyRational.gannonRational'`
(`Classification/COne/LiteratureInputsProved.lean`).  Nothing here is
`C₂`-flavoured: the `C₂`-cofiniteness of `StronglyRational` is *not* used, because Gannon's clause
(3) is DLM Thm. 8.1(c) over **admissible** modules and needs rationality alone. -/
theorem gannonRational (h : StronglyRational W) (hFin : DLMFinitelyManyIrredAdmissible W)
    (hOrd : DLMSimpleAdmissibleOrdinary W) : GannonRational W :=
  gannonRational_of_admissiblyRational h.rational hFin hOrd

end StronglyRational

/-- **The Creutzig–Gannon route**: their `strongly-rational` (`StronglyFinite` + `Regular`)
implies the Dong–Mason / McRae one defined here, via `Regular ⟹ AdmissiblyRational`
(`Regular.admissiblyRational`, DLM Remark 3.2). -/
theorem stronglyRational_of_regular {W : VertexOperatorAlgebra 𝒱} (h : StronglyFinite W)
    (hreg : Regular W) : StronglyRational W where
  toStronglyFinite := h
  rational := hreg.admissiblyRational

/-- The converse of `stronglyRational_of_regular`, under the Abe–Buhl–Dong predicate
`ABDRegularOfC2AndRational` (`Modules/RationalityLattice.lean` §5): a strongly rational VOA is
`C₂`-cofinite, so ABD Thm. 4.5 upgrades its rationality to regularity — i.e. it is
strongly-rational in the Creutzig–Gannon sense too.  The predicate is proved for every VOA
(`LiteratureInputs.abdRegularOfC2AndRational_holds`); the hypothesis-free form is
`StronglyRational.regular` (`Classification/COne/LiteratureInputsProved.lean`). -/
theorem StronglyRational.regular_of_abd {W : VertexOperatorAlgebra 𝒱} (h : StronglyRational W)
    (hABD : ABDRegularOfC2AndRational W) : Regular W :=
  hABD h.c2Cofinite h.rational

/-! ## §7  Satisfiability: a witness generator at `𝒱 = ℂ𝟙`

A definition nobody can satisfy is worth nothing, and both bundles above are large enough that
this is a real worry.  `stronglyRational_of_span_vacuum` closes it in the same style as
`admissiblyRational_of_span_vacuum` (`Modules/AdmissibleRationality.lean`): every VOA whose
underlying space is `ℂ𝟙` is strongly rational, hence strongly finite.  Instantiated at `trivialVOA`
in `Examples/TrivialStronglyRational.lean`. -/

namespace VertexOperatorAlgebra

variable {W : VertexOperatorAlgebra 𝒱}

/-- `L₁𝟙 = 0`: the creation axiom VA3 at the nonnegative mode `ω₍₂₎`. -/
theorem L_one_vacuum_eq_zero (W : VertexOperatorAlgebra 𝒱) : W.L 1 W.vacuum = 0 := by
  rw [L_def, show (1 + 1 : ℤ) = 2 by ring, ← PreVertexAlgebra.smul_def,
    W.toPreVertexAlgebra.smul_vacuum_nonneg W.conformalVector (by norm_num : (0 : ℤ) ≤ 2)]

/-- If `𝒱 = ℂ𝟙` then `L₁` annihilates **everything**, in particular `L₁𝒱₁ = 0` (strong CFT
type). -/
theorem L_one_eq_zero_of_span_vacuum (hspan : Submodule.span ℂ ({W.vacuum} : Set 𝒱) = ⊤)
    (v : 𝒱) : W.L 1 v = 0 := by
  have hv : v ∈ Submodule.span ℂ ({W.vacuum} : Set 𝒱) := by rw [hspan]; exact Submodule.mem_top
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
  rw [map_smul, L_one_vacuum_eq_zero, smul_zero]

/-- If `𝒱 = ℂ𝟙` and `𝟙 ≠ 0` then `𝒱` is simple: a nonzero ideal contains some `c𝟙` with
`c ≠ 0`, hence `𝟙`, hence everything. -/
theorem isSimple_of_span_vacuum (hne : W.vacuum ≠ 0)
    (hspan : Submodule.span ℂ ({W.vacuum} : Set 𝒱) = ⊤) : W.IsSimple := by
  refine ⟨fun h => hne ?_, fun I _ => ?_⟩
  · exact (Submodule.mem_bot ℂ).mp (h ▸ (Submodule.mem_top : W.vacuum ∈ ⊤))
  · rcases eq_or_ne I ⊥ with rfl | hI
    · exact Or.inl rfl
    · refine Or.inr (eq_top_iff.mpr ?_)
      obtain ⟨x, hxI, hx0⟩ := (Submodule.ne_bot_iff I).mp hI
      have hx : x ∈ Submodule.span ℂ ({W.vacuum} : Set 𝒱) := by
        rw [hspan]; exact Submodule.mem_top
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
      have hc : c ≠ 0 := fun h => hx0 (by rw [h, zero_smul])
      have hvac : W.vacuum ∈ I := by
        have := I.smul_mem c⁻¹ hxI
        rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
      rw [← hspan]
      exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hvac)

/-- If `𝒱 = ℂ𝟙` then `𝒱` is finite-dimensional, hence `C₂`-cofinite (`A₂(𝒱)` is a quotient). -/
theorem c2Cofinite_of_span_vacuum (hspan : Submodule.span ℂ ({W.vacuum} : Set 𝒱) = ⊤) :
    C2Cofinite W := by
  haveI : Module.Finite ℂ 𝒱 :=
    Module.finite_def.mpr ⟨{W.vacuum}, by simpa using hspan⟩
  exact inferInstanceAs (FiniteDimensional ℂ (𝒱 ⧸ O₂ W))

end VertexOperatorAlgebra

/-- **Positive witness generator.**  Any VOA whose underlying space is `ℂ𝟙` (with `𝟙 ≠ 0`) is
**strongly rational**, hence strongly finite.  All four conjuncts fall out:

* simple — `isSimple_of_span_vacuum`;
* self-dual — `L₁` kills everything, so `L₁𝒱₁ = 0`, and `selfDual_of_L_one_grading_one_eq_zero`
  builds the canonical nondegenerate FHL form;
* `C₂`-cofinite — `𝒱` is one-dimensional, so `A₂(𝒱)` is;
* rational — `admissiblyRational_of_span_vacuum` (`Modules/AdmissibleRationality.lean`).

This is what keeps `StronglyFinite` / `StronglyRational` from being accidentally over-strong, and
so keeps any future `¬ StronglyRational …` from being vacuously true. -/
theorem stronglyRational_of_span_vacuum {W : VertexOperatorAlgebra 𝒱} (hne : W.vacuum ≠ 0)
    (hspan : Submodule.span ℂ ({W.vacuum} : Set 𝒱) = ⊤) : StronglyRational W where
  toStronglyFinite :=
    stronglyFinite_of_L_one_grading_one_eq_zero
      (VertexOperatorAlgebra.isSimple_of_span_vacuum hne hspan)
      (fun v _ => VertexOperatorAlgebra.L_one_eq_zero_of_span_vacuum hspan v)
      (VertexOperatorAlgebra.c2Cofinite_of_span_vacuum hspan)
  rational := admissiblyRational_of_span_vacuum W hspan

/-- The `StronglyFinite` half of `stronglyRational_of_span_vacuum`. -/
theorem stronglyFinite_of_span_vacuum {W : VertexOperatorAlgebra 𝒱} (hne : W.vacuum ≠ 0)
    (hspan : Submodule.span ℂ ({W.vacuum} : Set 𝒱) = ⊤) : StronglyFinite W :=
  (stronglyRational_of_span_vacuum hne hspan).toStronglyFinite

end VOA
