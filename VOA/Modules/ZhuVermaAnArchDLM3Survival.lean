/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchDLM3Zero

/-!
# DLM3 Theorem 4.1, part IV — the radical `J`, and the survival of `U` in `M̄_n(U)`

Dong–Li–Mason, *Vertex operator algebras and associative algebras* (arXiv `q-alg/9612010v2`), §4,
close their Theorem 4.1 with three sentences (printed p. 19):

> "Then from the definition of `W` (4.3) and Propositions 4.3, 4.6 and 4.7 we conclude that
> `U(V̂)W ⊂ J`. … Note that `J ∩ U = 0`.  So `L(U)(n)` contains `U` as an `A_n(V)`-submodule."

This file ports that architecture at `n = 0` (Zhu's classical theorem), in the repo's `IndMod` /
`IndBar` language, and isolates *exactly* what is left.

## The three moving parts, and which of them is proved here

DLM3's radical is
`J = {v ∈ M_n(U) | ⟨u′, x v⟩ = 0 for all u′ ∈ U* = Hom_ℂ(U,ℂ), all x ∈ U(V̂)}`, where `U*` is
extended to `M_n(U)` by *first* extending it to `M_n(U)(n)` through the length filtration `(4.5)`
and *then* letting it annihilate `⨁_{i≠n} M_n(U)(i)`.

* **At `n = 0` the length filtration collapses.**  DLM3 define `U_s ⊆ M_n(U)(n)` as the span of
  `o_{p₁}(a₁)⋯o_{p_s}(a_s)U` with `p₁ ≥ ⋯ ≥ p_s`, `Σpᵢ = 0`, `pᵢ ≠ 0`, `p_s ≥ −n`.  At `n = 0`
  the constraints `p_s ≥ 0`, `p_s ≠ 0` force `pᵢ ≥ p_s ≥ 1` for every `i`, contradicting `Σpᵢ = 0`
  unless `s = 0`.  So `U_s = 0` for `s ≥ 1`, `M_0(U)(0) = U_0 = U`, and the whole inductive
  extension `(4.5)` is *vacuous*.  The only surviving input is DLM3's PBW step
  `M_0(U)(0) = U`, which is packaged here as the carried datum `BottomProjection` — **data, never
  an axiom** in this file.  The PBW theorem `VOA.pbw` covers it: its
  `inducedBottom` field gives
  `voaPBWBottomInjective` and hence `voaPBWBottomProjection`
  (`Modules/ZhuVermaAnArchDLM3PBWAxiom.lean`).  Level independence is proved unconditionally
  (`levCover_iSupIndep`), and concrete adjoint and Heisenberg projection instances exist without
  `pbw`; this file does not construct one for arbitrary `U`.
  `bottomProjectionOfIsCompl` records that this datum is *precisely* the statement that the bottom
  `1 ⊗ U` is a complement of the other levels — i.e. exactly what PBW supplies and nothing more.
* **The radical `J` and `J ∩ U = 0` are then free** (`radical`, `radical_invariant`,
  `BottomProjection.eq_zero_of_indBottom_mem_radical`).  Since `U* = Hom_ℂ(U,ℂ)` is the *full*
  dual it separates points (`eq_zero_of_forall_dual`, proved here from a basis), so `J` is literally
  `⋂_{y ∈ U(V̂)} ker (π ∘ ρ(y))` (`mem_radical_iff_dual`); `J` is `V̂`-invariant by construction,
  which is DLM3's Proposition 4.7 *for free at the level of the definition*; and `x = 1` gives
  `J ∩ U = 0` in one line.  **No finite-dimensionality is used anywhere** — `U` is an arbitrary
  `ℂ`-vector space, and `OrdVModule.finrank` never enters.
* **What is left is one statement**: `DefectPairsToZero` — DLM3's `U(V̂)W ⊆ J`, i.e. every iterate
  defect lies in the radical.  This is their Propositions 4.3 (⟸ the key Lemma 4.4) + 4.6.

## The survival theorem

`survival` / `survival_zero`: given a `BottomProjection` and `DefectPairsToZero`, the bottom map
`U → M̄_n(U)` is **injective**, its image lies in the level-`n` piece and inside `Ω_n(M̄_n(U))`, and
it intertwines the `P_n`-action; at `n = 0`, for a bundled `A(𝒱)`-module `U`
(`parabolicRepOfAMod`), it intertwines the `A(𝒱)`-action with the zero modes `o(a)`.  Since
`indBarWeakModule` already makes `M̄_n(U)` a genuine weak `𝒱`-module and `indBarGraded` equips it
with the level family, this is exactly "an admissible module whose bottom is `U` as an
`A(𝒱)`-module".  `separatingRealization` feeds it back into the proved equivalence
`indBarBottom_injective_iff`.

## Unconditional reductions of the residual (the part that is real mathematics here)

1. **`indDefectVec_nonneg`** — every `ℓ ≥ 0` defect of `indRho P` is *identically zero* on
   `M_n(U)` itself (`ind_moduleIterate_nonneg`).  Hence `defectPairsToZero_of_neg`:
   `DefectPairsToZero` has content only at `ℓ < 0`, exactly DLM3's associativity direction.
2. **`indDefectVec_mem_levCover`** — the defect is *homogeneous*: for homogeneous `a ∈ 𝒱_{wa}`,
   `b ∈ 𝒱_{wb}` and `z` at level `d`, `δ(a,b,z,ℓ,K)` sits in the single level
   `d + (wa + wb − ℓ − K − 2)` (`defectVec_homogeneous` on the graded representation
   `indRho P`, whose grading is `actMode_levCover`).  Consequently
   **`BottomProjection.proj_defect_eq_zero_of_level_ne`**: `π` kills the defect outright unless the
   level matches, so at the bottom (`d = n`) only the *single* mode index `K = wa + wb − ℓ − 2`
   survives.  This is the formal counterpart of DLM3's repeated "`⟨u′, M_n(U)(m)⟩ = 0 if `m ≠ n`".
3. **`defectPairsToZero_of_bottom_of_stable`** — the generation reduction: `DefectPairsToZero`
   follows from (base) the defects *at the bottom* `1 ⊗ U` lying in `J`, plus (step) stability of
   that property under the `V̂`-action.  These are precisely DLM3 Prop 4.3 and Prop 4.6.  The
   supporting linearity of the defect in its module argument
   (`VHatRep.defectVec_add_right` / `defectVec_smul_right`) is proved in
   `ZhuVermaAnArchGradedCloseDeep`.
4. **The level structure of `M_0(U)`, PBW-free** (`§ Reduction 4`).  At `n = 0` the parabolic is
   `P₀ = V̂_{≤0}`, so a negative-degree mode kills `1 ⊗ U`; commuting such a mode rightwards through
   a word of non-negative modes only shortens the word (`⁅V̂(d),V̂(e)⁆ ⊆ V̂(d+e)`).  Formalized as
   `posLevel` (the non-negative word orbit of the bottom) and the straightening theorem
   `posLevel_indRho`, this yields **`levCover_eq_posLevel`** and hence
   * **`levCover_eq_bot_of_neg`** — `M_0(U)(d) = 0` for `d < 0` (DLM3's "`M̄_n(U)(m) = 0` if
     `m < 0`");
   * **`levCover_zero_eq_range`** — `M_0(U)(0) = 1 ⊗ U`, the *spanning* half of DLM3's PBW step;
   * **`bottomProjectionOfDisjoint`** — in this file the datum is reduced to injectivity plus
     directness; the later Euler-operator theorem `levCover_iSupIndep` discharges directness, so
     only bottom injectivity remains;
   * **`indDefectVec_bottom_eq_zero_of_level_neg`** — the bottom defect vanishes *outright* (not
     merely after pairing) whenever `wa + wb − ℓ − K − 2 < 0`.

## What is NOT proved (named precisely, not faked)

* `BottomProjection` — DLM3's PBW step. Carried as **data** here. The later
  `levCover_iSupIndep` theorem discharges level directness, leaving exactly injectivity of
  `u ↦ [1 ⊗ u]`. Mathlib has no PBW theorem; the project's theorem `VOA.pbw` (field `inducedBottom`,
  proved by `PBWTheorem.bottom_injective`) implies bottom injectivity (`voaPBWBottomInjective`,
  `Modules/ZhuVermaAnArchDLM3PBWAxiom.lean`),
  but it is not used in this file. Concrete adjoint and Heisenberg instances are proved elsewhere
  without `pbw`.
* `DefectPairsToZero` — DLM3's `U(V̂)W ⊆ J` (their Props 4.3/4.6; Lemma 4.4 + Appendix Prop 5.1).
  Carried as a `Prop`; reduced here to `ℓ < 0`, to a single level-matched mode index at the bottom,
  and to (bottom base) + (`V̂`-stability).

Everything below is green and `sorry`-free. Its proof terms are `VOA.pbw`-free and
`#print axioms` reports `[propext, Classical.choice, Quot.sound]`; that report does not include the
explicit independent `BottomProjection`/`DefectPairsToZero` parameters and is not an
unconditionality or satisfiability certificate.

## References
DLM3 (`q-alg/9612010v2`) §4: (4.1)–(4.5), Thm 4.1, Thm 4.2, Props 4.3/4.6/4.7, Lemma 4.4;
DLM2 (`q-alg/9509005`) Prop 6.1, Thm 6.2/6.3;
`ZhuVermaAnArchDLM3Induced` (`IndMod`, `indRho`, `ind_generation`, `IndBar`, `indBarWeakModule`),
`ZhuVermaAnArchDLM3Admissible` (`indBottom`, `indBarBottom`, `omegaN`, `Realization`,
`indBarBottom_injective_iff`), `ZhuVermaAnArchDLM3Level` (`levCover`, `levBar`, `indBarGraded`),
`ZhuVermaAnArchDLM3Zero` (`parabolicRepOfAMod`, `indBarBottom_zhu_equivariant`, `regularAMod`),
`ZhuVermaAnArchMUjacobiClose` (`defectVec`, `defectSubmodule`, `IsInvariant`),
`ZhuVermaAnArchBottomSurvival` (`IsGradedRep`, `defectVec_homogeneous`).
-/

namespace VOA

open VertexOperatorAlgebra
open Module (End)
open scoped BigOperators TensorProduct

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The full dual of a `ℂ`-vector space separates points

DLM3 take `U* = Hom_ℂ(U,ℂ)`, the *full* dual, and never impose any finiteness on `U`.  That is what
makes `J ∩ U = 0` free.  The following is the only property of `U*` they use. -/

/-- **`Hom_ℂ(U,ℂ)` separates points of `U`.**  No finiteness hypothesis: a basis exists for every
`ℂ`-vector space, and a nonzero vector has a nonzero coordinate. -/
theorem eq_zero_of_forall_dual {U : Type u} [AddCommGroup U] [Module ℂ U] {w : U}
    (h : ∀ f : U →ₗ[ℂ] ℂ, f w = 0) : w = 0 := by
  by_contra hw
  obtain ⟨s, ⟨B⟩⟩ := Module.Basis.exists_basis ℂ U
  have hrep : B.repr w ≠ 0 := fun hz => hw (by simpa using congrArg B.repr.symm hz)
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hrep
  exact hi (by simpa [Module.Basis.coord_apply] using h (B.coord i))

namespace VHat

namespace VHatRep

variable {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M]

/-! ## Linearity of the iterate defect in its module argument

`defectVec_add_right` / `defectVec_smul_right` are proved in `ZhuVermaAnArchGradedCloseDeep`; only
the (trivial) zero case is missing, and it is what makes "the defect pairs to zero at `z`" a
*submodule* condition on `z` — the shape the generation principle `ind_generation` consumes. -/

/-- The defect vanishes at `z = 0`. -/
theorem defectVec_zero_right (ρ : VHatRep W M) (htr : ActModeTruncated ρ) (u v : 𝒱) (ℓ K : ℤ) :
    defectVec ρ u v (0 : M) ℓ K = 0 := by
  have := defectVec_smul_right ρ htr (0 : ℂ) u v 0 ℓ K
  rwa [zero_smul, zero_smul] at this

end VHatRep

namespace DLM3

variable {W : VertexOperatorAlgebra 𝒱} {n : ℕ} {U : Type u} [AddCommGroup U] [Module ℂ U]

/-! ## The bottom projection — DLM3's PBW step, carried as data -/

/-- **DLM3's PBW input, minimally packaged.**  DLM3 (4.1) write "the PBW theorem implies that
`M_n(U)(i) = U(V̂)_{i−n}U`", and use it exactly twice: to know that `U` *is* the level-`n` piece of
`M_n(U)`, and to extend `u′ ∈ U*` to `M_n(U)` by zero off level `n`.  Both uses are captured by a
single linear map

* `proj` — the projection `M_n(U) → U`,
* `proj_bottom` — it retracts the bottom map `u ↦ [1 ⊗ u]`,
* `proj_levCover` — it annihilates every level `≠ n`.

At `n = 0` this is *all* of DLM3's PBW input (the length filtration `(4.5)` is vacuous there — see
the module docstring).  It is **data**, not an axiom: Mathlib has no Poincaré–Birkhoff–Witt theorem,
and this file does not use `VOA.pbw` (a theorem; its `inducedBottom` field
supplies it, see below). `bottomProjectionOfIsCompl` shows it is exactly the complementation
statement PBW
supplies. Its exact general boundary is bottom injectivity (level independence is
unconditional). Concrete adjoint and Heisenberg instances are proved axiom-free; the companion
`voaPBWBottomProjection` supplies arbitrary parabolic instances from the generic
relative-induction field of the theorem `VOA.pbw : PBWPrinciple`. -/
structure BottomProjection (P : ParabolicRep W n U) where
  /-- The projection onto the bottom `U` of `M_n(U)`. -/
  proj : IndMod P →ₗ[ℂ] U
  /-- It retracts the bottom map `u ↦ [1 ⊗ u]`. -/
  proj_bottom : ∀ u : U, proj (indBottom P u) = u
  /-- It annihilates every level other than `n` (DLM3: "`U*` annihilates `⨁_{i≠n} M(U)(i)`"). -/
  proj_levCover : ∀ ⦃k : ℤ⦄, k ≠ (n : ℤ) → ∀ ⦃z : IndMod P⦄, z ∈ levCover P k → proj z = 0

namespace BottomProjection

variable {P : ParabolicRep W n U}

/-- A bottom projection forces the bottom map to be injective. -/
theorem indBottom_injective (Pr : BottomProjection P) : Function.Injective (indBottom P) := by
  intro u₁ u₂ h
  rw [← Pr.proj_bottom u₁, ← Pr.proj_bottom u₂, h]

end BottomProjection

/-- **The bottom projection is exactly the PBW complementation statement.**  If the bottom map is
injective and its range is a complement of the span of the *other* levels, the projection exists.
(This is the shape in which PBW delivers `M_n(U)(n) = U`: the ordered monomials with at least one
positive factor span the other levels and meet `1 ⊗ U` trivially.) -/
noncomputable def bottomProjectionOfIsCompl (P : ParabolicRep W n U)
    (hinj : Function.Injective (indBottom P))
    (hc : IsCompl (LinearMap.range (indBottom P))
      (⨆ k : {k : ℤ // k ≠ (n : ℤ)}, levCover P (k : ℤ))) :
    BottomProjection P where
  proj := (LinearEquiv.ofInjective (indBottom P) hinj).symm.toLinearMap.comp
    (Submodule.projectionOnto _ _ hc)
  proj_bottom := by
    intro u
    have hx : (indBottom P u) = ((LinearEquiv.ofInjective (indBottom P) hinj u :
        LinearMap.range (indBottom P)) : IndMod P) := rfl
    rw [LinearMap.comp_apply, hx, Submodule.projectionOnto_apply_left hc]
    exact (LinearEquiv.ofInjective (indBottom P) hinj).symm_apply_apply u
  proj_levCover := by
    intro k hk z hz
    have hmem : z ∈ (⨆ k : {k : ℤ // k ≠ (n : ℤ)}, levCover P (k : ℤ)) :=
      Submodule.mem_iSup_of_mem (⟨k, hk⟩ : {k : ℤ // k ≠ (n : ℤ)}) hz
    have hzero := Submodule.projectionOnto_apply_right hc
      (⟨z, hmem⟩ : ↥(⨆ k : {k : ℤ // k ≠ (n : ℤ)}, levCover P (k : ℤ)))
    rw [LinearMap.comp_apply]
    simp only at hzero
    rw [hzero]
    exact map_zero _

/-! ## The radical `J` (DLM3, after (4.5)) -/

/-- **DLM3's radical**
`J = {v ∈ M_n(U) | ⟨u′, x v⟩ = 0 for all u′ ∈ U*, all x ∈ U(V̂)}`.

Because `U* = Hom_ℂ(U,ℂ)` is the full dual it separates points (`eq_zero_of_forall_dual`), so the
`u′`-quantifier can be dropped: `J = ⋂_{y ∈ U(V̂)} ker (π ∘ ρ(y))`.  `mem_radical_iff_dual` records
that the two descriptions agree. -/
noncomputable def radical {P : ParabolicRep W n U} (Pr : BottomProjection P) :
    Submodule ℂ (IndMod P) where
  carrier := {v | ∀ y : UEnv W, Pr.proj ((indRho P).toAlgHom y v) = 0}
  add_mem' := by
    intro x y hx hy z
    rw [map_add, map_add, hx z, hy z, add_zero]
  zero_mem' := by
    intro y
    rw [map_zero, map_zero]
  smul_mem' := by
    intro c x hx y
    rw [map_smul, map_smul, hx y, smul_zero]

variable {P : ParabolicRep W n U}

@[simp] theorem mem_radical_iff (Pr : BottomProjection P) (v : IndMod P) :
    v ∈ radical Pr ↔ ∀ y : UEnv W, Pr.proj ((indRho P).toAlgHom y v) = 0 := Iff.rfl

/-- **DLM3's literal form of the radical**, with the full dual `U*` reinstated. -/
theorem mem_radical_iff_dual (Pr : BottomProjection P) (v : IndMod P) :
    v ∈ radical Pr ↔
      ∀ (f : U →ₗ[ℂ] ℂ) (y : UEnv W), f (Pr.proj ((indRho P).toAlgHom y v)) = 0 := by
  constructor
  · intro hv f y
    rw [hv y, map_zero]
  · intro hv y
    exact eq_zero_of_forall_dual fun f => hv f y

/-- **`J` is a `V̂`-subrepresentation** — DLM3 Proposition 4.7, free from the definition: the
`U(V̂)`-quantifier in `J` absorbs the extra mode. -/
theorem radical_invariant (Pr : BottomProjection P) :
    VHatRep.IsInvariant (indRho P) (radical Pr) := by
  intro x v hv y
  have hmul : (indRho P).toAlgHom y (indRho P x v) = (indRho P).toAlgHom (y * uι W x) v := by
    rw [map_mul, VHatRep.toAlgHom_uι, Module.End.mul_apply]
  rw [hmul]
  exact hv _

/-- **`J ∩ U = 0`** — DLM3's "Note that `J ∩ U = 0`", in one line: take `x = 1`. -/
theorem BottomProjection.eq_zero_of_indBottom_mem_radical (Pr : BottomProjection P) {u : U}
    (h : indBottom P u ∈ radical Pr) : u = 0 := by
  have h1 := h 1
  rw [map_one, Module.End.one_apply, Pr.proj_bottom] at h1
  exact h1

/-! ## The one remaining input: `U(V̂)W ⊆ J` -/

/-- **DLM3's `U(V̂)W ⊆ J`** (their Propositions 4.3 + 4.6; Proposition 4.7 is already absorbed into
the definition of `radical`).  Every iterate defect of `M_n(U)` pairs to zero against `U*`.

Carried as a `Prop`, **never** an axiom.  It is reduced below to `ℓ < 0`
(`defectPairsToZero_of_neg`), to a single level-matched mode index at the bottom
(`BottomProjection.proj_defect_eq_zero_of_level_ne`), and to (bottom base) + (`V̂`-stability)
(`defectPairsToZero_of_bottom_of_stable`). -/
def DefectPairsToZero (Pr : BottomProjection P) : Prop :=
  ∀ (a b : 𝒱) (z : IndMod P) (ℓ K : ℤ), VHatRep.defectVec (indRho P) a b z ℓ K ∈ radical Pr

/-- The defect submodule of `M_n(U)` — the kernel of the defect quotient `M̄_n(U)` — is contained in
the radical.  (`radical` is invariant and, by hypothesis, covers the defect set; the defect
submodule is the least such.) -/
theorem defectSubmodule_le_radical (Pr : BottomProjection P) (h : DefectPairsToZero Pr) :
    VHatRep.defectSubmodule (indRho P) ≤ radical Pr := by
  refine sInf_le ⟨?_, radical_invariant Pr⟩
  rintro t ⟨a, b, z, ℓ, K, rfl⟩
  exact h a b z ℓ K

/-! ## Survival -/

/-- **`U` survives the defect quotient.**  DLM3's `J ∩ U = 0` transported through
`U(V̂)W ⊆ J`: the bottom map `U → M̄_n(U)` is injective. -/
theorem indBarBottom_injective_of_defectPairsToZero (Pr : BottomProjection P)
    (h : DefectPairsToZero Pr) : Function.Injective (indBarBottom P) := by
  intro u₁ u₂ h12
  rw [indBarBottom_apply, indBarBottom_apply, Submodule.Quotient.eq] at h12
  rw [← map_sub] at h12
  have hrad : indBottom P (u₁ - u₂) ∈ radical Pr := defectSubmodule_le_radical Pr h h12
  have := Pr.eq_zero_of_indBottom_mem_radical hrad
  exact sub_eq_zero.mp this

/-- **The separating realization.**  Feeding the survival statement back into the proved
equivalence `indBarBottom_injective_iff`: `M̄_n(U)` itself realizes `U` faithfully. -/
noncomputable def separatingRealization (Pr : BottomProjection P) (h : DefectPairsToZero Pr) :
    {R : Realization W n U P // R.Separates} :=
  ⟨indBarRealization P, indBarBottom_injective_of_defectPairsToZero Pr h⟩

/-- **DLM3 Theorem 4.1 / 4.2 at the level of the bottom map.**  Given the two carried inputs, the
weak `𝒱`-module `M̄_n(U)` (`indBarWeakModule`, with its level family `indBarGraded`) contains `U`:

1. the bottom map is **injective**;
2. its image lies in the level-`n` piece `M̄_n(U)(n)`;
3. its image consists of `n`-th lowest weight vectors, `Ω_n(M̄_n(U))` (DLM3 (3.3));
4. it intertwines the `P_n`-action on `U` with the `V̂`-action.

No finite-dimensionality of `U` is used. -/
theorem survival (Pr : BottomProjection P) (h : DefectPairsToZero Pr) :
    Function.Injective (indBarBottom P) ∧
      (∀ u : U, indBarBottom P u ∈ levBar P (n : ℤ)) ∧
      (∀ u : U, indBarBottom P u ∈ omegaN W n (indBarRho P)) ∧
      (∀ (g : Pn W n) (u : U),
        indBarBottom P (P.act g u) = indBarRho P (g : VHatCarrier W) (indBarBottom P u)) :=
  ⟨indBarBottom_injective_of_defectPairsToZero Pr h, indBarBottom_mem_levBar P,
    indBarBottom_mem_omegaN P, indBarBottom_equivariant P⟩

/-- **The `n = 0` main theorem — an admissible module whose bottom is `U` as an `A(𝒱)`-module.**
For a bundled `A(𝒱)`-module `U`, `M̄_0(U) = IndBar (parabolicRepOfAMod W U)` is a weak `𝒱`-module
(`indBarWeakModule`) with a spanning level family (`indBarGraded`), and the bottom map
`U → M̄_0(U)` is injective, lands in level `0` and in `Ω_0`, and is **`A(𝒱)`-equivariant**:
`[1 ⊗ ρ([a])u] = o(a)·[1 ⊗ u]` for homogeneous `a ∈ 𝒱_w`, where `o(a) = a₍w₋₁₎`.

This is exactly DLM3 Theorem 4.1 at `n = 0` — Zhu's "every `A(𝒱)`-module is the bottom of an
admissible module" — modulo the two named inputs `BottomProjection` and `DefectPairsToZero`. -/
theorem survival_zero (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (Pr : BottomProjection (parabolicRepOfAMod W U)) (h : DefectPairsToZero Pr) :
    Function.Injective (indBarBottom (parabolicRepOfAMod W U)) ∧
      (∀ u : U.carrier, indBarBottom (parabolicRepOfAMod W U) u
        ∈ levBar (parabolicRepOfAMod W U) ((0 : ℕ) : ℤ)) ∧
      (∀ u : U.carrier, indBarBottom (parabolicRepOfAMod W U) u
        ∈ omegaN W 0 (indBarRho (parabolicRepOfAMod W U))) ∧
      (∀ {w : ℤ} {a : 𝒱}, a ∈ W.grading w → ∀ u : U.carrier,
        indBarBottom (parabolicRepOfAMod W U) (U.ρ (_root_.VOA.mk W a) u)
          = (indBarRho (parabolicRepOfAMod W U)).actMode a (w - 1)
              (indBarBottom (parabolicRepOfAMod W U) u)) :=
  ⟨indBarBottom_injective_of_defectPairsToZero Pr h,
    indBarBottom_mem_levBar (parabolicRepOfAMod W U),
    indBarBottom_mem_omegaN (parabolicRepOfAMod W U),
    fun ha u => indBarBottom_zhu_equivariant W U ha u⟩

/-! ## Reduction 1 — only `ℓ < 0` has content

`ind_moduleIterate_nonneg` says the `ℓ ≥ 0` half of the iterate identity holds on `M_n(U)` itself,
*before* any quotient.  So every `ℓ ≥ 0` defect is literally zero and `DefectPairsToZero` is a
statement about `ℓ < 0` only — DLM3's associativity direction. -/

/-- **Every `ℓ ≥ 0` defect of `M_n(U)` vanishes identically.** -/
theorem indDefectVec_nonneg (P : ParabolicRep W n U) (a b : 𝒱) (z : IndMod P) (j : ℕ) (K : ℤ) :
    VHatRep.defectVec (indRho P) a b z (j : ℤ) K = 0 := by
  rw [VHatRep.defectVec, ind_moduleIterate_nonneg P a b z j K, sub_self]

/-- **`DefectPairsToZero` has content only at `ℓ < 0`.** -/
theorem defectPairsToZero_of_neg (Pr : BottomProjection P)
    (h : ∀ (a b : 𝒱) (z : IndMod P) (ℓ K : ℤ), ℓ < 0 →
      VHatRep.defectVec (indRho P) a b z ℓ K ∈ radical Pr) :
    DefectPairsToZero Pr := by
  intro a b z ℓ K
  rcases lt_or_ge ℓ 0 with hl | hl
  · exact h a b z ℓ K hl
  · obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le hl
    rw [indDefectVec_nonneg]
    exact Submodule.zero_mem _

/-! ## Reduction 2 — the defect is homogeneous, so only one mode index survives

DLM3 use "`⟨u′, M_n(U)(m)⟩ = 0 if `m ≠ n`" at every step of Lemma 4.4.  Its formal content here is
that `indRho P` is a graded representation for the level family `levCover P` (`actMode_levCover`),
whence the proved `defectVec_homogeneous` puts the whole defect in a *single* level. -/

/-- The induced representation is graded by the level family (DLM3 (4.1)). -/
theorem indRho_isGradedRep (P : ParabolicRep W n U) :
    VHatRep.IsGradedRep (indRho P) (levCover P) :=
  fun _ _ ha _ _ _ hx => actMode_levCover P ha hx

/-- The level shift for a general homogeneous element of `V̂` (not just a single mode): `V̂(e)`
carries `M_n(U)(c)` into `M_n(U)(c+e)`. -/
theorem indRho_deg_levCover (P : ParabolicRep W n U) {e c : ℤ} {x : VHatCarrier W}
    (hx : x ∈ deg W e) {z : IndMod P} (hz : z ∈ levCover P c) :
    indRho P x z ∈ levCover P (c + e) := by
  refine Submodule.span_induction
    (p := fun x _ => indRho P x z ∈ levCover P (c + e)) ?_ ?_ ?_ ?_ hx
  · rintro x ⟨w, m, a, ha, hd, rfl⟩
    have := actMode_levCover P (p := m) ha hz
    rw [VHatRep.actMode_def] at this
    rwa [hd] at this
  · dsimp only
    rw [map_zero]
    exact Submodule.zero_mem _
  · intro x₁ x₂ _ _ h₁ h₂
    rw [map_add]
    exact Submodule.add_mem _ h₁ h₂
  · intro c' x₁ _ h₁
    rw [map_smul]
    exact Submodule.smul_mem _ _ h₁

/-- **Homogeneity of the defect on `M_n(U)`**: for homogeneous `a ∈ 𝒱_{wa}`, `b ∈ 𝒱_{wb}` and `z`
at level `d`, the whole defect `δ(a,b,z,ℓ,K)` lies in the single level `d + (wa+wb−ℓ−K−2)`. -/
theorem indDefectVec_mem_levCover (P : ParabolicRep W n U) {wa wb : ℤ} {a b : 𝒱}
    (ha : a ∈ W.grading wa) (hb : b ∈ W.grading wb) {d : ℤ} {z : IndMod P}
    (hz : z ∈ levCover P d) (ℓ K : ℤ) :
    VHatRep.defectVec (indRho P) a b z ℓ K ∈ levCover P (d + (wa + wb - ℓ - K - 2)) :=
  VHatRep.defectVec_homogeneous (indRho_isGradedRep P) (ind_actModeTruncated P) ha hb hz ℓ K

/-- **The level selection rule.**  `π` annihilates the defect outright unless the level matches.
At the bottom (`d = n`) this leaves, for each homogeneous pair `(a,b)` and each `ℓ`, the *single*
mode index `K = wa + wb − ℓ − 2`. -/
theorem BottomProjection.proj_defect_eq_zero_of_level_ne (Pr : BottomProjection P) {wa wb : ℤ}
    {a b : 𝒱} (ha : a ∈ W.grading wa) (hb : b ∈ W.grading wb) {d : ℤ} {z : IndMod P}
    (hz : z ∈ levCover P d) (ℓ K : ℤ) (hne : d + (wa + wb - ℓ - K - 2) ≠ (n : ℤ)) :
    Pr.proj (VHatRep.defectVec (indRho P) a b z ℓ K) = 0 :=
  Pr.proj_levCover hne (indDefectVec_mem_levCover P ha hb hz ℓ K)

/-- The bottom case of the level selection rule: for `z = [1 ⊗ u]`, only `K = wa + wb − ℓ − 2`
survives. -/
theorem BottomProjection.proj_defect_bottom_eq_zero_of_ne (Pr : BottomProjection P) {wa wb : ℤ}
    {a b : 𝒱} (ha : a ∈ W.grading wa) (hb : b ∈ W.grading wb) (u : U) (ℓ K : ℤ)
    (hne : K ≠ wa + wb - ℓ - 2) :
    Pr.proj (VHatRep.defectVec (indRho P) a b (indBottom P u) ℓ K) = 0 :=
  Pr.proj_defect_eq_zero_of_level_ne ha hb (indBottom_mem_levCover P u) ℓ K
    (by intro hc; exact hne (by omega))

/-! ## Reduction 3 — generation: base at the bottom `+` `V̂`-stability

DLM3's Proposition 4.3 is the base case (`u ∈ U`) and their Proposition 4.6 propagates it from `U`
to all of `M_n(U)`; Proposition 4.7 is already absorbed into the definition of `radical`.  Here the
propagation is packaged in the exact form the repo's generation principle `ind_generation` wants:
the set of vectors whose defects lie in the radical is a *submodule*, so if it contains the bottom
and is stable under the loop modes it is everything. -/

/-- The set of module vectors whose iterate defects all lie in the radical.  A submodule, by the
proved linearity of `defectVec` in its module argument. -/
noncomputable def survSet (Pr : BottomProjection P) : Submodule ℂ (IndMod P) where
  carrier := {z | ∀ (a b : 𝒱) (ℓ K : ℤ),
    VHatRep.defectVec (indRho P) a b z ℓ K ∈ radical Pr}
  add_mem' := by
    intro x y hx hy a b ℓ K
    rw [VHatRep.defectVec_add_right (indRho P) (ind_actModeTruncated P)]
    exact Submodule.add_mem _ (hx a b ℓ K) (hy a b ℓ K)
  zero_mem' := by
    intro a b ℓ K
    rw [VHatRep.defectVec_zero_right (indRho P) (ind_actModeTruncated P)]
    exact Submodule.zero_mem _
  smul_mem' := by
    intro c x hx a b ℓ K
    rw [VHatRep.defectVec_smul_right (indRho P) (ind_actModeTruncated P)]
    exact Submodule.smul_mem _ _ (hx a b ℓ K)

@[simp] theorem mem_survSet (Pr : BottomProjection P) (z : IndMod P) :
    z ∈ survSet Pr ↔
      ∀ (a b : 𝒱) (ℓ K : ℤ), VHatRep.defectVec (indRho P) a b z ℓ K ∈ radical Pr := Iff.rfl

/-- **The generation reduction.**  `DefectPairsToZero` — DLM3's `U(V̂)W ⊆ J` — follows from

* `hbot` (DLM3 **Proposition 4.3**): the defects *at the bottom* `[1 ⊗ u]` lie in the radical;
* `hstab` (DLM3 **Proposition 4.6**): that property propagates along the `V̂`-action.

Nothing else is needed: `ind_generation` is PBW-free. -/
theorem defectPairsToZero_of_bottom_of_stable (Pr : BottomProjection P)
    (hbot : ∀ (u : U) (a b : 𝒱) (ℓ K : ℤ),
      VHatRep.defectVec (indRho P) a b (indBottom P u) ℓ K ∈ radical Pr)
    (hstab : ∀ (x : VHatCarrier W) (z : IndMod P), z ∈ survSet Pr → indRho P x z ∈ survSet Pr) :
    DefectPairsToZero Pr := by
  have htop : survSet Pr = ⊤ :=
    ind_generation P (survSet Pr) (fun u => by
      have := hbot u
      rwa [indBottom_apply] at this) hstab
  intro a b z ℓ K
  have hz : z ∈ survSet Pr := by rw [htop]; trivial
  exact hz a b ℓ K

/-! ## Reduction 4 — the level structure of `M_0(U)`, **PBW-free**

DLM3 read three facts off their PBW decomposition `M_n(U)(i) = U(V̂)_{i−n}U`: the levels below the
bottom vanish, the bottom level is `U`, and the whole decomposition is direct.  At `n = 0` the first
two are **provable without PBW**, by a straightening argument carried out on the *module* rather
than on `U(V̂)`:

`P₀ = V̂_{≤0}`, so a mode of negative degree annihilates `1 ⊗ U`; commuting such a mode to the right
through a word of non-negative modes produces, by `⁅V̂(d),V̂(e)⁆ ⊆ V̂(d+e)`, only shorter words.
Hence `M_0(U)` is spanned by *non-negative* words applied to the bottom (`posLevel`).  A
non-negative word of total degree `d < 0` is impossible, and one of total degree `0` has **all**
factors of degree `0` — and degree-`0` modes lie in `P₀` and act on `1 ⊗ U` through `P.act`.

The residual PBW content is therefore *only* the directness (`bottomProjectionOfDisjoint`). -/

section LevelZero

variable {Q : ParabolicRep W 0 U}

/-- One step of the non-negative word orbit: the span of `x·z` with `x ∈ V̂(e)` and `z ∈ S`. -/
noncomputable def modeStep (Q : ParabolicRep W 0 U) (e : ℤ) (S : Submodule ℂ (IndMod Q)) :
    Submodule ℂ (IndMod Q) :=
  Submodule.span ℂ {t | ∃ x ∈ deg W e, ∃ z ∈ S, t = indRho Q x z}

theorem mem_modeStep {e : ℤ} {S : Submodule ℂ (IndMod Q)} {x : VHatCarrier W} (hx : x ∈ deg W e)
    {z : IndMod Q} (hz : z ∈ S) : indRho Q x z ∈ modeStep Q e S :=
  Submodule.subset_span ⟨x, hx, z, hz, rfl⟩

theorem modeStep_bot (Q : ParabolicRep W 0 U) (e : ℤ) : modeStep Q e ⊥ = ⊥ := by
  rw [modeStep, Submodule.span_eq_bot]
  rintro t ⟨x, _, z, hz, rfl⟩
  rw [Submodule.mem_bot] at hz
  rw [hz, map_zero]

/-- **The non-negative word orbit of the bottom**, filtered by word length `r` and graded by the
total degree `d`. -/
noncomputable def posOrbit (Q : ParabolicRep W 0 U) : ℕ → ℤ → Submodule ℂ (IndMod Q)
  | 0, d => if d = 0 then LinearMap.range (indBottom Q) else ⊥
  | r + 1, d => ⨆ e : ℕ, modeStep Q (e : ℤ) (posOrbit Q r (d - (e : ℤ)))

theorem posOrbit_zero (Q : ParabolicRep W 0 U) (d : ℤ) :
    posOrbit Q 0 d = if d = 0 then LinearMap.range (indBottom Q) else ⊥ := rfl

theorem posOrbit_succ (Q : ParabolicRep W 0 U) (r : ℕ) (d : ℤ) :
    posOrbit Q (r + 1) d = ⨆ e : ℕ, modeStep Q (e : ℤ) (posOrbit Q r (d - (e : ℤ))) := rfl

/-- **The degree-`d` piece of the orbit**, `⨆_r`. -/
noncomputable def posLevel (Q : ParabolicRep W 0 U) (d : ℤ) : Submodule ℂ (IndMod Q) :=
  ⨆ r : ℕ, posOrbit Q r d

theorem posOrbit_le_posLevel (Q : ParabolicRep W 0 U) (r : ℕ) (d : ℤ) :
    posOrbit Q r d ≤ posLevel Q d :=
  le_iSup (fun r : ℕ => posOrbit Q r d) r

/-- **A non-negative word cannot have negative total degree.** -/
theorem posOrbit_eq_bot_of_neg (Q : ParabolicRep W 0 U) (r : ℕ) {d : ℤ} (hd : d < 0) :
    posOrbit Q r d = ⊥ := by
  induction r generalizing d with
  | zero => rw [posOrbit_zero, if_neg (by omega)]
  | succ r ih =>
    rw [posOrbit_succ, iSup_eq_bot]
    intro e
    rw [ih (d := d - (e : ℤ)) (by omega), modeStep_bot]

theorem posLevel_eq_bot_of_neg (Q : ParabolicRep W 0 U) {d : ℤ} (hd : d < 0) :
    posLevel Q d = ⊥ := by
  rw [posLevel, iSup_eq_bot]
  intro r
  exact posOrbit_eq_bot_of_neg Q r hd

theorem indBottom_mem_posOrbit (Q : ParabolicRep W 0 U) (u : U) :
    indBottom Q u ∈ posOrbit Q 0 0 := by
  rw [posOrbit_zero, if_pos rfl]
  exact ⟨u, rfl⟩

theorem indBottom_mem_posLevel (Q : ParabolicRep W 0 U) (u : U) :
    indBottom Q u ∈ posLevel Q 0 :=
  posOrbit_le_posLevel Q 0 0 (indBottom_mem_posOrbit Q u)

/-- Appending a **non-negative** mode to the orbit: the easy half of the straightening. -/
theorem posLevel_indRho_nonneg (Q : ParabolicRep W 0 U) {e : ℕ} {x : VHatCarrier W}
    (hx : x ∈ deg W (e : ℤ)) {d : ℤ} {z : IndMod Q} (hz : z ∈ posLevel Q d) :
    indRho Q x z ∈ posLevel Q (d + (e : ℤ)) := by
  refine Submodule.iSup_induction (fun r : ℕ => posOrbit Q r d)
    (motive := fun z => indRho Q x z ∈ posLevel Q (d + (e : ℤ))) hz ?_ ?_ ?_
  · intro r z hz'
    refine posOrbit_le_posLevel Q (r + 1) _ ?_
    rw [posOrbit_succ]
    refine Submodule.mem_iSup_of_mem e ?_
    rw [show d + (e : ℤ) - (e : ℤ) = d from by ring]
    exact mem_modeStep hx hz'
  · dsimp only
    rw [map_zero]
    exact Submodule.zero_mem _
  · intro z₁ z₂ h₁ h₂
    rw [map_add]
    exact Submodule.add_mem _ h₁ h₂

/-- Negative-degree modes annihilate the bottom of `M_0(U)`: at `n = 0` the parabolic is `V̂_{≤0}`
and the deep part is everything of negative degree. -/
theorem indRho_indBottom_eq_zero_of_neg (Q : ParabolicRep W 0 U) {e : ℤ} (he : e < 0)
    {x : VHatCarrier W} (hx : x ∈ deg W e) (u : U) : indRho Q x (indBottom Q u) = 0 := by
  have hdeep : x ∈ deepPart W 0 := by
    refine degSpan_mono W (S := {e}) (T := deepSet 0) ?_ ?_
    · intro d hd
      simp only [Set.mem_singleton_iff] at hd
      simp only [deepSet, Set.mem_setOf_eq]
      omega
    · rwa [degSpan_singleton]
  exact indBottom_mem_omegaN Q u x hdeep

/-- **The straightening step.**  A mode of *arbitrary* degree carries the non-negative word orbit
into the non-negative word orbit: commuting it rightwards uses only `⁅V̂(d),V̂(e)⁆ ⊆ V̂(d+e)` and
shortens the word, and at the bottom a negative mode simply dies. -/
theorem posLevel_indRho_orbit (Q : ParabolicRep W 0 U) :
    ∀ (r : ℕ) {e d : ℤ} {x : VHatCarrier W}, x ∈ deg W e → ∀ {z : IndMod Q},
      z ∈ posOrbit Q r d → indRho Q x z ∈ posLevel Q (d + e) := by
  intro r
  induction r with
  | zero =>
    intro e d x hx z hz
    by_cases hd : d = 0
    · subst hd
      rw [posOrbit_zero, if_pos rfl] at hz
      obtain ⟨u, rfl⟩ := hz
      rcases lt_or_ge e 0 with he | he
      · rw [indRho_indBottom_eq_zero_of_neg Q he hx u]
        exact Submodule.zero_mem _
      · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le he
        exact posLevel_indRho_nonneg Q hx (indBottom_mem_posLevel Q u)
    · rw [posOrbit_zero, if_neg hd, Submodule.mem_bot] at hz
      rw [hz, map_zero]
      exact Submodule.zero_mem _
  | succ r ih =>
    intro e d x hx z hz
    rw [posOrbit_succ] at hz
    refine Submodule.iSup_induction
      (fun e' : ℕ => modeStep Q (e' : ℤ) (posOrbit Q r (d - (e' : ℤ))))
      (motive := fun z => indRho Q x z ∈ posLevel Q (d + e)) hz ?_ ?_ ?_
    · intro e' z hz'
      refine Submodule.span_induction
        (p := fun z _ => indRho Q x z ∈ posLevel Q (d + e)) ?_ ?_ ?_ ?_ hz'
      · rintro t ⟨x', hx', w, hw, rfl⟩
        have hcomm : indRho Q x (indRho Q x' w)
            = indRho Q x' (indRho Q x w) + indRho Q ⁅x, x'⁆ w := by
          have hlie := Q |> fun _ => (indRho Q).map_lie x x'
          rw [hlie, Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply]
          abel
        rw [hcomm]
        refine Submodule.add_mem _ ?_ ?_
        · have h1 : indRho Q x w ∈ posLevel Q (d - (e' : ℤ) + e) := ih hx hw
          have h2 := posLevel_indRho_nonneg Q (e := e') hx' h1
          rwa [show d - (e' : ℤ) + e + (e' : ℤ) = d + e from by ring] at h2
        · have hbr : ⁅x, x'⁆ ∈ deg W (e + (e' : ℤ)) := deg_bracket_deg W hx hx'
          have h3 := ih hbr hw
          rwa [show d - (e' : ℤ) + (e + (e' : ℤ)) = d + e from by ring] at h3
      · dsimp only
        rw [map_zero]
        exact Submodule.zero_mem _
      · intro z₁ z₂ _ _ h₁ h₂
        rw [map_add]
        exact Submodule.add_mem _ h₁ h₂
      · intro c z₁ _ h₁
        rw [map_smul]
        exact Submodule.smul_mem _ _ h₁
    · dsimp only
      rw [map_zero]
      exact Submodule.zero_mem _
    · intro z₁ z₂ h₁ h₂
      rw [map_add]
      exact Submodule.add_mem _ h₁ h₂

/-- The straightening step, on the whole degree-`d` piece. -/
theorem posLevel_indRho (Q : ParabolicRep W 0 U) {e d : ℤ} {x : VHatCarrier W}
    (hx : x ∈ deg W e) {z : IndMod Q} (hz : z ∈ posLevel Q d) :
    indRho Q x z ∈ posLevel Q (d + e) := by
  refine Submodule.iSup_induction (fun r : ℕ => posOrbit Q r d)
    (motive := fun z => indRho Q x z ∈ posLevel Q (d + e)) hz ?_ ?_ ?_
  · intro r z hz'
    exact posLevel_indRho_orbit Q r hx hz'
  · dsimp only
    rw [map_zero]
    exact Submodule.zero_mem _
  · intro z₁ z₂ h₁ h₂
    rw [map_add]
    exact Submodule.add_mem _ h₁ h₂

/-! ### The identification `M_0(U)(d) = posLevel d` -/

/-- Every generator `[y ⊗ u]` with `y` a word of total degree `d` lies in the non-negative orbit
`posLevel d` (induction on the word length, straightening at each step). -/
theorem indMk_mem_posLevel_len (Q : ParabolicRep W 0 U) :
    ∀ (r : ℕ) {d : ℤ} {y : UEnv W}, y ∈ uenvDegLen W r d → ∀ u : U,
      indMk Q (y ⊗ₜ[ℂ] u) ∈ posLevel Q d := by
  intro r
  induction r with
  | zero =>
    intro d y hy u
    rw [uenvDegLen_zero] at hy
    by_cases hd : d = 0
    · subst hd
      rw [if_pos rfl] at hy
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
      rw [← TensorProduct.smul_tmul', map_smul]
      exact Submodule.smul_mem _ _ (indBottom_mem_posLevel Q u)
    · rw [if_neg hd, Submodule.mem_bot] at hy
      rw [hy, TensorProduct.zero_tmul, map_zero]
      exact Submodule.zero_mem _
  | succ r ih =>
    intro d y hy u
    rw [uenvDegLen_succ] at hy
    refine Submodule.iSup_induction (fun e : ℤ => uenvStep W e (uenvDegLen W r (d - e)))
      (motive := fun y => indMk Q (y ⊗ₜ[ℂ] u) ∈ posLevel Q d) hy ?_ ?_ ?_
    · intro e y hy'
      refine Submodule.span_induction
        (p := fun y _ => indMk Q (y ⊗ₜ[ℂ] u) ∈ posLevel Q d) ?_ ?_ ?_ ?_ hy'
      · rintro t ⟨x, hx, y', hy'', rfl⟩
        have hstep : indMk Q ((uι W x * y') ⊗ₜ[ℂ] u) = indRho Q x (indMk Q (y' ⊗ₜ[ℂ] u)) := by
          rw [indRho_apply, indActEnd_mk]
        rw [hstep]
        have := posLevel_indRho Q hx (ih hy'' u)
        rwa [show d - e + e = d from by ring] at this
      · dsimp only
        rw [TensorProduct.zero_tmul, map_zero]
        exact Submodule.zero_mem _
      · intro y₁ y₂ _ _ h₁ h₂
        rw [TensorProduct.add_tmul, map_add]
        exact Submodule.add_mem _ h₁ h₂
      · intro c y₁ _ h₁
        rw [← TensorProduct.smul_tmul', map_smul]
        exact Submodule.smul_mem _ _ h₁
    · dsimp only
      rw [TensorProduct.zero_tmul, map_zero]
      exact Submodule.zero_mem _
    · intro y₁ y₂ h₁ h₂
      rw [TensorProduct.add_tmul, map_add]
      exact Submodule.add_mem _ h₁ h₂

theorem levCover_le_posLevel (Q : ParabolicRep W 0 U) (d : ℤ) :
    levCover Q d ≤ posLevel Q d := by
  refine Submodule.span_le.mpr ?_
  rintro t ⟨y, hy, u, rfl⟩
  rw [Nat.cast_zero, sub_zero] at hy
  refine Submodule.iSup_induction (fun r : ℕ => uenvDegLen W r d)
    (motive := fun y => indMk Q (y ⊗ₜ[ℂ] u) ∈ posLevel Q d) hy ?_ ?_ ?_
  · intro r y hy'
    exact indMk_mem_posLevel_len Q r hy' u
  · dsimp only
    rw [TensorProduct.zero_tmul, map_zero]
    exact Submodule.zero_mem _
  · intro y₁ y₂ h₁ h₂
    rw [TensorProduct.add_tmul, map_add]
    exact Submodule.add_mem _ h₁ h₂

theorem posOrbit_le_levCover (Q : ParabolicRep W 0 U) :
    ∀ (r : ℕ) (d : ℤ), posOrbit Q r d ≤ levCover Q d := by
  intro r
  induction r with
  | zero =>
    intro d
    rw [posOrbit_zero]
    by_cases hd : d = 0
    · subst hd
      rw [if_pos rfl]
      rintro t ⟨u, rfl⟩
      have := indBottom_mem_levCover Q u
      rwa [Nat.cast_zero] at this
    · rw [if_neg hd]
      exact bot_le
  | succ r ih =>
    intro d
    rw [posOrbit_succ]
    refine iSup_le fun e => Submodule.span_le.mpr ?_
    rintro t ⟨x, hx, z, hz, rfl⟩
    have := indRho_deg_levCover Q hx (ih (d - (e : ℤ)) hz)
    rwa [show d - (e : ℤ) + (e : ℤ) = d from by ring] at this

/-- **`M_0(U)(d)` is exactly the degree-`d` non-negative orbit of the bottom** — the PBW-free
straightening, in full. -/
theorem levCover_eq_posLevel (Q : ParabolicRep W 0 U) (d : ℤ) :
    levCover Q d = posLevel Q d :=
  le_antisymm (levCover_le_posLevel Q d)
    (iSup_le fun r => posOrbit_le_levCover Q r d)

/-- **`M_0(U)(d) = 0` for `d < 0`** — DLM3's "`M̄_n(U)(m) = 0` if `m < 0`", **PBW-free**. -/
theorem levCover_eq_bot_of_neg (Q : ParabolicRep W 0 U) {d : ℤ} (hd : d < 0) :
    levCover Q d = ⊥ := by
  rw [levCover_eq_posLevel, posLevel_eq_bot_of_neg Q hd]

theorem posOrbit_zero_le_range (Q : ParabolicRep W 0 U) :
    ∀ r : ℕ, posOrbit Q r 0 ≤ LinearMap.range (indBottom Q) := by
  intro r
  induction r with
  | zero => rw [posOrbit_zero, if_pos rfl]
  | succ r ih =>
    rw [posOrbit_succ]
    refine iSup_le fun e => ?_
    rcases Nat.eq_zero_or_pos e with he | he
    · subst he
      refine Submodule.span_le.mpr ?_
      rintro t ⟨x, hx, z, hz, rfl⟩
      obtain ⟨u, rfl⟩ := ih (by simpa using hz)
      have hxp : x ∈ parabolic W 0 := by
        refine degSpan_mono W (S := {(0 : ℤ)}) (T := parabolicSet 0) ?_ ?_
        · intro d hd
          simp only [Set.mem_singleton_iff] at hd
          exact Or.inl hd
        · rw [degSpan_singleton]
          simpa using hx
      rw [← indBottom_equivariant Q (⟨x, hxp⟩ : Pn W 0) u]
      exact ⟨_, rfl⟩
    · rw [posOrbit_eq_bot_of_neg Q r (by omega), modeStep_bot]
      exact bot_le

/-- **`M_0(U)(0) = 1 ⊗ U`** — the bottom level of `M_0(U)` is *exactly* the image of `U`,
**PBW-free**.  (A non-negative word of total degree `0` has all its factors in degree `0`, and
degree-`0` modes lie in `P₀`, acting on `1 ⊗ U` through `P.act`.)  This is the "spanning" half of
DLM3's PBW step; the remaining half is the *directness* isolated in
`bottomProjectionOfDisjoint`. -/
theorem levCover_zero_eq_range (Q : ParabolicRep W 0 U) :
    levCover Q 0 = LinearMap.range (indBottom Q) := by
  refine le_antisymm ?_ ?_
  · rw [levCover_eq_posLevel]
    exact iSup_le fun r => posOrbit_zero_le_range Q r
  · rintro t ⟨u, rfl⟩
    have := indBottom_mem_levCover Q u
    rwa [Nat.cast_zero] at this

/-- **The PBW residual, sharpened: only *directness* is missing.**  Given injectivity of the
bottom map and disjointness of the bottom level from the other levels, the `BottomProjection` datum
exists — the *spanning* half (`levCover_zero_eq_range`, `levCover_spanning`) is proved. -/
noncomputable def bottomProjectionOfDisjoint (Q : ParabolicRep W 0 U)
    (hinj : Function.Injective (indBottom Q))
    (hdisj : Disjoint (LinearMap.range (indBottom Q))
      (⨆ k : {k : ℤ // k ≠ ((0 : ℕ) : ℤ)}, levCover Q (k : ℤ))) :
    BottomProjection Q := by
  refine bottomProjectionOfIsCompl Q hinj ⟨hdisj, ?_⟩
  rw [codisjoint_iff, eq_top_iff, ← levCover_spanning Q]
  refine iSup_le fun k => ?_
  by_cases hk : k = ((0 : ℕ) : ℤ)
  · subst hk
    rw [Nat.cast_zero, levCover_zero_eq_range]
    exact le_sup_left
  · exact le_sup_of_le_right
      (le_iSup (fun k : {k : ℤ // k ≠ ((0 : ℕ) : ℤ)} => levCover Q (k : ℤ)) ⟨k, hk⟩)

/-! ### Consequences for the bottom defect -/

/-- **A negative-degree mode annihilates the bottom** (`P₀ = V̂_{≤0}`, deep part `= V̂_{<0}`). -/
theorem indBottom_actMode_eq_zero_of_neg (Q : ParabolicRep W 0 U) {w m : ℤ} {a : 𝒱}
    (ha : a ∈ W.grading w) (hm : w - m - 1 < 0) (u : U) :
    (indRho Q).actMode a m (indBottom Q u) = 0 :=
  indRho_indBottom_eq_zero_of_neg Q hm (gen_mem_deg W ha m) u

/-- **A degree-`0` mode acts on the bottom through `P₀`** — DLM3's `o(a)·[1 ⊗ u] = [1 ⊗ a·u]`. -/
theorem indBottom_actMode_deg_zero (Q : ParabolicRep W 0 U) {w m : ℤ} {a : 𝒱}
    (ha : a ∈ W.grading w) (hm : w - m - 1 = 0) (u : U) :
    (indRho Q).actMode a m (indBottom Q u)
      = indBottom Q (Q.act ⟨gen W a m, gen_mem_parabolic_of_deg_zero W 0 ha hm⟩ u) :=
  (indBottom_equivariant Q ⟨gen W a m, gen_mem_parabolic_of_deg_zero W 0 ha hm⟩ u).symm

/-- **The bottom defect vanishes outright below the bottom level.**  For homogeneous `a, b` the
defect at `[1 ⊗ u]` lives in level `wa + wb − ℓ − K − 2`, and `M_0(U)` has nothing below level `0`
(`levCover_eq_bot_of_neg`).  Unconditional: no `BottomProjection`, no PBW. -/
theorem indDefectVec_bottom_eq_zero_of_level_neg (Q : ParabolicRep W 0 U) {wa wb : ℤ} {a b : 𝒱}
    (ha : a ∈ W.grading wa) (hb : b ∈ W.grading wb) (u : U) (ℓ K : ℤ)
    (hlev : wa + wb - ℓ - K - 2 < 0) :
    VHatRep.defectVec (indRho Q) a b (indBottom Q u) ℓ K = 0 := by
  have hbot : indBottom Q u ∈ levCover Q (0 : ℤ) := by
    have := indBottom_mem_levCover Q u
    rwa [Nat.cast_zero] at this
  have hmem := indDefectVec_mem_levCover Q ha hb hbot ℓ K
  rw [levCover_eq_bot_of_neg Q (d := 0 + (wa + wb - ℓ - K - 2)) (by omega),
    Submodule.mem_bot] at hmem
  exact hmem

end LevelZero

end DLM3
end VHat
end VOA

-- Axiom check. Explicit assumptions such as `BottomProjection` are not printed here.
