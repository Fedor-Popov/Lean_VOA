/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Core.SingularVector
import VOA.Examples.VirasoroSimple
import Mathlib.Tactic.TFAE

/-!
# Generic scaffolding for simple quotients, and the recipe for `L_k(𝔰𝔩₂)`

`Core/QuotientVOA` already builds the *whole* simple-quotient machine for an **arbitrary**
vertex operator algebra: `QuotVOA.maxGradedIdeal W` is the maximal proper ideal of any `W`
(maximal among **all** proper ideals, `QuotVOA.le_maxGradedIdeal'`, because every ideal of a
VOA is automatically graded, `QuotVOA.isGradedIdeal_of_isIdeal`), `QuotVOA.maxQuotientVOA W`
is the quotient by it, and `QuotVOA.isSimple_maxQuotientVOA'` says that quotient **is
simple** as soon as `W.vacuum ≠ 0`.  No singular vector is needed, and nothing in that
machine is Virasoro-specific.

`Examples/VirasoroSimple` is therefore *only* an instantiation: its §2–§6 do nothing but feed
`virasoroVOA c` and the single Virasoro-specific input `vacVec_ne_zero c` into the generic
machine.  Its §1, by contrast, contains three theorems that are stated for an arbitrary VOA
and are generic in substance (`L_two_omega`, `vacuum_mem_of_conformalVector_mem`,
`isSimple_iff_maxGradedIdeal_eq_bot`); they are merely *housed* in a Virasoro file.  This
file imports them rather than restating them (repo rule: grep before you name — if it exists,
import it), and records that they would be better placed in `Core/QuotientVOA`.

So the honest summary is: **almost nothing new is needed.**  What this file adds is the thin
layer that is genuinely missing, all of it stated for a general
`W : VertexOperatorAlgebra 𝒱`:

## Main results

* §1 **The properness criterion.**  `eq_top_of_mem_grading_zero` — an ideal containing a
  *nonzero degree-`0`* vector is everything; and the resulting equivalences
  `ne_top_iff_vacuum_not_mem`, `inf_grading_zero_eq_bot_iff`,
  `ne_top_iff_inf_grading_zero_eq_bot`, packaged as `tfae_proper`:
  for an ideal `I` of a VOA with `𝟙 ≠ 0`,
  `I ≠ ⊤  ↔  𝟙 ∉ I  ↔  I ⊓ 𝒱₀ = ⊥`.
  `ne_top_iff_not_mem_of_grading_zero_eq_span` is the same test phrased against a
  `𝒱₀ = ℂ ∙ v` hypothesis of the shape the affine file supplies, and
  `vacuum_ne_zero_of_grading_zero_eq_span` extracts `𝟙 ≠ 0` from such a hypothesis.

  ⚠ **`𝒱₀ = ℂ ∙ 𝟙` is not a hypothesis one has to carry**: it is the VOA field
  `vacuum_grade` (CFT type is built into `Core.VertexOperatorAlgebra`).  On the affine side
  `gradingZA_zero_eq_smul_vacuum` is *literally* the proof of that field inside
  `AffineVOA.affineSl2VOA`.  So the "dim 𝒱₀ = 1" hypothesis in the general properness
  criterion is automatic, and the criterion reduces to the vacuum test.

* §2 **The maximal ideal / simple quotient, generically.**  `maxGradedIdeal_ne_top`,
  `maxGradedIdeal_inf_grading_zero_eq_bot`, `maxGradedIdeal_le_iSup_ne_zero`; the descent
  identities `maxQuotientVOA_grading`, `_vacuum`, `_conformalVector`, `_centralCharge`,
  `_mkQ_smul`, `_mkQ_grading`; non-degeneracy `maxQuotientVOA_vacuum_ne_zero`,
  `maxQuotientVOA_nontrivial`; the conformal vector survives when `c ≠ 0`
  (`conformalVector_not_mem_maxGradedIdeal`, `maxQuotientVOA_conformalVector_ne_zero`); and
  the generic-case isomorphism `maxQuotientEquiv` when `maxGradedIdeal W = ⊥`.
  Each of these is the Virasoro statement of `Examples/VirasoroSimple` with `virasoroVOA c`
  replaced by an arbitrary `W`; the Virasoro versions become one-line specialisations.

* §3 **The singular-vector bridge into the maximal ideal.**  This is the link that was
  missing: `Core/SingularVector` proves that a strongly singular vector `s` generates a
  *proper* ideal `(s)`, and `Core/QuotientVOA` proves `maxGradedIdeal` swallows every proper
  ideal, but nothing connected the two.  Here:
  `mem_maxGradedIdeal_of_idealGen_proper` (`s ∈ maxGradedIdeal W`),
  `mkQ_eq_zero_of_idealGen_proper` (**`s ↦ 0` in the simple quotient**),
  `maxGradedIdeal_ne_bot_of_idealGen_proper` (the simple quotient is a *proper* quotient),
  and their form-free specialisations
  `mem_maxGradedIdeal_of_stronglySingular`, `mkQ_eq_zero_of_stronglySingular`,
  `maxGradedIdeal_ne_bot_of_stronglySingular`, `maxQuotientVOA_ne_self_of_stronglySingular`.

* §4 **The recipe** for `L_k(𝔰𝔩₂)`, declaration by declaration, mirroring
  `Examples/VirasoroSimple` lines 183–229 one for one.  Documentation only: the code there is
  inside a docstring, is **never compiled**, and none of its names (`AffineSimple.maxIdealAff`,
  `affineSl2Simple`, `affineSl2Simple_isSimple`, …) exist in the library.

## Status

No `sorry`, `admit` or `native_decide`, and no new axioms.  Instance-independent:
nothing here mentions `WakModule`, `YA`, `affineSl2VOA` or
`Examples/AffineSl2VOAInstance`; §4 is a docstring.  See §5 for the axiom audit.

## References
Gannon §5.1.3 (ideals, simplicity); Lepowsky–Li §4.5; Frenkel–Zhu (the simple affine VOA
`L_k(𝔤)` as `V^k(𝔤)` modulo its maximal proper ideal).
-/

namespace VOA.SimpleQuot

open VOA
open VOA.QuotVOA
open VOA.SingVec

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## §1  The properness criterion

For a VOA the degree-`0` piece is *one-dimensional by definition*: `vacuum_grade` is the
field `𝒱₀ = ℂ ∙ 𝟙`.  Hence "`I` is proper" can be tested purely in degree `0`, which is what
makes properness cheap in every concrete example: one only ever has to know that the vacuum
is nonzero.
-/

section Properness

variable {W : VertexOperatorAlgebra 𝒱} {I : Submodule ℂ 𝒱}

/-- **An ideal containing a nonzero vector of degree `0` is everything.**  Degree `0` is the
line `ℂ ∙ 𝟙` (`vacuum_grade`), so such a vector is `c • 𝟙` with `c ≠ 0`; rescaling by `c⁻¹`
puts `𝟙` in `I`, and `u = u₍₋₁₎𝟙` then puts everything in `I`
(`QuotVOA.eq_top_of_vacuum_mem`).

This is the general form of the degree-`0` obstruction that `Examples/VirasoroNonvanishing`
supplies by hand for Virasoro. -/
theorem eq_top_of_mem_grading_zero (hI : W.IsIdeal I) {x : 𝒱}
    (hx0 : x ∈ W.grading 0) (hxI : x ∈ I) (hx : x ≠ 0) : I = ⊤ := by
  rw [W.vacuum_grade, Submodule.mem_span_singleton] at hx0
  obtain ⟨c, rfl⟩ := hx0
  have hc : c ≠ 0 := by
    intro h
    exact hx (by rw [h, zero_smul])
  refine eq_top_of_vacuum_mem hI ?_
  have hs := I.smul_mem c⁻¹ hxI
  rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at hs

/-- **Contrapositive**: a proper ideal contains no nonzero vector of degree `0`. -/
theorem eq_zero_of_mem_grading_zero_of_ne_top (hI : W.IsIdeal I) (hne : I ≠ ⊤) {x : 𝒱}
    (hx0 : x ∈ W.grading 0) (hxI : x ∈ I) : x = 0 := by
  by_contra hx
  exact hne (eq_top_of_mem_grading_zero hI hx0 hxI hx)

/-- **Properness is the vacuum test.**  `I ≠ ⊤ ↔ 𝟙 ∉ I`, for any ideal `I`. -/
theorem ne_top_iff_vacuum_not_mem (hI : W.IsIdeal I) : I ≠ ⊤ ↔ W.vacuum ∉ I := by
  constructor
  · intro h hv
    exact h (eq_top_of_vacuum_mem hI hv)
  · intro h htop
    exact h (by rw [htop]; exact Submodule.mem_top)

/-- **The vacuum test is the degree-`0` test.**  `𝟙 ∉ I ↔ I ⊓ 𝒱₀ = ⊥`, for any submodule
`I` (no ideal hypothesis), provided `𝟙 ≠ 0`.  Forward is
`QuotVOA.inf_grading_zero_eq_bot`; backward uses `𝟙 ∈ 𝒱₀`. -/
theorem inf_grading_zero_eq_bot_iff (hvac : W.vacuum ≠ 0) :
    I ⊓ W.grading 0 = ⊥ ↔ W.vacuum ∉ I := by
  constructor
  · intro h hv
    have hmem : W.vacuum ∈ I ⊓ W.grading 0 := ⟨hv, W.vacuum_mem⟩
    rw [h, Submodule.mem_bot] at hmem
    exact hvac hmem
  · exact inf_grading_zero_eq_bot

/-- **Properness in degree `0`.**  For an ideal `I` of a VOA with `𝟙 ≠ 0`:
`I ≠ ⊤ ↔ I ⊓ 𝒱₀ = ⊥`. -/
theorem ne_top_iff_inf_grading_zero_eq_bot (hI : W.IsIdeal I) (hvac : W.vacuum ≠ 0) :
    I ≠ ⊤ ↔ I ⊓ W.grading 0 = ⊥ :=
  (ne_top_iff_vacuum_not_mem hI).trans (inf_grading_zero_eq_bot_iff hvac).symm

/-- **The properness criterion, packaged.**  For an ideal `I` of a vertex operator algebra
`W` with nonzero vacuum, the following are equivalent:

1. `I` is proper, `I ≠ ⊤`;
2. `I` misses the vacuum, `𝟙 ∉ I`;
3. `I` meets the (one-dimensional) degree-`0` piece trivially, `I ⊓ 𝒱₀ = ⊥`.

The "dim `𝒱₀ = 1`" hypothesis one might expect is *not* needed as a hypothesis: it is the
VOA field `vacuum_grade`, `𝒱₀ = ℂ ∙ 𝟙`. -/
theorem tfae_proper (hI : W.IsIdeal I) (hvac : W.vacuum ≠ 0) :
    List.TFAE [I ≠ ⊤, W.vacuum ∉ I, I ⊓ W.grading 0 = ⊥] := by
  tfae_have 1 ↔ 2 := ne_top_iff_vacuum_not_mem hI
  tfae_have 2 ↔ 3 := (inf_grading_zero_eq_bot_iff hvac).symm
  tfae_finish

/-- **The criterion against an explicit spanning vector.**  Concrete constructions produce
degree `0` in the shape `𝒱₀ = ℂ ∙ v` for a *named* vector `v` (for affine `𝔰𝔩₂`,
`AffineVOA.gradingZA_zero_eq_span_vacuum : gradingZA k 0 = span ℂ {vacuumA k}`).  One does
not need to know `v = 𝟙` on the nose: any nonzero spanning vector of `𝒱₀` tests properness
just as well. -/
theorem ne_top_iff_not_mem_of_grading_zero_eq_span (hI : W.IsIdeal I) {v : 𝒱}
    (h0 : W.grading 0 = ℂ ∙ v) (hv : v ≠ 0) : I ≠ ⊤ ↔ v ∉ I := by
  have hv0 : v ∈ W.grading 0 := by
    rw [h0]
    exact Submodule.mem_span_singleton_self v
  constructor
  · intro h hvI
    exact h (eq_top_of_mem_grading_zero hI hv0 hvI hv)
  · intro h htop
    exact h (by rw [htop]; exact Submodule.mem_top)

/-- **`𝟙 ≠ 0` comes for free from a nonzero spanning vector of `𝒱₀`.**  If `𝒱₀ = ℂ ∙ v` with
`v ≠ 0`, then `𝟙 ≠ 0`: otherwise `𝒱₀ = ℂ ∙ 𝟙 = ⊥` would force `v = 0`.  So a concrete
`grading_zero_eq_span` lemma already carries the nonvanishing input that the whole
simple-quotient machine needs. -/
theorem vacuum_ne_zero_of_grading_zero_eq_span {v : 𝒱} (h0 : W.grading 0 = ℂ ∙ v)
    (hv : v ≠ 0) : W.vacuum ≠ 0 := by
  intro h
  refine hv ?_
  have hbot : (ℂ ∙ v) = (⊥ : Submodule ℂ 𝒱) := by
    rw [← h0, W.vacuum_grade, h]
    simp
  have hmem : v ∈ (⊥ : Submodule ℂ 𝒱) := by
    rw [← hbot]
    exact Submodule.mem_span_singleton_self v
  simpa using hmem

end Properness

/-! ## §2  The maximal ideal and the simple quotient, for an arbitrary VOA

Everything below is `Examples/VirasoroSimple` §2–§6 with `virasoroVOA c` replaced by a
general `W`.  Once these exist, each Virasoro (or affine, or lattice, …) statement is a
one-line application, and the only input any concrete case has to supply is `W.vacuum ≠ 0`.
-/

section MaxQuotient

variable (W : VertexOperatorAlgebra 𝒱)

/-- **The maximal proper ideal is proper** (`VirasoroSimple.maxIdealVir_ne_top`, generically). -/
theorem maxGradedIdeal_ne_top (hvac : W.vacuum ≠ 0) : maxGradedIdeal W ≠ ⊤ := by
  intro h
  exact vacuum_not_mem_maxGradedIdeal W hvac (by rw [h]; exact Submodule.mem_top)

/-- **The maximal proper ideal meets degree `0` trivially.** -/
theorem maxGradedIdeal_inf_grading_zero_eq_bot (hvac : W.vacuum ≠ 0) :
    maxGradedIdeal W ⊓ W.grading 0 = ⊥ :=
  inf_grading_zero_eq_bot (vacuum_not_mem_maxGradedIdeal W hvac)

/-- **The maximal proper ideal lives in positive-and-negative degrees**, avoiding degree `0`
entirely. -/
theorem maxGradedIdeal_le_iSup_ne_zero (hvac : W.vacuum ≠ 0) :
    maxGradedIdeal W ≤ ⨆ (n : ℤ) (_ : n ≠ 0), W.grading n :=
  le_iSup_ne_zero (maxGradedIdeal_isGradedIdeal W) (vacuum_not_mem_maxGradedIdeal W hvac)

/-! ### The descent identities (all `rfl`) -/

/-- The grading of the simple quotient is the image grading. -/
theorem maxQuotientVOA_grading (n : ℤ) :
    (maxQuotientVOA W).grading n = (W.grading n).map (maxGradedIdeal W).mkQ := rfl

/-- The vacuum descends. -/
theorem maxQuotientVOA_vacuum :
    (maxQuotientVOA W).vacuum = (maxGradedIdeal W).mkQ W.vacuum := rfl

/-- **The conformal vector descends.** -/
theorem maxQuotientVOA_conformalVector :
    (maxQuotientVOA W).conformalVector = (maxGradedIdeal W).mkQ W.conformalVector := rfl

/-- **The simple quotient has the same central charge.** -/
theorem maxQuotientVOA_centralCharge :
    (maxQuotientVOA W).centralCharge = W.centralCharge := rfl

/-- **The projection intertwines every product**: `[u]₍ₙ₎[v] = [u₍ₙ₎v]`.  With the four
identities above this is the whole morphism content of `W ↠ W / maxGradedIdeal W` (the repo
has no bundled VOA-morphism type). -/
theorem maxQuotientVOA_mkQ_smul (u : 𝒱) (n : ℤ) (v : 𝒱) :
    (maxQuotientVOA W).smul ((maxGradedIdeal W).mkQ u) n ((maxGradedIdeal W).mkQ v)
      = (maxGradedIdeal W).mkQ (W.smul u n v) :=
  quotientVOA_mkQ_smul (maxGradedIdeal_isIdeal W) (maxGradedIdeal_isGradedIdeal W) u n v

/-- The projection preserves degrees. -/
theorem maxQuotientVOA_mkQ_grading {n : ℤ} {x : 𝒱} (hx : x ∈ W.grading n) :
    (maxGradedIdeal W).mkQ x ∈ (maxQuotientVOA W).grading n :=
  quotientVOA_mkQ_grading (maxGradedIdeal_isIdeal W) (maxGradedIdeal_isGradedIdeal W) hx

theorem maxQuotientVOA_mkQ_surjective : Function.Surjective (maxGradedIdeal W).mkQ :=
  (maxGradedIdeal W).mkQ_surjective

/-! ### Non-degeneracy -/

/-- **The vacuum survives the quotient**, for every `W` with `𝟙 ≠ 0`.  So the simple
quotient is never the zero algebra. -/
theorem maxQuotientVOA_vacuum_ne_zero (hvac : W.vacuum ≠ 0) :
    (maxQuotientVOA W).vacuum ≠ 0 := by
  intro h
  refine vacuum_not_mem_maxGradedIdeal W hvac ?_
  have h' : (maxGradedIdeal W).mkQ W.vacuum = 0 := h
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h'
  exact h'

/-- **The simple quotient is nontrivial.** -/
theorem maxQuotientVOA_nontrivial (hvac : W.vacuum ≠ 0) :
    Nontrivial (𝒱 ⧸ maxGradedIdeal W) :=
  ⟨⟨(maxQuotientVOA W).vacuum, 0, maxQuotientVOA_vacuum_ne_zero W hvac⟩⟩

/-- **The conformal vector is not in the maximal ideal**, when `c ≠ 0`: `L₂ω = (c/2)𝟙`
(`VirSimple.L_two_omega`, a general VOA identity) would otherwise put `𝟙` there.  At `c = 0`
this genuinely fails — the simple quotient can be the one-dimensional VOA `ℂ𝟙` with
`ω = 0`. -/
theorem conformalVector_not_mem_maxGradedIdeal (hvac : W.vacuum ≠ 0)
    (hc : W.centralCharge ≠ 0) : W.conformalVector ∉ maxGradedIdeal W := by
  intro h
  exact vacuum_not_mem_maxGradedIdeal W hvac
    (VirSimple.vacuum_mem_of_conformalVector_mem (maxGradedIdeal_isIdeal W) hc h)

/-- **The conformal vector survives the quotient**, when `c ≠ 0`.  Together with
`maxQuotientVOA_centralCharge` this says the simple quotient keeps a genuine Virasoro
element of the same central charge. -/
theorem maxQuotientVOA_conformalVector_ne_zero (hvac : W.vacuum ≠ 0)
    (hc : W.centralCharge ≠ 0) : (maxQuotientVOA W).conformalVector ≠ 0 := by
  intro h
  refine conformalVector_not_mem_maxGradedIdeal W hvac hc ?_
  have h' : (maxGradedIdeal W).mkQ W.conformalVector = 0 := h
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h'
  exact h'

/-! ### The generic case `maxGradedIdeal W = ⊥` -/

/-- When the maximal ideal is trivial the projection is injective. -/
theorem mkQ_injective_of_maxGradedIdeal_eq_bot (h : maxGradedIdeal W = ⊥) :
    Function.Injective (maxGradedIdeal W).mkQ := by
  rw [← LinearMap.ker_eq_bot, Submodule.ker_mkQ]
  exact h

/-- When the maximal ideal is trivial the projection is bijective. -/
theorem mkQ_bijective_of_maxGradedIdeal_eq_bot (h : maxGradedIdeal W = ⊥) :
    Function.Bijective (maxGradedIdeal W).mkQ :=
  ⟨mkQ_injective_of_maxGradedIdeal_eq_bot W h, (maxGradedIdeal W).mkQ_surjective⟩

/-- **`W` is already simple ⟹ it *is* its own simple quotient**, as a linear isomorphism
`𝒱 ≃ₗ 𝒱 ⧸ maxGradedIdeal W`.  Combine with `VirSimple.isSimple_iff_maxGradedIdeal_eq_bot`
(a general theorem, housed in the Virasoro file) to turn `W.IsSimple` into the hypothesis
`maxGradedIdeal W = ⊥`. -/
noncomputable def maxQuotientEquiv (h : maxGradedIdeal W = ⊥) :
    𝒱 ≃ₗ[ℂ] (𝒱 ⧸ maxGradedIdeal W) :=
  LinearEquiv.ofBijective (maxGradedIdeal W).mkQ (mkQ_bijective_of_maxGradedIdeal_eq_bot W h)

theorem maxQuotientEquiv_apply (h : maxGradedIdeal W = ⊥) (x : 𝒱) :
    maxQuotientEquiv W h x = (maxGradedIdeal W).mkQ x := rfl

/-- The generic-case isomorphism intertwines every product. -/
theorem maxQuotientEquiv_smul (h : maxGradedIdeal W = ⊥) (u v : 𝒱) (n : ℤ) :
    maxQuotientEquiv W h (W.smul u n v)
      = (maxQuotientVOA W).smul (maxQuotientEquiv W h u) n (maxQuotientEquiv W h v) := by
  simp only [maxQuotientEquiv_apply]
  exact (maxQuotientVOA_mkQ_smul W u n v).symm

/-- The generic-case isomorphism sends the vacuum to the vacuum. -/
theorem maxQuotientEquiv_vacuum (h : maxGradedIdeal W = ⊥) :
    maxQuotientEquiv W h W.vacuum = (maxQuotientVOA W).vacuum := rfl

/-- The generic-case isomorphism sends `ω` to `ω`. -/
theorem maxQuotientEquiv_conformalVector (h : maxGradedIdeal W = ⊥) :
    maxQuotientEquiv W h W.conformalVector = (maxQuotientVOA W).conformalVector := rfl

end MaxQuotient

/-! ## §3  The singular-vector bridge into the maximal ideal

`Core/SingularVector` proves that a strongly singular vector `s` generates a **proper** ideal
`(s) = SingVec.idealGen W s` (via the radical of the canonical FHL form), and that `(s) ≠ ⊥`.
`Core/QuotientVOA` proves that `maxGradedIdeal W` contains every proper ideal.  Nothing in
the repo joined the two.  Joining them is what says the simple quotient is a *proper*
quotient — and, concretely, that the singular vector **dies** in it.

This is the step that will turn `Examples/AffineSl2Singular.sl2Singular` into the statement
"`L_{-4/3}(𝔰𝔩₂) ≠ V^{-4/3}(𝔰𝔩₂)`, and the level-`-4/3` singular vector is zero in
`L_{-4/3}(𝔰𝔩₂)`".
-/

section SingularBridge

variable {W : VertexOperatorAlgebra 𝒱}

/-- **A vector generating a proper ideal lies in the maximal ideal.** -/
theorem mem_maxGradedIdeal_of_idealGen_proper {s : 𝒱} (hv : W.vacuum ∉ idealGen W s) :
    s ∈ maxGradedIdeal W :=
  le_maxGradedIdeal' (idealGen_isIdeal W s) hv (mem_idealGen_self W s)

/-- **Such a vector is `0` in the simple quotient.** -/
theorem mkQ_eq_zero_of_idealGen_proper {s : 𝒱} (hv : W.vacuum ∉ idealGen W s) :
    (maxGradedIdeal W).mkQ s = 0 := by
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact mem_maxGradedIdeal_of_idealGen_proper hv

/-- **A nonzero vector generating a proper ideal makes the maximal ideal nonzero**, i.e.
the simple quotient is a *proper* quotient of `W`. -/
theorem maxGradedIdeal_ne_bot_of_idealGen_proper {s : 𝒱} (hs0 : s ≠ 0)
    (hv : W.vacuum ∉ idealGen W s) : maxGradedIdeal W ≠ ⊥ := by
  intro h
  refine hs0 ?_
  have hmem : s ∈ maxGradedIdeal W := mem_maxGradedIdeal_of_idealGen_proper hv
  rw [h, Submodule.mem_bot] at hmem
  exact hmem

/-! ### Form-free specialisations, via the canonical FHL form

`SingVec.idealGen_proper_of_stronglySingular` needs a normalised fully invariant form; the
canonical FHL form (`Core/InvariantFormFHL2`) supplies one for any `W` with `𝟙 ≠ 0` and
`L₁𝒱₁ = 0` (quasi-primarity of weight-one states).  These are the versions a concrete example
should call. -/

/-- **A strongly singular vector lies in the maximal ideal.** -/
theorem mem_maxGradedIdeal_of_stronglySingular (hvac : W.vacuum ≠ 0)
    (hqp : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0) {k : ℤ} {s : 𝒱}
    (hs : IsStronglySingularOfWeight W k s) : s ∈ maxGradedIdeal W :=
  mem_maxGradedIdeal_of_idealGen_proper
    (idealGen_proper_of_stronglySingular (canonicalInvariantForm_isFullyInvariant hvac hqp)
      (canonicalInvariantForm_normalized hvac hqp) hs)

/-- **A strongly singular vector is `0` in the simple quotient.** -/
theorem mkQ_eq_zero_of_stronglySingular (hvac : W.vacuum ≠ 0)
    (hqp : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0) {k : ℤ} {s : 𝒱}
    (hs : IsStronglySingularOfWeight W k s) : (maxGradedIdeal W).mkQ s = 0 :=
  mkQ_eq_zero_of_idealGen_proper
    (idealGen_proper_of_stronglySingular (canonicalInvariantForm_isFullyInvariant hvac hqp)
      (canonicalInvariantForm_normalized hvac hqp) hs)

/-- **A strongly singular vector makes the maximal ideal nonzero.** -/
theorem maxGradedIdeal_ne_bot_of_stronglySingular (hvac : W.vacuum ≠ 0)
    (hqp : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0) {k : ℤ} {s : 𝒱}
    (hs : IsStronglySingularOfWeight W k s) : maxGradedIdeal W ≠ ⊥ :=
  maxGradedIdeal_ne_bot_of_idealGen_proper hs.ne_zero
    (idealGen_proper_of_stronglySingular (canonicalInvariantForm_isFullyInvariant hvac hqp)
      (canonicalInvariantForm_normalized hvac hqp) hs)

/-- **The simple quotient is a *proper* quotient**: the projection `W ↠ W/maxGradedIdeal W`
is not injective when `W` carries a strongly singular vector.  (Equivalently, by
`VirSimple.isSimple_iff_maxGradedIdeal_eq_bot`, `W` is not simple — which
`SingVec.not_isSimple_of_stronglySingular_FHL` already says; this is the quotient-side
statement.) -/
theorem mkQ_not_injective_of_stronglySingular (hvac : W.vacuum ≠ 0)
    (hqp : ∀ v, v ∈ W.grading 1 → W.L 1 v = 0) {k : ℤ} {s : 𝒱}
    (hs : IsStronglySingularOfWeight W k s) :
    ¬ Function.Injective (maxGradedIdeal W).mkQ := by
  intro hinj
  refine maxGradedIdeal_ne_bot_of_stronglySingular hvac hqp hs ?_
  rw [← Submodule.ker_mkQ (maxGradedIdeal W), LinearMap.ker_eq_bot]
  exact hinj

end SingularBridge

/-! ## §4  The recipe: how to obtain `L_k(𝔰𝔩₂)` from the instance

⚠ **NOT COMPILED; NOT LIBRARY THEOREMS.**  This section is documentation.  The code block below
lives inside this docstring and is never elaborated; `AffineSimple.affineSl2Simple`,
`affineSl2Simple_isSimple` and the other names in it do not exist in the library, and nothing
checks that the sketch typechecks.  As written it would depend on the theorem `VOA.pbw` (through
`vacuumA_ne_zero`).  The library's actual simple quotient at `k = -4/3` is
`simpleSl2QL := QuotVOA.maxQuotientVOA affineSl2QL` (`Examples.AffineSl2QuasiLisse`).

This section is documentation.  It describes how a module
`VOA/Examples/AffineSl2Simple.lean` could be written once
`VOA/Examples/AffineSl2VOAInstance.lean` produces a genuine

  `affineSl2VOA' k hk : VertexOperatorAlgebra (WakModule k)`

(whatever that file ends up calling it — below, `Wk k hk`).  The `Y`-independent fields of
that instance are already fixed by `AffineVOA.affineSl2VOA` in `Examples/AffineSl2VOA.lean`,
so the following are true **by `rfl`** for it and are the only interface facts needed:

* `(Wk k hk).vacuum = AffineVOA.vacuumA k`
* `(Wk k hk).conformalVector = AffineVOA.omegaA k`
* `(Wk k hk).grading n = AffineVOA.gradingZA k n`
* `(Wk k hk).centralCharge = AffineVOA.centralChargeA k`

### The file, declaration by declaration (mirroring `Examples/VirasoroSimple` 183–229)

```
import VOA.Examples.AffineSimpleQuotient   -- this file
import VOA.Examples.AffineSl2VOAInstance   -- for `Wk`
import VOA.Examples.AdmissibleLevel        -- for the level bookkeeping

namespace VOA.AffineSimple
open VOA VOA.QuotVOA VOA.SimpleQuot VOA.AffineVOA

variable (k : ℂ) (hk : k + 2 ≠ 0)

-- (1)  VirasoroSimple:183 — `maxIdealVir c := maxGradedIdeal (virasoroVOA c)`
noncomputable def maxIdealAff : Submodule ℂ (WakModule k) := maxGradedIdeal (Wk k hk)

-- (2)  VirasoroSimple:186
theorem maxIdealAff_isIdeal : (Wk k hk).IsIdeal (maxIdealAff k hk) :=
  maxGradedIdeal_isIdeal _

-- (3)  VirasoroSimple:189
theorem maxIdealAff_isGradedIdeal : IsGradedIdeal (Wk k hk) (maxIdealAff k hk) :=
  maxGradedIdeal_isGradedIdeal _

-- (4) PROPERNESS.  VirasoroSimple:195.  The Virasoro file needs the whole
--     `Examples/VirasoroNonvanishing` development here; the affine side already has it:
--     `AffineVOA.vacuumA_ne_zero k` (this is where the theorem
--     `VOA.pbw` enters, and the ONLY place it enters).
--     `(Wk k hk).vacuum = vacuumA k` is `rfl`.
theorem vacuumA_not_mem_maxIdealAff : vacuumA k ∉ maxIdealAff k hk :=
  vacuum_not_mem_maxGradedIdeal (Wk k hk) (vacuumA_ne_zero k)

-- (5)  VirasoroSimple:198 — a one-liner from this file's §2
theorem maxIdealAff_ne_top : maxIdealAff k hk ≠ ⊤ :=
  maxGradedIdeal_ne_top (Wk k hk) (vacuumA_ne_zero k)

-- (6)  VirasoroSimple:204 — maximality among ALL proper ideals
theorem le_maxIdealAff {J : Submodule ℂ (WakModule k)} (hJ : (Wk k hk).IsIdeal J)
    (hv : vacuumA k ∉ J) : J ≤ maxIdealAff k hk := le_maxGradedIdeal' hJ hv

-- (7) VirasoroSimple:216 — THE OBJECT.  `L_k(𝔰𝔩₂)`.
noncomputable def affineSl2Simple :
    VertexOperatorAlgebra (WakModule k ⧸ maxIdealAff k hk) := maxQuotientVOA (Wk k hk)

-- (8)  VirasoroSimple:221 — `c = 3k/(k+2)`, unchanged by the quotient
theorem affineSl2Simple_centralCharge :
    (affineSl2Simple k hk).centralCharge = 3 * k / (k + 2) := centralChargeA_eq k

-- (9–11)  VirasoroSimple:223–230 — all `rfl`, or `maxQuotientVOA_*` from §2
theorem affineSl2Simple_vacuum :
    (affineSl2Simple k hk).vacuum = (maxIdealAff k hk).mkQ (vacuumA k) := rfl
theorem affineSl2Simple_conformalVector :
    (affineSl2Simple k hk).conformalVector = (maxIdealAff k hk).mkQ (omegaA k) := rfl
theorem affineSl2Simple_grading (n : ℤ) :
    (affineSl2Simple k hk).grading n = (gradingZA k n).map (maxIdealAff k hk).mkQ := rfl

-- (12) SIMPLICITY (VirasoroSimple:242)
theorem affineSl2Simple_isSimple : (affineSl2Simple k hk).IsSimple :=
  isSimple_maxQuotientVOA' (Wk k hk) (vacuumA_ne_zero k)

-- (13)  non-degeneracy (VirasoroSimple:248, 255) — §2 of this file
theorem affineSl2Simple_vacuum_ne_zero : (affineSl2Simple k hk).vacuum ≠ 0 :=
  maxQuotientVOA_vacuum_ne_zero (Wk k hk) (vacuumA_ne_zero k)
theorem affineSl2Simple_nontrivial : Nontrivial (WakModule k ⧸ maxIdealAff k hk) :=
  maxQuotientVOA_nontrivial (Wk k hk) (vacuumA_ne_zero k)

-- (14)  ω survives whenever `c = 3k/(k+2) ≠ 0`, i.e. (given `k+2 ≠ 0`) whenever `k ≠ 0`
theorem affineSl2Simple_conformalVector_ne_zero (hc : centralChargeA k ≠ 0) :
    (affineSl2Simple k hk).conformalVector ≠ 0 :=
  maxQuotientVOA_conformalVector_ne_zero (Wk k hk) (vacuumA_ne_zero k) hc

-- (15)  the projection, as a morphism (VirasoroSimple:284)
theorem affineSl2Simple_mkQ_smul (u v : WakModule k) (n : ℤ) :
    (affineSl2Simple k hk).smul ((maxIdealAff k hk).mkQ u) n ((maxIdealAff k hk).mkQ v)
      = (maxIdealAff k hk).mkQ ((Wk k hk).smul u n v) :=
  maxQuotientVOA_mkQ_smul (Wk k hk) u n v
end VOA.AffineSimple
```

### The flagship `k = -4/3`

Specialise with the level bookkeeping of `Examples/AdmissibleLevel`:

* `hk : (-4/3 : ℂ) + 2 ≠ 0` — from `Admissible.AdmissibleLevel.add_two_ne_zero` applied to
  `Admissible.admissibleLevel_neg_four_thirds`, or directly by `norm_num`.
* `c = -6` — `Admissible.centralChargeA_neg_four_thirds`.  In particular `c ≠ 0`, so step
  (14) applies and `L_{-4/3}(𝔰𝔩₂)` retains a genuine Virasoro element of central charge `-6`.
* `L_{-4/3}(𝔰𝔩₂) := affineSl2Simple (-4/3) hk`.

### Making the quotient *nontrivial* (the singular vector), via §3

Steps (1)–(15) never look at a singular vector — the maximal ideal exists for every `k`, and
for generic `k` it is `⊥`.  To show `L_{-4/3}(𝔰𝔩₂)` is a **proper** quotient of
`V^{-4/3}(𝔰𝔩₂)`, feed `Examples/AffineSl2Singular.sl2Singular` into §3:

1. Prove `SingVec.IsStronglySingularOfWeight (Wk (-4/3) hk) 3 sl2Singular`.  Its four fields
   are, in order:
   * `ne_zero` — proved unconditionally (and `pbw`-free) as `Wak.sl2Singular_ne_zero`
     (`Examples.WakimotoFree`, Wakimoto realization);
   * `weight_pos` — `(0 : ℤ) < 3`, by `decide`;
   * `homogeneous` — `sl2Singular_mem : sl2Singular ∈ gradingZA (-4/3) 3` (`rfl`-transports
     to `(Wk _ _).grading 3`);
   * `annihilated` — from `sl2Singular_pos` (every current mode `J^a_m`, `m ≥ 1`, kills it)
     plus the fact that `𝒱` is generated by the currents, i.e. the strong-generation half of
     the reconstruction theorem.  ⚠ This is the second real work item.
2. Prove `hqp : ∀ v ∈ (Wk k hk).grading 1, (Wk k hk).L 1 v = 0` — weight-one states of an
   affine VOA are the currents `J^a_{-1}|0⟩`, and `L₁ J^a_{-1}|0⟩ = 0` by the Sugawara
   commutator already available in `Examples/AffineSl2Virasoro`.
3. Then, with no further work:
   * `mkQ_eq_zero_of_stronglySingular` — `sl2Singular ↦ 0` in `L_{-4/3}(𝔰𝔩₂)`;
   * `maxGradedIdeal_ne_bot_of_stronglySingular` — `maxIdealAff (-4/3) hk ≠ ⊥`;
   * `mkQ_not_injective_of_stronglySingular` — the quotient is proper;
   * `SingVec.not_isSimple_of_stronglySingular_FHL` — `V^{-4/3}(𝔰𝔩₂)` is not simple.

### What is *not* in the recipe

The associated variety (`= 𝒩(𝔰𝔩₂) = ℂ²/ℤ₂`), quasi-lisse-ness, `C₂`-cofiniteness and the
Arakawa–Kawasetsu input are all downstream of the object built here and are not touched.
-/

/-! ## §5  Axiom audit

`#print axioms` was run (temporarily, then removed in favour of this note) on every
declaration of §1–§3:

`eq_top_of_mem_grading_zero`, `eq_zero_of_mem_grading_zero_of_ne_top`,
`ne_top_iff_vacuum_not_mem`, `inf_grading_zero_eq_bot_iff`,
`ne_top_iff_inf_grading_zero_eq_bot`, `tfae_proper`,
`ne_top_iff_not_mem_of_grading_zero_eq_span`, `vacuum_ne_zero_of_grading_zero_eq_span`,
`maxGradedIdeal_ne_top`, `maxGradedIdeal_inf_grading_zero_eq_bot`,
`maxGradedIdeal_le_iSup_ne_zero`, `maxQuotientVOA_grading`, `maxQuotientVOA_vacuum`,
`maxQuotientVOA_conformalVector`, `maxQuotientVOA_centralCharge`, `maxQuotientVOA_mkQ_smul`,
`maxQuotientVOA_mkQ_grading`, `maxQuotientVOA_mkQ_surjective`,
`maxQuotientVOA_vacuum_ne_zero`, `maxQuotientVOA_nontrivial`,
`conformalVector_not_mem_maxGradedIdeal`, `maxQuotientVOA_conformalVector_ne_zero`,
`mkQ_injective_of_maxGradedIdeal_eq_bot`, `mkQ_bijective_of_maxGradedIdeal_eq_bot`,
`maxQuotientEquiv`, `maxQuotientEquiv_apply`, `maxQuotientEquiv_smul`,
`maxQuotientEquiv_vacuum`, `maxQuotientEquiv_conformalVector`,
`mem_maxGradedIdeal_of_idealGen_proper`, `mkQ_eq_zero_of_idealGen_proper`,
`maxGradedIdeal_ne_bot_of_idealGen_proper`, `mem_maxGradedIdeal_of_stronglySingular`,
`mkQ_eq_zero_of_stronglySingular`, `maxGradedIdeal_ne_bot_of_stronglySingular`,
`mkQ_not_injective_of_stronglySingular`.

Every one reports exactly `[propext, Classical.choice, Quot.sound]`.  The theorem
`VOA.pbw` is **not** used anywhere in this file — it will enter
the affine specialisation only through `AffineVOA.vacuumA_ne_zero`, at step (4) of §4's recipe.
-/

end VOA.SimpleQuot
