/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.LatticeGenGradedField
import Mathlib.Order.CompactlyGenerated.Basic

/-!
# ℚ-valued quadratic refinements of the lattice grading  (the general-`p` road)

`Examples.LatticeGenGrading` grades `V_L = FockN(rank L) ⊗ ℂ{L}` by the **standard** conformal
weight `w + ½⟨α,α⟩` (`halfNorm`, an integer by evenness).  The triplet and doublet `W`-algebras at
general `p` need a **deformed** weight coming from a background charge, and that weight is
**ℚ-valued, not ℤ-valued** (project decision: on the doublet half-lattice `⟨λ, γ/2⟩ = (p−1)/2` is
not an integer for any even `p`).  This file builds the refinement layer.

## Main definitions

* `QuadRefine L` — ℚ-valued quadratic data on `L`: a function `q : L.carrier → ℚ` whose
  **polarization is the lattice form**, `q(α+β) − q α − q β = ⟨α,β⟩`.  This is exactly the class of
  weight assignments of the form `½⟨α,α⟩ − ⟨Q₀,α⟩` for a background charge `Q₀`:
  `QuadRefine.bgCharge_add` proves that `halfNorm − q` is additive, so **every** refinement *is* a
  background-charge deformation of `halfNorm`, and conversely.
* `wtQrat` / `wtQ` — the refined weight `w + q α` of the bigraded piece `(w, α)`, as a rational and
  (its cast) as a complex number.  The grading is indexed by `ℂ`, matching the repo's
  `SuperVertexAlgebra`/`SuperNearVOA` ℂ-grading; the ℂ-grading → ℤ-grading transfer stays gated on
  an explicit integrality hypothesis, per the project decision.
* `gradingLatGenQ L qr` — the lattice VOA graded by the refined weight.
* `PosQuad L qr` — the CFT-type input (`0 < q α` for `α ≠ 0`), *stated*, to be checked per example.
* `QFinite L qr` — the finite-dimensionality input (`{α | q α ≤ N}` finite), likewise per example.

## Main results

* `gradeCollapse_isInternal` (§0) — **relabelling an internal direct sum along any map keeps it
  internal**, with no finiteness hypothesis whatsoever.  The finiteness-freeness is `Submodule`'s
  lattice being compactly generated and modular (`iSupIndep.disjoint_biSup_biSup`); the general
  lattice statement really would need finiteness (`disjoint_biSup_biSup'`).
* `gradingLatGenQ_isInternal` — **internality of the refined grading is `q`-independent**, exactly
  as the scoping analysis predicted: the statement needs *no* hypothesis on `q`, and none on `L`
  either (no `Even`, no `PosDef`, no `BoundedFinite`).  It is a statement about the
  charge/oscillator decomposition `bigradα`, and the refined weight only relabels which pieces are
  grouped together.
* `gradingLatGen_isInternal_free` — the same argument, applied to the **existing** `halfNorm`
  grading, discharges `hEven`/`hPos`/`BoundedFinite` from `gradingLatGen_isInternal_of_posDef`.
  (Those hypotheses are genuinely needed for `gradingLatGen_finrank`, not for internality.)
* `gradingLatGenQ_halfNormRefine` — at `q = halfNorm` the refined grading **recovers**
  `gradingLatGen`: `gradingLatGenQ L (halfNormRefine L hEven) (k : ℂ) = gradingLatGen L k`.
* `gradingLatGenQ_eq_bot_of_re_neg`, `gradingLatGenQ_zero_eq_span_vacuum` — the CFT-type
  consequences of `PosQuad`, in the `Complex.re` shape that `SuperNearVOA.BoundedBelow` and the
  `positivity` field want.
* `gradingLatGenQ_finrank` — each refined weight space is finite-dimensional, given `QFinite`.

## Which of the 19 `VertexOperatorAlgebra` fields depend on the grading

Reading `latticeVOAGen` (`Examples.LatticeGenInstance`), the grading enters **nine** fields:
`grading`, `isInternal`, `finrank`, `vacuum_mem`, `grading_mode`, `conformal_mem`, `L0_grading`,
`vacuum_grade`, `positivity`.  The other ten (`Y`, `vacuum`, `vacuum_Y`, `creation`, `locality`,
`regularity`, `conformalVector`, `centralCharge`, `virasoro`, `translation`) are untouched by a
change of weight label.  Of the nine, this file supplies the analogues of `grading`, `isInternal`,
`finrank`, `vacuum_grade` and `positivity`; `vacuum_mem` is immediate from `vacuum_grade`.  The
remaining three (`grading_mode`, `conformal_mem`, `L0_grading`) are *not* `q`-independent — they
constrain the deformed `L₀`, i.e. the background-charge Virasoro — and are deliberately left out
here rather than stated with a hole.

All `sorry`-free, axiom-clean.
-/

set_option linter.style.longLine false

open scoped BigOperators TensorProduct DirectSum
open VOA VOA.IntegralLattice

namespace VOA.LatGen

/-! ## §0  Collapsing an internal direct sum along a relabelling (finiteness-free)

A grading is `⨁ᵢ tᵢ`; a *coarser* grading is obtained by relabelling the index set along
`f : ι → κ` and summing the fibres.  The collapsed family is again independent and again spans, so
it is again an internal direct sum — **with no finiteness hypothesis**.  In a general modular
lattice one only gets `iSupIndep.disjoint_biSup_biSup'`, which needs one of the two index sets to
be finite; the lattice of submodules is additionally *compactly generated*, and there the finiteness
may be dropped (`iSupIndep.disjoint_biSup_biSup`).  This is the whole reason internality of the
refined lattice grading is `q`-independent. -/

section Collapse

variable {ι κ : Type*} {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

/-- The `k`-th piece of the grading obtained from `t` by relabelling the index along `f`. -/
def gradeCollapse (t : ι → Submodule R M) (f : ι → κ) (k : κ) : Submodule R M :=
  ⨆ i ∈ f ⁻¹' {k}, t i

theorem gradeCollapse_def (t : ι → Submodule R M) (f : ι → κ) (k : κ) :
    gradeCollapse t f k = ⨆ i ∈ f ⁻¹' {k}, t i := rfl

theorem le_gradeCollapse (t : ι → Submodule R M) (f : ι → κ) (i : ι) :
    t i ≤ gradeCollapse t f (f i) :=
  le_biSup t (show i ∈ f ⁻¹' {f i} by simp)

/-- The complement description of "all the other pieces". -/
theorem iSup_ne_gradeCollapse (t : ι → Submodule R M) (f : ι → κ) (k : κ) :
    (⨆ (k' : κ) (_ : k' ≠ k), gradeCollapse t f k') = ⨆ i ∈ (f ⁻¹' {k})ᶜ, t i := by
  apply le_antisymm
  · refine iSup_le fun k' => iSup_le fun hk' => ?_
    rw [gradeCollapse_def]
    refine iSup_le fun i => iSup_le fun hi => le_biSup t ?_
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hi
    simp only [Set.mem_compl_iff, Set.mem_preimage, Set.mem_singleton_iff, hi]
    exact hk'
  · refine iSup_le fun i => iSup_le fun hi => ?_
    have hik : f i ≠ k := by
      simpa only [Set.mem_compl_iff, Set.mem_preimage, Set.mem_singleton_iff] using hi
    refine le_trans (le_gradeCollapse t f i) ?_
    refine le_trans (le_iSup (fun _ : f i ≠ k => gradeCollapse t f (f i)) hik) ?_
    exact le_iSup (fun k' => ⨆ (_ : k' ≠ k), gradeCollapse t f k') (f i)

/-- **Independence is preserved by relabelling** — no finiteness hypothesis. -/
theorem gradeCollapse_iSupIndep {t : ι → Submodule R M} (ht : iSupIndep t) (f : ι → κ) :
    iSupIndep (gradeCollapse t f) := by
  rw [iSupIndep_def]
  intro k
  rw [gradeCollapse_def, iSup_ne_gradeCollapse t f k]
  exact ht.disjoint_biSup_biSup disjoint_compl_right

/-- **Spanning is preserved by relabelling.** -/
theorem gradeCollapse_iSup (t : ι → Submodule R M) (f : ι → κ) :
    (⨆ k : κ, gradeCollapse t f k) = ⨆ i, t i := by
  apply le_antisymm
  · refine iSup_le fun k => ?_
    rw [gradeCollapse_def]
    exact iSup_le fun i => iSup_le fun _ => le_iSup t i
  · exact iSup_le fun i =>
      le_trans (le_gradeCollapse t f i) (le_iSup (fun k => gradeCollapse t f k) (f i))

/-- **Relabelling an internal direct sum along an arbitrary map keeps it internal.**  Stated from
the two ingredients (independence + spanning) rather than from `DirectSum.IsInternal t`, so that no
`DecidableEq ι` instance has to be threaded through. -/
theorem gradeCollapse_isInternal [DecidableEq κ] {t : ι → Submodule R M}
    (h₁ : iSupIndep t) (h₂ : iSup t = ⊤) (f : ι → κ) :
    DirectSum.IsInternal (gradeCollapse t f) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (gradeCollapse_iSupIndep h₁ f)
    (by rw [show iSup (gradeCollapse t f) = iSup t from gradeCollapse_iSup t f]; exact h₂)

end Collapse

variable (L : IntegralLattice)

/-! ## §1  ℚ-valued quadratic data on a lattice -/

/-- **ℚ-valued quadratic data on a lattice `L`.**  The single axiom is that the polarization of `q`
is the lattice form.  It is what makes `q` a *quadratic refinement*: `q` need not be `½⟨α,α⟩`, but
it may differ from it only by an additive (linear) background charge — see `bgCharge_add`.

The value type is `ℚ`, **not** `ℤ`: on the doublet half-lattice `⟨λ, γ/2⟩ = (p−1)/2`, which is
never an integer for even `p`. -/
structure QuadRefine where
  /-- The refined weight of the charged vacuum `e^α`. -/
  q : L.carrier → ℚ
  /-- **Polarization**: `q(α+β) − q α − q β = ⟨α,β⟩`. -/
  polarization : ∀ α β : L.carrier, q (α + β) - q α - q β = (L.form α β : ℚ)

namespace QuadRefine

variable {L}

/-- `q 0 = 0`: the vacuum sits at weight `0`.  A theorem, not an axiom (polarize at `α = β = 0`). -/
theorem q_zero (qr : QuadRefine L) : qr.q 0 = 0 := by
  have h := qr.polarization 0 0
  simp only [add_zero, map_zero, Int.cast_zero] at h
  linarith

end QuadRefine

/-! ### `halfNorm` polarizes to the form, and the background charge -/


namespace QuadRefine

variable {L}

/-- The **background charge** of a refinement: `Q₀(α) := ½⟨α,α⟩ − q α`. -/
noncomputable def bgCharge (qr : QuadRefine L) (α : L.carrier) : ℚ :=
  (halfNorm L α : ℚ) - qr.q α

/-- **The background charge is additive** — i.e. every ℚ-valued quadratic refinement of the lattice
form is `½⟨α,α⟩` shifted by a *linear* functional.  This is the precise sense in which `QuadRefine`
is "the standard weight deformed by a background charge". -/
theorem bgCharge_add (hEven : L.Even) (qr : QuadRefine L) (α β : L.carrier) :
    qr.bgCharge (α + β) = qr.bgCharge α + qr.bgCharge β := by
  have hpol := qr.polarization α β
  simp only [bgCharge, halfNorm_add L hEven]
  push_cast
  linarith

end QuadRefine

/-! ## §2  The refined weight and the refined grading -/

/-- The **refined rational weight** `w + q α` of the bigraded piece `(w, α)`. -/
def wtQrat (qr : QuadRefine L) (p : ℤ × L.carrier) : ℚ := (p.1 : ℚ) + qr.q p.2

/-- The refined weight as a **complex** number (the grading index type of the repo's
`SuperVertexAlgebra`/`SuperNearVOA`). -/
def wtQ (qr : QuadRefine L) (p : ℤ × L.carrier) : ℂ := ((wtQrat L qr p : ℚ) : ℂ)

theorem wtQ_eq (qr : QuadRefine L) (p : ℤ × L.carrier) :
    wtQ L qr p = ((wtQrat L qr p : ℚ) : ℂ) := rfl

/-- `wtQ p = r` for a *rational* `r` is a rational equation (`ℚ ↪ ℂ`). -/
theorem wtQ_eq_ratCast_iff (qr : QuadRefine L) (p : ℤ × L.carrier) (r : ℚ) :
    wtQ L qr p = (r : ℂ) ↔ wtQrat L qr p = r := by
  constructor
  · intro h; rw [wtQ_eq] at h; exact_mod_cast h
  · intro h; rw [wtQ_eq, h]

/-- The real part of the refined weight is the refined rational weight. -/
theorem wtQ_re (qr : QuadRefine L) (p : ℤ × L.carrier) :
    (wtQ L qr p).re = (p.1 : ℝ) + ((qr.q p.2 : ℚ) : ℝ) := by
  simp only [wtQ_eq, wtQrat, Complex.ratCast_re]
  push_cast
  ring

/-- **The lattice VOA graded by a refined (ℚ-valued, hence ℂ-indexed) weight.** -/
noncomputable def gradingLatGenQ (qr : QuadRefine L) (k : ℂ) : Submodule ℂ (LatModuleGen L) :=
  gradeCollapse (bigradα L) (wtQ L qr) k

theorem gradingLatGenQ_def (qr : QuadRefine L) (k : ℂ) :
    gradingLatGenQ L qr k = ⨆ p ∈ (wtQ L qr) ⁻¹' {k}, bigradα L p := rfl

theorem bigradα_le_gradingLatGenQ (qr : QuadRefine L) (p : ℤ × L.carrier) :
    bigradα L p ≤ gradingLatGenQ L qr (wtQ L qr p) :=
  le_gradeCollapse (bigradα L) (wtQ L qr) p

/-! ### (c) Internality — `q`-independent, hypothesis-free -/

/-- **The refined grading spans `V_L`.**  No hypothesis on `q` or on `L`. -/
theorem gradingLatGenQ_iSup_eq_top (qr : QuadRefine L) : iSup (gradingLatGenQ L qr) = ⊤ := by
  rw [show iSup (gradingLatGenQ L qr) = iSup (bigradα L) from
    gradeCollapse_iSup (bigradα L) (wtQ L qr)]
  exact bigradα_iSup_eq_top L

/-- **The refined weight spaces are independent.**  No hypothesis on `q` or on `L`. -/
theorem gradingLatGenQ_iSupIndep (qr : QuadRefine L) : iSupIndep (gradingLatGenQ L qr) :=
  gradeCollapse_iSupIndep (bigradα_iSupIndep L) (wtQ L qr)

/-- **(c)  The refined grading is an internal direct-sum decomposition of `V_L`.**

Internality is **`q`-independent**, and indeed hypothesis-free: it holds for *every* `QuadRefine`,
with no `Even`, no `PosDef`, no `BoundedFinite`.  The reason is structural — internality is a
statement about the charge/oscillator decomposition `bigradα` (`bigradα_isInternal`, itself
finiteness-free), and the refined weight only *relabels* which `bigradα`-pieces get grouped
together (`gradeCollapse_isInternal`). -/
theorem gradingLatGenQ_isInternal (qr : QuadRefine L) :
    DirectSum.IsInternal (gradingLatGenQ L qr) :=
  gradeCollapse_isInternal (bigradα_iSupIndep L) (bigradα_iSup_eq_top L) (wtQ L qr)

/-! ### The same argument, applied to the existing `halfNorm` grading

`gradingLatGen_isInternal_of_posDef` needs `hEven`/`hPos` (through `BoundedFinite`).  The collapse
lemma shows those are needed only for `gradingLatGen_finrank`, never for internality. -/

/-- The existing `L₀`-grading *is* a relabelling of `bigradα` along `p ↦ p.1 + ½⟨p.2,p.2⟩`. -/
theorem gradingLatGen_eq_gradeCollapse (k : ℤ) :
    gradingLatGen L k
      = gradeCollapse (bigradα L) (fun p : ℤ × L.carrier => p.1 + halfNorm L p.2) k := by
  have hset : {p : ℤ × L.carrier | p.1 + halfNorm L p.2 = k}
      = (fun p : ℤ × L.carrier => p.1 + halfNorm L p.2) ⁻¹' {k} := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff]
  rw [gradingLatGen_eq_biSup L k, gradeCollapse_def, hset]

/-- **`gradingLatGen` is internal with no hypotheses at all** — strengthening
`gradingLatGen_isInternal_of_posDef` by discharging `hEven`, `hPos` and `BoundedFinite`. -/
theorem gradingLatGen_isInternal_free : DirectSum.IsInternal (gradingLatGen L) := by
  have h := gradeCollapse_isInternal (bigradα_iSupIndep L) (bigradα_iSup_eq_top L)
    (fun p : ℤ × L.carrier => p.1 + halfNorm L p.2)
  rwa [show (gradeCollapse (bigradα L) (fun p : ℤ × L.carrier => p.1 + halfNorm L p.2))
      = gradingLatGen L from funext fun k => (gradingLatGen_eq_gradeCollapse L k).symm] at h

/-! ## §3  (e)  Instantiation at `q = halfNorm`: the refined grading recovers `gradingLatGen` -/

/-- The **standard** refinement `q = ½⟨α,α⟩` (needs evenness, so that `halfNorm` polarizes to the
form on the nose). -/
noncomputable def halfNormRefine (hEven : L.Even) : QuadRefine L where
  q := fun α => (halfNorm L α : ℚ)
  polarization := by
    intro α β
    rw [halfNorm_add L hEven]
    push_cast
    ring

@[simp] theorem halfNormRefine_q (hEven : L.Even) (α : L.carrier) :
    (halfNormRefine L hEven).q α = (halfNorm L α : ℚ) := rfl

theorem wtQrat_halfNormRefine (hEven : L.Even) (p : ℤ × L.carrier) :
    wtQrat L (halfNormRefine L hEven) p = ((p.1 + halfNorm L p.2 : ℤ) : ℚ) := by
  simp only [wtQrat, halfNormRefine_q]
  push_cast
  ring

theorem wtQ_halfNormRefine_preimage (hEven : L.Even) (k : ℤ) :
    (wtQ L (halfNormRefine L hEven)) ⁻¹' {(k : ℂ)}
      = {p : ℤ × L.carrier | p.1 + halfNorm L p.2 = k} := by
  ext p
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq, wtQ_eq,
    wtQrat_halfNormRefine]
  constructor
  · intro h; exact_mod_cast h
  · intro h; exact_mod_cast congrArg (fun n : ℤ => ((n : ℚ) : ℂ)) h

/-- **(e)  At `q = ½⟨·,·⟩` the refined grading is the existing `L₀`-grading**, weight `k : ℤ`
sitting at the complex index `(k : ℂ)`. -/
theorem gradingLatGenQ_halfNormRefine (hEven : L.Even) (k : ℤ) :
    gradingLatGenQ L (halfNormRefine L hEven) (k : ℂ) = gradingLatGen L k := by
  rw [gradingLatGenQ_def, wtQ_halfNormRefine_preimage L hEven k, gradingLatGen_eq_biSup L k]

/-! ## §4  (d)  `PosQuad`: the CFT-type input, and what it buys

`PosQuad` is **not** proved for a general lattice — it is an input to be checked per example.  For
`q = halfNorm` it is `halfNorm_pos`, i.e. positive-definiteness (`posQuad_halfNormRefine` below);
for the triplet/doublet background charges it is a genuine computation on the relevant
(half-)lattice, and the project decision records that the *doublet* ambient has negative weights,
so it will fail there and the module machinery must be routed through `BoundedBelow` instead. -/

/-- **`PosQuad`** — the refined weight of every non-trivial charge sector is strictly positive.
This is what makes the refined grading CFT-type: `𝒱_h = 0` for `Re h < 0`
(`gradingLatGenQ_eq_bot_of_re_neg`) and `𝒱₀ = ℂ𝟙` (`gradingLatGenQ_zero_eq_span_vacuum`). -/
def PosQuad (qr : QuadRefine L) : Prop := ∀ α : L.carrier, α ≠ 0 → 0 < qr.q α

variable {L}

theorem PosQuad.nonneg {qr : QuadRefine L} (h : PosQuad L qr) (α : L.carrier) : 0 ≤ qr.q α := by
  rcases eq_or_ne α 0 with rfl | hα
  · exact le_of_eq qr.q_zero.symm
  · exact le_of_lt (h α hα)

theorem PosQuad.nonnegR {qr : QuadRefine L} (h : PosQuad L qr) (α : L.carrier) :
    (0 : ℝ) ≤ ((qr.q α : ℚ) : ℝ) := by
  exact_mod_cast h.nonneg α

variable (L)

/-- **`𝒱_h = 0` for `Re h < 0`** — the `positivity` field's analogue, and `BoundedBelow` with
`B = 0`. -/
theorem gradingLatGenQ_eq_bot_of_re_neg {qr : QuadRefine L} (hq : PosQuad L qr) (k : ℂ)
    (hk : k.re < 0) : gradingLatGenQ L qr k = ⊥ := by
  rw [gradingLatGenQ_def]
  refine le_bot_iff.mp (iSup_le fun p => iSup_le fun hp => ?_)
  obtain ⟨w, α⟩ := p
  have hw : wtQ L qr (w, α) = k := hp
  have hre : (w : ℝ) + ((qr.q α : ℚ) : ℝ) = k.re := by
    rw [← hw, wtQ_re]
  have h0 := hq.nonnegR α
  have hwR : (w : ℝ) < 0 := by linarith
  have hwZ : w < 0 := by exact_mod_cast hwR
  rw [bigradα_eq_bot_of_neg L α hwZ]

/-- **`𝒱₀ = ℂ𝟙`** — the `vacuum_grade` field's analogue. -/
theorem gradingLatGenQ_zero_eq_span_vacuum {qr : QuadRefine L} (hq : PosQuad L qr) :
    gradingLatGenQ L qr 0 = ℂ ∙ latVacuumGen L := by
  rw [gradingLatGenQ_def, ← bigradα_zero_zero L]
  apply le_antisymm
  · refine iSup_le fun p => iSup_le fun hp => ?_
    obtain ⟨w, α⟩ := p
    have hw : wtQ L qr (w, α) = 0 := hp
    have hre : (w : ℝ) + ((qr.q α : ℚ) : ℝ) = 0 := by
      rw [← wtQ_re L qr (w, α), hw]; simp
    rcases eq_or_ne α 0 with rfl | hα
    · have hq0 : ((qr.q (0 : L.carrier) : ℚ) : ℝ) = 0 := by
        rw [qr.q_zero]; simp
      have hwR : (w : ℝ) = 0 := by rw [hq0] at hre; linarith
      have hwZ : w = 0 := by exact_mod_cast hwR
      rw [hwZ]
    · have hpos : (0 : ℝ) < ((qr.q α : ℚ) : ℝ) := by exact_mod_cast hq α hα
      have hwR : (w : ℝ) < 0 := by linarith
      have hwZ : w < 0 := by exact_mod_cast hwR
      rw [bigradα_eq_bot_of_neg L α hwZ]
      exact bot_le
  · refine le_biSup (bigradα L) ?_
    simp only [Set.mem_preimage, Set.mem_singleton_iff, wtQ_eq, wtQrat]
    simp [qr.q_zero]

/-- The **vacuum lies in refined weight `0`** — the `vacuum_mem` field's analogue. -/
theorem latVacuumGen_mem_gradingLatGenQ {qr : QuadRefine L} (hq : PosQuad L qr) :
    latVacuumGen L ∈ gradingLatGenQ L qr 0 := by
  rw [gradingLatGenQ_zero_eq_span_vacuum L hq]
  exact Submodule.mem_span_singleton_self (latVacuumGen L)

/-- `PosQuad` holds for the standard refinement exactly when `L` is positive definite. -/
theorem posQuad_halfNormRefine (hEven : L.Even) (hPos : L.PosDef) :
    PosQuad L (halfNormRefine L hEven) := by
  intro α hα
  have := halfNorm_pos L hEven hPos hα
  simpa [halfNormRefine_q] using (by exact_mod_cast this : (0 : ℚ) < (halfNorm L α : ℚ))

/-! ## §5  Finite-dimensionality of the refined weight spaces

`QFinite` is the `q`-dependent input (the refined analogue of `BoundedFinite`).  Unlike internality,
finite-dimensionality genuinely depends on `q`: it is the statement that the deformed weight is a
proper (bounded-fibre) function on the charge lattice. -/

/-- **`QFinite`** — for every bound, only finitely many charges have refined weight below it. -/
def QFinite (qr : QuadRefine L) : Prop := ∀ N : ℚ, {α : L.carrier | qr.q α ≤ N}.Finite

/-- The non-negative-boson-weight part of the refined weight-`k` fibre. -/
def fiberQ (qr : QuadRefine L) (k : ℂ) : Set (ℤ × L.carrier) :=
  {p : ℤ × L.carrier | wtQ L qr p = k ∧ 0 ≤ p.1}

/-- Negative boson weights contribute nothing, so the refined weight space is the sup over the
non-negative fibre.  (Unconditional: `bigradα (w,α) = ⊥` for `w < 0`.) -/
theorem gradingLatGenQ_eq_biSup_pos (qr : QuadRefine L) (k : ℂ) :
    gradingLatGenQ L qr k = ⨆ p ∈ fiberQ L qr k, bigradα L p := by
  rw [gradingLatGenQ_def]
  apply le_antisymm
  · refine iSup_le fun p => iSup_le fun hp => ?_
    by_cases hw : 0 ≤ p.1
    · exact le_biSup (bigradα L) (⟨hp, hw⟩ : p ∈ fiberQ L qr k)
    · obtain ⟨w, α⟩ := p
      rw [bigradα_eq_bot_of_neg L α (by omega : w < 0)]
      exact bot_le
  · exact iSup_le fun p => iSup_le fun hp => le_biSup (bigradα L) hp.1

/-- The non-negative fibre is finite, given `QFinite`. -/
theorem fiberQ_finite {qr : QuadRefine L} (hqf : QFinite L qr) (k : ℂ) :
    (fiberQ L qr k).Finite := by
  by_cases hk : ∃ r : ℚ, (r : ℂ) = k
  · obtain ⟨r, rfl⟩ := hk
    have hrat : ∀ p ∈ fiberQ L qr (r : ℂ), wtQrat L qr p = r := by
      rintro p ⟨h, -⟩
      exact (wtQ_eq_ratCast_iff L qr p r).mp h
    have hinj : Set.InjOn Prod.snd (fiberQ L qr (r : ℂ)) := by
      intro p hp p' hp' hsnd
      have h1 := hrat p hp
      have h2 := hrat p' hp'
      have : (p.1 : ℚ) = (p'.1 : ℚ) := by
        simp only [wtQrat, hsnd] at h1
        simp only [wtQrat] at h2
        linarith
      have : p.1 = p'.1 := by exact_mod_cast this
      rw [Prod.ext_iff]
      exact ⟨this, hsnd⟩
    have hsub : Prod.snd '' (fiberQ L qr (r : ℂ)) ⊆ {α : L.carrier | qr.q α ≤ r} := by
      rintro α ⟨p, hp, rfl⟩
      have h1 := hrat p hp
      have h2 : (0 : ℤ) ≤ p.1 := hp.2
      have h2' : (0 : ℚ) ≤ (p.1 : ℚ) := by exact_mod_cast h2
      simp only [wtQrat] at h1
      simp only [Set.mem_setOf_eq]
      linarith
    exact Set.Finite.of_finite_image (Set.Finite.subset (hqf r) hsub) hinj
  · have : fiberQ L qr k = ∅ := by
      ext p
      simp only [fiberQ, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro h _
      exact hk ⟨wtQrat L qr p, h⟩
    rw [this]
    exact Set.finite_empty

/-- **Each refined weight space is finite-dimensional**, given `QFinite`. -/
theorem gradingLatGenQ_finrank {qr : QuadRefine L} (hqf : QFinite L qr) (k : ℂ) :
    FiniteDimensional ℂ (gradingLatGenQ L qr k) := by
  rw [gradingLatGenQ_eq_biSup_pos L qr k, ← iSup_subtype'']
  have : Finite (fiberQ L qr k) := fiberQ_finite L hqf k
  infer_instance

/-- `QFinite` holds for the standard refinement, from `BoundedFinite` (hence from `hPos`). -/
theorem qFinite_halfNormRefine (hEven : L.Even) (hPos : L.PosDef) :
    QFinite L (halfNormRefine L hEven) := by
  intro N
  refine Set.Finite.subset (IntegralLattice.boundedFinite L hPos (2 * ⌈N⌉)) ?_
  intro α hα
  simp only [Set.mem_setOf_eq, halfNormRefine_q] at hα
  have h1 : (halfNorm L α : ℚ) ≤ (⌈N⌉ : ℚ) := le_trans hα (Int.le_ceil N)
  have h2 : halfNorm L α ≤ ⌈N⌉ := by exact_mod_cast h1
  have h3 := two_halfNorm L hEven α
  simp only [Set.mem_setOf_eq]
  omega

end VOA.LatGen
