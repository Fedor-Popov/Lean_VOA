/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Examples.VirasoroQuotientForm
import VOA.Examples.VirasoroPartitionBasis
import VOA.Core.GoodFiltration

/-!
# The length filtration on `L(c,0)` — ABLR eq. (3.11) = Kaufmann `Ṽ_{n,k}`

⚠ **This file constructs a DEFINITION and proves its order-theoretic properties.  It proves
nothing about graded unitarity, positivity, signatures, or dimensions of layers.**

The filtration is ABLR eq. (3.11) of Arabi Ardehali–Beem–Lemos–Rastelli, arXiv:2507.23781v2,

  `G_p V = span{ L₋₂₋ₙ₁ ⋯ L₋₂₋ₙ_k Ω : k ≤ p }`,

which is literally Kaufmann's `Ṽ_{n,k}` (hep-th/9405041, §4.2).  In this repository's indexing the
entry `i` of a `VirModule.SortedWord` denotes the mode `L₋ᵢ₋₂`, so `w.length` **is** the
filtration degree `R` and `VirModule.energyVir w` **is** the conformal weight.

## The design decision that keeps this honest

`goodFil` is defined as the **image under `mkQ` of a span of monomials**, never as the span of a
claimed basis of the simple quotient:

* defined as an image, it is unconditional — every field of `GradedFlag` below is *proved*;
* defined via an "admissible basis" it would silently import the **open half** of the Kaufmann
  conjecture (that the admissible monomials descend to a basis of `L(c_{2,2n+1},0)ₙ` — the
  Andrews–Gordon/Salazar refined character) into its own definition.

That refined-character statement is **not** a field here, is **not** proved anywhere, and appears
only as the explicitly cited hypothesis `AdmissiblePartitions.AdmissibleBasisHyp`.

## What is proved

* `virFil`, `goodFil` — the filtration on `V(c,0)` and its image on `L(c,0)`.
* `length_le_energyVir` — a word of energy `N` has length `≤ N`; hence the flag is **finite**:
  `virFil_eq_grading_of_le` says it has already reached `𝒱ₙ` at `p = n`.
* `iSup_virFil`, and hence `exhaustive` — the flag exhausts every weight space.  This is the
  only nontrivial field, and it rests on the *proved* sorting theorem
  `VirModule.gradingVir_eq_sortedSpanVir`.
* `virGradedFlag : GradedFlag (virasoroSimple c)` — the assembled object, for **every** `c`.

## ⚠ What is NOT proved

`GradedFlag.ModeCompatible` (`u₍ₖ₎v ∈ G_{p+q}`) is **not** established for `virGradedFlag`, so no
`GoodFiltration` instance is constructed.  That predicate is itself flagged in
`Core.GoodFiltration` as a **reconstruction** of ABLR's word "good" — the source is not in
`refs/` and the axiom could not be transcribed.  Nothing downstream needs it: the reduction in
`Core.GradedUnitarity` consumes only `mono`, `le_grading`, `bot` and `exhaustive`.

## References
* Arabi Ardehali, Beem, Lemos, Rastelli, arXiv:2507.23781v2, eq. (3.11).
* R. M. Kaufmann, hep-th/9405041, §4.2.
-/

namespace VOA

namespace VirGoodFil

open VOA.VirModule VOA.VirSimple VOA.VirQuotForm
open VOA.VertexOperatorAlgebra

variable (c : ℂ)

/-! ## §1  The filtration on `V(c,0)` -/

/-- **ABLR eq. (3.11) on the universal module.**  `virFil c p n` is the span of the sorted
creation monomials of conformal weight `n` and **length at most `p`**.

The weight is an integer; for `n < 0` the defining set is empty (energies are natural numbers),
so `virFil c p n = ⊥` automatically and no case split is needed. -/
noncomputable def virFil (p : ℕ) (n : ℤ) : Submodule ℂ (VirUniv c) :=
  Submodule.span ℂ
    { x | ∃ w : List ℕ, SortedWord w ∧ (energyVir w : ℤ) = n ∧ w.length ≤ p ∧
            negWordVir c w = x }

/-- **The good filtration on `L(c,0)`**: the image of `virFil` under the quotient map.

⚠ An *image*, not a span of a claimed basis — see the file docstring. -/
noncomputable def goodFil (p : ℕ) (n : ℤ) : Submodule ℂ (VirUniv c ⧸ maxIdealVir c) :=
  (virFil c p n).map (maxIdealVir c).mkQ

/-- Increasing the allowed number of creation modes can only enlarge the universal filtration
step. Every old generating word still satisfies the new length bound. -/
theorem virFil_mono {p q : ℕ} (n : ℤ) (h : p ≤ q) : virFil c p n ≤ virFil c q n :=
  Submodule.span_mono (fun _ ⟨w, hw, hen, hlen, hx⟩ => ⟨w, hw, hen, hlen.trans h, hx⟩)

/-- The same inclusions survive projection to the simple quotient: taking a linear image preserves
inclusion of the universal filtration subspaces. -/
theorem goodFil_mono {p q : ℕ} (n : ℤ) (h : p ≤ q) : goodFil c p n ≤ goodFil c q n :=
  Submodule.map_mono (virFil_mono c n h)

/-- Every generator of a filtration step has the specified conformal weight. Its entire linear
span therefore stays inside that homogeneous weight space. -/
theorem virFil_le_grading (p : ℕ) (n : ℤ) : virFil c p n ≤ gradingVir c n := by
  rw [virFil, Submodule.span_le]
  rintro _ ⟨w, -, hen, -, rfl⟩
  exact hen ▸ negWord_mem_gradingVir c w

/-- The quotient filtration remains homogeneous, because the simple VOA grading is the image of
the corresponding universal weight space. -/
theorem goodFil_le_grading (p : ℕ) (n : ℤ) :
    goodFil c p n ≤ (virasoroSimple c).grading n :=
  Submodule.map_mono (virFil_le_grading c p n)

/-! ## §2  Degree `0`, and the vacuum line -/

/-- A word of length `≤ 0` is the empty word, whose energy is `0`; so in positive weight the
degree-`0` piece has no generators. -/
theorem virFil_zero_of_pos {n : ℤ} (hn : 0 < n) : virFil c 0 n = ⊥ := by
  rw [virFil, Submodule.span_eq_bot]
  rintro _ ⟨w, -, hen, hlen, rfl⟩
  exact absurd hen (by rw [List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)]; simp; omega)

/-- No positive-weight state can be built with zero creation modes, even after taking the simple
quotient. The zeroth filtration step at positive weight is zero. -/
theorem goodFil_zero_of_pos {n : ℤ} (hn : 0 < n) : goodFil c 0 n = ⊥ := by
  rw [goodFil, virFil_zero_of_pos c hn, Submodule.map_bot]

/-- The defining set of `virFil c 0 0` is exactly `{𝟙}`. -/
theorem virFil_zero_zero_gens :
    { x | ∃ w : List ℕ, SortedWord w ∧ (energyVir w : ℤ) = (0 : ℤ) ∧ w.length ≤ 0 ∧
        negWordVir c w = x } = {vacVec c} := by
  ext x
  constructor
  · rintro ⟨w, -, -, hlen, rfl⟩
    rw [List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)]
    rfl
  · rintro rfl
    exact ⟨[], sortedWord_nil, by simp, le_rfl, rfl⟩

/-- At weight zero and length zero, the only creation word is empty. The universal filtration step
is exactly the one-dimensional vacuum span. -/
theorem virFil_zero_zero : virFil c 0 0 = ℂ ∙ vacVec c := by
  rw [virFil, virFil_zero_zero_gens]

/-- Projecting the universal vacuum line gives precisely the simple VOA vacuum line. This
identifies the starting step of the quotient flag. -/
theorem goodFil_zero_zero : goodFil c 0 0 = ℂ ∙ (virasoroSimple c).vacuum := by
  rw [goodFil, virFil_zero_zero, Submodule.map_span]
  congr 1
  simp [Set.image_singleton]
  rfl

/-! ## §3  Exhaustiveness -/

/-- A creation word of energy `N` has length at most `N`: each letter contributes at least `2`. -/
theorem length_le_energyVir : ∀ w : List ℕ, w.length ≤ energyVir w
  | [] => by simp
  | i :: rest => by
      have := length_le_energyVir rest
      rw [energyVir_cons, List.length_cons]
      omega

/-- The sorted span of energy `N` sits inside the union of the flag. -/
theorem sortedSpan_le_iSup_virFil (N : ℕ) :
    sortedSpanVir c N ≤ ⨆ p : ℕ, virFil c p (N : ℤ) := by
  rw [sortedSpanVir, Submodule.span_le]
  rintro _ ⟨u, hu, hen, rfl⟩
  exact Submodule.mem_iSup_of_mem u.length
    (Submodule.subset_span ⟨u, hu, by exact_mod_cast hen, le_rfl, rfl⟩)

/-- **The flag exhausts every weight space.**

For `n < 0` both sides are `⊥`.  For `n ≥ 0` this is the *proved* sorting theorem
`VirModule.gradingVir_eq_sortedSpanVir` (every creation monomial is a combination of sorted ones
of the same energy) together with the observation that a sorted word lies in the flag at its own
length. -/
theorem iSup_virFil (n : ℤ) : (⨆ p : ℕ, virFil c p n) = gradingVir c n := by
  refine le_antisymm (iSup_le fun p => virFil_le_grading c p n) ?_
  rw [gradingVir, Submodule.span_le]
  rintro _ ⟨ws, hen, rfl⟩
  have h1 : negWordVir c ws ∈ sortedSpanVir c (energyVir ws) :=
    negWordVir_mem_sortedSpanVir c ws
  have h2 := sortedSpan_le_iSup_virFil c (energyVir ws) h1
  rwa [hen] at h2

/-- Every simple-quotient state of a fixed weight occurs at some finite length bound. This follows
by projecting the proved exhaustive universal flag, with no admissible-basis or character
assumption. -/
theorem iSup_goodFil (n : ℤ) :
    (⨆ p : ℕ, goodFil c p n) = (virasoroSimple c).grading n := by
  have h : (⨆ p : ℕ, goodFil c p n) = (⨆ p : ℕ, virFil c p n).map (maxIdealVir c).mkQ :=
    (Submodule.map_iSup (maxIdealVir c).mkQ (fun p => virFil c p n)).symm
  rw [h, iSup_virFil]
  rfl

/-- **The flag is finite**: at degree `p = N` it has already reached the whole weight space,
because a word of energy `N` has length at most `N` (`length_le_energyVir`).

So the supremum in `exhaustive` is attained, and "the layers of `𝒱ₙ`" is a finite list. -/
theorem virFil_eq_grading_of_le {N p : ℕ} (h : N ≤ p) :
    virFil c p (N : ℤ) = gradingVir c (N : ℤ) := by
  refine le_antisymm (virFil_le_grading c p _) ?_
  rw [gradingVir_eq_sortedSpanVir, sortedSpanVir, Submodule.span_le]
  rintro _ ⟨u, hu, hen, rfl⟩
  exact Submodule.subset_span
    ⟨u, hu, by exact_mod_cast hen, le_trans (hen ▸ length_le_energyVir u) h, rfl⟩

/-- At weight N, any length bound at least N has already reached the entire simple-quotient weight
space. Thus each weight has only finitely many potentially new filtration steps; their
dimensions and signatures are not computed here. -/
theorem goodFil_eq_grading_of_le {N p : ℕ} (h : N ≤ p) :
    goodFil c p (N : ℤ) = (virasoroSimple c).grading (N : ℤ) := by
  rw [goodFil, virFil_eq_grading_of_le c h]; rfl

/-! ## §4  The assembled `GradedFlag` -/

/-- **The length filtration of `L(c,0)`, packaged as a `Core.GoodFiltration.GradedFlag`.**
Every field is proved, for **every** central charge `c`.

⚠ This is a `GradedFlag`, **not** a `GoodFiltration`: the vertex-algebraic clause
`GradedFlag.ModeCompatible` is not established here, and is in any case flagged in
`Core.GoodFiltration` as a *reconstruction* of ABLR's unread "good" axiom.  Nothing in
`Core.GradedUnitarity`'s reduction uses it.

⚠ Constructing this object asserts **nothing** about the form: not nondegeneracy on the steps, not
positivity on the layers, not the dimensions of the layers. -/
noncomputable def virGradedFlag : GradedFlag (virasoroSimple c) where
  piece := goodFil c
  le_grading := goodFil_le_grading c
  mono := fun n h => goodFil_mono c n h
  bot := fun _ hn => goodFil_zero_of_pos c hn
  vacuum_zero := goodFil_zero_zero c
  exhaustive := iSup_goodFil c

/-- The packaged graded flag uses exactly the quotient image filtration defined above. Accessing
its piece introduces no additional basis choice, positivity claim or mode-compatibility
assumption. -/
@[simp] theorem virGradedFlag_piece (p : ℕ) (n : ℤ) :
    (virGradedFlag c).piece p n = goodFil c p n := rfl

end VirGoodFil

end VOA
