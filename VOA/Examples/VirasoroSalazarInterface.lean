/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Examples.VirasoroAdmissibleCombinatorics
import VOA.Examples.VirasoroGoodFiltration

/-!
# An axiom-free interface for Salazar's filtered Virasoro basis theorem

Salazar's Theorem 0.2 gives a vector-space basis of the boundary simple Virasoro module by
admissible PBW monomials.  Proposition 2.2 supplies the stronger filtered statement needed by the
graded-unitarity project.  These are logically different from the refined-character equality:

* `AdmissibleMonomialBasisAt` says the admissible monomial images form a basis of one weight space;
* `AdmissibleFilteredBasisAt` additionally identifies every length-filtration step with the span
  of the admissible basis vectors of bounded length;
* `AdmissibleCharacterAt` records only the resulting step dimensions.

Nothing in this file asserts any of these propositions.  They are definitions of explicit
predicates, together with unconditional implications between them.  In particular, this file
adds no axiom and does not hide Salazar's theorem inside an instance or a definition.
-/

set_option linter.style.longLine false

namespace VOA

namespace AdmissiblePartitions

open VOA.VirModule VOA.VirSimple VOA.VirGoodFil
open VOA.VertexOperatorAlgebra
open Module (finrank)

/-! ## Admissible monomials in the simple quotient -/

/-- The image in the simple quotient of the creation monomial indexed by an admissible word. -/
noncomputable def admissibleSimpleWord (c : ℂ) (n N : ℕ) (w : AdmissibleOfEnergy n N) :
    (virasoroSimple c).grading (N : ℤ) :=
  ⟨(maxIdealVir c).mkQ (negWordVir c w.1.1), by
    have hw := negWord_mem_gradingVir c w.1.1
    rw [w.1.2.2] at hw
    exact virasoroSimple_mkQ_grading (c := c) hw⟩

/-- Forgetting the proof that an admissible word has weight N leaves precisely
its image under the universal-to-simple quotient map. No basis claim is used. -/
@[simp] theorem admissibleSimpleWord_val (c : ℂ) (n N : ℕ) (w : AdmissibleOfEnergy n N) :
    (admissibleSimpleWord c n N w : VirUniv c ⧸ maxIdealVir c) =
      (maxIdealVir c).mkQ (negWordVir c w.1.1) := rfl

/-- The admissible family restricted to lengths at most `p`. -/
noncomputable def admissibleSimpleWordLE (c : ℂ) (n N p : ℕ) :
    AdmissibleOfEnergyLengthLE n N p → (virasoroSimple c).grading (N : ℤ) :=
  fun w => admissibleSimpleWord c n N w.1

/-- Every admissible monomial of length at most `p` belongs to the corresponding filtration
step.  This is immediate from the definition of `goodFil` as the image of the universal
creation-word span; no basis theorem is involved. -/
theorem admissibleSimpleWord_mem_pieceIn (c : ℂ) {n N p : ℕ}
    (w : AdmissibleOfEnergy n N) (hw : w.1.1.length ≤ p) :
    admissibleSimpleWord c n N w ∈ (virGradedFlag c).pieceIn p (N : ℤ) := by
  change (maxIdealVir c).mkQ (negWordVir c w.1.1) ∈ goodFil c p (N : ℤ)
  rw [goodFil]
  refine ⟨negWordVir c w.1.1, ?_, rfl⟩
  exact Submodule.subset_span ⟨w.1.1, w.1.2.1, by exact_mod_cast w.1.2.2, hw, rfl⟩

/-- Linear combinations of admissible words of length at most p belong to the
length-p filtration. This proves the easy inclusion; expressing every filtered
state in these admissible words is the separate, substantive basis input. -/
theorem span_admissibleSimpleWordLE_le_pieceIn (c : ℂ) (n N p : ℕ) :
    Submodule.span ℂ (Set.range (admissibleSimpleWordLE c n N p)) ≤
      (virGradedFlag c).pieceIn p (N : ℤ) := by
  rw [Submodule.span_le]
  rintro _ ⟨w, rfl⟩
  exact admissibleSimpleWord_mem_pieceIn c w.1 w.2

/-! ## Three deliberately separate theorem interfaces -/

/-- The admissible monomial images form a vector-space basis at weight `N`.

This is the shape of Salazar's Theorem 0.2 after specialization to the boundary vacuum module.
It does not by itself identify initial length segments with `goodFil`. -/
def AdmissibleMonomialBasisAt (c : ℂ) (n N : ℕ) : Prop :=
  LinearIndependent ℂ (admissibleSimpleWord c n N) ∧
    Submodule.span ℂ (Set.range (admissibleSimpleWord c n N)) = ⊤

/-- The filtration-refining strengthening of the admissible monomial basis theorem.

The first field is the full monomial basis statement.  The second is the genuinely filtered
content: at every `p`, the length step is exactly the span of admissible monomials of length at
most `p`.  The reverse inclusion of `span_admissibleSimpleWordLE_le_pieceIn` is the substantive
part of Salazar's filtered bridge. -/
structure AdmissibleFilteredBasisAt (c : ℂ) (n N : ℕ) : Prop where
  /-- The admissible images form a basis of the whole weight space. -/
  basis : AdmissibleMonomialBasisAt c n N
  /-- The basis refines the creation-word length filtration. -/
  filtration_eq : ∀ p : ℕ,
    (virGradedFlag c).pieceIn p (N : ℤ) =
      Submodule.span ℂ (Set.range (admissibleSimpleWordLE c n N p))

/-- The refined-character statement at one weight, stated only as equality of cumulative
dimensions.  It is strictly weaker data than `AdmissibleFilteredBasisAt`. -/
def AdmissibleCharacterAt (c : ℂ) (n N : ℕ) : Prop :=
  ∀ p : ℕ,
    finrank ℂ ((virGradedFlag c).pieceIn p (N : ℤ)) = admissibleCumulativeCount n N p

/-- The cumulative character condition can be read as a sum over exact word
lengths from zero to p. This is a reformulation of a dimension condition,
not a proof that the admissible words form a filtered basis. -/
theorem admissibleCharacterAt_iff (c : ℂ) (n N : ℕ) :
    AdmissibleCharacterAt c n N ↔
      ∀ p : ℕ, finrank ℂ ((virGradedFlag c).pieceIn p (N : ℤ)) =
        ∑ r ∈ Finset.range (p + 1), admissibleCount n N r := by
  simp only [AdmissibleCharacterAt, admissibleCumulativeCount_eq_sum]

/-! ## Unconditional consequences of the interfaces -/

/-- A filtered admissible basis is in particular an admissible vector-space basis. -/
theorem AdmissibleFilteredBasisAt.toMonomialBasis {c : ℂ} {n N : ℕ}
    (h : AdmissibleFilteredBasisAt c n N) : AdmissibleMonomialBasisAt c n N :=
  h.basis

/-- The bounded-length admissible family is linearly independent whenever the full family is. -/
theorem AdmissibleMonomialBasisAt.linearIndependentLE {c : ℂ} {n N : ℕ}
    (h : AdmissibleMonomialBasisAt c n N) (p : ℕ) :
    LinearIndependent ℂ (admissibleSimpleWordLE c n N p) :=
  h.1.comp _ Subtype.val_injective

/-- The filtered basis theorem implies the refined-character dimension equality. -/
theorem AdmissibleFilteredBasisAt.toCharacter {c : ℂ} {n N : ℕ}
    (h : AdmissibleFilteredBasisAt c n N) : AdmissibleCharacterAt c n N := by
  intro p
  rw [h.filtration_eq p, admissibleCumulativeCount]
  exact finrank_span_eq_card (h.basis.linearIndependentLE p)

/-- The unfiltered basis statement gives the total weight-space dimension. -/
theorem finrank_eq_card_of_admissibleMonomialBasisAt {c : ℂ} {n N : ℕ}
    (h : AdmissibleMonomialBasisAt c n N) :
    finrank ℂ ((virasoroSimple c).grading (N : ℤ)) = Fintype.card (AdmissibleOfEnergy n N) := by
  have hdim := finrank_span_eq_card h.1
  rw [h.2] at hdim
  simpa using hdim

end AdmissiblePartitions

end VOA
