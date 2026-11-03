/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import Mathlib.RingTheory.FiniteLength
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Algebraic finite-length criteria for the C₂ problem

A finite-dimensional subspace detecting **every strict subquotient** forces finite
length. The detecting subspace need not be a submodule over the larger ring. Thus
it can be a finite window of generalized conformal weight spaces. Merely meeting
every nonzero submodule is insufficient: detection is required for every `P < Q`.

The second result proves that vectors generating finite-length cyclic modules form
a submodule. This permits reduction to homogeneous generators without assuming
that an arbitrary cyclic submodule is graded.

These are algebraic lemmas, not a proof that C₂-cofiniteness supplies a detecting
subspace. The relevant VOA argument is Huang, arXiv:0712.4109, Proposition 4.3
(using Proposition 3.15), and Abe, arXiv:math/0311210, §2.
-/

namespace VOA.Classification.COne.FiniteLengthAlgebra

section Ring

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

/-- Finite length is inherited by a smaller submodule. -/
theorem finiteLength_mono {P Q : Submodule R M} (h : P ≤ Q)
    (hQ : IsFiniteLength R Q) : IsFiniteLength R P :=
  hQ.of_injective (Submodule.inclusion_injective h)

/-- A sum of two finite-length submodules has finite length. -/
theorem finiteLength_sup {P Q : Submodule R M}
    (hP : IsFiniteLength R P) (hQ : IsFiniteLength R Q) :
    IsFiniteLength R (P ⊔ Q : Submodule R M) := by
  obtain ⟨hPN, hPA⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp hP
  obtain ⟨hQN, hQA⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp hQ
  letI := hPN
  letI := hPA
  letI := hQN
  letI := hQA
  exact isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩

/-- The vectors whose cyclic submodules have finite length form an actual submodule. -/
def finiteLengthVectors (R M : Type*) [Ring R] [AddCommGroup M] [Module R M] :
    Submodule R M where
  carrier := {x | IsFiniteLength R (Submodule.span R {x})}
  zero_mem' := by
    change IsFiniteLength R (Submodule.span R {(0 : M)})
    rw [Submodule.span_zero_singleton]
    exact IsFiniteLength.of_subsingleton
  add_mem' := by
    intro x y hx hy
    apply finiteLength_mono (Q := Submodule.span R {x} ⊔ Submodule.span R {y})
      (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr ?_)) (finiteLength_sup hx hy)
    exact Submodule.add_mem _
      (Submodule.mem_sup_left (Submodule.mem_span_singleton_self x))
      (Submodule.mem_sup_right (Submodule.mem_span_singleton_self y))
  smul_mem' := by
    intro r x hx
    exact finiteLength_mono (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr
      ((Submodule.span R {x}).smul_mem r (Submodule.mem_span_singleton_self x)))) hx

/-- Local finite length implies finite length for every finitely generated submodule. -/
theorem finiteLength_of_fg_of_le_finiteLengthVectors (P : Submodule R M) (hP : P.FG)
    (hle : P ≤ finiteLengthVectors R M) : IsFiniteLength R P := by
  induction P, hP using Submodule.fg_induction with
  | singleton x => exact hle (Submodule.mem_span_singleton_self x)
  | sup P Q _ _ ihP ihQ =>
    exact finiteLength_sup (ihP (le_trans le_sup_left hle))
      (ihQ (le_trans le_sup_right hle))

end Ring

section Field

variable {K R M : Type*} [Field K] [Ring R] [Algebra K R]
  [AddCommGroup M] [Module R M] [Module K M] [IsScalarTower K R M]

/-- Every nonzero subquotient has a representative in `S`. All ring submodules,
not merely graded submodules or simple factors, are quantified over. -/
def DetectsSubquotients (S : Submodule K M) : Prop :=
  ∀ P Q : Submodule R M, P < Q → ∃ x : M, x ∈ S ∧ x ∈ Q ∧ x ∉ P

omit [Algebra K R] [IsScalarTower K R M] in
/-- Detection is equivalent to generation of every submodule by its intersection
with the same subspace. No finiteness or grading assumption is used here. -/
theorem detectsSubquotients_iff_span_inter_eq (S : Submodule K M) :
    DetectsSubquotients (R := R) S ↔
      ∀ Q : Submodule R M, Submodule.span R ((S : Set M) ∩ (Q : Set M)) = Q := by
  constructor
  · intro h Q
    have hle : Submodule.span R ((S : Set M) ∩ (Q : Set M)) ≤ Q :=
      Submodule.span_le.mpr (fun _ hx => hx.2)
    by_contra hne
    obtain ⟨x, hxS, hxQ, hxP⟩ := h _ Q (lt_of_le_of_ne hle hne)
    exact hxP (Submodule.subset_span ⟨hxS, hxQ⟩)
  · intro h P Q hPQ
    by_contra hnone
    have hQP : Q ≤ P := by
      rw [← h Q]
      refine Submodule.span_le.mpr (fun x hx => ?_)
      by_contra hxP
      exact hnone ⟨x, hx.1, hx.2, hxP⟩
    exact hPQ.not_ge hQP

/-- Intersecting with a detecting subspace strictly increases along every strict
inclusion of ring submodules. -/
theorem strictMono_comap_of_detectsSubquotients (S : Submodule K M)
    (hS : DetectsSubquotients (R := R) S) :
    StrictMono (fun P : Submodule R M => (P.restrictScalars K).comap S.subtype) := by
  intro P Q hPQ
  refine lt_of_le_of_ne (fun x hx => hPQ.le hx) ?_
  intro heq
  dsimp only at heq
  obtain ⟨x, hxS, hxQ, hxP⟩ := hS P Q hPQ
  have hx : (⟨x, hxS⟩ : S) ∈ (Q.restrictScalars K).comap S.subtype := hxQ
  rw [← heq] at hx
  exact hxP hx

/-- The finite-window dimension argument, valid over an arbitrary field and algebra.
It proves finite length over `R`, not finite dimension of the whole module over `K`. -/
theorem finiteLength_of_detectsSubquotients (S : Submodule K M)
    [FiniteDimensional K S] (hS : DetectsSubquotients (R := R) S) :
    IsFiniteLength R M := by
  have hmono := strictMono_comap_of_detectsSubquotients S hS
  haveI : WellFoundedLT (Submodule R M) := hmono.wellFoundedLT
  haveI : WellFoundedGT (Submodule R M) := hmono.wellFoundedGT
  exact isFiniteLength_iff_isNoetherian_isArtinian.mpr
    ⟨isNoetherian_iff'.mpr inferInstance, inferInstance⟩

/-- Every strictly increasing chain has at most `dim S` strict steps. -/
theorem chain_length_le_finrank (S : Submodule K M) [FiniteDimensional K S]
    (hS : DetectsSubquotients (R := R) S) {n : ℕ}
    (c : Fin (n + 1) → Submodule R M) (hc : StrictMono c) : n ≤ Module.finrank K S := by
  let d := fun i => Module.finrank K (((c i).restrictScalars K).comap S.subtype)
  have hd : StrictMono d :=
    Submodule.finrank_strictMono.comp ((strictMono_comap_of_detectsSubquotients S hS).comp hc)
  have hi : ∀ i : Fin (n + 1), i.val ≤ d i := by
    intro i
    induction i using Fin.induction with
    | zero => exact Nat.zero_le _
    | succ i ih =>
      have hlt := hd (show i.castSucc < i.succ from Fin.castSucc_lt_succ)
      change i.val + 1 ≤ d i.succ
      exact Nat.succ_le_of_lt (lt_of_le_of_lt ih hlt)
  exact le_trans (hi (Fin.last n)) (Submodule.finrank_le _)

/-- A detecting finite-dimensional subspace gives a composition series with an
explicit bound, not only the ascending and descending chain conditions. -/
theorem exists_compositionSeries_length_le (S : Submodule K M) [FiniteDimensional K S]
    (hS : DetectsSubquotients (R := R) S) :
    ∃ c : CompositionSeries (Submodule R M),
      c.head = ⊥ ∧ c.last = ⊤ ∧ c.length ≤ Module.finrank K S := by
  obtain ⟨c, hbot, htop⟩ := isFiniteLength_iff_exists_compositionSeries.mp
    (finiteLength_of_detectsSubquotients S hS)
  exact ⟨c, hbot, htop, chain_length_le_finrank S hS c c.strictMono⟩

end Field

end VOA.Classification.COne.FiniteLengthAlgebra
