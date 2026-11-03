/-
Copyright (c) 2026 Leonardo Rastelli and Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import VOA.LatticesAndCodes.Lattice.Euclidean

/-!
# Representation numbers

**Ebeling §2.1.** `IntegralLattice.repCount Γ m` is the number of vectors of `Γ` of norm `m` —
Ebeling's `r_Γ(m)`, the coefficient of the theta series.

This file is deliberately **analysis-free**. Convention S5 of `BLUEPRINT.md` splits the theta
layer in two: `repCount` is `ℕ`-valued and combinatorial, and `theta` is expressed through it, so
that Chapter 3's combinatorics never has to touch the analytic layer. The only input from
elsewhere is `IntegralLattice.finite_normSq_le` (M4), which is itself proved over `ℤ` from
Cauchy-Schwarz.

## Main definitions

* `IntegralLattice.repCount` — `r_Γ(m)`, as a natural number.
* `IntegralLattice.repFinset` — the vectors of norm `m`, as a `Finset`.
* `IntegralLattice.normBallFinset` — the vectors of norm at most `c`.

## Main results

* `IntegralLattice.repCount_zero`, `repCount_of_neg`, `repCount_eq_zero_of_not_even` — the
  values that vanish or are forced.
* `IntegralLattice.Isom.repCount_eq` — representation numbers are isometry invariants.
* `IntegralLattice.sum_repCount_Icc` — counting by norm: `∑_{0 ≤ m ≤ c} r_Γ(m)` is the number of
  vectors of norm at most `c`. This is the shape the growth estimates of M20 will want.

## References

Ebeling, *Lattices and Codes*, §2.1.
-/

namespace IntegralLattice

variable {Γ Λ : IntegralLattice}

/-! ### Representation numbers -/

theorem finite_setOf_normSq_eq (h : Γ.IsPosDef) (m : ℤ) : {x : Γ | normSq x = m}.Finite :=
  (Γ.finite_normSq_le h m).subset fun _ hx => le_of_eq hx

/-- The **representation number** `r_Γ(m)`: the number of vectors of `Γ` of norm `m`.
Ebeling §2.1. It is `ℕ`-valued and purely combinatorial — no analysis enters — which is what
convention S5 asks for: Chapter 3 reasons about `repCount` and never about `theta`. -/
noncomputable def repCount (Γ : IntegralLattice) (m : ℤ) : ℕ := {x : Γ | normSq x = m}.ncard

/-- The vectors of norm `m`, as a `Finset`. -/
noncomputable def repFinset (Γ : IntegralLattice) (h : Γ.IsPosDef) (m : ℤ) : Finset Γ :=
  (finite_setOf_normSq_eq h m).toFinset

@[simp] theorem mem_repFinset {h : Γ.IsPosDef} {m : ℤ} {x : Γ} :
    x ∈ Γ.repFinset h m ↔ normSq x = m := by
  simp [repFinset]

theorem card_repFinset (h : Γ.IsPosDef) (m : ℤ) :
    (Γ.repFinset h m).card = Γ.repCount m :=
  (Set.ncard_eq_toFinset_card _ (finite_setOf_normSq_eq h m)).symm

/-- There is nothing of negative norm. -/
theorem repCount_of_neg (h : Γ.IsPosDef) {m : ℤ} (hm : m < 0) : Γ.repCount m = 0 := by
  rw [repCount, Set.ncard_eq_zero (finite_setOf_normSq_eq h m)]
  refine Set.eq_empty_of_forall_notMem fun x hx => ?_
  have h1 : normSq x = m := hx
  have h2 := h.normSq_nonneg x
  omega

/-- Only the origin has norm zero. -/
theorem repCount_zero (h : Γ.IsPosDef) : Γ.repCount 0 = 1 := by
  have hset : {x : Γ | normSq x = 0} = {0} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    exact h.normSq_eq_zero_iff
  rw [repCount, hset, Set.ncard_singleton]

/-- On an even lattice the odd representation numbers vanish. -/
theorem repCount_eq_zero_of_not_even (h : Γ.IsPosDef) (he : Γ.IsEven) {m : ℤ}
    (hm : ¬ (2 : ℤ) ∣ m) : Γ.repCount m = 0 := by
  rw [repCount, Set.ncard_eq_zero (finite_setOf_normSq_eq h m)]
  refine Set.eq_empty_of_forall_notMem fun x hx => ?_
  have h1 : normSq x = m := hx
  exact hm (h1 ▸ he x)

/-- Representation numbers are isometry invariants. -/
theorem Isom.repCount_eq (f : Γ ≃ₗᵢ Λ) (m : ℤ) : Γ.repCount m = Λ.repCount m := by
  have himg : f.toLinearEquiv '' {x : Γ | normSq x = m} = {y : Λ | normSq y = m} := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      show normSq (f x) = m
      rw [f.map_normSq]
      exact hx
    · intro hy
      refine ⟨f.symm y, ?_, f.apply_symm_apply y⟩
      show normSq (f.symm y) = m
      have h1 : normSq (f (f.symm y)) = normSq (f.symm y) := f.map_normSq _
      rw [f.apply_symm_apply] at h1
      rw [← h1]
      exact hy
  show {x : Γ | normSq x = m}.ncard = {y : Λ | normSq y = m}.ncard
  rw [← himg, Set.ncard_image_of_injective _ f.toLinearEquiv.injective]

/-! ### Counting by norm -/

/-- The vectors of norm at most `c`, as a `Finset`. -/
noncomputable def normBallFinset (Γ : IntegralLattice) (h : Γ.IsPosDef) (c : ℤ) : Finset Γ :=
  (Γ.finite_normSq_le h c).toFinset

@[simp] theorem mem_normBallFinset {h : Γ.IsPosDef} {c : ℤ} {x : Γ} :
    x ∈ Γ.normBallFinset h c ↔ normSq x ≤ c := by
  simp [normBallFinset]

theorem repFinset_disjoint (h : Γ.IsPosDef) {m m' : ℤ} (hmm' : m ≠ m') :
    Disjoint (Γ.repFinset h m) (Γ.repFinset h m') :=
  Finset.disjoint_left.mpr fun x hx hx' => by
    rw [mem_repFinset] at hx hx'
    exact hmm' (hx ▸ hx')

/-- The vectors of norm at most `c` are partitioned by their norm. -/
theorem sum_repCount_Icc (h : Γ.IsPosDef) (c : ℤ) :
    ∑ m ∈ Finset.Icc 0 c, Γ.repCount m = (Γ.normBallFinset h c).card := by
  classical
  have hdisj : ∀ m ∈ Finset.Icc (0 : ℤ) c, ∀ m' ∈ Finset.Icc (0 : ℤ) c, m ≠ m' →
      Disjoint (Γ.repFinset h m) (Γ.repFinset h m') := fun m _ m' _ hmm' =>
    repFinset_disjoint h hmm'
  have hbi : Γ.normBallFinset h c = (Finset.Icc 0 c).biUnion (Γ.repFinset h) := by
    ext x
    simp only [mem_normBallFinset, Finset.mem_biUnion, Finset.mem_Icc, mem_repFinset]
    constructor
    · intro hx
      exact ⟨normSq x, ⟨h.normSq_nonneg x, hx⟩, rfl⟩
    · rintro ⟨m, ⟨-, hm⟩, hx⟩
      exact hx ▸ hm
  rw [hbi, Finset.card_biUnion hdisj]
  exact Finset.sum_congr rfl fun m _ => (card_repFinset h m).symm

end IntegralLattice
