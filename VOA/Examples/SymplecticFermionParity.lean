/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Examples.SymplecticFermionWords

/-!
# Symplectic fermions: parity of the creation monomials

The last hypothesis `reconstructε` still needs from the symplectic-fermion side: **a null
combination of creation monomials has null parity components**.

## Why this is not automatic

`reconstructε` runs Goddard uniqueness one Koszul sign at a time, so `ker S ≤ ker F` has to be
checked parity by parity: from `∑ᵢ cᵢ · stᵢ = 0` one must be able to conclude that the even part
`∑_{|i| even} cᵢ · stᵢ` already vanishes on its own.  For a general spanning family that is false
— it is exactly the statement that the family is *parity graded*.

For symplectic fermions it is true for a structural reason, and the reason is the whole point of
building the Fock space as a Clifford algebra rather than by hand: `CliffordAlgebra QSF` is
`ℤ/2`-graded (`CliffordAlgebra.gradedAlgebra`), and its even and odd parts are **complementary**
(`CliffordAlgebra.evenOdd_isCompl`), hence in particular disjoint.  A word of length `n` is a
product of `n` generators, so `stWordSF l` is homogeneous of parity `l.length`; a combination
supported in one parity therefore lands in one summand, and a sum of the two summands can only
vanish if each does.

So the two results below are: homogeneity (`stWordSF_mem_evenOdd`), and the consequence of
disjointness (`stWordSF_parity_split`).  Nothing about vertex operators enters — this is pure
Clifford grading.
-/

namespace VOA.SympFerm

open CliffordAlgebra

/-- **A word is homogeneous of parity its length.**  `stWordSF l` is a product of `l.length`
generators `ι QSF (single p 1)`, each of which is odd, so the product lies in the `l.length`
component of the `ℤ/2` grading.  The induction is the graded-monoid one: `1` is even, and
multiplying an odd element by a parity-`n` element gives parity `1 + n`. -/
theorem stWordSF_mem_evenOdd (l : SFWord) :
    stWordSF l ∈ evenOdd QSF ((l.length : ℕ) : ZMod 2) := by
  induction l with
  | nil =>
      have hlen : ((List.length ([] : SFWord) : ℕ) : ZMod 2) = 0 := by
        rw [List.length_nil, Nat.cast_zero]
      rw [stWordSF_nil, hlen]
      exact SetLike.one_mem_graded (evenOdd QSF)
  | cons a rest ih =>
      have hlen : (((a :: rest).length : ℕ) : ZMod 2)
          = (1 : ZMod 2) + ((rest.length : ℕ) : ZMod 2) := by
        rw [List.length_cons, Nat.cast_add, Nat.cast_one, add_comm]
      rw [stWordSF_cons, hlen]
      exact SetLike.mul_mem_graded (ι_mem_evenOdd_one QSF _) ih

/-- A linear combination of words all of the same parity is homogeneous of that parity: the
grading components are submodules, so they are closed under the scalar multiples and the finite
sum that `Finsupp.linearCombination` unfolds to. -/
theorem lc_stWordSF_mem_evenOdd (d : SFWord →₀ ℂ) (q : ZMod 2)
    (hd : ∀ l ∈ d.support, ((l.length : ℕ) : ZMod 2) = q) :
    Finsupp.linearCombination ℂ stWordSF d ∈ evenOdd QSF q := by
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  refine Submodule.sum_mem _ (fun l hl => ?_)
  rw [← hd l hl]
  exact Submodule.smul_mem _ _ (stWordSF_mem_evenOdd l)

/-- **A parity and its opposite are disjoint.**  `evenOdd_isCompl` states this for the ordered
pair `(0, 1)`; since `ZMod 2` has only two elements, `q` and `q + 1` are that pair in one order or
the other, and `Disjoint` is symmetric. -/
theorem evenOdd_disjoint_succ (q : ZMod 2) :
    Disjoint (evenOdd QSF q) (evenOdd QSF (q + 1)) := by
  by_cases hq : q = 0
  · subst hq
    rw [zero_add]
    exact (evenOdd_isCompl QSF).disjoint
  · have hq1 : q = 1 := by rw [zmod_two_ne 0 q hq, zero_add]
    subst hq1
    rw [show (1 : ZMod 2) + 1 = 0 from by decide]
    exact (evenOdd_isCompl QSF).disjoint.symm

/-- **A null combination has null parity components** — the `hparity` hypothesis of
`reconstructε`, for the symplectic-fermion spanning family.

Split `c` into its parity-`p` part `A` and the rest `B`.  Then `S A + S B = 0`, so `S A = -S B`.
But `S A` lies in `evenOdd QSF p` and `S B` in `evenOdd QSF (p + 1)`, so `S A` lies in both, and
those two submodules are disjoint.  Hence `S A = 0`. -/
theorem stWordSF_parity_split (c : SFWord →₀ ℂ)
    (hc : Finsupp.linearCombination ℂ stWordSF c = 0) (p : ZMod 2) :
    Finsupp.linearCombination ℂ stWordSF
      (c.filter (fun l => ((l.length : ℕ) : ZMod 2) = p)) = 0 := by
  -- `c = A + B` with `A` the parity-`p` part.
  have hsum : Finsupp.linearCombination ℂ stWordSF
        (c.filter (fun l => ((l.length : ℕ) : ZMod 2) = p))
      + Finsupp.linearCombination ℂ stWordSF
        (c.filter (fun l => ¬ (((l.length : ℕ) : ZMod 2) = p))) = 0 := by
    have h := hc
    rw [finsupp_parity_split (fun l : SFWord => ((l.length : ℕ) : ZMod 2)) p c, map_add] at h
    exact h
  -- The parity-`p` part is homogeneous of parity `p`.
  have hmemP : Finsupp.linearCombination ℂ stWordSF
      (c.filter (fun l => ((l.length : ℕ) : ZMod 2) = p)) ∈ evenOdd QSF p := by
    refine lc_stWordSF_mem_evenOdd _ p (fun l hl => ?_)
    have hmem := Finsupp.support_filter
      (p := fun l : SFWord => ((l.length : ℕ) : ZMod 2) = p) (f := c) ▸ hl
    exact (Finset.mem_filter.mp hmem).2
  -- The complementary part is homogeneous of the opposite parity, because `ZMod 2` has two
  -- elements: not being `p` means being `p + 1`.
  have hmemQ : Finsupp.linearCombination ℂ stWordSF
      (c.filter (fun l => ¬ (((l.length : ℕ) : ZMod 2) = p))) ∈ evenOdd QSF (p + 1) := by
    refine lc_stWordSF_mem_evenOdd _ (p + 1) (fun l hl => ?_)
    have hmem := Finsupp.support_filter
      (p := fun l : SFWord => ¬ (((l.length : ℕ) : ZMod 2) = p)) (f := c) ▸ hl
    exact zmod_two_ne p ((l.length : ℕ) : ZMod 2) (Finset.mem_filter.mp hmem).2
  -- Being the negative of the other part, `A` is *also* of parity `p + 1`.
  have hmemP' : Finsupp.linearCombination ℂ stWordSF
      (c.filter (fun l => ((l.length : ℕ) : ZMod 2) = p)) ∈ evenOdd QSF (p + 1) := by
    rw [eq_neg_of_add_eq_zero_left hsum]
    exact Submodule.neg_mem _ hmemQ
  exact Submodule.disjoint_def.mp (evenOdd_disjoint_succ p) _ hmemP hmemP'

end VOA.SympFerm
